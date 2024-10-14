use std::cell::RefCell;
use std::cmp::max;
use std::collections::VecDeque;
use std::mem::{take, zeroed};
use std::num::NonZero;
use std::ptr::NonNull;
use std::sync::atomic::Ordering::{Relaxed, SeqCst};
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicU64};
use std::thread::available_parallelism;

use crate::utils::{Stack, ULL};

const SLOTS_PER_NODE: usize = 8;

struct Reclaimer {
    slots: ULL<Slot, SLOTS_PER_NODE>,
    era: AtomicU64,

    // limbo lists may be transferred here on drop.
    drop_cache: Stack<Vec<RetiredFn>>,
}

pub fn join(cleanup_freq: usize) -> ThreadContext {
    let mut node = &RECLAIMER.slots.head;
    let mut index = 0;
    // iterate until we successfully claim a slot, expanding the list as necessary.
    loop {
        if index > 0 && index % SLOTS_PER_NODE == 0 {
            node = unsafe { node.get_or_init_next() };
        }
        if node.items[index % SLOTS_PER_NODE].try_claim() {
            break;
        }
        index += 1;
    }
    // set len to max(len, index + 1).
    let mut len = RECLAIMER.slots.len.load(SeqCst);
    while index + 1 > len {
        match RECLAIMER
            .slots
            .len
            .compare_exchange(len, index + 1, SeqCst, SeqCst)
        {
            Ok(_) => break,
            Err(l) => len = l,
        }
    }
    ThreadContext {
        slot: &node.items[index % SLOTS_PER_NODE],
        index,
        cleanup_freq,
        cleanup_counter: 0,
        counts: VecDeque::default(),
        intervals: Vec::default(),
        ready_to_drop: Vec::default(),
    }
}

static RECLAIMER: Reclaimer = Reclaimer {
    slots: unsafe { zeroed() },
    era: AtomicU64::new(1),
    drop_cache: Stack::new(),
};

/// See: https://docs.rs/crossbeam-utils/latest/src/crossbeam_utils/cache_padded.rs.html
#[cfg_attr(
    any(
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "powerpc64",
    ),
    repr(align(128))
)]
#[cfg_attr(
    any(
        target_arch = "arm",
        target_arch = "mips",
        target_arch = "mips32r6",
        target_arch = "mips64",
        target_arch = "mips64r6",
        target_arch = "sparc",
        target_arch = "hexagon",
    ),
    repr(align(32))
)]
#[cfg_attr(target_arch = "m68k", repr(align(16)))]
#[cfg_attr(target_arch = "s390x", repr(align(256)))]
#[cfg_attr(
    not(any(
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "powerpc64",
        target_arch = "arm",
        target_arch = "mips",
        target_arch = "mips32r6",
        target_arch = "mips64",
        target_arch = "mips64r6",
        target_arch = "sparc",
        target_arch = "hexagon",
        target_arch = "m68k",
        target_arch = "s390x",
    )),
    repr(align(64))
)]
struct Slot {
    start_era: AtomicU64,
    end_era: AtomicU64,
    is_claimed: AtomicBool,
}

impl Slot {
    fn try_claim(&self) -> bool {
        self.is_claimed
            .compare_exchange(false, true, SeqCst, Relaxed)
            .is_ok()
    }
}

thread_local! {
    static CTX: RefCell<ThreadContext> = RefCell::new(join(available_parallelism().map_or(32, NonZero::get)));
    static LIMBO_LIST: RefCell<LocalLimboList> = RefCell::new(LocalLimboList::new());
}

struct LocalLimboList(Vec<RetiredFn>);

impl LocalLimboList {
    fn new() -> Self {
        Self(
            RECLAIMER
                .drop_cache
                .take_all()
                .into_iter()
                .flatten()
                .collect(),
        )
    }
}

impl Drop for LocalLimboList {
    fn drop(&mut self) {
        if !self.0.is_empty() {
            RECLAIMER.drop_cache.insert(take(&mut self.0));
        }
    }
}

pub struct ThreadContext {
    slot: &'static Slot,
    index: usize,

    cleanup_freq: usize,
    cleanup_counter: usize,

    // a monotonically increasing queue consisting of (era, count) tuples.
    counts: VecDeque<(u64, usize)>,
    // a reusable Vec for storing hazardous intervals when scanning slots.
    intervals: Vec<(u64, u64)>,
    // a reusable Vec for storing items that are ready to be dropped.
    ready_to_drop: Vec<RetiredFn>,
}

pub fn load<T>(src: &AtomicPtr<T>) -> Option<Guard<T>> {
    protect(src, NonNull::new(src.load(SeqCst))?)
}

pub fn protect<T>(src: &AtomicPtr<T>, ptr: NonNull<T>) -> Option<Guard<T>> {
    let mut initial_end_era = 0;
    let mut era = RECLAIMER.era.load(SeqCst);
    CTX.with_borrow_mut(|ctx| {
        if let Some(back) = ctx.counts.back_mut() {
            initial_end_era = back.0;
            if initial_end_era == era {
                // the current era was already protected by a previous call to this method.
                // simply increment the count of the last protected era.
                back.1 += 1;
                return Some(Guard { era, ptr });
            }
        }
        ctx.slot.end_era.store(era, SeqCst);
        while let Some(ptr) = NonNull::new(src.load(SeqCst)) {
            let next_era = RECLAIMER.era.load(SeqCst);
            if era == next_era {
                ctx.counts.push_back((era, 1));
                if ctx.counts.len() == 1 {
                    // this is our first reservation, so start_era must also be updated.
                    ctx.slot.start_era.store(era, SeqCst);
                }
                return Some(Guard { era, ptr });
            }
            era = next_era;
            ctx.slot.end_era.store(era, SeqCst);
        }
        // null ptrs don't need protection; reset end_era to what it was before.
        ctx.slot.end_era.store(initial_end_era, SeqCst);
        None
    })
}

pub fn retire(ptr: NonNull<u8>, f: fn(NonNull<u8>), birth_era: u64) {
    CTX.with(|ref_cell| {
        if let Ok(mut ctx) = ref_cell.try_borrow_mut() {
            ctx.cleanup_counter = (ctx.cleanup_counter + 1) % ctx.cleanup_freq;
            if ctx.cleanup_counter == 0 {
                ctx.scan_and_cleanup();
            }
        }
    });
    let retire_era = RECLAIMER.era.load(SeqCst);
    let r = RetiredFn {
        ptr,
        f,
        span: (birth_era, retire_era),
    };
    LIMBO_LIST.with_borrow_mut(|list| list.0.push(r));
}

pub fn increment_era() {
    RECLAIMER.era.fetch_add(1, SeqCst);
}

pub fn load_era() -> u64 {
    RECLAIMER.era.load(SeqCst)
}

impl ThreadContext {
    fn scan_and_cleanup(&mut self) {
        // scan the global array of reservations.
        for slot in RECLAIMER.slots.into_iter() {
            let end = slot.end_era.load(SeqCst);
            if end == 0 {
                // this thread has no reservations.
                continue;
            }
            let mut start = slot.start_era.load(SeqCst);
            if start == 0 {
                // this slot has one reservation, defined by end_era.
                start = end;
            }
            self.intervals.push((start, end));
        }

        // merge the intervals.
        if self.intervals.len() > 1 {
            self.intervals.sort_unstable();
            let mut i = 1;
            for j in 1..self.intervals.len() {
                let (start, end) = self.intervals[j];
                // [(1, 2), (3, 4)] can be merged into [(1, 4)].
                if start <= self.intervals[i - 1].1 + 1 {
                    self.intervals[i - 1].1 = max(end, self.intervals[i - 1].1);
                } else {
                    self.intervals[i] = (start, end);
                    i += 1;
                }
            }
            self.intervals.truncate(i);
        }

        LIMBO_LIST.with_borrow_mut(|list| {
            // go through the limbo list and delete the entries without conflicts.
            let mut i = 0;
            while i < list.0.len() {
                let has_conflict = self
                    .intervals
                    .iter()
                    .any(|x| intervals_overlap(list.0[i].span, *x));
                if has_conflict {
                    i += 1;
                } else {
                    self.ready_to_drop.push(list.0.swap_remove(i));
                }
            }
        });
        self.ready_to_drop.clear();
        self.intervals.clear();
    }
}

fn intervals_overlap(a: (u64, u64), b: (u64, u64)) -> bool {
    a.0 <= b.1 && b.0 <= a.1
}

impl Drop for ThreadContext {
    fn drop(&mut self) {
        let mut nodes = vec![&RECLAIMER.slots.head];
        while let Some(next) = unsafe { nodes.last().unwrap().next.load(SeqCst).as_ref() } {
            nodes.push(next);
        }
        for i in (0..self.index + 1).rev() {
            let slot = &nodes[i / SLOTS_PER_NODE].items[i % SLOTS_PER_NODE];
            // temporarily claim the slot for purposes of shrinking the list length.
            if i < self.index && !slot.try_claim() {
                break;
            }
            let succeeded = RECLAIMER
                .slots
                .len
                .compare_exchange(i + 1, i, SeqCst, SeqCst)
                .is_ok();
            slot.is_claimed.store(false, SeqCst);
            if !succeeded {
                break;
            }
        }
    }
}

pub struct Guard<T> {
    era: u64,
    ptr: NonNull<T>,
}

impl<T> Guard<T> {
    pub fn as_ptr(&self) -> *mut T {
        self.ptr.as_ptr()
    }
}

impl<T> Drop for Guard<T> {
    fn drop(&mut self) {
        CTX.with_borrow_mut(|ctx| {
            // decrement the count.
            let pair = ctx.counts.iter_mut().find(|(e, _)| *e == self.era).unwrap();
            pair.1 -= 1;

            let mut start_era_changed = false;
            let mut end_era_changed = false;

            // pop from the front and back of the queue to shrink the interval.
            while let Some((_, count)) = ctx.counts.front() {
                if *count > 0 {
                    break;
                }
                ctx.counts.pop_front();
                start_era_changed = true;
            }
            while let Some((_, count)) = ctx.counts.back() {
                if *count > 0 {
                    break;
                }
                ctx.counts.pop_back();
                end_era_changed = true;
            }

            // update our interval.
            if ctx.counts.is_empty() {
                // we have no more reservations; zero out our interval.
                ctx.slot.end_era.store(0, SeqCst);
                ctx.slot.start_era.store(0, SeqCst);
            } else if start_era_changed {
                ctx.slot
                    .start_era
                    .store(ctx.counts.front().unwrap().0, SeqCst);
            } else if end_era_changed {
                ctx.slot.end_era.store(ctx.counts.back().unwrap().0, SeqCst);
            }
        });
    }
}

struct RetiredFn {
    ptr: NonNull<u8>,
    f: fn(NonNull<u8>),
    span: (u64, u64),
}

impl Drop for RetiredFn {
    fn drop(&mut self) {
        (self.f)(self.ptr);
    }
}

#[cfg(test)]
mod tests {
    use std::mem::zeroed;
    use std::ptr::NonNull;
    use std::sync::atomic::Ordering::{Relaxed, SeqCst};
    use std::sync::atomic::{AtomicPtr, AtomicUsize};
    use std::thread;

    use crate::smr::{increment_era, load, load_era, retire};

    #[test]
    fn test_protect_retire_miri() {
        test_protect_retire::<5, 30>();
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_protect_retire_no_miri() {
        test_protect_retire::<64, 50>();
    }

    struct Obj<T> {
        val: T,
        birth_era: u64,
    }

    fn test_protect_retire<const THREADS: usize, const MAX_VAL: usize>() {
        let counts: [AtomicUsize; MAX_VAL] = unsafe { zeroed() };
        let x = AtomicPtr::new(Box::into_raw(Box::new(Obj {
            val: 0,
            birth_era: load_era(),
        })));

        thread::scope(|scope| {
            for _ in 0..THREADS {
                scope.spawn(|| {
                    for val in 0..MAX_VAL {
                        if let Some(guard) = load(&x) {
                            unsafe {
                                counts[(*guard.as_ptr()).val].fetch_add(1, Relaxed);
                            }
                        }
                        let obj = Obj {
                            val,
                            birth_era: load_era(),
                        };
                        let swapped = x.swap(Box::into_raw(Box::new(obj)), SeqCst);
                        if let Some(to_retire) = NonNull::<u8>::new(swapped as *mut u8) {
                            unsafe {
                                retire(
                                    to_retire,
                                    dealloc_boxed_ptr::<Obj<usize>>,
                                    (*swapped).birth_era,
                                );
                            }
                        }
                        increment_era();
                    }
                });
            }
        });

        let total = counts.iter().fold(0, |x, y| x + y.load(Relaxed));
        assert_eq!(total, THREADS * MAX_VAL);

        unsafe {
            drop(Box::from_raw(x.load(Relaxed)));
        }
    }

    fn dealloc_boxed_ptr<T>(p: NonNull<u8>) {
        unsafe {
            drop(Box::from_raw(p.as_ptr() as *mut T));
        }
    }
}
