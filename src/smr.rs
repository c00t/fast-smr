use std::cell::{Cell, RefCell};
use std::cmp::max;
use std::collections::VecDeque;
use std::mem::zeroed;
use std::ptr::NonNull;
use std::sync::atomic::Ordering::{Relaxed, SeqCst};
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicU64};

use crate::utils::{Stack, ULL};

const SLOTS_PER_NODE: usize = 8;

pub struct Reclaimer {
    slots: ULL<Slot, SLOTS_PER_NODE>,

    // the global era value.
    era: AtomicU64,

    // limbo lists may be transferred here on drop.
    drop_cache: Stack<Vec<RetiredFn>>,
}

impl Reclaimer {
    pub const fn new() -> Self {
        Self {
            slots: unsafe { zeroed() },
            era: AtomicU64::new(1),
            drop_cache: Stack::new(),
        }
    }
    pub fn join(&self, cleanup_freq: usize) -> ThreadContext<'_> {
        let mut node = &self.slots.head;
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
        let mut len = self.slots.len.load(SeqCst);
        while index + 1 > len {
            match self
                .slots
                .len
                .compare_exchange(len, index + 1, SeqCst, SeqCst)
            {
                Ok(_) => break,
                Err(l) => len = l,
            }
        }
        ThreadContext {
            reclaimer: self,
            slot: &node.items[index % SLOTS_PER_NODE],
            index,
            limbo_list: RefCell::new(self.drop_cache.take_all().into_iter().flatten().collect()),
            cleanup_freq,
            cleanup_counter: Cell::new(0),
            counts: RefCell::default(),
            intervals: RefCell::default(),
        }
    }
    pub fn increment_era(&self) {
        self.era.fetch_add(1, SeqCst);
    }
    pub fn load_era(&self) -> u64 {
        self.era.load(SeqCst)
    }
}

impl Default for Reclaimer {
    fn default() -> Self {
        Self::new()
    }
}

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

pub struct ThreadContext<'a> {
    reclaimer: &'a Reclaimer,
    slot: &'a Slot,
    index: usize,

    limbo_list: RefCell<Vec<RetiredFn>>,
    cleanup_freq: usize,
    cleanup_counter: Cell<usize>,

    // a monotonically increasing queue consisting of (era, count) tuples.
    counts: RefCell<VecDeque<(u64, usize)>>,
    // a reusable Vec for storing hazardous intervals when scanning slots.
    intervals: RefCell<Vec<(u64, u64)>>,
}

impl<'a> ThreadContext<'a> {
    pub fn load<T>(&self, src: &AtomicPtr<T>) -> Option<Guard<'_, 'a, T>> {
        self.protect(src, NonNull::new(src.load(SeqCst))?)
    }
    pub fn protect<T>(&self, src: &AtomicPtr<T>, ptr: NonNull<T>) -> Option<Guard<'_, 'a, T>> {
        let mut counts = self.counts.borrow_mut();
        let mut initial_end_era = 0;
        let mut era = self.reclaimer.era.load(SeqCst);
        if let Some(back) = counts.back_mut() {
            initial_end_era = back.0;
            if initial_end_era == era {
                // the current era was already protected by a previous call to this method.
                // simply increment the count of the last protected era.
                back.1 += 1;
                return Some(Guard {
                    ctx: self,
                    era,
                    ptr,
                });
            }
        }
        self.slot.end_era.store(era, SeqCst);
        while let Some(ptr) = NonNull::new(src.load(SeqCst)) {
            let next_era = self.reclaimer.era.load(SeqCst);
            if era == next_era {
                counts.push_back((era, 1));
                if counts.len() == 1 {
                    // this is our first reservation, so start_era must also be updated.
                    self.slot.start_era.store(era, SeqCst);
                }
                return Some(Guard {
                    ctx: self,
                    era,
                    ptr,
                });
            }
            era = next_era;
            self.slot.end_era.store(era, SeqCst);
        }
        // null ptrs don't need protection; reset end_era to what it was before.
        self.slot.end_era.store(initial_end_era, SeqCst);
        None
    }

    pub fn retire(&self, ptr: NonNull<u8>, f: fn(NonNull<u8>), birth_era: u64) {
        if self.cleanup_freq == 0 {
            panic!("cannot retire using this context: cleanup_freq is 0.")
        }
        self.cleanup_counter
            .set((self.cleanup_counter.get() + 1) % self.cleanup_freq);
        if self.cleanup_counter.get() == 0 {
            self.scan_and_cleanup();
        }
        let retire_era = self.reclaimer.era.load(SeqCst);
        self.limbo_list.borrow_mut().push(RetiredFn {
            ptr,
            f,
            span: (birth_era, retire_era),
        });
    }

    fn scan_and_cleanup(&self) {
        let mut limbo_list = self.limbo_list.borrow_mut();
        let mut intervals = self.intervals.borrow_mut();

        // scan the global array of reservations.
        for slot in self.reclaimer.slots.into_iter() {
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
            intervals.push((start, end));
        }

        // merge the intervals.
        if intervals.len() > 1 {
            intervals.sort_unstable();
            let mut i = 1;
            for j in 1..intervals.len() {
                let (start, end) = intervals[j];
                // [(1, 2), (3, 4)] can be merged into [(1, 4)].
                if start <= intervals[i - 1].1 + 1 {
                    intervals[i - 1].1 = max(end, intervals[i - 1].1);
                } else {
                    intervals[i] = (start, end);
                    i += 1;
                }
            }
            intervals.truncate(i);
        }

        // go through the limbo list and delete the entries without conflicts.
        let mut i = 0;
        while i < limbo_list.len() {
            let has_conflict = intervals
                .iter()
                .any(|x| intervals_overlap(limbo_list[i].span, *x));
            if has_conflict {
                i += 1;
            } else {
                limbo_list.swap_remove(i);
            }
        }
        intervals.clear();
    }
}

fn intervals_overlap(a: (u64, u64), b: (u64, u64)) -> bool {
    a.0 <= b.1 && b.0 <= a.1
}

impl<'a> Drop for ThreadContext<'a> {
    fn drop(&mut self) {
        debug_assert!(self.counts.borrow_mut().is_empty());
        self.scan_and_cleanup();
        if self.limbo_list.borrow_mut().len() > 0 {
            self.reclaimer.drop_cache.insert(self.limbo_list.take());
        }

        let mut nodes = vec![&self.reclaimer.slots.head];
        while let Some(next) = unsafe { nodes.last().unwrap().next.load(SeqCst).as_ref() } {
            nodes.push(next);
        }
        for i in (0..self.index + 1).rev() {
            let slot = &nodes[i / SLOTS_PER_NODE].items[i % SLOTS_PER_NODE];
            // temporarily claim the slot for purposes of shrinking the list length.
            if i < self.index && !slot.try_claim() {
                break;
            }
            let succeeded = self
                .reclaimer
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

pub struct Guard<'a, 'b: 'a, T> {
    ctx: &'b ThreadContext<'a>,
    era: u64,
    ptr: NonNull<T>,
}

impl<'a, 'b: 'a, T> Guard<'a, 'b, T> {
    pub fn as_ptr(&self) -> *mut T {
        self.ptr.as_ptr()
    }
}

impl<'a, 'b: 'a, T> Drop for Guard<'a, 'b, T> {
    fn drop(&mut self) {
        let mut counts = self.ctx.counts.borrow_mut();

        // decrement the count.
        let pair = counts.iter_mut().find(|(e, _)| *e == self.era).unwrap();
        pair.1 -= 1;

        let mut start_era_changed = false;
        let mut end_era_changed = false;

        // pop from the front and back of the queue to shrink the interval.
        while let Some((_, count)) = counts.front() {
            if *count > 0 {
                break;
            }
            counts.pop_front();
            start_era_changed = true;
        }
        while let Some((_, count)) = counts.back() {
            if *count > 0 {
                break;
            }
            counts.pop_back();
            end_era_changed = true;
        }

        // update our interval.
        if counts.is_empty() {
            // we have no more reservations; zero out our interval.
            self.ctx.slot.end_era.store(0, SeqCst);
            self.ctx.slot.start_era.store(0, SeqCst);
        } else if start_era_changed {
            self.ctx
                .slot
                .start_era
                .store(counts.front().unwrap().0, SeqCst);
        } else if end_era_changed {
            self.ctx
                .slot
                .end_era
                .store(counts.back().unwrap().0, SeqCst);
        }
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

    use crate::smr::Reclaimer;

    struct Obj<T> {
        val: T,
        birth_era: u64,
    }

    #[test]
    fn test_protect_retire() {
        const THREADS_COUNT: usize = 32;
        const MAX_VAL: usize = 10;

        let r = Reclaimer::new();

        let counts: [AtomicUsize; MAX_VAL] = unsafe { zeroed() };

        let x = AtomicPtr::new(Box::into_raw(Box::new(Obj {
            val: 0,
            birth_era: r.load_era(),
        })));

        thread::scope(|scope| {
            for _ in 0..THREADS_COUNT {
                scope.spawn(|| {
                    let ctx = r.join(1);
                    for val in 0..MAX_VAL {
                        if let Some(guard) = ctx.load(&x) {
                            unsafe {
                                counts[(*guard.as_ptr()).val].fetch_add(1, Relaxed);
                            }
                        }
                        let obj = Obj {
                            val,
                            birth_era: r.load_era(),
                        };
                        let swapped = x.swap(Box::into_raw(Box::new(obj)), SeqCst);
                        if let Some(to_retire) = NonNull::<u8>::new(swapped as *mut u8) {
                            unsafe {
                                ctx.retire(
                                    to_retire,
                                    dealloc_boxed_ptr::<Obj<usize>>,
                                    (*swapped).birth_era,
                                );
                            }
                        }
                        r.increment_era();
                    }
                });
            }
        });

        assert_eq!(r.slots.len.load(Relaxed), 0);

        let total = counts.iter().fold(0, |x, y| x + y.load(Relaxed));
        assert_eq!(total, THREADS_COUNT * MAX_VAL);

        unsafe {
            drop(Box::from_raw(x.load(Relaxed)));
        }
    }

    fn dealloc_boxed_ptr<T>(p: NonNull<u8>) {
        unsafe {
            drop(Box::from_raw(p.as_ptr() as *mut T));
        }
    }

    #[test]
    fn test_reclaimer_join_leave() {
        const TRIALS: usize = 10;
        const THREADS_COUNT: usize = 10;

        let r = Reclaimer::new();

        for _ in 0..TRIALS {
            thread::scope(|scope| {
                for _ in 0..THREADS_COUNT {
                    scope.spawn(|| drop(r.join(0)));
                }
            });
            assert_eq!(r.slots.len.load(Relaxed), 0);
        }
    }
}
