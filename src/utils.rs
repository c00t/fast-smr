use std::mem::{take, zeroed};
use std::ptr::null_mut;
use std::sync::atomic::Ordering::{Acquire, Relaxed, SeqCst};
use std::sync::atomic::{AtomicPtr, AtomicUsize};

// A specialized lock-free stack.
pub(crate) struct Stack<T> {
    head: AtomicPtr<Node<T>>,
}

impl<T> Stack<T> {
    pub(crate) const fn new() -> Self {
        Self {
            head: AtomicPtr::new(null_mut()),
        }
    }
    pub(crate) fn insert(&self, item: T) {
        let mut next = self.head.load(SeqCst);
        let node = Box::into_raw(Box::new(Node { item, next }));
        // CAS loop, so not wait-free.
        while let Err(head) = self.head.compare_exchange(next, node, SeqCst, SeqCst) {
            next = head;
            unsafe {
                (*node).next = next;
            }
        }
    }
}

impl<T: Default> Stack<T> {
    pub(crate) fn take_all(&self) -> Vec<T> {
        let mut result = Vec::default();
        let mut node_ptr = self.head.swap(null_mut(), SeqCst);
        while !node_ptr.is_null() {
            unsafe {
                result.push(take(&mut (*node_ptr).item));
                let next = (*node_ptr).next;
                drop(Box::from_raw(node_ptr));
                node_ptr = next;
            }
        }
        result
    }
}

impl<T> Drop for Stack<T> {
    fn drop(&mut self) {
        let mut node_ptr = self.head.swap(null_mut(), Relaxed);
        while !node_ptr.is_null() {
            unsafe {
                let next = (*node_ptr).next;
                drop(Box::from_raw(node_ptr));
                node_ptr = next;
            }
        }
    }
}

struct Node<T> {
    item: T,
    next: *mut Self,
}

// A specialized lock-free unrolled linked list.
#[repr(C)]
#[allow(clippy::upper_case_acronyms)]
pub(crate) struct ULL<T, const N: usize> {
    pub(crate) head: ULLNode<T, N>,
    pub(crate) len: AtomicUsize,
}

#[repr(C)]
pub(crate) struct ULLNode<T, const N: usize> {
    pub(crate) items: [T; N],
    pub(crate) next: AtomicPtr<Self>,
}

impl<T, const N: usize> ULLNode<T, N> {
    pub(crate) unsafe fn get_or_init_next(&self) -> &Self {
        let next = self.next.load(SeqCst);
        if !next.is_null() {
            return &*next;
        }
        let new_node = Box::into_raw(Box::new(Self {
            items: zeroed(),
            next: AtomicPtr::default(),
        }));
        match self
            .next
            .compare_exchange(null_mut(), new_node, SeqCst, SeqCst)
        {
            Ok(_) => &*new_node,
            Err(existing) => {
                drop(Box::from_raw(new_node));
                &*existing
            }
        }
    }
}

impl<T, const N: usize> Drop for ULLNode<T, N> {
    fn drop(&mut self) {
        let next = self.next.load(Acquire);
        if !next.is_null() {
            unsafe {
                drop(Box::from_raw(next));
            }
        }
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a ULL<T, N> {
    type Item = &'a T;
    type IntoIter = ULLIter<'a, T, N>;

    fn into_iter(self) -> Self::IntoIter {
        ULLIter {
            node: &self.head,
            index: 0,
            len: self.len.load(Acquire),
        }
    }
}

pub(crate) struct ULLIter<'a, T, const N: usize> {
    node: &'a ULLNode<T, N>,
    index: usize,
    len: usize,
}

impl<'a, T, const N: usize> Iterator for ULLIter<'a, T, N> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index == self.len {
            return None;
        }
        if self.index > 0 && self.index % N == 0 {
            self.node = unsafe { &*self.node.next.load(Acquire) };
        }
        let item = &self.node.items[self.index % N];
        self.index += 1;
        Some(item)
    }
}

#[cfg(test)]
mod tests {
    use std::mem::zeroed;
    use std::sync::atomic::Ordering::{Relaxed, SeqCst};
    use std::sync::atomic::{AtomicBool, AtomicUsize};
    use std::thread;

    use crate::utils::Stack;

    #[test]
    fn test_sync_list() {
        const THREADS_COUNT: usize = 10;
        const MAX_VAL: usize = 200;

        let list = Stack::new();

        let counts: Vec<AtomicUsize> = (0..MAX_VAL).map(|_| AtomicUsize::default()).collect();

        thread::scope(|scope| {
            for _ in 0..THREADS_COUNT {
                scope.spawn(|| {
                    for i in 0..MAX_VAL {
                        list.insert(i);
                    }
                    for x in list.take_all() {
                        counts[x].fetch_add(1, Relaxed);
                    }
                });
            }
        });

        list.insert(0); // make sure the drop impl is correct (no memory leak).

        for count in &counts {
            assert_eq!(count.load(Relaxed), THREADS_COUNT);
        }
    }

    #[test]
    fn test_length_logic() {
        const THREADS_COUNT: usize = 20;

        // this test mimics the logic of updating the length of the ULL in Reclaimer.

        static SLOTS: [AtomicBool; THREADS_COUNT] = unsafe { zeroed() };
        static LEN: AtomicUsize = AtomicUsize::new(0);

        let join = || {
            let mut index = 0;
            while SLOTS[index]
                .compare_exchange(false, true, SeqCst, Relaxed)
                .is_err()
            {
                index += 1;
            }
            let mut len = LEN.load(SeqCst);
            while index + 1 > len {
                match LEN.compare_exchange(len, index + 1, SeqCst, SeqCst) {
                    Ok(_) => break,
                    Err(l) => len = l,
                }
            }
            index
        };

        let decrease_length_from = |index: usize| {
            for i in (0..index + 1).rev() {
                // temporarily claim the slot for purposes of shrinking the list.
                if i < index
                    && SLOTS[i]
                        .compare_exchange(false, true, SeqCst, Relaxed)
                        .is_err()
                {
                    break;
                }
                let should_shrink = LEN.compare_exchange(i + 1, i, SeqCst, Relaxed).is_ok();
                SLOTS[i].store(false, SeqCst);
                if !should_shrink {
                    continue;
                }
            }
        };

        thread::scope(|scope| {
            for _ in 0..THREADS_COUNT {
                scope.spawn(|| {
                    decrease_length_from(join());
                });
            }
        });

        assert_eq!(LEN.load(Relaxed), 0);
    }
}
