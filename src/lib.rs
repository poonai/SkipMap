#![feature(allocator_api, rustc_private, test)]
extern crate arena;
extern crate rand;
use std::alloc::{Alloc, Global, Layout};
use std::cmp::Ordering;
use std::marker::PhantomData;
use std::mem;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering::*;
// Logic for memory management
// Once Node is created, it'll be dellocated only if the skip
// list goes down.
// Our implementation allows updation, (i.e) value will be updated
// but value won't be dropped cuz we not having any reference count
// of the value, so whenever update happens on a node we'll replace the node
// value reference by new. (This would be a atomic instruction)
// In order to drop the value, we'll have the reference of the value in the SkipMap
// when the skop is going down, we'll deallocate the node after we'll dellocate the
// created value. We are doing this to avoid new node creation on updation
// The list which maintains the referernce on the value will be mutex lock
// basically insert and read will be lock free
// update will be lock, since we have to deallocate the memory
// Guys if you have better idea, I would be happy to hear.

// non generic idea, we can give the reference of the value to the user
// It is upto them to deallocate. but I won't be implementing now. This for the people
// who want to tweak and play.

/// Node contains the data, this will be allocated in the heap
/// we'll be having only the reference of the node. I'll be dropped
/// once the SkipMap drops
struct Node<K, V> {
    key: K,
    value: V,
    lanes: [AtomicUsize; 25],
}
impl<K: Ord + Clone, V> Node<K, V> {
    pub fn new_addr(key: K, val: V) -> usize {
        let node_layout = Layout::new::<Node<K, V>>();
        let alloc: *mut u8 = unsafe {
            match Global.alloc(node_layout) {
                Ok(byte) => byte.as_ptr(),
                Err(_e) => panic!("not able to allocate da"),
            }
        };
        let node = alloc as *mut Node<K, V>;
        unsafe {
            (*node).key = key;
            (*node).value = val;
            (*node).lanes = mem::zeroed();
        }
        node as usize
    }

    // node set at can be used only if the lane is uninitialized
    fn set_at(&self, addr: usize, height: usize) -> bool {
        let atomic_ref = unsafe { self.lanes.get_unchecked(height) };
        if 0 == atomic_ref.compare_and_swap(0, addr, Relaxed) {
            return true;
        }
        false
    }
    fn store(&self, addr: usize, height: usize) {
        let atomic_ref = unsafe { self.lanes.get_unchecked(height) };
        atomic_ref.store(addr, Relaxed);
    }
}
impl<K, V> Node<K, V> {
    fn get_at(&self, height: usize) -> Option<AtomicPtrs<K, V>> {
        let atomic_ref = unsafe { self.lanes.get_unchecked(height) };
        let addr = atomic_ref.load(Relaxed);
        if addr == 0 {
            return None;
        }
        return Some(AtomicPtrs {
            loaded_addr: addr,
            addr: atomic_ref,
            node: unsafe { mem::transmute(addr) },
        });
    }
    fn dealloc(&self) {
        let node_layout = Layout::new::<Node<K, V>>();
        unsafe {
            Global.dealloc(
                std::ptr::NonNull::new(self as *const Node<K, V> as *mut Node<K, V> as *mut u8)
                    .unwrap(),
                node_layout,
            );
        }
    }
}

/// AtomicPtrs is a helper struct which will be used for maintaing the state of the
/// atomic operations
struct AtomicPtrs<'a, K: 'a, V: 'a> {
    loaded_addr: usize,
    addr: &'a AtomicUsize,
    node: &'a Node<K, V>,
}

impl<'a, K: 'a, V: 'a> AtomicPtrs<'a, K, V> {
    fn compare_and_swap(&self, addr: usize) -> bool {
        if self.loaded_addr == self.addr.compare_and_swap(self.loaded_addr, addr, Relaxed) {
            return true;
        }
        return false;
    }
}

/// # SkipMap
/// containes the initial height lanes
/// In our implementation, we don't have any head node.
/// SkipMap is considered as head, It'll have mutiple lanes, which
/// holds the references of the heap allocated node.
/// Supported Operations.
/// 1) Insert
/// 2) Get
/// 3) Update (with lock)
pub struct SkipMap<K, V> {
    lanes: [AtomicUsize; 25],
    height: AtomicUsize,
    _key_type: PhantomData<K>,
    _value_type: PhantomData<V>,
}

pub fn random_height() -> usize {
    const MASK: u32 = 1 << 23;
    1 + (rand::random::<u32>() | MASK).trailing_zeros() as usize
}

impl<K, V> SkipMap<K, V> {
    fn get_at(&self, height: usize) -> Option<AtomicPtrs<K, V>> {
        let atomic_ref = unsafe { self.lanes.get_unchecked(height) };
        let addr = atomic_ref.load(Relaxed);
        if addr == 0 {
            return None;
        }
        return Some(AtomicPtrs {
            loaded_addr: addr,
            addr: atomic_ref,
            node: unsafe { mem::transmute(addr) },
        });
    }
}
impl<K: Ord + Clone, V: Clone> SkipMap<K, V> {
    /// return the uninitialized SkipMap
    pub fn new() -> SkipMap<K, V> {
        SkipMap {
            lanes: unsafe { mem::zeroed() },
            height: AtomicUsize::new(0),
            _value_type: unsafe { mem::uninitialized() },
            _key_type: unsafe { mem::uninitialized() },
        }
    }

    fn set_at(&self, addr: usize, height: usize) -> bool {
        let atomic_ref = unsafe { self.lanes.get_unchecked(height) };
        if 0 == atomic_ref.compare_and_swap(0, addr, Relaxed) {
            return true;
        }
        false
    }

    fn find(&self, key: &K) -> Option<&Node<K, V>> {
        // check first two node of the lane
        // whether to take the lane or not
        let mut height = self.height.load(Relaxed);
        let mut before: AtomicPtrs<K, V>;
        loop {
            before = match self.get_at(height) {
                Some(ptrs) => ptrs,
                None => {
                    if height > 0 {
                        height = height - 1;
                        continue;
                    }
                    return None;
                }
            };
            match before.node.key.cmp(key) {
                Ordering::Greater => {
                    if height > 0 {
                        height = height - 1;
                        continue;
                    }
                    return None;
                }
                Ordering::Equal => return Some(before.node),
                Ordering::Less => {
                    // check whether we can take this lane or not
                    let next: AtomicPtrs<K, V>;
                    loop {
                        next = match before.node.get_at(height) {
                            Some(ptrs) => ptrs,
                            None => {
                                if height > 0 {
                                    height = height - 1;
                                    continue;
                                }
                                return None;
                            }
                        };
                        break;
                    }

                    match next.node.key.cmp(key) {
                        Ordering::Greater => {
                            // don't take this lane get down
                            if height > 0 {
                                height = height - 1;
                                continue;
                            }
                            return None;
                        }
                        Ordering::Equal => return Some(next.node),
                        Ordering::Less => {
                            // take this lane and get ready for the next iteration
                            before = next;
                            break;
                        }
                    }
                }
            };
        }
        loop {
            match before.node.key.cmp(&key) {
                Ordering::Greater => loop {
                    if height > 0 {
                        height = height - 1;
                        before = match before.node.get_at(height) {
                            Some(ptrs) => ptrs,
                            None => {
                                continue;
                            }
                        };
                        break;
                    }
                    return None;
                },
                Ordering::Equal => return Some(before.node),
                Ordering::Less => {
                    // go right.
                    let mut next: AtomicPtrs<K, V>;
                    // check which lane next node has lesser
                    // value from there take right
                    loop {
                        next = match before.node.get_at(height) {
                            Some(ptrs) => ptrs,
                            None => {
                                if height > 0 {
                                    height = height - 1;
                                    continue;
                                }
                                return None;
                            }
                        };
                        match next.node.key.cmp(&key) {
                            Ordering::Greater => loop {
                                if height > 0 {
                                    height = height - 1;
                                    break;
                                }
                                return None;
                            },
                            Ordering::Less => {
                                before = next;
                                break;
                            }
                            Ordering::Equal => return Some(next.node),
                        };
                    }
                }
            }
        }
    }
    pub fn get(&self, key: &K) -> Option<&V> {
        match self.find(key) {
            Some(node) => {
                return Some(&node.value);
            }
            None => None,
        }
    }
    /// Inserts data into the SkipMap
    pub fn insert(&self, key: K, value: V) -> bool {
        //check for update
        match self.find(&key) {
            Some(_node) => {
                return false;
            }
            None => {}
        };

        // Insert from base
        let height = random_height();
        let current_height = self.height.load(Relaxed);

        if height > current_height {
            self.height
                .compare_and_swap(current_height, height, Relaxed);
        }
        let x_addr = Node::new_addr(key.clone(), value);

        // will be used in setting the next addresss.
        let x_node: &Node<K, V> = unsafe { mem::transmute(x_addr) };
        // When your cas operation fails,
        // retry the insertion for that level alone.
        // Mostly it won't fail
        for i in 0..height {
            loop {
                let (before, after) = self.split_nodes_for_level(&key, i);
                let before = match before {
                    Some(before) => before,
                    None => {
                        // check whether afer also none
                        let after = match after {
                            Some(after) => after,
                            None => {
                                // case
                                // both before and after are none.
                                // i.e this is the initial node for
                                // this level.
                                // so do skip list insert.
                                if !self.set_at(x_addr, i) {
                                    // If more inserts happens.
                                    // No otherway we have. we just have to retry inserting.
                                    continue;
                                }
                                break;
                            }
                        };
                        // case
                        // first node itself greater than incoming node.
                        x_node.store(after.loaded_addr, i);
                        if !after.compare_and_swap(x_addr) {
                            // retry computation for this level
                            continue;
                        }
                        break;
                    }
                };

                let after = match after {
                    Some(ptr) => ptr,
                    None => {
                        //case that we don't have end node.
                        // we adding in the end of the level
                        if !before.node.set_at(x_addr, i) {
                            // recompute before and after
                            continue;
                        }
                        break;
                    }
                };

                //case we have both before and after.
                //no need to check for insertion cuz newly created node.
                x_node.store(after.loaded_addr, i);
                if !after.compare_and_swap(x_addr) {
                    // recompute before and after
                    continue;
                }
                break;
            }
        }
        true
    }
    fn split_nodes_for_level(
        &self,
        key: &K,
        height: usize,
    ) -> (Option<AtomicPtrs<K, V>>, Option<AtomicPtrs<K, V>>) {
        // if the level is not populated, both before and after will be none.
        // if the inital node is greater than insertion, then None, intial
        // if no last node then before and none.
        // otherwise befor and after node.
        let mut level = match self.get_at(height) {
            Some(ptr) => ptr,
            None => return (None, None),
        };
        let mut before: Option<AtomicPtrs<K, V>> = None;
        loop {
            match level.node.key.cmp(&key) {
                Ordering::Greater => return (before, Some(level)),
                Ordering::Equal => unreachable!(),
                Ordering::Less => {
                    level = match level.node.get_at(height) {
                        Some(ptr) => {
                            before = Some(level);
                            ptr
                        }
                        None => return (Some(level), None),
                    };
                }
            };
        }
    }
}

impl<K, V> Drop for SkipMap<K, V> {
    fn drop(&mut self) {
        //drop one bye one in the bottom
        let mut bottom = match self.get_at(0) {
            Some(node) => node,
            None => return,
        };
        loop {
            match bottom.node.get_at(0) {
                Some(ptrs) => {
                    bottom.node.dealloc();
                    bottom = ptrs;
                }
                None => {
                    break;
                }
            }
        }
    }
}
#[test]
fn test_split_nodes_for_level() {
    let skip_map: SkipMap<String, String> = SkipMap::new();
    let a_node = Node::new_addr(String::from("b"), 3);
    skip_map.set_at(a_node, 0);
    // testing all three cases
    // case 1:
    // before should be none
    // after should have value
    let (before, after) = skip_map.split_nodes_for_level(&String::from("a"), 0);
    match before {
        Some(_ptrs) => {
            unreachable!();
        }
        None => {}
    }
    match after {
        Some(ptrs) => {
            assert_eq!(ptrs.node.key, "b");
        }
        None => unreachable!(),
    }
    // case 2:
    // before should have value and after should be none
    let (before, after) = skip_map.split_nodes_for_level(&String::from("c"), 0);
    match after {
        Some(_ptrs) => {
            unreachable!();
        }
        None => {}
    }
    match before {
        Some(ptrs) => {
            assert_eq!(ptrs.node.key, "b");
        }
        None => unreachable!(),
    };
    let a_node_ref: &Node<String, String> = unsafe { mem::transmute(a_node) };
    let d_node = Node::new_addr(String::from("d"), 45);
    a_node_ref.set_at(d_node, 0);
    // case 3:
    // before and after should have value
    let (before, after) = skip_map.split_nodes_for_level(&String::from("c"), 0);
    match after {
        Some(ptrs) => {
            assert_eq!(ptrs.node.key, "d");
        }
        None => {
            unreachable!();
        }
    }
    match before {
        Some(ptrs) => {
            assert_eq!(ptrs.node.key, "b");
        }
        None => unreachable!(),
    }
}

unsafe impl<K: Send + Sync + Ord, V: Send + Sync> Send for SkipMap<K, V> {}
unsafe impl<K: Send + Sync + Ord, V: Send + Sync> Sync for SkipMap<K, V> {}

#[cfg(test)]
mod tests {

    use super::SkipMap;
    #[test]
    fn it_works() {
        let skip_map: SkipMap<String, String> = SkipMap::new();
        skip_map.insert(String::from("a"), String::from("1"));
        skip_map.insert(String::from("b"), String::from("2"));
        skip_map.insert(String::from("d"), String::from("4"));
        skip_map.insert(String::from("g"), String::from("7"));

        skip_map.insert(String::from("h"), String::from("8"));
        skip_map.insert(String::from("i"), String::from("9"));
        skip_map.insert(String::from("e"), String::from("6"));
        skip_map.insert(String::from("f"), String::from("5"));
        assert_eq!(skip_map.get(&String::from("a")).expect("expected 4"), "1");
        assert_eq!(skip_map.get(&String::from("g")).expect("expected 7"), "7");
    }

}
extern crate test;
use self::test::Bencher;
use std::sync::Arc;
use std::thread;
#[bench]
fn insert(b: &mut Bencher) {
    b.iter(|| {
        let SkipMap: SkipMap<usize, usize> = SkipMap::new();
        for i in 0..1_000 {
            SkipMap.insert(i, i);
        }
    });
}
#[bench]
fn insert_concurrent(b: &mut Bencher) {
    b.iter(|| {
        let SkipMap: SkipMap<usize, usize> = SkipMap::new();
        let arc_list = Arc::new(SkipMap);
        let mut threads = Vec::new();
        let list = arc_list.clone();
        let t = thread::spawn(move || {
            for i in 0..250 {
                list.insert(i, i);
            }
        });
        threads.push(t);
        let list = arc_list.clone();
        let t = thread::spawn(move || {
            for i in 251..500 {
                list.insert(i, i);
            }
        });
        threads.push(t);
        let list = arc_list.clone();
        let t = thread::spawn(move || {
            for i in 501..750 {
                list.insert(i, i);
            }
        });
        threads.push(t);
        let list = arc_list.clone();
        let t = thread::spawn(move || {
            for i in 751..1000 {
                list.insert(i, i);
            }
        });
        threads.push(t);
        for t in threads {
            t.join().unwrap();
        }
    })
}
