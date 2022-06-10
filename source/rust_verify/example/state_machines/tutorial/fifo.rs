#![allow(unused_imports)]

// port of single-producer single-consumer queue from LinearDafny
// https://github.com/vmware-labs/verified-betrfs/tree/concurrency-experiments/concurrency/spsc-queue

// ANCHOR:full
use builtin::*;
use builtin_macros::*;
mod pervasive;
use pervasive::*;
use pervasive::multiset::*;
use pervasive::vec::*;
use pervasive::option::*;
use pervasive::map::*;
use pervasive::ptr::*;
use pervasive::seq::*;
use pervasive::cell::*;
use pervasive::atomic::*;
use pervasive::modes::*;
use pervasive::invariant::*;
use std::sync::Arc;

use state_machines_macros::tokenized_state_machine;

// ANCHOR: enum_state
#[is_variant]
pub enum ProducerState {
    Idle(nat),        // local copy of tail
    Producing(nat),
}

#[is_variant]
pub enum ConsumerState {
    Idle(nat),        // local copy of head
    Consuming(nat),
}
// ANCHOR_END: enum_state

// ANCHOR: fields
tokenized_state_machine!{FifoQueue<T> {
    fields {
        // IDs of the cells used in the ring buffer.
        // These are fixed throughout the protocol.

        #[sharding(constant)]
        pub backing_cells: Seq<int>,

        // All the stored permissions

        #[sharding(storage_map)]
        pub storage: Map<nat, cell::Permission<T>>,

        // Represents the shared `head` field

        #[sharding(variable)]
        pub head: nat,

        // Represents the shared `tail` field

        #[sharding(variable)]
        pub tail: nat,

        // Represents the local state of the single-producer

        #[sharding(variable)]
        pub producer: ProducerState,

        // Represents the local state of the single-consumer

        #[sharding(variable)]
        pub consumer: ConsumerState,
    }
    // ANCHOR_END: fields

    #[spec]
    fn len(&self) -> nat {
        self.backing_cells.len()
    }

    // ANCHOR: inc_wrap
    #[spec] #[verifier(publish)]
    pub fn inc_wrap(i: nat, len: nat) -> nat {
        if i + 1 == len { 0 } else { i + 1 }
    }
    // ANCHOR_END: inc_wrap

    // Make sure the producer state and the consumer state aren't inconsistent.

    #[invariant]
    pub fn not_overlapping(&self) -> bool {
        match (self.producer, self.consumer) {
            (ProducerState::Producing(tail), ConsumerState::Idle(head)) => {
                Self::inc_wrap(tail, self.len()) != head
            }
            (ProducerState::Producing(tail), ConsumerState::Consuming(head)) => {
                head != tail
                && Self::inc_wrap(tail, self.len()) != head
            }
            (ProducerState::Idle(tail), ConsumerState::Idle(head)) => {
                true
            }
            (ProducerState::Idle(tail), ConsumerState::Consuming(head)) => {
                head != tail
            }
        }
    }

    // `head` and `tail` are in-bounds
    // shared `head` and `tail` fields agree with the ProducerState and ConsumerState

    #[invariant]
    pub fn in_bounds(&self) -> bool {
        0 <= self.head && self.head < self.len() &&
        0 <= self.tail && self.tail < self.len()
        && match self.producer {
            ProducerState::Producing(tail) => {
                self.tail == tail
            }
            ProducerState::Idle(tail) => {
                self.tail == tail
            }
        }
        && match self.consumer {
            ConsumerState::Consuming(head) => {
                self.head == head
            }
            ConsumerState::Idle(head) => {
                self.head == head
            }
        }
    }

    // Indicates whether we expect the cell at index `i` to be full based on
    // the values of the `head` and `tail`.

    #[spec]
    fn in_active_range(&self, i: nat) -> bool {
        // Note that self.head = self.tail means empty range
        0 <= i && i < self.len() && (
            if self.head <= self.tail {
                self.head <= i && i < self.tail
            } else {
                i >= self.head || i < self.tail
            }
        )
    }

    // Indicates whether we expect a cell to be checked out or not,
    // based on the producer/consumer state.

    #[spec]
    fn is_checked_out(&self, i: nat) -> bool {
        equal(self.producer, ProducerState::Producing(i))
        || equal(self.consumer, ConsumerState::Consuming(i))
    }

    // Predicate to determine that the state at cell index `i`
    // is correct. For each index, there are three possibilities:
    //
    //  1. No cell permission is stored
    //  2. Permission is stored; permission indicates a full cell
    //  3. Permission is stored; permission indicates an empty cell
    //
    // Which of these 3 possibilities we should be in depends on the
    // producer/consumer/head/tail state.

    #[spec]
    fn valid_storage_at_idx(&self, i: nat) -> bool {
        if self.is_checked_out(i) {
            // No cell permission is stored
            !self.storage.dom().contains(i)
        } else {
            // Permission is stored
            self.storage.dom().contains(i)

            // Permission must be for the correct cell:
            && equal(
                self.storage.index(i).pcell,
                self.backing_cells.index(i)
            )

            && if self.in_active_range(i) {
                // The cell is full
                self.storage.index(i).value.is_Some()
            } else {
                // The cell is empty
                self.storage.index(i).value.is_None()
            }
        }
    }

    #[invariant]
    pub fn valid_storage_all(&self) -> bool {
        forall(|i| 0 <= i && i < self.len() >>=
            self.valid_storage_at_idx(i))
    }

    init!{
        initialize(backing_cells: Seq<int>, storage: Map<nat, cell::Permission<T>>) {
            // Upon initialization, the user needs to deposit _all_ the relevant
            // cell permissions to start with. Each permission should indicate
            // an empty cell.

            require(
                forall(|i| 0 <= i && i < backing_cells.len() >>=
                    #[trigger] storage.dom().contains(i)
                    && equal(
                        storage.index(i).pcell,
                        backing_cells.index(i)
                    )
                    && storage.index(i).value.is_None(),
                )
            );
            require(backing_cells.len() > 0);

            init backing_cells = backing_cells;
            init storage = storage;
            init head = 0;
            init tail = 0;
            init producer = ProducerState::Idle(0);
            init consumer = ConsumerState::Idle(0);
        }
    }

    // ANCHOR: transition_produce_start
    transition!{
        produce_start() {
            // In order to begin, we have to be in ProducerState::Idle.
            require(pre.producer.is_Idle());

            // We'll be comparing the producer's _local_ copy of the tail
            // with the _shared_ version of the head.
            let tail = pre.producer.get_Idle_0();
            let head = pre.head;

            assert(0 <= tail && tail < pre.backing_cells.len());

            // Compute the incremented tail, wrapping around if necessary.
            let next_tail = Self::inc_wrap(tail, pre.backing_cells.len());

            // We have to check that the buffer isn't full to proceed.
            require(next_tail != head);

            // Update the producer's local state to be in the `Producing` state.
            update producer = ProducerState::Producing(tail);

            // Withdraw ("check out") the permission stored at index `tail`.
            // This creates a proof obligation for the transition system to prove that
            // there is actually a permission stored at this index.
            withdraw storage -= [tail => let perm] by {
                assert(pre.valid_storage_at_idx(tail));
            };

            // The transition needs to guarantee to the client that the
            // permission they are checking out:
            //  (i) is for the cell at index `tail` (the IDs match)
            //  (ii) the permission indicates that the cell is empty
            assert(
                equal(perm.pcell, pre.backing_cells.index(tail))
                && perm.value.is_None()
            ) by {
                assert(!pre.in_active_range(tail));
                assert(pre.valid_storage_at_idx(tail));
            };
        }
    }
    // ANCHOR_END: transition_produce_start

    // ANCHOR: transition_produce_end
    transition!{
        // This transition is parameterized by the value of the permission
        // being inserted. Since the permission is being deposited
        // (coming from "outside" the system) we can't compute it as a
        // function of the current state, unlike how we did it for the
        // `produce_start` transition).
        produce_end(perm: cell::Permission<T>) {
            // In order to complete the produce step,
            // we have to be in ProducerState::Producing.
            require(pre.producer.is_Producing());
            let tail = pre.producer.get_Producing_0();

            assert(0 <= tail && tail < pre.backing_cells.len());

            // Compute the incremented tail, wrapping around if necessary.
            let next_tail = Self::inc_wrap(tail, pre.backing_cells.len());

            // This time, we don't need to compare the `head` and `tail` - we already
            // check that, and anyway, we don't have access to the `head` field
            // for this transition. (This transition is supposed to occur while
            // modifying the `tail` field, so we can't do both.)

            // However, we _do_ need to check that the permission token being
            // checked in satisfies its requirements. It has to be associated
            // with the correct cell, and it has to be full.

            require(equal(perm.pcell, pre.backing_cells.index(tail))
              && perm.value.is_Some());

            // Perform our updates. Update the tail to the computed value,
            // both the shared version and the producer's local copy.
            // Also, move back to the Idle state.
            update producer = ProducerState::Idle(next_tail);
            update tail = next_tail;

            // Check the permission back into the storage map.
            deposit storage += [tail => perm] by { assert(pre.valid_storage_at_idx(tail)); };
        }
    }
    // ANCHOR_END: transition_produce_end

    transition!{
        consume_start() {
            // In order to begin, we have to be in ConsumerState::Idle.
            require(pre.consumer.is_Idle());

            // We'll be comparing the consumer's _local_ copy of the head
            // with the _shared_ version of the tail.
            let head = pre.consumer.get_Idle_0();
            let tail = pre.tail;

            assert(0 <= head && head < pre.backing_cells.len());

            // We have to check that the buffer isn't empty to proceed.
            require(head != tail);

            // Update the consumer's local state to be in the `Consuming` state.
            update consumer = ConsumerState::Consuming(head);

            // Withdraw ("check out") the permission stored at index `tail`.

            birds_eye let perm = pre.storage.index(head);
            withdraw storage -= [head => perm] by {
                assert(pre.valid_storage_at_idx(head));
            };

            assert(equal(perm.pcell, pre.backing_cells.index(head))) by {
                assert(pre.valid_storage_at_idx(head));
            };
            assert(perm.value.is_Some()) by {
                assert(pre.in_active_range(head));
                assert(pre.valid_storage_at_idx(head));
            };
        }
    }

    transition!{
        consume_end(perm: cell::Permission<T>) {
            require(pre.consumer.is_Consuming());
            let head = pre.consumer.get_Consuming_0();

            assert(0 <= head && head < pre.backing_cells.len());
            let next_head = Self::inc_wrap(head, pre.backing_cells.len());

            update consumer = ConsumerState::Idle(next_head);
            update head = next_head;

            require(equal(perm.pcell, pre.backing_cells.index(head))
              && perm.value.is_None());
            deposit storage += [head => perm] by { assert(pre.valid_storage_at_idx(head)); };
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, backing_cells: Seq<int>, storage: Map<nat, cell::Permission<T>>) {
        assert_forall_by(|i| {
            requires(0 <= i && i < post.len());
            ensures(post.valid_storage_at_idx(i));

            assert(post.storage.dom().contains(i));
            /*
            assert(equal(
                post.storage.index(i).pcell,
                post.backing_cells.index(i)
            ));
            assert(if post.in_active_range(i) {
                post.storage.index(i).value.is_Some()
            } else {
                post.storage.index(i).value.is_None()
            });*/
        });
    }

    //// Invariant proofs

    #[inductive(produce_start)]
    fn produce_start_inductive(pre: Self, post: Self) {
        let tail = pre.producer.get_Idle_0();
        assert(!pre.in_active_range(tail));
        match (post.producer, post.consumer) {
            (ProducerState::Producing(tail), ConsumerState::Idle(head)) => {
                assert(Self::inc_wrap(tail, post.len()) != head);
            }
            (ProducerState::Producing(tail), ConsumerState::Consuming(head)) => {
                assert(head != tail);
                assert(Self::inc_wrap(tail, post.len()) != head);
            }
            (ProducerState::Idle(tail), ConsumerState::Idle(head)) => {
            }
            (ProducerState::Idle(tail), ConsumerState::Consuming(head)) => {
                assert(head != tail);
            }
        }
        assert(forall(|i| pre.valid_storage_at_idx(i) >>= post.valid_storage_at_idx(i)));
    }

    #[inductive(produce_end)]
    fn produce_end_inductive(pre: Self, post: Self, perm: cell::Permission<T>) {
        assert_forall_by(|i| {
            requires(pre.valid_storage_at_idx(i));
            ensures(post.valid_storage_at_idx(i));

            /*if post.is_checked_out(i) {
                assert(!post.storage.dom().contains(i));
            } else {
                assert(post.storage.dom().contains(i));
                assert(equal(
                    post.storage.index(i).pcell,
                    post.backing_cells.index(i)
                ));
                assert(if post.in_active_range(i) {
                    post.storage.index(i).value.is_Some()
                } else {
                    post.storage.index(i).value.is_None()
                });
            }*/
        });
    }

    #[inductive(consume_start)]
    fn consume_start_inductive(pre: Self, post: Self) {
        assert_forall_by(|i| {
            requires(pre.valid_storage_at_idx(i));
            ensures(post.valid_storage_at_idx(i));
        });
    }
   
    #[inductive(consume_end)]
    fn consume_end_inductive(pre: Self, post: Self, perm: cell::Permission<T>) {
        let head = pre.consumer.get_Consuming_0();
        assert(post.storage.dom().contains(head));
        assert(equal(
                post.storage.index(head).pcell,
                post.backing_cells.index(head)
            ));
        assert(if post.in_active_range(head) {
                post.storage.index(head).value.is_Some()
            } else {
                post.storage.index(head).value.is_None()
            });

        match (pre.producer, pre.consumer) {
            (ProducerState::Producing(tail), ConsumerState::Idle(head)) => {
                assert(pre.head != pre.tail);
            }
            (ProducerState::Producing(tail), ConsumerState::Consuming(head)) => {
                assert(pre.head != pre.tail);
            }
            (ProducerState::Idle(tail), ConsumerState::Idle(head)) => {
                assert(pre.head != pre.tail);
            }
            (ProducerState::Idle(tail), ConsumerState::Consuming(head)) => {
                assert(pre.head != pre.tail);
            }
        };

        assert(pre.head != pre.tail);
        assert(!post.is_checked_out(head));
        assert(post.valid_storage_at_idx(head));

        assert_forall_by(|i| {
            requires(pre.valid_storage_at_idx(i));
            ensures(post.valid_storage_at_idx(i));
        });
    }
}}

// ANCHOR: impl_queue_struct
#[proof]
struct HeadTailTokens<T> {
    #[proof] head: FifoQueue::head<T>,
    #[proof] tail: FifoQueue::tail<T>,

    #[proof] head_perm: PermissionU64,
    #[proof] tail_perm: PermissionU64,
}

impl<T> HeadTailTokens<T> {
    #[spec]
    pub fn wf(&self, instance: FifoQueue::Instance<T>,
            head_id: int, tail_id: int) -> bool {
           equal(self.head.instance, instance)
        && equal(self.tail.instance, instance)
        && equal(self.head_perm.patomic, head_id)
        && equal(self.tail_perm.patomic, tail_id)
        && equal(self.head_perm.value as nat, self.head.value)
        && equal(self.tail_perm.value as nat, self.tail.value)
    }
}

struct Queue<T> {
    buffer: Vec<PCell<T>>,
    head: PAtomicU64,
    tail: PAtomicU64,

    #[proof] instance: FifoQueue::Instance<T>,
    #[proof] inv: AtomicInvariant<HeadTailTokens<T>>,
}

impl<T> Queue<T> {
    #[spec]
    pub fn wf(&self) -> bool {
        // The Cell IDs in the instance protocol match the cell IDs in the actual vector:
        self.instance.backing_cells().len() == self.buffer.view().len()
        && forall(|i: int| 0 <= i && i < self.buffer.view().len() as int >>=
            self.instance.backing_cells().index(i) ==
                self.buffer.view().index(i).id())

        // HeadTailTokens are well-formed:
        && forall(|v| self.inv.inv(v) ==
            v.wf(self.instance, self.head.id(), self.tail.id()))
    }
}
// ANCHOR_END: impl_queue_struct

// ANCHOR: impl_producer_struct
pub struct Producer<T> {
    queue: Arc<Queue<T>>,
    tail: usize,

    #[proof] producer: FifoQueue::producer<T>
}

impl<T> Producer<T> {
    #[spec]
    pub fn wf(&self) -> bool {
           (*self.queue).wf()
        && equal(self.producer.instance, (*self.queue).instance)
        && equal(self.producer.value, ProducerState::Idle(self.tail as nat))
        && ((self.tail as int) < (*self.queue).buffer.view().len())
    }
}
// ANCHOR_END: impl_producer_struct

// ANCHOR: impl_consumer_struct
pub struct Consumer<T> {
    queue: Arc<Queue<T>>,
    head: usize,

    #[proof] consumer: FifoQueue::consumer<T>
}

impl<T> Consumer<T> {
    #[spec]
    pub fn wf(&self) -> bool {
           (*self.queue).wf()
        && equal(self.consumer.instance, (*self.queue).instance)
        && equal(self.consumer.value, ConsumerState::Idle(self.head as nat))
        && (self.head as int) < (*self.queue).buffer.view().len()
    }
}
// ANCHOR_END: impl_consumer_struct

// ANCHOR: impl_new_queue
pub fn new_queue<T>(len: usize) -> (Producer<T>, Consumer<T>) {
    requires(len > 0);
    ensures(|pc: (Producer<T>, Consumer<T>)| [
        pc.0.wf(),
        pc.1.wf(),
    ]);

    // Initialize the vector to store the cells
    let mut backing_cells_vec = Vec::<PCell<T>>::empty();

    // Initialize map for the permissions to the cells
    // (keyed by the indices into the vector)
    #[proof] let mut perms = Map::<nat, cell::Permission<T>>::proof_empty();

    while backing_cells_vec.len() < len {
        invariant(
            forall(|j: int| 0 <= j && j < backing_cells_vec.len() as int >>=
                #[trigger] perms.dom().contains(j as nat)
                &&
                backing_cells_vec.index(j as nat).id() == perms.index(j as nat).pcell
                &&
                perms.index(j as nat).value.is_None()
            )
        );

        #[spec] let i = backing_cells_vec.len();
        
        let (cell, Proof(cell_perm)) = PCell::empty();
        backing_cells_vec.push(cell);

        perms.proof_insert(i, cell_perm);
    }

    // Vector for ids
    #[spec] let mut backing_cells_ids = Seq::<int>::new(
        backing_cells_vec.view().len(),
        |i| backing_cells_vec.view().index(i).id());

    // Initialize an instance of the FIFO queue
    #[proof] let (instance, head_token, tail_token, producer_token, consumer_token)
        = FifoQueue::Instance::initialize(backing_cells_ids, perms, perms);

    // Initialize atomics
    let (head_atomic, Proof(head_perm)) = PAtomicU64::new(0);
    let (tail_atomic, Proof(tail_perm)) = PAtomicU64::new(0);

    // Initialize the atomic invariant to store atomic tokens
    #[proof] let inv = AtomicInvariant::new(
        HeadTailTokens {
            head: head_token,
            tail: tail_token,
            head_perm,
            tail_perm,
        },
        |v| v.wf(instance, head_atomic.id(), tail_atomic.id()),
        0,
    );

    // Initialize the queue
    let queue = Queue::<T> {
        instance,
        head: head_atomic,
        tail: tail_atomic,
        inv: inv,
        buffer: backing_cells_vec,
    };

    // Share the queue between the producer and consumer
    let queue_arc = Arc::new(queue);

    let prod = Producer::<T> {
        queue: queue_arc.clone(),
        tail: 0,
        producer: producer_token,
    };

    let cons = Consumer::<T> {
        queue: queue_arc,
        head: 0,
        consumer: consumer_token,
    };

    (prod, cons)
}
// ANCHOR_END: impl_new_queue

// ANCHOR: impl_producer
impl<T> Producer<T> {
    fn enqueue(&mut self, t: T) {
        requires(old(self).wf());
        ensures(self.wf());

        // Loop: if the queue is full, then block until it is not.  
        loop {
            invariant(self.wf());

            let queue = &*self.queue;
            let len = queue.buffer.len();

            assert(0 <= self.tail && self.tail < len);

            // Calculate the index of the slot right after `tail`, wrapping around
            // if necessary. If the enqueue is successful, then we will be updating
            // the `tail` to this value.
            let next_tail = if self.tail + 1 == len { 0 } else { self.tail + 1 };

            let head;
            #[proof] let cell_perm;
            open_atomic_invariant!(&queue.inv => htt => {
                // Get the current `head` value from the shared atomic.
                head = queue.head.load(&htt.head_perm);

                // If `head != next_tail`, then we proceed with the operation.
                // We check here, ghostily, in the `open_atomic_invariant` block if that's the case.
                // If so, we proceed with the `produce_start` transition
                // and obtain the cell permission.
                cell_perm = if head != next_tail as u64 {
                    #[proof] let cp = queue.instance.produce_start(&htt.head, &mut self.producer);
                    Option::Some(cp)
                } else {
                    Option::None
                };
            });

            // Here's where we "actually" do the `head != next_tail` check:
            if head != next_tail as u64 {
                // Unwrap the cell_perm from the option.
                #[proof] let mut cell_perm = match cell_perm {
                    Option::Some(cp) => cp,
                    Option::None => { assert(false); proof_from_false() }
                };

                // Write the element t into the buffer, updating the cell
                // from uninitialized to initialized (to the value t).
                queue.buffer.index(self.tail).put(&mut cell_perm, t);

                // Store the updated tail to the shared `tail` atomic,
                // while performing the `produce_end` transition.
                open_atomic_invariant!(&queue.inv => htt => {
                    queue.tail.store(&mut htt.tail_perm, next_tail as u64);
                    queue.instance.produce_end(cell_perm,
                        cell_perm, &mut htt.tail, &mut self.producer);
                });

                self.tail = next_tail;

                return;
            }
        }
    }
}
// ANCHOR_END: impl_producer

// ANCHOR: impl_consumer
impl<T> Consumer<T> {
    fn deque(&mut self) -> T {
        requires(old(self).wf());
        ensures(|t: T| self.wf());

        loop {
            invariant(self.wf());

            let queue = &*self.queue;
            let len = queue.buffer.len();

            assert(0 <= self.head && self.head < len);

            let next_head = if self.head + 1 == len { 0 } else { self.head + 1 };

            let tail;
            #[proof] let cell_perm;
            open_atomic_invariant!(&queue.inv => htt => {
                tail = queue.tail.load(&htt.tail_perm);

                cell_perm = if self.head as u64 != tail {
                    #[proof] let (_, cp) = queue.instance.consume_start(&htt.tail, &mut self.consumer);
                    Option::Some(cp)
                } else {
                    Option::None
                };
            });

            if self.head as u64 != tail {
                #[proof] let mut cell_perm = match cell_perm {
                    Option::Some(cp) => cp,
                    Option::None => { assert(false); proof_from_false() }
                };
                let t = queue.buffer.index(self.head).take(&mut cell_perm);

                open_atomic_invariant!(&queue.inv => htt => {
                    queue.head.store(&mut htt.head_perm, next_head as u64);
                    queue.instance.consume_end(cell_perm,
                        cell_perm, &mut htt.head, &mut self.consumer);
                });

                self.head = next_head;
                
                return t;
            }
        }
    }
}
// ANCHOR_END: impl_consumer
// ANCHOR_END: full

fn main() { }