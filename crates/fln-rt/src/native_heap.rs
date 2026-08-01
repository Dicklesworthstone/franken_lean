//! The NativeHeap (plan §6.1b; bead fln-lld): the toolchain's own working
//! structures as typed handles with generational IDs — no obligation to the
//! ABI's layout.
//!
//! # What this is and what it is not
//!
//! The CompatHeap (fln-unsafe-abi) is the ABI's exact object model: pointer
//! identity, RC discipline, membrane-only allocation. The NativeHeap is the
//! other half of the two-heap architecture: Vellum trees, Athanor
//! transactions, Crucible terms, Ledger records live here as typed handles,
//! persistent/immutable where semantics allow. It is deliberately NOT the
//! ABI: no layout contract, no RC word, no membrane discipline — a handle is
//! a `(slot, generation, type)` triple, and every resolution misuse is a
//! typed error, never a raw pointer and never UB. The one assertion is the
//! programmer invariant, not a runtime fact: allocating on a closed heap is
//! a caller bug (the converters' region discipline), asserted rather than
//! modelled as a typed outcome.
//!
//! The handle semantics mirror asupersync's `RegionHeap`
//! (`HeapIndex{index, generation, type_id}` with ABA retirement at
//! `u32::MAX`) so that the substrate can move to the literal asupersync edge
//! mechanically if the dependency-universe call ever admits it. The measured
//! constraint (recorded on the bead): the franken_lean workspace carries zero
//! external crates, and asupersync's own tree pulls serde — so this module
//! is std-only with the same semantics, and the question stays routed.
//!
//! # The laws
//!
//! * **Handle authenticity.** A handle resolves only to its own live,
//!   same-generation, same-type allocation. A stale handle (freed, wrong
//!   generation, closed heap) is a typed error, never a wrong value.
//! * **ABA retirement.** A freed slot's generation advances; at `u32::MAX`
//!   the slot retires permanently rather than re-issue a generation a stale
//!   handle could still hold.
//! * **Persistent objects are never counted.** A persistent allocation
//!   refuses `free` and `get_mut` — immutable where semantics allow, exactly
//!   the tri-state law's `m_rc == 0` arm on this side of the membrane.
//! * **Total interning.** Values stored through `intern` dedup structurally:
//!   the same value returns the same live handle (R10's dedup), and a freed
//!   interned value leaves the index so a later intern allocates fresh.
//! * **Close reclaims.** Closing the heap reclaims every allocation;
//!   handles into a closed heap refuse, and so does allocation.

#![forbid(unsafe_code)]

use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;
use std::marker::PhantomData;

/// Every way the heap can refuse, each typed and naming its cause. No misuse
/// is ever a panic or a wrong value (the panic law, on this side of the
/// membrane: a stale handle is a fact about the caller's model, not a
/// crash).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HeapError {
    /// The heap is closed: nothing allocates, nothing resolves.
    Closed,
    /// The handle names no live allocation (freed, wrong generation, or
    /// never issued by this heap).
    StaleHandle,
    /// The handle's type does not match the requested type.
    TypeMismatch,
    /// A persistent allocation was offered to `get_mut` or `free`.
    PersistentMutation,
}

impl fmt::Display for HeapError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Closed => write!(f, "the heap is closed"),
            Self::StaleHandle => {
                write!(f, "the handle names no live allocation")
            }
            Self::TypeMismatch => {
                write!(f, "the handle's type does not match the request")
            }
            Self::PersistentMutation => {
                write!(f, "a persistent allocation is immutable and never freed")
            }
        }
    }
}

impl std::error::Error for HeapError {}

/// A typed handle into the NativeHeap. `Copy` by construction (a handle is a
/// fact, not an ownership claim); resolution goes through the heap, which is
/// where the laws live.
pub struct NativeHandle<T> {
    index: u32,
    generation: u32,
    _type: PhantomData<fn() -> T>,
}

impl<T> NativeHandle<T> {
    fn new(index: u32, generation: u32) -> Self {
        Self {
            index,
            generation,
            _type: PhantomData,
        }
    }

    /// Reconstitute a handle from its parts — for receipts, diagnostics, and
    /// tests that must plant a handle of a chosen shape. The heap's laws do
    /// not relax: a fabricated handle resolves only if it names a live,
    /// same-generation, same-type allocation.
    pub fn from_parts(index: u32, generation: u32) -> Self {
        Self::new(index, generation)
    }

    /// The slot index (diagnostics only; never an address).
    pub fn slot(self) -> u32 {
        self.index
    }

    /// The generation this handle was issued at (diagnostics only).
    pub fn generation(self) -> u32 {
        self.generation
    }
}

/// The next generation for a freed slot, or `None` when the slot must be
/// retired. Recycling at `u32::MAX` with wrapping arithmetic would re-issue
/// generation 0 — and after a full `u32` of alloc/dealloc cycles on the same
/// slot, a stale handle could still hold it (ABA: `get`/`get_mut`/`free`
/// would then accept the stale handle). Returning `None` retires the slot
/// permanently instead (the substrate's own law).
#[doc(hidden)]
pub const fn next_slot_generation(current: u32) -> Option<u32> {
    current.checked_add(1)
}

// A handle is a fact, not a resource: Clone + Copy by hand so the impl does
// not require T: Clone/Copy.
impl<T> Clone for NativeHandle<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> Copy for NativeHandle<T> {}
impl<T> PartialEq for NativeHandle<T> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index && self.generation == other.generation
    }
}
impl<T> Eq for NativeHandle<T> {}
impl<T> Hash for NativeHandle<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.index.hash(state);
        self.generation.hash(state);
    }
}
impl<T> fmt::Debug for NativeHandle<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "NativeHandle({}, gen {})", self.index, self.generation)
    }
}

/// One slot in the heap.
enum Slot {
    /// A live allocation.
    Occupied {
        value: Box<dyn Any + Send + Sync>,
        generation: u32,
        persistent: bool,
    },
    /// A freed slot, on the free list, with the generation its NEXT occupant
    /// will carry. `None` for the tail.
    Vacant {
        next_free: Option<u32>,
        generation: u32,
    },
}

/// The intern index entry: the slot the value lives at. Equality of the
/// full value is verified against the stored value on a hit, so a hash
/// collision can never silently fuse two values.
struct InternEntry {
    slot: u32,
}

/// The NativeHeap: a region-backed, handle-addressed store with total
/// interning and persistent semantics. Not thread-safe, by design and like
/// the substrate it mirrors: a region owns its heap during use; sharing is
/// through the handles, not through the heap object.
pub struct NativeHeap {
    slots: Vec<Slot>,
    free_head: Option<u32>,
    live: usize,
    intern: HashMap<(TypeId, u64), InternEntry>,
    closed: bool,
}

impl Default for NativeHeap {
    fn default() -> Self {
        Self::new()
    }
}

impl NativeHeap {
    pub fn new() -> Self {
        Self {
            slots: Vec::new(),
            free_head: None,
            live: 0,
            intern: HashMap::new(),
            closed: false,
        }
    }

    /// Live allocations (persistent included).
    pub fn live(&self) -> usize {
        self.live
    }

    /// True after `close` — a fact the converters rely on, since a
    /// conversion region that leaked would keep its scratch alive.
    pub fn is_closed(&self) -> bool {
        self.closed
    }

    fn alloc_slot(&mut self, value: Box<dyn Any + Send + Sync>, persistent: bool) -> (u32, u32) {
        self.live += 1;
        if let Some(head) = self.free_head {
            let (next_free, generation) = match &self.slots[head as usize] {
                Slot::Vacant {
                    next_free,
                    generation,
                } => (*next_free, (*generation).max(1)),
                Slot::Occupied { .. } => unreachable!("free list points at a live slot"),
            };
            self.free_head = next_free;
            self.slots[head as usize] = Slot::Occupied {
                value,
                generation,
                persistent,
            };
            (head, generation)
        } else {
            let index = self.slots.len() as u32;
            self.slots.push(Slot::Occupied {
                value,
                generation: 1,
                persistent,
            });
            (index, 1)
        }
    }

    /// Allocate a value. The returned handle is the only way back to it.
    pub fn alloc<T: Send + Sync + 'static>(&mut self, value: T) -> NativeHandle<T> {
        assert!(
            !self.closed,
            "alloc on a closed heap is a caller bug — the converters' region discipline, not a runtime state to model"
        );
        let (index, generation) = self.alloc_slot(Box::new(value), false);
        NativeHandle::new(index, generation)
    }

    /// Allocate a persistent value: immutable and never freed individually
    /// (the `m_rc == 0` arm of the tri-state law, on this side of the
    /// membrane — compact-region residents and `lean_mark_persistent`
    /// graphs are never counted).
    pub fn alloc_persistent<T: Send + Sync + 'static>(&mut self, value: T) -> NativeHandle<T> {
        assert!(
            !self.closed,
            "alloc_persistent on a closed heap is a caller bug"
        );
        let (index, generation) = self.alloc_slot(Box::new(value), true);
        NativeHandle::new(index, generation)
    }

    /// Store a value with total interning: an equal value already live in
    /// the heap returns its handle instead of a new allocation (R10's dedup
    /// — the dual-heap memory law). `key` extracts the interning key; the
    /// full value is compared on a hit, so a collision cannot fuse.
    pub fn intern<T, K>(&mut self, value: T, key: impl Fn(&T) -> K) -> NativeHandle<T>
    where
        T: Eq + Send + Sync + 'static,
        K: Hash + Eq + 'static,
    {
        self.intern_by(value, key, |a, b| a == b)
    }

    /// Intern with a caller-chosen equality — for value types without
    /// `PartialEq` (like `Expr`, whose identity discipline is the computed
    /// hash, upstream's own hash-consing). The equality on a hit is the
    /// caller's declared one, never an implicit default.
    pub fn intern_by<T, K>(
        &mut self,
        value: T,
        key: impl Fn(&T) -> K,
        eq: impl Fn(&T, &T) -> bool,
    ) -> NativeHandle<T>
    where
        T: Send + Sync + 'static,
        K: Hash + Eq + 'static,
    {
        assert!(!self.closed, "intern on a closed heap is a caller bug");
        let key_value = key(&value);
        let key_hash = {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            key_value.hash(&mut hasher);
            std::hash::Hasher::finish(&hasher)
        };
        let map_key = (TypeId::of::<K>(), key_hash);
        if let Some(entry) = self.intern.get(&map_key) {
            let slot = entry.slot;
            if let Slot::Occupied { value: stored, .. } = &self.slots[slot as usize]
                && let Some(stored) = stored.downcast_ref::<T>()
                && eq(stored, &value)
            {
                let generation = match &self.slots[slot as usize] {
                    Slot::Occupied { generation, .. } => *generation,
                    Slot::Vacant { .. } => unreachable!(),
                };
                return NativeHandle::new(slot, generation);
            }
            // The indexed slot died under the entry (freed) or holds a
            // different value under a colliding hash: the index is stale,
            // and the honest move is to replace it below.
        }
        let (index, generation) = self.alloc_slot(Box::new(value), false);
        self.intern.insert(map_key, InternEntry { slot: index });
        NativeHandle::new(index, generation)
    }

    /// Resolve a handle for reading. Every refusal is typed.
    pub fn get<T: 'static>(&self, handle: NativeHandle<T>) -> Result<&T, HeapError> {
        if self.closed {
            return Err(HeapError::Closed);
        }
        let Some(slot) = self.slots.get(handle.index as usize) else {
            return Err(HeapError::StaleHandle);
        };
        match slot {
            Slot::Occupied {
                value, generation, ..
            } => {
                if *generation != handle.generation {
                    return Err(HeapError::StaleHandle);
                }
                value.downcast_ref::<T>().ok_or(HeapError::TypeMismatch)
            }
            Slot::Vacant { .. } => Err(HeapError::StaleHandle),
        }
    }

    /// Resolve a handle for writing. A persistent allocation refuses: the
    /// persistent arm of the tri-state law is immutable.
    pub fn get_mut<T: 'static>(&mut self, handle: NativeHandle<T>) -> Result<&mut T, HeapError> {
        if self.closed {
            return Err(HeapError::Closed);
        }
        let Some(slot) = self.slots.get_mut(handle.index as usize) else {
            return Err(HeapError::StaleHandle);
        };
        match slot {
            Slot::Occupied {
                value,
                generation,
                persistent,
            } => {
                if *generation != handle.generation {
                    return Err(HeapError::StaleHandle);
                }
                if *persistent {
                    return Err(HeapError::PersistentMutation);
                }
                value.downcast_mut::<T>().ok_or(HeapError::TypeMismatch)
            }
            Slot::Vacant { .. } => Err(HeapError::StaleHandle),
        }
    }

    /// Free one allocation. Double free, a stale handle, and a persistent
    /// allocation are all typed refusals, never UB and never a panic.
    pub fn free<T: 'static>(&mut self, handle: NativeHandle<T>) -> Result<(), HeapError> {
        if self.closed {
            return Err(HeapError::Closed);
        }
        let Some(slot) = self.slots.get_mut(handle.index as usize) else {
            return Err(HeapError::StaleHandle);
        };
        let (value_generation, persistent) = match slot {
            Slot::Occupied {
                generation,
                persistent,
                ..
            } => (*generation, *persistent),
            Slot::Vacant { .. } => return Err(HeapError::StaleHandle),
        };
        if value_generation != handle.generation {
            return Err(HeapError::StaleHandle);
        }
        if persistent {
            return Err(HeapError::PersistentMutation);
        }
        let index = handle.index;
        // ABA retirement: the next occupant carries generation+1; at u32::MAX
        // the slot retires permanently rather than re-issue a generation a
        // stale handle could still hold (the substrate's own law).
        let next_generation = next_slot_generation(value_generation);
        let retired = next_generation.is_none();
        let replacement = Slot::Vacant {
            next_free: if retired { None } else { self.free_head },
            generation: next_generation.unwrap_or(u32::MAX),
        };
        self.slots[index as usize] = replacement;
        if !retired {
            self.free_head = Some(index);
        }
        self.live -= 1;
        // Any intern entry naming this slot is now stale; drop it so a
        // later intern allocates fresh rather than resolving to a re-used
        // slot's different value.
        self.intern.retain(|_, entry| entry.slot != index);
        Ok(())
    }

    /// Close the heap: every allocation reclaimed, every handle refused from
    /// now on. The converters' short-lived conversion regions end here —
    /// R10's scratch never outlives its region.
    pub fn close(&mut self) {
        for slot in &mut self.slots {
            *slot = Slot::Vacant {
                next_free: None,
                generation: 0,
            };
        }
        self.free_head = None;
        self.live = 0;
        self.intern.clear();
        self.closed = true;
    }
}
