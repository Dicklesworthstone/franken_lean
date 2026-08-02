//! The Lean task manager — a literal port of the pin's `task_manager`
//! (`object.cpp:727-1113`) on `std::sync::{Mutex, Condvar}` + `std::thread`,
//! zero new dependencies (bead fln-3gv slice 3; design + the measured
//! asupersync pricing: bead-comments fln-3gv:1847/:1852).
//!
//! One mutex guards the whole manager state; three condvars — queue wake,
//! task-finished (wakes `wait_for` and `wait_any`), dedicated-finished
//! (shutdown only). Priorities 0..=8 are pooled deques, `LEAN_SYNC_PRIO`
//! runs inline on the resolving thread (`enqueue_core`, object.cpp:758-763),
//! priorities above `LEAN_MAX_PRIO` get a dedicated detached thread. Workers
//! spawn lazily (`enqueue_core`) and a pooled worker blocked in `wait_for`
//! raises the worker cap so the pool cannot starve (object.cpp:990-1012).
//!
//! **The worker-spawn seam** is [`Manager::spawn_worker`] +
//! [`Manager::spawn_dedicated_worker`]: the one point that would change if
//! the §6.7-vs-D1 ruling (routed to the sequencer, fln-3gv:1852) ever puts
//! an asupersync substrate underneath. Everything else — the state machine,
//! the blocking plane, promise resolution — is the manager itself and stays.
//!
//! Deviations, disclosed (mechanism, not observables):
//! * `lean_task_imp` blocks live on the Rust heap (`Box`), not the small
//!   object heap — the imp never crosses the membrane as an object and no
//!   conforming code can observe its allocator.
//! * `m_shutting_down` is an `AtomicBool` beside the mutex (the pin reads
//!   the plain field unlocked, which Rust will not express); written under
//!   the lock, read `Relaxed`, same observable answers.
//! * Scheduled-task headers keep the membrane's size-prefixed `m_cs_sz`
//!   (the pin's `lean_set_task_header` zeroes it, which its sizeless
//!   `mi_free` never reads; the membrane's release discipline does —
//!   FLN-UL-0004). No conforming code reads a task's `m_cs_sz`.
//! * No `save_stack_info` (the stack-probe subsystem is separate), and
//!   worker panic messages go to the process stderr (the standing slice-1
//!   restriction).

use crate::layout::{LeanObject, LeanTaskImp, LeanTaskObject};
use crate::membrane;
use crate::object;
use crate::rc;
use crate::tagged::is_scalar;
use core::ffi::c_void;
use std::collections::VecDeque;
use std::ptr::null_mut;
use std::sync::atomic::{AtomicBool, AtomicPtr, Ordering};
use std::sync::{Condvar, Mutex, MutexGuard};

/// `LEAN_MAX_PRIO` (`object.cpp:70`).
pub(crate) const LEAN_MAX_PRIO: u32 = 8;
/// `LEAN_SYNC_PRIO` (`object.cpp:71`).
pub(crate) const LEAN_SYNC_PRIO: u32 = u32::MAX;

/// A task pointer licensed to cross threads: every task the manager holds is
/// multi-threaded by construction (`alloc_task_scheduled`'s MT header +
/// `mark_mt` on the closure), so the pointee's discipline is atomic.
// UNSAFE-LEDGER: FLN-UL-0227
#[allow(unsafe_code)]
mod send_wrappers {
    use super::{LeanTaskObject, Manager};

    #[derive(Clone, Copy)]
    pub(crate) struct TaskPtr(pub(crate) *mut LeanTaskObject);
    // SAFETY: the manager's tasks are MT objects whose mutable fields are
    // either `_Atomic` (m_value) or guarded by the manager mutex (m_imp and
    // everything behind it), exactly the pin's own cross-thread license.
    unsafe impl Send for TaskPtr {}

    #[derive(Clone, Copy)]
    pub(crate) struct MgrRef(pub(crate) *const Manager);
    // SAFETY: workers dereference the manager only between construction and
    // the join/wait in `Drop` (`~task_manager`, object.cpp:937-953); the
    // shutdown protocol keeps the referent alive past the last worker touch.
    unsafe impl Send for MgrRef {}
}
pub(crate) use send_wrappers::{MgrRef, TaskPtr};

thread_local! {
    /// `g_current_task_object` (`object.cpp:700`), set only by `run_task`.
    static CURRENT_TASK: core::cell::Cell<*mut LeanTaskObject> =
        const { core::cell::Cell::new(null_mut()) };
}

/// `g_task_manager` (`object.cpp:1063`): a plain global pointer, installed by
/// `lean_init_task_manager[_using]`, removed and dropped by
/// `lean_finalize_task_manager`.
static G_TASK_MANAGER: AtomicPtr<Manager> = AtomicPtr::new(null_mut());

/// The `g_task_manager` read every task-plane entry point performs.
// UNSAFE-LEDGER: FLN-UL-0228
#[allow(unsafe_code)]
pub(crate) fn manager() -> Option<&'static Manager> {
    let p = G_TASK_MANAGER.load(Ordering::Acquire);
    if p.is_null() {
        None
    } else {
        // SAFETY: the pointer was minted by `Box::into_raw` in `init` and is
        // invalidated only by `finalize`, whose contract (as upstream's) is
        // that no task-plane call races it.
        Some(unsafe { &*p })
    }
}

/// `lean_init_task_manager_using` (`object.cpp:1065-1072`): zero workers
/// means NO manager, exactly as upstream.
pub(crate) fn init_using(num_workers: u32) {
    debug_assert!(
        G_TASK_MANAGER.load(Ordering::Acquire).is_null(),
        "task manager already initialized"
    );
    if num_workers > 0 {
        let mgr = Box::into_raw(Box::new(Manager::new(num_workers)));
        G_TASK_MANAGER.store(mgr, Ordering::Release);
    }
}

/// `get_lean_num_threads` (`object.cpp:1074-1081`).
pub(crate) fn default_num_workers() -> u32 {
    if let Some(n) = std::env::var_os("LEAN_NUM_THREADS") {
        // atoi semantics: leading digits, else 0.
        let s = n.to_string_lossy();
        let digits: String = s.chars().take_while(char::is_ascii_digit).collect();
        return digits.parse().unwrap_or(0);
    }
    std::thread::available_parallelism().map_or(1, |n| n.get() as u32)
}

/// `lean_finalize_task_manager` (`object.cpp:1092-1097`).
// UNSAFE-LEDGER: FLN-UL-0229
#[allow(unsafe_code)]
pub(crate) fn finalize() {
    let p = G_TASK_MANAGER.swap(null_mut(), Ordering::AcqRel);
    if !p.is_null() {
        // SAFETY: the pointer came from `Box::into_raw` in `init_using`;
        // dropping runs the shutdown protocol (join workers, wait dedicated)
        // before the memory is released, exactly as `delete g_task_manager`.
        drop(unsafe { Box::from_raw(p) });
    }
}

struct State {
    workers: Vec<std::thread::JoinHandle<()>>,
    idle_std_workers: u32,
    max_std_workers: u32,
    num_dedicated_workers: u32,
    queues: [VecDeque<TaskPtr>; (LEAN_MAX_PRIO as usize) + 1],
    queues_size: u32,
    max_prio: u32,
}

pub(crate) struct Manager {
    state: Mutex<State>,
    queue_cv: Condvar,
    task_finished_cv: Condvar,
    dedicated_finished_cv: Condvar,
    /// Written under the state lock, read unlocked exactly as the pin reads
    /// its plain field (`shutting_down()`, object.cpp:1045-1047).
    shutting_down: AtomicBool,
}

fn lock_state<'a>(m: &'a Mutex<State>) -> MutexGuard<'a, State> {
    m.lock().unwrap_or_else(std::sync::PoisonError::into_inner)
}

// ---------------------------------------------------------------- field access

/// Task salient-field helpers, funneling every raw read/write the manager
/// performs. `m_value` is the `_Atomic` slot; `m_imp` and everything behind
/// it are guarded by the manager mutex per the state machine
/// (`lean.h:245-295`).
// UNSAFE-LEDGER: FLN-UL-0230
#[allow(unsafe_code)]
mod fields {
    use super::{LeanObject, LeanTaskImp, Ordering, TaskPtr};

    pub(super) fn value(t: TaskPtr) -> *mut LeanObject {
        // SAFETY: t is a live task per the caller's state-machine position.
        unsafe { (*t.0).m_value.load(Ordering::Acquire) }
    }
    pub(super) fn set_value(t: TaskPtr, v: *mut LeanObject) {
        // SAFETY: as above; the single publication point (resolve_core).
        unsafe { (*t.0).m_value.store(v, Ordering::Release) }
    }
    pub(super) fn imp(t: TaskPtr) -> *mut LeanTaskImp {
        // SAFETY: as above; callers hold the manager lock wherever the imp
        // can race (the pin's own discipline).
        unsafe { (&raw const (*t.0).m_imp).read() }
    }
    pub(super) fn set_imp(t: TaskPtr, imp: *mut LeanTaskImp) {
        // SAFETY: as above.
        unsafe { (&raw mut (*t.0).m_imp).write(imp) }
    }
}
use fields::{imp, set_imp, set_value, value};

/// Imp-block field helpers (behind the manager lock everywhere they race).
// UNSAFE-LEDGER: FLN-UL-0231
#[allow(unsafe_code)]
mod imp_fields {
    use super::{LeanObject, LeanTaskImp};
    use crate::layout::LeanTaskObject;

    // The shared invariant every body cites: the imp pointer is live between
    // `alloc_task_scheduled` and `free_task`/`resolve_core`, and mutated
    // only under the manager lock or before publication, per the pin's
    // state machine.
    pub(super) fn closure(i: *mut LeanTaskImp) -> *mut LeanObject {
        // SAFETY: the mod-header invariant.
        unsafe { (&raw const (*i).m_closure).read() }
    }
    pub(super) fn set_closure(i: *mut LeanTaskImp, c: *mut LeanObject) {
        // SAFETY: the mod-header invariant.
        unsafe { (&raw mut (*i).m_closure).write(c) }
    }
    pub(super) fn head_dep(i: *mut LeanTaskImp) -> *mut LeanTaskObject {
        // SAFETY: the mod-header invariant.
        unsafe { (&raw const (*i).m_head_dep).read() }
    }
    pub(super) fn set_head_dep(i: *mut LeanTaskImp, d: *mut LeanTaskObject) {
        // SAFETY: the mod-header invariant.
        unsafe { (&raw mut (*i).m_head_dep).write(d) }
    }
    pub(super) fn next_dep(i: *mut LeanTaskImp) -> *mut LeanTaskObject {
        // SAFETY: the mod-header invariant.
        unsafe { (&raw const (*i).m_next_dep).read() }
    }
    pub(super) fn set_next_dep(i: *mut LeanTaskImp, d: *mut LeanTaskObject) {
        // SAFETY: the mod-header invariant.
        unsafe { (&raw mut (*i).m_next_dep).write(d) }
    }
    pub(super) fn prio(i: *mut LeanTaskImp) -> u32 {
        // SAFETY: the mod-header invariant.
        unsafe { (&raw const (*i).m_prio).read() }
    }
    pub(super) fn canceled(i: *mut LeanTaskImp) -> bool {
        // SAFETY: the mod-header invariant.
        unsafe { (&raw const (*i).m_canceled).read() != 0 }
    }
    pub(super) fn set_canceled(i: *mut LeanTaskImp, v: bool) {
        // SAFETY: the mod-header invariant.
        unsafe { (&raw mut (*i).m_canceled).write(u8::from(v)) }
    }
    pub(super) fn keep_alive(i: *mut LeanTaskImp) -> bool {
        // SAFETY: the mod-header invariant.
        unsafe { (&raw const (*i).m_keep_alive).read() != 0 }
    }
    pub(super) fn deleted(i: *mut LeanTaskImp) -> bool {
        // SAFETY: the mod-header invariant.
        unsafe { (&raw const (*i).m_deleted).read() != 0 }
    }
    pub(super) fn set_deleted(i: *mut LeanTaskImp, v: bool) {
        // SAFETY: the mod-header invariant.
        unsafe { (&raw mut (*i).m_deleted).write(u8::from(v)) }
    }
}

/// `free_task` (`object.cpp:717-721`): release the imp box (if any) and the
/// task object's membrane block.
// UNSAFE-LEDGER: FLN-UL-0232
#[allow(unsafe_code)]
fn free_task(t: TaskPtr) {
    // SAFETY: called only from the states whose next transition is `freed`
    // (Deactivated x {dequeued, finished, dep-finished, dep-deactivated});
    // the imp box came from `Box::into_raw` in the scheduled allocator.
    unsafe {
        let i = imp(t);
        if !i.is_null() {
            drop(Box::from_raw(i));
        }
        let sz = core::mem::size_of::<LeanTaskObject>();
        membrane::release_with_size(
            t.0.cast::<LeanObject>(),
            membrane::align_obj_size(sz),
            "del.task",
        );
    }
}

/// The scalar-checked `lean_dec` the manager applies to values and closures
/// it owns (`object.cpp` uses the checked inlines throughout).
// UNSAFE-LEDGER: FLN-UL-0233
#[allow(unsafe_code)]
fn dec_checked(o: *mut LeanObject) {
    if !o.is_null() && !is_scalar(o) {
        // SAFETY: o is a live object the caller owns one reference to.
        unsafe { rc::dec_ref(o) };
    }
}

impl Manager {
    fn new(max_std_workers: u32) -> Manager {
        Manager {
            state: Mutex::new(State {
                workers: Vec::new(),
                idle_std_workers: 0,
                max_std_workers,
                num_dedicated_workers: 0,
                queues: std::array::from_fn(|_| VecDeque::new()),
                queues_size: 0,
                max_prio: 0,
            }),
            queue_cv: Condvar::new(),
            task_finished_cv: Condvar::new(),
            dedicated_finished_cv: Condvar::new(),
            shutting_down: AtomicBool::new(false),
        }
    }

    /// `dequeue` (`object.cpp:742-756`).
    fn dequeue(g: &mut MutexGuard<'_, State>) -> TaskPtr {
        debug_assert!(g.queues_size != 0);
        let mp = g.max_prio as usize;
        let t = g.queues[mp]
            .pop_front()
            .expect("dequeue: empty max-prio queue");
        g.queues_size -= 1;
        if g.queues[g.max_prio as usize].is_empty() {
            while g.max_prio > 0 {
                g.max_prio -= 1;
                if !g.queues[g.max_prio as usize].is_empty() {
                    break;
                }
            }
        }
        t
    }

    /// `enqueue_core` (`object.cpp:758-777`).
    fn enqueue_core<'a>(
        &'a self,
        mut g: MutexGuard<'a, State>,
        t: TaskPtr,
    ) -> MutexGuard<'a, State> {
        let i = imp(t);
        debug_assert!(!i.is_null());
        let prio = imp_fields::prio(i);
        if prio == LEAN_SYNC_PRIO {
            return self.run_task(g, t);
        }
        if prio > LEAN_MAX_PRIO {
            self.spawn_dedicated_worker(&mut g, t);
            return g;
        }
        if prio > g.max_prio {
            g.max_prio = prio;
        }
        g.queues[prio as usize].push_back(t);
        g.queues_size += 1;
        if g.idle_std_workers == 0 && (g.workers.len() as u32) < g.max_std_workers {
            self.spawn_worker(&mut g);
        } else {
            self.queue_cv.notify_one();
        }
        g
    }

    /// `enqueue` (`object.cpp:955-958`).
    pub(crate) fn enqueue(&self, t: TaskPtr) {
        let g = lock_state(&self.state);
        drop(self.enqueue_core(g, t));
    }

    /// `spawn_worker` (`object.cpp:797-828`) — THE WORKER-SPAWN SEAM
    /// (fln-3gv:1852): the one function an alternative thread substrate
    /// would replace.
    fn spawn_worker(&self, g: &mut MutexGuard<'_, State>) {
        if self.shutting_down.load(Ordering::Relaxed) {
            return;
        }
        let me = MgrRef(self as *const Manager);
        let handle = std::thread::Builder::new()
            .name("fln-task-worker".into())
            .spawn(move || worker_main(me))
            .expect("task worker spawn failed");
        g.workers.push(handle);
    }

    /// `spawn_dedicated_worker` (`object.cpp:839-849`): detached; the
    /// shutdown protocol waits on the counter, never a join handle.
    fn spawn_dedicated_worker(&self, g: &mut MutexGuard<'_, State>, t: TaskPtr) {
        g.num_dedicated_workers += 1;
        let me = MgrRef(self as *const Manager);
        // SAFETY of the reference lifetime is MgrRef's ledger row; the
        // JoinHandle is deliberately dropped (detached), as upstream's
        // lthread is.
        let builder = std::thread::Builder::new().name("fln-task-dedicated".into());
        let _detached = builder
            .spawn(move || {
                let mgr = mgr_deref(me);
                let g = lock_state(&mgr.state);
                let mut g = mgr.run_task(g, t);
                g.num_dedicated_workers -= 1;
                mgr.dedicated_finished_cv.notify_all();
                drop(g);
            })
            .expect("dedicated task worker spawn failed");
    }

    /// `run_task` (`object.cpp:851-887`), guard passed by value across the
    /// unlock windows exactly where the pin unlocks.
    fn run_task<'a>(&'a self, mut g: MutexGuard<'a, State>, t: TaskPtr) -> MutexGuard<'a, State> {
        let i = imp(t);
        debug_assert!(!i.is_null());
        if imp_fields::deleted(i) {
            free_task(t);
            return g;
        }
        crate::set_allocation_heartbeats(0); // reset_heartbeat
        let v;
        {
            let prev = CURRENT_TASK.with(|c| c.replace(t.0));
            let c = imp_fields::closure(i);
            imp_fields::set_closure(i, null_mut());
            drop(g);
            v = apply_closure_to_unit(c);
            // Delayed-by-keep_alive deactivation: after the final execution.
            if !v.is_null() && imp_fields::keep_alive(i) {
                dec_checked(t.0.cast::<LeanObject>());
            }
            g = lock_state(&self.state);
            CURRENT_TASK.with(|cell| cell.set(prev));
        }
        debug_assert!(!imp(t).is_null());
        if imp_fields::deleted(i) {
            drop(g);
            dec_checked(v);
            free_task(t);
            g = lock_state(&self.state);
        } else if !v.is_null() {
            debug_assert!(imp_fields::closure(i).is_null());
            g = self.resolve_core(g, t, v);
        } else {
            // `bind` re-arm: the closure was re-installed by task_bind_fn1;
            // extract before unlocking (the pin's own NOTE).
            let c = imp_fields::closure(i);
            drop(g);
            let dep = bind_closure_dep_task(c);
            self.add_dep(dep, t);
            g = lock_state(&self.state);
        }
        g
    }

    /// `resolve_core` (`object.cpp:892-902`): the single `mark_mt` choke
    /// point for every value entering `m_value`.
    // UNSAFE-LEDGER: FLN-UL-0234
    #[allow(unsafe_code)]
    fn resolve_core<'a>(
        &'a self,
        g: MutexGuard<'a, State>,
        t: TaskPtr,
        v: *mut LeanObject,
    ) -> MutexGuard<'a, State> {
        if !is_scalar(v) {
            // SAFETY: v is the owned result being published; marking precedes
            // the store exactly as the pin's resolve_core does.
            unsafe { rc::mark_mt(v) };
        }
        set_value(t, v);
        let i = imp(t);
        set_imp(t, null_mut());
        let g = self.handle_finished(g, i);
        // SAFETY: the imp box is exclusively the manager's here; every
        // reader saw `m_imp == NULL` published above or holds the lock.
        unsafe {
            drop(Box::from_raw(i));
        }
        self.task_finished_cv.notify_all();
        g
    }

    /// `handle_finished` (`object.cpp:904-917`).
    fn handle_finished<'a>(
        &'a self,
        mut g: MutexGuard<'a, State>,
        i: *mut LeanTaskImp,
    ) -> MutexGuard<'a, State> {
        let mut it = imp_fields::head_dep(i);
        imp_fields::set_head_dep(i, null_mut());
        while !it.is_null() {
            let it_imp = imp(TaskPtr(it));
            if imp_fields::canceled(i) {
                imp_fields::set_canceled(it_imp, true);
            }
            let next_it = imp_fields::next_dep(it_imp);
            imp_fields::set_next_dep(it_imp, null_mut());
            if imp_fields::deleted(it_imp) {
                free_task(TaskPtr(it));
            } else {
                g = self.enqueue_core(g, TaskPtr(it));
            }
            it = next_it;
        }
        g
    }

    /// `resolve` (`object.cpp:960-972`): double-checked; the second value is
    /// silently dropped ("only the first call has an effect").
    pub(crate) fn resolve(&self, t: TaskPtr, v: *mut LeanObject) {
        if !value(t).is_null() {
            dec_checked(v);
            return;
        }
        let g = lock_state(&self.state);
        if !value(t).is_null() {
            drop(g); // `dec(v)` could re-enter deactivate_task and the lock
            dec_checked(v);
            return;
        }
        drop(self.resolve_core(g, t, v));
    }

    /// `add_dep` (`object.cpp:974-988`).
    pub(crate) fn add_dep(&self, t1: TaskPtr, t2: TaskPtr) {
        debug_assert!(value(t2).is_null());
        if !value(t1).is_null() {
            self.enqueue(t2);
            return;
        }
        let g = lock_state(&self.state);
        if !value(t1).is_null() {
            drop(self.enqueue_core(g, t2));
            return;
        }
        let i1 = imp(t1);
        let i2 = imp(t2);
        imp_fields::set_next_dep(i2, imp_fields::head_dep(i1));
        imp_fields::set_head_dep(i1, t2.0);
        drop(g);
    }

    /// `wait_for` (`object.cpp:990-1012`): a blocked pooled worker raises
    /// the cap; `Task.get` from a `sync := true` task is the pin's panic.
    pub(crate) fn wait_for(&self, t: TaskPtr) {
        if !value(t).is_null() {
            return;
        }
        let mut g = lock_state(&self.state);
        if !value(t).is_null() {
            return;
        }
        let cur = CURRENT_TASK.with(core::cell::Cell::get);
        let cur_prio = if cur.is_null() {
            None
        } else {
            Some(imp_fields::prio(imp(TaskPtr(cur))))
        };
        let in_pool = matches!(cur_prio, Some(p) if p <= LEAN_MAX_PRIO);
        if cur_prio == Some(LEAN_SYNC_PRIO) {
            crate::export::panic_impl(b"PANIC: `Task.get` called from a `(sync := true)` task");
        }
        if in_pool {
            g.max_std_workers += 1;
            if g.idle_std_workers == 0 {
                self.spawn_worker(&mut g);
            } else {
                self.queue_cv.notify_one();
            }
        }
        while value(t).is_null() {
            g = self
                .task_finished_cv
                .wait(g)
                .unwrap_or_else(std::sync::PoisonError::into_inner);
        }
        if in_pool {
            g.max_std_workers -= 1;
        }
    }

    /// `cancel` (`object.cpp:1039-1043`).
    pub(crate) fn cancel(&self, t: TaskPtr) {
        let g = lock_state(&self.state);
        let i = imp(t);
        if !i.is_null() {
            imp_fields::set_canceled(i, true);
        }
        drop(g);
    }

    /// `check_canceled` for the current task (`object.cpp:1246-1252`).
    pub(crate) fn check_canceled_current(&self) -> bool {
        let cur = CURRENT_TASK.with(core::cell::Cell::get);
        if cur.is_null() {
            return false;
        }
        let i = imp(TaskPtr(cur));
        debug_assert!(!i.is_null());
        imp_fields::canceled(i) || self.shutting_down.load(Ordering::Relaxed)
    }

    /// `get_task_state` (`object.cpp:1049-1060`): 0 waiting/queued,
    /// 1 running/promised, 2 finished.
    pub(crate) fn get_task_state(&self, t: TaskPtr) -> u8 {
        let g = lock_state(&self.state);
        let i = imp(t);
        let s = if !i.is_null() {
            if !imp_fields::closure(i).is_null() {
                0
            } else {
                1
            }
        } else {
            2
        };
        drop(g);
        s
    }

    /// `deactivate_task` (`object.cpp:1025-1037`) reached from the rc
    /// teardown when a task's count hits zero. The finished arm hands its
    /// value to the caller's iterative todo stack instead of recursing; the
    /// unfinished arm is `deactivate_task_core` (`object.cpp:779-795`).
    pub(crate) fn deactivate_for_teardown(
        &self,
        t: TaskPtr,
        todo_push: &mut dyn FnMut(*mut LeanObject),
    ) {
        let g = lock_state(&self.state);
        let v = value(t);
        if !v.is_null() {
            debug_assert!(imp(t).is_null());
            drop(g);
            if !is_scalar(v) {
                todo_push(v);
            }
            free_task(t);
            return;
        }
        let i = imp(t);
        debug_assert!(!i.is_null());
        let c = imp_fields::closure(i);
        let mut it = imp_fields::head_dep(i);
        imp_fields::set_closure(i, null_mut());
        imp_fields::set_head_dep(i, null_mut());
        imp_fields::set_canceled(i, true);
        imp_fields::set_deleted(i, true);
        drop(g);
        while !it.is_null() {
            let it_imp = imp(TaskPtr(it));
            debug_assert!(imp_fields::deleted(it_imp));
            let next_it = imp_fields::next_dep(it_imp);
            free_task(TaskPtr(it));
            it = next_it;
        }
        if !c.is_null() && !is_scalar(c) {
            todo_push(c);
        }
        // The task object itself stays: a worker / handle_finished /
        // dep-deactivation frees it (the Deactivated state's transitions).
    }
}

impl Drop for Manager {
    /// `~task_manager` (`object.cpp:937-953`): flag + wake everyone, join
    /// the pooled workers, then wait out the dedicated counter.
    fn drop(&mut self) {
        let mut g = lock_state(&self.state);
        self.shutting_down.store(true, Ordering::Relaxed);
        let workers = std::mem::take(&mut g.workers);
        drop(g);
        self.queue_cv.notify_all();
        for w in workers {
            let _ = w.join();
        }
        let mut g = lock_state(&self.state);
        while g.num_dedicated_workers > 0 {
            g = self
                .dedicated_finished_cv
                .wait(g)
                .unwrap_or_else(std::sync::PoisonError::into_inner);
        }
        drop(g);
    }
}

/// The pooled worker loop (`object.cpp:801-827`).
fn worker_main(me: MgrRef) {
    let mgr = mgr_deref(me);
    let mut g = lock_state(&mgr.state);
    g.idle_std_workers += 1;
    loop {
        if g.queues_size == 0 {
            if mgr.shutting_down.load(Ordering::Relaxed) {
                break;
            }
            g = mgr
                .queue_cv
                .wait(g)
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            continue;
        }
        if g.workers.len() as u32 > g.max_std_workers {
            // The pin dequeues regardless; the cap only gates new spawns.
        }
        let t = Manager::dequeue(&mut g);
        g.idle_std_workers -= 1;
        g = mgr.run_task(g, t);
        g.idle_std_workers += 1;
        crate::set_allocation_heartbeats(0);
    }
    g.idle_std_workers -= 1;
    drop(g);
}

/// The `MgrRef` deref, funneled once.
// UNSAFE-LEDGER: FLN-UL-0235
#[allow(unsafe_code)]
fn mgr_deref(me: MgrRef) -> &'static Manager {
    // SAFETY: MgrRef's ledger row — the shutdown protocol outlives every
    // worker touch.
    unsafe { &*me.0 }
}

/// `lean_apply_1(c, box(0))` as `run_task` performs it.
// UNSAFE-LEDGER: FLN-UL-0236
#[allow(unsafe_code)]
fn apply_closure_to_unit(c: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: c is the owned task closure; apply consumes it and yields the
    // owned result (or the bind re-arm sentinel NULL).
    unsafe { crate::export::apply_core(c, &[crate::tagged::boxi(0)]) }
}

/// Read the first fixed argument (the nested task) out of a
/// `task_bind_fn2` closure (`run_task`'s re-arm arm, `object.cpp:880-884`).
// UNSAFE-LEDGER: FLN-UL-0237
#[allow(unsafe_code)]
fn bind_closure_dep_task(c: *mut LeanObject) -> TaskPtr {
    // SAFETY: c is the bind continuation closure task_bind_fn1 installed
    // under the lock; its arg 0 is the nested task by construction.
    unsafe {
        let (_, _, _, args) = object::closure_fields(c);
        TaskPtr(args.read().cast::<LeanTaskObject>())
    }
}

// ---------------------------------------------------------------- task fns

/// `task_map_fn` (`object.cpp:1166-1172`).
// UNSAFE-LEDGER: FLN-UL-0238
#[allow(unsafe_code)]
pub(crate) extern "C" fn task_map_fn(
    f: *mut LeanObject,
    t: *mut LeanObject,
    _w: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: t is a finished task (the manager enqueued this closure from
    // handle_finished); the value is duplicated before the task's release.
    unsafe {
        let (v, _) = object::task_fields(t);
        debug_assert!(!v.is_null());
        if !is_scalar(v) {
            rc::inc_ref_n(v, 1);
        }
        rc::dec_ref(t);
        crate::export::apply_core(f, &[v])
    }
}

/// `task_bind_fn2` (`object.cpp:1205-1211`).
// UNSAFE-LEDGER: FLN-UL-0239
#[allow(unsafe_code)]
pub(crate) extern "C" fn task_bind_fn2(t: *mut LeanObject, _w: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: t is the finished nested task this continuation waited on.
    unsafe {
        let (v, _) = object::task_fields(t);
        debug_assert!(!v.is_null());
        if !is_scalar(v) {
            rc::inc_ref_n(v, 1);
        }
        rc::dec_ref(t);
        v
    }
}

/// `task_bind_fn1` (`object.cpp:1213-1232`): NULL is the "did not finish"
/// sentinel that re-arms the current task on the nested one.
// UNSAFE-LEDGER: FLN-UL-0240
#[allow(unsafe_code)]
pub(crate) extern "C" fn task_bind_fn1(
    x: *mut LeanObject,
    f: *mut LeanObject,
    _w: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: x is the finished input task; the nested task returned by f is
    // either consumed here (finished) or stored as the re-arm continuation
    // under the run_task contract.
    unsafe {
        let (v, _) = object::task_fields(x);
        debug_assert!(!v.is_null());
        if !is_scalar(v) {
            rc::inc_ref_n(v, 1);
        }
        rc::dec_ref(x);
        let new_task = crate::export::apply_core(f, &[v]);
        let (v2, _) = object::task_fields(new_task);
        if !v2.is_null() {
            if !is_scalar(v2) {
                rc::inc_ref_n(v2, 1);
            }
            rc::dec_ref(new_task);
            return v2;
        }
        let cur = CURRENT_TASK.with(core::cell::Cell::get);
        debug_assert!(!cur.is_null());
        let cur_imp = imp(TaskPtr(cur));
        debug_assert!(!cur_imp.is_null());
        debug_assert!(imp_fields::closure(cur_imp).is_null());
        let c = object::alloc_closure(task_bind_fn2 as *mut c_void, 2, 1);
        object::closure_set(c, 0, new_task);
        rc::mark_mt(c);
        imp_fields::set_closure(cur_imp, c);
        null_mut() // notify the queue that this task did not finish yet
    }
}
