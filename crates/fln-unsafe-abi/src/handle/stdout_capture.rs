//! Explicit, thread-local memory sinks for the reviewed Golem stdout callback.
//! No native FILE is created, closed, or redirected. A retained callback binds
//! each scope to one validated stdout Handle; other Handles keep normal fwrite.

use super::Obj;
use std::cell::RefCell;
use std::marker::PhantomData;
use std::rc::Rc;

/// Capture setup or resource failure, never an operating-system write result.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StdoutCaptureError {
    InvalidStdout,
    Allocation,
    Limit { limit: usize, requested: usize },
    ScopeUnavailable,
}

/// Completed capture data. Bytes accepted before a failure remain intact.
#[derive(Debug)]
pub struct CapturedStdout {
    pub bytes: Vec<u8>,
    pub error: Option<StdoutCaptureError>,
}

/// A concrete thread-affine scope. Dropping or finishing it removes only its
/// own frame, so non-LIFO destruction cannot corrupt a younger scope. Unwind
/// restores the prior sink; forgetting a guard deliberately retains its sink.
pub struct StdoutCapture {
    id: Option<u64>,
    not_send: PhantomData<Rc<()>>,
}

struct Frame {
    id: u64,
    callback: Obj,
    bytes: Vec<u8>,
    escaped_bytes: usize,
    limit: usize,
    error: Option<StdoutCaptureError>,
}

#[derive(Default)]
struct State {
    frames: Vec<Frame>,
    next_id: u64,
}

thread_local! {
    static STATE: RefCell<State> = RefCell::new(State::default());
}

impl StdoutCapture {
    /// Capture this thread's exact current native stdout. `max_escaped_bytes`
    /// bounds JSON string content after escaping (excluding quotes), and hence
    /// also bounds the unchanged raw UTF-8 bytes. Each write is all-or-nothing.
    pub fn begin(max_escaped_bytes: usize) -> Result<Self, StdoutCaptureError> {
        let callback = Obj::stdio_stdout()
            .and_then(|stream| stream.try_ctor_child(4))
            .ok_or(StdoutCaptureError::InvalidStdout)?;
        STATE.with(|state| {
            let mut state = state.borrow_mut();
            let next_id = state
                .next_id
                .checked_add(1)
                .ok_or(StdoutCaptureError::ScopeUnavailable)?;
            state
                .frames
                .try_reserve(1)
                .map_err(|_| StdoutCaptureError::Allocation)?;
            let id = state.next_id;
            state.next_id = next_id;
            state.frames.push(Frame {
                id,
                callback,
                bytes: Vec::new(),
                escaped_bytes: 0,
                limit: max_escaped_bytes,
                error: None,
            });
            Ok(Self {
                id: Some(id),
                not_send: PhantomData,
            })
        })
    }

    /// Finish this scope without changing any still-live nested capture.
    pub fn finish(mut self) -> CapturedStdout {
        self.id.take().and_then(remove).map_or_else(
            || CapturedStdout {
                bytes: Vec::new(),
                error: Some(StdoutCaptureError::ScopeUnavailable),
            },
            |frame| CapturedStdout {
                bytes: frame.bytes,
                error: frame.error,
            },
        )
    }
}

impl Drop for StdoutCapture {
    fn drop(&mut self) {
        if let Some(id) = self.id.take() {
            drop(remove(id));
        }
    }
}

fn remove(id: u64) -> Option<Frame> {
    STATE
        .try_with(|state| {
            let mut state = state.borrow_mut();
            let index = state.frames.iter().position(|frame| frame.id == id)?;
            Some(state.frames.remove(index))
        })
        .ok()
        .flatten()
}

fn escaped_length(bytes: &[u8]) -> Option<usize> {
    bytes.iter().try_fold(0usize, |total, byte| {
        total.checked_add(match byte {
            b'"' | b'\\' | b'\n' | b'\r' | b'\t' | 8 | 12 => 2,
            0..=31 => 6,
            _ => 1,
        })
    })
}

fn same_handle(left: &Obj, right: &Obj) -> bool {
    // SAFETY: both Obj values own live objects. The exact callback observer
    // validates pointer, arity and capture class before returning borrowed
    // Handle pointers, which are compared only while both owners remain live.
    // UNSAFE-LEDGER: FLN-UL-0627
    #[allow(unsafe_code)]
    unsafe {
        match (
            crate::stdio::stream_put_str_handle(left.0),
            crate::stdio::stream_put_str_handle(right.0),
        ) {
            (Some(left), Some(right)) => left == right,
            _ => false,
        }
    }
}

/// Called only after the normal callback, canonical String, and world checks.
pub(super) fn write_if_captured(callback: &Obj, text: &Obj) -> Result<bool, StdoutCaptureError> {
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        let Some(frame) = state
            .frames
            .iter_mut()
            .rev()
            .find(|frame| same_handle(callback, &frame.callback))
        else {
            return Ok(false);
        };
        if let Some(error) = frame.error {
            return Err(error);
        }
        let Some((size, _, _, bytes)) = text.try_string_view() else {
            // The caller established canonical String shape before this hook.
            frame.error = Some(StdoutCaptureError::ScopeUnavailable);
            return Err(StdoutCaptureError::ScopeUnavailable);
        };
        let bytes = &bytes[..size - 1];
        let requested =
            escaped_length(bytes).and_then(|length| frame.escaped_bytes.checked_add(length));
        let error = if requested.is_none_or(|length| length > frame.limit) {
            Some(StdoutCaptureError::Limit {
                limit: frame.limit,
                requested: requested.unwrap_or(usize::MAX),
            })
        } else if frame.bytes.try_reserve(bytes.len()).is_err() {
            Some(StdoutCaptureError::Allocation)
        } else {
            None
        };
        if let Some(error) = error {
            frame.error = Some(error);
            return Err(error);
        }
        frame.bytes.extend_from_slice(bytes);
        frame.escaped_bytes = requested.unwrap_or(frame.escaped_bytes);
        Ok(true)
    })
}

#[cfg(test)]
mod tests;
