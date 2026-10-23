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
    InvalidStderr,
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
    stderr: Option<Obj>,
    escaped: bool,
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
        Self::begin_scope(max_escaped_bytes, false, true)
    }

    /// Isolate this thread's stdout and optionally stderr into one ordered
    /// UTF-8 buffer. Unlike JSON capture, the allowance counts raw bytes.
    pub fn begin_isolated(
        max_bytes: usize,
        isolate_stderr: bool,
    ) -> Result<Self, StdoutCaptureError> {
        Self::begin_scope(max_bytes, isolate_stderr, false)
    }

    fn begin_scope(
        limit: usize,
        isolate_stderr: bool,
        escaped: bool,
    ) -> Result<Self, StdoutCaptureError> {
        let callback = Obj::stdio_stdout()
            .and_then(|stream| stream.try_ctor_child(4))
            .ok_or(StdoutCaptureError::InvalidStdout)?;
        let stderr = if isolate_stderr {
            Some(
                Obj::stdio_stderr()
                    .and_then(|stream| stream.try_ctor_child(4))
                    .ok_or(StdoutCaptureError::InvalidStderr)?,
            )
        } else {
            None
        };
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
                stderr,
                escaped,
                bytes: Vec::new(),
                escaped_bytes: 0,
                limit,
                error: None,
            });
            Ok(Self {
                id: Some(id),
                not_send: PhantomData,
            })
        })
    }

    /// The current thread's first unsettled capture failure. Runtime callers
    /// use this after void diagnostic effects to stop before a continuation.
    pub fn current_error() -> Option<StdoutCaptureError> {
        STATE.with(|state| {
            state
                .borrow()
                .frames
                .iter()
                .rev()
                .find_map(|frame| frame.error)
        })
    }

    /// Retain already isolated output in the enclosing memory capture. This
    /// never writes to a process stream when no capture is installed.
    pub fn append_current(text: &str) -> Result<(), StdoutCaptureError> {
        STATE.with(|state| {
            let mut state = state.borrow_mut();
            let frame = state
                .frames
                .last_mut()
                .ok_or(StdoutCaptureError::ScopeUnavailable)?;
            append(frame, &[text.as_bytes()])
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

fn matches(frame: &Frame, callback: &Obj) -> bool {
    same_handle(callback, &frame.callback)
        || frame
            .stderr
            .as_ref()
            .is_some_and(|stderr| same_handle(callback, stderr))
}

fn append(frame: &mut Frame, parts: &[&[u8]]) -> Result<(), StdoutCaptureError> {
    if let Some(error) = frame.error {
        return Err(error);
    }
    let size = parts.iter().try_fold(0usize, |n, p| n.checked_add(p.len()));
    let requested = parts.iter().try_fold(frame.escaped_bytes, |n, p| {
        n.checked_add(if frame.escaped {
            escaped_length(p)?
        } else {
            p.len()
        })
    });
    let error = if requested.is_none_or(|length| length > frame.limit) {
        Some(StdoutCaptureError::Limit {
            limit: frame.limit,
            requested: requested.unwrap_or(usize::MAX),
        })
    } else if size.is_none_or(|size| frame.bytes.try_reserve(size).is_err()) {
        Some(StdoutCaptureError::Allocation)
    } else {
        None
    };
    if let Some(error) = error {
        frame.error = Some(error);
        return Err(error);
    }
    for part in parts {
        frame.bytes.extend_from_slice(part);
    }
    frame.escaped_bytes = requested.unwrap_or(frame.escaped_bytes);
    Ok(())
}

/// The native panic/trace router uses its current validated stderr callback,
/// including a deliberate alias of stdout. Foreign streams keep their router.
pub(crate) fn write_diagnostic_if_captured(bytes: &[u8]) -> Result<bool, StdoutCaptureError> {
    let Some(callback) = Obj::stdio_stderr().and_then(|stream| stream.try_ctor_child(4)) else {
        return Ok(false);
    };
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        let Some(frame) = state
            .frames
            .iter_mut()
            .rev()
            .find(|frame| matches(frame, &callback))
        else {
            return Ok(false);
        };
        // Lossy UTF-8 cannot be shorter than these bytes. Refuse an already
        // impossible request before allocating its normalized representation.
        let minimum = frame
            .escaped_bytes
            .checked_add(bytes.len())
            .and_then(|n| n.checked_add(1));
        if minimum.is_none_or(|n| n > frame.limit) {
            let error = StdoutCaptureError::Limit {
                limit: frame.limit,
                requested: minimum.unwrap_or(usize::MAX),
            };
            frame.error.get_or_insert(error);
            return Err(frame.error.unwrap_or(error));
        }
        let line = String::from_utf8_lossy(bytes);
        append(frame, &[line.as_bytes(), b"\n"])?;
        Ok(true)
    })
}

/// Called only after the normal callback, canonical String, and world checks.
pub(super) fn write_if_captured(callback: &Obj, text: &Obj) -> Result<bool, StdoutCaptureError> {
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        let Some(frame) = state
            .frames
            .iter_mut()
            .rev()
            .find(|frame| matches(frame, callback))
        else {
            return Ok(false);
        };
        if let Some(error) = frame.error {
            return Err(error);
        }
        let Some((size, _, _, bytes)) = text.try_borrow_string_view() else {
            // The caller established canonical String shape before this hook.
            frame.error = Some(StdoutCaptureError::ScopeUnavailable);
            return Err(StdoutCaptureError::ScopeUnavailable);
        };
        let bytes = &bytes[..size - 1];
        append(frame, &[bytes])?;
        Ok(true)
    })
}

#[cfg(test)]
mod tests;
