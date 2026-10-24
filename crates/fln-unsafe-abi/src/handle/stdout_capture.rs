//! Explicit, thread-local memory sinks for reviewed native stream callbacks.
//! No native FILE is created, closed, or redirected. A retained callback binds
//! each scope to validated stdout and optionally stderr Handles; other Handles
//! keep normal fwrite.

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
    stderr_callback: Option<Obj>,
    bytes: Vec<u8>,
    escaped_bytes: usize,
    limit: usize,
    /// Raw isolation counts bytes as written. Evaluation capture counts escaped JSON bytes.
    count_raw: bool,
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
        Self::begin_streams(max_escaped_bytes, false, false)
    }

    /// Capture this thread's exact current native stdout and stderr in one
    /// ordered buffer. Native nonfatal panic and trace lines join the same
    /// bounded stream. This does not replace or empty the thread's stdin.
    pub fn begin_evaluation(max_escaped_bytes: usize) -> Result<Self, StdoutCaptureError> {
        Self::begin_streams(max_escaped_bytes, true, false)
    }

    /// Isolate this thread's stdout and optionally stderr into one ordered
    /// buffer whose allowance counts raw bytes, not JSON escapes.
    pub fn begin_isolated(
        max_bytes: usize,
        isolate_stderr: bool,
    ) -> Result<Self, StdoutCaptureError> {
        Self::begin_streams(max_bytes, isolate_stderr, true)
    }

    /// The current thread's first unsettled capture failure.
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

    /// Retain text in the enclosing memory capture. Absent scope refuses.
    pub fn append_current(text: &str) -> Result<(), StdoutCaptureError> {
        STATE.with(|state| {
            let mut state = state.borrow_mut();
            let frame = state
                .frames
                .last_mut()
                .ok_or(StdoutCaptureError::ScopeUnavailable)?;
            frame.append(text.as_bytes())
        })
    }

    fn begin_streams(
        max_escaped_bytes: usize,
        capture_stderr: bool,
        count_raw: bool,
    ) -> Result<Self, StdoutCaptureError> {
        let callback = Obj::stdio_stdout()
            .and_then(|stream| stream.try_ctor_child(4))
            .ok_or(StdoutCaptureError::InvalidStdout)?;
        // Both complete native streams must validate before a frame exists.
        let stderr_callback = if capture_stderr {
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
                stderr_callback,
                bytes: Vec::new(),
                escaped_bytes: 0,
                limit: max_escaped_bytes,
                count_raw,
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

impl Frame {
    fn matches(&self, callback: &Obj) -> bool {
        same_handle(callback, &self.callback)
            || self
                .stderr_callback
                .as_ref()
                .is_some_and(|stderr| same_handle(callback, stderr))
    }

    fn reserve_write(
        &mut self,
        raw_bytes: Option<usize>,
        escaped_bytes: Option<usize>,
    ) -> Result<usize, StdoutCaptureError> {
        if let Some(error) = self.error {
            return Err(error);
        }
        let requested = escaped_bytes.and_then(|length| self.escaped_bytes.checked_add(length));
        let error = if raw_bytes.is_none() || requested.is_none_or(|length| length > self.limit) {
            Some(StdoutCaptureError::Limit {
                limit: self.limit,
                requested: requested.unwrap_or(usize::MAX),
            })
        } else if self.bytes.try_reserve(raw_bytes.unwrap_or(0)).is_err() {
            Some(StdoutCaptureError::Allocation)
        } else {
            None
        };
        if let Some(error) = error {
            self.error = Some(error);
            return Err(error);
        }
        Ok(requested.expect("the complete write fits the capture limit"))
    }

    fn append(&mut self, bytes: &[u8]) -> Result<(), StdoutCaptureError> {
        let budget = if self.count_raw {
            Some(bytes.len())
        } else {
            escaped_length(bytes)
        };
        let requested = self.reserve_write(Some(bytes.len()), budget)?;
        self.bytes.extend_from_slice(bytes);
        self.escaped_bytes = requested;
        Ok(())
    }

    fn append_diagnostic(&mut self, message: &[u8]) -> Result<(), StdoutCaptureError> {
        if let Some(error) = self.error {
            return Err(error);
        }
        // Count lossy UTF-8 recovery and the added newline before allocating.
        // A refused message never builds an unbounded recovered String or
        // contributes a partial line to the capture.
        let mut raw_bytes = Some(1usize);
        let mut escaped_bytes = Some(2usize);
        lossy_chunks(message, |chunk| {
            raw_bytes = raw_bytes.and_then(|length| length.checked_add(chunk.len()));
            escaped_bytes = escaped_bytes.and_then(|length| {
                escaped_length(chunk).and_then(|extra| length.checked_add(extra))
            });
        });
        let budget = if self.count_raw { raw_bytes } else { escaped_bytes };
        let requested = self.reserve_write(raw_bytes, budget)?;
        lossy_chunks(message, |chunk| self.bytes.extend_from_slice(chunk));
        self.bytes.push(b'\n');
        self.escaped_bytes = requested;
        Ok(())
    }
}

fn lossy_chunks(mut bytes: &[u8], mut visit: impl FnMut(&[u8])) {
    loop {
        match std::str::from_utf8(bytes) {
            Ok(valid) => {
                visit(valid.as_bytes());
                return;
            }
            Err(error) => {
                let valid = error.valid_up_to();
                visit(&bytes[..valid]);
                visit("\u{fffd}".as_bytes());
                match error.error_len() {
                    Some(invalid) => bytes = &bytes[valid + invalid..],
                    None => return,
                }
            }
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
            .find(|frame| frame.matches(callback))
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
        frame.append(&bytes[..size - 1])?;
        Ok(true)
    })
}

/// The nonfatal native panic/trace route. A captured failure is handled too:
/// `finish` reports its sticky error, and no rejected bytes escape to fwrite.
pub(crate) fn diagnostic_if_captured(message: &[u8]) -> bool {
    if STATE
        .try_with(|state| state.borrow().frames.is_empty())
        .unwrap_or(true)
    {
        return false;
    }
    let Some(callback) = Obj::stdio_stderr().and_then(|stream| stream.try_ctor_child(4)) else {
        return false;
    };
    STATE
        .try_with(|state| {
            let mut state = state.borrow_mut();
            let Some(frame) = state
                .frames
                .iter_mut()
                .rev()
                .find(|frame| frame.matches(&callback))
            else {
                return false;
            };
            let _ = frame.append_diagnostic(message);
            true
        })
        .unwrap_or(false)
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod evaluation_tests;
