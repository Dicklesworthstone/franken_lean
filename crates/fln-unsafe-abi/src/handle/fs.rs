//! Concrete safe doors for the pinned Handle.mk and Handle.putStr rows.
//! Native packed IO.Result never escapes as the checked logical IO result.

use super::{Obj, canonical_stdio_string, native_stdio_ctor_shape, stdio_result_transport};

mod read;

/// A bounded getLine failure. Consumed counts refer to original file bytes,
/// including the input-cap lookahead; output observations count recovered
/// UTF-8 bytes. Resource stops do not rewind an already advanced cursor.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FileReadError {
    InvalidHandle,
    InvalidWorld,
    InputLimit {
        limit: usize,
        observed: usize,
        bytes_consumed: usize,
    },
    OutputLimit {
        limit: usize,
        observed: usize,
        bytes_consumed: usize,
    },
    Allocation {
        requested: usize,
        bytes_consumed: usize,
    },
    Unrepresentable {
        errno: i32,
        bytes_consumed: usize,
    },
    MalformedResult {
        bytes_consumed: usize,
    },
}

/// Invalid inputs are rejected before filesystem effects. The remaining
/// failures describe an attempted open/write and promise no rollback.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FileIoError {
    InvalidFilename,
    InvalidMode,
    InvalidHandle,
    InvalidString,
    InvalidWorld,
    MalformedOpenResult,
    UnrepresentableWrite { errno: i32, bytes_written: usize },
    MalformedWriteResult { bytes_written: usize },
}

impl Obj {
    /// Whether this object owns exactly a native FILE Handle. No raw pointer
    /// escapes and no external finalizer or callback is invoked.
    pub fn is_file_handle(&self) -> bool {
        // SAFETY: Obj guarantees a scalar or live object; the observer checks
        // its category and exact external class before reading its FILE.
        // UNSAFE-LEDGER: FLN-UL-0631
        #[allow(unsafe_code)]
        unsafe {
            crate::stdio::is_native_file_handle(self.0)
        }
    }

    /// Open the canonical String filename with exact Mode ordinal 0..=4 and
    /// world scalar zero. Filename NUL is the pin's logical invalidArgument
    /// error, not a truncated host path. Mode.write can truncate immediately.
    ///
    /// The owned neutral record has seven object fields:
    /// [payload, success, errorTag, osCode, hasFilename, filename, details].
    /// Success payload is the native Handle, all error fields zero/empty;
    /// failure payload is scalar zero and the validated native error data.
    /// This is neither a logical Handle constructor nor EST.Out.
    pub fn try_file_open(filename: &Obj, mode: &Obj, world: &Obj) -> Result<Obj, FileIoError> {
        if !world.is_scalar() || world.unbox() != 0 {
            return Err(FileIoError::InvalidWorld);
        }
        if !mode.is_scalar() || mode.unbox() > 4 {
            return Err(FileIoError::InvalidMode);
        }
        if !canonical_stdio_string(filename) {
            return Err(FileIoError::InvalidFilename);
        }
        // All input checks precede runtime initialization and filesystem work.
        // Reuse the pin's one-time SIGPIPE policy for file-only embeddings.
        crate::stdio::initialize_io_signals();
        // SAFETY: mode is bounded and filename satisfies String's full law;
        // primitive borrows it and transfers one owned native result here.
        // UNSAFE-LEDGER: FLN-UL-0632
        #[allow(unsafe_code)]
        let result = unsafe { Obj(crate::stdio::prim_handle_mk(filename.0, mode.unbox() as u8)) };
        file_result_transport(&result, true).ok_or(FileIoError::MalformedOpenResult)
    }

    /// Write exact String content bytes (including embedded NUL) to this
    /// borrowed native Handle. Success matches fwrite, not fflush/fsync;
    /// final close remains reference-count driven and ignores close errors.
    ///
    /// Returns the same seven-field neutral transport as try_file_open, with
    /// Unit scalar zero as success payload. A post-write failure retains the
    /// byte count reported by fwrite and may follow a visible prefix.
    pub fn try_file_put_str(&self, text: &Obj, world: &Obj) -> Result<Obj, FileIoError> {
        if !world.is_scalar() || world.unbox() != 0 {
            return Err(FileIoError::InvalidWorld);
        }
        if !canonical_stdio_string(text) {
            return Err(FileIoError::InvalidString);
        }
        if !self.is_file_handle() {
            return Err(FileIoError::InvalidHandle);
        }
        crate::stdio::initialize_io_signals();
        // SAFETY: exact Handle and canonical String established above, both
        // borrowed. No user-provided function pointer is called.
        // UNSAFE-LEDGER: FLN-UL-0633
        #[allow(unsafe_code)]
        let result = unsafe { crate::stdio::checked_handle_put_str(self.0, text.0) }.map_err(
            |(errno, bytes_written)| FileIoError::UnrepresentableWrite {
                errno,
                bytes_written,
            },
        )?;
        let (result, bytes_written) = result.ok_or(FileIoError::InvalidHandle)?;
        let result = Obj(result);
        file_result_transport(&result, false)
            .ok_or(FileIoError::MalformedWriteResult { bytes_written })
    }
}

fn file_result_transport(result: &Obj, handle_success: bool) -> Option<Obj> {
    if result.is_scalar() || result.header().tag > 1 {
        return None;
    }
    let success = result.header().tag == 0;
    if !native_stdio_ctor_shape(result, u8::from(!success), 1, 0) {
        return None;
    }
    if success {
        let payload = result.try_ctor_child(0)?;
        if if handle_success {
            !payload.is_file_handle()
        } else {
            !payload.is_scalar() || payload.unbox() != 0
        } {
            return None;
        }
        return Some(file_success_transport(payload));
    }
    // Reuse the complete nineteen-constructor packed error validation. No
    // error value is interpreted as an owned native Handle.
    let error = stdio_result_transport(result)?;
    let mut fields = Vec::with_capacity(7);
    fields.push(Obj::mk_nat(0));
    for field in 0..6 {
        fields.push(error.try_ctor_child(field)?);
    }
    Some(Obj::mk_ctor(0, fields, &[]))
}

fn file_success_transport(payload: Obj) -> Obj {
    Obj::mk_ctor(
        0,
        vec![
            payload,
            Obj::mk_nat(1),
            Obj::mk_nat(0),
            Obj::mk_nat(0),
            Obj::mk_nat(0),
            Obj::mk_string(""),
            Obj::mk_string(""),
        ],
        &[],
    )
}

fn string_result_transport(result: &Obj) -> Option<Obj> {
    if result.is_scalar() {
        return None;
    }
    if result.header().tag == 1 {
        return file_result_transport(result, false);
    }
    if !native_stdio_ctor_shape(result, 0, 1, 0) {
        return None;
    }
    let payload = result.try_ctor_child(0)?;
    if !canonical_stdio_string(&payload) {
        return None;
    }
    Some(file_success_transport(payload))
}

#[cfg(test)]
mod tests;
