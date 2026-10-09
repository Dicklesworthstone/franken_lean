use super::{FileReadError, Obj, string_result_transport};
use crate::stdio::FileReadFailure;

impl Obj {
    /// Bounded pinned Handle.getLine, borrowing the native Handle and world0.
    /// Newline/CR/NUL are retained. Invalid UTF-8 uses the pin's replacement
    /// walk; EOF returns an unterminated tail or an empty String and clears
    /// its flag. The Handle remains open and aliases share the advanced cursor.
    ///
    /// Returns the filesystem seven-field transport with String as the
    /// success payload. Errors with a native representation use the same
    /// validated IO.Error transport as open/write. Input/output limits and
    /// host buffer-allocation failures preserve consumed bytes and must be
    /// treated as resource nonanswers, never logical IO errors.
    ///
    /// At the input ceiling a single lookahead distinguishes EOF from a
    /// longer line: an additional byte is consumed and reported on failure.
    pub fn try_file_get_line(
        &self,
        world: &Obj,
        max_input_bytes: usize,
        max_output_bytes: usize,
    ) -> Result<Obj, FileReadError> {
        if !world.is_scalar() || world.unbox() != 0 {
            return Err(FileReadError::InvalidWorld);
        }
        if !self.is_file_handle() {
            return Err(FileReadError::InvalidHandle);
        }
        // SAFETY: exact native Handle checked, and self retains its FILE for
        // the entire bounded operation. The helper's lock is RAII; returned
        // native IO.Result has exactly one owned reference captured here.
        // UNSAFE-LEDGER: FLN-UL-0642
        #[allow(unsafe_code)]
        let result = unsafe {
            crate::stdio::checked_handle_get_line(self.0, max_input_bytes, max_output_bytes)
        }
        .map_err(|error| match error {
            FileReadFailure::InputLimit {
                limit,
                observed,
                bytes_consumed,
            } => FileReadError::InputLimit {
                limit,
                observed,
                bytes_consumed,
            },
            FileReadFailure::OutputLimit {
                limit,
                observed,
                bytes_consumed,
            } => FileReadError::OutputLimit {
                limit,
                observed,
                bytes_consumed,
            },
            FileReadFailure::Allocation {
                requested,
                bytes_consumed,
            } => FileReadError::Allocation {
                requested,
                bytes_consumed,
            },
            FileReadFailure::Unrepresentable {
                errno,
                bytes_consumed,
            } => FileReadError::Unrepresentable {
                errno,
                bytes_consumed,
            },
        })?;
        let (result, bytes_consumed) = result.ok_or(FileReadError::InvalidHandle)?;
        let result = Obj(result);
        string_result_transport(&result).ok_or(FileReadError::MalformedResult { bytes_consumed })
    }
}

#[cfg(test)]
mod tests;
