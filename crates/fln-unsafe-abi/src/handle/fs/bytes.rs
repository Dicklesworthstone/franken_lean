use super::{FileIoError, FileReadError, Obj, file_result_transport, file_success_transport};
use crate::handle::native_stdio_ctor_shape;
use crate::stdio::FileReadFailure;

impl Obj {
    /// Write exactly the initialized, salient bytes of a borrowed native
    /// ByteArray to this exact native Handle. World must be scalar zero;
    /// scalar-array element width must be one and size must fit capacity.
    /// No spare capacity is inspected, copied, or written. NUL and invalid
    /// UTF-8 bytes are ordinary data, and neither input is consumed.
    ///
    /// The seven-field filesystem transport carries Unit scalar zero on
    /// success. Success means fwrite accepted every byte, including an empty
    /// write; it does not promise flush or close success. A post-write failure
    /// preserves errno and the reported prefix length without claiming rollback.
    pub fn try_file_write(&self, buffer: &Obj, world: &Obj) -> Result<Obj, FileIoError> {
        if !world.is_scalar() || world.unbox() != 0 {
            return Err(FileIoError::InvalidWorld);
        }
        if !canonical_file_byte_array(buffer) {
            return Err(FileIoError::InvalidByteArray);
        }
        if !self.is_file_handle() {
            return Err(FileIoError::InvalidHandle);
        }
        crate::stdio::initialize_io_signals();
        // SAFETY: exact live Handle and canonical ByteArray were established
        // before effects. Both remain borrowed; only its initialized prefix
        // enters fwrite and the helper returns one owned native result.
        // UNSAFE-LEDGER: FLN-UL-0657
        #[allow(unsafe_code)]
        let result = unsafe { crate::stdio::checked_handle_write(self.0, buffer.0) }.map_err(
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

    /// Borrow this exact native Handle and read at most the boxed native
    /// USize count with one fread. The entire requested capacity is bounded
    /// and allocated fallibly before reading. Zero count succeeds without
    /// touching FILE, including on a valid write-only Handle. Positive short
    /// reads succeed; zero at EOF clears the flag and returns an empty array.
    /// No newline, NUL, or UTF-8 processing occurs.
    ///
    /// Count must be tag-0, zero object fields, one native word of scalar
    /// storage; tagged Nat and mpz objects are refused. World must be scalar0.
    /// Neither input is consumed. The seven-field filesystem transport has
    /// a canonical native ByteArray payload only on success, scalar0 on error.
    /// Allocation/limit failures are resource nonanswers; they are never
    /// manufactured IO.Error values. The Handle and aliases remain usable.
    pub fn try_file_read(
        &self,
        count: &Obj,
        world: &Obj,
        max_bytes: usize,
    ) -> Result<Obj, FileReadError> {
        if !world.is_scalar() || world.unbox() != 0 {
            return Err(FileReadError::InvalidWorld);
        }
        if !self.is_file_handle() {
            return Err(FileReadError::InvalidHandle);
        }
        if !native_stdio_ctor_shape(count, 0, 0, size_of::<usize>()) {
            return Err(FileReadError::InvalidCount);
        }
        let count = count
            .try_ctor_scalar_u64(0)
            .and_then(|value| usize::try_from(value).ok())
            .ok_or(FileReadError::InvalidCount)?;
        // SAFETY: self keeps an exact native Handle alive, count is a native
        // word, and the helper bounds/allocation-checks before fread. A native
        // result transfers exactly one reference, wrapped immediately below.
        // UNSAFE-LEDGER: FLN-UL-0652
        #[allow(unsafe_code)]
        let result = unsafe { crate::stdio::checked_handle_read(self.0, count, max_bytes) }
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
        byte_result_transport(&result, count, bytes_consumed)
            .ok_or(FileReadError::MalformedResult { bytes_consumed })
    }
}

fn canonical_file_byte_array(buffer: &Obj) -> bool {
    if buffer.is_scalar()
        || buffer.header().tag != crate::contract::TAG_SCALAR_ARRAY
        || buffer.header().other != 1
    {
        return false;
    }
    // SAFETY: exact scalar-array category precedes header-field access.
    // Obj owns a live allocation; its salient prefix is initialized. Only
    // size and capacity are inspected, never uninitialized spare storage.
    // UNSAFE-LEDGER: FLN-UL-0656
    #[allow(unsafe_code)]
    let (_, size, capacity, _) = unsafe { crate::object::sarray_fields(buffer.0) };
    size <= capacity
}

fn byte_result_transport(result: &Obj, capacity: usize, consumed: usize) -> Option<Obj> {
    if native_stdio_ctor_shape(result, 1, 1, 0) {
        return file_result_transport(result, false);
    }
    if !native_stdio_ctor_shape(result, 0, 1, 0) {
        return None;
    }
    let payload = result.try_ctor_child(0)?;
    if payload.is_scalar()
        || payload.header().tag != crate::contract::TAG_SCALAR_ARRAY
        || payload.header().other != 1
    {
        return None;
    }
    // SAFETY: exact sarray tag and element width precede salient-field reads.
    // No capacity byte is inspected or copied. Only checked_handle_read can
    // supply this private helper in production; fread initialized its prefix.
    // UNSAFE-LEDGER: FLN-UL-0653
    #[allow(unsafe_code)]
    let (_, size, actual_capacity, _) = unsafe { crate::object::sarray_fields(payload.0) };
    if size != consumed || actual_capacity != capacity || size > capacity {
        return None;
    }
    Some(file_success_transport(payload))
}

#[cfg(test)]
mod tests;
