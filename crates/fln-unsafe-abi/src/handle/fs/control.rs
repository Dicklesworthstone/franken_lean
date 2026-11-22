//! Checked cursor, truncation, and advisory-lock operations on native Handles.

use super::{FileIoError, Obj, file_result_transport, file_success_transport};
use crate::stdio::HandleControl;

impl Obj {
    /// Seek this borrowed native Handle to the beginning. This retains the
    /// epoch's fseek behavior, including flushing pending output before seeking.
    pub fn try_file_rewind(&self, world: &Obj) -> Result<Obj, FileIoError> {
        self.file_control(world, HandleControl::Rewind)
    }

    /// Truncate the file at this Handle's current position. Pending output is
    /// not implicitly flushed: callers that need it written must flush first.
    pub fn try_file_truncate(&self, world: &Obj) -> Result<Obj, FileIoError> {
        self.file_control(world, HandleControl::Truncate)
    }

    /// Acquire an exclusive or shared advisory lock, waiting for competing
    /// locks just as the epoch primitive does. The Handle remains borrowed.
    pub fn try_file_lock(&self, exclusive: bool, world: &Obj) -> Result<Obj, FileIoError> {
        self.file_control(world, HandleControl::Lock(exclusive))
    }

    /// Attempt an advisory lock without waiting. The neutral success payload
    /// is Bool: false means contention, while other OS failures remain errors.
    pub fn try_file_try_lock(&self, exclusive: bool, world: &Obj) -> Result<Obj, FileIoError> {
        self.file_control(world, HandleControl::TryLock(exclusive))
    }

    /// Release this Handle's advisory lock. Releasing an unlocked Handle has
    /// the same behavior as the native epoch primitive.
    pub fn try_file_unlock(&self, world: &Obj) -> Result<Obj, FileIoError> {
        self.file_control(world, HandleControl::Unlock)
    }

    fn file_control(&self, world: &Obj, operation: HandleControl) -> Result<Obj, FileIoError> {
        if !world.is_scalar() || world.unbox() != 0 {
            return Err(FileIoError::InvalidWorld);
        }
        if !self.is_file_handle() {
            return Err(FileIoError::InvalidHandle);
        }
        crate::stdio::initialize_io_signals();
        // SAFETY: the exact live Handle and world0 were validated before any
        // effect. The helper borrows its FILE and transfers one owned result.
        // UNSAFE-LEDGER: FLN-UL-0673
        #[allow(unsafe_code)]
        let result = unsafe { crate::stdio::checked_handle_control(self.0, operation) }
            .map_err(|errno| FileIoError::UnrepresentableControl { errno })?
            .ok_or(FileIoError::InvalidHandle)?;
        let result = Obj(result);
        control_result_transport(&result, matches!(operation, HandleControl::TryLock(_)))
            .ok_or(FileIoError::MalformedControlResult)
    }
}

fn control_result_transport(result: &Obj, boolean_success: bool) -> Option<Obj> {
    if !boolean_success || (!result.is_scalar() && result.header().tag == 1) {
        return file_result_transport(result, false);
    }
    if !super::native_stdio_ctor_shape(result, 0, 1, 0) {
        return None;
    }
    let payload = result.try_ctor_child(0)?;
    if !payload.is_scalar() || payload.unbox() > 1 {
        return None;
    }
    Some(file_success_transport(payload))
}

#[cfg(test)]
mod tests;
