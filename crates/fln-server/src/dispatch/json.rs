// The structural JSON decoder is shared by Full and incremental synchronization.
// Include it in this module so its existing visibility and strict field rules
// remain unchanged; edit application can reuse its private parsing primitives.
include!("json/core.rs");

mod edits;
pub(super) use edits::content_changes_text_from;

mod files;
pub(super) use files::{RegistrationReply, registration_reply, supports_file_registration, watched_file_uris};
