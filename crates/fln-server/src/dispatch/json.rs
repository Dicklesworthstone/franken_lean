// The structural JSON decoder is shared by Full and incremental synchronization.
// Include it in this module so its existing visibility and strict field rules
// remain unchanged; edit application can reuse its private parsing primitives.
include!("json/core.rs");

mod edits;
pub(super) use edits::{Position, byte_offset};
pub(super) fn query_position(params: RawField<'_>) -> Result<Position, &'static str> {
    let RawField::Value(params) = params_object(params) else {
        return Err("position parameters require an object");
    };
    edits::position(object_field(params, "position"))
}

pub(super) use edits::content_changes_text_from;

mod files;
pub(super) use files::{
    RegistrationReply, registration_reply, supports_file_registration, watched_file_uris,
};
