// The structural JSON decoder is shared by Full and incremental synchronization.
// Include it in this module so its existing visibility and strict field rules
// remain unchanged; edit application can reuse its private parsing primitives.
include!("json/core.rs");

mod edits;
pub(super) use edits::{Position, byte_offset, position};
pub(super) fn query_position(params: RawField<'_>) -> Result<Position, &'static str> {
    let RawField::Value(params) = params_object(params) else {
        return Err("position parameters require an object");
    };
    edits::position(object_field(params, "position"))
}

pub(super) fn query_range(params: RawField<'_>) -> Result<(Position, Position), &'static str> {
    let RawField::Value(params) = params_object(params) else {
        return Err("range parameters require an object");
    };
    let RawField::Value(range) = object_field(params, "range") else {
        return Err("semantic token range requires one range");
    };
    let start = edits::position(object_field(range, "start"))?;
    let end = edits::position(object_field(range, "end"))?;
    if start > end {
        return Err("semantic token range is reversed");
    }
    Ok((start, end))
}

pub(super) use edits::content_changes_text_from;

mod files;
pub(super) use files::{
    RegistrationReply, registration_reply, supports_file_registration, watched_file_uris,
};

pub(super) mod rpc;
