//! JSON execution keeps program stdout in a bounded field of its result.
//! The scope must be entered on the worker that runs Golem: native stdout is
//! thread-local. Human and Lean presentations retain ordinary native writes.

use super::{MultiplexerOutput, json_string};
use std::cell::Cell;

thread_local! {
    static JSON_PANIC: Cell<bool> = const { Cell::new(false) };
}

/// Process owners opt in once at startup; individual workers never replace
/// the global hook. Other threads and non-JSON work retain the previous hook.
pub(super) fn install_panic_hook() {
    static INSTALL: std::sync::Once = std::sync::Once::new();
    INSTALL.call_once(|| {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if !JSON_PANIC.try_with(Cell::get).unwrap_or(false) {
                previous(info);
            }
        }));
    });
}

struct JsonPanicScope(bool);

impl JsonPanicScope {
    fn enter() -> Self {
        Self(JSON_PANIC.with(|active| active.replace(true)))
    }
}

impl Drop for JsonPanicScope {
    fn drop(&mut self) {
        let _ = JSON_PANIC.try_with(|active| active.set(self.0));
    }
}

const MAX_DOCUMENT_BYTES: usize = 16 * 1024 * 1024;
// Every accepted byte must still fit in a resource-error envelope if the
// successful document's other fields leave insufficient space for stdout.
const ERROR_ENVELOPE_BYTES: usize = 1024;

pub(super) fn json(
    enabled: bool,
    schema: &str,
    work: impl FnOnce() -> MultiplexerOutput,
) -> MultiplexerOutput {
    if !enabled {
        return work();
    }
    let _panic_scope = JsonPanicScope::enter();
    let guard = match fln::StdoutCapture::begin(MAX_DOCUMENT_BYTES - ERROR_ENVELOPE_BYTES) {
        Ok(guard) => guard,
        Err(error) => return capture_failure(schema, error, &[]),
    };
    // Catch while the guard remains live so an internal fault preserves the
    // already accepted prefix and cannot leave a sink installed on the worker.
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(work));
    let captured = guard.finish();
    if let Some(error) = captured.error {
        return capture_failure(schema, error, &captured.bytes);
    }
    let output = match result {
        Ok(output) => output,
        Err(_) => {
            return failure(
                schema,
                "internal-fault",
                "execution worker panicked",
                4,
                &captured.bytes,
            );
        }
    };
    attach(schema, output, &captured.bytes)
}

pub(super) fn optional_json(
    enabled: bool,
    schema: &str,
    work: impl FnOnce() -> Option<MultiplexerOutput>,
) -> Option<MultiplexerOutput> {
    if !enabled {
        return work();
    }
    let mut selected = false;
    let output = json(true, schema, || match work() {
        Some(output) => {
            selected = true;
            output
        }
        None => MultiplexerOutput::success(String::new()),
    });
    // A setup failure must not fall through to an uncaptured execution path.
    (selected || output.exit_code != 0).then_some(output)
}

fn capture_failure(
    schema: &str,
    error: fln::StdoutCaptureError,
    bytes: &[u8],
) -> MultiplexerOutput {
    let (class, code) = match error {
        fln::StdoutCaptureError::Allocation | fln::StdoutCaptureError::Limit { .. } => {
            ("resource", 3)
        }
        fln::StdoutCaptureError::InvalidStdout => ("capability", 5),
        fln::StdoutCaptureError::ScopeUnavailable => ("internal-fault", 4),
    };
    failure(
        schema,
        class,
        &format!("stdout capture: {error:?}"),
        code,
        bytes,
    )
}

fn failure(schema: &str, class: &str, detail: &str, code: u8, bytes: &[u8]) -> MultiplexerOutput {
    // The boundary accepts only complete canonical UTF-8 String writes.
    let text = match std::str::from_utf8(bytes) {
        Ok(text) => text,
        Err(_) => {
            return MultiplexerOutput::failure(
                format!(
                    "{{\"schema\":{},\"outcome\":\"error\",\"authority\":false,\"class\":\"internal-fault\",\"detail\":\"stdout capture violated UTF-8 contract\",\"stdout\":\"\"}}\n",
                    json_string(schema)
                ),
                4,
            );
        }
    };
    MultiplexerOutput::failure(
        format!(
            "{{\"schema\":{},\"outcome\":\"error\",\"authority\":false,\"class\":{},\"detail\":{},\"detailTruncated\":false,\"stdout\":{}}}\n",
            json_string(schema),
            json_string(class),
            json_string(detail),
            json_string(text),
        ),
        code,
    )
}

fn attach(schema: &str, mut output: MultiplexerOutput, bytes: &[u8]) -> MultiplexerOutput {
    // Silent programs retain the existing JSON response byte-for-byte. Capture
    // failures are handled before this point, with their retained prefix.
    if bytes.is_empty() {
        return output;
    }
    let text = match std::str::from_utf8(bytes) {
        Ok(text) => text,
        Err(_) => {
            return failure(
                schema,
                "internal-fault",
                "stdout capture violated UTF-8 contract",
                4,
                bytes,
            );
        }
    };
    let document = match (output.stdout.is_empty(), output.stderr.is_empty()) {
        (false, true) => &mut output.stdout,
        (true, false) => &mut output.stderr,
        _ => {
            return failure(
                schema,
                "internal-fault",
                "execution produced ambiguous JSON channels",
                4,
                bytes,
            );
        }
    };
    // These are internal single-object renderers, never caller-supplied JSON.
    if !document.starts_with('{') || !document.ends_with("}\n") {
        return failure(
            schema,
            "internal-fault",
            "execution did not produce one JSON object",
            4,
            bytes,
        );
    }
    let encoded = json_string(text);
    let prefix = document.len() - 2;
    let separator = if prefix == 1 { "" } else { "," };
    let suffix = format!("{separator}\"stdout\":{encoded}}}\n");
    let length = prefix.checked_add(suffix.len());
    if length.is_none_or(|length| length > MAX_DOCUMENT_BYTES) {
        return failure(
            schema,
            "resource",
            "source program JSON output exceeds 16 MiB",
            3,
            bytes,
        );
    }
    if document.try_reserve(suffix.len()).is_err() {
        return failure(
            schema,
            "resource",
            "could not reserve captured stdout JSON",
            3,
            bytes,
        );
    }
    document.truncate(prefix);
    document.push_str(&suffix);
    output
}

#[cfg(test)]
mod tests;
