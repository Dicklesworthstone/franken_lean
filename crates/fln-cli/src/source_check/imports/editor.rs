//! Editor source closures: accepted open buffers override disk snapshots.
use super::*;
use fln_server::dispatch::OpenDocumentSource;

pub(in crate::source_check) struct Sources {
    pub(in crate::source_check) names: Vec<Name>,
    pub(in crate::source_check) sources: Vec<Vec<u8>>,
    pub(in crate::source_check) uris: Vec<String>,
}

fn hex(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

/// Local UTF-8 file URIs only. Preserve literal '+' and decode percent escapes
/// once. Fragments, queries, remote authorities and nonabsolute paths are refused.
pub(in crate::source_check) fn document_path(uri: &str) -> Result<PathBuf, Failure> {
    let rest = uri.strip_prefix("file://").ok_or_else(|| Failure::input("source imports require a local file URI"))?;
    let rest = if rest.starts_with('/') { rest } else {
        rest.strip_prefix("localhost").filter(|s| s.starts_with('/'))
            .ok_or_else(|| Failure::input("remote file URI authorities are unsupported"))?
    };
    if rest.contains(['?', '#']) {
        return Err(Failure::input("file URI queries and fragments are unsupported"));
    }
    let mut bytes = Vec::with_capacity(rest.len());
    let raw = rest.as_bytes();
    let mut index = 0usize;
    while index < raw.len() {
        if raw[index] == b'%' {
            let high = raw.get(index + 1).copied().and_then(hex);
            let low = raw.get(index + 2).copied().and_then(hex);
            let (Some(high), Some(low)) = (high, low) else {
                return Err(Failure::input("malformed percent escape in file URI"));
            };
            bytes.push(high * 16 + low);
            index += 3;
        } else {
            bytes.push(raw[index]);
            index += 1;
        }
    }
    let text = String::from_utf8(bytes).map_err(|_| Failure::input("file URI path is not UTF-8"))?;
    if text.contains('\0') { return Err(Failure::input("file URI path contains NUL")); }
    #[cfg(windows)]
    let text = if text.as_bytes().get(2) == Some(&b':') { text[1..].to_owned() } else { text };
    let path = PathBuf::from(text);
    if !path.is_absolute() { return Err(Failure::input("file URI path must be absolute")); }
    let parent = path.parent().ok_or_else(|| Failure::input("file URI needs a file name"))?;
    let parent = std::fs::canonicalize(parent).map_err(|e| Failure::io(parent, e))?;
    let name = path.file_name().ok_or_else(|| Failure::input("file URI needs a file name"))?;
    let path = parent.join(name);
    match std::fs::symlink_metadata(&path) {
        Ok(metadata) if metadata.file_type().is_symlink() || !metadata.is_file() => {
            Err(Failure::input("editor source is a symlink or not a regular file"))
        }
        Ok(_) => Ok(path),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(path),
        Err(error) => Err(Failure::io(&path, error)),
    }
}

fn file_uri(path: &Path) -> Result<String, Failure> {
    let text = path.to_str().ok_or_else(|| Failure::input("source path is not UTF-8"))?;
    #[cfg(windows)]
    let text = text.replace('\\', "/");
    let mut uri = String::from("file://");
    if !text.starts_with('/') { uri.push('/'); }
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    for byte in text.bytes() {
        if byte.is_ascii_alphanumeric() || matches!(byte, b'/' | b':' | b'-' | b'.' | b'_' | b'~') {
            uri.push(char::from(byte));
        } else {
            uri.push('%');
            uri.push(char::from(HEX[usize::from(byte >> 4)]));
            uri.push(char::from(HEX[usize::from(byte & 15)]));
        }
    }
    Ok(uri)
}

pub(in crate::source_check) fn load(
    uri: &str,
    text: &str,
    documents: &[OpenDocumentSource<'_>],
    max_bytes: usize,
) -> Result<Sources, Failure> {
    if text.len() > max_bytes { return Err(Failure::resource("editor source exceeds its byte limit")); }
    let header = parse_source_header(text.as_bytes()).map_err(|e| Failure::input(e.to_string()))?;
    // No filesystem authority is needed for import-free and untitled documents.
    if header.imports.is_empty() {
        return Ok(Sources {
            names: vec![Name::from_components(["__document"])],
            sources: vec![text.as_bytes().to_vec()], uris: vec![uri.to_owned()],
        });
    }
    let entry_path = document_path(uri)?;
    if entry_path.extension().and_then(|s| s.to_str()) != Some("lean") {
        return Err(Failure::input("source module entry needs a .lean extension"));
    }
    let stem = entry_path.file_stem().and_then(|s| s.to_str())
        .ok_or_else(|| Failure::input("source module entry needs a UTF-8 name"))?;
    validate_component(stem)?;
    let root = entry_path.parent().expect("normalized file parent");
    let entry_name = Name::from_components([stem]);
    let mut overlays = BTreeMap::new();
    for document in documents {
        let Ok(path) = document_path(document.uri) else { continue; };
        if !path.starts_with(root) { continue; }
        if let Some((previous, _)) = overlays.insert(path, (document.uri, document.text))
            && previous != document.uri
        {
            return Err(Failure::input("multiple open document URIs alias one source file"));
        }
    }
    if let Some((open_uri, _)) = overlays.get(&entry_path)
        && *open_uri != uri
    {
        return Err(Failure::input("another open document aliases this entry"));
    }
    let mut result = Sources {
        names: vec![entry_name.clone()], sources: vec![text.as_bytes().to_vec()], uris: vec![uri.to_owned()],
    };
    let mut by_name = BTreeMap::from([(entry_name.clone(), 0usize)]);
    let mut by_path = BTreeMap::from([(entry_path.clone(), entry_name)]);
    let mut total_bytes = text.len();
    let mut rows = 0usize;
    let mut cursor = 0usize;
    while cursor < result.sources.len() {
        let header = parse_source_header(&result.sources[cursor]).map_err(|e| {
            Failure::input(format!("{}: {e}", result.uris[cursor]))
        })?;
        rows = rows.checked_add(header.imports.len()).filter(|n| *n <= MAX_IMPORTS)
            .ok_or_else(|| Failure::resource("source import count exceeds 4096"))?;
        for name in header.imports {
            if by_name.contains_key(&name) { continue; }
            if result.sources.len() >= MAX_MODULES { return Err(Failure::resource("source module count exceeds 256")); }
            // The common resolver validates names and all on-disk path components.
            // A missing final file is legal only when an accepted editor buffer owns it.
            let path = checked_module_path(root, &name, true)?;
            if by_path.contains_key(&path) { return Err(Failure::input("source module paths alias one another")); }
            let remaining = max_bytes.checked_sub(total_bytes)
                .ok_or_else(|| Failure::resource("editor import closure exceeds its byte limit"))?;
            let (bytes, source_uri) = match overlays.get(&path) {
                Some((source_uri, Some(source))) => {
                    if source.len() > remaining { return Err(Failure::resource("editor import closure exceeds its byte limit")); }
                    (source.as_bytes().to_vec(), (*source_uri).to_owned())
                }
                Some((source_uri, None)) => {
                    return Err(Failure { class: "inconclusive", authority: false, exit: 3,
                        detail: format!("open imported document {source_uri} has no valid retained source; disk fallback is forbidden") });
                }
                None => {
                    let bytes = read_bounded(&path, remaining, "imported editor source").map_err(|error| Failure {
                        class: error.class(), detail: error.to_string(), authority: false, exit: error.exit_code(),
                    })?;
                    (bytes, file_uri(&path)?)
                }
            };
            total_bytes = total_bytes.checked_add(bytes.len()).filter(|n| *n <= max_bytes)
                .ok_or_else(|| Failure::resource("editor import closure exceeds its byte limit"))?;
            by_name.insert(name.clone(), result.sources.len());
            by_path.insert(path, name.clone());
            result.names.push(name);
            result.sources.push(bytes);
            result.uris.push(source_uri);
        }
        cursor += 1;
    }
    Ok(result)
}
