//! The pinned directory enumeration in a validated, compiler-neutral packet.
use super::{
    FileIoError, Obj, canonical_stdio_string, file_result_transport, file_success_transport,
    native_stdio_ctor_shape,
};

impl Obj {
    /// Enumerate a canonical String path with world scalar zero. The pin's
    /// native enumeration order, dot-entry filtering, filename UTF-8 recovery,
    /// embedded-NUL error and directory-error decoding are unchanged.
    ///
    /// The owned seven-field filesystem transport contains a native Array of
    /// neutral two-String records [root, fileName]. These records are not
    /// logical FilePath/DirEntry constructors; the compiler must rebuild its
    /// admitted shapes. Errors have scalar-zero payload and validated fields.
    /// Enumeration retains the native primitive's allocation behavior; this
    /// door does not claim an entry limit or interrupt an individual OS call.
    pub fn try_file_read_dir(filename: &Obj, world: &Obj) -> Result<Obj, FileIoError> {
        if !world.is_scalar() || world.unbox() != 0 {
            return Err(FileIoError::InvalidWorld);
        }
        if !canonical_stdio_string(filename) {
            return Err(FileIoError::InvalidFilename);
        }
        // SAFETY: the filename satisfies String's full law and remains
        // borrowed through opendir/readdir/closedir. The existing primitive
        // owns every entry and transfers exactly one native IO.Result here.
        // UNSAFE-LEDGER: FLN-UL-0658
        #[allow(unsafe_code)]
        let result = unsafe { Obj(crate::fs::prim_read_dir(filename.0)) };
        directory_result_transport(&result).ok_or(FileIoError::MalformedDirectoryResult)
    }
}

fn directory_result_transport(result: &Obj) -> Option<Obj> {
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
    let (length, _) = payload.try_array_view()?;
    for index in 0..length {
        let entry = payload.array_child(index);
        if !native_stdio_ctor_shape(&entry, 0, 2, 0) {
            return None;
        }
        for field in 0..2 {
            if !canonical_stdio_string(&entry.try_ctor_child(field)?) {
                return None;
            }
        }
    }
    Some(file_success_transport(payload))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shadow::{self, EventKind};
    use crate::tests::lock;
    use std::os::unix::ffi::OsStringExt;

    fn path(label: &str) -> std::path::PathBuf {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        std::env::temp_dir().join(format!(
            "fln-directory-{}-{nonce}-{label}",
            std::process::id()
        ))
    }

    fn field(value: &Obj, index: usize) -> Obj {
        assert!(native_stdio_ctor_shape(value, 0, 7, 0));
        value.try_ctor_child(index).unwrap()
    }

    fn text(value: &Obj) -> String {
        let (size, _, _, bytes) = value.try_string_view().unwrap();
        String::from_utf8(bytes[..size - 1].to_vec()).unwrap()
    }

    fn no_leaks() {
        let (events, live) = shadow::disable_and_drain();
        assert_eq!(live, 0, "every directory result reference must settle");
        assert!(!events.iter().any(|event| matches!(
            event.kind,
            EventKind::DoubleRelease | EventKind::ForeignPointer
        )));
    }

    #[test]
    fn directory_read_preserves_native_order_root_aliases_and_filename_recovery() {
        let _guard = lock();
        let directory = path("directory-native");
        std::fs::create_dir(&directory).unwrap();
        for name in ["z-last", "a-first", "λ🙂"] {
            std::fs::write(directory.join(name), b"retained fixture").unwrap();
        }
        let invalid = std::ffi::OsString::from_vec(b"raw-\xff-end".to_vec());
        std::fs::write(directory.join(invalid), b"retained raw filename").unwrap();
        let expected: Vec<_> = std::fs::read_dir(&directory)
            .unwrap()
            .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
            .collect();
        assert!(expected.iter().any(|name| name == "raw-\u{fffd}-end"));
        shadow::enable();
        {
            let filename = Obj::mk_string(directory.to_str().unwrap());
            let alias = filename.clone_ref();
            let before = filename.header().rc;
            {
                let result = Obj::try_file_read_dir(&filename, &Obj::mk_nat(0)).unwrap();
                assert_eq!(field(&result, 1).unbox(), 1);
                let array = field(&result, 0);
                assert_eq!(array.array_view().0, expected.len());
                let actual: Vec<_> = (0..expected.len())
                    .map(|index| {
                        let entry = array.array_child(index);
                        assert!(native_stdio_ctor_shape(&entry, 0, 2, 0));
                        assert_eq!(
                            text(&entry.try_ctor_child(0).unwrap()),
                            directory.to_str().unwrap()
                        );
                        text(&entry.try_ctor_child(1).unwrap())
                    })
                    .collect();
                assert_eq!(actual, expected, "native enumeration order is retained");
            }
            assert_eq!(filename.header().rc, before, "all entry roots settled");
            drop(filename);
            assert_eq!(text(&alias), directory.to_str().unwrap());
        }
        no_leaks();
    }

    #[test]
    fn directory_read_rejects_bad_inputs_and_preserves_native_error_packets() {
        let _guard = lock();
        let directory = path("directory-errors");
        std::fs::create_dir(&directory).unwrap();
        let file = directory.join("ordinary-file");
        std::fs::write(&file, b"unchanged").unwrap();
        let filename = Obj::mk_string(file.to_str().unwrap());
        assert!(matches!(
            Obj::try_file_read_dir(&filename, &Obj::mk_nat(1)),
            Err(FileIoError::InvalidWorld)
        ));
        assert!(matches!(
            Obj::try_file_read_dir(&Obj::mk_nat(0), &Obj::mk_nat(0)),
            Err(FileIoError::InvalidFilename)
        ));
        for (name, errno) in [
            (directory.join("missing").to_str().unwrap().to_owned(), 2),
            (file.to_str().unwrap().to_owned(), 20),
        ] {
            let result = Obj::try_file_read_dir(&Obj::mk_string(&name), &Obj::mk_nat(0)).unwrap();
            assert_eq!(field(&result, 0).unbox(), 0);
            assert_eq!(field(&result, 1).unbox(), 0);
            assert_eq!(field(&result, 3).unbox(), errno);
            assert_eq!(text(&field(&result, 5)), name);
        }
        let result = Obj::try_file_read_dir(&Obj::mk_string("bad\0path"), &Obj::mk_nat(0)).unwrap();
        assert_eq!(field(&result, 1).unbox(), 0);
        assert_eq!(text(&field(&result, 5)), "bad\0path");
        assert_eq!(std::fs::read(file).unwrap(), b"unchanged");
    }

    #[test]
    fn directory_transport_refuses_source_records_and_malformed_native_entries() {
        let _guard = lock();
        let string = || Obj::mk_string("name");
        for payload in [
            Obj::mk_nat(0),
            Obj::mk_ctor(0, vec![Obj::mk_array(Vec::new())], &[]),
            Obj::mk_array(vec![Obj::mk_ctor(0, vec![string()], &[])]),
            Obj::mk_array(vec![Obj::mk_ctor(1, vec![string(), string()], &[])]),
            Obj::mk_array(vec![Obj::mk_ctor(
                0,
                vec![Obj::mk_ctor(0, vec![string()], &[]), string()],
                &[],
            )]),
            Obj::mk_array(vec![Obj::mk_ctor(0, vec![string(), Obj::mk_nat(0)], &[])]),
        ] {
            assert!(directory_result_transport(&Obj::mk_ctor(0, vec![payload], &[])).is_none());
        }
        assert!(directory_result_transport(&Obj::mk_ctor(1, vec![string()], &[])).is_none());
        assert!(directory_result_transport(&Obj::mk_nat(0)).is_none());
    }
}
