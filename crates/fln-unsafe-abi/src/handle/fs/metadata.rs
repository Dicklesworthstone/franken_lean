//! File metadata crosses the membrane as bounded scalar data, never as a
//! native packed Metadata/SystemTime value pretending to be a logical record.
#![forbid(unsafe_code)]

use super::{
    FileIoError, Obj, canonical_stdio_string, file_result_transport, file_success_transport,
    native_stdio_ctor_shape,
};

impl Obj {
    /// Observe a canonical String path, following symbolic links, with world
    /// scalar zero. Returns the ordinary seven-field filesystem packet.
    ///
    /// Its success payload has nine object fields:
    /// [accessNegative, accessMagnitude, accessNsec, modifiedNegative,
    /// modifiedMagnitude, modifiedNsec, byteSize, fileType, numLinks].
    /// Negative seconds use Int.negSucc's predecessor magnitude. Every number
    /// is a native Nat; fileType is 0..=3 and nanoseconds are below one billion.
    /// The compiler rebuilds the separately checked logical data structures.
    pub fn try_file_metadata(filename: &Obj, world: &Obj) -> Result<Obj, FileIoError> {
        metadata(filename, world, false)
    }

    /// Observe a canonical String path without following its final symbolic
    /// link. The transport and preconditions are the same as try_file_metadata.
    /// Missing paths and embedded NUL remain the epoch's ordinary IO errors.
    pub fn try_file_symlink_metadata(filename: &Obj, world: &Obj) -> Result<Obj, FileIoError> {
        metadata(filename, world, true)
    }
}

fn metadata(filename: &Obj, world: &Obj, symlink: bool) -> Result<Obj, FileIoError> {
    if !world.is_scalar() || world.unbox() != 0 {
        return Err(FileIoError::InvalidWorld);
    }
    if !canonical_stdio_string(filename) {
        return Err(FileIoError::InvalidFilename);
    }
    // The existing ABI exports borrow the validated String and return one
    // owned native IO.Result. No source callback or unchecked pointer enters.
    let result = Obj(if symlink {
        crate::export::export_lean_io_symlink_metadata(filename.0)
    } else {
        crate::export::export_lean_io_metadata(filename.0)
    });
    metadata_result_transport(&result).ok_or(FileIoError::MalformedMetadataResult)
}

fn natural(value: u64) -> Obj {
    match usize::try_from(value) {
        Ok(value) if value <= crate::tagged::MAX_SMALL_NAT => Obj::mk_nat(value),
        _ => Obj::mk_mpz(&[value], false),
    }
}

/// Decode only the signed i64 timestamp domain supplied by stat. A native Int
/// is a small signed-u32 scalar or one normalized signed mpz limb; logical
/// Int constructors and wider/malformed values cannot enter this transport.
fn seconds(value: &Obj) -> Option<(bool, u64)> {
    let (negative, magnitude) = if value.is_scalar() {
        let bits = u32::try_from(value.unbox()).ok()?;
        let signed = i32::from_ne_bytes(bits.to_ne_bytes());
        (signed.is_negative(), u64::from(signed.unsigned_abs()))
    } else {
        let (_, sign, limbs) = value.try_mpz_view()?;
        let [magnitude] = limbs else {
            return None;
        };
        let negative = sign < 0;
        let maximum = (i64::MAX as u64) + u64::from(negative);
        if *magnitude == 0 || *magnitude > maximum {
            return None;
        }
        (negative, *magnitude)
    };
    Some((
        negative,
        if negative {
            magnitude.checked_sub(1)?
        } else {
            magnitude
        },
    ))
}

fn timestamp(value: &Obj) -> Option<[Obj; 3]> {
    if !native_stdio_ctor_shape(value, 0, 1, size_of::<u32>()) {
        return None;
    }
    let (negative, magnitude) = seconds(&value.try_ctor_child(0)?)?;
    let nsec = value.try_ctor_scalar_u32(size_of::<usize>())?;
    if nsec >= 1_000_000_000 {
        return None;
    }
    Some([
        Obj::mk_nat(usize::from(negative)),
        natural(magnitude),
        natural(u64::from(nsec)),
    ])
}

fn metadata_result_transport(result: &Obj) -> Option<Obj> {
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
    if !native_stdio_ctor_shape(&payload, 0, 2, 2 * size_of::<u64>() + size_of::<u8>()) {
        return None;
    }
    let accessed = timestamp(&payload.try_ctor_child(0)?)?;
    let modified = timestamp(&payload.try_ctor_child(1)?)?;
    let scalar = 2 * size_of::<usize>();
    let byte_size = payload.try_ctor_scalar_u64(scalar)?;
    let links = payload.try_ctor_scalar_u64(scalar + size_of::<u64>())?;
    // The allocator initializes the final padded word. Copy its first byte
    // through the existing checked u32 read; no uninitialized padding is read
    // and the scalar's meaning does not depend on the padding's contents.
    let file_type = payload
        .try_ctor_scalar_u32(scalar + 2 * size_of::<u64>())?
        .to_ne_bytes()[0];
    if file_type > 3 {
        return None;
    }
    let fields = accessed
        .into_iter()
        .chain(modified)
        .chain([
            natural(byte_size),
            Obj::mk_nat(usize::from(file_type)),
            natural(links),
        ])
        .collect();
    Some(file_success_transport(Obj::mk_ctor(0, fields, &[])))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shadow::{self, EventKind};
    use crate::tests::lock;
    use std::os::unix::fs::{MetadataExt, symlink};
    use std::path::PathBuf;
    use std::time::{Duration, SystemTime, UNIX_EPOCH};

    fn directory() -> PathBuf {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path =
            std::env::temp_dir().join(format!("fln-metadata-{}-{nonce}-λ", std::process::id()));
        std::fs::create_dir(&path).unwrap();
        path
    }

    fn number(value: &Obj) -> u64 {
        if value.is_scalar() {
            value.unbox() as u64
        } else {
            let (_, sign, limbs) = value.try_mpz_view().unwrap();
            assert_eq!(sign, 1);
            assert_eq!(limbs.len(), 1);
            limbs[0]
        }
    }

    fn packet(result: &Obj) -> Vec<u64> {
        assert!(native_stdio_ctor_shape(result, 0, 7, 0));
        assert_eq!(result.try_ctor_child(1).unwrap().unbox(), 1);
        let payload = result.try_ctor_child(0).unwrap();
        assert!(native_stdio_ctor_shape(&payload, 0, 9, 0));
        (0..9)
            .map(|index| number(&payload.try_ctor_child(index).unwrap()))
            .collect()
    }

    fn expected_time(sec: i64, nsec: i64) -> [u64; 3] {
        [
            u64::from(sec < 0),
            if sec < 0 {
                sec.unsigned_abs() - 1
            } else {
                sec as u64
            },
            nsec as u64,
        ]
    }

    #[test]
    fn metadata_preserves_real_files_symlinks_timestamps_and_borrowed_paths() {
        let _guard = lock();
        let root = directory();
        let file = root.join("data");
        let link = root.join("symbolic");
        let hard_link = root.join("hard");
        std::fs::write(&file, b"seven!!").unwrap();
        std::fs::hard_link(&file, &hard_link).unwrap();
        symlink(&file, &link).unwrap();
        // Exercise both sides of the native small-Int timestamp boundary.
        std::fs::File::open(&file)
            .unwrap()
            .set_times(
                std::fs::FileTimes::new()
                    .set_accessed(UNIX_EPOCH - Duration::new(1, 0))
                    .set_modified(UNIX_EPOCH + Duration::new(2_200_000_000, 123_456_789)),
            )
            .unwrap();
        let expected = std::fs::metadata(&file).unwrap();
        assert!(expected.mtime() > i64::from(i32::MAX));
        assert!(expected.atime() < 0);
        shadow::enable();
        {
            let world = Obj::mk_nat(0);
            let filename = Obj::mk_string(link.to_str().unwrap());
            let alias = filename.clone_ref();
            let before = filename.header().rc;
            let values = packet(&Obj::try_file_metadata(&filename, &world).unwrap());
            assert_eq!(
                &values[..3],
                &expected_time(expected.atime(), expected.atime_nsec())
            );
            assert_eq!(
                &values[3..6],
                &expected_time(expected.mtime(), expected.mtime_nsec())
            );
            assert_eq!(&values[6..], &[expected.size(), 1, expected.nlink()]);
            let symlink_values =
                packet(&Obj::try_file_symlink_metadata(&filename, &world).unwrap());
            assert_eq!(symlink_values[7], 2);
            assert_eq!(
                symlink_values[6],
                std::fs::symlink_metadata(&link).unwrap().size()
            );
            let directory_values = packet(
                &Obj::try_file_metadata(&Obj::mk_string(root.to_str().unwrap()), &world).unwrap(),
            );
            assert_eq!(directory_values[7], 0);
            assert_eq!(filename.header().rc, before);
            drop(filename);
            assert!(canonical_stdio_string(&alias));
        }
        let (events, live) = shadow::disable_and_drain();
        assert_eq!(live, 0, "all metadata references settle");
        assert!(!events.iter().any(|event| matches!(
            event.kind,
            EventKind::DoubleRelease | EventKind::ForeignPointer
        )));
    }

    #[test]
    fn metadata_keeps_missing_nul_and_dangling_link_errors_and_checks_inputs() {
        let _guard = lock();
        let root = directory();
        let missing = root.join("absent");
        let dangling = root.join("dangling");
        symlink(&missing, &dangling).unwrap();
        let world = Obj::mk_nat(0);
        for call in [Obj::try_file_metadata, Obj::try_file_symlink_metadata] {
            assert_eq!(
                call(&world, &world).err(),
                Some(FileIoError::InvalidFilename)
            );
            assert_eq!(
                call(&Obj::mk_string("valid"), &Obj::mk_nat(1)).err(),
                Some(FileIoError::InvalidWorld)
            );
            for path in [missing.to_str().unwrap(), "embedded\0nul"] {
                let result = call(&Obj::mk_string(path), &world).unwrap();
                assert_eq!(result.try_ctor_child(0).unwrap().unbox(), 0);
                assert_eq!(result.try_ctor_child(1).unwrap().unbox(), 0);
                let filename = result.try_ctor_child(5).unwrap();
                let (size, _, _, bytes) = filename.try_string_view().unwrap();
                assert_eq!(&bytes[..size - 1], path.as_bytes());
            }
        }
        let path = Obj::mk_string(dangling.to_str().unwrap());
        let followed = Obj::try_file_metadata(&path, &world).unwrap();
        assert_eq!(followed.try_ctor_child(1).unwrap().unbox(), 0);
        assert_eq!(
            packet(&Obj::try_file_symlink_metadata(&path, &world).unwrap())[7],
            2
        );
    }

    fn native_payload(accessed: Obj, modified: Obj, size: u64, links: u64, kind: u8) -> Obj {
        let scalars: Vec<_> = size
            .to_ne_bytes()
            .into_iter()
            .chain(links.to_ne_bytes())
            .chain([kind])
            .collect();
        Obj::mk_ctor(0, vec![accessed, modified], &scalars)
    }

    fn native_time(sec: i64, nsec: u32) -> Obj {
        Obj::mk_ctor(0, vec![Obj::mk_int(sec)], &nsec.to_ne_bytes())
    }

    #[test]
    fn metadata_transport_preserves_full_width_values_and_refuses_logical_lookalikes() {
        let _guard = lock();
        let value = Obj::mk_ctor(
            0,
            vec![native_payload(
                native_time(i64::MIN, 999_999_999),
                native_time(i64::MAX, 0),
                u64::MAX,
                u64::MAX,
                3,
            )],
            &[],
        );
        assert_eq!(
            packet(&metadata_result_transport(&value).unwrap()),
            vec![
                1,
                i64::MAX as u64,
                999_999_999,
                0,
                i64::MAX as u64,
                0,
                u64::MAX,
                3,
                u64::MAX
            ]
        );
        for payload in [
            Obj::mk_nat(0),
            Obj::mk_ctor(0, Vec::new(), &[]),
            native_payload(native_time(0, 1_000_000_000), native_time(0, 0), 1, 1, 1),
            native_payload(native_time(0, 0), native_time(0, 0), 1, 1, 4),
            native_payload(
                Obj::mk_ctor(0, vec![Obj::mk_string("not Int")], &0_u32.to_ne_bytes()),
                native_time(0, 0),
                1,
                1,
                1,
            ),
        ] {
            assert!(metadata_result_transport(&Obj::mk_ctor(0, vec![payload], &[])).is_none());
        }
        assert!(metadata_result_transport(&Obj::mk_ctor(1, vec![Obj::mk_nat(0)], &[])).is_none());
    }
}
