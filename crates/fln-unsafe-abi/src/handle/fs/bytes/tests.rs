use super::{FileIoError, FileReadError, Obj, byte_result_transport};
use crate::shadow::{self, EventKind};
use crate::tests::lock;
use std::io::Write;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

static SERIAL: AtomicUsize = AtomicUsize::new(0);
fn path(label: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "fln-read-bytes-{}-{}-{label}",
        std::process::id(),
        SERIAL.fetch_add(1, Ordering::Relaxed)
    ))
}
fn word(count: usize) -> Obj {
    Obj::mk_ctor(0, vec![], &count.to_ne_bytes())
}
fn open(path: &std::path::Path, mode: usize) -> Obj {
    let packet = Obj::try_file_open(
        &Obj::mk_string(path.to_str().unwrap()),
        &Obj::mk_nat(mode),
        &Obj::mk_nat(0),
    )
    .unwrap();
    assert_eq!(packet.try_ctor_child(1).unwrap().unbox(), 1);
    packet.try_ctor_child(0).unwrap()
}
fn bytes(packet: &Obj, requested: usize) -> Vec<u8> {
    assert_eq!(packet.header().other, 7);
    assert_eq!(packet.try_ctor_child(1).unwrap().unbox(), 1);
    let (width, size, capacity, bytes) =
        packet.try_ctor_child(0).unwrap().try_sarray_view().unwrap();
    assert_eq!(width, 1);
    assert_eq!(size, bytes.len());
    assert_eq!(capacity, requested);
    for index in 2..5 {
        assert_eq!(packet.try_ctor_child(index).unwrap().unbox(), 0);
    }
    bytes
}
fn read(handle: &Obj, count: usize) -> Vec<u8> {
    let packet = handle
        .try_file_read(&word(count), &Obj::mk_nat(0), 65536)
        .unwrap();
    bytes(&packet, count)
}
fn no_leaks() {
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0);
    assert!(
        events.iter().all(|event| !matches!(
            event.kind,
            EventKind::DoubleRelease | EventKind::ForeignPointer
        )),
        "ownership faults: {events:?}"
    );
}

fn written(packet: &Obj) {
    assert_eq!(packet.header().tag, 0);
    assert_eq!(packet.header().other, 7);
    assert_eq!(packet.try_ctor_child(0).unwrap().unbox(), 0);
    assert_eq!(packet.try_ctor_child(1).unwrap().unbox(), 1);
    for index in 2..5 {
        assert_eq!(packet.try_ctor_child(index).unwrap().unbox(), 0);
    }
    for index in 5..7 {
        assert_eq!(
            packet
                .try_ctor_child(index)
                .unwrap()
                .try_string_view()
                .unwrap()
                .3,
            [0]
        );
    }
}

#[test]
fn binary_write_preserves_raw_prefix_spare_capacity_aliases_and_borrows() {
    let _guard = lock();
    let source = path("write-source");
    let destination = path("write-destination");
    let input = [0, 0xff, 0x80, b'\n', 0xe2, 0x82, b'Z'];
    std::fs::write(&source, input).unwrap();
    shadow::enable();
    {
        let reader = open(&source, 0);
        // A positive short read initializes only its salient prefix. The
        // remaining native allocation has never been initialized or copied.
        let read_packet = reader
            .try_file_read(&word(4096), &Obj::mk_nat(0), 4096)
            .unwrap();
        let buffer = read_packet.try_ctor_child(0).unwrap();
        let view = buffer.try_sarray_view().unwrap();
        assert_eq!((view.0, view.1, view.2), (1, input.len(), 4096));
        assert_eq!(view.3, input);
        let buffer_alias = buffer.clone_ref();
        let handle = open(&destination, 1);
        let alias = handle.clone_ref();
        let world = Obj::mk_nat(0);
        let before = (handle.header().rc, buffer.header().rc);
        written(&handle.try_file_write(&buffer, &world).unwrap());
        assert_eq!((handle.header().rc, buffer.header().rc), before);
        assert_eq!(world.unbox(), 0);
        assert_eq!(buffer.try_sarray_view().unwrap().3, input);
        drop(handle);
        drop(buffer);
        written(&alias.try_file_write(&buffer_alias, &world).unwrap());
    }
    no_leaks();
    assert_eq!(std::fs::read(&destination).unwrap(), input.repeat(2));
    assert_eq!(std::fs::read(&source).unwrap(), input);
}

#[test]
fn binary_write_empty_and_read_only_errors_follow_native_status() {
    let _guard = lock();
    let path = path("write-read-only");
    let input = [0, 0xff, 0x80, b'Z'];
    std::fs::write(&path, input).unwrap();
    shadow::enable();
    {
        let handle = open(&path, 0);
        let empty = Obj::mk_sarray(1, &[]);
        let world = Obj::mk_nat(0);
        written(&handle.try_file_write(&empty, &world).unwrap());
        let buffer = Obj::mk_sarray(1, &input);
        let before = (handle.header().rc, buffer.header().rc);
        let failure = handle.try_file_write(&buffer, &world).unwrap();
        assert_eq!((handle.header().rc, buffer.header().rc), before);
        assert_eq!(failure.try_ctor_child(0).unwrap().unbox(), 0);
        assert_eq!(failure.try_ctor_child(1).unwrap().unbox(), 0);
        assert_eq!(failure.try_ctor_child(2).unwrap().unbox(), 12);
        assert_eq!(
            failure.try_ctor_child(3).unwrap().unbox(),
            crate::stdio::EBADF as usize
        );
        assert_eq!(failure.try_ctor_child(4).unwrap().unbox(), 0);
        written(&handle.try_file_write(&empty, &world).unwrap());
        assert_eq!(buffer.try_sarray_view().unwrap().3, input);
    }
    no_leaks();
    assert_eq!(std::fs::read(&path).unwrap(), input);
}

#[test]
fn binary_write_validates_all_borrowed_inputs_before_effects() {
    let _guard = lock();
    let path = path("write-preconditions");
    std::fs::write(&path, b"untouched").unwrap();
    shadow::enable();
    {
        let handle = open(&path, 3);
        let buffer = Obj::mk_sarray(1, &[0, 0xff]);
        let world = Obj::mk_nat(0);
        for bad_world in [Obj::mk_nat(1), Obj::mk_ctor(0, vec![], &[])] {
            assert!(matches!(
                handle.try_file_write(&buffer, &bad_world),
                Err(FileIoError::InvalidWorld)
            ));
        }
        for bad_buffer in [
            Obj::mk_nat(0),
            Obj::mk_string("wrong representation"),
            Obj::mk_ctor(0, vec![Obj::mk_sarray(1, &[1])], &[]),
            Obj::mk_array(vec![Obj::mk_nat(1)]),
            Obj::mk_sarray(2, &[1, 2]),
        ] {
            assert!(matches!(
                handle.try_file_write(&bad_buffer, &world),
                Err(FileIoError::InvalidByteArray)
            ));
        }
        let malformed = Obj::mk_sarray(1, &[0xee]);
        malformed.plant_sarray_size(2);
        let rejected = handle.try_file_write(&malformed, &world);
        malformed.restore_sarray_size(1);
        assert!(matches!(rejected, Err(FileIoError::InvalidByteArray)));
        for bad_handle in [
            Obj::mk_nat(0),
            Obj::mk_ref(Obj::mk_nat(0)),
            Obj::mk_external_counting(),
            Obj::mk_closure(2, vec![]),
        ] {
            assert!(matches!(
                bad_handle.try_file_write(&buffer, &world),
                Err(FileIoError::InvalidHandle)
            ));
        }
        assert_eq!(buffer.try_sarray_view().unwrap().3, [0, 0xff]);
    }
    no_leaks();
    assert_eq!(std::fs::read(&path).unwrap(), b"untouched");
}

#[test]
fn counted_read_preserves_raw_bytes_short_reads_shared_cursor_and_borrows() {
    let _guard = lock();
    let path = path("raw");
    let input = [0, 0xff, 0x80, b'\n', 0xe2, 0x82, b'Z'];
    std::fs::write(&path, input).unwrap();
    shadow::enable();
    {
        let handle = open(&path, 0);
        let alias = handle.clone_ref();
        let count = word(3);
        let world = Obj::mk_nat(0);
        let before_handle = handle.header().rc;
        let before_count = count.header().rc;
        let packet = handle.try_file_read(&count, &world, 65536).unwrap();
        assert_eq!(bytes(&packet, 3), input[..3]);
        assert_eq!(handle.header().rc, before_handle);
        assert_eq!(count.header().rc, before_count);
        assert_eq!(world.unbox(), 0);
        assert_eq!(read(&alias, 0), []);
        assert_eq!(read(&alias, 2), input[3..5]);
        drop(handle);
        assert_eq!(read(&alias, 9), input[5..], "positive short read");
        assert_eq!(read(&alias, 3), []);
        assert_eq!(read(&alias, 3), []);
    }
    no_leaks();
}

#[test]
fn counted_read_zero_does_not_touch_write_only_handles_and_errors_are_real() {
    let _guard = lock();
    let path = path("write-only");
    std::fs::write(&path, b"unchanged").unwrap();
    shadow::enable();
    {
        let handle = open(&path, 4);
        assert_eq!(read(&handle, 0), []);
        let packet = handle.try_file_read(&word(1), &Obj::mk_nat(0), 10).unwrap();
        assert_eq!(packet.try_ctor_child(0).unwrap().unbox(), 0);
        assert_eq!(packet.try_ctor_child(1).unwrap().unbox(), 0);
        assert_eq!(packet.try_ctor_child(2).unwrap().unbox(), 12);
        assert_eq!(packet.try_ctor_child(3).unwrap().unbox(), 9);
        assert_eq!(packet.try_ctor_child(4).unwrap().unbox(), 0);
        assert_eq!(read(&handle, 0), [], "zero ignores a prior FILE error");
    }
    no_leaks();
    assert_eq!(std::fs::read(&path).unwrap(), b"unchanged");
}

#[test]
fn counted_read_checks_handle_world_and_exact_native_word_before_cursor_effects() {
    let _guard = lock();
    let path = path("preconditions");
    std::fs::write(&path, b"keep").unwrap();
    shadow::enable();
    {
        let handle = open(&path, 0);
        for count in [
            Obj::mk_nat(1),
            Obj::mk_ctor(0, vec![], &[]),
            Obj::mk_ctor(1, vec![], &1usize.to_ne_bytes()),
            Obj::mk_ctor(0, vec![Obj::mk_nat(1)], &1usize.to_ne_bytes()),
            Obj::mk_ctor(0, vec![], &[0; 16]),
            Obj::mk_string("1"),
        ] {
            assert_eq!(
                handle
                    .try_file_read(&count, &Obj::mk_nat(0), 10)
                    .err()
                    .unwrap(),
                FileReadError::InvalidCount
            );
        }
        for world in [Obj::mk_nat(1), Obj::mk_ctor(0, vec![], &[])] {
            assert_eq!(
                handle.try_file_read(&word(1), &world, 10).err().unwrap(),
                FileReadError::InvalidWorld
            );
        }
        for handle in [Obj::mk_nat(0), Obj::mk_string("not a Handle")] {
            assert_eq!(
                handle
                    .try_file_read(&word(1), &Obj::mk_nat(0), 10)
                    .err()
                    .unwrap(),
                FileReadError::InvalidHandle
            );
        }
        assert_eq!(read(&handle, 4), b"keep");
    }
    no_leaks();
}

#[test]
fn counted_read_limit_and_impossible_allocation_stop_before_reading() {
    let _guard = lock();
    let path = path("limits");
    std::fs::write(&path, b"keep").unwrap();
    shadow::enable();
    {
        let handle = open(&path, 0);
        assert_eq!(
            handle
                .try_file_read(&word(5), &Obj::mk_nat(0), 4)
                .err()
                .unwrap(),
            FileReadError::InputLimit {
                limit: 4,
                observed: 5,
                bytes_consumed: 0,
            }
        );
        assert_eq!(
            handle
                .try_file_read(&word(usize::MAX), &Obj::mk_nat(0), usize::MAX)
                .err()
                .unwrap(),
            FileReadError::Allocation {
                requested: usize::MAX,
                bytes_consumed: 0,
            }
        );
        assert_eq!(
            handle
                .try_file_read(&word(isize::MAX as usize), &Obj::mk_nat(0), usize::MAX)
                .err()
                .unwrap(),
            FileReadError::Allocation {
                requested: (isize::MAX as usize)
                    .saturating_add(size_of::<crate::layout::LeanSarrayObject>()),
                bytes_consumed: 0,
            }
        );
        assert_eq!(read(&handle, 4), b"keep");
    }
    no_leaks();
}

#[test]
fn counted_read_preserves_positive_short_eof_flag_and_zero_read_does_not_clear_it() {
    let _guard = lock();
    let path = path("eof-append");
    std::fs::write(&path, b"A").unwrap();
    let handle = open(&path, 0);
    assert_eq!(read(&handle, 4), b"A");
    std::fs::OpenOptions::new()
        .append(true)
        .open(&path)
        .unwrap()
        .write_all(b"B")
        .unwrap();
    assert_eq!(
        read(&handle, 0),
        [],
        "zero leaves the existing EOF flag alone"
    );
    assert_eq!(read(&handle, 4), [], "first zero-at-EOF clears the flag");
    assert_eq!(read(&handle, 4), b"B");
    assert_eq!(read(&handle, 1), []);
    assert_eq!(read(&handle, 1), []);
}

#[test]
fn counted_read_private_transport_rejects_wrong_payload_width_size_and_capacity() {
    let _guard = lock();
    shadow::enable();
    {
        for payload in [
            Obj::mk_nat(0),
            Obj::mk_string("A"),
            Obj::mk_sarray(2, &[0, 1]),
        ] {
            let result = Obj::mk_ctor(0, vec![payload], &[]);
            assert!(byte_result_transport(&result, 1, 1).is_none());
        }
        let result = Obj::mk_ctor(0, vec![Obj::mk_sarray(1, &[0xff, 0])], &[]);
        assert!(byte_result_transport(&result, 2, 1).is_none());
        assert!(byte_result_transport(&result, 3, 2).is_none());
        assert_eq!(
            bytes(&byte_result_transport(&result, 2, 2).unwrap(), 2),
            [0xff, 0]
        );
        assert!(byte_result_transport(&Obj::mk_ctor(0, vec![], &[]), 0, 0).is_none());
    }
    no_leaks();
}
