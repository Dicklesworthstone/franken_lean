//! The filesystem plane: the errno-decoded fs prim family — bead `fln-3gv`
//! slice 6a, porting `io.cpp:372-382` (`lean_chmod`), `io.cpp:1169-1183`
//! (`create_dir`), `io.cpp:1185-1195` (`remove_dir`), `io.cpp:1197-1227`
//! non-Windows arm (`rename`), `io.cpp:1064-1086` (`read_dir`),
//! `io.cpp:1002-1055` non-Windows arm (`realpath`), and `io.cpp:1409-1417`
//! (`current_dir`) at the pin.
//!
//! The uv-decoded members — whose observable error shape is libuv's
//! (negative codes, `uv_strerror` details) — run through the MEASURED
//! decoder below: `remove_file`/`hard_link` (slice 6b) and the temp family
//! (slice 6c). Deliberately NOT here, named rather than implied:
//! `metadata`/`symlink_metadata` (the uv_stat shapes, a later slice) and
//! `app_path`/`getenv`, the env/misc family.
//!
//! Mechanism deviations, disclosed:
//! - **`rename`'s errno is captured at the failure site.** The pin builds
//!   its "A and/or B" filename string first and reads `errno` after; ours
//!   snapshots `errno` immediately after the failed `rename(2)`, so an
//!   allocator syscall inside the string build cannot clobber the code. The
//!   observable differs only where the pin's own is unspecified.
//! - **Platform layout facts are measured, not transcribed**: `PATH_MAX`
//!   and `offsetof(struct dirent, d_name)` come from
//!   `tribunal/fixtures/c4/errno_extract.c` — rerun it to re-derive.
//!
//! Platform posture: Linux/glibc only, exactly like [`crate::stdio`].

use core::ffi::{c_char, c_int, c_void};

use crate::layout::LeanObject;
use crate::stdio::{
    ERR_NO_FILE_OR_DIRECTORY, decode_io_error, err_code_details, err_file_code_details,
    err_optfile_code_details, errno, io_result_mk_error, io_result_mk_ok, mk_embedded_nul_error,
    mk_string, opt_of_borrowed,
};
use crate::{object, rc, tagged};

// ---------------------------------------------------------------- platform

// UNSAFE-LEDGER: FLN-UL-0344
#[allow(unsafe_code)]
unsafe extern "C" {
    fn chmod(path: *const c_char, mode: u32) -> c_int;
    fn mkdir(path: *const c_char, mode: u32) -> c_int;
    fn rmdir(path: *const c_char) -> c_int;
    fn rename(from: *const c_char, to: *const c_char) -> c_int;
    fn getcwd(buf: *mut c_char, size: usize) -> *mut c_char;
    fn realpath(path: *const c_char, resolved: *mut c_char) -> *mut c_char;
    fn opendir(name: *const c_char) -> *mut c_void;
    fn readdir(dirp: *mut c_void) -> *mut c_void;
    fn closedir(dirp: *mut c_void) -> c_int;
    fn mkostemp(template: *mut c_char, flags: c_int) -> c_int;
    fn mkdtemp(template: *mut c_char) -> *mut c_char;
    fn fdopen(fd: c_int, mode: *const c_char) -> *mut c_void;
    fn stat(path: *const c_char, buf: *mut c_void) -> c_int;
    fn lstat(path: *const c_char, buf: *mut c_void) -> c_int;
    fn unlink(path: *const c_char) -> c_int;
    fn link(orig: *const c_char, new_path: *const c_char) -> c_int;
}

// Measured constants (errno_extract.c on this platform's headers).
const PATH_MAX: usize = 4096;
const DIRENT_D_NAME_OFFSET: usize = 19;

/// The pin's embedded-NUL precondition, shared by every fs prim: the
/// C-string length must be exactly the string's byte size minus its NUL.
/// Answers the NUL-terminated bytes, or None when a NUL is embedded.
///
/// # Safety
/// `s` is a borrowed live string object.
// UNSAFE-LEDGER: FLN-UL-0345
#[allow(unsafe_code)]
unsafe fn cstr_of(s: *mut LeanObject) -> Option<Vec<u8>> {
    // SAFETY: string fields read within the live object; the copied bytes
    // are NUL-terminated by the string law.
    unsafe {
        let (m_size, _, _, bytes) = object::string_fields(s);
        let nul_at = bytes.iter().position(|&b| b == 0).unwrap_or(m_size);
        if nul_at == m_size - 1 {
            Some(bytes)
        } else {
            None
        }
    }
}

// ---------------------------------------------------------------- prims

/// `lean_chmod` (`io.cpp:372-382`; the extern census `IO.setAccessRights`):
/// chmod(2); failure decodes errno with the filename.
///
/// # Safety
/// `filename` is borrowed and live; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0346
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_chmod(filename: *mut LeanObject, mode: u32) -> *mut LeanObject {
    // SAFETY: live string per contract; fresh result objects.
    unsafe {
        let Some(bytes) = cstr_of(filename) else {
            return mk_embedded_nul_error(filename);
        };
        if chmod(bytes.as_ptr().cast::<c_char>(), mode) == 0 {
            io_result_mk_ok(tagged::boxi(0))
        } else {
            io_result_mk_error(decode_io_error(errno(), filename))
        }
    }
}

/// `lean_io_create_dir` (`io.cpp:1169-1183`): mkdir mode 0777 (the umask
/// applies, as the pin's); failure decodes errno with the path.
///
/// # Safety
/// `p` is borrowed and live; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0347
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_create_dir(p: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: live string per contract; fresh result objects.
    unsafe {
        let Some(bytes) = cstr_of(p) else {
            return mk_embedded_nul_error(p);
        };
        if mkdir(bytes.as_ptr().cast::<c_char>(), 0o777) == 0 {
            io_result_mk_ok(tagged::boxi(0))
        } else {
            io_result_mk_error(decode_io_error(errno(), p))
        }
    }
}

/// `lean_io_remove_dir` (`io.cpp:1185-1195`): rmdir; failure decodes errno
/// with the path.
///
/// # Safety
/// `p` is borrowed and live; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0348
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_remove_dir(p: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: live string per contract; fresh result objects.
    unsafe {
        let Some(bytes) = cstr_of(p) else {
            return mk_embedded_nul_error(p);
        };
        if rmdir(bytes.as_ptr().cast::<c_char>()) == 0 {
            io_result_mk_ok(tagged::boxi(0))
        } else {
            io_result_mk_error(decode_io_error(errno(), p))
        }
    }
}

/// `lean_io_rename` (`io.cpp:1197-1227`, the non-Windows arm): rename(2);
/// failure decodes errno against the pin's synthesized `"A and/or B"`
/// filename (built and released here exactly as the pin's `object_ref`).
///
/// # Safety
/// `from` and `to` are borrowed and live; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0349
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_rename(from: *mut LeanObject, to: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: live strings per contract; the synthesized filename is owned
    // here and released after the decoder duplicates what it keeps.
    unsafe {
        let Some(from_bytes) = cstr_of(from) else {
            return mk_embedded_nul_error(from);
        };
        let Some(to_bytes) = cstr_of(to) else {
            return mk_embedded_nul_error(to);
        };
        if rename(
            from_bytes.as_ptr().cast::<c_char>(),
            to_bytes.as_ptr().cast::<c_char>(),
        ) == 0
        {
            return io_result_mk_ok(tagged::boxi(0));
        }
        let code = errno();
        let from_str = String::from_utf8_lossy(&from_bytes[..from_bytes.len() - 1]).into_owned();
        let to_str = String::from_utf8_lossy(&to_bytes[..to_bytes.len() - 1]).into_owned();
        let joined = mk_string(&format!("{from_str} and/or {to_str}"));
        let err = io_result_mk_error(decode_io_error(code, joined));
        rc::dec_ref(joined);
        err
    }
}

/// `lean_io_current_dir` (`io.cpp:1409-1417`): getcwd into a PATH_MAX
/// buffer; failure is the pin's bare `userError` string (tag 18), not an
/// errno decode.
///
/// # Safety
/// Caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0350
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_current_dir() -> *mut LeanObject {
    // SAFETY: getcwd writes at most PATH_MAX bytes into the local buffer;
    // fresh result objects.
    unsafe {
        let mut buf = [0u8; PATH_MAX];
        if getcwd(buf.as_mut_ptr().cast::<c_char>(), PATH_MAX).is_null() {
            let msg = mk_string("failed to retrieve current working directory");
            let user_err = object::alloc_ctor(18, 1, 0);
            object::ctor_set(user_err, 0, msg);
            io_result_mk_error(user_err)
        } else {
            let n = buf.iter().position(|&b| b == 0).unwrap_or(PATH_MAX);
            io_result_mk_ok(crate::export::mk_string_from_bytes_impl(
                buf.as_ptr().cast::<c_char>(),
                n,
            ))
        }
    }
}

/// `lean_io_realpath` (`io.cpp:1002-1055`, the non-Windows arm). NOTE the
/// pin's own signature: `filename` arrives OWNED (`obj_arg`), unlike every
/// sibling, and is released on every arm; failure is the pin's
/// `mk_file_not_found_error` — noFileOrDirectory with ENOENT and EMPTY
/// details (`io.cpp:85-90`), never a strerror decode.
///
/// # Safety
/// `filename` is consumed; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0351
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_realpath(filename: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: live string per contract; realpath writes at most PATH_MAX
    // bytes into the local buffer; every arm settles the owned argument.
    unsafe {
        let Some(bytes) = cstr_of(filename) else {
            let res = mk_embedded_nul_error(filename);
            rc::dec_ref(filename);
            return res;
        };
        let mut buf = [0u8; PATH_MAX];
        if realpath(
            bytes.as_ptr().cast::<c_char>(),
            buf.as_mut_ptr().cast::<c_char>(),
        )
        .is_null()
        {
            rc::inc_ref_n(filename, 1);
            let err = crate::stdio::err_file_code_details(
                ERR_NO_FILE_OR_DIRECTORY,
                filename,
                super::stdio::ENOENT as u32,
                mk_string(""),
            );
            let res = io_result_mk_error(err);
            rc::dec_ref(filename);
            res
        } else {
            let n = buf.iter().position(|&b| b == 0).unwrap_or(PATH_MAX);
            let s = crate::export::mk_string_from_bytes_impl(buf.as_ptr().cast::<c_char>(), n);
            rc::dec_ref(filename);
            io_result_mk_ok(s)
        }
    }
}

/// `lean_io_read_dir` (`io.cpp:1064-1086`): opendir/readdir/closedir with
/// `.` and `..` skipped; each entry is the two-field `DirEntry` ctor
/// (root = the borrowed dirname duplicated, filename = the entry name
/// through the validating string constructor); a closedir failure is an
/// invariant fault exactly as the pin's `lean_always_assert`.
///
/// # Safety
/// `dirname` is borrowed and live; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0352
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_read_dir(dirname: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: live string per contract; each dirent's d_name is read as a
    // NUL-terminated C string at the measured field offset while the
    // stream is open; every fresh object's slots settle before escape.
    unsafe {
        let Some(bytes) = cstr_of(dirname) else {
            return mk_embedded_nul_error(dirname);
        };
        let dp = opendir(bytes.as_ptr().cast::<c_char>());
        if dp.is_null() {
            return io_result_mk_error(decode_io_error(errno(), dirname));
        }
        let mut arr = object::alloc_array(0, 0);
        loop {
            let entry = readdir(dp);
            if entry.is_null() {
                break;
            }
            let name = entry.cast::<u8>().add(DIRENT_D_NAME_OFFSET);
            let mut len = 0usize;
            while *name.add(len) != 0 {
                len += 1;
            }
            let name_bytes = core::slice::from_raw_parts(name, len);
            if name_bytes == b"." || name_bytes == b".." {
                continue;
            }
            let lentry = object::alloc_ctor(0, 2, 0);
            rc::inc_ref_n(dirname, 1);
            object::ctor_set(lentry, 0, dirname);
            object::ctor_set(
                lentry,
                1,
                crate::export::mk_string_from_bytes_impl(name.cast::<c_char>(), len),
            );
            arr = crate::export::export_lean_array_push(arr, lentry);
        }
        if closedir(dp) != 0 {
            crate::export::internal_panic_impl("read_dir: closedir failed");
        }
        io_result_mk_ok(arr)
    }
}

// ------------------------------------------------- the uv-decoded members

use crate::stdio::{
    E2BIG, EACCES, EADDRINUSE, EADDRNOTAVAIL, EAFNOSUPPORT, EAGAIN, EBADF, EBADMSG, EBUSY, ECHILD,
    ECONNABORTED, ECONNREFUSED, ECONNRESET, EDEADLK, EDESTADDRREQ, EDOM, EEXIST, EFAULT, EFBIG,
    EHOSTUNREACH, EIDRM, EILSEQ, EINPROGRESS, EINTR, EINVAL, EIO, EISCONN, EISDIR, ELOOP, EMFILE,
    EMLINK, EMSGSIZE, ENAMETOOLONG, ENETDOWN, ENETRESET, ENETUNREACH, ENFILE, ENOBUFS, ENODATA,
    ENODEV, ENOENT, ENOEXEC, ENOLCK, ENOLINK, ENOMEM, ENOMSG, ENOPROTOOPT, ENOSPC, ENOSR, ENOSTR,
    ENOSYS, ENOTCONN, ENOTDIR, ENOTEMPTY, ENOTSOCK, ENOTTY, ENXIO, EOPNOTSUPP, EPERM, EPIPE,
    EPROTO, EPROTONOSUPPORT, EPROTOTYPE, ERANGE, EROFS, ESPIPE, ESRCH, ETIME, ETIMEDOUT, ETXTBSY,
    EXDEV,
};

// GENERATED from `tribunal/fixtures/c4/uv_error_contract.txt` — measured by
// `uv_error_extract.c` from the Reference's own exported
// `lean_decode_uv_error` at the pin (D5/D9: mined, never hand-transcribed).
// Regenerate with the extractor; never hand-edit a row.
// (errno, IO.Error variant tag, libuv uv_strerror details.)
#[rustfmt::skip]
const UV_ERROR_ROWS: &[(c_int, u8, &str)] = &[
    (EINTR, 10, "interrupted system call"),
    (ELOOP, 12, "too many symbolic links encountered"),
    (ENAMETOOLONG, 12, "name too long"),
    (EDESTADDRREQ, 12, "destination address required"),
    (EBADF, 12, "bad file descriptor"),
    (EDOM, 1, "Unknown system error -33"),
    (EINVAL, 12, "invalid argument"),
    (EILSEQ, 12, "illegal byte sequence"),
    (ENOEXEC, 1, "Unknown system error -8"),
    (ENOSTR, 1, "Unknown system error -60"),
    (ENOTCONN, 12, "socket is not connected"),
    (ENOTSOCK, 12, "socket operation on non-socket"),
    (ENOENT, 11, "no such file or directory"),
    (EACCES, 13, "permission denied"),
    (EROFS, 13, "read-only file system"),
    (ECONNABORTED, 13, "software caused connection abort"),
    (EFBIG, 13, "file too large"),
    (EPERM, 13, "operation not permitted"),
    (EMFILE, 14, "too many open files"),
    (ENFILE, 14, "file table overflow"),
    (ENOSPC, 14, "no space left on device"),
    (E2BIG, 14, "argument list too long"),
    (EAGAIN, 14, "resource temporarily unavailable"),
    (EMLINK, 14, "too many links"),
    (EMSGSIZE, 14, "message too long"),
    (ENOBUFS, 14, "no buffer space available"),
    (ENOLCK, 1, "Unknown system error -37"),
    (ENOMEM, 14, "not enough memory"),
    (ENOSR, 1, "Unknown system error -63"),
    (EISDIR, 15, "illegal operation on a directory"),
    (EBADMSG, 1, "Unknown system error -74"),
    (ENOTDIR, 15, "not a directory"),
    (ENXIO, 16, "no such device or address"),
    (EHOSTUNREACH, 16, "host is unreachable"),
    (ENETUNREACH, 16, "network is unreachable"),
    (ECHILD, 1, "Unknown system error -10"),
    (ECONNREFUSED, 16, "connection refused"),
    (ENODATA, 16, "no data available"),
    (ENOMSG, 1, "Unknown system error -42"),
    (ESRCH, 16, "no such process"),
    (EEXIST, 0, "file already exists"),
    (EINPROGRESS, 1, "Unknown system error -115"),
    (EISCONN, 0, "socket is already connected"),
    (EIO, 5, "i/o error"),
    (ENOTEMPTY, 6, "directory not empty"),
    (ENOTTY, 7, "inappropriate ioctl for device"),
    (ECONNRESET, 3, "connection reset by peer"),
    (EIDRM, 1, "Unknown system error -43"),
    (ENETDOWN, 3, "network is down"),
    (ENETRESET, 1, "Unknown system error -102"),
    (ENOLINK, 1, "Unknown system error -67"),
    (EPIPE, 3, "broken pipe"),
    (EPROTO, 8, "protocol error"),
    (EPROTONOSUPPORT, 8, "protocol not supported"),
    (EPROTOTYPE, 8, "protocol wrong type for socket"),
    (ETIME, 1, "Unknown system error -62"),
    (ETIMEDOUT, 9, "connection timed out"),
    (EADDRINUSE, 2, "address already in use"),
    (EBUSY, 2, "resource busy or locked"),
    (EDEADLK, 1, "Unknown system error -35"),
    (ETXTBSY, 2, "text file is busy"),
    (EADDRNOTAVAIL, 4, "address not available"),
    (EAFNOSUPPORT, 4, "address family not supported"),
    (ENODEV, 4, "no such device"),
    (ENOPROTOOPT, 4, "protocol not available"),
    (ENOSYS, 4, "function not implemented"),
    (EOPNOTSUPP, 4, "operation not supported on socket"),
    (ERANGE, 4, "result too large"),
    (ESPIPE, 4, "invalid seek"),
    (EXDEV, 4, "cross-device link not permitted"),
    (EFAULT, 1, "bad address in system call argument"),
];

/// The `lean_decode_uv_error` twin (`io.cpp:258-363`) for the fs members
/// the pin routes through libuv: the input is libuv's NEGATED errno (what
/// `uv_fs_unlink`/`uv_fs_link` return on POSIX), the stored osCode is that
/// negative value wrapped into u32 exactly as the pin's int-to-uint32
/// conversion, and the details are libuv's `uv_strerror` strings — measured
/// per errno in the generated table above, with libuv's own
/// "Unknown system error N" shape for every code its map lacks.
///
/// # Safety
/// `fname` is borrowed and live; caller owns the result.
// UNSAFE-LEDGER: FLN-UL-0361
#[allow(unsafe_code)]
unsafe fn decode_uv_error(neg: c_int, fname: *mut LeanObject) -> *mut LeanObject {
    let e = -neg;
    let (tag, details_text) = UV_ERROR_ROWS
        .iter()
        .find(|&&(row_e, _, _)| row_e == e)
        .map_or_else(
            || (1u8, format!("Unknown system error {neg}")),
            |&(_, t, d)| (t, d.to_string()),
        );
    let code = neg as u32;
    // SAFETY: every builder consumes its freshly built arguments; the
    // ctor families are exactly the errno decoder's (the pin keeps the two
    // switches in sync and the measured tags confirm it).
    unsafe {
        let details = mk_string(&details_text);
        match tag {
            // (filename : String) families — interrupted, noFileOrDirectory.
            // The pin lean_asserts fname non-null here (io.cpp:262/278); a
            // null in release is the pin's own UB, refused typed instead.
            10 | 11 => {
                if fname.is_null() {
                    crate::export::internal_panic_impl(
                        "decode_uv_error: bare-String variant with no filename",
                    );
                }
                rc::inc_ref_n(fname, 1);
                err_file_code_details(tag, fname, code, details)
            }
            // (filename : Option String) families.
            0 | 12 | 13 | 14 | 15 | 16 => {
                err_optfile_code_details(tag, opt_of_borrowed(fname), code, details)
            }
            // (osCode, details) families and the default arm.
            _ => err_code_details(tag, code, details),
        }
    }
}

/// `lean_io_remove_file` (`io.cpp:1339-1350`, the non-Windows arm): the
/// pin calls `uv_fs_unlink`, which on POSIX is unlink(2) answering the
/// NEGATED errno; failure decodes through the uv decoder with the filename.
///
/// # Safety
/// `filename` is borrowed and live; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0362
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_remove_file(filename: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: live string per contract; fresh result objects.
    unsafe {
        let Some(bytes) = cstr_of(filename) else {
            return mk_embedded_nul_error(filename);
        };
        if unlink(bytes.as_ptr().cast::<c_char>()) == 0 {
            io_result_mk_ok(tagged::boxi(0))
        } else {
            io_result_mk_error(decode_uv_error(-errno(), filename))
        }
    }
}

/// `lean_io_hard_link` (`io.cpp:1229-1245`): the pin calls `uv_fs_link`
/// (link(2) on POSIX); failure decodes through the uv decoder with the
/// ORIG path, exactly the pin's argument choice.
///
/// # Safety
/// `orig` and `link_path` are borrowed and live; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0363
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_hard_link(
    orig: *mut LeanObject,
    link_path: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: live strings per contract; fresh result objects.
    unsafe {
        let Some(orig_bytes) = cstr_of(orig) else {
            return mk_embedded_nul_error(orig);
        };
        let Some(link_bytes) = cstr_of(link_path) else {
            return mk_embedded_nul_error(link_path);
        };
        if link(
            orig_bytes.as_ptr().cast::<c_char>(),
            link_bytes.as_ptr().cast::<c_char>(),
        ) == 0
        {
            io_result_mk_ok(tagged::boxi(0))
        } else {
            io_result_mk_error(decode_uv_error(-errno(), orig))
        }
    }
}

// ---------------------------------------------------- the temp family

/// The `uv_os_tmpdir` twin (libuv `unix/core.c`, reached from
/// `io.cpp:1252/1298`): TMPDIR, then TMP, TEMP, TEMPDIR, else `/tmp`,
/// with one trailing slash trimmed when the path is longer than root —
/// libuv's exact probe order and trim rule.
fn os_tmpdir() -> Vec<u8> {
    use std::os::unix::ffi::OsStrExt;
    let mut dir = ["TMPDIR", "TMP", "TEMP", "TEMPDIR"]
        .iter()
        .find_map(|v| std::env::var_os(v).filter(|s| !s.is_empty()))
        .map_or_else(|| b"/tmp".to_vec(), |s| s.as_bytes().to_vec());
    if dir.len() > 1 && dir.last() == Some(&b'/') {
        dir.pop();
    }
    dir
}

/// The shared template builder (`io.cpp:1258-1276`): base + `/` when the
/// base does not already end with one + the pin's `tmp.XXXXXXXX` pattern,
/// NUL-terminated for the C template calls.
fn temp_template() -> Vec<u8> {
    let mut path = os_tmpdir();
    if path.last() != Some(&b'/') {
        path.push(b'/');
    }
    path.extend_from_slice(b"tmp.XXXXXXXX");
    path.push(0);
    path
}

/// `lean_io_create_tempfile` (`io.cpp:1248-1291`): mkostemp with
/// O_CLOEXEC (libuv's own call under `uv_fs_mkstemp`), the fd fdopened
/// `r+`, answered as the pin's `(Handle x FilePath)` pair ctor; failure
/// decodes through the uv decoder with a NULL fname exactly as the pin's.
///
/// # Safety
/// Caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0367
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_create_tempfile() -> *mut LeanObject {
    // SAFETY: the template buffer is NUL-terminated and mutated in place by
    // mkostemp; the resulting fd is owned by the wrapped handle; fresh
    // objects settle before escape. The pin performs no fdopen null check
    // (io.cpp:1286) and this mirrors it.
    unsafe {
        let mut template = temp_template();
        let fd = mkostemp(
            template.as_mut_ptr().cast::<c_char>(),
            crate::stdio::O_CLOEXEC,
        );
        if fd < 0 {
            return io_result_mk_error(decode_uv_error(-errno(), core::ptr::null_mut()));
        }
        let handle = fdopen(fd, c"r+".as_ptr());
        let pair = object::alloc_ctor(0, 2, 0);
        object::ctor_set(pair, 0, crate::stdio::io_wrap_handle(handle));
        object::ctor_set(
            pair,
            1,
            crate::export::mk_string_from_bytes_impl(
                template.as_ptr().cast::<c_char>(),
                template.len() - 1,
            ),
        );
        io_result_mk_ok(pair)
    }
}

/// `lean_io_create_tempdir` (`io.cpp:1294-1337`): mkdtemp over the same
/// template, answering the created path; failure decodes through the uv
/// decoder with a NULL fname exactly as the pin's.
///
/// # Safety
/// Caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0368
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_create_tempdir() -> *mut LeanObject {
    // SAFETY: the template buffer is NUL-terminated and mutated in place by
    // mkdtemp; fresh objects settle before escape.
    unsafe {
        let mut template = temp_template();
        if mkdtemp(template.as_mut_ptr().cast::<c_char>()).is_null() {
            return io_result_mk_error(decode_uv_error(-errno(), core::ptr::null_mut()));
        }
        io_result_mk_ok(crate::export::mk_string_from_bytes_impl(
            template.as_ptr().cast::<c_char>(),
            template.len() - 1,
        ))
    }
}

// ------------------------------------------------- the metadata family

// Measured stat(2) layout facts (errno_extract.c; glibc x86-64).
const STAT_SIZE: usize = 144;
const STAT_ST_MODE_OFFSET: usize = 24;
const STAT_ST_NLINK_OFFSET: usize = 16;
const STAT_ST_SIZE_OFFSET: usize = 48;
const STAT_ST_ATIM_OFFSET: usize = 72;
const STAT_ST_MTIM_OFFSET: usize = 88;
const S_IFMT_MASK: u32 = 61440;
const S_IFDIR_BITS: u32 = 16384;
const S_IFREG_BITS: u32 = 32768;
const S_IFLNK_BITS: u32 = 40960;

/// `lean_int64_to_int`'s small arm (`lean.h:1618-1623`): a value inside
/// [INT_MIN, INT_MAX] boxes as `lean_box((unsigned)(int)n)`. The big arm is
/// `lean_big_int64_to_int`, which is the bignum shim's Unsupported census
/// row — unreachable for any real filesystem timestamp before the year
/// 2038 rolls st_atim past INT_MAX, and refused typed rather than
/// fabricated when it is.
fn int64_to_int(n: i64) -> *mut LeanObject {
    if (i64::from(i32::MIN)..=i64::from(i32::MAX)).contains(&n) {
        #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
        tagged::boxi((n as i32) as u32 as usize)
    } else {
        crate::export::internal_panic_impl(
            "metadata: timestamp outside the small-Int range needs the bignum shim \
             (lean_big_int64_to_int, Unsupported census row)",
        )
    }
}

/// `timespec_to_obj` (`io.cpp:1107-1112`): the `SystemTime` ctor — sec as
/// Int in field 0, nsec as the u32 scalar.
///
/// # Safety
/// Caller owns the result.
// UNSAFE-LEDGER: FLN-UL-0372
#[allow(unsafe_code)]
unsafe fn timespec_to_obj(sec: i64, nsec: u32) -> *mut LeanObject {
    // SAFETY: fresh ctor, every slot initialized before escape.
    unsafe {
        let o = object::alloc_ctor(0, 1, 4);
        object::ctor_set(o, 0, int64_to_int(sec));
        object::ctor_set_scalar::<u32>(o, size_of::<usize>(), nsec);
        o
    }
}

/// `metadata_core` (`io.cpp:1114-1129`): the `Metadata` ctor over the raw
/// stat buffer — accessed/modified SystemTimes, byteSize and nlink as u64
/// scalars, and the FileType byte (dir 0, file 1, symlink 2, other 3).
///
/// # Safety
/// `buf` holds a stat(2)-filled `struct stat`.
// UNSAFE-LEDGER: FLN-UL-0373
#[allow(unsafe_code)]
unsafe fn metadata_core(buf: &[u8; STAT_SIZE]) -> *mut LeanObject {
    // SAFETY: field reads at the measured offsets within the fixed-size
    // buffer; fresh ctor slots initialized before escape.
    unsafe {
        let read_u64 = |off: usize| u64::from_le_bytes(buf[off..off + 8].try_into().unwrap());
        let read_i64 = |off: usize| i64::from_le_bytes(buf[off..off + 8].try_into().unwrap());
        let mode = u32::from_le_bytes(
            buf[STAT_ST_MODE_OFFSET..STAT_ST_MODE_OFFSET + 4]
                .try_into()
                .unwrap(),
        );
        let mdata = object::alloc_ctor(0, 2, 2 * size_of::<u64>() + 1);
        object::ctor_set(
            mdata,
            0,
            timespec_to_obj(
                read_i64(STAT_ST_ATIM_OFFSET),
                #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
                {
                    read_i64(STAT_ST_ATIM_OFFSET + 8) as u32
                },
            ),
        );
        object::ctor_set(
            mdata,
            1,
            timespec_to_obj(
                read_i64(STAT_ST_MTIM_OFFSET),
                #[allow(clippy::cast_sign_loss, clippy::cast_possible_truncation)]
                {
                    read_i64(STAT_ST_MTIM_OFFSET + 8) as u32
                },
            ),
        );
        object::ctor_set_scalar::<u64>(
            mdata,
            2 * size_of::<usize>(),
            read_u64(STAT_ST_SIZE_OFFSET),
        );
        object::ctor_set_scalar::<u64>(
            mdata,
            2 * size_of::<usize>() + size_of::<u64>(),
            read_u64(STAT_ST_NLINK_OFFSET),
        );
        let ftype: u8 = match mode & S_IFMT_MASK {
            m if m == S_IFDIR_BITS => 0,
            m if m == S_IFREG_BITS => 1,
            m if m == S_IFLNK_BITS => 2,
            _ => 3,
        };
        object::ctor_set_scalar::<u8>(mdata, 2 * size_of::<usize>() + 2 * size_of::<u64>(), ftype);
        io_result_mk_ok(mdata)
    }
}

/// `lean_io_metadata` (`io.cpp:1131-1146`): stat through the uv decoder.
///
/// # Safety
/// `filename` is borrowed and live; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0374
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_metadata(filename: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: live string per contract; the stat buffer is stack-local.
    unsafe {
        let Some(bytes) = cstr_of(filename) else {
            return mk_embedded_nul_error(filename);
        };
        let mut buf = [0u8; STAT_SIZE];
        if stat(
            bytes.as_ptr().cast::<c_char>(),
            buf.as_mut_ptr().cast::<c_void>(),
        ) != 0
        {
            io_result_mk_error(decode_uv_error(-errno(), filename))
        } else {
            metadata_core(&buf)
        }
    }
}

/// `lean_io_symlink_metadata` (`io.cpp:1148-1165`, the non-Windows arm):
/// lstat through the uv decoder.
///
/// # Safety
/// `filename` is borrowed and live; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0375
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_symlink_metadata(filename: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: live string per contract; the stat buffer is stack-local.
    unsafe {
        let Some(bytes) = cstr_of(filename) else {
            return mk_embedded_nul_error(filename);
        };
        let mut buf = [0u8; STAT_SIZE];
        if lstat(
            bytes.as_ptr().cast::<c_char>(),
            buf.as_mut_ptr().cast::<c_void>(),
        ) != 0
        {
            io_result_mk_error(decode_uv_error(-errno(), filename))
        } else {
            metadata_core(&buf)
        }
    }
}

// ---------------------------------------------------- the env/misc family

// UNSAFE-LEDGER: FLN-UL-0379
#[allow(unsafe_code)]
unsafe extern "C" {
    fn getenv(name: *const c_char) -> *mut c_char;
    fn clock_gettime(clockid: c_int, tp: *mut i64) -> c_int;
    fn gettid() -> c_int;
    fn getpid() -> c_int;
    fn readlink(path: *const c_char, buf: *mut c_char, bufsiz: usize) -> isize;
    fn open(path: *const c_char, flags: c_int, mode: c_int) -> c_int;
    fn read(fd: c_int, buf: *mut c_void, count: usize) -> isize;
    fn close(fd: c_int) -> c_int;
}

const CLOCK_MONOTONIC: c_int = 1;
const O_RDONLY: c_int = 0;

/// `lean_uint64_to_nat`'s law (`lean.h:1640-1646`): box iff the value fits
/// the small Nat, else the big constructor Marrow already exports.
fn uint64_to_nat(n: u64) -> *mut LeanObject {
    #[allow(clippy::cast_possible_truncation)]
    if n as usize <= tagged::MAX_SMALL_NAT && u64::try_from(usize::MAX).is_ok_and(|m| n <= m) {
        tagged::boxi(n as usize)
    } else {
        crate::export::export_lean_big_uint64_to_nat(n)
    }
}

/// The pin's `userError` result (`io_result_mk_error(char const *)`,
/// object.h): the bare tag-18 string error the misc family uses.
///
/// # Safety
/// Caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0380
#[allow(unsafe_code)]
unsafe fn io_user_error(msg: &str) -> *mut LeanObject {
    // SAFETY: fresh ctor, slot initialized before escape.
    unsafe {
        let e = object::alloc_ctor(18, 1, 0);
        object::ctor_set(e, 0, mk_string(msg));
        io_result_mk_error(e)
    }
}

/// `lean_io_getenv` (`io.cpp:964-1000`, the POSIX arm): an embedded NUL
/// answers `none` (NOT an error — the pin's arm differs from the fs
/// family's here); a present variable answers `some` through the
/// validating string constructor.
///
/// # Safety
/// `env_var` is borrowed and live; caller owns the result.
// UNSAFE-LEDGER: FLN-UL-0381
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_getenv(env_var: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: live string per contract; the env value is copied before any
    // later libc call could invalidate it.
    unsafe {
        let Some(bytes) = cstr_of(env_var) else {
            return tagged::boxi(0);
        };
        let val = getenv(bytes.as_ptr().cast::<c_char>());
        if val.is_null() {
            tagged::boxi(0)
        } else {
            let mut len = 0usize;
            while *val.add(len) != 0 {
                len += 1;
            }
            let s = crate::export::mk_string_from_bytes_impl(val, len);
            let some = object::alloc_ctor(1, 1, 0);
            object::ctor_set(some, 0, s);
            some
        }
    }
}

/// The steady-clock read both mono prims share (`io.cpp:843-857`:
/// std::chrono::steady_clock, which is CLOCK_MONOTONIC on this platform).
///
/// # Safety
/// Infallible on a valid clock id per POSIX; a failure is an invariant
/// fault.
// UNSAFE-LEDGER: FLN-UL-0382
#[allow(unsafe_code)]
unsafe fn mono_now_ns() -> u64 {
    // SAFETY: the two-slot timespec is stack-local; CLOCK_MONOTONIC is
    // valid on every supported kernel.
    unsafe {
        let mut ts = [0i64; 2];
        if clock_gettime(CLOCK_MONOTONIC, ts.as_mut_ptr()) != 0 {
            crate::export::internal_panic_impl("clock_gettime(CLOCK_MONOTONIC) failed");
        }
        #[allow(clippy::cast_sign_loss)]
        {
            (ts[0] as u64) * 1_000_000_000 + (ts[1] as u64)
        }
    }
}

/// `lean_io_mono_ms_now` (`io.cpp:843-849`).
///
/// # Safety
/// Caller owns the result.
// UNSAFE-LEDGER: FLN-UL-0383
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_mono_ms_now() -> *mut LeanObject {
    // SAFETY: pure construction over the clock read.
    unsafe { uint64_to_nat(mono_now_ns() / 1_000_000) }
}

/// `lean_io_mono_nanos_now` (`io.cpp:851-857`).
///
/// # Safety
/// Caller owns the result.
// UNSAFE-LEDGER: FLN-UL-0384
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_mono_nanos_now() -> *mut LeanObject {
    // SAFETY: pure construction over the clock read.
    unsafe { uint64_to_nat(mono_now_ns()) }
}

/// `lean_io_get_tid` (`process.cpp:340-352`, the Linux arm: gettid).
///
/// # Safety
/// Trivially safe syscall wrapper.
// UNSAFE-LEDGER: FLN-UL-0385
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_get_tid() -> u64 {
    // SAFETY: gettid cannot fail.
    #[allow(clippy::cast_sign_loss)]
    unsafe {
        gettid() as u64
    }
}

/// `lean_io_process_get_pid` (`process.cpp:330-333`).
///
/// # Safety
/// Trivially safe syscall wrapper.
// UNSAFE-LEDGER: FLN-UL-0386
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_get_pid() -> u32 {
    // SAFETY: getpid cannot fail.
    #[allow(clippy::cast_sign_loss)]
    unsafe {
        getpid() as u32
    }
}

/// `lean_io_app_path` (`io.cpp:1354-1407`, the Linux arm): readlink of
/// `/proc/<pid>/exe`; failure is the pin's bare userError.
///
/// # Safety
/// Caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0387
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_app_path() -> *mut LeanObject {
    // SAFETY: both buffers are stack-local and NUL-clean per the memset
    // the pin performs; readlink writes at most PATH_MAX - 1 bytes.
    unsafe {
        let path = format!("/proc/{}/exe\0", prim_get_pid());
        let mut dest = [0u8; PATH_MAX];
        let n = readlink(
            path.as_ptr().cast::<c_char>(),
            dest.as_mut_ptr().cast::<c_char>(),
            PATH_MAX - 1,
        );
        if n == -1 {
            io_user_error("failed to locate application")
        } else {
            #[allow(clippy::cast_sign_loss)]
            io_result_mk_ok(crate::export::mk_string_from_bytes_impl(
                dest.as_ptr().cast::<c_char>(),
                n as usize,
            ))
        }
    }
}

/// The pin's initialization flag pair (`io.cpp:76-83`): a process-global
/// bool generated main flips after the module initializers run.
static INITIALIZING: core::sync::atomic::AtomicBool = core::sync::atomic::AtomicBool::new(true);

pub(crate) fn mark_end_initialization() {
    INITIALIZING.store(false, core::sync::atomic::Ordering::Relaxed);
}

#[cfg(test)]
pub(crate) fn reset_initializing_for_tests() {
    INITIALIZING.store(true, core::sync::atomic::Ordering::Relaxed);
}

pub(crate) fn initializing() -> u8 {
    u8::from(INITIALIZING.load(core::sync::atomic::Ordering::Relaxed))
}

/// `lean_io_get_random_bytes` (`io.cpp:865-925`, the POSIX arm):
/// `/dev/urandom` with O_CLOEXEC, the zero-byte fast path, the overflow
/// refusal as ENOMEM, and the EINTR-retrying read loop; the open failure
/// decodes errno WITH the device path, a read failure without.
///
/// # Safety
/// Caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0388
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_get_random_bytes(nbytes: usize) -> *mut LeanObject {
    // SAFETY: the sarray is freshly allocated with capacity nbytes and its
    // size set only after every byte is written; the fd closes on every
    // arm.
    unsafe {
        if nbytes == 0 {
            return io_result_mk_ok(object::alloc_sarray(1, 0, 0));
        }
        let fd = open(
            c"/dev/urandom".as_ptr(),
            O_RDONLY | crate::stdio::O_CLOEXEC,
            0,
        );
        if fd < 0 {
            let dev = mk_string("/dev/urandom");
            let err = io_result_mk_error(decode_io_error(errno(), dev));
            rc::dec_ref(dev);
            return err;
        }
        if nbytes
            .checked_add(size_of::<crate::layout::LeanSarrayObject>())
            .is_none()
        {
            close(fd);
            return io_result_mk_error(decode_io_error(
                crate::stdio::ENOMEM,
                core::ptr::null_mut(),
            ));
        }
        let res = object::alloc_sarray(1, 0, nbytes);
        let (_, _, _, data) = object::sarray_fields(res);
        let mut remain = nbytes;
        let mut dst = data;
        while remain > 0 {
            let nread = read(fd, dst.cast::<c_void>(), remain);
            if nread < 0 {
                if errno() != crate::stdio::EINTR {
                    close(fd);
                    rc::dec_ref(res);
                    return io_result_mk_error(decode_io_error(errno(), core::ptr::null_mut()));
                }
            } else {
                #[allow(clippy::cast_sign_loss)]
                {
                    remain -= nread as usize;
                    dst = dst.add(nread as usize);
                }
            }
        }
        close(fd);
        (&raw mut (*res.cast::<crate::layout::LeanSarrayObject>()).m_size).write(nbytes);
        io_result_mk_ok(res)
    }
}
