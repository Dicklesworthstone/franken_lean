//! The filesystem plane: the errno-decoded fs prim family — bead `fln-3gv`
//! slice 6a, porting `io.cpp:372-382` (`lean_chmod`), `io.cpp:1169-1183`
//! (`create_dir`), `io.cpp:1185-1195` (`remove_dir`), `io.cpp:1197-1227`
//! non-Windows arm (`rename`), `io.cpp:1064-1086` (`read_dir`),
//! `io.cpp:1002-1055` non-Windows arm (`realpath`), and `io.cpp:1409-1417`
//! (`current_dir`) at the pin.
//!
//! Deliberately NOT here, named rather than implied: the uv-decoded members
//! — `remove_file`, `hard_link`, `metadata`/`symlink_metadata`,
//! `create_tempfile`/`create_tempdir` — whose observable error shape is
//! libuv's (negative codes, `uv_strerror` details), a different decoder a
//! later slice ports; and `app_path`/`getenv`, the env/misc family.
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
    ERR_NO_FILE_OR_DIRECTORY, decode_io_error, errno, io_result_mk_error, io_result_mk_ok,
    mk_embedded_nul_error, mk_string,
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
