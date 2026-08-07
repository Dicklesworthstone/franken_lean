//! The stdio plane: `IO.FS.Handle`, the native `FS.Stream` constructor, and
//! the thread-current standard-stream trio — bead `fln-3gv` slice 5a (design
//! comment 1856), porting `io.cpp:95-160` (handle class, stream globals,
//! get/get_set), `io.cpp:385-418` (`handle_mk`), `io.cpp:516-531` (`is_tty`),
//! `io.cpp:550-556` (`flush`), `io.cpp:661-670` (`put_str`), and
//! `io.cpp:163-260` (the errno decoder) at the pin.
//!
//! Disclosed mechanism deviations, all observable-preserving and each held by
//! the extern rows + the gauntlet's corpus facts:
//!
//! - **The stream constructor is native.** The pin's `lean_stream_of_handle`
//!   is `@[export]`ed LEAN code (`Init/System/IO.lean`, `Stream.ofHandle`)
//!   that `initialize_io` calls into; Marrow's staticlib carries no compiled
//!   Lean, so the six-field `FS.Stream` ctor is built here over native
//!   closures driving the same prims — the Native-Mirror arm (B2) at spike
//!   depth. Compiled code consumes the structure shape, which is identical.
//! - **The process-initial trio seeds lazily.** The pin builds the three
//!   streams eagerly in `initialize_io`; ours materialize on first use,
//!   before any conforming code can observe a stream, so no compiled-code
//!   observable distinguishes the two. SIGPIPE is ignored at that seed —
//!   the pin's disposition (`io.cpp:1654-1656`), installed before any stdio
//!   write our streams can produce.
//! - **Every stream field is live.** `read` and `write` went live in slice
//!   5b over their ported prims; `getLine` in slice 5c over
//!   `prim_handle_get_line` (`io.cpp:635-659`), retiring the last typed
//!   stream-field refusal.
//! - **Thread-current semantics are the pin's exactly**: each thread's
//!   current streams seed from the PROCESS-initial trio, never from the
//!   spawning thread's current set (`MK_THREAD_LOCAL_GET`, io.cpp:115-117),
//!   so a `get_set` on one thread is invisible to every other.
//!
//! Platform posture: Linux/glibc only, exactly like the loader door
//! (`door.rs`) and the layout mirrors' target gate in `lib.rs`. Every
//! platform constant below is MEASURED from this platform's own headers by
//! `tribunal/fixtures/c4/errno_extract.c` rather than transcribed — rerun it
//! to re-derive the table.

use core::ffi::{c_char, c_int, c_void};
use std::sync::OnceLock;

use crate::layout::{LeanExternalClass, LeanObject};
use crate::{object, rc, tagged};

// ---------------------------------------------------------------- platform

// UNSAFE-LEDGER: FLN-UL-0267
#[allow(unsafe_code)]
unsafe extern "C" {
    /// glibc's `FILE *stdin/stdout/stderr` data symbols.
    static stdin: *mut c_void;
    static stdout: *mut c_void;
    static stderr: *mut c_void;
    fn open(path: *const c_char, flags: c_int, mode: c_int) -> c_int;
    fn fdopen(fd: c_int, mode: *const c_char) -> *mut c_void;
    fn fwrite(ptr: *const c_void, size: usize, n: usize, f: *mut c_void) -> usize;
    fn fread(ptr: *mut c_void, size: usize, n: usize, f: *mut c_void) -> usize;
    fn feof(f: *mut c_void) -> c_int;
    fn ferror(f: *mut c_void) -> c_int;
    fn clearerr(f: *mut c_void);
    fn flockfile(f: *mut c_void);
    fn funlockfile(f: *mut c_void);
    fn getc_unlocked(f: *mut c_void) -> c_int;
    fn fflush(f: *mut c_void) -> c_int;
    fn fclose(f: *mut c_void) -> c_int;
    fn fileno(f: *mut c_void) -> c_int;
    fn isatty(fd: c_int) -> c_int;
    fn fseek(f: *mut c_void, offset: i64, whence: c_int) -> c_int;
    fn ftello(f: *mut c_void) -> i64;
    fn ftruncate(fd: c_int, length: i64) -> c_int;
    fn flock(fd: c_int, operation: c_int) -> c_int;
    fn strerror(errnum: c_int) -> *const c_char;
    fn signal(signum: c_int, handler: usize) -> usize;
    /// glibc's thread-local `errno` accessor (what the `errno` macro reads).
    fn __errno_location() -> *mut c_int;
}

// Measured constants (errno_extract.c on this platform's headers; Linux
// asm-generic values, arch-uniform for x86-64/aarch64).
pub(crate) const EINTR: c_int = 4;
pub(crate) const ELOOP: c_int = 40;
pub(crate) const ENAMETOOLONG: c_int = 36;
pub(crate) const EDESTADDRREQ: c_int = 89;
pub(crate) const EBADF: c_int = 9;
pub(crate) const EDOM: c_int = 33;
pub(crate) const EINVAL: c_int = 22;
pub(crate) const EILSEQ: c_int = 84;
pub(crate) const ENOEXEC: c_int = 8;
pub(crate) const ENOSTR: c_int = 60;
pub(crate) const ENOTCONN: c_int = 107;
pub(crate) const ENOTSOCK: c_int = 88;
pub(crate) const ENOENT: c_int = 2;
pub(crate) const EACCES: c_int = 13;
pub(crate) const EROFS: c_int = 30;
pub(crate) const ECONNABORTED: c_int = 103;
pub(crate) const EFBIG: c_int = 27;
pub(crate) const EPERM: c_int = 1;
pub(crate) const EMFILE: c_int = 24;
pub(crate) const ENFILE: c_int = 23;
pub(crate) const ENOSPC: c_int = 28;
pub(crate) const E2BIG: c_int = 7;
pub(crate) const EAGAIN: c_int = 11;
pub(crate) const EMLINK: c_int = 31;
pub(crate) const EMSGSIZE: c_int = 90;
pub(crate) const ENOBUFS: c_int = 105;
pub(crate) const ENOLCK: c_int = 37;
pub(crate) const ENOMEM: c_int = 12;
pub(crate) const ENOSR: c_int = 63;
pub(crate) const EISDIR: c_int = 21;
pub(crate) const EBADMSG: c_int = 74;
pub(crate) const ENOTDIR: c_int = 20;
pub(crate) const ENXIO: c_int = 6;
pub(crate) const EHOSTUNREACH: c_int = 113;
pub(crate) const ENETUNREACH: c_int = 101;
pub(crate) const ECHILD: c_int = 10;
pub(crate) const ECONNREFUSED: c_int = 111;
pub(crate) const ENODATA: c_int = 61;
pub(crate) const ENOMSG: c_int = 42;
pub(crate) const ESRCH: c_int = 3;
pub(crate) const EEXIST: c_int = 17;
pub(crate) const EINPROGRESS: c_int = 115;
pub(crate) const EISCONN: c_int = 106;
pub(crate) const EIO: c_int = 5;
pub(crate) const ENOTEMPTY: c_int = 39;
pub(crate) const ENOTTY: c_int = 25;
pub(crate) const ECONNRESET: c_int = 104;
pub(crate) const EIDRM: c_int = 43;
pub(crate) const ENETDOWN: c_int = 100;
pub(crate) const ENETRESET: c_int = 102;
pub(crate) const ENOLINK: c_int = 67;
pub(crate) const EPIPE: c_int = 32;
pub(crate) const EPROTO: c_int = 71;
pub(crate) const EPROTONOSUPPORT: c_int = 93;
pub(crate) const EPROTOTYPE: c_int = 91;
pub(crate) const ETIME: c_int = 62;
pub(crate) const ETIMEDOUT: c_int = 110;
pub(crate) const EADDRINUSE: c_int = 98;
pub(crate) const EBUSY: c_int = 16;
pub(crate) const EDEADLK: c_int = 35;
pub(crate) const ETXTBSY: c_int = 26;
pub(crate) const EADDRNOTAVAIL: c_int = 99;
pub(crate) const EAFNOSUPPORT: c_int = 97;
pub(crate) const ENODEV: c_int = 19;
pub(crate) const ENOPROTOOPT: c_int = 92;
pub(crate) const ENOSYS: c_int = 38;
pub(crate) const EOPNOTSUPP: c_int = 95;
pub(crate) const ERANGE: c_int = 34;
pub(crate) const ESPIPE: c_int = 29;
pub(crate) const EXDEV: c_int = 18;
pub(crate) const EFAULT: c_int = 14;
const O_RDONLY: c_int = 0;
const O_WRONLY: c_int = 1;
const O_RDWR: c_int = 2;
const O_CREAT: c_int = 64;
const O_TRUNC: c_int = 512;
const O_EXCL: c_int = 128;
const O_APPEND: c_int = 1024;
const O_CLOEXEC: c_int = 524288;
const SIGPIPE: c_int = 13;
const SIG_IGN: usize = 1;
const SEEK_SET: c_int = 0;
const LOCK_SH: c_int = 1;
const LOCK_EX: c_int = 2;
const LOCK_NB: c_int = 4;
const LOCK_UN: c_int = 8;
// EWOULDBLOCK == EAGAIN on Linux (asm-generic); the try_lock arm keys on it.
const EWOULDBLOCK: c_int = EAGAIN;

pub(crate) fn errno() -> c_int {
    // SAFETY: glibc guarantees a valid thread-local location.
    // UNSAFE-LEDGER: FLN-UL-0268
    #[allow(unsafe_code)]
    unsafe {
        *__errno_location()
    }
}

// ---------------------------------------------------------------- handle

/// `io_handle_finalizer` (`io.cpp:93-100`): fclose with errors deliberately
/// swallowed — finalizing a handle in an invalid state (broken pipe) must
/// work and not terminate the process; the pin cites Rust's own `File` for
/// the same decision.
// UNSAFE-LEDGER: FLN-UL-0269
#[allow(unsafe_code)]
unsafe extern "C" fn handle_finalize(h: *mut c_void) {
    // SAFETY: `h` is the FILE* this external object owns, closed exactly
    // once here because the object dies exactly once.
    unsafe {
        fclose(h);
    }
}

/// `io_handle_foreach` (`io.cpp:102-103`): no boxed children.
// UNSAFE-LEDGER: FLN-UL-0270
#[allow(unsafe_code)]
unsafe extern "C" fn handle_foreach(_h: *mut c_void, _fn: *mut LeanObject) {}

/// `g_io_handle_external_class` (`io.cpp:1641`), registered once per
/// process, immortal exactly as the pin's.
fn handle_class() -> *mut LeanExternalClass {
    static CLASS: OnceLock<usize> = OnceLock::new();
    *CLASS.get_or_init(|| object::register_external_class(handle_finalize, handle_foreach) as usize)
        as *mut LeanExternalClass
}

/// `io_wrap_handle` (`io.cpp:105-107`): a Handle external object owning the
/// FILE*.
///
/// # Safety
/// `fp` is a live FILE* whose ownership transfers to the object.
// UNSAFE-LEDGER: FLN-UL-0271
#[allow(unsafe_code)]
pub(crate) unsafe fn io_wrap_handle(fp: *mut c_void) -> *mut LeanObject {
    // SAFETY: the registered class outlives every object; fp per contract.
    unsafe { object::alloc_external(handle_class(), fp) }
}

/// `io_get_handle` (`io.cpp:159-161`): the FILE* out of a live Handle.
///
/// # Safety
/// `h` is a live external Handle object.
// UNSAFE-LEDGER: FLN-UL-0272
#[allow(unsafe_code)]
unsafe fn io_get_handle(h: *mut LeanObject) -> *mut c_void {
    // SAFETY: live external per contract.
    unsafe { object::external_fields(h).1 }
}

// ---------------------------------------------------------------- builders

/// An owned Lean string from a Rust str (the pin's `mk_string`).
///
/// # Safety
/// Caller owns the result.
// UNSAFE-LEDGER: FLN-UL-0273
#[allow(unsafe_code)]
pub(crate) unsafe fn mk_string(s: &str) -> *mut LeanObject {
    // SAFETY: byte/char counts are computed from the same str.
    unsafe { object::mk_string_unchecked(s.as_bytes(), s.chars().count()) }
}

/// `lean_io_result_mk_ok` / `_mk_error` (`lean.h:2952-2961`): the EIO
/// result ctors.
///
/// # Safety
/// `a` is consumed; caller owns the result.
// UNSAFE-LEDGER: FLN-UL-0274
#[allow(unsafe_code)]
pub(crate) unsafe fn io_result_mk_ok(a: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: fresh 1-field ctor, slot initialized before escape.
    unsafe {
        let r = object::alloc_ctor(0, 1, 0);
        object::ctor_set(r, 0, a);
        r
    }
}

/// See [`io_result_mk_ok`].
// UNSAFE-LEDGER: FLN-UL-0275
#[allow(unsafe_code)]
pub(crate) unsafe fn io_result_mk_error(e: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: fresh 1-field ctor, slot initialized before escape.
    unsafe {
        let r = object::alloc_ctor(1, 1, 0);
        object::ctor_set(r, 0, e);
        r
    }
}

/// An `IO.Error` ctor of the `(osCode : UInt32) (details : String)` family
/// (generated layout: `lean_alloc_ctor(tag, 1, 4)`, u32 at
/// `sizeof(void*)*1` — IOError.c:998-1009's shape minus the Option slot).
///
/// # Safety
/// `details` is consumed; caller owns the result.
// UNSAFE-LEDGER: FLN-UL-0276
#[allow(unsafe_code)]
unsafe fn err_code_details(tag: u8, code: u32, details: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: fresh ctor, every slot initialized before escape.
    unsafe {
        let r = object::alloc_ctor(tag, 1, 4);
        object::ctor_set(r, 0, details);
        object::ctor_set_scalar::<u32>(r, size_of::<usize>(), code);
        r
    }
}

/// The `(filename : Option String) (osCode) (details)` family
/// (IOError.c:768-780 / 998-1009: `lean_alloc_ctor(tag, 2, 4)`, field 0 the
/// Option — `box(0)` none, `ctor(1,1,0)` some — u32 at `sizeof(void*)*2`).
///
/// # Safety
/// `fname_opt` and `details` are consumed; caller owns the result.
// UNSAFE-LEDGER: FLN-UL-0277
#[allow(unsafe_code)]
unsafe fn err_optfile_code_details(
    tag: u8,
    fname_opt: *mut LeanObject,
    code: u32,
    details: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: fresh ctor, every slot initialized before escape.
    unsafe {
        let r = object::alloc_ctor(tag, 2, 4);
        object::ctor_set(r, 0, fname_opt);
        object::ctor_set(r, 1, details);
        object::ctor_set_scalar::<u32>(r, 2 * size_of::<usize>(), code);
        r
    }
}

/// The `(filename : String) (osCode) (details)` family (IOError.c:822-833:
/// `lean_alloc_ctor(tag, 2, 4)` with a bare String in field 0).
///
/// # Safety
/// `fname` and `details` are consumed; caller owns the result.
// UNSAFE-LEDGER: FLN-UL-0278
#[allow(unsafe_code)]
pub(crate) unsafe fn err_file_code_details(
    tag: u8,
    fname: *mut LeanObject,
    code: u32,
    details: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: fresh ctor, every slot initialized before escape.
    unsafe {
        let r = object::alloc_ctor(tag, 2, 4);
        object::ctor_set(r, 0, fname);
        object::ctor_set(r, 1, details);
        object::ctor_set_scalar::<u32>(r, 2 * size_of::<usize>(), code);
        r
    }
}

/// `Option.some fname` with `fname` duplicated in (the decoder's
/// `inc_ref(fname)` arms), or `Option.none` for a null fname.
///
/// # Safety
/// `fname` is borrowed (may be null); caller owns the result.
// UNSAFE-LEDGER: FLN-UL-0279
#[allow(unsafe_code)]
unsafe fn opt_of_borrowed(fname: *mut LeanObject) -> *mut LeanObject {
    if fname.is_null() {
        return tagged::boxi(0);
    }
    // SAFETY: fname live per contract; the some-cell owns the new token.
    unsafe {
        rc::inc_ref_n(fname, 1);
        let some = object::alloc_ctor(1, 1, 0);
        object::ctor_set(some, 0, fname);
        some
    }
}

// IO.Error ctor tags, in the inductive's declaration order
// (Init/System/IOError.lean:30-140; `interrupted`'s generated tag 10 and
// `eof`'s `box(17)` at IOError.c:822/791 anchor the numbering).
const ERR_ALREADY_EXISTS: u8 = 0;
const ERR_OTHER: u8 = 1;
const ERR_RESOURCE_BUSY: u8 = 2;
const ERR_RESOURCE_VANISHED: u8 = 3;
const ERR_UNSUPPORTED_OPERATION: u8 = 4;
const ERR_HARDWARE_FAULT: u8 = 5;
const ERR_UNSATISFIED_CONSTRAINTS: u8 = 6;
const ERR_ILLEGAL_OPERATION: u8 = 7;
const ERR_PROTOCOL: u8 = 8;
const ERR_TIME_EXPIRED: u8 = 9;
const ERR_INTERRUPTED: u8 = 10;
pub(crate) const ERR_NO_FILE_OR_DIRECTORY: u8 = 11;
const ERR_INVALID_ARGUMENT: u8 = 12;
const ERR_PERMISSION_DENIED: u8 = 13;
const ERR_RESOURCE_EXHAUSTED: u8 = 14;
const ERR_INAPPROPRIATE_TYPE: u8 = 15;
const ERR_NO_SUCH_THING: u8 = 16;
// (unexpectedEof is box(17) and userError tag 18; neither is built here —
// eof belongs to the read prims and userError to mk_io_user_error's slice.)

/// `lean_decode_io_error` (`io.cpp:161-260`), arm-for-arm: errno plus an
/// optional filename to the pin's exact `IO.Error` variant, with the ctors
/// built natively (the pin's `lean_mk_io_error_*` helpers are Lean-compiled
/// and absent from a staticlib link; their generated bodies are the layout
/// authority cited on each builder above).
///
/// # Safety
/// `fname` is borrowed and may be null exactly where the pin's
/// `lean_assert`s permit; caller owns the result.
// UNSAFE-LEDGER: FLN-UL-0280
#[allow(unsafe_code)]
pub(crate) unsafe fn decode_io_error(errnum: c_int, fname: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: strerror returns a static/thread buffer; read before any
    // other libc call on this thread can clobber it.
    let details = unsafe {
        let p = strerror(errnum);
        let mut n = 0usize;
        while *p.add(n) != 0 {
            n += 1;
        }
        let bytes = core::slice::from_raw_parts(p.cast::<u8>(), n);
        mk_string(&String::from_utf8_lossy(bytes))
    };
    let code = errnum as u32;
    // SAFETY: every builder consumes its freshly built arguments.
    unsafe {
        match errnum {
            EINTR => {
                debug_assert!(!fname.is_null());
                rc::inc_ref_n(fname, 1);
                err_file_code_details(ERR_INTERRUPTED, fname, code, details)
            }
            ELOOP | ENAMETOOLONG | EDESTADDRREQ | EBADF | EDOM | EINVAL | EILSEQ | ENOEXEC
            | ENOSTR | ENOTCONN | ENOTSOCK => err_optfile_code_details(
                ERR_INVALID_ARGUMENT,
                opt_of_borrowed(fname),
                code,
                details,
            ),
            ENOENT => {
                debug_assert!(!fname.is_null());
                rc::inc_ref_n(fname, 1);
                err_file_code_details(ERR_NO_FILE_OR_DIRECTORY, fname, code, details)
            }
            EACCES | EROFS | ECONNABORTED | EFBIG | EPERM => err_optfile_code_details(
                ERR_PERMISSION_DENIED,
                opt_of_borrowed(fname),
                code,
                details,
            ),
            EMFILE | ENFILE | ENOSPC | E2BIG | EAGAIN | EMLINK | EMSGSIZE | ENOBUFS | ENOLCK
            | ENOMEM | ENOSR => err_optfile_code_details(
                ERR_RESOURCE_EXHAUSTED,
                opt_of_borrowed(fname),
                code,
                details,
            ),
            EISDIR | EBADMSG | ENOTDIR => err_optfile_code_details(
                ERR_INAPPROPRIATE_TYPE,
                opt_of_borrowed(fname),
                code,
                details,
            ),
            ENXIO | EHOSTUNREACH | ENETUNREACH | ECHILD | ECONNREFUSED | ENODATA | ENOMSG
            | ESRCH => {
                err_optfile_code_details(ERR_NO_SUCH_THING, opt_of_borrowed(fname), code, details)
            }
            EEXIST | EINPROGRESS | EISCONN => {
                err_optfile_code_details(ERR_ALREADY_EXISTS, opt_of_borrowed(fname), code, details)
            }
            EIO => err_code_details(ERR_HARDWARE_FAULT, code, details),
            ENOTEMPTY => err_code_details(ERR_UNSATISFIED_CONSTRAINTS, code, details),
            ENOTTY => err_code_details(ERR_ILLEGAL_OPERATION, code, details),
            ECONNRESET | EIDRM | ENETDOWN | ENETRESET | ENOLINK | EPIPE => {
                err_code_details(ERR_RESOURCE_VANISHED, code, details)
            }
            EPROTO | EPROTONOSUPPORT | EPROTOTYPE => err_code_details(ERR_PROTOCOL, code, details),
            ETIME | ETIMEDOUT => err_code_details(ERR_TIME_EXPIRED, code, details),
            EADDRINUSE | EBUSY | EDEADLK | ETXTBSY => {
                err_code_details(ERR_RESOURCE_BUSY, code, details)
            }
            EADDRNOTAVAIL | EAFNOSUPPORT | ENODEV | ENOPROTOOPT | ENOSYS | EOPNOTSUPP | ERANGE
            | ESPIPE | EXDEV => err_code_details(ERR_UNSUPPORTED_OPERATION, code, details),
            // The pin writes `case EFAULT: default:` — one arm, named then
            // open (io.cpp:258-260).
            EFAULT => err_code_details(ERR_OTHER, code, details),
            _ => err_code_details(ERR_OTHER, code, details),
        }
    }
}

/// `mk_embedded_nul_error` (`io.cpp:366-369`, the global helper `handle_mk`
/// and the fs family share): a string whose byte size disagrees with its
/// C-string length carries an embedded NUL; the pin refuses it as
/// `invalidArgument` before touching the filesystem. Slice 6a corrected the
/// details text to the pin's exact "string contains NUL bytes" (the first
/// version paraphrased it, a divergence in the observable details string).
///
/// # Safety
/// `fname` is borrowed and live; caller owns the result.
// UNSAFE-LEDGER: FLN-UL-0281
#[allow(unsafe_code)]
pub(crate) unsafe fn mk_embedded_nul_error(fname: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: fresh objects; the option cell duplicates fname.
    unsafe {
        let details = mk_string("string contains NUL bytes");
        io_result_mk_error(err_optfile_code_details(
            ERR_INVALID_ARGUMENT,
            opt_of_borrowed(fname),
            EINVAL as u32,
            details,
        ))
    }
}

// ---------------------------------------------------------------- prims

/// `lean_io_prim_handle_mk` (`io.cpp:385-418`), arm-for-arm: mode 0-4 to
/// open(2) flags with `O_CLOEXEC`, the embedded-NUL refusal, `open` then
/// `fdopen` under the matching stdio mode string.
///
/// # Safety
/// `filename` is a borrowed live string; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0282
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_handle_mk(filename: *mut LeanObject, mode: u8) -> *mut LeanObject {
    let flags = O_CLOEXEC
        | match mode {
            0 => O_RDONLY,
            1 => O_WRONLY | O_CREAT | O_TRUNC,
            2 => O_WRONLY | O_CREAT | O_TRUNC | O_EXCL,
            3 => O_RDWR,
            _ => O_WRONLY | O_CREAT | O_APPEND,
        };
    // SAFETY: string fields read within the live object; the copied bytes
    // are NUL-terminated by the string law.
    unsafe {
        let (m_size, _, _, bytes) = object::string_fields(filename);
        let nul_at = bytes.iter().position(|&b| b == 0).unwrap_or(m_size);
        if nul_at != m_size - 1 {
            return mk_embedded_nul_error(filename);
        }
        let fd = open(bytes.as_ptr().cast::<c_char>(), flags, 0o666);
        if fd == -1 {
            return io_result_mk_error(decode_io_error(errno(), filename));
        }
        let fp_mode: &[u8] = match mode {
            0 => b"r\0",
            1 | 2 => b"w\0",
            3 => b"r+\0",
            _ => b"a\0",
        };
        let fp = fdopen(fd, fp_mode.as_ptr().cast::<c_char>());
        if fp.is_null() {
            return io_result_mk_error(decode_io_error(errno(), filename));
        }
        io_result_mk_ok(io_wrap_handle(fp))
    }
}

/// `lean_io_prim_handle_put_str` (`io.cpp:661-670`): fwrite of the string's
/// bytes sans NUL; a short write decodes errno.
///
/// # Safety
/// `h` and `s` are borrowed and live; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0283
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_handle_put_str(
    h: *mut LeanObject,
    s: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: live objects per contract; fwrite reads exactly n bytes of
    // the copied data.
    unsafe {
        let fp = io_get_handle(h);
        let (m_size, _, _, bytes) = object::string_fields(s);
        let n = m_size - 1;
        let m = fwrite(bytes.as_ptr().cast::<c_void>(), 1, n, fp);
        if m == n {
            io_result_mk_ok(tagged::boxi(0))
        } else {
            io_result_mk_error(decode_io_error(errno(), core::ptr::null_mut()))
        }
    }
}

/// `lean_io_prim_handle_read` (`io.cpp:584-607`), arm-for-arm: the
/// overflow pre-check decodes ENOMEM; a zero-byte read answers ok before
/// touching fread (the pin cites lean4#12138); a short read with EOF set
/// clears the flag and answers the partial buffer; anything else decodes
/// errno after releasing the buffer.
///
/// # Safety
/// `h` is borrowed and live; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0314
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_handle_read(h: *mut LeanObject, nbytes: usize) -> *mut LeanObject {
    if nbytes
        .checked_add(size_of::<crate::layout::LeanSarrayObject>())
        .is_none()
    {
        // SAFETY: fresh error objects only.
        unsafe {
            return io_result_mk_error(decode_io_error(ENOMEM, core::ptr::null_mut()));
        }
    }
    // SAFETY: the sarray is freshly allocated with capacity nbytes; fread
    // writes at most that many bytes into its data base; m_size is set to
    // exactly the bytes written before the object escapes.
    unsafe {
        let fp = io_get_handle(h);
        let res = object::alloc_sarray(1, 0, nbytes);
        if nbytes == 0 {
            return io_result_mk_ok(res);
        }
        let (_, _, _, data) = object::sarray_fields(res);
        let n = fread(data.cast::<c_void>(), 1, nbytes, fp);
        if n > 0 {
            (&raw mut (*res.cast::<crate::layout::LeanSarrayObject>()).m_size).write(n);
            io_result_mk_ok(res)
        } else if feof(fp) != 0 {
            clearerr(fp);
            io_result_mk_ok(res)
        } else {
            rc::dec_ref(res);
            io_result_mk_error(decode_io_error(errno(), core::ptr::null_mut()))
        }
    }
}

/// `lean_io_prim_handle_write` (`io.cpp:609-618`): fwrite of the byte
/// array's salient bytes; a short write decodes errno.
///
/// # Safety
/// `h` and `buf` are borrowed and live; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0315
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_handle_write(
    h: *mut LeanObject,
    buf: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: live objects per contract; fwrite reads exactly n salient
    // bytes from the live array's data base.
    unsafe {
        let fp = io_get_handle(h);
        let (_, n, _, data) = object::sarray_fields(buf);
        let m = fwrite(data.cast::<c_void>(), 1, n, fp);
        if m == n {
            io_result_mk_ok(tagged::boxi(0))
        } else {
            io_result_mk_error(decode_io_error(errno(), core::ptr::null_mut()))
        }
    }
}

/// `lean_io_prim_handle_get_line` (`io.cpp:635-659`), arm-for-arm: bytes
/// accumulated under the file lock via `getc_unlocked` until EOF or a
/// retained `'\n'`; ferror decodes errno (the buffer simply drops); EOF
/// clears the flag and answers the partial line ok; otherwise ok — both ok
/// arms through the pin's own `mk_string(std::string)`, which is
/// `lean_mk_string_from_bytes` (`object.cpp:2049-2051`): UTF-8 validated,
/// invalid bytes recovered lossily as U+FFFD.
///
/// # Safety
/// `h` is borrowed and live; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0329
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_handle_get_line(h: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: live handle per contract; the byte loop holds the FILE lock
    // exactly across the reads as the pin's flockfile pair does, and the
    // string constructor copies out of the local buffer before it drops.
    unsafe {
        let fp = io_get_handle(h);
        let mut result: Vec<u8> = Vec::new();
        flockfile(fp);
        loop {
            let c = getc_unlocked(fp);
            if c == -1 {
                break;
            }
            result.push(c as u8);
            if c == c_int::from(b'\n') {
                break;
            }
        }
        funlockfile(fp);
        if ferror(fp) != 0 {
            io_result_mk_error(decode_io_error(errno(), core::ptr::null_mut()))
        } else {
            if feof(fp) != 0 {
                clearerr(fp);
            }
            io_result_mk_ok(crate::export::mk_string_from_bytes_impl(
                result.as_ptr().cast::<c_char>(),
                result.len(),
            ))
        }
    }
}

/// `lean_io_prim_handle_flush` (`io.cpp:550-556`).
///
/// # Safety
/// `h` is borrowed and live; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0284
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_handle_flush(h: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: live handle per contract.
    unsafe {
        if fflush(io_get_handle(h)) == 0 {
            io_result_mk_ok(tagged::boxi(0))
        } else {
            io_result_mk_error(decode_io_error(errno(), core::ptr::null_mut()))
        }
    }
}

/// `lean_io_prim_handle_rewind` (`io.cpp:560-568`): fseek to the start;
/// failure decodes errno.
///
/// # Safety
/// `h` is borrowed and live; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0333
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_handle_rewind(h: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: live handle per contract.
    unsafe {
        if fseek(io_get_handle(h), 0, SEEK_SET) == 0 {
            io_result_mk_ok(tagged::boxi(0))
        } else {
            io_result_mk_error(decode_io_error(errno(), core::ptr::null_mut()))
        }
    }
}

/// `lean_io_prim_handle_truncate` (`io.cpp:570-582`, the non-Windows arm):
/// ftruncate at the handle's current offset; failure decodes errno.
///
/// # Safety
/// `h` is borrowed and live; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0334
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_handle_truncate(h: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: live handle per contract.
    unsafe {
        let fp = io_get_handle(h);
        if ftruncate(fileno(fp), ftello(fp)) == 0 {
            io_result_mk_ok(tagged::boxi(0))
        } else {
            io_result_mk_error(decode_io_error(errno(), core::ptr::null_mut()))
        }
    }
}

/// `lean_io_prim_handle_lock` (`io.cpp:480-488`, the non-Windows arm):
/// blocking flock, exclusive or shared; failure decodes errno.
///
/// # Safety
/// `h` is borrowed and live; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0335
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_handle_lock(h: *mut LeanObject, exclusive: u8) -> *mut LeanObject {
    // SAFETY: live handle per contract.
    unsafe {
        let fp = io_get_handle(h);
        let op = if exclusive != 0 { LOCK_EX } else { LOCK_SH };
        if flock(fileno(fp), op) == 0 {
            io_result_mk_ok(tagged::boxi(0))
        } else {
            io_result_mk_error(decode_io_error(errno(), core::ptr::null_mut()))
        }
    }
}

/// `lean_io_prim_handle_try_lock` (`io.cpp:490-502`, the non-Windows arm):
/// non-blocking flock — held elsewhere (EWOULDBLOCK) is `ok false`, never
/// an error; acquisition is `ok true`; anything else decodes errno.
///
/// # Safety
/// `h` is borrowed and live; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0336
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_handle_try_lock(h: *mut LeanObject, exclusive: u8) -> *mut LeanObject {
    // SAFETY: live handle per contract.
    unsafe {
        let fp = io_get_handle(h);
        let op = (if exclusive != 0 { LOCK_EX } else { LOCK_SH }) | LOCK_NB;
        if flock(fileno(fp), op) == 0 {
            io_result_mk_ok(tagged::boxi(1))
        } else if errno() == EWOULDBLOCK {
            io_result_mk_ok(tagged::boxi(0))
        } else {
            io_result_mk_error(decode_io_error(errno(), core::ptr::null_mut()))
        }
    }
}

/// `lean_io_prim_handle_unlock` (`io.cpp:504-512`, the non-Windows arm):
/// flock LOCK_UN; failure decodes errno.
///
/// # Safety
/// `h` is borrowed and live; caller owns the io_result.
// UNSAFE-LEDGER: FLN-UL-0337
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_handle_unlock(h: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: live handle per contract.
    unsafe {
        let fp = io_get_handle(h);
        if flock(fileno(fp), LOCK_UN) == 0 {
            io_result_mk_ok(tagged::boxi(0))
        } else {
            io_result_mk_error(decode_io_error(errno(), core::ptr::null_mut()))
        }
    }
}

/// `lean_io_prim_handle_is_tty` (`io.cpp:516-531`): isatty on the fd,
/// errors ignored for cross-platform consistency (the pin's own comment).
///
/// # Safety
/// `h` is borrowed and live.
// UNSAFE-LEDGER: FLN-UL-0285
#[allow(unsafe_code)]
pub(crate) unsafe fn prim_handle_is_tty(h: *mut LeanObject) -> u8 {
    // SAFETY: live handle per contract.
    unsafe { u8::from(isatty(fileno(io_get_handle(h))) != 0) }
}

// ------------------------------------------------------- stream (native)

/// `flush` field body: `Handle.flush h` applied to the world token.
// UNSAFE-LEDGER: FLN-UL-0286
#[allow(unsafe_code)]
extern "C" fn stream_flush_fn(h: *mut LeanObject, _w: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: h arrives owned (closure-arg transfer); the prim borrows it.
    unsafe {
        let r = prim_handle_flush(h);
        rc::dec_ref(h);
        r
    }
}

/// `putStr` field body: `Handle.putStr h s` applied to the world token.
// UNSAFE-LEDGER: FLN-UL-0287
#[allow(unsafe_code)]
extern "C" fn stream_put_str_fn(
    h: *mut LeanObject,
    s: *mut LeanObject,
    _w: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: h and s arrive owned; the prim borrows both.
    unsafe {
        let r = prim_handle_put_str(h, s);
        rc::dec_ref(h);
        if !tagged::is_scalar(s) {
            rc::dec_ref(s);
        }
        r
    }
}

/// `isTty` field body (BaseIO: the compiled result is the bare bool).
// UNSAFE-LEDGER: FLN-UL-0288
#[allow(unsafe_code)]
extern "C" fn stream_is_tty_fn(h: *mut LeanObject, _w: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: h arrives owned; the prim borrows it.
    unsafe {
        let b = prim_handle_is_tty(h);
        rc::dec_ref(h);
        tagged::boxi(b as usize)
    }
}

/// `read` field body: `Handle.read h` applied to (a boxed USize, world).
/// At this pin `lean_box_usize` is ALWAYS a 0-field ctor carrying the
/// usize scalar (`lean.h:2889-2897`) — never a tagged scalar.
// UNSAFE-LEDGER: FLN-UL-0316
#[allow(unsafe_code)]
extern "C" fn stream_read_fn(
    h: *mut LeanObject,
    sz: *mut LeanObject,
    _w: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: h and sz arrive owned; the prim borrows h; the USize box is
    // read then released.
    unsafe {
        let n = object::ctor_get_scalar::<usize>(sz, 0);
        rc::dec_ref(sz);
        let r = prim_handle_read(h, n);
        rc::dec_ref(h);
        r
    }
}

/// `write` field body: `Handle.write h` applied to (a ByteArray, world).
// UNSAFE-LEDGER: FLN-UL-0317
#[allow(unsafe_code)]
extern "C" fn stream_write_fn(
    h: *mut LeanObject,
    ba: *mut LeanObject,
    _w: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: h and ba arrive owned; the prim borrows both.
    unsafe {
        let r = prim_handle_write(h, ba);
        rc::dec_ref(h);
        rc::dec_ref(ba);
        r
    }
}

/// `getLine` field body: `Handle.getLine h` applied to the world token.
// UNSAFE-LEDGER: FLN-UL-0330
#[allow(unsafe_code)]
extern "C" fn stream_get_line_fn(h: *mut LeanObject, _w: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: h arrives owned (closure-arg transfer); the prim borrows it.
    unsafe {
        let r = prim_handle_get_line(h);
        rc::dec_ref(h);
        r
    }
}

/// The native `Stream.ofHandle` (`Init/System/IO.lean:1683-1690`,
/// `@[export lean_stream_of_handle]`): the six-field structure — flush,
/// read, write, getLine, putStr, isTty in declaration order — each field a
/// closure over the handle, exactly the shape the Lean definition compiles
/// to.
///
/// # Safety
/// `h` is consumed (distributed across the six closures); caller owns the
/// stream.
// UNSAFE-LEDGER: FLN-UL-0292
#[allow(unsafe_code)]
pub(crate) unsafe fn stream_of_handle(h: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: h arrives holding one token; five more are minted so each of
    // the six closures owns one. Every fresh object's slots are initialized
    // before escape.
    unsafe {
        rc::inc_ref_n(h, 5);
        let close1 = |target: *mut c_void, arity: u16| {
            let c = object::alloc_closure(target, arity, 1);
            object::closure_set(c, 0, h);
            c
        };
        let stream = object::alloc_ctor(0, 6, 0);
        object::ctor_set(stream, 0, close1(stream_flush_fn as *mut c_void, 2));
        object::ctor_set(stream, 1, close1(stream_read_fn as *mut c_void, 3));
        object::ctor_set(stream, 2, close1(stream_write_fn as *mut c_void, 3));
        object::ctor_set(stream, 3, close1(stream_get_line_fn as *mut c_void, 2));
        object::ctor_set(stream, 4, close1(stream_put_str_fn as *mut c_void, 3));
        object::ctor_set(stream, 5, close1(stream_is_tty_fn as *mut c_void, 2));
        stream
    }
}

// --------------------------------------------- the thread-current trio

const IX_STDIN: usize = 0;
const IX_STDOUT: usize = 1;
const IX_STDERR: usize = 2;

/// A process-initial stream pointer: persistent, immortal, immutable —
/// which is what justifies the Send+Sync claim.
struct InitialStream(*mut LeanObject);
// SAFETY: the pointee is mark_persistent'd before publication and never
// mutated; sharing an immortal immutable object across threads is the pin's
// own g_stream_* discipline.
// UNSAFE-LEDGER: FLN-UL-0293
#[allow(unsafe_code)]
unsafe impl Send for InitialStream {}
// SAFETY: as the Send impl directly above — the pointee is persistent,
// immortal and immutable before publication.
// UNSAFE-LEDGER: FLN-UL-0294
#[allow(unsafe_code)]
unsafe impl Sync for InitialStream {}

/// The pin's `initialize_io` stream half (`io.cpp:1647-1656`), run lazily
/// once per process: SIGPIPE ignored, the three streams built over the
/// process's own stdio FILE*s and marked persistent.
fn initial_streams() -> &'static [InitialStream; 3] {
    static INITIAL: OnceLock<[InitialStream; 3]> = OnceLock::new();
    INITIAL.get_or_init(|| {
        // SAFETY: the glibc FILE* globals are live for the process's life
        // and are NOT owned by these handles' finalizers, because the
        // persistent mark makes the wrapping objects immortal — fclose can
        // never run on them, exactly as the pin's eternal g_stream trio.
        // UNSAFE-LEDGER: FLN-UL-0295
        #[allow(unsafe_code)]
        unsafe {
            signal(SIGPIPE, SIG_IGN);
            let mk = |fp: *mut c_void| {
                let s = stream_of_handle(io_wrap_handle(fp));
                rc::mark_persistent(s);
                InitialStream(s)
            };
            [mk(stdin), mk(stdout), mk(stderr)]
        }
    })
}

thread_local! {
    /// The pin's `MK_THREAD_LOCAL_GET` trio: each thread's current streams,
    /// seeded from the PROCESS-initial set on first use, dec'd at thread
    /// exit (a no-op for the persistent initials).
    static CURRENT: std::cell::RefCell<CurrentStreams> =
        const { std::cell::RefCell::new(CurrentStreams([core::ptr::null_mut(); 3])) };
}

struct CurrentStreams([*mut LeanObject; 3]);

impl Drop for CurrentStreams {
    fn drop(&mut self) {
        for &p in &self.0 {
            if !p.is_null() {
                // SAFETY: the slot holds one owned token per seed/install.
                // UNSAFE-LEDGER: FLN-UL-0296
                #[allow(unsafe_code)]
                unsafe {
                    rc::dec_ref(p);
                }
            }
        }
    }
}

fn seeded(slot: &mut CurrentStreams, ix: usize) -> *mut LeanObject {
    if slot.0[ix].is_null() {
        let init = initial_streams()[ix].0;
        // SAFETY: persistent target — the inc is the pin's object_ref copy
        // discipline and is a no-op on the immortal initial.
        // UNSAFE-LEDGER: FLN-UL-0297
        #[allow(unsafe_code)]
        unsafe {
            rc::inc_ref_n(init, 1);
        }
        slot.0[ix] = init;
    }
    slot.0[ix]
}

/// `lean_get_stdout`-family core (`io.cpp:119-131`): a fresh reference to
/// this thread's current stream.
pub(crate) fn get_current(ix: usize) -> *mut LeanObject {
    CURRENT.with(|c| {
        let mut slot = c.borrow_mut();
        let s = seeded(&mut slot, ix);
        // SAFETY: live stream; the caller's token is minted here.
        // UNSAFE-LEDGER: FLN-UL-0298
        #[allow(unsafe_code)]
        unsafe {
            rc::inc_ref_n(s, 1);
        }
        s
    })
}

/// `lean_get_set_stdout`-family core (`io.cpp:133-158`): steal the old
/// current, install the new (ownership transfers in), return the old
/// (ownership transfers out).
pub(crate) fn get_set_current(ix: usize, new: *mut LeanObject) -> *mut LeanObject {
    CURRENT.with(|c| {
        let mut slot = c.borrow_mut();
        let old = seeded(&mut slot, ix);
        slot.0[ix] = new;
        old
    })
}

/// The eager half of `lean_initialize_runtime_module`'s twin: force the
/// process-initial trio (and with it the SIGPIPE disposition) exactly as
/// the pin's `initialize_io` does eagerly.
pub(crate) fn initialize_streams() {
    let _ = initial_streams();
}

pub(crate) fn get_stdin() -> *mut LeanObject {
    get_current(IX_STDIN)
}
pub(crate) fn get_stdout() -> *mut LeanObject {
    get_current(IX_STDOUT)
}
pub(crate) fn get_stderr() -> *mut LeanObject {
    get_current(IX_STDERR)
}
pub(crate) fn get_set_stdin(h: *mut LeanObject) -> *mut LeanObject {
    get_set_current(IX_STDIN, h)
}
pub(crate) fn get_set_stdout(h: *mut LeanObject) -> *mut LeanObject {
    get_set_current(IX_STDOUT, h)
}
pub(crate) fn get_set_stderr(h: *mut LeanObject) -> *mut LeanObject {
    get_set_current(IX_STDERR, h)
}
