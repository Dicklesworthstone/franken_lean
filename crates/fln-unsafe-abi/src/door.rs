//! The inbound plugin door's SPIKE-SCALE seam: dlopen/dlsym over the platform
//! loader, declared directly (bead `franken_lean-7xe`, G0-3 acceptance b; the
//! PRODUCT door — revocation-first, receipts — is `franken_lean-sno`'s, and the
//! dependency graph routes it AFTER this spike deliberately: sno depends on
//! fln-lld depends on 7xe).
//!
//! D1 note: the closed universe has no `libloading` and `std` has no dlopen;
//! the loader symbols are declared here directly — they come from the platform
//! loader already present in every process image, so this adds NO dependency.
//! Linux-only, exactly like the layout mirrors' target gate in `lib.rs`.

use core::ffi::{c_char, c_int, c_void, CStr};

/// `RTLD_NOW` (`dlfcn.h`, glibc): resolve every undefined symbol at load time —
/// the whole-membrane bind the spike wants, where one missing export fails
/// loudly with its name instead of lazily at first call.
pub(crate) const RTLD_NOW: c_int = 0x2;
/// `RTLD_GLOBAL` (`dlfcn.h`, glibc): the object's symbols join the global
/// scope, so a later load (the plugin) can resolve against an earlier one
/// (the initializer shim).
pub(crate) const RTLD_GLOBAL: c_int = 0x100;

// UNSAFE-LEDGER: FLN-UL-0187
#[allow(unsafe_code)]
unsafe extern "C" {
    fn dlopen(filename: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(handle: *mut c_void, symbol: *const c_char) -> *mut c_void;
    fn dlclose(handle: *mut c_void) -> c_int;
    fn dlerror() -> *mut c_char;
}

/// A loaded shared object. No revocation, no receipts — those are the product
/// door's; this handle exists to prove the membrane bind and is deliberately
/// `pub(crate)`.
pub(crate) struct LoadedPlugin(*mut c_void);

/// The loader's own error text, drained (dlerror clears on read).
fn take_dlerror() -> String {
    // SAFETY: dlerror returns either null or a NUL-terminated static/thread
    // buffer owned by the loader; read-only access before the next dl* call.
    // UNSAFE-LEDGER: FLN-UL-0188
    #[allow(unsafe_code)]
    unsafe {
        let p = dlerror();
        if p.is_null() {
            "<no loader diagnostic>".to_string()
        } else {
            CStr::from_ptr(p).to_string_lossy().into_owned()
        }
    }
}

impl LoadedPlugin {
    /// dlopen under the given flags; a failed load returns the loader's own
    /// diagnostic (which names the first unresolved symbol under RTLD_NOW —
    /// the demand-list measurement continuing itself).
    pub(crate) fn open(path: &CStr, flags: c_int) -> Result<LoadedPlugin, String> {
        // SAFETY: `path` is a valid NUL-terminated string; dlopen's contract.
        // UNSAFE-LEDGER: FLN-UL-0188
        #[allow(unsafe_code)]
        let h = unsafe { dlopen(path.as_ptr(), flags) };
        if h.is_null() {
            Err(take_dlerror())
        } else {
            Ok(LoadedPlugin(h))
        }
    }

    /// Resolve a symbol to a raw address; the CALLER owns the transmute to a
    /// function type, which is where the arity-by-type law applies.
    pub(crate) fn symbol(&self, name: &CStr) -> Result<*mut c_void, String> {
        // SAFETY: live handle; dlsym's contract. A null result with no error
        // is a genuinely-null symbol, reported as absent.
        // UNSAFE-LEDGER: FLN-UL-0188
        #[allow(unsafe_code)]
        let p = unsafe { dlsym(self.0, name.as_ptr()) };
        if p.is_null() {
            Err(take_dlerror())
        } else {
            Ok(p)
        }
    }
}

impl Drop for LoadedPlugin {
    fn drop(&mut self) {
        // SAFETY: live handle, closed exactly once; a nonzero dlclose is
        // loader-internal and unreportable from Drop — the spike accepts it,
        // the product door will receipt it.
        // UNSAFE-LEDGER: FLN-UL-0188
        #[allow(unsafe_code)]
        unsafe {
            let _ = dlclose(self.0);
        }
    }
}
