//! Deterministic bare-math symbols demanded by generated Lean C.
//!
//! The pinned `@[extern]` census names these functions directly (`sin`,
//! `sqrt`, `pow`, and their binary32 twins), rather than through the
//! `lean_*` object ABI.  Keeping the exports in this boundary crate lets
//! generated C link against Marrow without linking a platform libm, while
//! the arithmetic itself remains in the safe, `forbid(unsafe_code)`
//! `fln-libm` crate.

// Binary64 -----------------------------------------------------------------

// UNSAFE-LEDGER: FLN-UL-0569
#[allow(unsafe_code)]
#[unsafe(export_name = "fabs")]
pub(crate) extern "C" fn export_fabs(x: f64) -> f64 {
    fln_libm::abs(x)
}

// UNSAFE-LEDGER: FLN-UL-0570
#[allow(unsafe_code)]
#[unsafe(export_name = "acos")]
pub(crate) extern "C" fn export_acos(x: f64) -> f64 {
    fln_libm::acos(x)
}

// UNSAFE-LEDGER: FLN-UL-0571
#[allow(unsafe_code)]
#[unsafe(export_name = "acosh")]
pub(crate) extern "C" fn export_acosh(x: f64) -> f64 {
    fln_libm::acosh(x)
}

// UNSAFE-LEDGER: FLN-UL-0572
#[allow(unsafe_code)]
#[unsafe(export_name = "asin")]
pub(crate) extern "C" fn export_asin(x: f64) -> f64 {
    fln_libm::asin(x)
}

// UNSAFE-LEDGER: FLN-UL-0573
#[allow(unsafe_code)]
#[unsafe(export_name = "asinh")]
pub(crate) extern "C" fn export_asinh(x: f64) -> f64 {
    fln_libm::asinh(x)
}

// UNSAFE-LEDGER: FLN-UL-0574
#[allow(unsafe_code)]
#[unsafe(export_name = "atan")]
pub(crate) extern "C" fn export_atan(x: f64) -> f64 {
    fln_libm::atan(x)
}

// UNSAFE-LEDGER: FLN-UL-0575
#[allow(unsafe_code)]
#[unsafe(export_name = "atan2")]
pub(crate) extern "C" fn export_atan2(y: f64, x: f64) -> f64 {
    fln_libm::atan2(y, x)
}

// UNSAFE-LEDGER: FLN-UL-0576
#[allow(unsafe_code)]
#[unsafe(export_name = "atanh")]
pub(crate) extern "C" fn export_atanh(x: f64) -> f64 {
    fln_libm::atanh(x)
}

// UNSAFE-LEDGER: FLN-UL-0577
#[allow(unsafe_code)]
#[unsafe(export_name = "cbrt")]
pub(crate) extern "C" fn export_cbrt(x: f64) -> f64 {
    fln_libm::cbrt(x)
}

// UNSAFE-LEDGER: FLN-UL-0578
#[allow(unsafe_code)]
#[unsafe(export_name = "ceil")]
pub(crate) extern "C" fn export_ceil(x: f64) -> f64 {
    fln_libm::ceil(x)
}

// UNSAFE-LEDGER: FLN-UL-0579
#[allow(unsafe_code)]
#[unsafe(export_name = "cos")]
pub(crate) extern "C" fn export_cos(x: f64) -> f64 {
    fln_libm::cos(x)
}

// UNSAFE-LEDGER: FLN-UL-0580
#[allow(unsafe_code)]
#[unsafe(export_name = "cosh")]
pub(crate) extern "C" fn export_cosh(x: f64) -> f64 {
    fln_libm::cosh(x)
}

// UNSAFE-LEDGER: FLN-UL-0581
#[allow(unsafe_code)]
#[unsafe(export_name = "exp")]
pub(crate) extern "C" fn export_exp(x: f64) -> f64 {
    fln_libm::exp(x)
}

// UNSAFE-LEDGER: FLN-UL-0582
#[allow(unsafe_code)]
#[unsafe(export_name = "exp2")]
pub(crate) extern "C" fn export_exp2(x: f64) -> f64 {
    fln_libm::exp2(x)
}

// UNSAFE-LEDGER: FLN-UL-0583
#[allow(unsafe_code)]
#[unsafe(export_name = "floor")]
pub(crate) extern "C" fn export_floor(x: f64) -> f64 {
    fln_libm::floor(x)
}

// UNSAFE-LEDGER: FLN-UL-0584
#[allow(unsafe_code)]
#[unsafe(export_name = "log")]
pub(crate) extern "C" fn export_log(x: f64) -> f64 {
    fln_libm::log(x)
}

// UNSAFE-LEDGER: FLN-UL-0585
#[allow(unsafe_code)]
#[unsafe(export_name = "log10")]
pub(crate) extern "C" fn export_log10(x: f64) -> f64 {
    fln_libm::log10(x)
}

// UNSAFE-LEDGER: FLN-UL-0586
#[allow(unsafe_code)]
#[unsafe(export_name = "log2")]
pub(crate) extern "C" fn export_log2(x: f64) -> f64 {
    fln_libm::log2(x)
}

// UNSAFE-LEDGER: FLN-UL-0587
#[allow(unsafe_code)]
#[unsafe(export_name = "pow")]
pub(crate) extern "C" fn export_pow(x: f64, y: f64) -> f64 {
    fln_libm::pow(x, y)
}

// UNSAFE-LEDGER: FLN-UL-0588
#[allow(unsafe_code)]
#[unsafe(export_name = "round")]
pub(crate) extern "C" fn export_round(x: f64) -> f64 {
    fln_libm::round(x)
}

// UNSAFE-LEDGER: FLN-UL-0589
#[allow(unsafe_code)]
#[unsafe(export_name = "sin")]
pub(crate) extern "C" fn export_sin(x: f64) -> f64 {
    fln_libm::sin(x)
}

// UNSAFE-LEDGER: FLN-UL-0590
#[allow(unsafe_code)]
#[unsafe(export_name = "sinh")]
pub(crate) extern "C" fn export_sinh(x: f64) -> f64 {
    fln_libm::sinh(x)
}

// UNSAFE-LEDGER: FLN-UL-0591
#[allow(unsafe_code)]
#[unsafe(export_name = "sqrt")]
pub(crate) extern "C" fn export_sqrt(x: f64) -> f64 {
    fln_libm::sqrt(x)
}

// UNSAFE-LEDGER: FLN-UL-0592
#[allow(unsafe_code)]
#[unsafe(export_name = "tan")]
pub(crate) extern "C" fn export_tan(x: f64) -> f64 {
    fln_libm::tan(x)
}

// UNSAFE-LEDGER: FLN-UL-0593
#[allow(unsafe_code)]
#[unsafe(export_name = "tanh")]
pub(crate) extern "C" fn export_tanh(x: f64) -> f64 {
    fln_libm::tanh(x)
}

// Binary32 -----------------------------------------------------------------

// UNSAFE-LEDGER: FLN-UL-0594
#[allow(unsafe_code)]
#[unsafe(export_name = "fabsf")]
pub(crate) extern "C" fn export_fabsf(x: f32) -> f32 {
    fln_libm::f32::abs(x)
}

// UNSAFE-LEDGER: FLN-UL-0595
#[allow(unsafe_code)]
#[unsafe(export_name = "acosf")]
pub(crate) extern "C" fn export_acosf(x: f32) -> f32 {
    fln_libm::f32::acos(x)
}

// UNSAFE-LEDGER: FLN-UL-0596
#[allow(unsafe_code)]
#[unsafe(export_name = "acoshf")]
pub(crate) extern "C" fn export_acoshf(x: f32) -> f32 {
    fln_libm::f32::acosh(x)
}

// UNSAFE-LEDGER: FLN-UL-0597
#[allow(unsafe_code)]
#[unsafe(export_name = "asinf")]
pub(crate) extern "C" fn export_asinf(x: f32) -> f32 {
    fln_libm::f32::asin(x)
}

// UNSAFE-LEDGER: FLN-UL-0598
#[allow(unsafe_code)]
#[unsafe(export_name = "asinhf")]
pub(crate) extern "C" fn export_asinhf(x: f32) -> f32 {
    fln_libm::f32::asinh(x)
}

// UNSAFE-LEDGER: FLN-UL-0599
#[allow(unsafe_code)]
#[unsafe(export_name = "atanf")]
pub(crate) extern "C" fn export_atanf(x: f32) -> f32 {
    fln_libm::f32::atan(x)
}

// UNSAFE-LEDGER: FLN-UL-0600
#[allow(unsafe_code)]
#[unsafe(export_name = "atan2f")]
pub(crate) extern "C" fn export_atan2f(y: f32, x: f32) -> f32 {
    fln_libm::f32::atan2(y, x)
}

// UNSAFE-LEDGER: FLN-UL-0601
#[allow(unsafe_code)]
#[unsafe(export_name = "atanhf")]
pub(crate) extern "C" fn export_atanhf(x: f32) -> f32 {
    fln_libm::f32::atanh(x)
}

// UNSAFE-LEDGER: FLN-UL-0602
#[allow(unsafe_code)]
#[unsafe(export_name = "cbrtf")]
pub(crate) extern "C" fn export_cbrtf(x: f32) -> f32 {
    fln_libm::f32::cbrt(x)
}

// UNSAFE-LEDGER: FLN-UL-0603
#[allow(unsafe_code)]
#[unsafe(export_name = "ceilf")]
pub(crate) extern "C" fn export_ceilf(x: f32) -> f32 {
    fln_libm::f32::ceil(x)
}

// UNSAFE-LEDGER: FLN-UL-0604
#[allow(unsafe_code)]
#[unsafe(export_name = "cosf")]
pub(crate) extern "C" fn export_cosf(x: f32) -> f32 {
    fln_libm::f32::cos(x)
}

// UNSAFE-LEDGER: FLN-UL-0605
#[allow(unsafe_code)]
#[unsafe(export_name = "coshf")]
pub(crate) extern "C" fn export_coshf(x: f32) -> f32 {
    fln_libm::f32::cosh(x)
}

// UNSAFE-LEDGER: FLN-UL-0606
#[allow(unsafe_code)]
#[unsafe(export_name = "expf")]
pub(crate) extern "C" fn export_expf(x: f32) -> f32 {
    fln_libm::f32::exp(x)
}

// UNSAFE-LEDGER: FLN-UL-0607
#[allow(unsafe_code)]
#[unsafe(export_name = "exp2f")]
pub(crate) extern "C" fn export_exp2f(x: f32) -> f32 {
    fln_libm::f32::exp2(x)
}

// UNSAFE-LEDGER: FLN-UL-0608
#[allow(unsafe_code)]
#[unsafe(export_name = "floorf")]
pub(crate) extern "C" fn export_floorf(x: f32) -> f32 {
    fln_libm::f32::floor(x)
}

// UNSAFE-LEDGER: FLN-UL-0609
#[allow(unsafe_code)]
#[unsafe(export_name = "logf")]
pub(crate) extern "C" fn export_logf(x: f32) -> f32 {
    fln_libm::f32::log(x)
}

// UNSAFE-LEDGER: FLN-UL-0610
#[allow(unsafe_code)]
#[unsafe(export_name = "log10f")]
pub(crate) extern "C" fn export_log10f(x: f32) -> f32 {
    fln_libm::f32::log10(x)
}

// UNSAFE-LEDGER: FLN-UL-0611
#[allow(unsafe_code)]
#[unsafe(export_name = "log2f")]
pub(crate) extern "C" fn export_log2f(x: f32) -> f32 {
    fln_libm::f32::log2(x)
}

// UNSAFE-LEDGER: FLN-UL-0612
#[allow(unsafe_code)]
#[unsafe(export_name = "powf")]
pub(crate) extern "C" fn export_powf(x: f32, y: f32) -> f32 {
    fln_libm::f32::pow(x, y)
}

// UNSAFE-LEDGER: FLN-UL-0613
#[allow(unsafe_code)]
#[unsafe(export_name = "roundf")]
pub(crate) extern "C" fn export_roundf(x: f32) -> f32 {
    fln_libm::f32::round(x)
}

// UNSAFE-LEDGER: FLN-UL-0614
#[allow(unsafe_code)]
#[unsafe(export_name = "sinf")]
pub(crate) extern "C" fn export_sinf(x: f32) -> f32 {
    fln_libm::f32::sin(x)
}

// UNSAFE-LEDGER: FLN-UL-0615
#[allow(unsafe_code)]
#[unsafe(export_name = "sinhf")]
pub(crate) extern "C" fn export_sinhf(x: f32) -> f32 {
    fln_libm::f32::sinh(x)
}

// UNSAFE-LEDGER: FLN-UL-0616
#[allow(unsafe_code)]
#[unsafe(export_name = "sqrtf")]
pub(crate) extern "C" fn export_sqrtf(x: f32) -> f32 {
    fln_libm::f32::sqrt(x)
}

// UNSAFE-LEDGER: FLN-UL-0617
#[allow(unsafe_code)]
#[unsafe(export_name = "tanf")]
pub(crate) extern "C" fn export_tanf(x: f32) -> f32 {
    fln_libm::f32::tan(x)
}

// UNSAFE-LEDGER: FLN-UL-0618
#[allow(unsafe_code)]
#[unsafe(export_name = "tanhf")]
pub(crate) extern "C" fn export_tanhf(x: f32) -> f32 {
    fln_libm::f32::tanh(x)
}
