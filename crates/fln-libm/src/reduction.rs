//! Fixed Payne-Hanek argument reduction for binary64 trigonometric functions.
//!
//! This is an in-house, safe Rust transcription of the classic 24-bit-chunk
//! method, informed by the permissively licensed FreeBSD `rem_pio2` method.
//! It is not linked from, nor delegated to, a system libm.

const INV_PIO2: f64 = f64::from_bits(0x3fe4_5f30_6dc9_c883);
const PIO2_1: f64 = 1.570_796_326_734_125_6;
const PIO2_1T: f64 = 6.077_100_506_506_192e-11;
const PIO2_2: f64 = 6.077_100_506_303_966e-11;
const PIO2_2T: f64 = 2.022_266_248_795_950_6e-21;
const PIO2_3: f64 = 2.022_266_248_711_166_5e-21;
const PIO2_3T: f64 = 8.478_427_660_368_9e-32;
const TWO24: f64 = f64::from_bits(0x4170_0000_0000_0000);
const TWO_NEG24: f64 = f64::from_bits(0x3e70_0000_0000_0000);

// 396 hexadecimal digits of 2/pi.  Binary64 needs at most the first 66
// 24-bit chunks (its greatest exponent is 1023), unlike wider formats.
const TWO_OVER_PI: [i32; 66] = [
    0xa2f983, 0x6e4e44, 0x1529fc, 0x2757d1, 0xf534dd, 0xc0db62, 0x95993c, 0x439041, 0xfe5163,
    0xabdebb, 0xc561b7, 0x246e3a, 0x424dd2, 0xe00649, 0x2eea09, 0xd1921c, 0xfe1deb, 0x1cb129,
    0xa73ee8, 0x8235f5, 0x2ebb44, 0x84e99c, 0x7026b4, 0x5f7e41, 0x3991d6, 0x398353, 0x39f49c,
    0x845f8b, 0xbdf928, 0x3b1ff8, 0x97ffde, 0x05980f, 0xef2f11, 0x8b5a0a, 0x6d1f6d, 0x367ecf,
    0x27cb09, 0xb74f46, 0x3f669e, 0x5fea2d, 0x7527ba, 0xc7ebe5, 0xf17b3d, 0x0739f7, 0x8a5292,
    0xea6bfb, 0x5fb11f, 0x8d5d08, 0x560330, 0x46fc7b, 0x6babf0, 0xcfbc20, 0x9af436, 0x1da9e3,
    0x91615e, 0xe61b08, 0x659985, 0x5f14a0, 0x68408d, 0xffd880, 0x4d7327, 0x310606, 0x1556ca,
    0x73a8c9, 0x60e27b, 0xc08c6b,
];

const PIO2: [f64; 8] = [
    1.570_796_251_296_997,
    7.549_789_415_861_596e-8,
    5.390_302_529_957_765e-15,
    3.282_003_415_807_913e-22,
    1.270_655_753_080_676e-29,
    1.229_333_089_811_113_3e-36,
    2.733_700_538_164_645_6e-44,
    2.167_416_838_778_048_2e-51,
];

fn round_to_even(x: f64) -> f64 {
    let lower = super::floor(x);
    let fraction = x - lower;
    if fraction < 0.5 {
        lower
    } else if fraction > 0.5 {
        lower + 1.0
    } else if (lower as i64) & 1 == 0 {
        lower
    } else {
        lower + 1.0
    }
}

fn medium(x: f64, exponent: i32) -> (i32, f64, f64) {
    let n_as_float = round_to_even(x * INV_PIO2);
    let n = n_as_float as i32;
    let mut remainder = x - n_as_float * PIO2_1;
    let mut correction = n_as_float * PIO2_1T;
    let mut head = remainder - correction;
    let reduced_exponent = ((head.to_bits() >> 52) & 0x7ff) as i32;
    if exponent - reduced_exponent > 16 {
        let previous = remainder;
        correction = n_as_float * PIO2_2;
        remainder = previous - correction;
        correction = n_as_float * PIO2_2T - ((previous - remainder) - correction);
        head = remainder - correction;
        let reduced_exponent = ((head.to_bits() >> 52) & 0x7ff) as i32;
        if exponent - reduced_exponent > 49 {
            let previous = remainder;
            correction = n_as_float * PIO2_3;
            remainder = previous - correction;
            correction = n_as_float * PIO2_3T - ((previous - remainder) - correction);
            head = remainder - correction;
        }
    }
    (n, head, (remainder - head) - correction)
}

/// Returns `(quadrant, head, tail)` where `x = quadrant * pi/2 + head + tail`
/// and the remainder has magnitude at most pi/4.
pub(crate) fn rem_pio2(x: f64) -> (i32, f64, f64) {
    let bits = x.to_bits();
    let exponent_word = ((bits >> 52) & 0x7ff) as i32;
    let absolute_word = (bits >> 32) as u32 & 0x7fff_ffff;
    if absolute_word < 0x4139_21fb {
        return medium(x, exponent_word);
    }
    if exponent_word == 0x7ff {
        let nan = super::canonical_nan();
        return (0, nan, nan);
    }

    let sign_negative = bits >> 63 != 0;
    let normalized = f64::from_bits((bits & 0x000f_ffff_ffff_ffff) | (1046_u64 << 52));
    let mut pieces = [0.0; 3];
    let mut scaled = normalized;
    for piece in pieces.iter_mut().take(2) {
        *piece = scaled as i32 as f64;
        scaled = (scaled - *piece) * TWO24;
    }
    pieces[2] = scaled;
    let mut count = 3;
    while count > 1 && pieces[count - 1] == 0.0 {
        count -= 1;
    }
    let (quadrant, head, tail) = payne_hanek(&pieces[..count], exponent_word - 1046);
    if sign_negative {
        (-quadrant, -head, -tail)
    } else {
        (quadrant, head, tail)
    }
}

fn payne_hanek(parts: &[f64], exponent: i32) -> (i32, f64, f64) {
    const JK: usize = 4; // Enough for binary64's 53-bit result plus recomputation.
    let jx = parts.len() - 1;
    let mut jv = (exponent - 3).div_euclid(24);
    if jv < 0 {
        jv = 0;
    }
    let jv = jv as usize;
    let mut q0 = exponent - 24 * (jv as i32 + 1);
    let mut f = [0.0; 20];
    let mut q = [0.0; 20];
    let mut iq = [0_i32; 20];
    let mut fq = [0.0; 20];
    for (i, value) in f.iter_mut().enumerate().take(jx + JK + 1) {
        let source = jv as isize + i as isize - jx as isize;
        *value = if source < 0 {
            0.0
        } else {
            TWO_OVER_PI[source as usize] as f64
        };
    }
    for i in 0..=JK {
        for j in 0..=jx {
            q[i] += parts[j] * f[jx + i - j];
        }
    }

    let mut jz = JK;
    let (n, ih, fraction) = loop {
        let mut z = q[jz];
        for j in (1..=jz).rev() {
            let carry = (TWO_NEG24 * z) as i32 as f64;
            iq[jz - j] = (z - TWO24 * carry) as i32;
            z = q[j - 1] + carry;
        }
        z = super::scalbn(z, q0);
        z -= 8.0 * super::floor(z * 0.125);
        let mut n = z as i32;
        z -= n as f64;
        let ih = if q0 > 0 {
            let top = iq[jz - 1] >> (24 - q0);
            n += top;
            iq[jz - 1] -= top << (24 - q0);
            iq[jz - 1] >> (23 - q0)
        } else if q0 == 0 {
            iq[jz - 1] >> 23
        } else if z >= 0.5 {
            2
        } else {
            0
        };
        if ih > 0 {
            n += 1;
            let mut carry = false;
            for digit in iq.iter_mut().take(jz) {
                if !carry && *digit != 0 {
                    carry = true;
                    *digit = 0x0100_0000 - *digit;
                } else if carry {
                    *digit = 0x00ff_ffff - *digit;
                }
            }
            if q0 == 1 {
                iq[jz - 1] &= 0x007f_ffff;
            } else if q0 == 2 {
                iq[jz - 1] &= 0x003f_ffff;
            }
            if ih == 2 {
                z = 1.0 - z;
                if carry {
                    z -= super::scalbn(1.0, q0);
                }
            }
        }
        if z != 0.0 || (JK..jz).rev().any(|i| iq[i] != 0) {
            break (n, ih, z);
        }
        let mut extra = 1;
        while iq[JK - extra] == 0 {
            extra += 1;
        }
        for i in (jz + 1)..=(jz + extra) {
            f[jx + i] = TWO_OVER_PI[jv + i] as f64;
            for j in 0..=jx {
                q[i] += parts[j] * f[jx + i - j];
            }
        }
        jz += extra;
    };

    let mut z = fraction;
    if z == 0.0 {
        jz -= 1;
        q0 -= 24;
        while iq[jz] == 0 {
            jz -= 1;
            q0 -= 24;
        }
    } else {
        z = super::scalbn(z, -q0);
        if z >= TWO24 {
            let carry = (TWO_NEG24 * z) as i32 as f64;
            iq[jz] = (z - TWO24 * carry) as i32;
            jz += 1;
            q0 += 24;
            iq[jz] = carry as i32;
        } else {
            iq[jz] = z as i32;
        }
    }
    let mut scale = super::scalbn(1.0, q0);
    for i in (0..=jz).rev() {
        q[i] = scale * iq[i] as f64;
        scale *= TWO_NEG24;
    }
    for i in (0..=jz).rev() {
        for k in 0..=JK.min(jz - i) {
            fq[jz - i] += PIO2[k] * q[i + k];
        }
    }
    let mut head = 0.0;
    for i in (0..=jz).rev() {
        head += fq[i];
    }
    let mut tail = fq[0] - head;
    for value in fq.iter().take(jz + 1).skip(1) {
        tail += *value;
    }
    if ih == 0 {
        (n & 7, head, tail)
    } else {
        (n & 7, -head, -tail)
    }
}

#[cfg(test)]
mod tests {
    use super::rem_pio2;
    use crate::{cos, sin, tan};

    #[test]
    fn huge_finite_inputs_reduce_to_a_small_remainder() {
        for input in [1.0e20, -1.0e20, f64::MAX, -f64::MAX] {
            let (_, head, tail) = rem_pio2(input);
            assert!(
                (head + tail).abs() <= core::f64::consts::FRAC_PI_4,
                "input={input:?}, head={head:?}, tail={tail:?}"
            );
        }
    }

    #[test]
    fn huge_argument_trig_vectors_are_bit_stable() {
        const VECTORS: [(f64, u64, u64, u64); 4] = [
            (
                1.0e20,
                0xbfe4_a5e6_05fd_6450,
                0x3fe8_7272_0fc6_0d3d,
                0xbfeb_06fb_be99_5394,
            ),
            (
                -1.0e20,
                0x3fe4_a5e6_05fd_6450,
                0x3fe8_7272_0fc6_0d3d,
                0x3feb_06fb_be99_5394,
            ),
            (
                f64::MAX,
                0x3f74_52fc_98b3_4e97,
                0xbfef_ffe6_2ecf_ab75,
                0xbf74_530c_fe72_9484,
            ),
            (
                -f64::MAX,
                0xbf74_52fc_98b3_4e97,
                0xbfef_ffe6_2ecf_ab75,
                0x3f74_530c_fe72_9484,
            ),
        ];
        for (input, expected_sin, expected_cos, expected_tan) in VECTORS {
            assert_eq!(sin(input).to_bits(), expected_sin, "sin({input:?})");
            assert_eq!(cos(input).to_bits(), expected_cos, "cos({input:?})");
            assert_eq!(tan(input).to_bits(), expected_tan, "tan({input:?})");
        }
    }
}
