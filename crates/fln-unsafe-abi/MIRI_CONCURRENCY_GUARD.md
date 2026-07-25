# Miri concurrency guard for Marrow (fln-unsafe-abi + fln-rt)

The answer to "can any of this run under a sanitizer in CI" is **yes**, it is
cheap, and it demonstrably catches the real defect. This file is the runnable
spec; bead `fln-nhf5` tracks wiring it into CI, which is not this crate's domain.

## The command

```bash
rustup component add --toolchain nightly-2026-07-13-x86_64-unknown-linux-gnu miri rust-src

MIRIFLAGS="-Zmiri-disable-isolation -Zmiri-ignore-leaks" \
  cargo +nightly-2026-07-13 miri test -p fln-unsafe-abi --lib \
    mark_mt_negates_and_atomics_conserve
MIRIFLAGS="-Zmiri-disable-isolation -Zmiri-ignore-leaks" \
  cargo +nightly-2026-07-13 miri test -p fln-unsafe-abi --lib \
    mt_object_dies_on_last_dec
MIRIFLAGS="-Zmiri-disable-isolation -Zmiri-ignore-leaks" \
  cargo +nightly-2026-07-13 miri test -p fln-unsafe-abi --lib \
    rc_clone_and_drop_balance
MIRIFLAGS="-Zmiri-disable-isolation -Zmiri-ignore-leaks" \
  cargo +nightly-2026-07-13 miri test -p fln-rt --test region_engine \
    concurrent_publication
```

Measured wall time, whole set: **~12 s** (9.26 + 0.39 + 0.35 + 2.02).

## Why it is a targeted set and not `miri test`

Running the *whole* fln-unsafe-abi suite under Miri exceeds ten minutes and was
killed — Miri is roughly two orders of magnitude slower than native, and most of
those 39 tests are layout and codec assertions with no threads in them, so they
buy nothing for the cost. The four above are the ones that actually spawn
threads or contend on a shared artifact. Naming them explicitly is the point:
the guard covers the concurrency protocols, and this file says so rather than
implying whole-crate coverage.

## Why each flag

| Flag | Reason |
|---|---|
| `-Zmiri-disable-isolation` | `region_engine` writes real files; the publication test is *about* the filesystem rename, so it cannot be stubbed. |
| `-Zmiri-ignore-leaks` | `mt_object_dies_on_last_dec` enables the ownership shadow, which **quarantines** freed memory instead of releasing it — deliberate, and exactly what Miri's leak checker reports. Without this flag the run fails on intentional retention. |

## Proof that it catches the real thing

Not asserted — executed. With the `dec_ref` mode probe reverted to the plain
`ptr::read` it had before commit `8cd1d3b`, on the pinned toolchain, against the
real crate:

```
error: Undefined Behavior: Data race detected between (1) non-atomic read on
thread `unnamed-2` and (2) atomic read-modify-write on thread `unnamed-3`
  --> crates/fln-unsafe-abi/src/rc.rs:167:13    (the reverted probe)
  --> crates/fln-unsafe-abi/src/rc.rs:147:18    (the atomic fetch_sub)
```

Restored, the same command passes. So this is a guard, not a green rubber stamp:
it fails on the defect it exists to prevent.

## What this does NOT cover

* **`fln-unsafe-region`** (the mmap primitive). Miri cannot execute `mmap`, and
  that crate is not in this domain. The region *engine* in fln-rt is covered
  because it is pure slice arithmetic; the *mapping* under it is not.
* **The exported C surface under a real C caller.** Miri runs Rust; the stage0
  ABI gauntlet is the instrument for that, not this.
* **TSAN.** It needs `-Zbuild-std` and therefore `rust-src` for the pin. That
  component is now installed, so TSAN is worth attempting as a second detector
  — Miri is stricter about the memory model but does not run the real allocator
  or real OS threads, and the two find different things.
* **Everything single-threaded.** This is a concurrency guard. It is not a
  substitute for the ordinary suite, which still runs natively.

## The recurring hazard, for whoever audits Marrow next

All three defects found in this crate so far are **the same shape**: the
single-threaded-to-multi-threaded ownership transition.

1. The ST refcount could overflow and *wrap into the MT encoding* — a positive
   count becoming negative silently reclassifies the object's threading
   discipline (fixed: `checked_add` that faults in every profile).
2. Every mode probe read `m_rc` non-atomically while MT threads did atomic RMWs
   on it — the read that *decides* which discipline applies was itself racing
   (fixed: `Relaxed` loads).
3. Region publication keyed its staging file per-process, so two threads
   publishing one target shared it — a transition from one writer to many with
   no per-writer identity (fixed: per-thread staging names).

The pattern: **wherever this crate decides "how many owners does this have", the
decision itself is unsynchronised.** Start there. The tri-state encoding is a
concurrency protocol wearing an integer's clothes, and a wrong answer does not
error — it silently reinterprets the object as a different kind.
