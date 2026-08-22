//! End-to-end equivalence checks of every optimization level against MQT QCEC
//! (https://github.com/munich-quantum-toolkit/qcec).
//!
//! Ignored by default: it shells out to `uv`, which fetches mqt.qcec on
//! first use. Run with:
//!
//!     cargo test --release --test qcec -- --ignored --nocapture

use std::process::Command;

#[test]
#[ignore = "requires uv (and network on first run)"]
fn optimized_circuits_verify_against_qcec() {
    let script = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/qcec_check.py");
    let benchmarks = concat!(env!("CARGO_MANIFEST_DIR"), "/benchmarks/feynman");

    // Smallest 23 by file size. The full suite verifies too, but QCEC's
    // decision diagrams blow up on the larger circuits (gf2^7 already takes
    // ~3min in CI, gf2^8+ effectively hangs), so keep the default run small;
    // pass a larger count manually to widen coverage.
    //
    // The count is a rank, so it moves whenever a benchmark file is added or
    // removed: dropping the two smallest (1dcddcf) slid the window up to
    // include qcla_mod_7, which took over four hours to verify on its own and
    // pushed a passing CI job to 4h14m. Raise this only after timing what it
    // pulls in.
    let status = Command::new("uv")
        .args(["run", script, env!("CARGO_BIN_EXE_tzap"), benchmarks, "23"])
        .status()
        .expect("failed to launch `uv` — install it from https://docs.astral.sh/uv/");

    assert!(
        status.success(),
        "QCEC found a non-equivalent optimized circuit"
    );
}
