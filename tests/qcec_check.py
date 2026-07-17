# /// script
# requires-python = ">=3.10"
# dependencies = ["mqt.qcec>=3"]
# ///
"""Verify tzap -O3 output against the original circuits with MQT QCEC.

Usage: uv run tests/qcec_check.py <tzap-binary> <benchmark-dir> [count]

Optimizes the `count` smallest (by file size) .qasm files in the benchmark
directory and checks each optimized circuit against its original with QCEC.
tzap rewrites preserve unitaries only up to global phase, so both
`equivalent` and `equivalent_up_to_global_phase` verdicts pass. Exits
non-zero if any circuit fails to verify.
"""

import subprocess
import sys
import tempfile
from pathlib import Path

from mqt import qcec
from mqt.qcec.pyqcec import EquivalenceCriterion

ACCEPTED = (
    EquivalenceCriterion.equivalent,
    EquivalenceCriterion.equivalent_up_to_global_phase,
)


def main() -> None:
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    tzap = sys.argv[1]
    bench_dir = Path(sys.argv[2])
    count = int(sys.argv[3]) if len(sys.argv) > 3 else 30

    files = sorted(bench_dir.glob("*.qasm"), key=lambda p: p.stat().st_size)
    files = files[:count]
    if not files:
        sys.exit(f"no .qasm files found in {bench_dir}")

    failures = []
    with tempfile.TemporaryDirectory() as tmp:
        for original in files:
            optimized = Path(tmp) / original.name
            proc = subprocess.run(
                [tzap, "-O3", str(original), "-o", str(optimized)],
                capture_output=True,
                text=True,
            )
            if proc.returncode != 0:
                print(f"FAIL {original.name}: tzap exited {proc.returncode}")
                print(proc.stderr, file=sys.stderr)
                failures.append(original.name)
                continue

            result = qcec.verify(str(original), str(optimized))
            verdict = result.equivalence
            status = "PASS" if verdict in ACCEPTED else "FAIL"
            print(f"{status} {original.name}: {verdict}", flush=True)
            if verdict not in ACCEPTED:
                failures.append(original.name)

        negative_control(tzap, files[0], Path(tmp))

    if failures:
        sys.exit(f"{len(failures)}/{len(files)} circuits failed QCEC: {failures}")
    print(f"all {len(files)} circuits verified equivalent")


def negative_control(tzap: str, original: Path, tmp: Path) -> None:
    """Guard against a vacuously-passing checker: an optimized circuit with
    one extra X gate must be reported as NOT equivalent."""
    tampered = tmp / f"tampered_{original.name}"
    subprocess.run(
        [tzap, "-O3", str(original), "-o", str(tampered)],
        capture_output=True,
        check=True,
    )
    with tampered.open("a") as f:
        f.write("x q[0];\n")
    verdict = qcec.verify(str(original), str(tampered)).equivalence
    if verdict in ACCEPTED:
        sys.exit(f"negative control FAILED: extra X reported as {verdict}")
    print(f"PASS negative control ({original.name} + extra X): {verdict}")


if __name__ == "__main__":
    main()
