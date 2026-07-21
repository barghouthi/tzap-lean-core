# /// script
# requires-python = ">=3.10"
# dependencies = ["mqt.qcec>=3"]
# ///
"""Verify tzap -O3 and -Osuper output against original circuits with MQT QCEC.

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
OPTIMIZATION_LEVELS = ("-O3", "-Osuper")


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
            for level in OPTIMIZATION_LEVELS:
                optimized = Path(tmp) / f"{level[1:]}_{original.name}"
                proc = subprocess.run(
                    [tzap, level, str(original), "-o", str(optimized)],
                    capture_output=True,
                    text=True,
                )
                label = f"{original.name} ({level})"
                if proc.returncode != 0:
                    print(f"FAIL {label}: tzap exited {proc.returncode}")
                    print(proc.stderr, file=sys.stderr)
                    failures.append(label)
                    continue

                result = qcec.verify(str(original), str(optimized))
                verdict = result.equivalence
                status = "PASS" if verdict in ACCEPTED else "FAIL"
                print(f"{status} {label}: {verdict}", flush=True)
                if verdict not in ACCEPTED:
                    failures.append(label)

        negative_control(tzap, files[0], Path(tmp))

    checks = len(files) * len(OPTIMIZATION_LEVELS)
    if failures:
        sys.exit(f"{len(failures)}/{checks} circuits failed QCEC: {failures}")
    print(f"all {checks} optimized circuits verified equivalent")


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
