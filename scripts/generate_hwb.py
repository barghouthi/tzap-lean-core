#!/usr/bin/env python3
"""Generate OpenQASM circuits for the hidden weighted bit family.

For n input bits x_1..x_n, the hidden weighted bit function is

    HWB_n(x) = x_|x|

where |x| is the Hamming weight of x, and HWB_n(x) is 0 when |x| is 0.
The generated reversible circuit computes this as:

    out ^= HWB_n(input)

using clean work qubits that are restored to zero. The output uses only
OpenQASM 2.0 gates supported by tzap: x, cx, and ccx.
"""

from __future__ import annotations

import argparse
import itertools
import sys
from pathlib import Path
from typing import Iterable, TextIO


def qasm_x(out: TextIO, qubit: int) -> int:
    out.write(f"x q[{qubit}];\n")
    return 1


def qasm_cx(out: TextIO, control: int, target: int) -> int:
    out.write(f"cx q[{control}],q[{target}];\n")
    return 1


def qasm_ccx(out: TextIO, control1: int, control2: int, target: int) -> int:
    out.write(f"ccx q[{control1}],q[{control2}],q[{target}];\n")
    return 1


def emit_multi_controlled_x(
    out: TextIO,
    controls: list[int],
    target: int,
    work: list[int],
) -> int:
    """Emit an m-controlled X using clean work qubits, restoring work to zero."""
    if not controls:
        return qasm_x(out, target)
    if len(controls) == 1:
        return qasm_cx(out, controls[0], target)
    if len(controls) == 2:
        return qasm_ccx(out, controls[0], controls[1], target)

    needed = len(controls) - 2
    if len(work) < needed:
        raise ValueError(f"need {needed} work qubits for {len(controls)} controls")

    gates = 0
    gates += qasm_ccx(out, controls[0], controls[1], work[0])
    for index in range(2, len(controls) - 1):
        gates += qasm_ccx(out, controls[index], work[index - 2], work[index - 1])

    gates += qasm_ccx(out, controls[-1], work[needed - 1], target)

    for index in range(len(controls) - 2, 1, -1):
        gates += qasm_ccx(out, controls[index], work[index - 2], work[index - 1])
    gates += qasm_ccx(out, controls[0], controls[1], work[0])
    return gates


def hwb_terms(size: int) -> Iterable[tuple[int, ...]]:
    """Yield the positive-control sets that make HWB_size equal to one.

    Qubit indices are zero-based, while the HWB definition is one-based:
    when the Hamming weight is k, the function returns x_k.
    """
    inputs = range(size)
    for weight in range(1, size + 1):
        hidden_bit = weight - 1
        for subset in itertools.combinations(inputs, weight):
            if hidden_bit in subset:
                yield subset


def emit_hwb(out: TextIO, size: int) -> int:
    if size < 1:
        raise ValueError("size must be at least 1")

    output = size
    work = list(range(size + 1, size + 1 + max(0, size - 2)))
    num_qubits = size + 1 + len(work)
    inputs = list(range(size))
    input_set = set(inputs)
    gates = 0

    out.write("OPENQASM 2.0;\n")
    out.write('include "qelib1.inc";\n')
    out.write(f"qreg q[{num_qubits}];\n")
    out.write(f"// hwb{size}: q[0..{size - 1}] are inputs, q[{output}] is output")
    if work:
        out.write(f", q[{work[0]}..{work[-1]}] are clean work qubits")
    out.write(".\n")

    for positive_controls in hwb_terms(size):
        positive_set = set(positive_controls)
        negative_controls = sorted(input_set - positive_set)

        for qubit in negative_controls:
            gates += qasm_x(out, qubit)
        gates += emit_multi_controlled_x(out, inputs, output, work)
        for qubit in reversed(negative_controls):
            gates += qasm_x(out, qubit)

    return gates


def output_path(out_dir: Path, prefix: str, size: int) -> Path:
    return out_dir / f"{prefix}{size}.qasm"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate OpenQASM hidden weighted bit circuits.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("start", type=int, help="first HWB size to generate")
    parser.add_argument(
        "end",
        type=int,
        nargs="?",
        help="last HWB size to generate, inclusive; omit to generate one size",
    )
    parser.add_argument(
        "-o",
        "--out-dir",
        type=Path,
        default=Path("benchmarks/feynman"),
        help="directory for generated hwb<N>.qasm files",
    )
    parser.add_argument("--prefix", default="hwb", help="output filename prefix")
    parser.add_argument(
        "--force",
        action="store_true",
        help="overwrite existing output files",
    )
    parser.add_argument(
        "--stdout",
        action="store_true",
        help="write a single generated circuit to stdout instead of a file",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="print the files that would be generated without writing them",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    end = args.end if args.end is not None else args.start
    if args.start < 1 or end < 1:
        print("error: sizes must be at least 1", file=sys.stderr)
        return 2
    if end < args.start:
        print("error: end must be greater than or equal to start", file=sys.stderr)
        return 2

    sizes = list(range(args.start, end + 1))
    if args.stdout and len(sizes) != 1:
        print("error: --stdout can only be used with one size", file=sys.stderr)
        return 2
    if args.stdout and args.dry_run:
        print("error: --stdout and --dry-run cannot be combined", file=sys.stderr)
        return 2

    if args.stdout:
        emit_hwb(sys.stdout, sizes[0])
        return 0

    if not args.dry_run:
        args.out_dir.mkdir(parents=True, exist_ok=True)

    for size in sizes:
        path = output_path(args.out_dir, args.prefix, size)
        if args.dry_run:
            print(path)
            continue
        if path.exists() and not args.force:
            print(f"error: {path} already exists; pass --force to overwrite", file=sys.stderr)
            return 1

        mode = "w" if args.force else "x"
        with path.open(mode, encoding="utf-8") as out:
            gates = emit_hwb(out, size)
        print(f"wrote {path} ({size} inputs, {gates} gates)")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
