# ⚡️ tzap

[![CI](https://github.com/qqq-wisc/tzap/actions/workflows/ci.yml/badge.svg)](https://github.com/qqq-wisc/tzap/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/tzap-opt.svg)](https://crates.io/crates/tzap-opt)
![Rust](https://img.shields.io/badge/Rust-000000?logo=rust&logoColor=white)
![Lean 4](https://img.shields.io/badge/Lean_4-black?logo=lean&logoColor=white)
![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-blue)
[![arXiv](https://img.shields.io/badge/arXiv-2605.13929-b31b1b.svg)](https://arxiv.org/abs/2605.13929)

A super fast, Rust-based optimizer for large Clifford+T circuits.
- tzap's **philosophy** is that each optimization pass should be **linear** in circuit size.
- tzap **minimizes T-count** with a new linear-time phase folding algorithm, based on [this paper](https://arxiv.org/abs/2605.13929).
- tzap implements a new and fast **superoptimization** pass.
- The core optimization algorithms are **fully formalized in Lean** under [`formalization`](formalization/).

tzap is **multiple orders of magnitude** faster than other optimizers&mdash;and **linearly** **scales** to **millions** of gates!
<img src="assets/comparison.png"
     alt="Runtime comparison of tzap, VOQC, and QuiZX on GF multipliers"
     style="width: 100%; height: auto;">

## Installation

**Homebrew** (macOS/Linux, easiest option):

```bash
brew install qqq-wisc/tap/tzap
```

**crates.io** (requires [Rust](https://rustup.rs/); builds from source):

```bash
cargo install tzap-opt
```

**pip** (no Rust required, downloads a prebuilt binary):

```bash
pip install tzap  # uv pip install tzap
```

Install the optional Qiskit integration with:

```bash
pip install "tzap[qiskit]"
```

**From source** (this repo, requires [Rust](https://rustup.rs/)):

```bash
cargo install --path .
```

**Prebuilt binary** (no Rust required, downloads and runs a shell installer) — macOS/Linux:

```bash
curl -LsSf https://github.com/qqq-wisc/tzap/releases/latest/download/tzap-opt-installer.sh | sh
```

## Usage

tzap is a command line utility. It also works as a Python or Rust library; see
the [Rust API documentation](API.md) for the latter.

**Optimize a circuit**

```bash
tzap input.qasm -o output.qasm
```

For example, using a benchmark in this repo:

```console
$ tzap benchmarks/feynman/hwb12.qasm -o optimized.qasm
⚡️ tzap v0.4.3
  Parsed benchmarks/feynman/hwb12.qasm (5.5 MB) in 0.098s
	└─ 20 qubits · 514,412 gates
  Loaded superoptimizer table in 0.018s

  Converged after 6 rounds

  ┌─ Final result · 43.7% fewer gates · 2.169s ──────────────────────────┐
  │ Gates    ━━━━━━━━━━━━━╸────────────────── ↓43.7% · 514,412 → 289,484 │
  │ 2q gates ━━━━━╸────────────────────────── ↓18.7% · 191,803 → 155,914 │
  │ T/Tdg    ━━━━━━━━━━━━━━━╸──────────────── ↓49.9% · 171,465 →  85,897 │
  │ Depth    ━━━━━━━╸──────────────────────── ↓24.3% · 274,781 → 207,940 │
  └──────────────────────────────────────────────────────────────────────┘
  wrote optimized.qasm
```

**Optimization levels**

| Level | Description |
|---|---|
| `-O1` | Randomized phase folding + basic gate cancellation. Fastest; already captures most of the T-gate reduction. |
| `-O2` | Adds superoptimization to `-O1`. |
| `-O3` | Repeats `-O2` until reaching a fixpoint. **Default.** |
| `-Osuper` | Like `-O3`, but with more superoptimization power (slower on first use). |

```bash
tzap benchmarks/feynman/hwb12.qasm -O1 -o optimized.qasm
```

**Python bindings**

`optimize_qasm` runs the same native Rust optimizer as the CLI and returns both
the optimized OpenQASM 2 program and its metrics:

```python
from tzap import optimize_qasm

with open("input.qasm") as source:
    result = optimize_qasm(source.read(), level="O3")

print(result.qasm)
print(result.report.baseline.gates, "->", result.report.output.gates)
```

The optimizer releases Python's GIL while it runs. All CLI optimization
options are available as keyword arguments, including `passes`,
`decompose_rz`, `decompose_cz`, `rz_epsilon`, and `parallel`.

**Qiskit transpiler pass**

Install `tzap[qiskit]`, then add `TzapOptimizationPass` to any Qiskit pass
manager:

```python
from qiskit import QuantumCircuit
from qiskit.transpiler import PassManager
from tzap.qiskit import TzapOptimizationPass

circuit = QuantumCircuit(2)
circuit.h(0)
circuit.cx(0, 1)
circuit.t(1)

optimized = PassManager([
    TzapOptimizationPass(level="O3"),
]).run(circuit)
```

There is also a short `TZapPass` alias and a convenience function:

```python
from tzap.qiskit import optimize

optimized = optimize(circuit, level="O1")
```

The Qiskit circuit must first be translated to tzap's supported basis shown
below. Bound numeric `rz` angles, measurements, and resets are supported;
control-flow operations, classical conditions, symbolic parameters, and
unsupported gates raise a `TranspilerError`. The pass retains the circuit's
registers, bit identities, name, metadata, and existing global phase.

**Decompose Rz into Clifford+T**

Use `--decompose-rz` when the target backend only accepts Clifford+T; tzap uses [gridsynth](https://crates.io/crates/rsgridsynth). `--epsilon` trades approximation accuracy for circuit size (default `1e-10`; larger is coarser).

```bash
tzap input.qasm -o output.qasm --decompose-rz --epsilon 1e-6
```

Use `--decompose-cz` to decompose CZ gates into `H`+`CX`+`H` before the
optimization pipeline.

**Custom pipeline**

`--passes` runs an explicit, ordered sequence of passes in place of the default pipeline.

```bash
tzap input.qasm -o output.qasm --passes CancelGates,PhaseFoldRand
tzap input.qasm -o output.qasm --passes DecomposeCz,CancelGates,PhaseFoldRand
```

## Circuit support

tzap supports a subset of OpenQASM 2.0:

- **Gates:** `h`, `x`, `z`, `s`, `sdg`, `t`, `tdg`, `rz`, `cx`, `ccx`, `ccz`, `cz`, `measure`, `reset`
- **Declarations:** `qreg`, `creg`
- **Not supported:** classical conditionals (`if`), custom gate definitions (`gate`), barriers, `include` files (besides `qelib1.inc`, which is ignored)
- Unrecognized lines produce an error

Toffoli (`ccx`) and doubly controlled-Z (`ccz`) are auto-decomposed into Clifford+T. Controlled-Z (`cz`) is kept native so phase folding and cancellation can operate through it; use `--decompose-cz` for `H`+`CX` output. `Rz` is left as-is unless you pass `--decompose-rz`.

## Correctness

1. **Fuzzing and equivalence verification** on small random circuits and benchmark circuits.
2. **Lean formalization:** core algorithms are implemented and proven sound in Lean 4 — see [`formalization`](formalization/).

## Citation

If you use tzap in your research, please cite:

```bibtex
@misc{albarghouthi2026tzap,
      title={Linear-Time T-Gate Optimization via Random Abstraction}, 
      author={Aws Albarghouthi},
      year={2026},
      eprint={2605.13929},
      archivePrefix={arXiv},
      primaryClass={cs.PL},
      url={https://arxiv.org/abs/2605.13929}, 
}
```
