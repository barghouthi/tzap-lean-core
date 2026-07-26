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

You can use tzap as a command-line utility or a library.

### Install the binary

These options install the standalone native `tzap` executable.

**Homebrew** (macOS/Linux):

```bash
brew install qqq-wisc/tap/tzap
```

**Prebuilt release binary** (macOS/Linux):

```bash
curl -LsSf https://github.com/qqq-wisc/tzap/releases/latest/download/tzap-opt-installer.sh | sh
```

**Build and install from crates.io** (requires [Rust](https://rustup.rs/)):

```bash
cargo install tzap-opt
```

**Build from source** (requires Rust):

```bash
cargo install --path .
```

### Install a library

**Python library** (prebuilt wheels; no Rust compiler required):

```bash
pip install tzap  # uv pip install tzap
```

The Python package requires Python 3.10 or later and includes both the Qiskit
and PennyLane integrations. See the
[Qiskit API guide](docs/qiskit.md) or
[PennyLane API guide](docs/pennylane.md) for framework-specific setup.

**Rust library**:

```bash
cargo add tzap-opt
```

The package is named `tzap-opt` on crates.io, but is imported as `tzap` in
Rust code. See the [Rust API documentation](API.md).

## Running tzap

The standard command-line workflow is described below.

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

**Qiskit**

After `pip install tzap`, add tzap to a Qiskit pass manager:

```python
from qiskit import QuantumCircuit
from qiskit.transpiler import PassManager
from tzap.qiskit import TZapPass

circuit = QuantumCircuit(2)
circuit.h(0)
circuit.cx(0, 1)
circuit.t(1)

optimized = PassManager([
    TZapPass(level="O3"),
]).run(circuit)
```

See the [Qiskit API guide](docs/qiskit.md) for the convenience function,
supported basis, pass options, circuit-preservation guarantees, and errors.

**PennyLane**

```python
import pennylane as qml
from tzap.pennylane import optimize

device = qml.device("default.qubit", wires=2)

@optimize(level="O3")
@qml.qnode(device)
def circuit():
    qml.Hadamard(0)
    qml.Hadamard(0)
    qml.T(1)
    qml.T(1)
    return qml.probs(wires=[0, 1])

print(qml.draw(circuit)())
```

See the [PennyLane API guide](docs/pennylane.md) for QNode,
quantum-function, and tape usage, supported operations, differentiation
constraints, and errors.

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
