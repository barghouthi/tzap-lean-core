# ⚡️ tzap

[![CI](https://github.com/qqq-wisc/tzap/actions/workflows/ci.yml/badge.svg)](https://github.com/qqq-wisc/tzap/actions/workflows/ci.yml)
![Rust](https://img.shields.io/badge/Rust-000000?logo=rust&logoColor=white)
![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-blue)
[![arXiv](https://img.shields.io/badge/arXiv-2605.13929-b31b1b.svg)](https://arxiv.org/abs/2605.13929)

A fast, Rust-based T-gate optimizer for large Clifford+T circuits. tzap (pronounced *T-zap*) applies phase folding that is O(n) in the number of gates, based on [this paper](https://arxiv.org/abs/2605.13929).

It takes OpenQASM 2.0 circuits as input, optimizes them, and outputs optimized OpenQASM 2.0.

**Gate handling:**

- **Toffoli (`ccx`)** gates are automatically decomposed into Clifford+T before optimization.
- **Rz** gates are left as-is by default. Pass `--decompose-rz` to decompose them into Clifford+T via [gridsynth](https://crates.io/crates/rsgridsynth). Use `--epsilon <eps>` to control the approximation precision (default: `1e-10`; accepts scientific notation).

## Usage

CLI usage or API usage (see [API.md](API.md)).

```bash
tzap input.qasm                           # optimize, print stats only
tzap input.qasm -o output.qasm            # write optimized circuit to file
tzap input.qasm -o output.qasm --decompose-rz              # decompose Rz via gridsynth (epsilon=1e-10)
tzap input.qasm -o output.qasm --decompose-rz --epsilon 1e-6  # coarser approximation
```

Output is only written when `-o` is given.

### Example

```bash
$ tzap benchmarks/feynman/barenco_tof_5.qasm

⚡️ tzap
  Parsing benchmarks/feynman/barenco_tof_5.qasm (0.0 MB)
	└─ 9 qubits · 218 gates · 84 T/Tdg · 0.000s

  Pair cancellation
	└─ 170 gates · 84 T · 0.000s
  Phase folding
	└─ 146 gates · 40 T · 0.000s

  ⚡️ Result
	├─ Gates  218 → 146 (↓33.0%)
	├─ T/Tdg  84 → 40 (↓52.4%)
	└─ Time   0.000s
```

## Benchmarks

The chart below shows runtimes on a standard suite of GF(2^k) multiplier circuits of increasing size, from 112 T-gates (k=4) up to ~115K T-gates (k=128). These are a common benchmark family in the T-gate optimization literature.

![tzap vs quizx runtime](assets/comparison.png)

tzap matches the T-gate reduction of [quizx](https://github.com/zxcalc/quizx) (the Rust port of PyZX) on every circuit, while running **orders of magnitude faster** — up to **92,000× faster** on the largest circuits. quizx times out (2hrs) entirely on the k=128 circuit where tzap finishes in 56 ms.

## Limitations

tzap supports a subset of OpenQASM 2.0:

- **Supported gates:** `h`, `x`, `z`, `s`, `sdg`, `t`, `tdg`, `rz`, `cx`, `ccx`, `cz`, `measure`, `reset`
- **Supported declarations:** `qreg`, `creg`
- **Not supported:** classical conditionals (`if`), custom gate definitions (`gate`), barriers, and `include` files (besides `qelib1.inc`, which is ignored)
- Unrecognized lines will produce an error

## Building
Install [Rust](https://github.com/qqq-wisc/tzap.git) then

```
cargo install --path .
```

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
