# ⚡️ tzap

[![CI](https://github.com/qqq-wisc/tzap/actions/workflows/ci.yml/badge.svg)](https://github.com/qqq-wisc/tzap/actions/workflows/ci.yml)
![Rust](https://img.shields.io/badge/Rust-000000?logo=rust&logoColor=white)
![Lean 4](https://img.shields.io/badge/Lean_4-black?logo=lean&logoColor=white)
![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-blue)
[![arXiv](https://img.shields.io/badge/arXiv-2605.13929-b31b1b.svg)](https://arxiv.org/abs/2605.13929)

A super fast, Rust-based optimizer for large Clifford+T circuits.
- tzap minimizes T-count with a novel phase folding technique that is O(n) in circuit size, based on [this paper](https://arxiv.org/abs/2605.13929).
- tzap also implements standard optimizations for gate cancellation.
- The core randomized phase folding algorithm is fully formalized in Lean under [`formalization`](formalization/).

tzap is **multiple orders of mangitude** faster than other optimizers---and way more scalable!
<img src="assets/comparison.png"
     alt="Runtime comparison of tzap, VOQC, Feynman, and QuiZX on GF multipliers"
     style="width: 100%; height: auto;">

## Usage

CLI usage or API usage (see [API.md](API.md)).

```bash
tzap input.qasm                           # optimize, print stats only
tzap input.qasm -o output.qasm            # write optimized circuit to file
tzap input.qasm -o output.qasm --decompose-rz              # decompose Rz via gridsynth (epsilon=1e-10)
tzap input.qasm -o output.qasm --decompose-rz --epsilon 1e-6  # coarser approximation
tzap input.qasm -o output.qasm --passes CancelGates,PhaseFoldRand  # explicit pass pipeline
```

Output is written only when an output file is given (via `-o`).

**Gate handling:** Toffoli (`ccx`) gates are automatically decomposed into Clifford+T before optimization. Controlled-Z (`cz`) gates remain native so phase folding and cancellation can operate through them; use `--passes DecomposeCz` when a backend requires `H`+`CX` output. `Rz` gates are left as-is by default; pass `--decompose-rz` to decompose them into Clifford+T via [gridsynth](https://crates.io/crates/rsgridsynth), and `--epsilon <eps>` to control the approximation precision (default: `1e-10`; accepts scientific notation).

### Example

```bash
$ tzap benchmarks/feynman/barenco_tof_5.qasm

⚡️ tzap
  Parsing benchmarks/feynman/barenco_tof_5.qasm (0.0 MB)
	└─ 9 qubits · 218 gates · 84 T/Tdg · 0.000s

  Gate cancellation
	└─ 170 gates · 84 T · 0.000s
  Phase folding
	└─ 146 gates · 40 T · 0.000s

  ⚡️ Result
	├─ Gates  218 → 146 (↓33.0%)
	├─ T/Tdg  84 → 40 (↓52.4%)
	└─ Time   0.000s
```

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
