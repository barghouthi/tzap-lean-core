# ⚡️ tzap

[![CI](https://github.com/qqq-wisc/tzap/actions/workflows/ci.yml/badge.svg)](https://github.com/qqq-wisc/tzap/actions/workflows/ci.yml)
![Rust](https://img.shields.io/badge/Rust-000000?logo=rust&logoColor=white)
![Lean 4](https://img.shields.io/badge/Lean_4-black?logo=lean&logoColor=white)
![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-blue)
[![arXiv](https://img.shields.io/badge/arXiv-2605.13929-b31b1b.svg)](https://arxiv.org/abs/2605.13929)

A super fast, Rust-based optimizer for large Clifford+T circuits.
- tzap's **philosophy** is that each optimization pass should be **linear** in circuit size.
- tzap **minimizes T-count** with a new linear-time phase folding algorithm, based on [this paper](https://arxiv.org/abs/2605.13929).
- tzap also implements standard optimizations for gate cancellation.
- The core randomized phase folding algorithm is **fully formalized in Lean** under [`formalization`](formalization/).

tzap is **multiple orders of mangitude** faster than other optimizers&mdash;and **linearly** **scales** to **millions** of gates!
<img src="assets/comparison.png"
     alt="Runtime comparison of tzap, VOQC, and QuiZX on GF multipliers"
     style="width: 100%; height: auto;">

## CLI Usage

tzap is a CLI optimization tool for quantum circuits. You can also use tzap as a Rust library; see the [Rust API documentation](API.md).

**Optimize a circuit and inspect the results**

The most common usage of tzap is `tzap input.qasm -o output.qasm`, where the `input.qasm` circuit is optimized into `output.qasm`. For example, using the benchmarks in this repo:

```bash
tzap benchmarks/feynman/barenco_tof_5.qasm -o optimized.qasm
```

The default optimization is fast and lightweight. To run the most powerful optimization pass, use `--max`:

```bash
tzap --max benchmarks/feynman/barenco_tof_5.qasm -o optimized.qasm
```

tzap output:

```text
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

**Decompose Rz gates into Clifford+T and choose the precision**

Use `--decompose-rz` when the target backend accepts only Clifford+T gates. tzap decomposes `Rz` gates with [gridsynth](https://crates.io/crates/rsgridsynth). Use `--epsilon` to trade approximation accuracy for a potentially smaller circuit; a larger epsilon permits a coarser approximation. If you omit `--epsilon`, tzap uses `1e-10`.

```bash
tzap input.qasm -o output.qasm --decompose-rz --epsilon 1e-6  # omit --epsilon to use 1e-10
```

**Run a custom optimization pipeline**

tzap allows you to run a custom sequence of optimization passes with `--passes`. Use it when you need explicit control over which passes run and their order. The listed passes replace the default pipeline.

```bash
tzap input.qasm -o output.qasm --passes CancelGates,PhaseFoldRand
```

**Run maximum optimization**

Use `--max` to repeat `CancelGates`, `SuperOpt`, and `PhaseFoldRand` until the gate count reaches a fixpoint. When combined with `--decompose-rz`, Rz decomposition runs once after the first optimization iteration, and optimization then continues to a fixpoint. `--max` cannot be combined with `--passes` or `--fixpoint`.

```bash
tzap --max input.qasm -o output.qasm
tzap --max input.qasm -o output.qasm --decompose-rz --epsilon 1e-6
```

## Circuit support

tzap supports a subset of OpenQASM 2.0:

- **Supported gates:** `h`, `x`, `z`, `s`, `sdg`, `t`, `tdg`, `rz`, `cx`, `ccx`, `cz`, `measure`, `reset`
- **Supported declarations:** `qreg`, `creg`
- **Not supported:** classical conditionals (`if`), custom gate definitions (`gate`), barriers, and `include` files (besides `qelib1.inc`, which is ignored)
- Unrecognized lines will produce an error

**Gate handling**: Toffoli (`ccx`) gates are automatically decomposed into Clifford+T before optimization. Controlled-Z (`cz`) gates remain native so phase folding and cancellation can operate through them; use `--passes DecomposeCz` when a backend requires `H`+`CX` output. `Rz` gates are left as-is unless you pass `--decompose-rz`.

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
