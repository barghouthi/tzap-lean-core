# tzap API

## Circuits

A `Circuit` holds a list of gates over a fixed number of qubits.

```rust
use tzap::circuit::{Circuit, Gate};

let mut circuit = Circuit::new(2);
circuit.apply(Gate::h(0));
circuit.apply(Gate::cnot { control: 0, target: 1 });
circuit.apply(Gate::t(0));
```

To use `measure` gates, allocate classical bits with
`Circuit::with_cbits(num_qubits, num_cbits)` instead of `Circuit::new`.

### Supported gates

| Gate | Constructor |
|------|------------|
| X | `Gate::x(qubit)` |
| H | `Gate::h(qubit)` |
| S | `Gate::s(qubit)` |
| Sdg | `Gate::sdg(qubit)` |
| Z | `Gate::z(qubit)` |
| T | `Gate::t(qubit)` |
| Tdg | `Gate::tdg(qubit)` |
| Rz | `Gate::rz(angle, qubit)` |
| CNOT | `Gate::cnot { control, target }` |
| CZ | `Gate::cz { control, target }` |
| Toffoli | `Gate::ccx { control1, control2, target }` |
| CCZ | `Gate::ccz { control1, control2, target }` |
| Measure | `Gate::measure { qubit, cbit }` |
| Reset | `Gate::reset(qubit)` |

### QASM I/O

Parse from and convert to OpenQASM 2.0. `from_qasm` returns
`Result<Circuit, String>`:

```rust
let circuit = Circuit::from_qasm("
    OPENQASM 2.0;
    include \"qelib1.inc\";
    qreg q[2];
    h q[0];
    cx q[0],q[1];
").expect("invalid QASM");

let qasm_string = circuit.to_qasm();
```

The QASM parser accepts `ccz` as a native circuit gate. `DecomposeToffoli`
lowers both `ccx` and `ccz` to Clifford+T.

## Passes

Every pass implements the `Pass` trait:

```rust
use tzap::pass::Pass;

pub trait Pass: Sync {
    fn name(&self) -> &str;
    fn run(&self, circuit: &Circuit) -> Circuit;
}
```

A custom pass only needs to supply `name` and `run`.

### Available passes

| Pass | Import | Description |
|------|--------|-------------|
| `DecomposeToffoli` | `tzap::decompose` | Breaks CCX and CCZ gates into Clifford+T |
| `DecomposeCz` | `tzap::decompose` | Explicitly lowers CZ gates to H+CX+H |
| `DecomposeRz` | `tzap::decompose_rz` | Decomposes Rz gates into Clifford+T via gridsynth |
| `CancelGates` | `tzap::cancel` | Removes adjacent self-inverse gate pairs (HH, XX, etc.) |
| `SuperOpt` | `tzap::super_opt` | Replaces small windows using its shared unitary-to-circuit table |
| `PhaseFoldRand` | `tzap::phase_fold_rand` | Merges T/Rz gates across the circuit via randomized parity tracking |
| `PhaseFoldGlobalExpr` | `tzap::phase_fold_global_expr` | Merges T/Rz gates via symbolic parity expressions |

### Running passes

Run a single pass:

```rust
use tzap::decompose::DecomposeToffoli;

let optimized = DecomposeToffoli.run(&circuit);
```

Run a pipeline:

```rust
use tzap::decompose::DecomposeToffoli;
use tzap::cancel::CancelGates;
use tzap::phase_fold_rand::PhaseFoldRand;
use tzap::pass::{Pass, PassResult, run_passes, count_t};

let passes: Vec<&dyn Pass> = vec![
    &DecomposeToffoli,
    &CancelGates,
    &PhaseFoldRand,
];

let result: PassResult = run_passes(&circuit, &passes);
println!("{} gates, {} T", result.circuit.gates.len(), count_t(&result.circuit));
```

`run_passes` returns a `PassResult`:

```rust
pub struct PassResult {
    pub circuit: Circuit,
    pub t_after_first: usize,       // T-count after only the first pass
    pub gates_after_first: usize,   // gate count after only the first pass
}
```

The `t_after_first` / `gates_after_first` fields are useful for
attributing reductions to the leading decomposition pass when reporting
end-to-end numbers. Helpers `count_t` and `count_rz` are also exposed
from `tzap::pass`.

### SuperOpt

`SuperOpt` is a peephole pass. It scans each maximal connected subcircuit window
and replaces it with the smallest equivalent circuit from a precomputed
unitary-to-circuit table, applying a rewrite only when it strictly reduces the
gate count. Every replacement is verified by matrix equality up to global phase
before use, so rewrites are always semantics-preserving. The pass accepts unitary
circuits only.

```rust
use tzap::super_opt::{SuperOpt, SuperOptTableConfig};

let pass = SuperOpt::new(3, 10, SuperOptTableConfig::default())?;
let result = pass.run(&circuit)?;
println!("{} rewrites", result.rewrites.len());
# Ok::<(), Box<dyn std::error::Error>>(())
```

Parameters:

- `max_qubits` — maximum distinct qubits in a scanned window.
- `window_gates` — maximum gates in a scanned window.
- `SuperOptTableConfig::new(max_qubits, max_gates, max_entries_per_qubit)` — bounds
  for the synthesis table, independent of the window size; `default()` is
  `(3, 8, 200_000)`. Tables are built on first use and shared for the life of the
  process.

`SuperOpt` also implements `tzap::pass::Pass`. Chain `.without_subcircuits()` when
only the optimized circuit is needed, to skip retaining per-window diagnostics.

### DecomposeRz epsilon

Control the approximation precision with the `epsilon` field (default `1e-10`):

```rust
use tzap::decompose_rz::DecomposeRz;

let pass = DecomposeRz { epsilon: 1e-6 };
let cliffordt = pass.run(&circuit);
```
