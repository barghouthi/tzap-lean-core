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
| `DecomposeToffoli` | `tzap::decompose` | Breaks Toffoli gates into CNOT+T/Tdg |
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

### SuperOpt window analysis

`SuperOptPass` makes one forward scan while maintaining one connected
component anchored at every gate. Unrelated gates are skipped, but shared
per-qubit history allows a later bridge to pull an entire previously disconnected
component into the window. A matrix is returned whenever that closed component
grows, from one gate through at most `window_gates` gates, while using at most
`max_qubits`. Components that grow past either bound are retired. With a synthesis
table attached, every matrix—including identity—is handled through the same lookup:
the empty circuit is naturally the table's smallest identity representative.
Overlapping rewrites are resolved greedily in forward completion order, so no input
gate is rewritten twice. The pass accepts unitary circuits only.

```rust
use tzap::super_opt::SuperOptPass;

let result = SuperOptPass::analyzer(3, 8).run(&circuit)?;
println!("removed {:?}", result.removed_subcircuits);
println!("optimized gate count {}", result.circuit.gates.len());
for subcircuit in result.subcircuits {
    println!(
        "gate indices {:?}, physical qubits {:?}, matrix dimension {}",
        subcircuit.gate_indices,
        subcircuit.qubits,
        subcircuit.matrix.dimension(),
    );
}
# Ok::<(), Box<dyn std::error::Error>>(())
```

`subcircuit.gate_indices` is chronological but need not be contiguous because
unrelated intervening gates are omitted. Closure is transitive: when
`H q0; H q1; X q1; CX q0,q1` is viewed from the first gate, the bridge pulls in
both gates on `q1`, producing the indivisible four-gate component rather than a
three-gate subset that omits `X q1`. The matrix uses the sorted order in
`subcircuit.qubits`; local qubit zero is the most significant basis-state bit.
Canonically identical completed components share an `Arc<UnitaryMatrix>`;
`cache_hits` and `cache_misses` report that reuse.

`SuperOptPass` also implements `tzap::pass::Pass`; through that interface,
`run` returns the optimized circuit directly.

Optimization-only callers should chain `.without_subcircuits()`: rewrites still
apply and `removed_subcircuits`, `rewrites`, and the cache statistics are still
reported, but the per-window `subcircuits` diagnostics are not retained. Large
circuits emit millions of windows, so skipping collection saves substantial
memory and time.

For general peephole synthesis, construct the optimizer backed by tzap's shared
unitary-to-circuit database. The constructor takes both window bounds and the
synthesis-table bounds; matching table configs are built on first use and cached
for the life of the process. Rewrites are applied only when they strictly reduce
the gate count.

```rust
use tzap::super_opt::{SuperOptPass, SuperOptTableConfig};

let pass = SuperOptPass::new(4, 8, SuperOptTableConfig::default())?
    .without_subcircuits();
let result = pass.run(&circuit)?;
println!("{} rewrites", result.rewrites.len());
# Ok::<(), Box<dyn std::error::Error>>(())
```

`SuperOptTableConfig::default()` currently enumerates up to four-qubit,
eight-gate library circuits with a one-million-entry cap per qubit width. Use
`SuperOptTableConfig::new(max_qubits, max_gates, max_entries_per_qubit)` to tune
that synthesis table independently from the scanned window size.

The database is generated dynamically rather than loaded from a file. Candidate
circuits are matrix-verified before any entry is used for a rewrite.

The enumerated library is `X`, `H`, `S`, `Sdg`, `Z`, `T`, `Tdg`, `CNOT`, `CZ`,
and `CCX`; arbitrary `Rz` gates are absent from the database, though an input
containing `Rz` can still match a library unitary. The one-million-entry database
contains about 2.7 million unitaries and takes about six seconds to build in a
release binary on the current benchmark machine. It fully enumerates through
depth eight for one and two qubits, depth four for three qubits, and depth three
for four qubits.

### DecomposeRz epsilon

Control the approximation precision with the `epsilon` field (default `1e-10`):

```rust
use tzap::decompose_rz::DecomposeRz;

let pass = DecomposeRz { epsilon: 1e-6 };
let cliffordt = pass.run(&circuit);
```
