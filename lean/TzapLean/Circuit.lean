import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Pi

/-!
# Circuit Syntax

A Lean transcription of the Rust circuit representation in `src/circuit.rs`, one
declaration per Rust item:

| Rust (`src/circuit.rs`) | Lean (this file) |
|---|---|
| `type Qubit = usize` | `Qubit := Nat` |
| `type CBit = usize` | `CBit := Nat` |
| `enum Gate` | `Gate` |
| `struct Circuit` | `Circuit` |
| `Circuit::new`, `Circuit::with_cbits`, `Circuit::apply` | `Circuit.new`, `Circuit.withCbits`, `Circuit.apply` |
| `Gate::map_qubits` | `Gate.mapQubits` |
| `qubit_operands`, `qubits_of` | `Gate.qubitOperands`, `Gate.qubitsOf` |
| `remap_gate`, `remap_subcircuit` | `remapGate`, `remapSubcircuit` |
| `impl Display` | `Repr`/`toString` instances |

Two deliberate departures from the Rust:

* **Rotation angles are rational multiples of `π`.** `Gate.rz θ q` denotes the Rust
  `Gate::rz(θ · π, q)`; the `f64` angle becomes `θ : ℚ`, so `t = rz (1/4)` and
  `z = rz 1` hold exactly rather than up to floating-point error. Every angle the
  optimizer actually manipulates (`π/4` multiples, and gridsynth output) is of this
  form.
* **Qubit indices are unbounded `Nat`s, as in Rust.** Well-formedness — every operand
  below `numQubits`, every classical bit below `numCbits` — is the separate predicate
  `Circuit.WellFormed`. `TzapLean/Semantics.lean` gives out-of-range operands the
  identity semantics, so every syntactic circuit denotes *something*, and
  well-formedness is only needed where it is genuinely used.
-/

namespace TzapLean

/-- Index of a qubit within a `Circuit`. As in Rust this is an unbounded index; see
`Circuit.WellFormed`. -/
abbrev Qubit := Nat

/-- Index of a classical bit within a `Circuit`. -/
abbrev CBit := Nat

/-- A single quantum (or classical `measure`/`reset`) operation.

Constructor names mirror the Rust `Gate` variants, which in turn mirror their QASM gate
names. `rz θ q` rotates by `θ · π` (see the module docstring). -/
inductive Gate where
  | x (q : Qubit)
  | h (q : Qubit)
  | s (q : Qubit)
  | sdg (q : Qubit)
  | z (q : Qubit)
  | t (q : Qubit)
  | tdg (q : Qubit)
  /-- `rz θ q` is the Rust `Gate::rz(θ * π, q)`: a `z`-rotation by `θ · π`. -/
  | rz (theta : ℚ) (q : Qubit)
  | cnot (control target : Qubit)
  | cz (control target : Qubit)
  | ccx (control₁ control₂ target : Qubit)
  | ccz (control₁ control₂ target : Qubit)
  | measure (qubit : Qubit) (cbit : CBit)
  | reset (q : Qubit)
  deriving DecidableEq, Repr, Inhabited

namespace Gate

/-- The qubits a gate acts on, in the order the Rust `qubits_of` reports them.
`measure` reports only its qubit; its classical bit is not a qubit. -/
def qubitsOf : Gate → List Qubit
  | .x q | .h q | .s q | .sdg q | .z q | .t q | .tdg q | .rz _ q | .reset q => [q]
  | .measure q _ => [q]
  | .cnot c tgt | .cz c tgt => [c, tgt]
  | .ccx c₁ c₂ tgt | .ccz c₁ c₂ tgt => [c₁, c₂, tgt]

/-- `(count, operands)` form of `qubitsOf`, mirroring the Rust `qubit_operands`, whose
point there is to avoid a heap allocation per gate. Kept for faithfulness; `qubitsOf` is
the form the proofs use. -/
def qubitOperands (g : Gate) : Nat × List Qubit :=
  (g.qubitsOf.length, g.qubitsOf)

/-- The classical bits a gate writes: `[c]` for `measure`, `[]` otherwise. -/
def cbitsOf : Gate → List CBit
  | .measure _ c => [c]
  | _ => []

/-- The same gate with every qubit operand sent through `f`. Classical bits are
untouched. Mirrors the Rust `Gate::map_qubits`. -/
def mapQubits (f : Qubit → Qubit) : Gate → Gate
  | .x q => .x (f q)
  | .h q => .h (f q)
  | .s q => .s (f q)
  | .sdg q => .sdg (f q)
  | .z q => .z (f q)
  | .t q => .t (f q)
  | .tdg q => .tdg (f q)
  | .rz θ q => .rz θ (f q)
  | .cnot c tgt => .cnot (f c) (f tgt)
  | .cz c tgt => .cz (f c) (f tgt)
  | .ccx c₁ c₂ tgt => .ccx (f c₁) (f c₂) (f tgt)
  | .ccz c₁ c₂ tgt => .ccz (f c₁) (f c₂) (f tgt)
  | .measure q c => .measure (f q) c
  | .reset q => .reset (f q)

/-- `true` for the three-qubit `ccx`, the flag the Rust `has_toffoli` tracks. -/
def isToffoli : Gate → Bool
  | .ccx .. => true
  | _ => false

/-- `true` for `ccz`, the flag the Rust `has_ccz` tracks. -/
def isCcz : Gate → Bool
  | .ccz .. => true
  | _ => false

/-- `true` for `measure` and `reset` — the non-unitary gates. The Rust `has_measurement`
flag tracks exactly this, `reset` included. -/
def isMeasurement : Gate → Bool
  | .measure .. | .reset _ => true
  | _ => false

/-- A gate denotes a unitary iff it is neither `measure` nor `reset`. -/
def isUnitary (g : Gate) : Bool := !g.isMeasurement

@[simp] theorem isUnitary_eq (g : Gate) : g.isUnitary = !g.isMeasurement := rfl

/-- One-line rendering, matching the Rust `Display` impl. -/
def toString : Gate → String
  | .x q => s!"x q{q}"
  | .h q => s!"h q{q}"
  | .s q => s!"s q{q}"
  | .sdg q => s!"sdg q{q}"
  | .z q => s!"z q{q}"
  | .t q => s!"t q{q}"
  | .tdg q => s!"tdg q{q}"
  | .rz θ q => s!"rz({θ}π) q{q}"
  | .cnot c tgt => s!"cnot q{c}, q{tgt}"
  | .cz c tgt => s!"cz q{c}, q{tgt}"
  | .ccx c₁ c₂ tgt => s!"ccx q{c₁}, q{c₂}, q{tgt}"
  | .ccz c₁ c₂ tgt => s!"ccz q{c₁}, q{c₂}, q{tgt}"
  | .measure q c => s!"measure q{q} -> c{c}"
  | .reset q => s!"reset q{q}"

instance : ToString Gate := ⟨Gate.toString⟩

end Gate

/-- An ordered sequence of `Gate`s over a fixed number of qubits and classical bits.

The `has*` flags are maintained by `Circuit.apply`, exactly as in Rust, where they let
passes cheaply skip circuits without a given gate kind. `apply_hasToffoli` and friends
below prove the flags agree with the corresponding scan over `gates`, so a proof may use
whichever form is convenient. -/
structure Circuit where
  numQubits : Nat
  numCbits : Nat := 0
  gates : List Gate := []
  hasToffoli : Bool := false
  hasCcz : Bool := false
  hasMeasurement : Bool := false
  deriving Repr, Inhabited

namespace Circuit

/-- An empty circuit over `numQubits` qubits and no classical bits. -/
def new (numQubits : Nat) : Circuit := { numQubits }

/-- An empty circuit over `numQubits` qubits and `numCbits` classical bits. Use this
instead of `new` when the circuit contains `measure` gates. -/
def withCbits (numQubits numCbits : Nat) : Circuit := { numQubits, numCbits }

/-- Append `gate`, updating the `has*` flags as needed. Gates accumulate at the end of
`gates`, so list order is execution order. -/
def apply (c : Circuit) (g : Gate) : Circuit :=
  { c with
    gates := c.gates ++ [g]
    hasToffoli := c.hasToffoli || g.isToffoli
    hasCcz := c.hasCcz || g.isCcz
    hasMeasurement := c.hasMeasurement || g.isMeasurement }

/-- Build a circuit by applying `gs` in order to the empty `n`-qubit, `m`-cbit circuit.

Written directly rather than as `gs.foldl Circuit.apply (withCbits n m)`, which is what it
means but not what it should cost: `apply` appends one gate with `c.gates ++ [g]`, so folding
it over `n` gates copies the list `n` times. Parsing gf2^32 spent 3.1 s of its 3.2 s here.
`ofGates_eq_foldl` records that the two agree. -/
def ofGates (n m : Nat) (gs : List Gate) : Circuit where
  numQubits := n
  numCbits := m
  gates := gs
  hasToffoli := gs.any Gate.isToffoli
  hasCcz := gs.any Gate.isCcz
  hasMeasurement := gs.any Gate.isMeasurement

/-- Number of gates. -/
def size (c : Circuit) : Nat := c.gates.length

/-- Every gate operand is in range: qubits below `numQubits`, classical bits below
`numCbits`. The Rust representation leaves this implicit; the semantics in
`TzapLean/Semantics.lean` needs it only to relate out-of-range operands to real ones. -/
def WellFormed (c : Circuit) : Prop :=
  ∀ g ∈ c.gates, (∀ q ∈ g.qubitsOf, q < c.numQubits) ∧ (∀ b ∈ g.cbitsOf, b < c.numCbits)

/-- Rendering, matching the Rust `Display` impl for `Circuit`. -/
def toString (c : Circuit) : String :=
  let header := s!"Circuit ({c.numQubits} qubits, {c.gates.length} gates):\n"
  let body := c.gates.zipIdx.foldl (fun acc (g, i) => acc ++ s!"  {i}: {g}\n") ""
  header ++ body

instance : ToString Circuit := ⟨Circuit.toString⟩

@[simp] theorem gates_new (n : Nat) : (new n).gates = [] := rfl
@[simp] theorem numCbits_new (n : Nat) : (new n).numCbits = 0 := rfl
@[simp] theorem gates_apply (c : Circuit) (g : Gate) :
    (c.apply g).gates = c.gates ++ [g] := rfl
@[simp] theorem numQubits_apply (c : Circuit) (g : Gate) :
    (c.apply g).numQubits = c.numQubits := rfl
@[simp] theorem numCbits_apply (c : Circuit) (g : Gate) :
    (c.apply g).numCbits = c.numCbits := rfl

/-- The `hasToffoli` flag of a circuit built by `apply` from a flagless start is exactly
"some gate is a `ccx`". -/
theorem hasToffoli_apply (c : Circuit) (g : Gate) :
    (c.apply g).hasToffoli = (c.hasToffoli || g.isToffoli) := rfl

theorem hasCcz_apply (c : Circuit) (g : Gate) :
    (c.apply g).hasCcz = (c.hasCcz || g.isCcz) := rfl

theorem hasMeasurement_apply (c : Circuit) (g : Gate) :
    (c.apply g).hasMeasurement = (c.hasMeasurement || g.isMeasurement) := rfl

/-- The flags maintained incrementally by `apply` agree with a scan of the gate list.
Stated for `ofGates`, i.e. for circuits built the way the Rust API builds them. -/
theorem flags_ofGates (n m : Nat) (gs : List Gate) :
    (ofGates n m gs).hasToffoli = gs.any Gate.isToffoli ∧
    (ofGates n m gs).hasCcz = gs.any Gate.isCcz ∧
    (ofGates n m gs).hasMeasurement = gs.any Gate.isMeasurement :=
  ⟨rfl, rfl, rfl⟩

/-- Gate list of `ofGates`: the gates, in order. -/
@[simp] theorem gates_ofGates (n m : Nat) (gs : List Gate) : (ofGates n m gs).gates = gs := rfl

@[simp] theorem numQubits_ofGates (n m : Nat) (gs : List Gate) :
    (ofGates n m gs).numQubits = n := rfl

@[simp] theorem numCbits_ofGates (n m : Nat) (gs : List Gate) :
    (ofGates n m gs).numCbits = m := rfl

/-- **Building directly is building by `apply`.** The efficient definition above denotes what
the Rust API's incremental construction denotes. -/
theorem ofGates_eq_foldl (n m : Nat) (gs : List Gate) :
    ofGates n m gs = gs.foldl Circuit.apply (withCbits n m) := by
  have key : ∀ (gs : List Gate) (c : Circuit),
      gs.foldl Circuit.apply c =
        { numQubits := c.numQubits, numCbits := c.numCbits, gates := c.gates ++ gs,
          hasToffoli := c.hasToffoli || gs.any Gate.isToffoli,
          hasCcz := c.hasCcz || gs.any Gate.isCcz,
          hasMeasurement := c.hasMeasurement || gs.any Gate.isMeasurement } := by
    intro gs
    induction gs with
    | nil => intro c; simp
    | cons g gs ih =>
        intro c
        rw [List.foldl_cons, ih]
        simp [Circuit.apply, List.any_cons, Bool.or_assoc]
  rw [key gs (withCbits n m)]
  simp [ofGates, withCbits]

end Circuit

/-- Remap a gate's qubits through a lookup table: qubit `i` becomes its index in `qubits`
(and is left alone if absent, where Rust would panic). Classical bits are not remapped. -/
def remapGate (g : Gate) (qubits : List Qubit) : Gate :=
  g.mapQubits fun q => (qubits.idxOf q)

/-- Build a compact circuit with qubits remapped to `0 .. qubits.length - 1`. -/
def remapSubcircuit (gs : List Gate) (qubits : List Qubit) : Circuit :=
  Circuit.ofGates qubits.length 0 (gs.map (remapGate · qubits))

end TzapLean
