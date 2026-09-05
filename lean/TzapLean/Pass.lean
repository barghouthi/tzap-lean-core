import TzapLean.Equivalence

/-!
# Passes

The Rust `Pass` trait is a name and a `Circuit → Circuit` function:

```rust
pub trait Pass {
    fn name(&self) -> &str;
    fn run(&self, circuit: &Circuit) -> Circuit;
}
```

with "returns an equivalent one" a comment. Here a pass has both the raw executable function
used by the CLI and a certified action on `Circuit.Checked n m`, whose indices fix the register
sizes and whose value carries the `Wf` precondition.  An unverified transformation is not a
`Pass`, so composition does not need separate preservation obligations.
-/

namespace TzapLean

noncomputable section

/-- An optimization pass: a circuit transformation carrying its own correctness proof. -/
structure Pass where
  /-- The pass's name, as in the Rust trait. -/
  name : String
  /-- The transformation. -/
  run : Circuit → Circuit
  /-- The same transformation on a validated, size-indexed circuit. -/
  certified : ∀ {n m}, Circuit.Checked n m → Circuit.Checked n m
  /-- The certified action is the raw executable function on the underlying circuit. -/
  certified_run : ∀ {n m} (c : Circuit.Checked n m), (certified c).raw = run c.raw
  /-- **The correctness obligation**: the output denotes the same channel as the input. -/
  correct : ∀ {n m} (c : Circuit.Checked n m),
    Equivalent n m (certified c).raw.gates c.raw.gates

namespace Pass

/-- Running one pass after another. -/
def comp (p q : Pass) : Pass where
  name := q.name ++ " ∘ " ++ p.name
  run := q.run ∘ p.run
  certified := fun c => q.certified (p.certified c)
  certified_run c := by simp [q.certified_run, p.certified_run]
  correct c := Equivalent.trans (q.correct (p.certified c)) (p.correct c)

/-- Run a list of passes in order, as the Rust `run_passes` does. -/
def runAll : List Pass → Circuit → Circuit
  | [], c => c
  | p :: ps, c => runAll ps (p.run c)

/-- **Composed correctness**: any pipeline of passes preserves the semantics. -/
theorem correct_runAll (ps : List Pass) (c : Circuit) (hc : c.Wf) :
    Equivalent c.numQubits c.numCbits (runAll ps c).gates c.gates := by
  induction ps generalizing c with
  | nil => exact Equivalent.refl _ _ _
  | cons p ps ih =>
      let checked := Circuit.Checked.of c hc
      let out := p.certified checked
      have hraw : out.raw = p.run c := p.certified_run checked
      have houtwf : (p.run c).Wf := by simpa [← hraw] using out.wf
      have hn : (p.run c).numQubits = c.numQubits := by
        calc
          (p.run c).numQubits = out.raw.numQubits := congrArg Circuit.numQubits hraw.symm
          _ = c.numQubits := out.numQubits_eq
      have hm : (p.run c).numCbits = c.numCbits := by
        calc
          (p.run c).numCbits = out.raw.numCbits := congrArg Circuit.numCbits hraw.symm
          _ = c.numCbits := out.numCbits_eq
      have h₁ : Equivalent c.numQubits c.numCbits (p.run c).gates c.gates := by
        rw [← hraw]
        have hp := p.correct checked
        change Equivalent c.numQubits c.numCbits out.raw.gates checked.raw.gates at hp
        simpa [checked, Circuit.Checked.of] using hp
      have h₂ := ih (p.run c) houtwf
      rw [hn, hm] at h₂
      exact Equivalent.trans h₂ h₁

end Pass

/-! ## Circuit statistics (the Rust `pass.rs` helpers) -/

/-- Number of `t`/`tdg` gates. -/
def countT (c : Circuit) : Nat :=
  c.gates.countP fun g => match g with | .t _ | .tdg _ => true | _ => false

/-- Number of `rz` gates. -/
def countRz (c : Circuit) : Nat :=
  c.gates.countP fun g => match g with | .rz _ _ => true | _ => false

/-- Number of two-qubit `cnot`/`cz` gates. -/
def count2q (c : Circuit) : Nat :=
  c.gates.countP fun g => match g with | .cnot .. | .cz .. => true | _ => false

/-- Per-wire next-free layer after scheduling `gs`, greedily as early as possible. -/
def depthAux : (Qubit → Nat) → List Gate → (Qubit → Nat)
  | next, [] => next
  | next, g :: gs =>
      let layer := (g.qubitsOf.map next).foldl max 0 + 1
      depthAux (fun q => if g.qubitsOf.contains q then layer else next q) gs

/-- Circuit depth: gates on disjoint qubits share a layer. -/
def depth (c : Circuit) : Nat :=
  ((List.range c.numQubits).map (depthAux (fun _ => 0) c.gates)).foldl max 0

end
end TzapLean
