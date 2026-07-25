import TZap.Cyclotomic.Basic
import TZap.Semantics
import TZap.Unitary

/-!
# Clifford+T Amplitudes Are Cyclotomic

The main result: every complex number appearing in the weighted relation of a Clifford+T circuit
is exactly representable in SuperOpt's cyclotomic format
`(a + bω + cω² + dω³)/√2^k` (`TZap/Cyclotomic/Basic.lean`).

`IsCliffordT` restricts `Gate` to the gate set SuperOpt's exact matrices cover: `X`, `CNOT`,
Hadamard, and `Rz` at integer multiples of `π/4` — which is `T` (`k = 1`), `S` (`k = 2`), `Z`
(`k = 4`), `S†` (`k = 6`) and `T†` (`k = 7`). Arbitrary `Rz θ` is excluded, matching the Rust
comment that "Rz gates are window barriers and never reach this code": the proof below turns the
amplitude `e^{iθ}` into a *power of `ω`*, which needs `θ` to be a multiple of `π/4`. (This file
does not claim the converse — that some particular other angle is unrepresentable — since
nothing downstream needs it.)

The proof is three steps:

* `isCyclotomic_gate` — every entry of a single gate's matrix is representable. The `Rz (kπ/4)`
  entry is the power `ω^k`, the Hadamard entry is `±1/√2`, and `X`/`CNOT` entries are `0` or `1`.
* `isCyclotomic_circuit` — induction along the gate list. Composition is a finite sum of
  products, so this is exactly the closure package proved in `Basic.lean`.
* `exists_cyclotomic_representation` — the same statement spelled out as the explicit
  `∃ a b c d k` normal form, and `Unitary.isCyclotomic_unitary` for the dense-matrix semantics
  that `TZap/SuperOpt` and `src/super_opt/matrix.rs` actually manipulate.
-/

namespace TZap.Cyclotomic

open TZap.Semantics

noncomputable section

/-- The Clifford+T gate set: `X`, `CNOT`, Hadamard, and `Rz` at integer multiples of `π/4`.

`rzPiDivFour 1` is `T` and `rzPiDivFour 2` is `S` (see `IsCliffordT.t` and `IsCliffordT.s`);
the inverses `T†` and `S†` are `k = 7` and `k = 6`, since `Rz` angles are only used modulo `2π`
and `ω` has order eight. -/
inductive IsCliffordT {n : Nat} : Gate n → Prop
  | x (q : Fin n) : IsCliffordT (.x q)
  | cnot (c t : Fin n) : IsCliffordT (.cnot c t)
  | hadamard (q : Fin n) : IsCliffordT (.hadamard q)
  | rzPiDivFour (k : ℕ) (q : Fin n) : IsCliffordT (.rz ((k : ℝ) * (Real.pi / 4)) q)

/-- The `T` gate, `Rz (π/4)`. -/
theorem IsCliffordT.t {n : Nat} (q : Fin n) : IsCliffordT (Gate.rz (Real.pi / 4) q) := by
  have h : Real.pi / 4 = ((1 : ℕ) : ℝ) * (Real.pi / 4) := by push_cast; ring
  rw [h]
  exact IsCliffordT.rzPiDivFour 1 q

/-- The `S` gate, `Rz (π/2)`. -/
theorem IsCliffordT.s {n : Nat} (q : Fin n) : IsCliffordT (Gate.rz (Real.pi / 2) q) := by
  have h : Real.pi / 2 = ((2 : ℕ) : ℝ) * (Real.pi / 4) := by push_cast; ring
  rw [h]
  exact IsCliffordT.rzPiDivFour 2 q

/-- An `Rz (kπ/4)` phase factor is the `k`-th power of `ω`. This is the step that pins the gate
set down: it is where `π/4` being the rotation quantum turns an exponential into an algebraic
integer. -/
theorem phase_pi_div_four (k : ℕ) :
    Semantics.phase ((k : ℝ) * (Real.pi / 4)) true = omega ^ k := by
  have h : Complex.I * (((k : ℝ) * (Real.pi / 4) : ℝ) : ℂ)
      = (k : ℂ) * (Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) := by
    push_cast
    ring
  simp only [Semantics.phase, if_pos]
  rw [h, Complex.exp_nat_mul]
  rfl

/-- Every `Rz (kπ/4)` amplitude is representable. -/
theorem isCyclotomic_phase (k : ℕ) (b : Bool) :
    IsCyclotomic (Semantics.phase ((k : ℝ) * (Real.pi / 4)) b) := by
  cases b with
  | false => simpa [Semantics.phase] using IsCyclotomic.one
  | true =>
      rw [phase_pi_div_four]
      exact IsCyclotomic.omega_mem.pow k

/-- The Hadamard entries `±1/√2` are representable, with denominator exponent `k = 1`. -/
theorem isCyclotomic_hadCoeff (input output : Bool) :
    IsCyclotomic (Semantics.hadCoeff input output) := by
  unfold Semantics.hadCoeff
  split
  · exact ⟨-1, 0, 0, 0, 1, by push_cast; ring⟩
  · exact ⟨1, 0, 0, 0, 1, by push_cast; ring⟩

/-- **Step 1.** Every entry of a Clifford+T gate's matrix is cyclotomically representable. -/
theorem isCyclotomic_gate {n : Nat} {g : Gate n} (hg : IsCliffordT g) (b b' : Basis n) :
    IsCyclotomic (Semantics.gate g b b') := by
  cases hg with
  | x q =>
      simp only [Semantics.gate]
      split
      · exact IsCyclotomic.one
      · exact IsCyclotomic.zero
  | cnot c t =>
      simp only [Semantics.gate]
      split
      · exact IsCyclotomic.one
      · exact IsCyclotomic.zero
  | hadamard q =>
      simp only [Semantics.gate]
      split
      · exact isCyclotomic_hadCoeff _ _
      · exact IsCyclotomic.zero
  | rzPiDivFour k q =>
      simp only [Semantics.gate]
      split
      · exact isCyclotomic_phase k _
      · exact IsCyclotomic.zero

/-- **Step 2 (main theorem).** Every amplitude of a Clifford+T circuit is cyclotomically
representable.

The induction is driven entirely by the ring structure: the empty circuit contributes `0` and
`1`, and each `cons` step is a finite sum over the intermediate basis of products of a gate
entry with a smaller circuit amplitude. -/
theorem isCyclotomic_circuit {n : Nat} :
    ∀ (C : Circuit n), (∀ g ∈ C, IsCliffordT g) → ∀ x y : Basis n,
      IsCyclotomic (Semantics.circuit C x y) := by
  intro C
  induction C with
  | nil =>
      intro _ x y
      simp only [Semantics.circuit, WeightedRelation.id]
      split
      · exact IsCyclotomic.one
      · exact IsCyclotomic.zero
  | cons g D ih =>
      intro hC x y
      simp only [Semantics.circuit, WeightedRelation.comp]
      refine IsCyclotomic.sum _ _ fun z _ => ?_
      exact (isCyclotomic_gate (hC g List.mem_cons_self) x z).mul
        (ih (fun h hh => hC h (List.mem_cons_of_mem _ hh)) z y)

/-- **The statement spelled out.** Every complex number in the weighted relation of a Clifford+T
circuit is literally of SuperOpt's form: an integer combination of `1, ω, ω², ω³` over a power
of `√2`. -/
theorem exists_cyclotomic_representation {n : Nat} (C : Circuit n)
    (hC : ∀ g ∈ C, IsCliffordT g) (x y : Basis n) :
    ∃ (a b c d : ℤ) (k : ℕ),
      Semantics.circuit C x y
        = ((a : ℂ) + b * omega + c * omega ^ 2 + d * omega ^ 3)
            / ((Real.sqrt 2 : ℝ) : ℂ) ^ k :=
  isCyclotomic_circuit C hC x y

/-- The amplitudes live in the subring `ℤ[ω][1/√2]` of `ℂ`. -/
theorem circuit_mem_cyclotomicSubring {n : Nat} (C : Circuit n)
    (hC : ∀ g ∈ C, IsCliffordT g) (x y : Basis n) :
    Semantics.circuit C x y ∈ cyclotomicSubring :=
  isCyclotomic_circuit C hC x y

/-- The same conclusion for the dense unitary semantics of `TZap/Unitary.lean` — the
row-output/column-input matrix that `TZap/SuperOpt` and `src/super_opt/matrix.rs` manipulate. -/
theorem isCyclotomic_unitary {n : Nat} (C : Circuit n)
    (hC : ∀ g ∈ C, IsCliffordT g) (output input : Basis n) :
    IsCyclotomic (Unitary.unitary C output input) := by
  rw [Unitary.unitary_apply_eq_semantics]
  exact isCyclotomic_circuit C hC input output

/-! ## Worked example

A guard against a vacuous hypothesis: `IsCliffordT` is satisfiable, so
`isCyclotomic_circuit` really does say something about real circuits. -/

section Example

/-- `H · T · CNOT` on two qubits — a genuine Clifford+T circuit. -/
def exampleCircuit : Circuit 2 :=
  [Gate.hadamard 0, Gate.rz (Real.pi / 4) 0, Gate.cnot 0 1]

theorem exampleCircuit_isCliffordT : ∀ g ∈ exampleCircuit, IsCliffordT g := by
  intro g hg
  simp only [exampleCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact IsCliffordT.hadamard 0
  · exact IsCliffordT.t 0
  · exact IsCliffordT.cnot 0 1

/-- Every amplitude of that circuit is cyclotomic. -/
theorem exampleCircuit_isCyclotomic (x y : Basis 2) :
    IsCyclotomic (Semantics.circuit exampleCircuit x y) :=
  isCyclotomic_circuit _ exampleCircuit_isCliffordT x y

end Example

end
end TZap.Cyclotomic
