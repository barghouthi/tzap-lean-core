import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.CharP.Two
import Tzap.Symbolic

/-!
# Canonical affine normal forms over 𝔽₂

The symbolic analysis (`Tzap.Symbolic`) represents each qubit's parity as an
expression *tree* (`Parity`: constants, variables, xor). Trees that denote the
same Boolean affine function can look different, so the optimizer cannot
compare parities syntactically. This file provides the canonical
representation used for comparison:

* `Form` — a Boolean affine function in normal form: a constant in
  `F₂ = ZMod 2` plus a finitely supported coefficient vector `Nat →₀ F₂`
  (one coefficient per variable). Two `Form`s are equal iff they denote the
  same affine function, and equality is decidable.
* `normalize : Parity → Form` — folds an expression tree into its normal
  form, commuting with evaluation (`normalize_eval`).
* `Bounded m` — all variables mentioned lie below `m`; needed so that a form
  can be hashed using only the finite sample of draws for variables `< m`.

Downstream, `Algorithm.lean` merges rotations whose parities have equal
normal forms, `Randomized.lean` hashes parities through `normalize`, and
`Collision.lean` proves the hash-collision bound for *distinct* `Form`s.
-/


namespace Tzap.Affine

open Tzap.Symbolic

noncomputable section

/-- The two-element field `𝔽₂ = ZMod 2`, the coefficient field for affine parities.
Booleans embed into it via `bit`, turning xor into addition. -/
abbrev F₂ := ZMod 2

/-- Embed a Boolean into `F₂`: `true ↦ 1`, `false ↦ 0`. This is the bridge between
the Boolean world of the symbolic analysis and the linear-algebraic world used here. -/
def bit (b : Bool) : F₂ := if b then 1 else 0

/-- `bit` is injective: distinct Booleans map to distinct field elements. Used to
transport *disequalities* of parities back from `F₂` to `Bool`
(see `normalize_ne_of_eval_ne`). -/
theorem bit_injective : Function.Injective bit := by
  intro a b h
  cases a <;> cases b <;> simp_all [bit]

/-- `bit` turns Boolean xor into addition in `F₂` (which has characteristic 2, so
`1 + 1 = 0`). This is why affine normal forms can use ordinary `Finsupp` addition. -/
theorem bit_xor (a b : Bool) : bit (a != b) = bit a + bit b := by
  cases a <;> cases b <;> simp [bit]
  exact (CharTwo.add_self_eq_zero (1 : F₂)).symm

/-- Canonical normal form of a Boolean affine function: `c ⊕ ⨁_{i ∈ support} vᵢ`, stored
as a constant `c : F₂` plus a finitely supported coefficient vector (`Nat →₀ F₂`, so a
coefficient is `1` exactly when variable `i` appears). Since coefficients live in `F₂`,
this representation is *canonical*: two forms are equal as structures iff they denote
the same function on all valuations. `DecidableEq` makes parity comparison executable,
which is what `Algorithm.lean`'s merge decisions rely on. -/
structure Form where
  constant : F₂
  coefficients : Nat →₀ F₂
deriving DecidableEq

/-- Extensionality: a `Form` is determined by its constant and its coefficient vector. -/
@[ext] theorem Form.ext {p q : Form} (hc : p.constant = q.constant)
    (hl : p.coefficients = q.coefficients) : p = q := by
  cases p
  cases q
  simp_all

/-- Forms carry componentwise `0`, `+`, and `-` (constant and coefficients separately).
Over `F₂` subtraction coincides with addition, but `Sub` is kept so that
`Collision.lean` can phrase collision of `p` and `q` as a statement about `p - q`. -/
instance : Zero Form := ⟨⟨0, 0⟩⟩
instance : Add Form := ⟨fun p q => ⟨p.constant + q.constant, p.coefficients + q.coefficients⟩⟩
instance : Sub Form := ⟨fun p q => ⟨p.constant - q.constant, p.coefficients - q.coefficients⟩⟩

@[simp] theorem add_constant (p q : Form) : (p + q).constant = p.constant + q.constant := rfl
@[simp] theorem add_coefficients (p q : Form) :
    (p + q).coefficients = p.coefficients + q.coefficients := rfl
@[simp] theorem sub_coefficients (p q : Form) :
    (p - q).coefficients = p.coefficients - q.coefficients := rfl

/-! ## Evaluation -/

/-- Evaluate a form at a valuation of the variables: the constant plus the sum of
`coefficient i * valuation i` over the (finite) support. This is the affine function the
form denotes; `Randomized.evalBits` and `Collision.output` apply it coordinatewise to
`k`-bit draws to hash a parity. -/
def eval (valuation : Nat → F₂) (p : Form) : F₂ :=
  p.constant + p.coefficients.sum (fun i coefficient => coefficient * valuation i)

/-- Evaluation is additive: `eval` of a sum of forms is the sum of evaluations.
The algebraic heart of `normalize_eval` (xor of parities ↦ sum of forms). -/
@[simp] theorem eval_add (v) (p q : Form) : eval v (p + q) = eval v p + eval v q := by
  simp [eval, add_assoc, add_left_comm, add_comm, add_mul, Finsupp.sum_add_index]

/-! ## Normalization -/

/-- Normalize the expression-tree representation used by the symbolic proof into its
canonical affine form: a constant `b` becomes the pure constant `bit b`, a variable `i`
becomes the single coefficient `xᵢ`, and xor becomes addition of forms. Trees denoting
the same affine function normalize to the *same* `Form`, so `normalize p = normalize q`
is the decidable parity-equality test used by both the exact and randomized optimizers. -/
def normalize : Parity → Form
  | .const b => ⟨bit b, 0⟩
  | .var i => ⟨0, Finsupp.single i 1⟩
  | .xor p q => normalize p + normalize q

@[simp] theorem normalize_xor (p q) : normalize (.xor p q) = normalize p + normalize q := rfl

/-- Normalization commutes with evaluation: evaluating `normalize p` at the `F₂`-image of
a Boolean valuation gives the `F₂`-image of `p.eval`. This is the semantic correctness of
`normalize`, and the reason hashing through normal forms (in `Randomized.lean`) computes
the same value as hashing the parity tree itself. -/
theorem normalize_eval (p : Parity) (valuation : Nat → Bool) :
    eval (fun i => bit (valuation i)) (normalize p) = bit (p.eval valuation) := by
  induction p with
  | const b => simp [normalize, eval]
  | var i => simp [normalize, eval]
  | xor p q ihp ihq => simp [ihp, ihq, bit_xor]

/-- Contrapositive completeness: if two parities *disagree* on some Boolean valuation,
their normal forms are distinct. Downstream (`RandomizedSoundness.lean`) this converts
"the analysis's parities differ semantically" into the `normalize p ≠ normalize q`
hypothesis needed to apply the collision bound. -/
theorem normalize_ne_of_eval_ne {p q : Parity} {valuation : Nat → Bool}
    (h : p.eval valuation ≠ q.eval valuation) : normalize p ≠ normalize q := by
  intro heq
  apply h
  apply bit_injective
  rw [← normalize_eval p valuation, ← normalize_eval q valuation, heq]

/-! ## Boundedness -/

/-- A form is `Bounded m` when every variable it mentions has index `< m`. The randomized
algorithm only samples draws for the `m` variables the analysis allocates, so boundedness
is exactly the condition under which hashing a form is determined by a finite
`Sample m k` (see `Collision.sum_liftSample_eq` and `affine_collision_bound`). -/
def Bounded (m : Nat) (p : Form) : Prop :=
  ∀ i ∈ p.coefficients.support, i < m

/-- Normalization preserves boundedness: if the parity tree only mentions variables below
`m` (`Parity.Bounded`), so does its normal form. Combined with the analysis's invariant
that all parities are bounded by the fresh counter, this discharges the boundedness
hypotheses of the collision bound. -/
theorem normalize_bounded {p : Parity} {m : Nat} (hp : p.Bounded m) :
    Bounded m (normalize p) := by
  induction p with
  | const b =>
      intro i hi
      simp [normalize] at hi
  | var i =>
      intro j hj
      simp only [normalize, Finsupp.mem_support_iff, Finsupp.single_apply] at hj
      split at hj
      · subst j
        exact hp
      · simp at hj
  | xor p q ihp ihq =>
      simp only [Parity.Bounded] at hp
      intro i hi
      simp only [normalize, add_coefficients, Finsupp.mem_support_iff,
        Finsupp.add_apply] at hi
      by_cases hpi : (normalize p).coefficients i = 0
      · have hqi : (normalize q).coefficients i ≠ 0 := by
          intro hq0
          simp [hpi, hq0] at hi
        exact ihq hp.2 i (Finsupp.mem_support_iff.mpr hqi)
      · exact ihp hp.1 i (Finsupp.mem_support_iff.mpr hpi)

end
end Tzap.Affine
