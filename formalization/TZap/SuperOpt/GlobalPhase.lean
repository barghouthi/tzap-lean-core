import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.UnitaryGroup
import TZap.Unitary

/-!
# Canonicalizing a Matrix Up to Global Phase

SuperOpt's synthesis table is keyed by a window's unitary matrix, but two circuits that differ
only by an unobservable global phase `e^{iφ}` must hit the *same* key: they implement the same
operator, so either is a valid replacement for the other. The table therefore stores a canonical
representative of each phase class.

This file formalizes the canonicalization recipe and proves it is exactly right. The recipe is:

> Scan the entries in a fixed order, take the first nonzero one, and divide the whole matrix by
> that entry's phase.

The two things that must be true for this to work are proved here:

* **It never fails and never picks inconsistently.** Every nonzero matrix has a first nonzero
  entry (`exists_isPivot`), it is unique (`IsPivot.unique`), and — the crux — rescaling by a
  nonzero constant does not move it (`IsPivot.smul`). Two phase-equivalent matrices therefore
  pivot at the *same position* (`IsPivot.of_equivUpToPhase`), so the recipe divides both by
  corresponding entries rather than comparing unrelated ones.
* **It decides the question.** `canonicalize_eq_iff`: for nonzero `U` and `V`,
  `canonicalize U = canonicalize V ↔ EquivUpToPhase U V`. Completeness (equivalent matrices always
  produce equal keys) and soundness (equal keys always mean equivalent matrices) in one
  statement. `canonicalize_eq_iff_of_mem_unitaryGroup` specializes it to genuine unitaries, which
  are nonzero automatically.

Nothing here depends on *which* order the scan uses — only that it is a fixed linear order — so
the results apply to the implementation's row-major scan over integer-indexed basis states. That
concrete order is provided at the end as `Basis.instLinearOrder`.

## Correspondence with the Rust implementation

`src/super_opt/matrix.rs` works over the cyclotomic ring `ℤ[ω][1/√2]`, where the only global
phases a Clifford+T circuit can produce are the eight powers of `ω`. It exploits that: instead of
dividing (which would leave the ring), `canonical_phase_power` multiplies by the power of `ω`
making the pivot's coefficient tuple lexicographically least. That is the same recipe specialized
to a finite phase group — same pivot, same "rescale so the pivot is canonical", but choosing
a representative within the ring rather than forcing the pivot to `1`.

| Lean | Rust (`src/super_opt/matrix.rs`) |
| --- | --- |
| `IsPivot` | `data.iter().find(|entry| !entry.is_zero())` in `canonical_phase_power` |
| `phaseOf (pivot U)` | the `ω`-power that `canonical_phase_power` divides out |
| `canonicalize` | `entry.times_omega(phase)` applied to every entry |
| `canonicalize_eq_iff` | `equivalent_up_to_global_phase` |
-/

namespace TZap.SuperOpt.GlobalPhase

open scoped Classical

noncomputable section

variable {ι : Type*}

/-! ## Equivalence up to global phase

Nothing in this section needs the index type ordered or finite — only the pivot machinery below
does. -/

/-- `U` and `V` denote the same operator up to an unobservable global phase: `V = c • U` for
some unit-modulus scalar `c`. -/
def EquivUpToPhase (U V : Matrix ι ι ℂ) : Prop := ∃ c : ℂ, ‖c‖ = 1 ∧ V = c • U

namespace EquivUpToPhase

@[refl] theorem refl (U : Matrix ι ι ℂ) : EquivUpToPhase U U :=
  ⟨1, by simp, by simp⟩

theorem symm {U V : Matrix ι ι ℂ} (h : EquivUpToPhase U V) : EquivUpToPhase V U := by
  obtain ⟨c, hc, rfl⟩ := h
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0] at hc
    simp at hc
  refine ⟨c⁻¹, by simp [norm_inv, hc], ?_⟩
  rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]

theorem trans {U V W : Matrix ι ι ℂ} (h₁ : EquivUpToPhase U V) (h₂ : EquivUpToPhase V W) :
    EquivUpToPhase U W := by
  obtain ⟨c, hc, rfl⟩ := h₁
  obtain ⟨d, hd, rfl⟩ := h₂
  exact ⟨d * c, by simp [hc, hd], by rw [smul_smul]⟩

/-- A phase scalar is nonzero. -/
theorem ne_zero_of_norm_one {c : ℂ} (hc : ‖c‖ = 1) : c ≠ 0 := by
  intro h0
  rw [h0] at hc
  simp at hc

end EquivUpToPhase

/-! ## The first nonzero entry -/

variable [LinearOrder ι]

/-- `IsPivot U p` says `p` is the first nonzero entry of `U` in row-major order: the entry is
itself nonzero, every earlier row is identically zero, and every earlier column of `p`'s own row
is zero. -/
def IsPivot (U : Matrix ι ι ℂ) (p : ι × ι) : Prop :=
  U p.1 p.2 ≠ 0 ∧ (∀ i j, i < p.1 → U i j = 0) ∧ (∀ j, j < p.2 → U p.1 j = 0)

/-- The scan never fails: every nonzero matrix has a first nonzero entry. -/
theorem exists_isPivot [Fintype ι] {U : Matrix ι ι ℂ} (hU : U ≠ 0) : ∃ p, IsPivot U p := by
  have hne : ∃ i j, U i j ≠ 0 := by
    by_contra h
    refine hU (funext fun i => funext fun j => ?_)
    by_contra hij
    exact h ⟨i, j, hij⟩
  obtain ⟨i, j, hij⟩ := hne
  -- The rows that contain a nonzero entry, and the least such row.
  have hrows : (Finset.univ.filter fun i => ∃ j, U i j ≠ 0).Nonempty :=
    ⟨i, by simp [Finset.mem_filter]; exact ⟨j, hij⟩⟩
  set row := (Finset.univ.filter fun i => ∃ j, U i j ≠ 0).min' hrows with hrow
  have hrow_mem := Finset.min'_mem _ hrows
  rw [← hrow] at hrow_mem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hrow_mem
  -- The nonzero columns of that row, and the least such column.
  have hcols : (Finset.univ.filter fun j => U row j ≠ 0).Nonempty := by
    obtain ⟨j', hj'⟩ := hrow_mem
    exact ⟨j', by simp [Finset.mem_filter, hj']⟩
  set col := (Finset.univ.filter fun j => U row j ≠ 0).min' hcols with hcol
  have hcol_mem := Finset.min'_mem _ hcols
  rw [← hcol] at hcol_mem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcol_mem
  refine ⟨(row, col), hcol_mem, ?_, ?_⟩
  · -- No earlier row has any nonzero entry, or it would beat `row` in the minimum.
    intro i' j' hlt
    by_contra hne'
    have : row ≤ i' := by
      rw [hrow]
      exact Finset.min'_le _ _ (by simp [Finset.mem_filter]; exact ⟨j', hne'⟩)
    exact absurd hlt (not_lt.mpr this)
  · -- Likewise no earlier column of `row`.
    intro j' hlt
    by_contra hne'
    have : col ≤ j' := by
      rw [hcol]
      exact Finset.min'_le _ _ (by simp [Finset.mem_filter, hne'])
    exact absurd hlt (not_lt.mpr this)

/-- The first nonzero entry is unique — so "the" pivot is well defined. -/
theorem IsPivot.unique {U : Matrix ι ι ℂ} {p q : ι × ι}
    (hp : IsPivot U p) (hq : IsPivot U q) : p = q := by
  obtain ⟨hp0, hprow, hpcol⟩ := hp
  obtain ⟨hq0, hqrow, hqcol⟩ := hq
  have hfst : p.1 = q.1 := by
    rcases lt_trichotomy p.1 q.1 with h | h | h
    · exact absurd (hqrow p.1 p.2 h) hp0
    · exact h
    · exact absurd (hprow q.1 q.2 h) hq0
  have hsnd : p.2 = q.2 := by
    rcases lt_trichotomy p.2 q.2 with h | h | h
    · exact absurd (hqcol p.2 (by rw [← hfst] at *; exact h)) (by rw [hfst] at hp0; exact hp0)
    · exact h
    · exact absurd (hpcol q.2 h) (by rw [hfst]; exact hq0)
  exact Prod.ext hfst hsnd

/-- **The crux.** Rescaling by a nonzero constant does not move the first nonzero entry: it
scales every entry by the same nonzero factor, so it changes no entry's zero-ness. -/
theorem IsPivot.smul {U : Matrix ι ι ℂ} {c : ℂ} (hc : c ≠ 0) {p : ι × ι}
    (h : IsPivot U p) : IsPivot (c • U) p := by
  obtain ⟨h0, hrow, hcol⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simpa [Matrix.smul_apply, mul_eq_zero, hc] using h0
  · intro i j hlt
    simp [Matrix.smul_apply, hrow i j hlt]
  · intro j hlt
    simp [Matrix.smul_apply, hcol j hlt]

/-- Phase-equivalent matrices pivot at the *same position*. This is what makes comparing their
canonical forms meaningful: the recipe divides each by the entry at one and the same place. -/
theorem IsPivot.of_equivUpToPhase {U V : Matrix ι ι ℂ} {p : ι × ι}
    (huv : EquivUpToPhase U V) (h : IsPivot U p) : IsPivot V p := by
  obtain ⟨c, hc, rfl⟩ := huv
  exact h.smul (EquivUpToPhase.ne_zero_of_norm_one hc)

/-- The value of the first nonzero entry, or `0` for the zero matrix. -/
def pivot (U : Matrix ι ι ℂ) : ℂ :=
  if h : ∃ p, IsPivot U p then U h.choose.1 h.choose.2 else 0

theorem pivot_eq {U : Matrix ι ι ℂ} {p : ι × ι} (h : IsPivot U p) : pivot U = U p.1 p.2 := by
  have hex : ∃ p, IsPivot U p := ⟨p, h⟩
  rw [pivot, dif_pos hex]
  rw [hex.choose_spec.unique h]

@[simp] theorem pivot_zero : pivot (0 : Matrix ι ι ℂ) = 0 := by
  rw [pivot, dif_neg]
  rintro ⟨p, hp, -, -⟩
  exact hp rfl

theorem pivot_ne_zero [Fintype ι] {U : Matrix ι ι ℂ} (hU : U ≠ 0) : pivot U ≠ 0 := by
  obtain ⟨p, hp⟩ := exists_isPivot hU
  rw [pivot_eq hp]
  exact hp.1

/-- Rescaling scales the pivot value by the same factor — because it is the same entry. -/
theorem pivot_smul [Fintype ι] {U : Matrix ι ι ℂ} {c : ℂ} (hc : c ≠ 0) :
    pivot (c • U) = c * pivot U := by
  rcases eq_or_ne U 0 with rfl | hU
  · simp
  · obtain ⟨p, hp⟩ := exists_isPivot hU
    rw [pivot_eq (hp.smul hc), pivot_eq hp]
    simp [Matrix.smul_apply]

/-! ## Canonicalization -/

/-- The phase of a complex number: `z / ‖z‖`, the unit-modulus part of `z` (and `0` at `0`). -/
def phaseOf (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

@[simp] theorem phaseOf_zero : phaseOf (0 : ℂ) = 0 := by simp [phaseOf]

theorem norm_phaseOf {z : ℂ} (hz : z ≠ 0) : ‖phaseOf z‖ = 1 := by
  have h : ‖((‖z‖ : ℝ) : ℂ)‖ = ‖z‖ := by simp
  rw [phaseOf, norm_div, h]
  exact div_self (norm_ne_zero_iff.mpr hz)

theorem phaseOf_ne_zero {z : ℂ} (hz : z ≠ 0) : phaseOf z ≠ 0 :=
  EquivUpToPhase.ne_zero_of_norm_one (norm_phaseOf hz)

/-- Multiplying by a unit-modulus scalar multiplies the phase by that scalar. -/
theorem phaseOf_mul {c z : ℂ} (hc : ‖c‖ = 1) : phaseOf (c * z) = c * phaseOf z := by
  rw [phaseOf, phaseOf, norm_mul, hc, one_mul, mul_div_assoc]

/-- The canonical representative of `U`'s phase class: `U` divided by the phase of its first
nonzero entry. -/
def canonicalize (U : Matrix ι ι ℂ) : Matrix ι ι ℂ := (phaseOf (pivot U))⁻¹ • U

/-- Canonicalization is phase-invariant: the whole point. -/
theorem canonicalize_smul [Fintype ι] {U : Matrix ι ι ℂ} {c : ℂ} (hc : ‖c‖ = 1) :
    canonicalize (c • U) = canonicalize U := by
  have hc0 : c ≠ 0 := EquivUpToPhase.ne_zero_of_norm_one hc
  rw [canonicalize, canonicalize, pivot_smul hc0, phaseOf_mul hc, mul_inv, smul_smul]
  congr 1
  field_simp

/-- The canonical representative really is in the same phase class as the matrix it came from,
so a table keyed by `canonicalize` stores a legitimate stand-in. -/
theorem equivUpToPhase_canonicalize [Fintype ι] {U : Matrix ι ι ℂ} (hU : U ≠ 0) :
    EquivUpToPhase U (canonicalize U) :=
  ⟨(phaseOf (pivot U))⁻¹, by
    rw [norm_inv, norm_phaseOf (pivot_ne_zero hU), inv_one], rfl⟩

@[simp] theorem canonicalize_zero : canonicalize (0 : Matrix ι ι ℂ) = 0 := by
  rw [canonicalize, smul_zero]

/-- Canonicalization is idempotent, so it really is a canonical form. -/
theorem canonicalize_idem [Fintype ι] (U : Matrix ι ι ℂ) :
    canonicalize (canonicalize U) = canonicalize U := by
  rcases eq_or_ne U 0 with rfl | hU
  · rw [canonicalize_zero, canonicalize_zero]
  · exact canonicalize_smul (by rw [norm_inv, norm_phaseOf (pivot_ne_zero hU), inv_one])

/-- **Main theorem.** For nonzero matrices, the first-nonzero-entry recipe decides equivalence up
to global phase exactly: equal canonical forms iff the matrices differ by a global phase.

Left to right is soundness (a table hit is a genuine phase-equivalence, so the replacement
circuit implements the same operator); right to left is completeness (phase-equivalent matrices
never miss each other in the table). -/
theorem canonicalize_eq_iff [Fintype ι] {U V : Matrix ι ι ℂ} (hU : U ≠ 0) (hV : V ≠ 0) :
    canonicalize U = canonicalize V ↔ EquivUpToPhase U V := by
  constructor
  · intro h
    have hau : phaseOf (pivot U) ≠ 0 := phaseOf_ne_zero (pivot_ne_zero hU)
    have hav : phaseOf (pivot V) ≠ 0 := phaseOf_ne_zero (pivot_ne_zero hV)
    refine ⟨phaseOf (pivot V) * (phaseOf (pivot U))⁻¹, ?_, ?_⟩
    · rw [norm_mul, norm_inv, norm_phaseOf (pivot_ne_zero hU),
        norm_phaseOf (pivot_ne_zero hV)]
      norm_num
    · -- Scale `canonicalize U = canonicalize V` back up by `V`'s phase.
      have hscaled := congrArg (fun M => phaseOf (pivot V) • M) h
      simp only [canonicalize, smul_smul] at hscaled
      rw [mul_inv_cancel₀ hav, one_smul] at hscaled
      exact hscaled.symm
  · rintro ⟨c, hc, rfl⟩
    exact (canonicalize_smul hc).symm

/-! ## Application to unitaries -/

omit [LinearOrder ι] in
/-- A unitary matrix over a nonempty index type is nonzero, so `canonicalize_eq_iff` applies to it
without further hypotheses. -/
theorem ne_zero_of_mem_unitaryGroup [Fintype ι] [DecidableEq ι] [Nonempty ι] {U : Matrix ι ι ℂ}
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) : U ≠ 0 := by
  intro h0
  have h1 : (star U) * U = 1 := hU.1
  rw [h0] at h1
  -- `Uᴴ * U = 1` with `U = 0` reads `0 = 1` at any diagonal entry.
  have hdiag := congrFun (congrFun h1 (Classical.arbitrary ι)) (Classical.arbitrary ι)
  simp at hdiag

/-- The recipe decides equivalence up to global phase for any two unitaries. -/
theorem canonicalize_eq_iff_of_mem_unitaryGroup [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {U V : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hV : V ∈ Matrix.unitaryGroup ι ℂ) :
    canonicalize U = canonicalize V ↔ EquivUpToPhase U V :=
  canonicalize_eq_iff (ne_zero_of_mem_unitaryGroup hU) (ne_zero_of_mem_unitaryGroup hV)

end

end TZap.SuperOpt.GlobalPhase

/-! ## The implementation's scan order

The results above hold for any fixed linear order on the index type. The optimizer scans its
row-major `data` array, i.e. it orders basis states by the integer they encode, with qubit `q`
contributing `2^q` (`bit(q) = 1 << q` in `src/super_opt/matrix.rs`). That order is supplied here
so the theorems apply directly to `TZap.Unitary.UnitaryMatrix`.
-/

namespace TZap.Basis

/-- The integer a basis state encodes, little-endian: qubit `q` contributes `2^q`, matching the
implementation's `bit(q) = 1 << q`. -/
def toNat {n : Nat} (b : Basis n) : Nat :=
  (finFunctionFinEquiv fun q => if b q then (1 : Fin 2) else 0 : Fin (2 ^ n))

theorem toNat_injective {n : Nat} : Function.Injective (toNat (n := n)) := by
  intro a b hab
  have h : (fun q => if a q then (1 : Fin 2) else 0) = fun q => if b q then (1 : Fin 2) else 0 := by
    apply finFunctionFinEquiv.injective
    exact Fin.ext hab
  funext q
  have hq := congrFun h q
  by_cases ha : a q <;> by_cases hb : b q <;> simp [ha, hb] at hq ⊢

/-- Basis states ordered by the integer they encode — the order in which the implementation's
row-major scan visits matrix entries. -/
instance instLinearOrder {n : Nat} : LinearOrder (Basis n) :=
  LinearOrder.lift' toNat toNat_injective

end TZap.Basis
