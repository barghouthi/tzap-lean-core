import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.IntervalCases
import Tzap.Cyclotomic.Basic

/-!
# Canonicalizing the Ring Representation Up to Global Phase

`Tzap/SuperOpt/GlobalPhase.lean` canonicalizes a complex matrix by dividing by the phase of its
first nonzero entry. That recipe is correct but leaves the cyclotomic ring: dividing by `‖z‖`
is not a ring operation, so it cannot be performed on the exact representation SuperOpt stores.

This file formalizes the canonicalization SuperOpt actually runs, entirely inside the ring. The
observation it exploits is that a Clifford+T circuit can only ever produce a global phase that is
one of the eight powers of `ω`, and multiplying by a power of `ω` *is* a ring operation — on the
coefficient representation it is the signed rotation `(a, b, c, d) ↦ (-d, a, b, c)`. So instead of
scaling the pivot entry to `1`, we multiply the whole matrix by the power of `ω` that sends the
pivot to a fixed representative of its rotation orbit.

## Main results

* `CycInt.canon_rotate`: the scalar canonical form is invariant under multiplication by `ω`.
* `CycInt.canon_eq_iff`: two ring elements have the same canonical form exactly when one is a
  power of `ω` times the other.
* `CycInt.rotate_canonPow`: canonicalization is realized by an explicit power of `ω`, so it is
  computed inside the ring and never divides.
* `IsPivot.rotateMat`: a rotation moves no entry onto or off zero, so it cannot move the pivot.
  This is the ring-level counterpart of `GlobalPhase.IsPivot.smul`.
* `canonMat_pivot_eq_canon` and `canonMat_pivot_eq_of_rotateMat`: the matrix canonical form
  carries the canonical pivot entry, and rotating the matrix does not change it — so comparing
  canonical pivot entries decides whether two matrices differ by a power of `ω`.

`toComplex_rotate` connects the rotation back to the complex semantics, so a rotation really does
denote multiplication by a global phase.

## Relation to `GlobalPhase`

Together, `exists_omega_pow_of_isCyclotomic_of_norm_one` and `canonMat_eq_iff` give for the exact
representation what `GlobalPhase.canonicalize_eq_iff` gives for complex matrices: a global phase
between two Clifford+T matrices is necessarily a power of `ω`, and rotating by powers of `ω` is
decided by comparing canonical forms. Unlike `GlobalPhase.canonicalize`, nothing here divides, so
every intermediate value stays in the ring.

## Correspondence with the Rust implementation

| Lean | Rust (`src/super_opt/matrix.rs`) |
| --- | --- |
| `CycInt` | `Cyclotomic { coefficients: [i8; 4] }` |
| `CycInt.timesOmega` | `Cyclotomic::times_omega` at `power = 1` |
| `CycInt.canonPow` | the `ω`-power chosen by `canonical_phase_power` |
| `pivot` | `data.iter().find(|entry| !entry.is_zero())` |
| `canonMat` | `entry.times_omega(phase)` applied to every entry |

The denominator exponent plays no part here: a rotation multiplies by a unit, so it leaves the
shared `√2` denominator untouched, and canonicalization concerns the numerator matrix alone.
-/

-- Several matrix-level lemmas do not need the order on indices.
set_option linter.unusedSectionVars false

namespace Tzap.Cyclotomic

/-- The coefficient representation of an element of `ℤ[ω]`, namely `a + bω + cω² + dω³`. This is
the Rust `Cyclotomic` struct, with `ℤ` in place of `i8`. -/
structure CycInt where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
deriving DecidableEq

namespace CycInt

@[ext]
theorem ext' {z w : CycInt} (ha : z.a = w.a) (hb : z.b = w.b) (hc : z.c = w.c)
    (hd : z.d = w.d) : z = w := by
  cases z; cases w; simp_all

instance : Zero CycInt := ⟨⟨0, 0, 0, 0⟩⟩

@[simp] theorem zero_a : (0 : CycInt).a = 0 := rfl
@[simp] theorem zero_b : (0 : CycInt).b = 0 := rfl
@[simp] theorem zero_c : (0 : CycInt).c = 0 := rfl
@[simp] theorem zero_d : (0 : CycInt).d = 0 := rfl

/-! ## Denotation -/

/-- The complex number a coefficient tuple denotes. -/
noncomputable def toComplex (z : CycInt) : ℂ :=
  (z.a : ℂ) + z.b * omega + z.c * omega ^ 2 + z.d * omega ^ 3

theorem isCycInt_toComplex (z : CycInt) : IsCycInt z.toComplex :=
  ⟨z.a, z.b, z.c, z.d, rfl⟩

/-- Every element of `ℤ[ω]` is denoted by some coefficient tuple. -/
theorem exists_toComplex_eq {x : ℂ} (hx : IsCycInt x) : ∃ z : CycInt, z.toComplex = x := by
  obtain ⟨a, b, c, d, rfl⟩ := hx
  exact ⟨⟨a, b, c, d⟩, rfl⟩

/-! ## Multiplication by `ω` as a rotation -/

/-- Multiplication by `ω`, on coefficients: `(a, b, c, d) ↦ (-d, a, b, c)`. The sign is the
reduction `ω⁴ = -1`. -/
def timesOmega (z : CycInt) : CycInt := ⟨-z.d, z.a, z.b, z.c⟩

@[simp] theorem timesOmega_a (z : CycInt) : (timesOmega z).a = -z.d := rfl
@[simp] theorem timesOmega_b (z : CycInt) : (timesOmega z).b = z.a := rfl
@[simp] theorem timesOmega_c (z : CycInt) : (timesOmega z).c = z.b := rfl
@[simp] theorem timesOmega_d (z : CycInt) : (timesOmega z).d = z.c := rfl

theorem toComplex_timesOmega (z : CycInt) : (timesOmega z).toComplex = omega * z.toComplex := by
  simp only [toComplex, timesOmega_a, timesOmega_b, timesOmega_c, timesOmega_d]
  push_cast
  linear_combination (-(z.d : ℂ)) * omega_pow_four

@[simp] theorem timesOmega_eq_zero_iff {z : CycInt} : timesOmega z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have ha : z.a = 0 := by simpa using congrArg CycInt.b h
    have hb : z.b = 0 := by simpa using congrArg CycInt.c h
    have hc : z.c = 0 := by simpa using congrArg CycInt.d h
    have hd : z.d = 0 := by
      have := congrArg CycInt.a h
      simpa [neg_eq_zero] using this
    exact ext' ha hb hc hd
  · intro h
    subst h
    rfl

/-- Multiplication by `ωⁿ`. -/
def rotate (n : ℕ) (z : CycInt) : CycInt := timesOmega^[n] z

@[simp] theorem rotate_zero (z : CycInt) : rotate 0 z = z := rfl

theorem rotate_succ (n : ℕ) (z : CycInt) : rotate (n + 1) z = timesOmega (rotate n z) :=
  Function.iterate_succ_apply' _ _ _

theorem rotate_add (m n : ℕ) (z : CycInt) : rotate (m + n) z = rotate m (rotate n z) := by
  simpa [rotate, Nat.add_comm] using Function.iterate_add_apply timesOmega m n z

theorem toComplex_rotate (n : ℕ) (z : CycInt) :
    (rotate n z).toComplex = omega ^ n * z.toComplex := by
  induction n with
  | zero => simp
  | succ n ih => rw [rotate_succ, toComplex_timesOmega, ih]; ring

@[simp] theorem rotate_eq_zero_iff {n : ℕ} {z : CycInt} : rotate n z = 0 ↔ z = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [rotate_succ, timesOmega_eq_zero_iff, ih]

@[simp] theorem rotate_four (z : CycInt) : rotate 4 z = ⟨-z.a, -z.b, -z.c, -z.d⟩ := by
  simp [rotate, Function.iterate_succ_apply', timesOmega]

/-- `ω⁸ = 1`, so eight rotations return to the start. -/
@[simp] theorem rotate_eight (z : CycInt) : rotate 8 z = z := by
  have h : (8 : ℕ) = 4 + 4 := by norm_num
  rw [h, rotate_add, rotate_four, rotate_four]
  simp

theorem rotate_eight_mul (q : ℕ) (z : CycInt) : rotate (8 * q) z = z := by
  induction q with
  | zero => simp
  | succ q ih =>
      have h : 8 * (q + 1) = 8 + 8 * q := by ring
      rw [h, rotate_add, ih, rotate_eight]

theorem rotate_mod_eight (n : ℕ) (z : CycInt) : rotate (n % 8) z = rotate n z := by
  conv_rhs => rw [← Nat.div_add_mod n 8]
  rw [rotate_add, rotate_eight_mul]

/-- Rotation amounts only matter modulo eight. -/
theorem rotate_congr {m n : ℕ} (h : m % 8 = n % 8) (z : CycInt) :
    rotate m z = rotate n z := by
  rw [← rotate_mod_eight m, ← rotate_mod_eight n, h]

/-- Every rotation is invertible: rotating by `8 - (j % 8)` undoes a rotation by `j`. -/
theorem rotate_left_inverse (j : ℕ) (z : CycInt) : rotate (8 - j % 8) (rotate j z) = z := by
  rw [← rotate_add, rotate_congr (show (8 - j % 8 + j) % 8 = 0 % 8 by omega)]
  simp

theorem eq_zero_iff {z : CycInt} : z = 0 ↔ z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 := by
  constructor
  · intro h
    subst h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro ⟨ha, hb, hc, hd⟩
    exact ext' ha hb hc hd

/-- **The rotation action is free on nonzero elements.** A nontrivial rotation fixes only `0`:
each of the seven cases forces every coefficient to vanish. -/
theorem eq_zero_of_rotate_eq_self {j : ℕ} (hj0 : 0 < j) (hj8 : j < 8) {z : CycInt}
    (h : rotate j z = z) : z = 0 := by
  obtain ⟨a, b, c, d⟩ := z
  rw [eq_zero_iff]
  show a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0
  interval_cases j
  all_goals
    simp only [rotate, Function.iterate_succ_apply', Function.iterate_zero_apply, timesOmega,
      CycInt.mk.injEq] at h
  all_goals omega

/-! ## The canonical representative of a rotation orbit -/

/-- A linear order on coefficient tuples, lexicographic in `(a, b, c, d)`. Any linear order would
do; this one matches the Rust comparison. -/
def key (z : CycInt) : ℤ ×ₗ ℤ ×ₗ ℤ ×ₗ ℤ :=
  toLex (z.a, toLex (z.b, toLex (z.c, z.d)))

theorem key_injective : Function.Injective key := by
  intro z w h
  simp only [key, toLex_inj, Prod.mk.injEq] at h
  exact ext' h.1 h.2.1 h.2.2.1 h.2.2.2

noncomputable instance : LinearOrder CycInt := LinearOrder.lift' key key_injective

/-- The rotation orbit of `z`: the eight multiples `ωʲ z`. -/
def orbit (z : CycInt) : Finset CycInt := (Finset.range 8).image fun j => rotate j z

theorem self_mem_orbit (z : CycInt) : z ∈ orbit z :=
  Finset.mem_image.2 ⟨0, by simp, by simp⟩

theorem orbit_nonempty (z : CycInt) : (orbit z).Nonempty := ⟨z, self_mem_orbit z⟩

theorem mem_orbit_iff {z w : CycInt} : w ∈ orbit z ↔ ∃ j, w = rotate j z := by
  constructor
  · intro h
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 h
    exact ⟨j, hj.symm⟩
  · intro ⟨j, hj⟩
    refine Finset.mem_image.2 ⟨j % 8, Finset.mem_range.2 (Nat.mod_lt _ (by norm_num)), ?_⟩
    rw [rotate_mod_eight, ← hj]

/-- Rotating a tuple does not change its orbit. -/
theorem orbit_rotate (i : ℕ) (z : CycInt) : orbit (rotate i z) = orbit z := by
  apply Finset.ext
  intro w
  simp only [mem_orbit_iff]
  constructor
  · intro ⟨j, hj⟩
    exact ⟨j + i, by rw [hj, rotate_add]⟩
  · intro ⟨j, hj⟩
    refine ⟨j + (8 - i % 8), ?_⟩
    rw [← rotate_add, hj]
    exact rotate_congr (show j % 8 = (j + (8 - i % 8) + i) % 8 by omega) z

/-- The canonical representative of `z`'s rotation orbit: the least element under `key`. -/
noncomputable def canon (z : CycInt) : CycInt := (orbit z).min' (orbit_nonempty z)

theorem canon_mem_orbit (z : CycInt) : canon z ∈ orbit z := Finset.min'_mem _ _

theorem exists_rotate_canon (z : CycInt) : ∃ j, canon z = rotate j z :=
  mem_orbit_iff.1 (canon_mem_orbit z)

/-- The canonical form denotes the same operator up to a global phase. -/
theorem exists_toComplex_canon (z : CycInt) :
    ∃ j : ℕ, (canon z).toComplex = omega ^ j * z.toComplex := by
  obtain ⟨j, hj⟩ := exists_rotate_canon z
  exact ⟨j, by rw [hj, toComplex_rotate]⟩

/-- **Invariance.** Multiplying by a power of `ω` does not change the canonical form. This is the
ring-level counterpart of `GlobalPhase.canonicalize_smul`. -/
theorem canon_rotate (i : ℕ) (z : CycInt) : canon (rotate i z) = canon z :=
  le_antisymm
    (Finset.min'_le _ _ (by rw [orbit_rotate]; exact canon_mem_orbit z))
    (Finset.min'_le _ _ (by rw [← orbit_rotate i z]; exact canon_mem_orbit (rotate i z)))

/-- **Completeness.** Two tuples have the same canonical form exactly when one is a power of `ω`
times the other. This is the ring-level counterpart of `GlobalPhase.canonicalize_eq_iff`. -/
theorem canon_eq_iff {z w : CycInt} : canon z = canon w ↔ ∃ j, w = rotate j z := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := exists_rotate_canon z
    obtain ⟨j, hj⟩ := exists_rotate_canon w
    have hij : rotate i z = rotate j w := by rw [← hi, ← hj, h]
    exact ⟨8 - j % 8 + i, by rw [rotate_add, hij, rotate_left_inverse]⟩
  · intro ⟨j, hj⟩
    rw [hj, canon_rotate]

@[simp] theorem canon_zero : canon (0 : CycInt) = 0 := by
  have h : orbit (0 : CycInt) = {0} := by
    apply Finset.ext
    intro w
    simp only [mem_orbit_iff, Finset.mem_singleton]
    constructor
    · intro ⟨j, hj⟩; rw [hj]; simp
    · intro hw; exact ⟨0, by simp [hw]⟩
  simp [canon, h]

@[simp] theorem canon_eq_zero_iff {z : CycInt} : canon z = 0 ↔ z = 0 := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := exists_rotate_canon z
    rw [hj] at h
    exact rotate_eq_zero_iff.1 h
  · intro h; subst h; simp

/-- The power of `ω` that canonicalization multiplies by. -/
noncomputable def canonPow (z : CycInt) : ℕ := (exists_rotate_canon z).choose

theorem rotate_canonPow (z : CycInt) : rotate (canonPow z) z = canon z :=
  ((exists_rotate_canon z).choose_spec).symm

/-- For a nonzero element, two rotations agree exactly when their amounts agree modulo eight.
This is freeness of the action, in the form the matrix-level proofs consume. -/
theorem rotate_eq_iff_mod {z : CycInt} (hz : z ≠ 0) {s t : ℕ} :
    rotate s z = rotate t z ↔ s % 8 = t % 8 := by
  constructor
  · intro h
    have h1 : rotate (8 - t % 8 + s) z = z := by
      rw [rotate_add, h, rotate_left_inverse]
    have h2 : rotate ((8 - t % 8 + s) % 8) z = z := by
      rw [rotate_mod_eight]; exact h1
    by_cases hj : (8 - t % 8 + s) % 8 = 0
    · omega
    · exact absurd (eq_zero_of_rotate_eq_self (Nat.pos_of_ne_zero hj)
        (Nat.mod_lt _ (by norm_num)) h2) hz
  · intro h
    exact rotate_congr h z

end CycInt

/-! ## Matrices over the ring -/

open CycInt

variable {ι : Type*}

/-- Rotate every entry of a matrix by the same power of `ω`: multiplication of the whole matrix
by a global phase, performed inside the ring. -/
def rotateMat (n : ℕ) (M : Matrix ι ι CycInt) : Matrix ι ι CycInt := fun i j => rotate n (M i j)

@[simp] theorem rotateMat_apply (n : ℕ) (M : Matrix ι ι CycInt) (i j : ι) :
    rotateMat n M i j = rotate n (M i j) := rfl

@[simp] theorem rotateMat_zero (M : Matrix ι ι CycInt) : rotateMat 0 M = M := rfl

theorem rotateMat_congr {m n : ℕ} (h : m % 8 = n % 8) (M : Matrix ι ι CycInt) :
    rotateMat m M = rotateMat n M := by
  funext i j
  exact rotate_congr h _

theorem rotateMat_left_inverse (j : ℕ) (M : Matrix ι ι CycInt) :
    rotateMat (8 - j % 8) (rotateMat j M) = M := by
  funext i k
  exact rotate_left_inverse j _

theorem rotateMat_add (m n : ℕ) (M : Matrix ι ι CycInt) :
    rotateMat (m + n) M = rotateMat m (rotateMat n M) := by
  funext i j
  simp [rotate_add]

section Pivot

variable [LinearOrder ι]

/-- Positions in row-major order, the scan order SuperOpt uses. -/
def posLT (p q : ι × ι) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

instance : DecidableRel (posLT (ι := ι)) := fun _ _ => by
  unfold posLT; infer_instance

/-- `IsPivot M p` says `p` holds the first nonzero entry of `M` in row-major order. -/
def IsPivot (M : Matrix ι ι CycInt) (p : ι × ι) : Prop :=
  M p.1 p.2 ≠ 0 ∧ ∀ q, posLT q p → M q.1 q.2 = 0

theorem IsPivot.unique {M : Matrix ι ι CycInt} {p q : ι × ι} (hp : IsPivot M p)
    (hq : IsPivot M q) : p = q := by
  by_contra hne
  rcases lt_trichotomy p.1 q.1 with h | h | h
  · exact hp.1 (hq.2 p (Or.inl h))
  · rcases lt_trichotomy p.2 q.2 with h2 | h2 | h2
    · exact hp.1 (hq.2 p (Or.inr ⟨h, h2⟩))
    · exact hne (Prod.ext h h2)
    · exact hq.1 (hp.2 q (Or.inr ⟨h.symm, h2⟩))
  · exact hq.1 (hp.2 q (Or.inl h))

/-- Rotation moves no entry off or onto zero, so it cannot move the pivot. This is the ring-level
counterpart of `GlobalPhase.IsPivot.smul`. -/
theorem IsPivot.rotateMat {M : Matrix ι ι CycInt} {p : ι × ι} (n : ℕ) (hp : IsPivot M p) :
    IsPivot (rotateMat n M) p := by
  refine ⟨?_, ?_⟩
  · simp only [rotateMat_apply, ne_eq, rotate_eq_zero_iff]
    exact hp.1
  · intro q hq
    simp [hp.2 q hq]

/-- The canonical form of a matrix over the ring: rotate every entry by the power of `ω` that
canonicalizes the pivot entry. Entries stay in the ring, unlike division by the pivot's modulus. -/
noncomputable def canonMat (M : Matrix ι ι CycInt) (p : ι × ι) : Matrix ι ι CycInt :=
  rotateMat (canonPow (M p.1 p.2)) M

theorem canonMat_pivot_eq_canon (M : Matrix ι ι CycInt) (p : ι × ι) :
    canonMat M p p.1 p.2 = canon (M p.1 p.2) := by
  simp [canonMat, rotate_canonPow]

/-- The canonical form is a rotation of the original, hence denotes the same operator up to a
global phase. -/
theorem exists_rotateMat_canonMat (M : Matrix ι ι CycInt) (p : ι × ι) :
    ∃ n, canonMat M p = rotateMat n M := ⟨_, rfl⟩

/-- **Invariance, for the whole matrix.** Rotating a matrix leaves its canonical form unchanged.
This is the ring-level counterpart of `GlobalPhase.canonicalize_smul`; it needs the pivot entry to
be nonzero, which is exactly what makes the rotation amount unique modulo eight. -/
theorem canonMat_rotateMat (n : ℕ) {M : Matrix ι ι CycInt} {p : ι × ι} (hp : M p.1 p.2 ≠ 0) :
    canonMat (rotateMat n M) p = canonMat M p := by
  have hpiv : rotate (canonPow (rotate n (M p.1 p.2)) + n) (M p.1 p.2)
      = rotate (canonPow (M p.1 p.2)) (M p.1 p.2) := by
    rw [rotate_add, rotate_canonPow, canon_rotate, rotate_canonPow]
  have hmod := (rotate_eq_iff_mod hp).1 hpiv
  have h1 : canonMat (rotateMat n M) p
      = rotateMat (canonPow (rotate n (M p.1 p.2)) + n) M := by
    simp only [canonMat, rotateMat_apply, rotateMat_add]
  rw [h1, canonMat, rotateMat_congr hmod]

/-- **Completeness, for the whole matrix.** Two matrices over the ring have the same canonical
form exactly when one is a power of `ω` times the other. This is the ring-level counterpart of
`GlobalPhase.canonicalize_eq_iff`. -/
theorem canonMat_eq_iff {M N : Matrix ι ι CycInt} {p : ι × ι} (hp : M p.1 p.2 ≠ 0) :
    canonMat M p = canonMat N p ↔ ∃ j, N = rotateMat j M := by
  constructor
  · intro h
    refine ⟨8 - canonPow (N p.1 p.2) % 8 + canonPow (M p.1 p.2), ?_⟩
    have : rotateMat (8 - canonPow (N p.1 p.2) % 8 + canonPow (M p.1 p.2)) M
        = rotateMat (8 - canonPow (N p.1 p.2) % 8) (canonMat M p) := by
      rw [rotateMat_add, canonMat]
    rw [this, h, canonMat, rotateMat_left_inverse]
  · intro ⟨j, hj⟩
    rw [hj, canonMat_rotateMat j hp]

/-- The pivot entry decides phase equivalence: two matrices over the ring are related by a
rotation exactly when their pivot entries are, which by `CycInt.canon_eq_iff` is decided by
comparing the canonical forms of those entries alone. -/
theorem canon_pivot_eq_iff {M N : Matrix ι ι CycInt} {p : ι × ι} (n : ℕ)
    (h : N = rotateMat n M) :
    canon (N p.1 p.2) = canon (M p.1 p.2) := by
  rw [h]
  simpa using canon_rotate n (M p.1 p.2)

theorem canonMat_pivot_eq_of_rotateMat {M N : Matrix ι ι CycInt} {p : ι × ι} (n : ℕ)
    (h : N = rotateMat n M) :
    canonMat N p p.1 p.2 = canonMat M p p.1 p.2 := by
  rw [canonMat_pivot_eq_canon, canonMat_pivot_eq_canon, canon_pivot_eq_iff n h]

end Pivot


/-! ## Modulus-one elements of the ring

The remaining step is the number-theoretic fact that licenses working with rotations at all: the
only elements of `ℤ[1/√2, i]` of modulus one are the eight powers of `ω`. The proof is a descent.
Writing `S z` and `T z` for the two integer invariants below, the squared modulus of `z` is
`S z + √2 * T z`; since `√2` is irrational, an integer modulus forces `T z = 0`, and then a parity
argument shows `z` is divisible by `√2` whenever `S z` is even, driving the induction down to
`S z = 1`.
-/

namespace CycInt

/-- The rational part of the squared modulus. -/
def S (z : CycInt) : ℤ := z.a ^ 2 + z.b ^ 2 + z.c ^ 2 + z.d ^ 2

/-- The `√2` part of the squared modulus. -/
def T (z : CycInt) : ℤ := z.a * (z.b - z.d) + z.c * (z.b + z.d)

theorem omega_cube : omega ^ 3 = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (Complex.I - 1) := by
  have h : omega ^ 3 = omega ^ 2 * omega := by ring
  rw [h, omega_sq, omega_eq]
  linear_combination ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I_sq

theorem toComplex_re (z : CycInt) :
    z.toComplex.re = (z.a : ℝ) + Real.sqrt 2 / 2 * ((z.b : ℝ) - (z.d : ℝ)) := by
  rw [toComplex, omega_cube, omega_sq, omega_eq]
  simp
  ring

theorem toComplex_im (z : CycInt) :
    z.toComplex.im = (z.c : ℝ) + Real.sqrt 2 / 2 * ((z.b : ℝ) + (z.d : ℝ)) := by
  rw [toComplex, omega_cube, omega_sq, omega_eq]
  simp
  ring

theorem normSq_toComplex (z : CycInt) :
    Complex.normSq z.toComplex = (S z : ℝ) + Real.sqrt 2 * (T z : ℝ) := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [Complex.normSq_apply, toComplex_re, toComplex_im]
  simp only [S, T]
  push_cast
  linear_combination ((z.b : ℝ) ^ 2 + (z.d : ℝ) ^ 2) / 2 * hs

/-- `√2` is irrational, so `s + √2 t` is an integer only when `t = 0`. -/
theorem eq_zero_and_eq_of_add_sqrt_two {s t m : ℤ}
    (h : (s : ℝ) + Real.sqrt 2 * (t : ℝ) = (m : ℝ)) : t = 0 ∧ s = m := by
  by_cases ht : t = 0
  · subst ht
    simp only [Int.cast_zero, mul_zero, add_zero] at h
    exact ⟨rfl, by exact_mod_cast h⟩
  · exfalso
    have h1 : (t : ℝ) * Real.sqrt 2 = ((m - s : ℤ) : ℝ) := by push_cast; linarith
    have h2 : Irrational ((t : ℝ) * Real.sqrt 2) := irrational_sqrt_two.intCast_mul ht
    rw [h1] at h2
    exact (Int.not_irrational _) h2

/-- Four squares summing to one: `z` is a rotation of `1`. -/
theorem eq_rotate_one_of_S_eq_one {z : CycInt} (h : S z = 1) :
    ∃ j, z = rotate j ⟨1, 0, 0, 0⟩ := by
  obtain ⟨a, b, c, d⟩ := z
  simp only [S] at h
  have ha : -1 ≤ a ∧ a ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg d, sq_nonneg (a - 1),
      sq_nonneg (a + 1)]
  have hb : -1 ≤ b ∧ b ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg a, sq_nonneg c, sq_nonneg d, sq_nonneg (b - 1),
      sq_nonneg (b + 1)]
  have hc : -1 ≤ c ∧ c ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg d, sq_nonneg (c - 1),
      sq_nonneg (c + 1)]
  have hd : -1 ≤ d ∧ d ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (d - 1),
      sq_nonneg (d + 1)]
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  obtain ⟨hd1, hd2⟩ := hd
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
    first
      | omega
      | exact ⟨0, by decide⟩
      | exact ⟨1, by decide⟩
      | exact ⟨2, by decide⟩
      | exact ⟨3, by decide⟩
      | exact ⟨4, by decide⟩
      | exact ⟨5, by decide⟩
      | exact ⟨6, by decide⟩
      | exact ⟨7, by decide⟩

theorem exists_omega_pow_of_S_eq_one {z : CycInt} (h : S z = 1) :
    ∃ j, z.toComplex = omega ^ j := by
  obtain ⟨j, hj⟩ := eq_rotate_one_of_S_eq_one h
  refine ⟨j, ?_⟩
  rw [hj, toComplex_rotate]
  simp [toComplex]

/-! ### Division by `√2` -/

/-- Multiplication by `√2 = ω - ω³`, on coefficients. -/
def timesSqrt2 (z : CycInt) : CycInt := ⟨z.b - z.d, z.a + z.c, z.b + z.d, z.c - z.a⟩

theorem toComplex_timesSqrt2 (z : CycInt) :
    (timesSqrt2 z).toComplex = ((Real.sqrt 2 : ℝ) : ℂ) * z.toComplex := by
  rw [sqrt_two_eq]
  simp only [toComplex, timesSqrt2]
  push_cast
  linear_combination ((z.b : ℂ) - (z.d : ℂ) + (z.c : ℂ) * omega + (z.d : ℂ) * omega ^ 2) *
    omega_pow_four

/-- A tuple whose coefficients pair up in parity is divisible by `√2`. -/
theorem exists_timesSqrt2 {z : CycInt} (hac : (z.a + z.c) % 2 = 0) (hbd : (z.b + z.d) % 2 = 0) :
    ∃ w, timesSqrt2 w = z := by
  refine ⟨⟨(z.b - z.d) / 2, (z.a + z.c) / 2, (z.b + z.d) / 2, (z.c - z.a) / 2⟩, ?_⟩
  apply ext' <;> simp only [timesSqrt2] <;> omega

/-- `x² ≡ x` modulo two. -/
theorem sq_sub_self_even (x : ℤ) : (x ^ 2 - x) % 2 = 0 := by
  rcases Int.even_or_odd x with ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> ring_nf <;> omega

/-- The descent hypothesis: an even `S` with vanishing `T` forces both parities to match. -/
theorem parities_of_even_S {z : CycInt} (hS : S z % 2 = 0) (hT : T z = 0) :
    (z.a + z.c) % 2 = 0 ∧ (z.b + z.d) % 2 = 0 := by
  obtain ⟨a, b, c, d⟩ := z
  show (a + c) % 2 = 0 ∧ (b + d) % 2 = 0
  simp only [S] at hS
  simp only [T] at hT
  have hsum : (a + b + c + d) % 2 = 0 := by
    have h1 := sq_sub_self_even a
    have h2 := sq_sub_self_even b
    have h3 := sq_sub_self_even c
    have h4 := sq_sub_self_even d
    omega
  have hprod : (a + c) * (b + d) = 2 * (a * d) := by linear_combination hT
  have heven : ((a + c) * (b + d)) % 2 = 0 := by rw [hprod]; omega
  rcases Int.even_mul.1 (Int.even_iff.2 heven) with hh | hh
  · have hac := Int.even_iff.1 hh
    exact ⟨by omega, by omega⟩
  · have hbd := Int.even_iff.1 hh
    exact ⟨by omega, by omega⟩

/-- **Modulus-one elements are rotations.** If the squared modulus of `z` is `2^k`, then `z`
denotes `ωʲ √2^k` for some `j`. -/
theorem exists_omega_pow_of_normSq : ∀ (k : ℕ) (z : CycInt),
    Complex.normSq z.toComplex = 2 ^ k →
      ∃ j, z.toComplex = omega ^ j * ((Real.sqrt 2 : ℝ) : ℂ) ^ k := by
  intro k
  induction k with
  | zero =>
      intro z hz
      have h : (S z : ℝ) + Real.sqrt 2 * (T z : ℝ) = ((1 : ℤ) : ℝ) := by
        rw [← normSq_toComplex]; simpa using hz
      obtain ⟨-, hS⟩ := eq_zero_and_eq_of_add_sqrt_two h
      obtain ⟨j, hj⟩ := exists_omega_pow_of_S_eq_one hS
      exact ⟨j, by simpa using hj⟩
  | succ k ih =>
      intro z hz
      have h : (S z : ℝ) + Real.sqrt 2 * (T z : ℝ) = ((2 ^ (k + 1) : ℤ) : ℝ) := by
        rw [← normSq_toComplex, hz]; push_cast; ring
      obtain ⟨hT, hS⟩ := eq_zero_and_eq_of_add_sqrt_two h
      have hSeven : S z % 2 = 0 := by
        rw [hS]
        have hp : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
        rw [hp]
        omega
      obtain ⟨hac, hbd⟩ := parities_of_even_S hSeven hT
      obtain ⟨w, hw⟩ := exists_timesSqrt2 hac hbd
      have hnorm : Complex.normSq w.toComplex = 2 ^ k := by
        have h2 : Complex.normSq z.toComplex = 2 * Complex.normSq w.toComplex := by
          rw [← hw, toComplex_timesSqrt2, Complex.normSq_mul, Complex.normSq_ofReal,
            Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
        rw [hz] at h2
        have hpow : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
        rw [hpow] at h2
        linarith
      obtain ⟨j, hj⟩ := ih w hnorm
      refine ⟨j, ?_⟩
      rw [← hw, toComplex_timesSqrt2, hj]
      ring

/-- **The characterization.** The only elements of `ℤ[1/√2, i]` of modulus one are the eight
powers of `ω`. This is what licenses replacing an arbitrary global phase `e^{iθ}` between two
Clifford+T unitaries by a rotation, and so connects this file to
`SuperOpt.GlobalPhase.canonicalize_eq_iff`. -/
theorem exists_omega_pow_of_isCyclotomic_of_norm_one {x : ℂ} (hx : IsCyclotomic x)
    (h1 : ‖x‖ = 1) : ∃ j : ℕ, x = omega ^ j := by
  obtain ⟨a, b, c, d, k, rfl⟩ := hx
  have hz : ((a : ℂ) + b * omega + c * omega ^ 2 + d * omega ^ 3)
      = (CycInt.mk a b c d).toComplex := by
    simp [toComplex]
  rw [hz] at h1 ⊢
  have hsne : Complex.normSq (((Real.sqrt 2 : ℝ) : ℂ) ^ k) = 2 ^ k := by
    rw [map_pow, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have h1' : Complex.normSq ((CycInt.mk a b c d).toComplex / ((Real.sqrt 2 : ℝ) : ℂ) ^ k) = 1 := by
    rw [Complex.normSq_eq_norm_sq, h1]; norm_num
  have hknz : Complex.normSq (((Real.sqrt 2 : ℝ) : ℂ) ^ k) ≠ 0 := by
    rw [hsne]; positivity
  have hnormSq : Complex.normSq (CycInt.mk a b c d).toComplex = 2 ^ k := by
    rw [Complex.normSq_div, div_eq_one_iff_eq hknz] at h1'
    rw [h1', hsne]
  obtain ⟨j, hj⟩ := exists_omega_pow_of_normSq k _ hnormSq
  refine ⟨j, ?_⟩
  rw [hj]
  have : ((Real.sqrt 2 : ℝ) : ℂ) ^ k ≠ 0 := by
    apply pow_ne_zero
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  field_simp

end CycInt

end Tzap.Cyclotomic
