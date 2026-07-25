import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The Cyclotomic Ring `ℤ[ω][1/√2]`

This file formalizes the exact number representation `src/super_opt/matrix.rs` uses for
Clifford+T window matrices, and proves it is closed under the ring operations.

SuperOpt stores each matrix entry as

```text
(a + b*omega + c*omega^2 + d*omega^3) / sqrt(2)^k
```

with `omega = exp(i*pi/4)`, `omega^4 = -1`, four integer coefficients `a, b, c, d` (the Rust
`Cyclotomic { coefficients: [i8; 4] }`) and one denominator exponent `k` shared by the whole
matrix. `IsCyclotomic` below is exactly that predicate on a complex number, with `ℤ` in place of
`i8` — the Rust code additionally tracks overflow of the `i8` window and conservatively skips a
window when a coefficient escapes it, which is a representability *restriction* on top of the
mathematical statement proved here.

The main results are the closure lemmas `IsCyclotomic.add`, `IsCyclotomic.mul` and
`IsCyclotomic.sum`. They are what `TZap/Cyclotomic/Semantics.lean` needs: circuit semantics is
built from sums of products of gate entries, so a set containing every gate entry and closed
under `+` and `*` contains every circuit amplitude.

Only what the main theorem depends on is kept here; the representable numbers do also form a
subring of `ℂ`, but nothing downstream needed that packaging.

## Correspondence with the Rust implementation

| Lean | Rust (`src/super_opt/matrix.rs`) |
| --- | --- |
| `omega` | `omega = exp(i*pi/4)` |
| `(a, b, c, d)` in `IsCycInt` | `Cyclotomic { coefficients: [i8; 4] }` |
| `omega_pow_four : ω^4 = -1` | the `omega^4 = -1` reduction in `times_omega` |
| `IsCycInt.omega_mul` | `Cyclotomic::times_omega` at `power = 1` |
| `k` in `IsCyclotomic` | `denominator_exponent` |
| `sqrt_two_eq : √2 = ω - ω³` | the `sqrt(2) = omega - omega^3` identity behind `divide_by_sqrt_2` |
-/

namespace TZap.Cyclotomic

noncomputable section

/-- `ω = exp(iπ/4)`, a primitive eighth root of unity — SuperOpt's `omega`.

The exponent is written `I * ↑θ` to match `Semantics.phase`, so that an `Rz (kπ/4)` amplitude is
literally a power of `ω`. -/
def omega : ℂ := Complex.exp (Complex.I * ((Real.pi / 4 : ℝ) : ℂ))

/-- `(√2)² = 2` in `ℂ`; used to put `ω` in Cartesian form. -/
theorem ofReal_sqrt_two_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- Cartesian form of `ω`: `(√2/2)(1 + i)`. -/
theorem omega_eq : omega = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + Complex.I) := by
  rw [omega, mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast
  ring

/-- `ω² = i`. -/
theorem omega_sq : omega ^ 2 = Complex.I := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := ofReal_sqrt_two_sq
  rw [omega_eq]
  push_cast
  linear_combination ((1 + Complex.I) ^ 2 / 4) * h2 + (1 / 2 : ℂ) * Complex.I_sq

/-- `ω⁴ = -1`: the reduction rule Rust's `times_omega` implements as a signed rotation of the
coefficient array. -/
theorem omega_pow_four : omega ^ 4 = -1 := by
  have h : omega ^ 4 = (omega ^ 2) ^ 2 := by ring
  rw [h, omega_sq, Complex.I_sq]

/-- `√2 = ω - ω³`. This is why a `√2` denominator can always be cleared into the numerator, and
it is the identity underlying Rust's exact `divide_by_sqrt_2`. -/
theorem sqrt_two_eq : ((Real.sqrt 2 : ℝ) : ℂ) = omega - omega ^ 3 := by
  have h3 : omega ^ 3 = omega * omega ^ 2 := by ring
  rw [h3, omega_sq, omega_eq]
  push_cast
  linear_combination (((Real.sqrt 2 : ℝ) : ℂ) / 2) * Complex.I_sq

/-! ## The cyclotomic integers `ℤ[ω]` -/

/-- The numerator ring `ℤ[ω]`: numbers of the form `a + bω + cω² + dω³` with integer
coefficients. This is the Rust `Cyclotomic` struct's value, before the `√2` denominator. -/
def IsCycInt (z : ℂ) : Prop :=
  ∃ a b c d : ℤ, z = (a : ℂ) + b * omega + c * omega ^ 2 + d * omega ^ 3

namespace IsCycInt

theorem zero : IsCycInt 0 := ⟨0, 0, 0, 0, by norm_num⟩

theorem one : IsCycInt 1 := ⟨1, 0, 0, 0, by norm_num⟩

theorem omega_mem : IsCycInt omega := ⟨0, 1, 0, 0, by norm_num⟩

theorem add {x y : ℂ} (hx : IsCycInt x) (hy : IsCycInt y) : IsCycInt (x + y) := by
  obtain ⟨a, b, c, d, rfl⟩ := hx
  obtain ⟨a', b', c', d', rfl⟩ := hy
  exact ⟨a + a', b + b', c + c', d + d', by push_cast; ring⟩

/-- Scaling by an integer. -/
theorem intCast_mul {x : ℂ} (hx : IsCycInt x) (m : ℤ) : IsCycInt ((m : ℂ) * x) := by
  obtain ⟨a, b, c, d, rfl⟩ := hx
  exact ⟨m * a, m * b, m * c, m * d, by push_cast; ring⟩

/-- Multiplication by `ω` — the coefficient rotation `(a, b, c, d) ↦ (-d, a, b, c)`, which is
exactly Rust's `times_omega` at `power = 1`. -/
theorem omega_mul {x : ℂ} (hx : IsCycInt x) : IsCycInt (omega * x) := by
  obtain ⟨a, b, c, d, rfl⟩ := hx
  refine ⟨-d, a, b, c, ?_⟩
  push_cast
  linear_combination (d : ℂ) * omega_pow_four

/-- `ℤ[ω]` is closed under multiplication: expand the right factor over the basis
`1, ω, ω², ω³` and apply `omega_mul` repeatedly. -/
theorem mul {x y : ℂ} (hx : IsCycInt x) (hy : IsCycInt y) : IsCycInt (x * y) := by
  obtain ⟨a, b, c, d, rfl⟩ := hy
  have h1 := hx
  have h2 := hx.omega_mul
  have h3 := hx.omega_mul.omega_mul
  have h4 := hx.omega_mul.omega_mul.omega_mul
  have hx4 : x * ((a : ℂ) + b * omega + c * omega ^ 2 + d * omega ^ 3)
      = (a : ℂ) * x + (b : ℂ) * (omega * x) + (c : ℂ) * (omega * (omega * x))
        + (d : ℂ) * (omega * (omega * (omega * x))) := by ring
  rw [hx4]
  exact (((h1.intCast_mul a).add (h2.intCast_mul b)).add (h3.intCast_mul c)).add
    (h4.intCast_mul d)

theorem pow {x : ℂ} (hx : IsCycInt x) : ∀ k : ℕ, IsCycInt (x ^ k)
  | 0 => by simpa using one
  | k + 1 => by
      rw [pow_succ]
      exact (hx.pow k).mul hx

/-- `√2` lies in `ℤ[ω]`, as `ω - ω³`. -/
theorem sqrt_two : IsCycInt ((Real.sqrt 2 : ℝ) : ℂ) :=
  ⟨0, 1, 0, -1, by rw [sqrt_two_eq]; push_cast; ring⟩

end IsCycInt

/-! ## The full representation `ℤ[ω][1/√2]` -/

/-- **SuperOpt's exact entry format.** `z` is representable cyclotomically when it is an
integer combination of `1, ω, ω², ω³` divided by a power of `√2`:

```text
z = (a + b*omega + c*omega^2 + d*omega^3) / sqrt(2)^k
```

`(a, b, c, d)` is the Rust `Cyclotomic` coefficient array and `k` the `denominator_exponent`. -/
def IsCyclotomic (z : ℂ) : Prop :=
  ∃ (a b c d : ℤ) (k : ℕ),
    z = ((a : ℂ) + b * omega + c * omega ^ 2 + d * omega ^ 3) / ((Real.sqrt 2 : ℝ) : ℂ) ^ k

/-- Repackaging of `IsCyclotomic` in terms of `IsCycInt`, which is what the closure proofs
manipulate. -/
theorem isCyclotomic_iff {z : ℂ} :
    IsCyclotomic z ↔ ∃ (N : ℂ) (k : ℕ), IsCycInt N ∧ z = N / ((Real.sqrt 2 : ℝ) : ℂ) ^ k := by
  constructor
  · rintro ⟨a, b, c, d, k, rfl⟩
    exact ⟨_, k, ⟨a, b, c, d, rfl⟩, rfl⟩
  · rintro ⟨N, k, ⟨a, b, c, d, rfl⟩, rfl⟩
    exact ⟨a, b, c, d, k, rfl⟩

namespace IsCyclotomic

theorem of_isCycInt {z : ℂ} (hz : IsCycInt z) : IsCyclotomic z :=
  isCyclotomic_iff.2 ⟨z, 0, hz, by simp⟩

theorem zero : IsCyclotomic 0 := of_isCycInt IsCycInt.zero

theorem one : IsCyclotomic 1 := of_isCycInt IsCycInt.one

theorem omega_mem : IsCyclotomic omega := of_isCycInt IsCycInt.omega_mem

/-- Closure under addition: put both entries over the larger denominator by pushing the
difference of exponents into the numerator, which stays in `ℤ[ω]` because `√2` does. -/
theorem add {x y : ℂ} (hx : IsCyclotomic x) (hy : IsCyclotomic y) : IsCyclotomic (x + y) := by
  obtain ⟨M, k, hM, rfl⟩ := isCyclotomic_iff.1 hx
  obtain ⟨N, l, hN, rfl⟩ := isCyclotomic_iff.1 hy
  rcases le_total k l with h | h
  · refine isCyclotomic_iff.2
      ⟨M * ((Real.sqrt 2 : ℝ) : ℂ) ^ (l - k) + N, l,
        (hM.mul (IsCycInt.sqrt_two.pow _)).add hN, ?_⟩
    have hpow : ((Real.sqrt 2 : ℝ) : ℂ) ^ l
        = ((Real.sqrt 2 : ℝ) : ℂ) ^ (l - k) * ((Real.sqrt 2 : ℝ) : ℂ) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel h]
    rw [hpow]
    field_simp
  · refine isCyclotomic_iff.2
      ⟨M + N * ((Real.sqrt 2 : ℝ) : ℂ) ^ (k - l), k,
        hM.add (hN.mul (IsCycInt.sqrt_two.pow _)), ?_⟩
    have hpow : ((Real.sqrt 2 : ℝ) : ℂ) ^ k
        = ((Real.sqrt 2 : ℝ) : ℂ) ^ (k - l) * ((Real.sqrt 2 : ℝ) : ℂ) ^ l := by
      rw [← pow_add, Nat.sub_add_cancel h]
    rw [hpow]
    field_simp

/-- Closure under multiplication: numerators multiply in `ℤ[ω]`, denominator exponents add. -/
theorem mul {x y : ℂ} (hx : IsCyclotomic x) (hy : IsCyclotomic y) : IsCyclotomic (x * y) := by
  obtain ⟨M, k, hM, rfl⟩ := isCyclotomic_iff.1 hx
  obtain ⟨N, l, hN, rfl⟩ := isCyclotomic_iff.1 hy
  refine isCyclotomic_iff.2 ⟨M * N, k + l, hM.mul hN, ?_⟩
  rw [pow_add]
  field_simp

theorem pow {x : ℂ} (hx : IsCyclotomic x) : ∀ k : ℕ, IsCyclotomic (x ^ k)
  | 0 => by simpa using one
  | k + 1 => by
      rw [pow_succ]
      exact (hx.pow k).mul hx

/-- Closure under finite sums — the form the circuit-semantics induction consumes, since
`WeightedRelation.comp` sums over the intermediate basis. -/
theorem sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, IsCyclotomic (f i)) :
    IsCyclotomic (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end IsCyclotomic

end
end TZap.Cyclotomic
