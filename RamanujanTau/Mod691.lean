/-
# Ramanujan's congruence `τ(n) ≡ σ₁₁(n) (mod 691)` — the modular-forms argument

Weight-12 level-one modular forms `M₁₂` are 2-dimensional. Both `E₄³` and the normalized weight-12
Eisenstein series `E₁₂` have constant term `1`, so `E₄³ − E₁₂` has constant term `0` and is therefore a cusp
form, hence a scalar multiple of `Δ`. Matching the `q¹` coefficient (`E₄³`: `720`, `E₁₂`: `65520/691`,
`Δ`: `τ(1)=1`) gives

  `E₄³ = E₁₂ + (432000/691)·Δ`.

Reading off the `qⁿ` coefficient (`n ≥ 1`): `a(n) = (65520/691)σ₁₁(n) + (432000/691)τ(n)` where `a(n)` is an
integer (`E₄³` has integer q-expansion). Since `65520 + 432000 = 720·691`, clearing `691` gives
`432000(τ(n) − σ₁₁(n)) ≡ 0 (mod 691)`, and `691 ∤ 432000` yields `τ(n) ≡ σ₁₁(n) (mod 691)`.

This file builds the argument on Mathlib's modular-forms library. **Milestone 1 (here):** the `E₁₂`
q-expansion coefficient `(65520/691)·σ₁₁`.
-/
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.DimensionFormulas.LevelOne

namespace RamanujanTau.Mod691

open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane
open scoped MatrixGroups ArithmeticFunction.sigma

/-- The normalized weight-12 Eisenstein series `E₁₂` for `SL₂(ℤ)`. -/
noncomputable def E12 := E (show 3 ≤ 12 by norm_num)

/-- `B₁₂ = −691/2730`. -/
lemma bernoulli_twelve : bernoulli 12 = -691 / 2730 := by decide +kernel

/-- **Milestone 1: the `E₁₂` q-expansion carries `691`.** For `m ≥ 1`,
`(E₁₂)_m = (65520/691)·σ₁₁(m)`. -/
lemma E12_qExpansion_coeff {m : ℕ} (hm : m ≠ 0) :
    (qExpansion 1 E12).coeff m = (65520 / 691 : ℂ) * (σ 11 m : ℂ) := by
  rw [E12, E_qExpansion_coeff (show 3 ≤ 12 by norm_num) (by decide) m, if_neg hm,
      bernoulli_twelve]
  norm_num

/-! ### Milestone 2: the `E₄³` q-expansion (constant term `1`, `q¹`-coefficient `720`) -/

/-- `E₄`'s q-expansion constant term is `1`. -/
lemma qE4_coeff_zero : (qExpansion 1 E₄).coeff 0 = 1 := E_qExpansion_coeff_zero _ ⟨2, rfl⟩

/-- `E₄³` has constant term `1`. -/
lemma qE4cube_coeff_zero : ((qExpansion 1 E₄) ^ 3).coeff 0 = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff,
      qE4_coeff_zero, one_pow]

/-- `E₄³` has `q¹`-coefficient `720 = 3·240`. -/
lemma qE4cube_coeff_one : ((qExpansion 1 E₄) ^ 3).coeff 1 = 720 := by
  have h0 := qE4_coeff_zero
  have h1 : (qExpansion 1 E₄).coeff 1 = 240 := E₄_qExpansion_coeff_one
  have hp2_0 : ((qExpansion 1 E₄) ^ 2).coeff 0 = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff,
        h0, one_pow]
  have hp2_1 : ((qExpansion 1 E₄) ^ 2).coeff 1 = 480 := by
    rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ, Finset.sum_range_one, h0, h1]
    ring
  rw [pow_succ, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Finset.sum_range_one, hp2_0, hp2_1, h0, h1]
  ring

end RamanujanTau.Mod691
