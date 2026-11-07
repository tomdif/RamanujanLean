/-
# Power-saving Rankin–Selberg for every level-one cusp form

For `f ∈ S_k(SL₂(ℤ))`, `G_f = |f|²y^k` is an `RSFn` with `m = k − 1`, `cₙ = |a_f(n)|²`
(`rsFnCusp`): Parseval is `RankinSelberg.hasSum_normSq_coeff`, cusp decay comes from
`CuspFormClass.exp_decay_atImInfty'`. Hence (`rankinSelberg_power_saving_general`), for every
weight `k`,

    |∑_{n≤N} |a_f(n)|²/n^{k−1} − c_f N| ≤ C_f N^{1−1/84},   c_f = (3/π)(4π)^k‖f‖²/(k−1)!.

For `k < 12` the space `S_k` is zero (Mathlib `CuspForm.rank_eq_zero_of_weight_lt_twelve`) and the
statement is trivial; for `k ≥ 12` it is `power_saving_RSFn` (which needs `m = k − 1 ≥ 2`).
-/
import RamanujanTau.RankinErrorGeneral.UnfoldProofG
import RamanujanTau.RankinSelbergGeneral.Main

set_option autoImplicit false

namespace RamanujanTau.RankinErrorGeneral

open Finset Real Filter Topology MeasureTheory
open Complex ModularForm
open RamanujanTau.RankinSelberg hiding G G_smul continuous_G G_pos
open RamanujanTau.RankinSelbergGeneral
open UpperHalfPlane hiding I
open scoped MatrixGroups

variable {k : ℕ}

/-- Exponential decay of `G_f = |f|²y^k` at the cusp. -/
lemma exists_Gf_exp_le (f : CuspForm 𝒮ℒ (k : ℤ)) : ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ z : ℍ,
    1 / 2 ≤ z.im → Gf f z ≤ K * Real.exp (-c * z.im) := by
  obtain ⟨c, hc, hO⟩ := CuspFormClass.exp_decay_atImInfty' f
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1 hC
  obtain ⟨M, hM0, hM⟩ := exists_Gf_le f
  set c₁ := c / 2 with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  set A' := max A 1
  refine ⟨|C| ^ 2 * (Nat.factorial k : ℝ) / c₁ ^ k + M * Real.exp (c₁ * A'), c₁, by positivity,
    hc₁0, fun z hz => ?_⟩
  have hy0 : 0 < z.im := z.im_pos
  rcases le_or_gt A' z.im with h | h
  · have hb := hA z ((le_max_left _ _).trans h)
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hb
    have h1 : ‖f z‖ ^ 2 ≤ |C| ^ 2 * Real.exp (-c * z.im) ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
        (Real.exp_pos _).le)) 2
    have h2 : z.im ^ k * Real.exp (-c₁ * z.im) ≤ (Nat.factorial k : ℝ) / c₁ ^ k := by
      have := Real.pow_div_factorial_le_exp (x := c₁ * z.im) (by positivity) k
      rw [mul_pow] at this
      have he : Real.exp (-c₁ * z.im) * Real.exp (c₁ * z.im) = 1 := by
        rw [← Real.exp_add]; simp
      rw [le_div_iff₀ (by positivity)]
      calc z.im ^ k * Real.exp (-c₁ * z.im) * c₁ ^ k
          = (c₁ ^ k * z.im ^ k / (Nat.factorial k : ℝ)) * Real.exp (-c₁ * z.im) *
              (Nat.factorial k : ℝ) := by field_simp
        _ ≤ Real.exp (c₁ * z.im) * Real.exp (-c₁ * z.im) * (Nat.factorial k : ℝ) := by gcongr
        _ = (Nat.factorial k : ℝ) := by rw [mul_comm (Real.exp _), he, one_mul]
    have hexp : Real.exp (-c * z.im) ^ 2 = Real.exp (-c₁ * z.im) * Real.exp (-c₁ * z.im) *
        Real.exp (-c * z.im) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; rw [hc₁]; ring
    unfold Gf
    calc ‖f z‖ ^ 2 * z.im ^ k ≤ |C| ^ 2 * Real.exp (-c * z.im) ^ 2 * z.im ^ k := by gcongr
      _ = |C| ^ 2 * (z.im ^ k * Real.exp (-c₁ * z.im)) * Real.exp (-c₁ * z.im) *
          Real.exp (-c * z.im) := by rw [hexp]; ring
      _ ≤ |C| ^ 2 * ((Nat.factorial k : ℝ) / c₁ ^ k) * Real.exp (-c₁ * z.im) * 1 := by
          gcongr
          · exact Real.exp_le_one_iff.2 (by nlinarith)
      _ ≤ _ := by
          have : 0 ≤ M * Real.exp (c₁ * A') * Real.exp (-c₁ * z.im) := by positivity
          rw [mul_one, add_mul, mul_div_assoc]; linarith
  · have he : 1 ≤ Real.exp (c₁ * A') * Real.exp (-c₁ * z.im) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
    have : Gf f z ≤ M * (Real.exp (c₁ * A') * Real.exp (-c₁ * z.im)) :=
      (hM z).trans (le_mul_of_one_le_right hM0 he)
    have h0 : 0 ≤ |C| ^ 2 * (Nat.factorial k : ℝ) / c₁ ^ k * Real.exp (-c₁ * z.im) := by positivity
    rw [add_mul]; nlinarith

lemma parseval_Gf (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => coeffSq f n * (y ^ (k - 1 + 1) * Real.exp (-(4 * π * n) * y)))
      (∫ x in (0 : ℝ)..1, Gf f (hp hy x)) := by
  have h := (hasSum_normSq_coeff (k := (k : ℤ)) f hy).mul_right (y ^ k)
  have e1 : ∀ n : ℕ, Real.exp (-2 * π * y) ^ (2 * n) = Real.exp (-(4 * π * n) * y) := by
    intro n; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hint : ∫ x in (0 : ℝ)..1, Gf f (hp hy x) = (∫ x in (0 : ℝ)..1, ‖f (hp hy x)‖ ^ 2) * y ^ k := by
    rw [← intervalIntegral.integral_mul_const]
    congr 1; funext x; unfold Gf; rw [hp_im]
  rw [hint, Nat.sub_add_cancel hk]
  convert h using 1
  funext n; unfold coeffSq; rw [e1]; ring

/-- `G_f = |f|²y^k` as an `RSFn` (`m = k − 1`, `cₙ = |a_f(n)|²`). -/
@[reducible] noncomputable def rsFnCusp (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) : RSFn where
  toHoroFn := horoFn f
  m := k - 1
  cf := coeffSq f
  cf_nonneg _ := sq_nonneg _
  cf_zero := by simp [coeffSq, coeff_zero_eq_zero]
  parseval hy := parseval_Gf f hk hy
  exp_decay := exists_Gf_exp_le f

lemma rsConst_eq (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) :
    petNormSqF f * rsConstM (k - 1) = rsConst f := by
  unfold rsConstM rsConst
  rw [Nat.sub_add_cancel hk]
  have hπ := Real.pi_pos
  field_simp

lemma cuspForm_eq_zero_of_lt (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : k < 12) : f = 0 :=
  rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by omega)) f

/-- **Rankin–Selberg with a power saving, for every level-one cusp form:**
`|∑_{n≤N} |a_f(n)|²/n^{k−1} − c_f N| ≤ C_f N^{1−1/84}`, `c_f = (3/π)(4π)^k‖f‖²/(k−1)!`. -/
theorem rankinSelberg_power_saving_general (f : CuspForm 𝒮ℒ (k : ℤ)) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1) - rsConst f * N| ≤
        C * (N : ℝ) ^ (1 - 1 / 84 : ℝ) := by
  rcases lt_or_ge k 12 with hk | hk
  · obtain rfl := cuspForm_eq_zero_of_lt f hk
    refine ⟨0, fun N _ => ?_⟩
    have h1 : ∀ n, coeffSq (0 : CuspForm 𝒮ℒ (k : ℤ)) n = 0 := fun n => by
      simp [coeffSq, qExpansion_zero]
    have h2 : rsConst (0 : CuspForm 𝒮ℒ (k : ℤ)) = 0 := by
      simp [rsConst, petNormSqF, Gf]
    simp [h1, h2]
  · letI := rsFnCusp f (by omega)
    obtain ⟨C, hC⟩ := power_saving_RSFn (show 2 ≤ k - 1 by omega)
    refine ⟨C, fun N hN => ?_⟩
    have h : |∑ n ∈ Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1) -
        petNormSqF f * rsConstM (k - 1) * N| ≤ C * (N : ℝ) ^ (1 - 1 / 84 : ℝ) := hC N hN
    rw [rsConst_eq f (by omega)] at h
    exact h

/-- The same with the explicit constant `(3/π)(4π)^k‖f‖²/(k−1)!`. -/
theorem rankinSelberg_power_saving_general' (f : CuspForm 𝒮ℒ (k : ℤ)) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, ‖(qExpansion 1 f).coeff n‖ ^ 2 / (n : ℝ) ^ (k - 1) -
          3 / π * (4 * π) ^ k * petNormSqF f / (Nat.factorial (k - 1) : ℝ) * N| ≤
        C * (N : ℝ) ^ (1 - 1 / 84 : ℝ) :=
  rankinSelberg_power_saving_general f

/-! ### Consistency with `RankinError` at `f = Δ` -/

/-- **At `f = Δ` the general theorem gives `RankinError.rankinSelberg_power_saving_84`**
(same statement, same constant `(3/π)(4π)¹²‖Δ‖²/11!`). -/
theorem rankinSelberg_power_saving_discriminant :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ (1 - 1 / 84 : ℝ) := by
  obtain ⟨C, hC⟩ := rankinSelberg_power_saving_general (k := 12)
    (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ))
  refine ⟨C, fun N hN => ?_⟩
  have h := hC N hN
  have e : ∀ n, coeffSq (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) n =
      ((tau n : ℝ)) ^ 2 := fun n => by
    unfold coeffSq
    have e := TauBound.qExpansion_discriminant_coeff_tau n
    erw [e, Complex.norm_intCast, sq_abs]
  simp only [e, rsConst, petNormSqF_discriminant] at h
  exact h

/-- The statement coincides with the one already proved in `RankinError/`. -/
example : (∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ (1 - 1 / 84 : ℝ)) :=
  RankinError.rankinSelberg_power_saving_84

end RamanujanTau.RankinErrorGeneral

#print axioms RamanujanTau.RankinErrorGeneral.rankinSelberg_power_saving_general
#print axioms RamanujanTau.RankinErrorGeneral.rankinSelberg_power_saving_discriminant
