/-
# The power saving `1/84` from the weight-`(m+1)` Rankin–Selberg data

Generalizes `RankinError/Landau3.lean` and `power_saving_84_of_RSData` (`m = 11`).
`power_saving_84_of_RSDataM`: if `m ≥ 2`, `a ≥ 0`, `a 0 = 0`, `∑ aₙ n^{−5/2} < ∞` and `RSDataM m a κ`,
then `|∑_{n≤N} aₙ − κ c_m N| ≤ C N^{1 − 1/84}` with `c_m = 3(4π)^{m+1}/(π m!)`.
-/
import RamanujanTau.RankinErrorGeneral.PL
import RamanujanTau.RankinError.RieszK

set_option autoImplicit false

namespace RamanujanTau.RankinErrorGeneral

open Complex Real MeasureTheory Set Filter Topology
open RamanujanTau.RankinError

/-- `g(s) = γ(s)⁻¹ ζ(2s)⁻¹`. -/
noncomputable def gfunM (m : ℕ) (s : ℂ) : ℂ := invGamM m s * (riemannZeta (2 * s))⁻¹

/-- The residue constant `3 (4π)^{m+1} / (π · m!)`. -/
noncomputable def rsConstM (m : ℕ) : ℝ := 3 * (4 * π) ^ (m + 1) / (π * (Nat.factorial m : ℝ))

lemma gfunM_one (m : ℕ) : gfunM m 1 = (rsConstM m : ℂ) := by
  unfold gfunM invGamM rsConstM
  rw [mul_one, riemannZeta_two, cpow_one, Complex.Gamma_one,
    show (1 : ℂ) + m = (m : ℂ) + 1 by ring, Complex.Gamma_nat_eq_factorial,
    show (m : ℂ) + 1 = ((m + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast]
  have hπ : (π : ℂ) ≠ 0 := pi_ne_zero'
  have hf : ((Nat.factorial m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  push_cast
  field_simp
  ring

lemma differentiableOn_gfunM (m : ℕ) : DifferentiableOn ℂ (gfunM m) {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  simp only [mem_setOf_eq] at hs
  have h2 : 1 < (2 * s).re := by simp; linarith
  have hz : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h2
  have hz' : DifferentiableAt ℂ (fun s : ℂ => riemannZeta (2 * s)) s := by
    have : 2 * s ≠ 1 := by intro h; rw [h] at h2; simp at h2
    exact (differentiableAt_riemannZeta this).comp s (differentiableAt_id.const_mul 2)
  exact ((differentiable_invGamM m s).mul (hz'.inv hz)).differentiableWithinAt

section F

variable {m : ℕ} {a : ℕ → ℝ} {κ : ℝ} (d : RSDataM m a κ)

/-- `F(s) = (Λ₀(s) − κ/s) g(s) + κ (g(s) − g(1))/(s − 1)`, holomorphic on `Re s > 1/2`. -/
noncomputable def FfunM (s : ℂ) : ℂ := (d.Λ₀ s - κ / s) * gfunM m s + κ * dslope (gfunM m) 1 s

lemma differentiableOn_FfunM : DifferentiableOn ℂ (FfunM d) {s : ℂ | 1 / 2 < s.re} := by
  have hU : {s : ℂ | 1 / 2 < s.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp; norm_num)
  have hdsl := (differentiableOn_dslope hU).2 (differentiableOn_gfunM m)
  intro s hs
  simp only [mem_setOf_eq] at hs
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  refine DifferentiableWithinAt.add ?_ ((hdsl s hs).const_mul _)
  refine DifferentiableWithinAt.mul ?_ (differentiableOn_gfunM m s hs)
  exact ((d.diff s).sub ((differentiableAt_const _).div differentiableAt_id hs0)).differentiableWithinAt

lemma FfunM_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    FfunM d s = (d.Λ₀ s + κ * (1 / (s - 1) - 1 / s)) * gfunM m s - (κ * rsConstM m : ℝ) / (s - 1) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 h1
  unfold FfunM
  rw [dslope_of_ne _ h1, slope_def_field, gfunM_one]
  push_cast
  field_simp
  ring

lemma LSeries_eq_FfunM {s : ℂ} (hs : 2 < s.re) :
    LSeries (fun n => (a n : ℂ)) s = FfunM d s + (κ * rsConstM m : ℝ) / (s - 1) := by
  have h0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs <;> linarith
  have h1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs <;> linarith
  rw [FfunM_eq d h0 h1, ← d.unfold s hs, sub_add_cancel]
  have hz : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  have hg := gamM_mul_invGamM m (s := s) (by linarith)
  unfold gfunM
  field_simp
  linear_combination (-(LSeries (fun n => (a n : ℂ)) s)) * hg

variable (hsum : LSeriesSummable (fun n => (a n : ℂ)) ((5 / 2 : ℝ) : ℂ)) (hm : 2 ≤ m)

include hsum hm in
lemma FfunM_bound : ∃ B : ℝ, ∀ s : ℂ, 3 / 4 ≤ s.re → s.re ≤ 5 / 2 →
    ‖FfunM d s‖ ≤ B * (1 + |s.im|) ^ 19 := by
  obtain ⟨C, hC⟩ := fPLM_bound d hsum hm
  obtain ⟨Z, hZ0, hZ⟩ := exists_norm_inv_zeta_le
  -- the compact part `|Im s| ≤ 1`
  have hK : IsCompact (Icc (3 / 4 : ℝ) (5 / 2) ×ℂ Icc (-1 : ℝ) 1) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn (FfunM d) (Icc (3 / 4 : ℝ) (5 / 2) ×ℂ Icc (-1 : ℝ) 1) := by
    refine (differentiableOn_FfunM d).continuousOn.mono ?_
    intro z hz; rw [mem_reProdIm] at hz; simp; linarith [hz.1.1]
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨|C| * 6 ^ 19 * Z + |κ * rsConstM m| + |C₂|, fun s h1 h2 => ?_⟩
  have hT : 1 ≤ (1 + |s.im|) ^ 19 := one_le_pow₀ (by linarith [abs_nonneg s.im])
  rcases le_or_gt |s.im| 1 with ht | ht
  · have := hC₂ s (by rw [mem_reProdIm]; exact ⟨⟨h1, h2⟩, abs_le.1 ht⟩)
    have h0 : 0 ≤ |C| * 6 ^ 19 * Z + |κ * rsConstM m| := by positivity
    calc ‖FfunM d s‖ ≤ |C₂| := this.trans (le_abs_self _)
      _ ≤ (|C| * 6 ^ 19 * Z + |κ * rsConstM m| + |C₂|) * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hT (by positivity)
  · -- `|Im s| > 1`
    have hs0 : s ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
    have hs1 : s ≠ 1 := by intro h; rw [h] at ht; simp at ht; linarith
    have hsn : 1 ≤ ‖s‖ := by have := Complex.abs_im_le_norm s; linarith
    have hs1n : 1 ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1); simp at this; linarith
    have hs3 : ‖s + 3‖ ≤ 6 * (1 + |s.im|) := by
      have := Complex.norm_le_abs_re_add_abs_im (s + 3)
      simp at this
      rw [abs_of_nonneg (by linarith)] at this; linarith
    rw [FfunM_eq d hs0 hs1]
    have hfull : (d.Λ₀ s + κ * (1 / (s - 1) - 1 / s)) * gfunM m s =
        fPLM d s * (s + 3) ^ 19 / (s * (s - 1)) * (riemannZeta (2 * s))⁻¹ := by
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
      have h3 : (s + 3) ^ 19 ≠ 0 := by
        apply pow_ne_zero; intro h; have := congrArg re h; simp at this; linarith
      have h3' : s + 3 ≠ 0 := by
        intro h; have := congrArg re h; simp at this; linarith
      unfold fPLM gfunM
      rw [num_eqM d hs0 hs1']
      field_simp
    rw [hfull]
    have hPL := hC s (by linarith) h2
    have hz := hZ (2 * s) (by simp; linarith)
    have e1 : ‖fPLM d s * (s + 3) ^ 19 / (s * (s - 1)) * (riemannZeta (2 * s))⁻¹‖ ≤
        |C| * 6 ^ 19 * Z * (1 + |s.im|) ^ 19 := by
      rw [norm_mul, norm_div, norm_mul, norm_mul, norm_pow]
      have hden : 1 ≤ ‖s‖ * ‖s - 1‖ := by nlinarith
      have hnum : ‖fPLM d s‖ * ‖s + 3‖ ^ 19 ≤ |C| * (6 * (1 + |s.im|)) ^ 19 :=
        mul_le_mul (hPL.trans (le_abs_self _)) (pow_le_pow_left₀ (norm_nonneg _) hs3 _)
          (by positivity) (abs_nonneg _)
      calc ‖fPLM d s‖ * ‖s + 3‖ ^ 19 / (‖s‖ * ‖s - 1‖) * ‖(riemannZeta (2 * s))⁻¹‖
          ≤ |C| * (6 * (1 + |s.im|)) ^ 19 / 1 * Z :=
            mul_le_mul (div_le_div₀ (by positivity) hnum one_pos hden) hz (norm_nonneg _)
              (by positivity)
        _ = |C| * 6 ^ 19 * Z * (1 + |s.im|) ^ 19 := by rw [mul_pow]; ring
    have e2 : ‖((κ * rsConstM m : ℝ) : ℂ) / (s - 1)‖ ≤ |κ * rsConstM m| := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      exact div_le_self (abs_nonneg _) hs1n
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ |C| * 6 ^ 19 * Z * (1 + |s.im|) ^ 19 + |κ * rsConstM m| := add_le_add e1 e2
      _ ≤ (|C| * 6 ^ 19 * Z + |κ * rsConstM m| + |C₂|) * (1 + |s.im|) ^ 19 := by
          nlinarith [abs_nonneg C₂, abs_nonneg (κ * rsConstM m)]

end F

/-- **Power saving `1/84` from the weight-`(m+1)` Rankin–Selberg data** (`m ≥ 2`). -/
theorem power_saving_84_of_RSDataM {m : ℕ} (hm : 2 ≤ m) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 0) {κ : ℝ}
    (hκ : 0 ≤ κ) (d : RSDataM m a κ) (hsum : Summable fun n : ℕ => a n * (n : ℝ) ^ (-(5 / 2 : ℝ))) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, a n - κ * rsConstM m * N| ≤ C * (N : ℝ) ^ (1 - 1 / 84 : ℝ) := by
  have hLS : LSeriesSummable (fun n => (a n : ℂ)) ((5 / 2 : ℝ) : ℂ) := by
    unfold LSeriesSummable
    refine Summable.of_norm ?_
    refine hsum.congr fun n => ?_
    rw [LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [ha0]
    · rw [if_neg h.ne', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha n),
        Real.rpow_neg (Nat.cast_nonneg n)]
      simp [div_eq_mul_inv]
  obtain ⟨B, hB⟩ := FfunM_bound d hLS hm
  have hR := rieszAsymp_of_continuation a ha ha0 (K := 19) (c := 5 / 2) (σ₀ := 1 / 2)
    (σ₁ := 3 / 4) (c₀ := κ * rsConstM m) (B := B) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hsum (FfunM d) (differentiableOn_FfunM d)
    (fun s hs => LSeries_eq_FfunM d (by rw [hs]; norm_num)) hB
  have hc0 : 0 ≤ κ * rsConstM m := mul_nonneg hκ (by unfold rsConstM; positivity)
  have hD := riesz_kdiff a ha hc0 20 (θ := 1 - 3 / 4) (by norm_num) (by norm_num) hR
  obtain ⟨C, hC⟩ := partial_sum_of_riesz0 a hD
  refine ⟨C, fun N hN => ?_⟩
  have := hC N hN
  convert this using 3
  norm_num

end RamanujanTau.RankinErrorGeneral

#print axioms RamanujanTau.RankinErrorGeneral.power_saving_84_of_RSDataM
