/-
# Abel-summation continuation of `ζ(s)` and of the Rankin–Selberg series `R(s)`

For coefficients `a(n)` with `|Σ_{n≤N} a(n) − cN| ≤ C N^θ` (`0 ≤ θ < 1`) put
`E(t) = Σ_{n≤t} a(n) − ct` and `I(s) = ∫_1^∞ E(t) t^{−s−1} dt`.  Then

* `I` is holomorphic on `Re s > θ` (Mathlib's Mellin-transform differentiability);
* `‖I(s)‖ ≤ (C + ‖c‖)/(Re s − θ)`;
* `L(a,s) = c s/(s−1) + s I(s)` on `Re s > 1` (Mathlib's `LSeries_eq_mul_integral`).

Applied to `a = 1` (`θ = 0`) and to `a(n) = τ(n)²/n¹¹` (`θ = 3/5`, Rankin's error term
`RankinExact.rankinSelberg_exact`) this gives `(s−1)ζ(s)` holomorphic on `Re s > 0`, and
`(s−1)R(s)`, `R(s)` holomorphic on `Re s > 3/5` (resp. minus `s = 1`) with `R(s) ≪ |s|`
away from `s = 1`.
-/
import RamanujanTau.EdgeNonvanishing.Main

set_option autoImplicit false

namespace RamanujanTau.ZeroFreeRegion

open Complex Finset Filter Asymptotics MeasureTheory LSeries Set Topology
open RamanujanTau.EdgeNonvanishing

/-- The Abel error `E(t) = Σ_{1≤n≤t} a(n) − c t`. -/
noncomputable def errE (a : ℕ → ℂ) (c : ℂ) (t : ℝ) : ℂ := (∑ k ∈ Icc 1 ⌊t⌋₊, a k) - c * t

/-- `I(s) = ∫_1^∞ E(t) t^{−s−1} dt`. -/
noncomputable def abelI (a : ℕ → ℂ) (c : ℂ) (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), errE a c t * (t : ℂ) ^ (-(s + 1))

section general

variable {a : ℕ → ℂ} {c : ℂ} {C θ : ℝ}

lemma measurable_errE (a : ℕ → ℂ) (c : ℂ) : Measurable (errE a c) := by
  have h1 : Measurable (fun t : ℝ => ∑ k ∈ Icc 1 ⌊t⌋₊, a k) :=
    (measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Icc 1 n, a k)).comp Nat.measurable_floor
  exact h1.sub (measurable_const.mul Complex.measurable_ofReal)

lemma errE_bound (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hpart : ∀ N : ℕ, ‖(∑ k ∈ Icc 1 N, a k) - c * N‖ ≤ C * (N : ℝ) ^ θ)
    {t : ℝ} (ht : 1 ≤ t) : ‖errE a c t‖ ≤ (C + ‖c‖) * t ^ θ := by
  have ht0 : 0 ≤ t := by linarith
  have hfl : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
  have hfl' : t - ⌊t⌋₊ ≤ 1 := by
    have := Nat.lt_floor_add_one t
    linarith
  have h1 : errE a c t = ((∑ k ∈ Icc 1 ⌊t⌋₊, a k) - c * (⌊t⌋₊ : ℕ)) - c * ((t - ⌊t⌋₊ : ℝ) : ℂ) := by
    simp only [errE]; push_cast; ring
  have htθ : 1 ≤ t ^ θ := Real.one_le_rpow ht hθ
  rw [h1]
  calc _ ≤ ‖(∑ k ∈ Icc 1 ⌊t⌋₊, a k) - c * (⌊t⌋₊ : ℕ)‖ + ‖c * ((t - ⌊t⌋₊ : ℝ) : ℂ)‖ :=
        norm_sub_le _ _
    _ ≤ C * (⌊t⌋₊ : ℝ) ^ θ + ‖c‖ * 1 := by
        gcongr
        · exact hpart _
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by linarith [Nat.floor_le ht0])]
          exact mul_le_mul_of_nonneg_left hfl' (norm_nonneg _)
    _ ≤ C * t ^ θ + ‖c‖ * t ^ θ := by
        gcongr
    _ = (C + ‖c‖) * t ^ θ := by ring

lemma integrand_bound (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hpart : ∀ N : ℕ, ‖(∑ k ∈ Icc 1 N, a k) - c * N‖ ≤ C * (N : ℝ) ^ θ) (s : ℂ)
    {t : ℝ} (ht : 1 < t) :
    ‖errE a c t * (t : ℂ) ^ (-(s + 1))‖ ≤ (C + ‖c‖) * t ^ (θ - s.re - 1) := by
  have ht0 : 0 < t := by linarith
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
  have h2 : t ^ (θ - s.re - 1) = t ^ θ * t ^ (-(s + 1)).re := by
    rw [← Real.rpow_add ht0]; congr 1; simp; ring
  rw [h2, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (errE_bound hC hθ hpart ht.le) (by positivity)

lemma integrableOn_integrand (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hpart : ∀ N : ℕ, ‖(∑ k ∈ Icc 1 N, a k) - c * N‖ ≤ C * (N : ℝ) ^ θ) {s : ℂ}
    (hs : θ < s.re) :
    IntegrableOn (fun t : ℝ => errE a c t * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hint : IntegrableOn (fun t : ℝ => (C + ‖c‖) * t ^ (θ - s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  refine hint.mono' ?_ ?_
  · have hm : Measurable (fun t : ℝ => errE a c t * (t : ℂ) ^ (-(s + 1))) :=
      (measurable_errE a c).mul (by fun_prop)
    exact hm.aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun t ht => integrand_bound hC hθ hpart s ht

/-- `‖I(s)‖ ≤ (C + ‖c‖)/(Re s − θ)`. -/
theorem norm_abelI_le (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hpart : ∀ N : ℕ, ‖(∑ k ∈ Icc 1 N, a k) - c * N‖ ≤ C * (N : ℝ) ^ θ) {s : ℂ}
    (hs : θ < s.re) : ‖abelI a c s‖ ≤ (C + ‖c‖) / (s.re - θ) := by
  have ha : θ - s.re - 1 < -1 := by linarith
  have hint : IntegrableOn (fun t : ℝ => (C + ‖c‖) * t ^ (θ - s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt ha zero_lt_one).const_mul _
  have hb : ‖abelI a c s‖ ≤ ∫ t in Ioi (1 : ℝ), (C + ‖c‖) * t ^ (θ - s.re - 1) := by
    refine norm_integral_le_of_norm_le hint ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun t ht => integrand_bound hC hθ hpart s ht
  have hval : ∫ t in Ioi (1 : ℝ), (C + ‖c‖) * t ^ (θ - s.re - 1) = (C + ‖c‖) / (s.re - θ) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt ha zero_lt_one, Real.one_rpow]
    have : θ - s.re - 1 + 1 = -(s.re - θ) := by ring
    rw [this]; field_simp
  rw [hval] at hb
  exact hb

/-- `I` is holomorphic on `Re s > θ`. -/
theorem differentiableAt_abelI (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hpart : ∀ N : ℕ, ‖(∑ k ∈ Icc 1 N, a k) - c * N‖ ≤ C * (N : ℝ) ^ θ) {s : ℂ}
    (hs : θ < s.re) : DifferentiableAt ℂ (abelI a c) s := by
  set g : ℝ → ℂ := (Ioi (1 : ℝ)).indicator (errE a c) with hg
  have hgm : Measurable g := (measurable_errE a c).indicator measurableSet_Ioi
  have hgbd : ∀ t : ℝ, ‖g t‖ ≤ (C + ‖c‖) * (max t 1) ^ θ := by
    intro t
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · rw [hg, indicator_of_mem ht, max_eq_left (le_of_lt ht)]
      exact errE_bound hC hθ hpart (le_of_lt ht)
    · rw [hg, indicator_of_notMem ht, norm_zero]
      have : 0 ≤ C + ‖c‖ := add_nonneg hC (norm_nonneg _)
      exact mul_nonneg this (Real.rpow_nonneg (le_max_of_le_right zero_le_one) _)
  have hloc : LocallyIntegrableOn g (Ioi 0) := by
    rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
    intro k _ hk
    obtain ⟨B, hB⟩ := hk.bddAbove
    refine Measure.integrableOn_of_bounded (M := (C + ‖c‖) * (max B 1) ^ θ) hk.measure_lt_top.ne
      hgm.aestronglyMeasurable ?_
    rw [ae_restrict_iff' hk.measurableSet]
    refine Eventually.of_forall fun t ht => (hgbd t).trans ?_
    have : 0 ≤ C + ‖c‖ := add_nonneg hC (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_max_of_le_right zero_le_one)
      (max_le_max (hB ht) le_rfl) hθ) this
  have htop : g =O[atTop] (fun t : ℝ => t ^ (-(-θ))) := by
    refine IsBigO.of_bound (C + ‖c‖) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [neg_neg, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    calc ‖g t‖ ≤ (C + ‖c‖) * (max t 1) ^ θ := hgbd t
      _ = (C + ‖c‖) * t ^ θ := by rw [max_eq_left ht]
  have hbot : g =O[𝓝[>] 0] (fun t : ℝ => t ^ (-((-s).re - 1))) := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have : t ∉ Ioi (1 : ℝ) := fun h => by simp at h; linarith [ht.2]
    rw [hg, indicator_of_notMem this, norm_zero, zero_mul]
  have hM := mellin_differentiableAt_of_isBigO_rpow hloc htop (by simp; linarith) hbot
    (by linarith : (-s).re - 1 < (-s).re)
  have heq : abelI a c = fun w => mellin g (-w) := by
    funext w
    rw [abelI, mellin, hg]
    simp_rw [← indicator_smul_apply (s := Ioi (1 : ℝ)) (fun t => (t : ℂ) ^ (-w - 1))]
    rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [smul_eq_mul]
    rw [mul_comm]; congr 2; ring
  rw [heq]
  exact hM.comp s differentiableAt_id.neg

/-- `L(a,s) = c s/(s−1) + s I(s)` on `Re s > 1`. -/
theorem LSeries_eq_abel (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hpart : ∀ N : ℕ, ‖(∑ k ∈ Icc 1 N, a k) - c * N‖ ≤ C * (N : ℝ) ^ θ) {s : ℂ}
    (hs : 1 < s.re) (hS : LSeriesSummable a s) :
    LSeries a s = c * s / (s - 1) + s * abelI a c s := by
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, a k) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine IsBigO.of_bound (C + ‖c‖) (Eventually.of_forall fun n => ?_)
    rw [Real.rpow_one, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 := hpart n
    have h2 : (n : ℝ) ^ θ ≤ n := by
      calc (n : ℝ) ^ θ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 hθ1.le
        _ = n := Real.rpow_one _
    calc ‖∑ k ∈ Icc 1 n, a k‖ ≤ ‖(∑ k ∈ Icc 1 n, a k) - c * n‖ + ‖c * n‖ := norm_le_norm_sub_add _ _
      _ ≤ C * n + ‖c‖ * n := by
          gcongr
          · exact h1.trans (mul_le_mul_of_nonneg_left h2 hC)
          · rw [norm_mul]; simp
      _ = (C + ‖c‖) * n := by ring
  rw [LSeries_eq_mul_integral a zero_le_one hs hS hO]
  have hs0 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hsplit : ∀ t ∈ Ioi (1 : ℝ), (∑ k ∈ Icc 1 ⌊t⌋₊, a k) * (t : ℂ) ^ (-(s + 1)) =
      errE a c t * (t : ℂ) ^ (-(s + 1)) + c * (t : ℂ) ^ (-s) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by
      have : (0 : ℝ) < t := lt_trans zero_lt_one ht
      exact_mod_cast this.ne'
    have : (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-s) := by
      conv_lhs => arg 1; rw [← cpow_one (t : ℂ)]
      rw [← cpow_add _ _ ht0]; congr 1; ring
    rw [errE, sub_mul, mul_assoc, this]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit,
    integral_add (integrableOn_integrand hC hθ hpart (by linarith))
      ((integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one).const_mul c),
    integral_const_mul, integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one]
  rw [← abelI]
  have : ((1 : ℝ) : ℂ) ^ (-s + 1) = 1 := by simp
  rw [this]
  have hs1 : -s + 1 ≠ 0 := by
    intro h; apply hs0; linear_combination -h
  field_simp
  ring

end general

/-! ### `ζ` -/

lemma zeta_part : ∀ N : ℕ, ‖(∑ k ∈ Icc 1 N, (1 : ℕ → ℂ) k) - 1 * N‖ ≤ 0 * (N : ℝ) ^ (0 : ℝ) := by
  intro N; simp

/-- `(s−1)ζ(s)`, continued to `Re s > 0`. -/
noncomputable def Z1 (s : ℂ) : ℂ := s + (s - 1) * s * abelI 1 1 s

theorem differentiableAt_Z1 {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Z1 s := by
  have := differentiableAt_abelI le_rfl le_rfl zeta_part hs
  unfold Z1; fun_prop

theorem Z1_eq {s : ℂ} (hs : 1 < s.re) : Z1 s = (s - 1) * riemannZeta s := by
  have h := LSeries_eq_abel le_rfl le_rfl zero_lt_one zeta_part hs (LSeriesSummable_one_iff.mpr hs)
  rw [LSeries_one_eq_riemannZeta hs] at h
  have hs0 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [h, Z1]; field_simp

/-! ### `R` -/

lemma rs_part : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, ‖(∑ k ∈ Icc 1 N, rsB k) - (rsc : ℂ) * N‖ ≤ C * (N : ℝ) ^ ((3 : ℝ) / 5) := by
  obtain ⟨C, hC0, hC⟩ := rs_partial
  refine ⟨C, hC0, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have : (∑ k ∈ Icc 1 N, rsB k) - (rsc : ℂ) * N = ((∑ n ∈ Icc 1 N, rsb n - rsc * N : ℝ) : ℂ) := by
    simp [rsB]
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact hC N hN

/-- The Rankin–Selberg series continued to `Re s > 3/5`, `s ≠ 1`. -/
noncomputable def Rt (s : ℂ) : ℂ := rsc * s / (s - 1) + s * abelI rsB rsc s

/-- `(s−1)R(s)`, continued to `Re s > 3/5`. -/
noncomputable def R1 (s : ℂ) : ℂ := rsc * s + (s - 1) * s * abelI rsB rsc s

theorem differentiableAt_R1 {s : ℂ} (hs : 3 / 5 < s.re) : DifferentiableAt ℂ R1 s := by
  obtain ⟨C, hC0, hC⟩ := rs_part
  have := differentiableAt_abelI hC0 (by norm_num) hC hs
  unfold R1; fun_prop

theorem differentiableAt_Rt {s : ℂ} (hs : 3 / 5 < s.re) (h1 : s ≠ 1) : DifferentiableAt ℂ Rt s := by
  obtain ⟨C, hC0, hC⟩ := rs_part
  have := differentiableAt_abelI hC0 (by norm_num) hC hs
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  unfold Rt
  fun_prop (disch := exact h1')

theorem Rt_eq {s : ℂ} (hs : 1 < s.re) : Rt s = RS s := by
  obtain ⟨C, hC0, hC⟩ := rs_part
  rw [RS, LSeries_eq_abel hC0 (by norm_num) (by norm_num) hC hs (rs_summable hs), Rt]

theorem R1_eq {s : ℂ} (hs : 1 < s.re) : R1 s = (s - 1) * RS s := by
  have hs0 : s - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [← Rt_eq hs, Rt, R1]; field_simp

/-- `‖R(s)‖ ≤ |c|‖s‖/‖s−1‖ + K‖s‖/(Re s − 3/5)` on `Re s > 3/5`. -/
theorem norm_Rt_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 3 / 5 < s.re →
    ‖Rt s‖ ≤ |rsc| * ‖s‖ / ‖s - 1‖ + ‖s‖ * (K / (s.re - 3 / 5)) := by
  obtain ⟨C, hC0, hC⟩ := rs_part
  refine ⟨C + |rsc|, by positivity, fun s hs => ?_⟩
  have hI := norm_abelI_le hC0 (by norm_num) hC hs
  rw [Complex.norm_real, Real.norm_eq_abs] at hI
  calc ‖Rt s‖ ≤ ‖(rsc : ℂ) * s / (s - 1)‖ + ‖s * abelI rsB rsc s‖ := norm_add_le _ _
    _ ≤ |rsc| * ‖s‖ / ‖s - 1‖ + ‖s‖ * ((C + |rsc|) / (s.re - 3 / 5)) := by
        rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        gcongr

end RamanujanTau.ZeroFreeRegion
