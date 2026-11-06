/-
# An exact Euler–Maclaurin formula for `ζ(s)` in the strip, and the pointwise approximation

For `N ≥ 1`, `0 < Re s`, `Im s < 0`:

    ζ(s) = ∑_{n ≤ N} n^{−s} + N^{1−s}/(s−1) − s ∫_N^∞ {t} t^{−s−1} dt,

where the integral is `IN N s = mellin (gN N) (−s)`, `gN N = 1_{(N,∞)} · {·}`. For `Re s > 1` this is
Abel summation applied to `1_{n > N}` (Mathlib `LSeries_eq_mul_integral'`); both sides are holomorphic
on `{Re s > 0} ∩ {Im s < 0}` (a convex set avoiding the pole), so the identity principle extends it.
Hence `‖ζ(s) − ∑_{n≤N} n^{−s}‖ ≤ N^{1−u}/‖s−1‖ + ‖s‖ N^{−u}/u` (`u = Re s`).
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.RankinOmega

open Complex MeasureTheory Set Filter Topology Asymptotics

/-- The fractional part `t − ⌊t⌋₊`. -/
noncomputable def fr (t : ℝ) : ℝ := t - ⌊t⌋₊

lemma fr_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ fr t := by
  unfold fr; linarith [Nat.floor_le ht]

lemma fr_lt_one (t : ℝ) : fr t < 1 := by
  unfold fr; linarith [Nat.lt_floor_add_one t]

lemma measurable_fr : Measurable fr := by
  unfold fr
  exact measurable_id.sub ((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp Nat.measurable_floor)

/-- `gN N = 1_{(N,∞)} · fr`, as a complex function. -/
noncomputable def gN (N : ℕ) (t : ℝ) : ℂ := (Ioi (N : ℝ)).indicator (fun t => ((fr t : ℝ) : ℂ)) t

lemma measurable_gN (N : ℕ) : Measurable (gN N) :=
  (measurable_ofReal.comp measurable_fr).indicator measurableSet_Ioi

lemma norm_gN_le (N : ℕ) (t : ℝ) : ‖gN N t‖ ≤ 1 := by
  unfold gN
  by_cases h : t ∈ Ioi (N : ℝ)
  · rw [indicator_of_mem h, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fr_nonneg (le_trans (Nat.cast_nonneg N) (le_of_lt h)))]
    exact (fr_lt_one t).le
  · rw [indicator_of_notMem h, norm_zero]; norm_num

/-- `IN N s = ∫_N^∞ fr(t) t^{−s−1} dt`. -/
noncomputable def IN (N : ℕ) (s : ℂ) : ℂ := mellin (gN N) (-s)

lemma locallyIntegrableOn_gN (N : ℕ) : LocallyIntegrableOn (gN N) (Ioi 0) := by
  refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2 fun K _ hKc => ?_
  exact Measure.integrableOn_of_bounded hKc.measure_lt_top.ne
    (measurable_gN N).aestronglyMeasurable (Eventually.of_forall fun t => norm_gN_le N t)

lemma differentiableAt_IN (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (IN N) s := by
  have htop : gN N =O[atTop] (· ^ (-(0 : ℝ))) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
    simp only [neg_zero, Real.rpow_zero, norm_one, one_mul]
    exact norm_gN_le N t
  have hbot : gN N =O[𝓝[>] 0] (· ^ (-(-s.re - 1))) := by
    have : gN N =ᶠ[𝓝[>] 0] 0 := by
      have hN1 : (0 : ℝ) < N := by exact_mod_cast hN
      filter_upwards [Ioo_mem_nhdsGT hN1] with t ht
      simp only [gN, Pi.zero_apply]
      exact indicator_of_notMem (by simp only [mem_Ioi, not_lt]; exact ht.2.le) _
    exact this.trans_isBigO (isBigO_zero _ _)
  have hd := mellin_differentiableAt_of_isBigO_rpow (locallyIntegrableOn_gN N) htop
    (s := -s) (by simp; exact hs) hbot (by simp)
  exact hd.comp s differentiableAt_id.neg

/-- `IN N s` as a set integral. -/
lemma IN_eq (N : ℕ) (hN : 1 ≤ N) (s : ℂ) :
    IN N s = ∫ t in Ioi (N : ℝ), ((fr t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  unfold IN mellin gN
  have e : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • (Ioi (N : ℝ)).indicator (fun t => ((fr t : ℝ) : ℂ)) t =
      (Ioi (N : ℝ)).indicator (fun t => ((fr t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) t := by
    intro t
    by_cases h : t ∈ Ioi (N : ℝ)
    · rw [indicator_of_mem h, indicator_of_mem h, smul_eq_mul, mul_comm]
    · rw [indicator_of_notMem h, indicator_of_notMem h, smul_zero]
  simp_rw [e]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hN0]

/-- **Tail bound**: `‖IN N s‖ ≤ N^{−u}/u`, `u = Re s > 0`. -/
lemma norm_IN_le (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) :
    ‖IN N s‖ ≤ (N : ℝ) ^ (-s.re) / s.re := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [IN_eq N hN s]
  have hint : IntegrableOn (fun t : ℝ => t ^ (-s.re - 1)) (Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hN0
  have hval : ∫ t in Ioi (N : ℝ), t ^ (-s.re - 1) = (N : ℝ) ^ (-s.re) / s.re := by
    rw [integral_Ioi_rpow_of_lt (by linarith) hN0]
    rw [show -s.re - 1 + 1 = -s.re by ring]
    field_simp
  rw [← hval]
  refine norm_integral_le_of_norm_le hint ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 < t := lt_trans hN0 ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fr_nonneg ht0.le),
    Complex.norm_cpow_eq_rpow_re_of_pos ht0]
  have : (-s - 1).re = -s.re - 1 := by simp
  rw [this]
  have h1 := (fr_lt_one t).le
  have h2 : 0 ≤ t ^ (-s.re - 1) := Real.rpow_nonneg ht0.le _
  nlinarith [fr_nonneg ht0.le]

/-- The indicator `1_{n > N}`. -/
noncomputable def indGt (N : ℕ) (n : ℕ) : ℂ := if N < n then 1 else 0

lemma sum_indGt (N M : ℕ) : ∑ k ∈ Finset.Icc 1 M, indGt N k = ((M - N : ℕ) : ℂ) := by
  unfold indGt
  rw [Finset.sum_boole]
  congr 1
  have : (Finset.Icc 1 M).filter (fun k => N < k) = Finset.Icc (N + 1) M := by
    ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [this, Nat.card_Icc]; omega

/-- **The formula for `Re s > 1`.** -/
lemma zeta_formula_large (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s - ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) =
      (N : ℂ) ^ (1 - s) / (s - 1) - s * IN N s := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have hs1 : s - 1 ≠ 0 := by intro h; rw [sub_eq_zero] at h; rw [h] at hs; simp at hs
  -- Abel summation for `1_{n > N}`
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ‖indGt N k‖) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    rw [Real.rpow_one, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _),
      Real.norm_of_nonneg (Nat.cast_nonneg n), one_mul]
    calc ∑ k ∈ Finset.Icc 1 n, ‖indGt N k‖ ≤ ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) :=
          Finset.sum_le_sum fun k _ => by unfold indGt; split_ifs <;> simp
      _ = n := by simp
  have hL := LSeries_eq_mul_integral' (indGt N) (r := 1) zero_le_one hs hO
  -- the L-series is the tail of `ζ`
  have hLz : LSeries (indGt N) s = riemannZeta s - ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) := by
    rw [← LSeries_one_eq_riemannZeta hs]
    have hS1 : LSeriesSummable 1 s := LSeriesSummable_one_iff.2 hs
    have hS2 : LSeriesSummable (indGt N) s := by
      refine Summable.of_norm_bounded (g := fun n => ‖LSeries.term 1 s n‖) hS1.norm ?_
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · simp only [LSeries.term_of_ne_zero hn, norm_div]
        gcongr; unfold indGt; split_ifs <;> simp
    have hfin : LSeries 1 s - LSeries (indGt N) s =
        ∑' n, (LSeries.term 1 s n - LSeries.term (indGt N) s n) := by
      unfold LSeries; rw [hS1.tsum_sub hS2]
    have hsupp : ∀ n ∉ Finset.range (N + 1),
        LSeries.term 1 s n - LSeries.term (indGt N) s n = 0 := by
      intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      have hn0 : n ≠ 0 := by omega
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
      simp [indGt, show N < n by omega]
    rw [tsum_eq_sum hsupp] at hfin
    have hsum : ∑ n ∈ Finset.range (N + 1), (LSeries.term 1 s n - LSeries.term (indGt N) s n) =
        ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < N + 1)]
      · simp only [LSeries.term_zero, sub_zero, zero_add]
        rw [show Finset.Ico (0 + 1) (N + 1) = Finset.Icc 1 N by
          ext k; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega]
        refine Finset.sum_congr rfl fun n hn => ?_
        simp only [Finset.mem_Icc] at hn
        have hn0 : n ≠ 0 := by omega
        rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
        simp only [indGt, show ¬ N < n by omega, if_false, zero_div, sub_zero, Pi.one_apply]
        rw [Complex.cpow_neg, one_div]
    rw [hsum] at hfin
    linear_combination -hfin
  rw [← hLz, hL]
  -- the integral
  have hsplit : ∫ t in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, indGt N k) * (t : ℂ) ^ (-(s + 1)) =
      ∫ t in Ioi (N : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, indGt N k) * (t : ℂ) ^ (-(s + 1)) := by
    refine setIntegral_eq_of_subset_of_ae_diff_eq_zero measurableSet_Ioi.nullMeasurableSet
      (Ioi_subset_Ioi (by exact_mod_cast hN)) (Eventually.of_forall fun t ht => ?_)
    rcases ht with ⟨_, ht2⟩
    simp only [mem_Ioi, not_lt] at ht2
    rw [sum_indGt]
    have : ⌊t⌋₊ ≤ N := Nat.floor_le_of_le ht2
    rw [show ⌊t⌋₊ - N = 0 by omega]; simp
  have hpt : ∀ t ∈ Ioi (N : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, indGt N k) * (t : ℂ) ^ (-(s + 1)) =
      (t : ℂ) ^ (-s) - (N : ℂ) * (t : ℂ) ^ (-s - 1) - ((fr t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hN0 ht
    have hNt : N ≤ ⌊t⌋₊ := Nat.le_floor (le_of_lt ht)
    rw [sum_indGt, Nat.cast_sub hNt]
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have e1 : (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-s - 1) := by
      rw [show -s = (-s - 1) + 1 by ring, Complex.cpow_add _ _ htc, Complex.cpow_one]; ring
    rw [e1, show -(s + 1) = -s - 1 by ring]
    simp only [fr]; push_cast; ring
  have hI1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi (N : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) hN0
  have hI2 : IntegrableOn (fun t : ℝ => (N : ℂ) * (t : ℂ) ^ (-s - 1)) (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_cpow_of_lt (by simp; linarith) hN0).const_mul _
  have hI3 : IntegrableOn (fun t : ℝ => ((fr t : ℝ) : ℂ) * (t : ℂ) ^ (-s - 1)) (Ioi (N : ℝ)) := by
    have hb : IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ (-s - 1)‖) (Ioi (N : ℝ)) :=
      (integrableOn_Ioi_cpow_of_lt (by simp; linarith) hN0).norm
    refine hb.mono' ?_ ?_
    · refine ((measurable_ofReal.comp measurable_fr).aestronglyMeasurable).mul ?_
      refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
      have ht0 : 0 < t := lt_trans hN0 ht
      exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht0.ne')).continuousWithinAt
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have ht0 : 0 < t := lt_trans hN0 ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fr_nonneg ht0.le)]
      have := (fr_lt_one t).le
      have h0 : 0 ≤ ‖(t : ℂ) ^ (-s - 1)‖ := norm_nonneg _
      nlinarith
  have hsub1 := integral_sub (μ := volume.restrict (Ioi (N : ℝ))) (hI1.sub hI2) hI3
  have hsub2 := integral_sub (μ := volume.restrict (Ioi (N : ℝ))) hI1 hI2
  simp only [Pi.sub_apply] at hsub1
  rw [hsplit, setIntegral_congr_fun measurableSet_Ioi hpt, hsub1, hsub2, integral_const_mul, ← IN_eq N hN s,
    integral_Ioi_cpow_of_lt (by simp; linarith) hN0,
    integral_Ioi_cpow_of_lt (by simp; linarith) hN0]
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have e2 : ((N : ℝ) : ℂ) ^ (-s - 1 + 1) = (N : ℂ) ^ (-s) := by push_cast; ring_nf
  have e3 : ((N : ℝ) : ℂ) ^ (-s + 1) = (N : ℂ) * (N : ℂ) ^ (-s) := by
    push_cast
    rw [Complex.cpow_add _ _ hNc, Complex.cpow_one]; ring
  have e4 : (N : ℂ) ^ (1 - s) = (N : ℂ) * (N : ℂ) ^ (-s) := by
    rw [show (1 : ℂ) - s = -s + 1 by ring, Complex.cpow_add _ _ hNc, Complex.cpow_one]; ring
  rw [e2, e3, e4]
  have hs1' : -s + 1 ≠ 0 := by intro h; apply hs1; linear_combination -h
  have hs0' : -s - 1 + 1 ≠ 0 := by intro h; apply hs0; linear_combination -h
  field_simp
  ring

/-- **The exact formula on `0 < Re s`, `Im s < 0`.** -/
theorem zeta_formula (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) (him : s.im < 0) :
    riemannZeta s - ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s) =
      (N : ℂ) ^ (1 - s) / (s - 1) - s * IN N s := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} ∩ {z : ℂ | z.im < 0} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_im continuous_const)
  have hUc : IsPreconnected U :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hne1 : ∀ z ∈ U, z ≠ 1 := by
    intro z hz h; have := hz.2; rw [h] at this; simp at this
  have hF : DifferentiableOn ℂ (fun z => riemannZeta z - ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z)) U := by
    intro z hz
    refine ((differentiableAt_riemannZeta (hne1 z hz)).sub ?_).differentiableWithinAt
    refine DifferentiableAt.fun_sum fun n hn => ?_
    simp only [Finset.mem_Icc] at hn
    exact differentiableAt_id.neg.const_cpow (Or.inl (by exact_mod_cast (show n ≠ 0 by omega)))
  have hG : DifferentiableOn ℂ (fun z => (N : ℂ) ^ (1 - z) / (z - 1) - z * IN N z) U := by
    intro z hz
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.2 (hne1 z hz)
    refine (DifferentiableAt.sub ?_ (differentiableAt_id.mul (differentiableAt_IN N hN hz.1))).differentiableWithinAt
    exact ((differentiableAt_const _).sub differentiableAt_id |>.const_cpow
      (Or.inl (by exact_mod_cast (show N ≠ 0 by omega)))).div (differentiableAt_id.sub_const 1) hz1
  set z0 : ℂ := 3 - I with hz0
  have hz0U : z0 ∈ U := by simp [hU, hz0]
  have hev : (fun z => riemannZeta z - ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-z)) =ᶠ[𝓝 z0]
      (fun z => (N : ℂ) ^ (1 - z) / (z - 1) - z * IN N z) := by
    have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 z0 :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp [hz0])
    filter_upwards [hV] with z hz using zeta_formula_large N hN hz
  exact (hF.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hUo) hUc
    hz0U hev ⟨hs, him⟩

/-- **Pointwise approximation** of `ζ` by a Dirichlet polynomial. -/
theorem norm_zeta_sub_le (N : ℕ) (hN : 1 ≤ N) {s : ℂ} (hs : 0 < s.re) (him : s.im < 0) :
    ‖riemannZeta s - ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)‖ ≤
      (N : ℝ) ^ (1 - s.re) / ‖s - 1‖ + ‖s‖ * ((N : ℝ) ^ (-s.re) / s.re) := by
  rw [zeta_formula N hN hs him]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine (norm_sub_le _ _).trans ?_
  rw [norm_div, norm_mul]
  have e : ‖(N : ℂ) ^ (1 - s)‖ = (N : ℝ) ^ (1 - s.re) := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; rfl, Complex.norm_cpow_eq_rpow_re_of_pos hN0]
    simp
  rw [e]
  gcongr
  exact norm_IN_le N hN hs

end RamanujanTau.RankinOmega
