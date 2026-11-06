/-
# Ingham's theorem: `∫₀ᵀ |ζ(1/2+it)|² dt = T log(T/2π) + (2γ−1)T + O(T^{1/2+ε})`

Integrate the pointwise decomposition `|ζ|² = D(t) + O(t) + O(t^{c−1})` over `[8, T]`:
* diagonal: `D(t) = log(t/2π) + 2γ + O(t^{c−1})`, and `∫ log(t/2π) = [t log(t/2π) − t]`;
* off-diagonal: `|∫_8^T O(t) dt| ≤ Σ_{m≠n} 4 (T/2π)^c φ(m,n) = 8 (T/2π)^c Z²` (first-derivative test);
* AFE error: `∫_8^T C t^{c−1} ≤ C T^c / c`.
-/
import RamanujanTau.ZetaAFE.Pointwise

set_option autoImplicit false

namespace RamanujanTau.ZetaAFE

open Complex MeasureTheory Set Filter Topology
open scoped Interval

/-- Interchange of `∫_a^T` and `Σ'` under a uniform summable bound. -/
lemma integral_tsum_Icc {ι : Type*} [Countable ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ι → ℝ → E} {a T : ℝ} (haT : a ≤ T)
    (hf : ∀ p, ContinuousOn (f p) (Icc a T)) {u : ι → ℝ} (hu : Summable u)
    (hb : ∀ p t, t ∈ Icc a T → ‖f p t‖ ≤ u p) :
    ∫ t in a..T, ∑' p, f p t = ∑' p, ∫ t in a..T, f p t := by
  simp_rw [intervalIntegral.integral_of_le haT]
  have hint : ∀ p, Integrable (f p) (volume.restrict (Ioc a T)) := fun p =>
    ((hf p).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hsum : Summable fun p => ∫ t in Ioc a T, ‖f p t‖ := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun _ => norm_nonneg _)
      (fun p => ?_) (hu.mul_right (T - a))
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc a T)
      (f := fun t => ‖f p t‖) (C := u p) (by simp) (fun t ht => by
        rw [norm_norm]; exact hb p t (Ioc_subset_Icc_self ht))
    rw [Real.volume_real_Ioc_of_le haT] at h
    refine le_trans (le_of_eq ?_) h
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  exact (integral_tsum_of_summable_integral_norm hint hsum).symm

lemma continuousOn_bterm {a T : ℝ} (ha : 0 < a) (p : ℕ × ℕ) :
    ContinuousOn (fun t => bterm t (ellT t) p) (Icc a T) := by
  unfold bterm
  refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const (by fun_prop)) ?_
  refine Complex.continuous_ofReal.comp_continuousOn ?_
  exact continuous_V.comp_continuousOn (continuousOn_const.sub (continuousOn_ellT ha))

lemma norm_bterm_le_T {a T t : ℝ} (ha : 0 < a) (ht : t ∈ Icc a T) (p : ℕ × ℕ) :
    ‖bterm t (ellT t) p‖ ≤ 2 * T * (((p.1 : ℝ) + 1) ^ (-(3 / 2 : ℝ)) * ((p.2 : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
  refine (norm_bterm_le t (ellT t) p).trans ?_
  have ht0 : 0 < t := ha.trans_le ht.1
  rw [exp_ellT ht0]
  gcongr
  rw [div_le_iff₀ (by positivity)]
  have := Real.pi_gt_three
  nlinarith [ht.2]

lemma continuousOn_bo {a T : ℝ} (ha : 0 < a) (p : ℕ × ℕ) : ContinuousOn (fun t => bo t p) (Icc a T) := by
  unfold bo
  by_cases h : p.1 = p.2
  · simp only [h, if_true]; exact continuousOn_const
  · simp only [h, if_false]; exact continuousOn_bterm ha p

lemma norm_bo_le {a T t : ℝ} (ha : 0 < a) (ht : t ∈ Icc a T) (p : ℕ × ℕ) :
    ‖bo t p‖ ≤ 2 * T * (((p.1 : ℝ) + 1) ^ (-(3 / 2 : ℝ)) * ((p.2 : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
  unfold bo
  split_ifs
  · rw [norm_zero]
    have : 0 < T := (ha.trans_le ht.1).trans_le ht.2
    positivity
  · exact norm_bterm_le_T ha ht p

lemma continuousOn_Oft {a T : ℝ} (ha : 0 < a) : ContinuousOn Oft (Icc a T) :=
  continuousOn_tsum (fun p => continuousOn_bo ha p) ((summable_uu (by norm_num)).mul_left (2 * T))
    (fun p t ht => norm_bo_le ha ht p)

lemma diag_term_le {a T t : ℝ} (ha : 0 < a) (ht : t ∈ Icc a T) (n : ℕ) :
    ‖1 / ((n : ℝ) + 1) * V (2 * lg n - ellT t)‖ ≤ 2 * T * ((n : ℝ) + 1) ^ (-(3 : ℝ)) := by
  have ht0 : 0 < t := ha.trans_le ht.1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (V_nonneg _))]
  have hV := V_le_exp (2 * lg n - ellT t)
  have he : Real.exp (-(2 * lg n - ellT t)) = t / (2 * Real.pi) * ((n : ℝ) + 1) ^ (-(2 : ℝ)) := by
    rw [show -(2 * lg n - ellT t) = ellT t + (-2) * lg n by ring, Real.exp_add, exp_ellT ht0]
    unfold lg
    rw [Real.rpow_def_of_pos (by positivity)]; congr 2; ring
  have h3 : 1 / ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (-(2 : ℝ)) = ((n : ℝ) + 1) ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
    rw [show (3 : ℝ) = 1 + 2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one]
    field_simp
  have htT : t / (2 * Real.pi) ≤ T := by
    rw [div_le_iff₀ (by positivity)]; have := Real.pi_gt_three; nlinarith [ht.2]
  calc 1 / ((n : ℝ) + 1) * V (2 * lg n - ellT t)
      ≤ 1 / ((n : ℝ) + 1) * (2 * Real.exp (-(2 * lg n - ellT t))) := by gcongr
    _ = 2 * (t / (2 * Real.pi)) * (1 / ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (-(2 : ℝ))) := by rw [he]; ring
    _ ≤ 2 * T * (1 / ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (-(2 : ℝ))) := by gcongr
    _ = _ := by rw [h3]

lemma continuousOn_Dsum {a T : ℝ} (ha : 0 < a) : ContinuousOn (fun t => Dsum (ellT t)) (Icc a T) := by
  unfold Dsum
  refine continuousOn_tsum (fun n => ?_) ((summable_rpow_neg (σ := 3) (by norm_num)).mul_left (2 * T))
    (fun n t ht => diag_term_le ha ht n)
  exact ContinuousOn.mul continuousOn_const
    (continuous_V.comp_continuousOn (continuousOn_const.sub (continuousOn_ellT ha)))

/-- `∫_a^T log(t/2π) dt = [t log(t/2π) − t]_a^T`. -/
lemma integral_ellT {a T : ℝ} (ha : 0 < a) (haT : a ≤ T) :
    ∫ t in a..T, ellT t = (T * ellT T - T) - (a * ellT a - a) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => t * ellT t - t) (fun t ht => ?_) ?_
  · rw [uIcc_of_le haT] at ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have h := ((hasDerivAt_id t).mul (hasDerivAt_ellT ht0)).sub (hasDerivAt_id t)
    convert h using 1
    simp only [id]; field_simp; ring
  · exact (continuousOn_ellT ha)|>.intervalIntegrable_of_Icc (μ := volume) haT

lemma integral_rpow_le {c a T : ℝ} (hc : 0 < c) (ha : 0 < a) (haT : a ≤ T) :
    ∫ t in a..T, t ^ (c - 1) ≤ T ^ c / c := by
  rw [integral_rpow (Or.inl (by linarith)), show c - 1 + 1 = c by ring]
  have : 0 ≤ a ^ c := by positivity
  gcongr; linarith

/-- **Ingham's theorem with exponent `c ∈ (1/2, 1]`.** -/
theorem ingham_rpow {c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≤ 1) :
    ∃ C : ℝ, ∀ T : ℝ, 8 ≤ T →
      |(∫ t in (0:ℝ)..T, zsq t) - (T * ellT T + (2 * Real.eulerMascheroniConstant - 1) * T)| ≤
        C * T ^ c := by
  obtain ⟨CE, hCE0, hCE⟩ := pointwise_err hc hc1
  obtain ⟨CD, hCD0, hCD⟩ := diag_err hc hc1
  have hc0 : 0 < c := by linarith
  set γ := Real.eulerMascheroniConstant with hγ
  set Z2 : ℝ := Zs (1 / 2 + c) ^ 2 with hZ2
  refine ⟨|(∫ t in (0:ℝ)..8, zsq t) - (8 * ellT 8 - 8) - 16 * γ| + CD / c + 8 * Z2 + CE / c,
    fun T hT => ?_⟩
  have h8 : (0 : ℝ) < 8 := by norm_num
  have hT0 : 0 < T := by linarith
  have hTc : 1 ≤ T ^ c := Real.one_le_rpow (by linarith) hc0.le
  have hzI : ∀ a b : ℝ, IntervalIntegrable zsq volume a b := fun a b =>
    continuous_zsq.intervalIntegrable a b
  -- split [0,T] = [0,8] ∪ [8,T]
  have hsplit0 : (∫ t in (0:ℝ)..T, zsq t) = (∫ t in (0:ℝ)..8, zsq t) + ∫ t in (8:ℝ)..T, zsq t :=
    (intervalIntegral.integral_add_adjacent_intervals (hzI 0 8) (hzI 8 T)).symm
  -- complex decomposition on [8,T]
  set rest : ℝ → ℂ := fun t => ((zsq t : ℝ) : ℂ) - (Dsum (ellT t) : ℂ) - Oft t with hrest
  have hcD : ContinuousOn (fun t => ((Dsum (ellT t) : ℝ) : ℂ)) (Icc 8 T) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_Dsum h8)
  have hcO : ContinuousOn Oft (Icc 8 T) := continuousOn_Oft h8
  have hcZ : ContinuousOn (fun t => ((zsq t : ℝ) : ℂ)) (Icc 8 T) :=
    (Complex.continuous_ofReal.comp continuous_zsq).continuousOn
  have hiD := hcD|>.intervalIntegrable_of_Icc (μ := volume) hT
  have hiO := hcO|>.intervalIntegrable_of_Icc (μ := volume) hT
  have hiR : IntervalIntegrable rest volume 8 T := ((hcZ.sub hcD).sub hcO)|>.intervalIntegrable_of_Icc (μ := volume) hT
  have hdec : (((∫ t in (8:ℝ)..T, zsq t) : ℝ) : ℂ) =
      (∫ t in (8:ℝ)..T, ((Dsum (ellT t) : ℝ) : ℂ)) + (∫ t in (8:ℝ)..T, Oft t) + ∫ t in (8:ℝ)..T, rest t := by
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_add hiD hiO,
      ← intervalIntegral.integral_add (hiD.add hiO) hiR]
    congr 1; funext t; simp only [hrest]; ring
  -- the three bounds
  have hR : ‖∫ t in (8:ℝ)..T, rest t‖ ≤ CE / c * T ^ c := by
    have hb : ∀ t ∈ Ι (8:ℝ) T, ‖rest t‖ ≤ CE * t ^ (c - 1) := by
      intro t ht
      rw [uIoc_of_le hT] at ht
      exact hCE t ht.1.le
    refine (intervalIntegral.norm_integral_le_of_norm_le hT (Eventually.of_forall fun t ht =>
      hb t (by rw [uIoc_of_le hT]; exact ht)) ?_).trans ?_
    · exact (continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl ((show (0:ℝ) < x by linarith [hx.1]).ne'))))|>.intervalIntegrable_of_Icc (μ := volume) hT
    · rw [intervalIntegral.integral_const_mul]
      have := integral_rpow_le hc0 h8 hT
      calc CE * ∫ t in (8:ℝ)..T, t ^ (c - 1) ≤ CE * (T ^ c / c) := by gcongr
        _ = _ := by ring
  have hO : ‖∫ t in (8:ℝ)..T, Oft t‖ ≤ 8 * Z2 * T ^ c := by
    unfold Oft
    rw [integral_tsum_Icc hT (fun p => continuousOn_bo h8 p) ((summable_uu (by norm_num)).mul_left (2 * T))
      (fun p t ht => norm_bo_le h8 ht p)]
    have hbd : ∀ p, ‖∫ t in (8:ℝ)..T, bo t p‖ ≤ 4 * Real.exp (c * ellT T) * phiO (1 / 2 + c) p := by
      intro p
      by_cases hp : p.1 = p.2
      · simp only [bo, hp, if_true, intervalIntegral.integral_zero, norm_zero]
        have : 0 ≤ phiO (1 / 2 + c) p := add_nonneg (phi1_nonneg _ _) (phi1_nonneg _ _)
        positivity
      · simp only [bo, hp, if_false]
        exact norm_integral_bterm_off hc hc1 h8 hT p hp
    have hs := (summable_phiO (σ := 1 / 2 + c) (by linarith)).mul_left (4 * Real.exp (c * ellT T))
    refine (norm_tsum_le_tsum_norm (Summable.of_norm_bounded hs (fun p => (norm_norm _).le.trans (hbd p)))).trans ?_
    refine (Summable.tsum_le_tsum hbd (Summable.of_norm_bounded hs (fun p => (norm_norm _).le.trans (hbd p))) hs).trans ?_
    rw [tsum_mul_left, tsum_phiO (by linarith)]
    have := exp_c_ellT_le hc0.le hT0
    rw [hZ2]
    have hZ : 0 ≤ Zs (1 / 2 + c) ^ 2 := sq_nonneg _
    nlinarith
  have hD : |(∫ t in (8:ℝ)..T, Dsum (ellT t)) - ((T * ellT T - T) - (8 * ellT 8 - 8) + 2 * γ * (T - 8))| ≤
      CD / c * T ^ c := by
    have hiE : IntervalIntegrable ellT volume 8 T := (continuousOn_ellT h8)|>.intervalIntegrable_of_Icc (μ := volume) hT
    have hmain : ∫ t in (8:ℝ)..T, (ellT t + 2 * γ) = (T * ellT T - T) - (8 * ellT 8 - 8) + 2 * γ * (T - 8) := by
      rw [intervalIntegral.integral_add hiE intervalIntegrable_const, integral_ellT h8 hT,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [← hmain, ← intervalIntegral.integral_sub ((continuousOn_Dsum h8)|>.intervalIntegrable_of_Icc (μ := volume) hT)
      (hiE.add intervalIntegrable_const), ← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun t => CD * t ^ (c - 1)) hT
      (Eventually.of_forall fun t ht => ?_) ?_).trans ?_
    · rw [Real.norm_eq_abs, show Dsum (ellT t) - (ellT t + 2 * γ) = Dsum (ellT t) - ellT t - 2 * γ by ring]
      exact hCD t ht.1.le
    · exact (continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl ((show (0:ℝ) < x by linarith [hx.1]).ne'))))|>.intervalIntegrable_of_Icc (μ := volume) hT
    · rw [intervalIntegral.integral_const_mul]
      have := integral_rpow_le hc0 h8 hT
      calc CD * ∫ t in (8:ℝ)..T, t ^ (c - 1) ≤ CD * (T ^ c / c) := by gcongr
        _ = _ := by ring
  -- assemble
  set X := ∫ t in (8:ℝ)..T, zsq t with hX
  set M := (T * ellT T - T) - (8 * ellT 8 - 8) + 2 * γ * (T - 8) with hM
  have hXM : |X - M| ≤ CD / c * T ^ c + 8 * Z2 * T ^ c + CE / c * T ^ c := by
    have h1 : ((X - M : ℝ) : ℂ) = (((∫ t in (8:ℝ)..T, Dsum (ellT t)) - M : ℝ) : ℂ) +
        (∫ t in (8:ℝ)..T, Oft t) + ∫ t in (8:ℝ)..T, rest t := by
      rw [Complex.ofReal_sub, hdec, Complex.ofReal_sub, intervalIntegral.integral_ofReal]; ring
    have h2 : |X - M| = ‖((X - M : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h2, h1]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith
  have hfinal : (∫ t in (0:ℝ)..T, zsq t) - (T * ellT T + (2 * γ - 1) * T) =
      ((∫ t in (0:ℝ)..8, zsq t) - (8 * ellT 8 - 8) - 16 * γ) + (X - M) := by
    rw [hsplit0, hM]; ring
  rw [hfinal]
  refine (abs_add_le _ _).trans ?_
  have hC0' := le_mul_of_one_le_right (abs_nonneg ((∫ t in (0:ℝ)..8, zsq t) - (8 * ellT 8 - 8) - 16 * γ)) hTc
  nlinarith

end RamanujanTau.ZetaAFE
