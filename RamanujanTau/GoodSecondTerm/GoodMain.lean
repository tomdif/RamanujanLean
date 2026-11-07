/-
# Good's mean square for `L(Δ,s)` with second term: reduction to the off-diagonal

`good_reduction` (unconditional): for `T ≥ 16`,

    ∫₀ᵀ |L(Δ,6+it)|² dt = 2c₀ T log(T/2π) + (2γ_Δ − 2c₀) T + Off(T) + O(T^{9/10}),

`Off(T) = Σ_{m≠n} ∫_{16}^T τ(m)τ(n)(mn)^{−6} (n/m)^{it} V(log(mn) − 2 log(t/2π)) dt`.
`good_second_term_of_offdiag`: if `|Off(T)| ≤ C T^{1−δ}` (`OffDiagHyp δ`) then the error is
`O(T^{1−δ} + T^{9/10})`.
-/
import RamanujanTau.GoodSecondTerm.PointwiseD
import RamanujanTau.ZetaAFE.Ingham

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.HeckeL
open scoped Interval

/-- `|L(Δ,6+it)|²`. -/
noncomputable def zsqD (t : ℝ) : ℝ := ‖tauL (6 + t * I)‖ ^ 2

lemma continuous_zsqD : Continuous zsqD := by
  unfold zsqD
  exact ((tauLSeries_entire.continuous.comp (by fun_prop : Continuous fun t : ℝ => (6 : ℂ) + t * I)).norm).pow 2

/-- `Off(T) = Σ_{m≠n} ∫_{16}^T b_{m,n}(t) dt`. -/
noncomputable def OffInt (T : ℝ) : ℂ := ∑' p, ∫ t in (16 : ℝ)..T, boD t p

/-- **The off-diagonal hypothesis** (shifted-convolution content of Good's theorem). -/
def OffDiagHyp (δ : ℝ) : Prop := ∃ C : ℝ, ∀ T : ℝ, 16 ≤ T → ‖OffInt T‖ ≤ C * T ^ (1 - δ)

noncomputable def tt7 (p : ℕ × ℕ) : ℝ :=
  (|((tau (p.1 + 1) : ℤ) : ℝ)| * ((p.1 : ℝ) + 1) ^ (-(7 : ℝ))) *
    (|((tau (p.2 + 1) : ℤ) : ℝ)| * ((p.2 : ℝ) + 1) ^ (-(7 : ℝ)))

lemma exp_two_ellT_le {a T t : ℝ} (ha : 0 < a) (ht : t ∈ Icc a T) : Real.exp (2 * ellT t) ≤ T ^ 2 := by
  have ht0 : 0 < t := ha.trans_le ht.1
  rw [show 2 * ellT t = ellT t + ellT t by ring, Real.exp_add, exp_ellT ht0]
  have h1 : t / (2 * Real.pi) ≤ T := by
    rw [div_le_iff₀ (by positivity)]; have := Real.pi_gt_three; nlinarith [ht.2]
  have h0 : 0 ≤ t / (2 * Real.pi) := by positivity
  nlinarith

lemma continuousOn_bD2 {a T : ℝ} (ha : 0 < a) (p : ℕ × ℕ) :
    ContinuousOn (fun t => bD t (2 * ellT t) p) (Icc a T) := by
  unfold bD
  refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const (by fun_prop)) ?_
  refine Complex.continuous_ofReal.comp_continuousOn ?_
  exact continuous_V.comp_continuousOn (continuousOn_const.sub
    (continuousOn_const.mul (continuousOn_ellT ha)))

lemma norm_boD_le {a T t : ℝ} (ha : 0 < a) (ht : t ∈ Icc a T) (p : ℕ × ℕ) :
    ‖boD t p‖ ≤ 2 * T ^ 2 * tt7 p := by
  have h7 : 0 ≤ tt7 p := by unfold tt7; positivity
  unfold boD
  split_ifs
  · rw [norm_zero]; positivity
  · refine (norm_bD_le t (2 * ellT t) p).trans ?_
    unfold tt7
    have := exp_two_ellT_le ha ht
    gcongr

lemma continuousOn_boD {a T : ℝ} (ha : 0 < a) (p : ℕ × ℕ) : ContinuousOn (fun t => boD t p) (Icc a T) := by
  unfold boD
  by_cases h : p.1 = p.2
  · simp only [h, if_true]; exact continuousOn_const
  · simp only [h, if_false]; exact continuousOn_bD2 ha p

lemma summable_tt7 : Summable tt7 := summable_tt (σ := 7) (by norm_num)

lemma continuousOn_OftD {a T : ℝ} (ha : 0 < a) : ContinuousOn OftD (Icc a T) :=
  continuousOn_tsum (fun p => continuousOn_boD ha p) (summable_tt7.mul_left (2 * T ^ 2))
    (fun p t ht => norm_boD_le ha ht p)

lemma diag_term_le_D (L : ℝ) (n : ℕ) :
    ‖bb (n + 1) / ((n : ℝ) + 1) * V (2 * lg n - L)‖ ≤
      2 * Real.exp L * (∑' m : ℕ, |((tau (m + 1) : ℤ) : ℝ)| * ((m : ℝ) + 1) ^ (-(7 : ℝ))) *
        (|((tau (n + 1) : ℤ) : ℝ)| * ((n : ℝ) + 1) ^ (-(7 : ℝ))) := by
  set x : ℕ → ℝ := fun n => |((tau (n + 1) : ℤ) : ℝ)| * ((n : ℝ) + 1) ^ (-(7 : ℝ)) with hx
  have hs : Summable x := summable_abs_tau_shift (σ := 7) (by norm_num)
  have hx0 : ∀ n, 0 ≤ x n := fun n => by simp only [hx]; positivity
  have h0 : 0 ≤ bb (n + 1) / ((n : ℝ) + 1) := div_nonneg (bb_nonneg _) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (V_nonneg _))]
  have hV := V_le_exp (2 * lg n - L)
  have hle : x n ≤ ∑' m, x m := hs.le_tsum n (fun m _ => hx0 m)
  calc bb (n + 1) / ((n : ℝ) + 1) * V (2 * lg n - L)
      ≤ bb (n + 1) / ((n : ℝ) + 1) * (2 * Real.exp (-(2 * lg n - L))) := by gcongr
    _ = 2 * Real.exp L * (x n * x n) := by
        rw [mul_left_comm, bb_shift_eq]; simp only [hx]; ring
    _ ≤ 2 * Real.exp L * (∑' m, x m) * x n := by
        have := hx0 n
        have : x n * x n ≤ (∑' m, x m) * x n := mul_le_mul_of_nonneg_right hle this
        nlinarith [Real.exp_pos L]

lemma continuousOn_DsumD {a T : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t => DsumD (2 * ellT t)) (Icc a T) := by
  unfold DsumD
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑' m : ℕ, |((tau (m + 1) : ℤ) : ℝ)| * ((m : ℝ) + 1) ^ (-(7 : ℝ)) :=
    ⟨_, rfl⟩
  refine continuousOn_tsum (fun n => ?_)
    ((summable_abs_tau_shift (σ := 7) (by norm_num)).mul_left (2 * T ^ 2 * S))
    (fun n t ht => ?_)
  · exact ContinuousOn.mul continuousOn_const
      (continuous_V.comp_continuousOn (continuousOn_const.sub
        (continuousOn_const.mul (continuousOn_ellT ha))))
  · refine (diag_term_le_D (2 * ellT t) n).trans ?_
    rw [← hSdef]
    have hS : 0 ≤ S := by rw [hSdef]; exact tsum_nonneg fun m => by positivity
    have h2 := exp_two_ellT_le ha ht
    have hxn : 0 ≤ |((tau (n + 1) : ℤ) : ℝ)| * ((n : ℝ) + 1) ^ (-(7 : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h2 (by norm_num)) hS) hxn

lemma integral_rpow_le' {e a T : ℝ} (he : -1 < e) (ha : 0 < a) (haT : a ≤ T) :
    ∫ t in a..T, t ^ e ≤ T ^ (e + 1) / (e + 1) := by
  have h := integral_rpow_le (c := e + 1) (by linarith) ha haT
  rwa [show e + 1 - 1 = e by ring] at h

/-- **Reduction of Good's second-term theorem to the off-diagonal.** -/
theorem good_reduction :
    ∃ C : ℝ, ∀ T : ℝ, 16 ≤ T →
      ‖(((∫ t in (0:ℝ)..T, ‖tauL (6 + t * I)‖ ^ 2) : ℝ) : ℂ) -
        ((2 * c0 * (T * Real.log (T / (2 * Real.pi))) + (2 * gammaD - 2 * c0) * T : ℝ) : ℂ) -
        OffInt T‖ ≤ C * T ^ (9 / 10 : ℝ) := by
  obtain ⟨CE, hCE0, hCE⟩ := pointwise_err_D
  obtain ⟨CD, hCD0, hCD⟩ := diag_err_D
  set γ := gammaD with hγ
  set K0 : ℝ := |(∫ t in (0:ℝ)..16, zsqD t) - 2 * c0 * (16 * ellT 16 - 16) - 32 * γ| with hK0
  refine ⟨K0 + CD / (9 / 10) + 2 * CE, fun T hT => ?_⟩
  have h16 : (0 : ℝ) < 16 := by norm_num
  have hT0 : 0 < T := by linarith
  have hTc : 1 ≤ T ^ (9 / 10 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hzI : ∀ a b : ℝ, IntervalIntegrable zsqD volume a b := fun a b =>
    continuous_zsqD.intervalIntegrable a b
  have hsplit0 : (∫ t in (0:ℝ)..T, zsqD t) = (∫ t in (0:ℝ)..16, zsqD t) + ∫ t in (16:ℝ)..T, zsqD t :=
    (intervalIntegral.integral_add_adjacent_intervals (hzI 0 16) (hzI 16 T)).symm
  set rest : ℝ → ℂ := fun t => ((zsqD t : ℝ) : ℂ) - (DsumD (2 * ellT t) : ℂ) - OftD t with hrest
  have hcD : ContinuousOn (fun t => ((DsumD (2 * ellT t) : ℝ) : ℂ)) (Icc 16 T) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_DsumD h16)
  have hcO : ContinuousOn OftD (Icc 16 T) := continuousOn_OftD h16
  have hcZ : ContinuousOn (fun t => ((zsqD t : ℝ) : ℂ)) (Icc 16 T) :=
    (Complex.continuous_ofReal.comp continuous_zsqD).continuousOn
  have hiD := hcD |>.intervalIntegrable_of_Icc (μ := volume) hT
  have hiO := hcO |>.intervalIntegrable_of_Icc (μ := volume) hT
  have hiR : IntervalIntegrable rest volume 16 T :=
    ((hcZ.sub hcD).sub hcO) |>.intervalIntegrable_of_Icc (μ := volume) hT
  have hdec : (((∫ t in (16:ℝ)..T, zsqD t) : ℝ) : ℂ) =
      (∫ t in (16:ℝ)..T, ((DsumD (2 * ellT t) : ℝ) : ℂ)) + (∫ t in (16:ℝ)..T, OftD t) +
        ∫ t in (16:ℝ)..T, rest t := by
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_add hiD hiO,
      ← intervalIntegral.integral_add (hiD.add hiO) hiR]
    congr 1; funext t; simp only [hrest]; ring
  have hO : (∫ t in (16:ℝ)..T, OftD t) = OffInt T := by
    unfold OftD OffInt
    exact integral_tsum_Icc hT (fun p => continuousOn_boD h16 p) (summable_tt7.mul_left (2 * T ^ 2))
      (fun p t ht => norm_boD_le h16 ht p)
  have hR : ‖∫ t in (16:ℝ)..T, rest t‖ ≤ 2 * CE * T ^ (9 / 10 : ℝ) := by
    refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun t => CE * t ^ (-(1 / 2 : ℝ))) hT
      (Eventually.of_forall fun t ht => hCE t ht.1.le) ?_).trans ?_
    · exact (continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl ((show (0:ℝ) < x by linarith [hx.1]).ne')))) |>.intervalIntegrable_of_Icc
          (μ := volume) hT
    · rw [intervalIntegral.integral_const_mul]
      have h1 := integral_rpow_le' (e := -(1 / 2 : ℝ)) (by norm_num) h16 hT
      have h2 : T ^ (-(1 / 2 : ℝ) + 1) ≤ T ^ (9 / 10 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have h3 : T ^ (-(1 / 2 : ℝ) + 1) / (-(1 / 2 : ℝ) + 1) = 2 * T ^ (-(1 / 2 : ℝ) + 1) := by ring
      rw [h3] at h1
      calc CE * ∫ t in (16:ℝ)..T, t ^ (-(1 / 2 : ℝ)) ≤ CE * (2 * T ^ (-(1 / 2 : ℝ) + 1)) := by gcongr
        _ ≤ CE * (2 * T ^ (9 / 10 : ℝ)) := by gcongr
        _ = _ := by ring
  set M : ℝ := 2 * c0 * ((T * ellT T - T) - (16 * ellT 16 - 16)) + 2 * γ * (T - 16) with hM
  have hD : |(∫ t in (16:ℝ)..T, DsumD (2 * ellT t)) - M| ≤ CD / (9 / 10) * T ^ (9 / 10 : ℝ) := by
    have hiE : IntervalIntegrable ellT volume 16 T :=
      (continuousOn_ellT h16) |>.intervalIntegrable_of_Icc (μ := volume) hT
    have hmain : ∫ t in (16:ℝ)..T, (2 * c0 * ellT t + 2 * γ) = M := by
      rw [intervalIntegral.integral_add (hiE.const_mul _) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, integral_ellT h16 hT, intervalIntegral.integral_const,
        smul_eq_mul, hM]
      ring
    rw [← hmain, ← intervalIntegral.integral_sub
      ((continuousOn_DsumD h16) |>.intervalIntegrable_of_Icc (μ := volume) hT)
      ((hiE.const_mul _).add intervalIntegrable_const), ← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun t => CD * t ^ (-(1 / 10 : ℝ))) hT
      (Eventually.of_forall fun t ht => ?_) ?_).trans ?_
    · rw [Real.norm_eq_abs, show DsumD (2 * ellT t) - (2 * c0 * ellT t + 2 * γ) =
        DsumD (2 * ellT t) - 2 * c0 * ellT t - 2 * γ by ring]
      exact hCD t ht.1.le
    · exact (continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl ((show (0:ℝ) < x by linarith [hx.1]).ne')))) |>.intervalIntegrable_of_Icc
          (μ := volume) hT
    · rw [intervalIntegral.integral_const_mul]
      have h1 := integral_rpow_le' (e := -(1 / 10 : ℝ)) (by norm_num) h16 hT
      rw [show -(1 / 10 : ℝ) + 1 = 9 / 10 by norm_num] at h1
      calc CD * ∫ t in (16:ℝ)..T, t ^ (-(1 / 10 : ℝ)) ≤ CD * (T ^ (9 / 10 : ℝ) / (9 / 10)) := by gcongr
        _ = _ := by ring
  -- assemble
  set X := ∫ t in (16:ℝ)..T, zsqD t with hX
  have hmainT : (2 * c0 * (T * Real.log (T / (2 * Real.pi))) + (2 * γ - 2 * c0) * T : ℝ) =
      ((∫ t in (0:ℝ)..16, zsqD t) - ((∫ t in (0:ℝ)..16, zsqD t) - 2 * c0 * (16 * ellT 16 - 16) - 32 * γ)) +
        M := by
    rw [hM]; unfold ellT; ring
  have hfin : (((∫ t in (0:ℝ)..T, ‖tauL (6 + t * I)‖ ^ 2) : ℝ) : ℂ) -
      ((2 * c0 * (T * Real.log (T / (2 * Real.pi))) + (2 * γ - 2 * c0) * T : ℝ) : ℂ) - OffInt T =
      ((((∫ t in (0:ℝ)..16, zsqD t) - 2 * c0 * (16 * ellT 16 - 16) - 32 * γ) : ℝ) : ℂ) +
        ((((∫ t in (16:ℝ)..T, DsumD (2 * ellT t)) - M) : ℝ) : ℂ) + ∫ t in (16:ℝ)..T, rest t := by
    have e0 : (∫ t in (0:ℝ)..T, ‖tauL (6 + t * I)‖ ^ 2) = ∫ t in (0:ℝ)..T, zsqD t := rfl
    rw [e0, hsplit0, hmainT, Complex.ofReal_add, hdec, ← hO, intervalIntegral.integral_ofReal]
    push_cast; ring
  rw [hfin]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, ← hK0]
  have hK0' : K0 ≤ K0 * T ^ (9 / 10 : ℝ) := le_mul_of_one_le_right (abs_nonneg _) hTc
  nlinarith

/-- **Good's theorem with second term, conditional on the off-diagonal bound.** -/
theorem good_second_term_of_offdiag {δ : ℝ} (h : OffDiagHyp δ) :
    ∃ C : ℝ, ∀ T : ℝ, 16 ≤ T →
      |(∫ t in (0:ℝ)..T, ‖tauL (6 + t * I)‖ ^ 2) -
        (2 * c0 * (T * Real.log (T / (2 * Real.pi))) + (2 * gammaD - 2 * c0) * T)| ≤
        C * (T ^ (1 - δ) + T ^ (9 / 10 : ℝ)) := by
  obtain ⟨C₁, hC₁⟩ := good_reduction
  obtain ⟨C₂, hC₂⟩ := h
  refine ⟨max C₁ 0 + max C₂ 0, fun T hT => ?_⟩
  have h1 := hC₁ T hT
  have h2 := hC₂ T hT
  set I₀ := ∫ t in (0:ℝ)..T, ‖tauL (6 + t * I)‖ ^ 2
  set m := 2 * c0 * (T * Real.log (T / (2 * Real.pi))) + (2 * gammaD - 2 * c0) * T
  have e : |I₀ - m| = ‖((I₀ : ℝ) : ℂ) - ((m : ℝ) : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [e]
  have htri : ‖((I₀ : ℝ) : ℂ) - ((m : ℝ) : ℂ)‖ ≤
      ‖((I₀ : ℝ) : ℂ) - ((m : ℝ) : ℂ) - OffInt T‖ + ‖OffInt T‖ := by
    have := norm_add_le (((I₀ : ℝ) : ℂ) - ((m : ℝ) : ℂ) - OffInt T) (OffInt T)
    simpa using this
  have hp1 : 0 ≤ T ^ (1 - δ) := by positivity
  have hp2 : 0 ≤ T ^ (9 / 10 : ℝ) := by positivity
  have a1 : C₁ * T ^ (9 / 10 : ℝ) ≤ max C₁ 0 * T ^ (9 / 10 : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hp2
  have a2 : C₂ * T ^ (1 - δ) ≤ max C₂ 0 * T ^ (1 - δ) := mul_le_mul_of_nonneg_right (le_max_left _ _) hp1
  have b1 : 0 ≤ max C₁ 0 * T ^ (1 - δ) := mul_nonneg (le_max_right _ _) hp1
  have b2 : 0 ≤ max C₂ 0 * T ^ (9 / 10 : ℝ) := mul_nonneg (le_max_right _ _) hp2
  nlinarith

end RamanujanTau.GoodSecondTerm
