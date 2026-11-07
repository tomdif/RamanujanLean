/-
# M3 step 3c: evaluation of the base sum

With `A(t) = c₀ log t + γ_Δ + E(t)`, `|E(t)| ≤ C t^{−1/5}` (`AA_asymp`), integration by parts gives

    Σ_n (λ(n)²/n) n^{iv} W̃(αn²) = γ_Δ W̃(α) + c₀ J(α) − iv ε(v) + O((α/T(u)T(u+v))^{1/20})

uniformly in `u`, `|v| ≤ 1`, `α > 0` (`base_eval`), where `J(α) = ∫₁^∞ t^{iv−1} W̃(αt²) dt` and
`ε(v) = ∫₁^∞ t^{iv−1} E(t) dt` does not depend on `u` or `α`.  Level 1.
-/
import RamanujanTau.SelbergKeyDiag2.Base2

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex MeasureTheory Set Filter Topology Finset RamanujanTau.HeckeAFE RamanujanTau.SelbergKey
  RamanujanTau.SelbergKey2
open RamanujanTau.GoodSecondTerm (AA bb c0 gammaD AA_asymp bb_nonneg)
open scoped Real

/-- `E(t) = A(t) − c₀ log t − γ_Δ`. -/
noncomputable def Et (t : ℝ) : ℝ := AA ⌊t⌋₊ - c0 * Real.log t - gammaD

/-- `ε(v) = ∫₁^∞ t^{iv−1} E(t) dt`. -/
noncomputable def epsv (v : ℝ) : ℂ := ∫ t in Ioi (1:ℝ), (t : ℂ) ^ ((v : ℂ) * I - 1) * (Et t : ℂ)

/-- `J(α) = ∫₁^∞ t^{iv−1} W̃(αt²) dt`. -/
noncomputable def Jv (u v α : ℝ) : ℂ :=
  ∫ t in Ioi (1:ℝ), (t : ℂ) ^ ((v : ℂ) * I - 1) * Wsh u (u + v) (α * t ^ 2)

lemma Et_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → |Et t| ≤ C * t ^ (-(1 / 5 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := AA_asymp
  refine ⟨2 * C + 2 * |c0|, by positivity, fun t ht => ?_⟩
  set N := ⌊t⌋₊
  have hN : 1 ≤ N := Nat.one_le_floor_iff _ |>.2 ht
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNt : (N : ℝ) ≤ t := Nat.floor_le (by linarith)
  have htN : t < N + 1 := Nat.lt_floor_add_one t
  have hN2 : t / 2 ≤ N := by linarith
  have h1 := hC N hN
  have ht0 : 0 < t := by linarith
  have hN0 : (0:ℝ) < N := by linarith
  -- `0 ≤ log t − log N ≤ 1/N ≤ 2/t`
  have hl0 : 0 ≤ Real.log t - Real.log N := by
    have := Real.log_le_log hN0 hNt; linarith
  have hl1 : Real.log t - Real.log N ≤ 2 / t := by
    rw [← Real.log_div ht0.ne' hN0.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one hN0.ne', div_le_div_iff₀ hN0 ht0]; nlinarith
  have hpow : (N : ℝ) ^ (-(1 / 5 : ℝ)) ≤ 2 * t ^ (-(1 / 5 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos (by positivity) hN2 (by norm_num : (-(1 / 5 : ℝ)) ≤ 0)
    rw [Real.div_rpow ht0.le (by norm_num)] at h
    refine h.trans ?_
    rw [div_eq_mul_inv, mul_comm]
    gcongr
    rw [← Real.rpow_neg (by norm_num)]; norm_num
    calc (2:ℝ) ^ (1 / 5 : ℝ) ≤ 2 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h2t : 2 / t ≤ 2 * t ^ (-(1 / 5 : ℝ)) := by
    rw [div_eq_mul_inv]; gcongr
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
  have e : Et t = (AA N - c0 * Real.log N - gammaD) - c0 * (Real.log t - Real.log N) := by
    unfold Et; ring
  rw [e]
  calc |AA N - c0 * Real.log N - gammaD - c0 * (Real.log t - Real.log N)|
      ≤ |AA N - c0 * Real.log N - gammaD| + |c0| * (Real.log t - Real.log N) := by
        refine (abs_sub _ _).trans ?_; rw [abs_mul, abs_of_nonneg hl0]
    _ ≤ C * (2 * t ^ (-(1 / 5 : ℝ))) + |c0| * (2 * t ^ (-(1 / 5 : ℝ))) := by
        gcongr
        · exact h1.trans (mul_le_mul_of_nonneg_left hpow hC0)
        · exact hl1.trans h2t
    _ = _ := by ring

lemma measurable_Et : Measurable Et := by
  unfold Et
  exact (((measurable_from_nat (f := AA)).comp Nat.measurable_floor).sub
    (measurable_const.mul Real.measurable_log)).sub measurable_const

lemma integrableOn_of_le {g : ℝ → ℂ} (hg : AEStronglyMeasurable g (volume.restrict (Ioi (1:ℝ))))
    {K a : ℝ} (ha : a < -1) (hb : ∀ t ∈ Ioi (1:ℝ), ‖g t‖ ≤ K * t ^ a) : IntegrableOn g (Ioi 1) :=
  Integrable.mono' ((integrableOn_Ioi_rpow_of_lt ha one_pos).const_mul K) hg
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hb))

lemma norm_integral_le_rpow {g : ℝ → ℂ} {K : ℝ} (hb : ∀ t ∈ Ioi (1:ℝ), ‖g t‖ ≤ K * t ^ (-(11 / 10 : ℝ))) :
    ‖∫ t in Ioi (1:ℝ), g t‖ ≤ 10 * K := by
  have hint := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(11 / 10 : ℝ)) < -1) one_pos).const_mul K
  refine (norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall hb))).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
  norm_num; ring

lemma continuousOn_cpow_Ioi (w : ℂ) : ContinuousOn (fun t : ℝ => (t : ℂ) ^ w) (Ioi 0) :=
  fun _ ht => (hasDerivAt_ofReal_cpow' ht w).continuousAt.continuousWithinAt

lemma continuousOn_W (u v α : ℝ) (hα : 0 < α) :
    ContinuousOn (fun t : ℝ => Wsh u (u + v) (α * t ^ 2)) (Ioi 0) := by
  intro t ht
  have ht0 : (0:ℝ) < t := ht
  have h1 := (hasDerivAt_Wd u v (show 0 < α * t ^ 2 by positivity)).continuousAt
  exact (ContinuousAt.comp (g := fun ξ => Wsh u (u + v) ξ) (f := fun s : ℝ => α * s ^ 2) h1
    (by fun_prop)).continuousWithinAt

lemma aesm_of_contOn {g : ℝ → ℂ} (hg : ContinuousOn g (Ioi 0)) :
    AEStronglyMeasurable g (volume.restrict (Ioi (1:ℝ))) :=
  (hg.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi

lemma measurable_Wd_comp (u v α : ℝ) : Measurable fun t : ℝ => Wd u v (α * t ^ 2) := by
  unfold Wd
  exact (measurable_deriv _).comp (by fun_prop : Continuous fun s : ℝ => α * s ^ 2).measurable

/-- **Evaluation of the base sum.** -/
theorem base_eval : ∃ K : ℝ, 0 ≤ K ∧ ∀ u v α : ℝ, 0 < α → |v| ≤ 1 →
    ‖(∑' n : ℕ, cA n * ft u v α n) -
        ((gammaD : ℂ) * Wsh u (u + v) α + (c0 : ℂ) * Jv u v α - (v : ℂ) * I * epsv v)‖ ≤
      K * (α / TT u v) ^ (1 / 20 : ℝ) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := Et_bound
  obtain ⟨CW, hCW0, hCW⟩ := Wsh_sub_one (c := 1 / 20) (by norm_num) (by norm_num)
  obtain ⟨Cd, hCd0, hCd⟩ := norm_xi_Wd_small
  refine ⟨10 * (CW * C₁) + 10 * (2 * Cd * C₁), by positivity, fun u v α hα hv => ?_⟩
  obtain ⟨K₁, hK₁0, hK₁⟩ := ft_decay u v hα
  obtain ⟨K₂, hK₂0, hK₂⟩ := ft'_decay u v hα
  have hT := TT_pos u v
  set r := α / TT u v with hr
  have hr0 : 0 < r := div_pos hα hT
  -- pointwise facts on `t > 1`
  have hrt : ∀ t : ℝ, 0 < t → (α * t ^ 2 / TT u v) ^ (1 / 20 : ℝ) = r ^ (1 / 20 : ℝ) * t ^ (1 / 10 : ℝ) := by
    intro t ht
    rw [show α * t ^ 2 / TT u v = r * t ^ 2 by rw [hr]; ring, Real.mul_rpow hr0.le (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  have hEt : ∀ t ∈ Ioi (1:ℝ), ‖((Et t : ℝ) : ℂ)‖ ≤ C₁ * t ^ (-(1 / 5 : ℝ)) := by
    intro t ht; rw [Complex.norm_real, Real.norm_eq_abs]; exact hC₁ t (le_of_lt ht)
  have hEm : AEStronglyMeasurable (fun t : ℝ => ((Et t : ℝ) : ℂ)) (volume.restrict (Ioi (1:ℝ))) :=
    (Complex.measurable_ofReal.comp measurable_Et).aestronglyMeasurable
  -- the error integrands
  set e1 : ℝ → ℂ := fun t => (t : ℂ) ^ ((v : ℂ) * I - 1) * (Wsh u (u + v) (α * t ^ 2) - 1) * (Et t : ℂ)
  set e2 : ℝ → ℂ := fun t => (t : ℂ) ^ ((v : ℂ) * I) * ((2 * α * t : ℝ) : ℂ) * Wd u v (α * t ^ 2) * (Et t : ℂ)
  have hb1 : ∀ t ∈ Ioi (1:ℝ), ‖e1 t‖ ≤ (CW * C₁ * r ^ (1 / 20 : ℝ)) * t ^ (-(11 / 10 : ℝ)) := by
    intro t ht
    have ht0 : (0:ℝ) < t := lt_trans one_pos ht
    simp only [e1]
    rw [norm_mul, norm_mul, norm_cpow_I_sub_one ht0]
    have h1 := hCW u (u + v) (α * t ^ 2) (by positivity)
    have h1' : ‖Wsh u (u + v) (α * t ^ 2) - 1‖ ≤ CW * (r ^ (1 / 20 : ℝ) * t ^ (1 / 10 : ℝ)) := by
      rw [← hrt t ht0]; exact h1
    calc t⁻¹ * ‖Wsh u (u + v) (α * t ^ 2) - 1‖ * ‖((Et t : ℝ) : ℂ)‖
        ≤ t⁻¹ * (CW * (r ^ (1 / 20 : ℝ) * t ^ (1 / 10 : ℝ))) * (C₁ * t ^ (-(1 / 5 : ℝ))) := by
          gcongr; exact hEt t ht
      _ = (CW * C₁ * r ^ (1 / 20 : ℝ)) * (t⁻¹ * t ^ (1 / 10 : ℝ) * t ^ (-(1 / 5 : ℝ))) := by ring
      _ = _ := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add ht0, ← Real.rpow_add ht0]; norm_num
  have hb2 : ∀ t ∈ Ioi (1:ℝ), ‖e2 t‖ ≤ (2 * Cd * C₁ * r ^ (1 / 20 : ℝ)) * t ^ (-(11 / 10 : ℝ)) := by
    intro t ht
    have ht0 : (0:ℝ) < t := lt_trans one_pos ht
    simp only [e2]
    have e : (t : ℂ) ^ ((v : ℂ) * I) * ((2 * α * t : ℝ) : ℂ) * Wd u v (α * t ^ 2) * (Et t : ℂ) =
        (t : ℂ) ^ ((v : ℂ) * I) * ((2 / t : ℝ) : ℂ) * (((α * t ^ 2 : ℝ) : ℂ) * Wd u v (α * t ^ 2)) *
          (Et t : ℂ) := by
      push_cast; field_simp
    rw [e, norm_mul, norm_mul, norm_mul, norm_cpow_I ht0, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    have h1 := hCd u v (α * t ^ 2) (by positivity)
    rw [hrt t ht0] at h1
    calc 1 * (2 / t) * ‖((α * t ^ 2 : ℝ) : ℂ) * Wd u v (α * t ^ 2)‖ * ‖((Et t : ℝ) : ℂ)‖
        ≤ 1 * (2 / t) * (Cd * (r ^ (1 / 20 : ℝ) * t ^ (1 / 10 : ℝ))) * (C₁ * t ^ (-(1 / 5 : ℝ))) := by
          gcongr; exact hEt t ht
      _ = (2 * Cd * C₁ * r ^ (1 / 20 : ℝ)) * (t⁻¹ * t ^ (1 / 10 : ℝ) * t ^ (-(1 / 5 : ℝ))) := by ring
      _ = _ := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add ht0, ← Real.rpow_add ht0]; norm_num
  have hn1 := norm_integral_le_rpow hb1
  have hn2 := norm_integral_le_rpow hb2
  -- measurability
  have hft'm : AEStronglyMeasurable (ft' u v α) (volume.restrict (Ioi (1:ℝ))) :=
    ((measurable_deriv (ft u v α)).aestronglyMeasurable).congr
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht =>
        (hasDerivAt_ft u v hα (lt_trans one_pos ht)).deriv))
  have hftc : ContinuousOn (ft u v α) (Ioi 0) := fun t ht =>
    (hasDerivAt_ft u v hα ht).continuousAt.continuousWithinAt
  have hcp1 := continuousOn_cpow_Ioi ((v : ℂ) * I - 1)
  have hcp0 := continuousOn_cpow_Ioi ((v : ℂ) * I)
  have hWc := continuousOn_W u v α hα
  have hWdm := measurable_Wd_comp u v α
  set L : ℝ → ℂ := fun t => ((c0 * Real.log t + gammaD : ℝ) : ℂ) with hL
  have hLb : ∀ t ∈ Ioi (1:ℝ), ‖L t‖ ≤ (|c0| + |gammaD|) * t := by
    intro t ht
    have ht1 : (1:ℝ) ≤ t := le_of_lt ht
    rw [hL, Complex.norm_real, Real.norm_eq_abs]
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hlog : Real.log t ≤ t := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    calc |c0 * Real.log t + gammaD| ≤ |c0| * Real.log t + |gammaD| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_of_nonneg hlog0]
      _ ≤ |c0| * t + |gammaD| * t := by gcongr; nlinarith [abs_nonneg gammaD]
      _ = _ := by ring
  have hLm : AEStronglyMeasurable L (volume.restrict (Ioi (1:ℝ))) :=
    (Complex.measurable_ofReal.comp ((measurable_const.mul Real.measurable_log).add
      measurable_const)).aestronglyMeasurable
  -- integrability
  have i1 : IntegrableOn (fun t => ft' u v α t * L t) (Ioi 1) := by
    refine integrableOn_of_le (hft'm.mul hLm) (K := K₂ * (|c0| + |gammaD|)) (a := -4) (by norm_num)
      fun t ht => ?_
    have ht0 : (0:ℝ) < t := lt_trans one_pos ht
    rw [norm_mul]
    calc ‖ft' u v α t‖ * ‖L t‖ ≤ (K₂ * t⁻¹ ^ 5) * ((|c0| + |gammaD|) * t) :=
          mul_le_mul (hK₂ t ht0) (hLb t ht) (norm_nonneg _) (by positivity)
      _ = K₂ * (|c0| + |gammaD|) * t ^ (-4:ℝ) := by
          rw [Real.rpow_neg ht0.le, show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
          field_simp
  have i2 : IntegrableOn (fun t => ft' u v α t * (Et t : ℂ)) (Ioi 1) := by
    refine integrableOn_of_le (hft'm.mul hEm) (K := K₂ * C₁) (a := -5) (by norm_num) fun t ht => ?_
    have ht0 : (0:ℝ) < t := lt_trans one_pos ht
    rw [norm_mul]
    have hp : t ^ (-(1 / 5 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt ht) (by norm_num)
    calc ‖ft' u v α t‖ * ‖((Et t : ℝ) : ℂ)‖ ≤ (K₂ * t⁻¹ ^ 5) * (C₁ * 1) :=
          mul_le_mul (hK₂ t ht0) ((hEt t ht).trans (by gcongr)) (norm_nonneg _) (by positivity)
      _ = K₂ * C₁ * t ^ (-5:ℝ) := by
          rw [Real.rpow_neg ht0.le, show (5:ℝ) = ((5:ℕ):ℝ) by norm_num, Real.rpow_natCast, inv_pow]
          ring
  have i3 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((v : ℂ) * I - 1) * (Et t : ℂ)) (Ioi 1) := by
    refine integrableOn_of_le ((aesm_of_contOn hcp1).mul hEm) (K := C₁) (a := -(6 / 5)) (by norm_num)
      fun t ht => ?_
    have ht0 : (0:ℝ) < t := lt_trans one_pos ht
    rw [norm_mul, norm_cpow_I_sub_one ht0]
    calc t⁻¹ * ‖((Et t : ℝ) : ℂ)‖ ≤ t⁻¹ * (C₁ * t ^ (-(1 / 5 : ℝ))) := by gcongr; exact hEt t ht
      _ = C₁ * (t⁻¹ * t ^ (-(1 / 5 : ℝ))) := by ring
      _ = C₁ * t ^ (-(6 / 5 : ℝ)) := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add ht0]; norm_num
  have ie1 : IntegrableOn e1 (Ioi 1) :=
    integrableOn_of_le (((aesm_of_contOn hcp1).mul ((aesm_of_contOn hWc).sub aestronglyMeasurable_const)).mul hEm)
      (by norm_num) hb1
  have ie2 : IntegrableOn e2 (Ioi 1) := by
    have hm : AEStronglyMeasurable (fun t : ℝ => ((2 * α * t : ℝ) : ℂ)) (volume.restrict (Ioi (1:ℝ))) :=
      (by fun_prop : Continuous fun t : ℝ => ((2 * α * t : ℝ) : ℂ)).aestronglyMeasurable
    exact integrableOn_of_le ((((aesm_of_contOn hcp0).mul hm).mul hWdm.aestronglyMeasurable).mul hEm)
      (by norm_num) hb2
  -- integration by parts for the `c₀ log t + γ` part
  have hibp : ∫ t in Ioi (1:ℝ), L t * ft' u v α t =
      0 - (gammaD : ℂ) * Wsh u (u + v) α - ∫ t in Ioi (1:ℝ), ((c0 / t : ℝ) : ℂ) * ft u v α t := by
    have hu : ∀ t ∈ Ioi (1:ℝ), HasDerivAt L ((c0 / t : ℝ) : ℂ) t := by
      intro t ht
      have ht0 : t ≠ 0 := (lt_trans one_pos ht).ne'
      have := (((Real.hasDerivAt_log ht0).const_mul c0).add_const gammaD).ofReal_comp
      simpa [hL, div_eq_mul_inv] using this
    have hvd : ∀ t ∈ Ioi (1:ℝ), HasDerivAt (ft u v α) (ft' u v α t) t :=
      fun t ht => hasDerivAt_ft u v hα (lt_trans one_pos ht)
    have huv' : IntegrableOn (L * ft' u v α) (Ioi 1) := by
      refine i1.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply]; ring
    have hu'v : IntegrableOn ((fun t : ℝ => ((c0 / t : ℝ) : ℂ)) * ft u v α) (Ioi 1) := by
      have hm : AEStronglyMeasurable (fun t : ℝ => ((c0 / t : ℝ) : ℂ)) (volume.restrict (Ioi (1:ℝ))) :=
        (Complex.measurable_ofReal.comp (measurable_const.div measurable_id)).aestronglyMeasurable
      refine integrableOn_of_le (hm.mul (aesm_of_contOn hftc)) (K := |c0| * K₁) (a := -5) (by norm_num)
        fun t ht => ?_
      have ht0 : (0:ℝ) < t := lt_trans one_pos ht
      simp only [Pi.mul_apply]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos ht0]
      calc |c0| / t * ‖ft u v α t‖ ≤ |c0| / t * (K₁ * t⁻¹ ^ 4) := by gcongr; exact hK₁ t ht0
        _ = |c0| * K₁ * t ^ (-5:ℝ) := by
            rw [Real.rpow_neg ht0.le, show (5:ℝ) = ((5:ℕ):ℝ) by norm_num, Real.rpow_natCast]
            field_simp
    have h0 : Tendsto (L * ft u v α) (𝓝[>] 1) (𝓝 ((gammaD : ℂ) * Wsh u (u + v) α)) := by
      have hc : ContinuousAt (L * ft u v α) 1 := by
        refine ContinuousAt.mul ?_ (hasDerivAt_ft u v hα one_pos).continuousAt
        exact (Complex.continuous_ofReal.continuousAt).comp
          ((continuousAt_const.mul (Real.continuousAt_log one_ne_zero)).add continuousAt_const)
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1:ℝ)))
      convert this using 2
      simp [hL, ft]
    have hinf : Tendsto (L * ft u v α) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_
        ((tendsto_const_nhds (x := (|c0| + |gammaD|) * K₁)).div_atTop tendsto_id)
      filter_upwards [eventually_gt_atTop 1] with t ht
      have ht0 : (0:ℝ) < t := lt_trans one_pos ht
      simp only [Pi.mul_apply, id]
      rw [norm_mul]
      calc ‖L t‖ * ‖ft u v α t‖ ≤ ((|c0| + |gammaD|) * t) * (K₁ * t⁻¹ ^ 4) :=
            mul_le_mul (hLb t ht) (hK₁ t ht0) (norm_nonneg _) (by positivity)
        _ ≤ (|c0| + |gammaD|) * K₁ / t := by
            rw [le_div_iff₀ ht0]
            have e : (|c0| + |gammaD|) * t * (K₁ * t⁻¹ ^ 4) * t = (|c0| + |gammaD|) * K₁ * (t ^ 2)⁻¹ := by
              field_simp
            rw [e]
            have : (t ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
            have h00 : 0 ≤ (|c0| + |gammaD|) * K₁ := by positivity
            nlinarith
    exact integral_Ioi_mul_deriv_eq_deriv_mul hu hvd huv' hu'v h0 hinf
  have hJ : ∫ t in Ioi (1:ℝ), ((c0 / t : ℝ) : ℂ) * ft u v α t = (c0 : ℂ) * Jv u v α := by
    unfold Jv
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0:ℝ) < t := lt_trans one_pos ht
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    unfold ft
    rw [Complex.cpow_sub _ _ htc, Complex.cpow_one]
    push_cast
    field_simp
  -- assemble
  have hsplit : ∀ t ∈ Ioi (1:ℝ), ft' u v α t * (AA ⌊t⌋₊ : ℂ) =
      L t * ft' u v α t + ((v : ℂ) * I * ((t : ℂ) ^ ((v : ℂ) * I - 1) * (Et t : ℂ)) +
        (v : ℂ) * I * e1 t + e2 t) := by
    intro t ht
    simp only [hL, e1, e2, ft', Et]
    push_cast
    ring
  have hA := base_abel u v hα
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit] at hA
  have i1' : IntegrableOn (fun t => L t * ft' u v α t) (Ioi 1) :=
    i1.congr_fun (fun t _ => mul_comm _ _) measurableSet_Ioi
  have hI : ∫ t in Ioi (1:ℝ), (L t * ft' u v α t + ((v : ℂ) * I * ((t : ℂ) ^ ((v : ℂ) * I - 1) * (Et t : ℂ)) +
      (v : ℂ) * I * e1 t + e2 t)) = (∫ t in Ioi (1:ℝ), L t * ft' u v α t) +
      ((v : ℂ) * I * epsv v + (v : ℂ) * I * (∫ t in Ioi (1:ℝ), e1 t) + ∫ t in Ioi (1:ℝ), e2 t) := by
    have j1 : IntegrableOn (fun t : ℝ => (v : ℂ) * I * ((t : ℂ) ^ ((v : ℂ) * I - 1) * (Et t : ℂ))) (Ioi 1) :=
      i3.const_mul _
    have j2 : IntegrableOn (fun t => (v : ℂ) * I * e1 t) (Ioi 1) := ie1.const_mul _
    have a1 := integral_add i1' ((j1.add j2).add ie2)
    have a2 := integral_add (j1.add j2) ie2
    have a3 := integral_add j1 j2
    simp only [Pi.add_apply] at a1 a2 a3
    rw [a1, a2, a3, integral_const_mul, integral_const_mul]
    rfl
  rw [hI, hibp, hJ] at hA
  rw [hA]
  have e : -(0 - (gammaD : ℂ) * Wsh u (u + v) α - (c0 : ℂ) * Jv u v α +
      ((v : ℂ) * I * epsv v + (v : ℂ) * I * (∫ t in Ioi (1:ℝ), e1 t) + (∫ t in Ioi (1:ℝ), e2 t))) -
      ((gammaD : ℂ) * Wsh u (u + v) α + (c0 : ℂ) * Jv u v α - (v : ℂ) * I * epsv v) =
      -((v : ℂ) * I * (∫ t in Ioi (1:ℝ), e1 t)) - (∫ t in Ioi (1:ℝ), e2 t) := by ring
  rw [e]
  have hvI : ‖(v : ℂ) * I‖ ≤ 1 := by rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hv
  calc ‖-((v : ℂ) * I * (∫ t in Ioi (1:ℝ), e1 t)) - (∫ t in Ioi (1:ℝ), e2 t)‖
      ≤ ‖(v : ℂ) * I‖ * ‖∫ t in Ioi (1:ℝ), e1 t‖ + ‖∫ t in Ioi (1:ℝ), e2 t‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_neg, norm_mul]
    _ ≤ 1 * (10 * (CW * C₁ * r ^ (1 / 20 : ℝ))) + 10 * (2 * Cd * C₁ * r ^ (1 / 20 : ℝ)) := by
        gcongr
    _ = _ := by ring

end RamanujanTau.SelbergKeyDiag2
