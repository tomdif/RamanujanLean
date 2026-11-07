/-
# M1(a): joint continuity of the lag diagonal `DiagLag` (removes the regularity clause)

* `continuous_W2sh_line`: `(u,u') ↦ W(6+iu, 6−iu'; ξ)` is continuous (dominated convergence; the
  integrand is bounded by `Γ(8)² ξ^{−2} e⁴/2 · e^{−y²}` uniformly in `(u,u')`).
* `norm_sTerm_le`: `|sTerm u u' (m,n)| ≤ C₀/|Γ(6+iu)Γ(6−iu')| · (4π²)^{−2} g(m) g(n)`,
  `g(m) = |τ(m)|/m⁸` — locally uniform in `(u,u')` since `|Γ(6+iu)Γ(6−iu')|` is continuous, `> 0`.
* `continuous_diagS`: Weierstrass M-test on closed balls (`continuousOn_tsum`).
* `continuous_DiagLag`: `Continuous (uncurry (DiagLag β y))` for every `β, y`.
* `SKSplitHyp'`: `SKSplitHyp` without the continuity clause; `sk_of_split'`,
  `tauL_positive_proportion_of_QF_split'`.
Level 1 / level 2 (on `QFHyp ∧ SKSplitHyp' θ`).
-/
import RamanujanTau.SelbergKey.Main

set_option autoImplicit false

namespace RamanujanTau.SelbergKey2

open Complex MeasureTheory Set Filter Topology RamanujanTau.HeckeL RamanujanTau.HeckeAFE
open RamanujanTau.SelbergKey
open scoped Real

lemma ne_neg_nat_of_re_pos' {w : ℂ} (hw : 0 < w.re) (m : ℕ) : w ≠ -m := by
  intro h; rw [h] at hw; simp at hw; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]

lemma continuous_Gamma_of_re {f : ℝ × ℝ → ℂ} (hf : Continuous f) (hre : ∀ q, 0 < (f q).re) :
    Continuous fun q => Gamma (f q) := by
  rw [continuous_iff_continuousAt]
  intro q
  exact ContinuousAt.comp (g := Gamma)
    (differentiableAt_Gamma _ (ne_neg_nat_of_re_pos' (hre q))).continuousAt hf.continuousAt

lemma continuous_Gpair : Continuous fun q : ℝ × ℝ => Gamma (6 + q.1 * I) * Gamma (6 - q.2 * I) :=
  (continuous_Gamma_of_re (by fun_prop) fun q => by simp).mul
    (continuous_Gamma_of_re (by fun_prop) fun q => by simp)

lemma Gpair_ne (q : ℝ × ℝ) : Gamma (6 + q.1 * I) * Gamma (6 - q.2 * I) ≠ 0 :=
  mul_ne_zero (HafnerProportion.Gamma_line_ne_zero q.1) (Gamma_six_sub_ne q.2)

/-- `(u,u') ↦ W(6+iu, 6−iu'; ξ)` (line `Re z = 2`) is continuous. -/
theorem continuous_W2sh_line {ξ : ℝ} (hξ : 0 < ξ) :
    Continuous fun q : ℝ × ℝ => W2sh (6 + q.1 * I) (6 - q.2 * I) ξ 2 := by
  unfold W2sh vline
  refine continuous_const.mul ?_
  set K : ℝ := Real.Gamma 8 * Real.Gamma 8 * ξ ^ (-(2:ℝ)) * (Real.exp (2 ^ 2) * 2⁻¹)
  have hξ0 : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
  refine continuous_of_dominated (bound := fun y => K * Real.exp (-1 * y ^ 2)) ?_ ?_
    ((integrable_exp_neg_mul_sq one_pos).const_mul K) ?_
  · intro q
    have h1 : (0:ℝ) < (6 + (q.1 : ℂ) * I).re + 2 := by simp; norm_num
    have h2 : (0:ℝ) < (6 - (q.2 : ℂ) * I).re + 2 := by simp; norm_num
    exact (integrable_W2sh_integrand (by norm_num) h1 h2 hξ).aestronglyMeasurable
  · intro q
    refine Eventually.of_forall fun y => ?_
    have h1 : (0:ℝ) < (6 + (q.1 : ℂ) * I).re + 2 := by simp; norm_num
    have h2 : (0:ℝ) < (6 - (q.2 : ℂ) * I).re + 2 := by simp; norm_num
    have := norm_W2sh_integrand_le (c := 2) (by norm_num) h1 h2 hξ y
    have e1 : (6 + (q.1 : ℂ) * I).re + 2 = 8 := by simp; norm_num
    have e2 : (6 - (q.2 : ℂ) * I).re + 2 = 8 := by simp; norm_num
    rw [e1, e2] at this
    exact this
  · refine Eventually.of_forall fun y => ?_
    refine Continuous.div_const ?_ _
    refine Continuous.mul ?_ continuous_const
    refine Continuous.mul ?_ continuous_const
    exact (continuous_Gamma_of_re (by fun_prop) fun q => by simp; norm_num).mul
      (continuous_Gamma_of_re (by fun_prop) fun q => by simp; norm_num)

/-- Each term of the lag series is continuous in `(u,u')`. -/
theorem continuous_sTerm (p : ℕ × ℕ) : Continuous fun q : ℝ × ℝ => sTerm q.1 q.2 p := by
  unfold sTerm Wsh
  obtain ⟨m, n⟩ := p
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [tauC_zero]; exact continuous_const
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tauC_zero]; exact continuous_const
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hξ : (0:ℝ) < 4 * π ^ 2 * m * n := by positivity
  refine Continuous.mul ?_ ((continuous_W2sh_line hξ).div continuous_Gpair Gpair_ne)
  refine Continuous.mul (Continuous.mul continuous_const ?_) ?_
  · exact continuous_iff_continuousAt.2 fun q =>
      ((continuousAt_const_cpow hm0).comp (by fun_prop : Continuous fun q : ℝ × ℝ =>
        -(6 + (q.1 : ℂ) * I)).continuousAt)
  · exact continuous_iff_continuousAt.2 fun q =>
      ((continuousAt_const_cpow hn0).comp (by fun_prop : Continuous fun q : ℝ × ℝ =>
        -(6 - (q.2 : ℂ) * I)).continuousAt)

/-- The constant `C₀ = (2π)⁻¹ Γ(8)² (e⁴/2) ∫ e^{−y²}` of `norm_W2sh_le`. -/
noncomputable def C0 : ℝ := (2 * π)⁻¹ * (Real.Gamma 8 * Real.Gamma 8 * (Real.exp (2 ^ 2) * 2⁻¹) *
      ∫ y : ℝ, Real.exp (-1 * y ^ 2))

lemma C0_nonneg : 0 ≤ C0 := by
  have : 0 ≤ ∫ y : ℝ, Real.exp (-1 * y ^ 2) := integral_nonneg fun _ => (Real.exp_pos _).le
  have := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 8)
  unfold C0; positivity

/-- `g(m) = |τ(m)|/m⁸`. -/
noncomputable def gt (m : ℕ) : ℝ := |(tau m : ℝ)| / (m : ℝ) ^ (8 : ℝ)

lemma summable_gt : Summable gt := RamanujanTau.HeckeConvex.summable_abs_tau_div_rpow (by norm_num)

lemma gt_nonneg (m : ℕ) : 0 ≤ gt m := by unfold gt; positivity

/-- Pointwise bound for the lag series terms. -/
theorem norm_sTerm_le (u u' : ℝ) (p : ℕ × ℕ) :
    ‖sTerm u u' p‖ ≤ (C0 / ‖Gamma (6 + u * I) * Gamma (6 - u' * I)‖ * (4 * π ^ 2) ^ (-(2:ℝ))) *
      (gt p.1 * gt p.2) := by
  set G : ℝ := ‖Gamma (6 + u * I) * Gamma (6 - u' * I)‖
  have hG : 0 < G := norm_pos_iff.mpr (Gpair_ne (u, u'))
  obtain ⟨m, n⟩ := p
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [sTerm, tauC_zero, gt]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sTerm, tauC_zero, gt]
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hξ : (0:ℝ) < 4 * π ^ 2 * m * n := by positivity
  have hW : ‖Wsh u u' (4 * π ^ 2 * m * n)‖ ≤ C0 * (4 * π ^ 2 * m * n) ^ (-(2:ℝ)) / G := by
    unfold Wsh
    rw [norm_div]
    exact div_le_div_of_nonneg_right (norm_W2sh_le (by simp) (by simp) hξ) hG.le
  have hτm : ‖tauC m‖ = |(tau m : ℝ)| := by simp [tauC, Complex.norm_intCast]
  have hτn : ‖tauC n‖ = |(tau n : ℝ)| := by simp [tauC, Complex.norm_intCast]
  unfold sTerm
  simp only
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hτm, hτn, norm_natCast_cpow_of_pos hm,
    norm_natCast_cpow_of_pos hn]
  have e1 : (-(6 + (u : ℂ) * I)).re = -6 := by simp
  have e2 : (-(6 - (u' : ℂ) * I)).re = -6 := by simp
  rw [e1, e2]
  have hsplit : (4 * π ^ 2 * m * n : ℝ) ^ (-(2:ℝ)) =
      (4 * π ^ 2) ^ (-(2:ℝ)) * ((m : ℝ) ^ (-(2:ℝ)) * (n : ℝ) ^ (-(2:ℝ))) := by
    rw [mul_assoc, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hmr.le hnr.le]
  have hm8 : (m : ℝ) ^ (-6:ℝ) * (m : ℝ) ^ (-(2:ℝ)) = 1 / (m : ℝ) ^ (8:ℝ) := by
    rw [← Real.rpow_add hmr, one_div, ← Real.rpow_neg hmr.le]; norm_num
  have hn8 : (n : ℝ) ^ (-6:ℝ) * (n : ℝ) ^ (-(2:ℝ)) = 1 / (n : ℝ) ^ (8:ℝ) := by
    rw [← Real.rpow_add hnr, one_div, ← Real.rpow_neg hnr.le]; norm_num
  have h0 : 0 ≤ |(tau m : ℝ)| * |(tau n : ℝ)| * (m : ℝ) ^ (-6:ℝ) * (n : ℝ) ^ (-6:ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (Real.rpow_nonneg hmr.le _)) (Real.rpow_nonneg hnr.le _)
  calc |(tau m : ℝ)| * |(tau n : ℝ)| * (m : ℝ) ^ (-6:ℝ) * (n : ℝ) ^ (-6:ℝ) *
        ‖Wsh u u' (4 * π ^ 2 * m * n)‖
      ≤ |(tau m : ℝ)| * |(tau n : ℝ)| * (m : ℝ) ^ (-6:ℝ) * (n : ℝ) ^ (-6:ℝ) *
        (C0 * (4 * π ^ 2 * m * n) ^ (-(2:ℝ)) / G) := mul_le_mul_of_nonneg_left hW h0
    _ = (C0 / G * (4 * π ^ 2) ^ (-(2:ℝ))) *
        (|(tau m : ℝ)| * ((m : ℝ) ^ (-6:ℝ) * (m : ℝ) ^ (-(2:ℝ))) *
          (|(tau n : ℝ)| * ((n : ℝ) ^ (-6:ℝ) * (n : ℝ) ^ (-(2:ℝ))))) := by
        rw [hsplit]; ring
    _ = _ := by rw [hm8, hn8]; simp only [gt]; ring

/-- **The diagonal sub-series is jointly continuous.** -/
theorem continuous_diagS (a b c d : ℕ) :
    Continuous fun q : ℝ × ℝ => diagS a b c d q.1 q.2 := by
  rw [continuous_iff_continuousAt]
  intro q₀
  set s : Set (ℝ × ℝ) := Metric.closedBall q₀ 1
  have hs : IsCompact s := isCompact_closedBall q₀ 1
  have hne : s.Nonempty := ⟨q₀, Metric.mem_closedBall_self zero_le_one⟩
  have hGc : Continuous fun q : ℝ × ℝ => ‖Gamma (6 + q.1 * I) * Gamma (6 - q.2 * I)‖ :=
    continuous_norm.comp continuous_Gpair
  obtain ⟨qm, hqm, hmin⟩ := hs.exists_isMinOn hne hGc.continuousOn
  set Gm : ℝ := ‖Gamma (6 + qm.1 * I) * Gamma (6 - qm.2 * I)‖
  have hGm : 0 < Gm := norm_pos_iff.mpr (Gpair_ne qm)
  set U : ℕ × ℕ → ℝ := fun p => (C0 / Gm * (4 * π ^ 2) ^ (-(2:ℝ))) * (gt p.1 * gt p.2)
  have hU : Summable U :=
    (Summable.mul_of_nonneg summable_gt summable_gt gt_nonneg gt_nonneg).mul_left _
  have hon : ContinuousOn (fun q : ℝ × ℝ => diagS a b c d q.1 q.2) s := by
    unfold diagS
    refine continuousOn_tsum (u := U) (fun p => ?_) hU (fun p q hq => ?_)
    · by_cases hp : isDiag a b c d p
      · simp only [hp, if_true]; exact (continuous_sTerm p).continuousOn
      · simp only [hp, if_false]; exact continuousOn_const
    · by_cases hp : isDiag a b c d p
      · simp only [hp, if_true]
        refine (norm_sTerm_le q.1 q.2 p).trans ?_
        have hGq : Gm ≤ ‖Gamma (6 + q.1 * I) * Gamma (6 - q.2 * I)‖ := hmin hq
        have h4 : 0 ≤ (4 * π ^ 2 : ℝ) ^ (-(2:ℝ)) := Real.rpow_nonneg (by positivity) _
        have hgg : 0 ≤ gt p.1 * gt p.2 := mul_nonneg (gt_nonneg _) (gt_nonneg _)
        have : C0 / ‖Gamma (6 + q.1 * I) * Gamma (6 - q.2 * I)‖ ≤ C0 / Gm :=
          div_le_div_of_nonneg_left C0_nonneg hGm hGq
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this h4) hgg
      · simp only [hp, if_false, norm_zero]
        exact mul_nonneg (mul_nonneg (div_nonneg C0_nonneg hGm.le)
          (Real.rpow_nonneg (by positivity) _)) (mul_nonneg (gt_nonneg _) (gt_nonneg _))
  exact hon.continuousAt (Metric.closedBall_mem_nhds q₀ one_pos)

lemma continuous_Ush : Continuous fun q : ℝ × ℝ => Ush q.1 q.2 := by
  unfold Ush
  have h2 : (2 * π : ℂ) ≠ 0 := two_pi_ne_zero
  refine Continuous.div ?_ ?_ fun q => ?_
  · refine Continuous.mul ?_ continuous_Gpair
    exact continuous_iff_continuousAt.2 fun q =>
      ((continuousAt_const_cpow h2).comp (by fun_prop : Continuous fun q : ℝ × ℝ =>
        (((q.2 - q.1 : ℝ) : ℂ) * I)).continuousAt)
  · refine Complex.continuous_ofReal.comp ?_
    exact (continuous_norm.comp (continuous_Gamma_of_re (by fun_prop) fun q => by simp)).mul
      (continuous_norm.comp (continuous_Gamma_of_re (by fun_prop) fun q => by simp))
  · have h1 := norm_pos_iff.mpr (HafnerProportion.Gamma_line_ne_zero q.1)
    have h2' := norm_pos_iff.mpr (HafnerProportion.Gamma_line_ne_zero q.2)
    exact_mod_cast (mul_pos h1 h2').ne'

lemma continuous_eph (a b : ℕ) {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    Continuous fun q => eph a b (f q) := by
  unfold eph; fun_prop

/-- **M1(a): `DiagLag` is jointly continuous.** -/
theorem continuous_DiagLag (β : ℕ → ℝ) (y : ℕ) : Continuous (Function.uncurry (DiagLag β y)) := by
  have hmap : Continuous fun q : ℝ × ℝ => (q.1, q.1 + q.2) := by fun_prop
  have hU := continuous_Ush.comp hmap
  simp only [Function.comp_def] at hU
  have hD : ∀ a b c d, Continuous fun q : ℝ × ℝ => diagS a b c d q.1 (q.1 + q.2) := by
    intro a b c d
    have := (continuous_diagS a b c d).comp hmap
    simp only [Function.comp_def] at this
    exact this
  have hQ : Continuous fun q : ℝ × ℝ =>
      quadSum β y q.1 (q.1 + q.2) (fun a b c d => diagS a b c d q.1 (q.1 + q.2)) := by
    unfold quadSum
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun d _ => ?_
    exact ((continuous_const.mul (continuous_eph a b continuous_fst)).mul
      (continuous_const.mul (continuous_eph c d (continuous_fst.add continuous_snd)))).mul (hD a b c d)
  have : Function.uncurry (DiagLag β y) = fun q : ℝ × ℝ =>
      2 * (Ush q.1 (q.1 + q.2) *
        quadSum β y q.1 (q.1 + q.2) (fun a b c d => diagS a b c d q.1 (q.1 + q.2))).re := by
    funext q; rfl
  rw [this]
  exact continuous_const.mul (Complex.continuous_re.comp (hU.mul hQ))

/-- **`SKSplitHyp` without the regularity clause.** -/
def SKSplitHyp' (θ : ℝ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ ∀ K : ℝ, 1 ≤ K → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    ∃ (φ : ℝ → ℝ) (A B : ℝ), Admissible T A B φ ∧
      lagInt (DiagLag (HafnerMV2.βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊) φ A B (K / Real.log T) ≤
        D / Real.sqrt K * T * (K / Real.log T) ^ 2 ∧
      lagInt (OffLag (HafnerMV2.βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊) φ A B (K / Real.log T) ≤
        1 / Real.sqrt K * T * (K / Real.log T) ^ 2

theorem splitHyp_of_splitHyp' {θ : ℝ} (H : SKSplitHyp' θ) : SKSplitHyp θ := by
  obtain ⟨D, hD, hK⟩ := H
  refine ⟨D, hD, fun K hK1 => ?_⟩
  obtain ⟨T₀, hT₀⟩ := hK K hK1
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨φ, A, B, hadm, hdiag, hoff⟩ := hT₀ T hT
  exact ⟨φ, A, B, hadm, continuous_DiagLag _ _, hdiag, hoff⟩

/-- **Hafner's positive proportion, conditional on `QFHyp ∧ SKSplitHyp' θ`** (level 2). -/
theorem tauL_positive_proportion_of_QF_split' {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 81600)
    (hQ : HafnerBridge.QFHyp) (hS : SKSplitHyp' θ) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ γ ∈ S, 0 < γ ∧ γ ≤ 3 * T ∧ tauL (6 + γ * I) = 0) ∧
        c * (ZeroCount.zeroCount (3 * T) : ℝ) ≤ S.card :=
  tauL_positive_proportion_of_QF_split hθ0 hθ hQ (splitHyp_of_splitHyp' hS)

end RamanujanTau.SelbergKey2
