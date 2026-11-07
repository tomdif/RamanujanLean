/-
# The mean-square function `P(w) = ∫ G(w − 2πiξ) G(w + 2πiξ) dξ` is holomorphic on `23/4 < Re w < 6`

`G(s) = L(Δ,s)/s`.  For real `σ` (and real coefficients) `P(σ) = ∫ |G(σ − 2πiξ)|² dξ`, the
Plancherel side of `∫ A(x)² x^{−2σ−1} dx`.

* `differentiableOn_intervalIntegral`: holomorphy of `w ↦ ∫_a^b F(w,ξ) dξ` for `F`, `∂_w F` jointly
  continuous (`hasDerivAt_integral_of_dominated_loc_of_deriv_le` with a compactness bound);
* `norm_Qd_le`: `|G(w−2πiξ)G(w+2πiξ)| ≤ (Ψ_σ(η−2πξ) + Ψ_σ(η+2πξ))/2`, `w = σ + iη`;
* `tail_Qd`: `|P(w) − P_N(w)| ≤ 4 ∫_N^∞ Ψ_σ` once `N ≥ |η|`;
* `differentiableOn_P`: locally uniform limit (`Tail.tail_bound`, uniform in `σ`) of the
  holomorphic `P_N`.
-/
import RamanujanTau.Voronoi.Tail

set_option autoImplicit false

namespace RamanujanTau.Voronoi

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.HeckeL
open scoped ComplexConjugate Real Interval

/-! ### Holomorphy of parametric integrals over compact intervals -/

theorem differentiableOn_intervalIntegral {U : Set ℂ} (hU : IsOpen U) {F F' : ℂ → ℝ → ℂ}
    (hFc : ContinuousOn (fun p : ℂ × ℝ => F p.1 p.2) (U ×ˢ univ))
    (hF'c : ContinuousOn (fun p : ℂ × ℝ => F' p.1 p.2) (U ×ˢ univ))
    (hd : ∀ w ∈ U, ∀ ξ, HasDerivAt (fun w => F w ξ) (F' w ξ) w) (a b : ℝ) :
    DifferentiableOn ℂ (fun w => ∫ ξ in a..b, F w ξ) U := by
  intro w0 hw0
  obtain ⟨r, hr0, hr⟩ := Metric.isOpen_iff.1 hU w0 hw0
  have hcb : Metric.closedBall w0 (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hr
  have hK : IsCompact (Metric.closedBall w0 (r / 2) ×ˢ Set.uIcc a b) :=
    (isCompact_closedBall _ _).prod isCompact_uIcc
  have hKsub : Metric.closedBall w0 (r / 2) ×ˢ Set.uIcc a b ⊆ U ×ˢ univ :=
    prod_mono hcb (subset_univ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hF'c.mono hKsub)
  have hcont : ∀ w ∈ U, Continuous fun ξ => F w ξ := fun w hw =>
    hFc.comp_continuous (continuous_const.prodMk continuous_id) (fun ξ => ⟨hw, mem_univ _⟩)
  have hcont' : ∀ w ∈ U, Continuous fun ξ => F' w ξ := fun w hw =>
    hF'c.comp_continuous (continuous_const.prodMk continuous_id) (fun ξ => ⟨hw, mem_univ _⟩)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := a) (b := b) (F := F) (F' := F') (x₀ := w0) (bound := fun _ => C)
    (s := Metric.ball w0 (r / 2)) (Metric.ball_mem_nhds w0 (by linarith))
    (by
      filter_upwards [hU.mem_nhds hw0] with w hw
      exact (hcont w hw).aestronglyMeasurable)
    ((hcont w0 hw0).intervalIntegrable _ _)
    ((hcont' w0 hw0).aestronglyMeasurable)
    (Eventually.of_forall fun t ht w hw => hC (w, t) ⟨Metric.ball_subset_closedBall hw,
      Set.uIoc_subset_uIcc ht⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ w hw => hd w (hcb (Metric.ball_subset_closedBall hw)) t)
  exact key.2.differentiableAt.differentiableWithinAt

/-! ### `G(s) = L(Δ,s)/s` -/

/-- `G(s) = L(Δ,s)/s`. -/
noncomputable def Gt (s : ℂ) : ℂ := tauL s / s

/-- The right half-plane. -/
def Hp : Set ℂ := {s | 0 < s.re}

lemma isOpen_Hp : IsOpen Hp := isOpen_lt continuous_const continuous_re

lemma differentiableOn_Gt : DifferentiableOn ℂ Gt Hp := by
  refine tauLSeries_entire.differentiableOn.div differentiableOn_id fun s hs h => ?_
  have : (0 : ℝ) < s.re := hs
  rw [h] at this; simp at this

lemma continuousOn_deriv_Gt : ContinuousOn (deriv Gt) Hp :=
  (differentiableOn_Gt.deriv isOpen_Hp).continuousOn

lemma hasDerivAt_Gt {s : ℂ} (hs : s ∈ Hp) : HasDerivAt Gt (deriv Gt s) s :=
  ((differentiableOn_Gt s hs).differentiableAt (isOpen_Hp.mem_nhds hs)).hasDerivAt

/-- `Q(w,ξ) = G(w − 2πiξ) G(w + 2πiξ)`. -/
noncomputable def Qd (w : ℂ) (ξ : ℝ) : ℂ :=
  Gt (w - 2 * π * ξ * I) * Gt (w + 2 * π * ξ * I)

/-- `∂_w Q`. -/
noncomputable def Qd' (w : ℂ) (ξ : ℝ) : ℂ :=
  deriv Gt (w - 2 * π * ξ * I) * Gt (w + 2 * π * ξ * I) +
    Gt (w - 2 * π * ξ * I) * deriv Gt (w + 2 * π * ξ * I)

/-- `P(w) = ∫ Q(w,ξ) dξ`. -/
noncomputable def P (w : ℂ) : ℂ := ∫ ξ : ℝ, Qd w ξ

/-- `P_N(w) = ∫_{−N}^{N} Q(w,ξ) dξ`. -/
noncomputable def PN (N : ℕ) (w : ℂ) : ℂ := ∫ ξ in (-(N : ℝ))..(N : ℝ), Qd w ξ

lemma mem_Hp_sub {w : ℂ} (hw : w ∈ Hp) (ξ : ℝ) : w - 2 * π * ξ * I ∈ Hp := by
  show 0 < (w - 2 * π * ξ * I).re
  have : (w - 2 * π * ξ * I).re = w.re := by simp
  rw [this]; exact hw

lemma mem_Hp_add {w : ℂ} (hw : w ∈ Hp) (ξ : ℝ) : w + 2 * π * ξ * I ∈ Hp := by
  show 0 < (w + 2 * π * ξ * I).re
  have : (w + 2 * π * ξ * I).re = w.re := by simp
  rw [this]; exact hw

lemma continuousOn_sub_comp {g : ℂ → ℂ} (hg : ContinuousOn g Hp) :
    ContinuousOn (fun p : ℂ × ℝ => g (p.1 - 2 * π * (p.2 : ℂ) * I)) (Hp ×ˢ univ) :=
  hg.comp (by fun_prop : Continuous fun p : ℂ × ℝ => p.1 - 2 * π * (p.2 : ℂ) * I).continuousOn
    (fun p hp => mem_Hp_sub hp.1 p.2)

lemma continuousOn_add_comp {g : ℂ → ℂ} (hg : ContinuousOn g Hp) :
    ContinuousOn (fun p : ℂ × ℝ => g (p.1 + 2 * π * (p.2 : ℂ) * I)) (Hp ×ˢ univ) :=
  hg.comp (by fun_prop : Continuous fun p : ℂ × ℝ => p.1 + 2 * π * (p.2 : ℂ) * I).continuousOn
    (fun p hp => mem_Hp_add hp.1 p.2)

lemma continuousOn_Qd : ContinuousOn (fun p : ℂ × ℝ => Qd p.1 p.2) (Hp ×ˢ univ) :=
  (continuousOn_sub_comp differentiableOn_Gt.continuousOn).mul
    (continuousOn_add_comp differentiableOn_Gt.continuousOn)

lemma continuousOn_Qd' : ContinuousOn (fun p : ℂ × ℝ => Qd' p.1 p.2) (Hp ×ˢ univ) :=
  ((continuousOn_sub_comp continuousOn_deriv_Gt).mul
    (continuousOn_add_comp differentiableOn_Gt.continuousOn)).add
    ((continuousOn_sub_comp differentiableOn_Gt.continuousOn).mul
    (continuousOn_add_comp continuousOn_deriv_Gt))

lemma hasDerivAt_Qd {w : ℂ} (hw : w ∈ Hp) (ξ : ℝ) :
    HasDerivAt (fun w => Qd w ξ) (Qd' w ξ) w := by
  have h1 := (hasDerivAt_Gt (mem_Hp_sub hw ξ)).comp w ((hasDerivAt_id w).sub_const
    (2 * π * (ξ : ℂ) * I))
  have h2 := (hasDerivAt_Gt (mem_Hp_add hw ξ)).comp w ((hasDerivAt_id w).add_const
    (2 * π * (ξ : ℂ) * I))
  have h := h1.mul h2
  unfold Qd Qd'
  convert h using 1
  simp

lemma differentiableOn_PN (N : ℕ) : DifferentiableOn ℂ (PN N) Hp :=
  differentiableOn_intervalIntegral isOpen_Hp continuousOn_Qd continuousOn_Qd'
    (fun w hw ξ => hasDerivAt_Qd hw ξ) _ _

/-! ### Bounds for `Q` -/

lemma Gt_sub_eq (w : ℂ) (ξ : ℝ) :
    w - 2 * π * ξ * I = ((w.re : ℝ) : ℂ) + ((w.im - 2 * π * ξ : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

lemma Gt_add_eq (w : ℂ) (ξ : ℝ) :
    w + 2 * π * ξ * I = ((w.re : ℝ) : ℂ) + ((w.im + 2 * π * ξ : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

lemma norm_Gt_sq (σ u : ℝ) : ‖Gt ((σ : ℂ) + (u : ℂ) * I)‖ ^ 2 = Psi σ u := rfl

/-- `|Q(w,ξ)| ≤ (Ψ_σ(η−2πξ) + Ψ_σ(η+2πξ))/2`. -/
lemma norm_Qd_le (w : ℂ) (ξ : ℝ) :
    ‖Qd w ξ‖ ≤ (Psi w.re (w.im - 2 * π * ξ) + Psi w.re (w.im + 2 * π * ξ)) / 2 := by
  unfold Qd
  rw [norm_mul, Gt_sub_eq, Gt_add_eq, ← norm_Gt_sq, ← norm_Gt_sq]
  nlinarith [sq_nonneg (‖Gt (((w.re : ℝ) : ℂ) + ((w.im - 2 * π * ξ : ℝ) : ℂ) * I)‖ -
    ‖Gt (((w.re : ℝ) : ℂ) + ((w.im + 2 * π * ξ : ℝ) : ℂ) * I)‖)]

lemma integrable_Psi_sub {σ : ℝ} (hi : Integrable (Psi σ)) (η : ℝ) :
    Integrable fun ξ : ℝ => Psi σ (η - 2 * π * ξ) :=
  (hi.comp_sub_left η).comp_mul_left' (by positivity : (2 * π : ℝ) ≠ 0)

lemma integrable_Psi_add {σ : ℝ} (hi : Integrable (Psi σ)) (η : ℝ) :
    Integrable fun ξ : ℝ => Psi σ (η + 2 * π * ξ) :=
  (hi.comp_add_left η).comp_mul_left' (by positivity : (2 * π : ℝ) ≠ 0)

lemma integrable_Qd {w : ℂ} (hw : w ∈ Hp) (hi : Integrable (Psi w.re)) :
    Integrable (Qd w) := by
  have hm : AEStronglyMeasurable (Qd w) volume := by
    exact (continuousOn_Qd.comp_continuous (continuous_const.prodMk continuous_id)
      (fun ξ => ⟨hw, mem_univ _⟩)).aestronglyMeasurable
  refine (((integrable_Psi_sub hi w.im).add (integrable_Psi_add hi w.im)).div_const 2).mono' hm
    (Eventually.of_forall fun ξ => norm_Qd_le w ξ)

/-! ### Tails -/

lemma setOf_abs_gt (N : ℝ) : {ξ : ℝ | N < |ξ|} = (Icc (-N) N)ᶜ := by
  ext ξ
  simp only [mem_setOf_eq, mem_compl_iff, mem_Icc, not_and_or, not_le]
  constructor
  · intro h
    rcases lt_abs.1 h with h1 | h1
    · right; exact h1
    · left; linarith
  · rintro (h1 | h1)
    · exact lt_abs.2 (Or.inr (by linarith))
    · exact lt_abs.2 (Or.inl h1)

lemma tail_sub {σ η N : ℝ} (hi : Integrable (Psi σ)) (hN0 : 0 ≤ N) (hNη : |η| ≤ N) :
    ∫ ξ, {ξ : ℝ | N < |ξ|}.indicator (fun ξ => Psi σ (η - 2 * π * ξ)) ξ ≤
      (2 * π)⁻¹ * ∫ u, {u : ℝ | N < |u|}.indicator (Psi σ) u := by
  set H : ℝ → ℝ := {u : ℝ | 2 * π * N < |η - u|}.indicator (Psi σ) with hH
  have hpt : ∀ ξ, {ξ : ℝ | N < |ξ|}.indicator (fun ξ => Psi σ (η - 2 * π * ξ)) ξ =
      (fun z => H (η - z)) (2 * π * ξ) := by
    intro ξ
    simp only [hH, Set.indicator, mem_setOf_eq]
    have e : |η - (η - 2 * π * ξ)| = 2 * π * |ξ| := by
      rw [sub_sub_cancel, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
    simp only [e]
    by_cases h : N < |ξ|
    · have : 2 * π * N < 2 * π * |ξ| := by gcongr
      simp [h, this]
    · have : ¬ 2 * π * N < 2 * π * |ξ| := by
        intro h'; exact h (lt_of_mul_lt_mul_left h' (by positivity))
      simp [h, this]
  have e1 : ∫ ξ, {ξ : ℝ | N < |ξ|}.indicator (fun ξ => Psi σ (η - 2 * π * ξ)) ξ =
      (2 * π)⁻¹ * ∫ u, H u := by
    simp_rw [hpt]
    rw [Measure.integral_comp_mul_left (fun z => H (η - z)) (2 * π), integral_sub_left_eq_self,
      abs_of_pos (by positivity : (0:ℝ) < (2 * π)⁻¹), smul_eq_mul]
  rw [e1]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hHm : MeasurableSet {u : ℝ | 2 * π * N < |η - u|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hGm : MeasurableSet {u : ℝ | N < |u|} := measurableSet_lt measurable_const (by fun_prop)
  refine integral_mono (hi.indicator hHm) (hi.indicator hGm) fun u => ?_
  simp only [hH, Set.indicator, mem_setOf_eq]
  by_cases h : 2 * π * N < |η - u|
  · have : N < |u| := by
      have h1 : |η - u| ≤ |η| + |u| := abs_sub _ _
      have h2 : N ≤ 2 * π * N - N := by nlinarith [Real.pi_gt_three]
      linarith
    simp [h, this]
  · simp only [h, if_false]
    split_ifs
    · exact Psi_nonneg _ _
    · exact le_rfl

lemma tail_add {σ η N : ℝ} (hi : Integrable (Psi σ)) (hN0 : 0 ≤ N) (hNη : |η| ≤ N) :
    ∫ ξ, {ξ : ℝ | N < |ξ|}.indicator (fun ξ => Psi σ (η + 2 * π * ξ)) ξ ≤
      (2 * π)⁻¹ * ∫ u, {u : ℝ | N < |u|}.indicator (Psi σ) u := by
  set H : ℝ → ℝ := {u : ℝ | 2 * π * N < |u - η|}.indicator (Psi σ) with hH
  have hpt : ∀ ξ, {ξ : ℝ | N < |ξ|}.indicator (fun ξ => Psi σ (η + 2 * π * ξ)) ξ =
      (fun z => H (η + z)) (2 * π * ξ) := by
    intro ξ
    simp only [hH, Set.indicator, mem_setOf_eq]
    have e : |η + 2 * π * ξ - η| = 2 * π * |ξ| := by
      rw [add_sub_cancel_left, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
    simp only [e]
    by_cases h : N < |ξ|
    · have : 2 * π * N < 2 * π * |ξ| := by gcongr
      simp [h, this]
    · have : ¬ 2 * π * N < 2 * π * |ξ| := by
        intro h'; exact h (lt_of_mul_lt_mul_left h' (by positivity))
      simp [h, this]
  have e1 : ∫ ξ, {ξ : ℝ | N < |ξ|}.indicator (fun ξ => Psi σ (η + 2 * π * ξ)) ξ =
      (2 * π)⁻¹ * ∫ u, H u := by
    simp_rw [hpt]
    rw [Measure.integral_comp_mul_left (fun z => H (η + z)) (2 * π), integral_add_left_eq_self,
      abs_of_pos (by positivity : (0:ℝ) < (2 * π)⁻¹), smul_eq_mul]
  rw [e1]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hHm : MeasurableSet {u : ℝ | 2 * π * N < |u - η|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hGm : MeasurableSet {u : ℝ | N < |u|} := measurableSet_lt measurable_const (by fun_prop)
  refine integral_mono (hi.indicator hHm) (hi.indicator hGm) fun u => ?_
  simp only [hH, Set.indicator, mem_setOf_eq]
  by_cases h : 2 * π * N < |u - η|
  · have : N < |u| := by
      have h1 : |u - η| ≤ |u| + |η| := abs_sub _ _
      have h2 : N ≤ 2 * π * N - N := by nlinarith [Real.pi_gt_three]
      linarith
    simp [h, this]
  · simp only [h, if_false]
    split_ifs
    · exact Psi_nonneg _ _
    · exact le_rfl

/-- `|P(w) − P_N(w)| ≤ (2π)⁻¹ ∫_{|u|>N} Ψ_σ`. -/
lemma norm_P_sub_PN {w : ℂ} (hw : w ∈ Hp) (hi : Integrable (Psi w.re)) (N : ℕ)
    (hN : |w.im| ≤ N) :
    ‖P w - PN N w‖ ≤ (2 * π)⁻¹ * ∫ u, {u : ℝ | (N : ℝ) < |u|}.indicator (Psi w.re) u := by
  have hQ := integrable_Qd hw hi
  set S : Set ℝ := {ξ : ℝ | (N : ℝ) < |ξ|} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_const (by fun_prop)
  have hSc : S = (Icc (-(N : ℝ)) N)ᶜ := setOf_abs_gt _
  have hPN : PN N w = ∫ ξ in Icc (-(N : ℝ)) N, Qd w ξ := by
    rw [PN, intervalIntegral.integral_of_le (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]),
      integral_Icc_eq_integral_Ioc]
  have hdiff : P w - PN N w = ∫ ξ in S, Qd w ξ := by
    rw [hPN, P, ← integral_add_compl measurableSet_Icc hQ, hSc]; ring
  rw [hdiff]
  set φ1 : ℝ → ℝ := fun ξ => Psi w.re (w.im - 2 * π * ξ) with hφ1
  set φ2 : ℝ → ℝ := fun ξ => Psi w.re (w.im + 2 * π * ξ) with hφ2
  have h1i := integrable_Psi_sub hi w.im
  have h2i := integrable_Psi_add hi w.im
  have hb : ∫ ξ in S, ‖Qd w ξ‖ ≤ ∫ ξ in S, (φ1 ξ + φ2 ξ) / 2 :=
    setIntegral_mono hQ.norm.integrableOn ((h1i.add h2i).div_const 2).integrableOn
      fun ξ => norm_Qd_le w ξ
  have hsplit : ∫ ξ in S, (φ1 ξ + φ2 ξ) / 2 = ((∫ ξ in S, φ1 ξ) + ∫ ξ in S, φ2 ξ) / 2 := by
    rw [integral_div, integral_add h1i.integrableOn h2i.integrableOn]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have t1 := tail_sub (σ := w.re) (η := w.im) hi hN0 hN
  have t2 := tail_add (σ := w.re) (η := w.im) hi hN0 hN
  rw [integral_indicator hSm] at t1 t2
  calc ‖∫ ξ in S, Qd w ξ‖ ≤ ∫ ξ in S, ‖Qd w ξ‖ := norm_integral_le_integral_norm _
    _ ≤ _ := hb
    _ = _ := hsplit
    _ ≤ ((2 * π)⁻¹ * (∫ u, {u : ℝ | (N : ℝ) < |u|}.indicator (Psi w.re) u) +
          (2 * π)⁻¹ * ∫ u, {u : ℝ | (N : ℝ) < |u|}.indicator (Psi w.re) u) / 2 := by
        gcongr
    _ = _ := by ring

/-- Uniform tails on `23/4 + d ≤ σ ≤ 6 − d`. -/
theorem uniform_tail : ∃ K : ℝ, 0 ≤ K ∧ ∀ d : ℝ, 0 < d → ∀ σ : ℝ, 23 / 4 + d ≤ σ → σ ≤ 6 - d →
    ∀ N : ℝ, 1 ≤ N → Integrable (Psi σ) ∧
      ∫ u, {u : ℝ | N < |u|}.indicator (Psi σ) u ≤ 2 * (K / d * N ^ (-(4 * d)) / (1 - 2 ^ (-(4 * d)))) := by
  obtain ⟨K, hK0, hK⟩ := tail_bound
  refine ⟨K, hK0, fun d hd σ h1 h2 N hN => ?_⟩
  set y : ℝ := 6 - σ with hy
  have hσ : σ = 6 - y := by rw [hy]; ring
  have hy0 : d ≤ y := by rw [hy]; linarith
  have hy1 : y ≤ 1 / 4 - d := by rw [hy]; linarith
  have hy0' : 0 < y := by linarith
  have hy1' : y < 1 / 4 := by linarith
  obtain ⟨hint, hbd⟩ := hK y hy0' hy1' N hN
  rw [← hσ] at hint hbd
  have hsp := even_split (continuous_Psi (by linarith)) (Psi_neg σ) (by linarith) hint
  refine ⟨hsp.1, ?_⟩
  rw [hsp.2.1]
  gcongr
  refine hbd.trans ?_
  have hp : 4 * d ≤ 1 - 4 * y := by linarith
  have hr1 : (2 : ℝ) ^ (-(1 - 4 * y)) ≤ 2 ^ (-(4 * d)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hr2 : (2 : ℝ) ^ (-(4 * d)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hN1 : N ^ (-(1 - 4 * y)) ≤ N ^ (-(4 * d)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hNp : 0 < N ^ (-(1 - 4 * y)) := Real.rpow_pos_of_pos (by linarith) _
  have hKy : K / y ≤ K / d := div_le_div_of_nonneg_left hK0 (by linarith) hy0
  have hden : (0 : ℝ) < 1 - (2 : ℝ) ^ (-(4 * d)) := by linarith
  calc K / y * N ^ (-(1 - 4 * y)) / (1 - 2 ^ (-(1 - 4 * y)))
      ≤ K / d * N ^ (-(4 * d)) / (1 - 2 ^ (-(1 - 4 * y))) := by
        have : (0 : ℝ) ≤ 1 - (2 : ℝ) ^ (-(1 - 4 * y)) := by linarith
        gcongr
    _ ≤ K / d * N ^ (-(4 * d)) / (1 - 2 ^ (-(4 * d))) := by
        apply div_le_div_of_nonneg_left (by positivity) hden (by linarith)

/-- The strip `23/4 < Re w < 6`. -/
def Wst : Set ℂ := {w | 23 / 4 < w.re ∧ w.re < 6}

lemma isOpen_Wst : IsOpen Wst :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)

lemma Wst_sub_Hp : Wst ⊆ Hp := fun w hw => by
  show 0 < w.re; linarith [hw.1]

/-- **`P` is holomorphic on `23/4 < Re w < 6`.** -/
theorem differentiableOn_P : DifferentiableOn ℂ P Wst := by
  obtain ⟨K, hK0, hK⟩ := uniform_tail
  have htlu : TendstoLocallyUniformlyOn (fun N : ℕ => PN N) P atTop Wst := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε x hx
    obtain ⟨hx1, hx2⟩ := hx
    set d : ℝ := min (x.re - 23 / 4) (6 - x.re) / 2 with hd
    have hd0 : 0 < d := by rw [hd]; exact div_pos (lt_min (by linarith) (by linarith)) two_pos
    have hdle1 : 2 * d ≤ x.re - 23 / 4 := by rw [hd]; linarith [min_le_left (x.re - 23 / 4) (6 - x.re)]
    have hdle2 : 2 * d ≤ 6 - x.re := by rw [hd]; linarith [min_le_right (x.re - 23 / 4) (6 - x.re)]
    refine ⟨Metric.ball x d, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hd0), ?_⟩
    set c : ℝ := (2 * π)⁻¹ * (2 * (K / d / (1 - 2 ^ (-(4 * d))))) with hc
    have hlim : Tendsto (fun N : ℕ => c * (N : ℝ) ^ (-(4 * d))) atTop (𝓝 (c * 0)) :=
      ((tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop).const_mul c
    rw [mul_zero] at hlim
    filter_upwards [hlim.eventually (gt_mem_nhds hε),
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (|x.im| + d + 1))]
      with N hN1 hN2
    intro y hy
    rw [Metric.mem_ball, Complex.dist_eq] at hy
    have hre : |y.re - x.re| < d := by
      have := Complex.abs_re_le_norm (y - x); rw [Complex.sub_re] at this; linarith
    have him : |y.im - x.im| < d := by
      have := Complex.abs_im_le_norm (y - x); rw [Complex.sub_im] at this; linarith
    have hyre1 : 23 / 4 + d ≤ y.re := by linarith [(abs_lt.1 hre).1]
    have hyre2 : y.re ≤ 6 - d := by linarith [(abs_lt.1 hre).2]
    have hNim : |y.im| ≤ (N : ℝ) := by
      have := abs_sub_abs_le_abs_sub y.im x.im
      have h' : |y.im| - |x.im| ≤ |y.im - x.im| := this
      linarith
    have hN1' : (1 : ℝ) ≤ N := by linarith [abs_nonneg x.im]
    obtain ⟨hint, hbd⟩ := hK d hd0 y.re hyre1 hyre2 N hN1'
    have hyH : y ∈ Hp := by show 0 < y.re; linarith
    rw [dist_eq_norm]
    calc ‖P y - PN N y‖ ≤ (2 * π)⁻¹ * ∫ u, {u : ℝ | (N : ℝ) < |u|}.indicator (Psi y.re) u :=
          norm_P_sub_PN hyH hint N hNim
      _ ≤ (2 * π)⁻¹ * (2 * (K / d * (N : ℝ) ^ (-(4 * d)) / (1 - 2 ^ (-(4 * d))))) := by gcongr
      _ = c * (N : ℝ) ^ (-(4 * d)) := by rw [hc]; ring
      _ < ε := hN1
  exact htlu.differentiableOn (Eventually.of_forall fun N =>
    (differentiableOn_PN N).mono Wst_sub_Hp) isOpen_Wst

end RamanujanTau.Voronoi
