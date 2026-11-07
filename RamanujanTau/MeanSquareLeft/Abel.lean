/-
# An Abelian (partial-summation) lemma for weighted mean values

If `g ≥ 0` is continuous with `(1/T) ∫₀ᵀ g → A`, and `F = g·h` on `[1,∞)` with
`h(t)/t^α → c` (`α > 0`), then

    (∫₀ᵀ F) / T^{α+1}  →  c·A/(α+1).

* `tendsto_weighted`: if `w ≥ 0` and `(∫₁ᵀ w)/T^b → W`, and `ψ → c`, then
  `(∫₁ᵀ wψ)/T^b → cW` (split at a point `U` beyond which `|ψ − c| ≤ ε`).
* `abel_rpow`: integration by parts `∫₁ᵀ t^α g = T^α G(T) − G(1) − α ∫₁ᵀ t^{α−1} G`,
  `G(t) = ∫₀ᵗ g`; with `t^{α−1}G(t) = t^α · (G(t)/t)` and `tendsto_weighted` this gives
  `(∫₁ᵀ g t^α)/T^{α+1} → A − αA/(α+1) = A/(α+1)`.
* `abel_mean`: the general statement above (a second `tendsto_weighted`).
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.MeanSquareLeft

open Real Filter Topology MeasureTheory Set

/-- **Weighted averages.** -/
lemma tendsto_weighted {w ψ : ℝ → ℝ} {b W c : ℝ} (hb : 0 < b)
    (hw0 : ∀ u, 1 ≤ u → 0 ≤ w u)
    (hwi : ∀ T, 1 ≤ T → IntervalIntegrable w volume 1 T)
    (hwψ : ∀ T, 1 ≤ T → IntervalIntegrable (fun u => w u * ψ u) volume 1 T)
    (hW : Tendsto (fun T => (∫ u in (1 : ℝ)..T, w u) / T ^ b) atTop (𝓝 W))
    (hψ : Tendsto ψ atTop (𝓝 c)) :
    Tendsto (fun T => (∫ u in (1 : ℝ)..T, w u * ψ u) / T ^ b) atTop (𝓝 (c * W)) := by
  have hTb : Tendsto (fun T : ℝ => T ^ b) atTop atTop := tendsto_rpow_atTop hb
  have hf : ∀ T, 1 ≤ T → IntervalIntegrable (fun u => w u * ψ u - c * w u) volume 1 T :=
    fun T hT => (hwψ T hT).sub ((hwi T hT).const_mul c)
  have hd : Tendsto (fun T => (∫ u in (1 : ℝ)..T, (w u * ψ u - c * w u)) / T ^ b) atTop
      (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    set ε := δ / (2 * (|W| + 1)) with hε
    have hW1 : 0 < |W| + 1 := by positivity
    have hε0 : 0 < ε := by positivity
    obtain ⟨U0, hU0⟩ := eventually_atTop.1 (hψ.eventually (Metric.closedBall_mem_nhds c hε0))
    set U := max U0 1 with hU
    have hU1 : 1 ≤ U := le_max_right _ _
    set K := |∫ u in (1 : ℝ)..U, (w u * ψ u - c * w u)| with hK
    have e1 : ∀ᶠ T in atTop, K / T ^ b < δ / 4 :=
      ((tendsto_const_nhds (x := K)).div_atTop hTb).eventually (gt_mem_nhds (by positivity))
    have e2 : ∀ᶠ T in atTop, (∫ u in (1 : ℝ)..T, w u) / T ^ b < |W| + 1 :=
      hW.eventually (gt_mem_nhds (by linarith [le_abs_self W]))
    filter_upwards [e1, e2, eventually_ge_atTop U] with T h1 h2 hTU
    have hT1 : 1 ≤ T := hU1.trans hTU
    have hT0 : 0 < T := by linarith
    have hTb0 : 0 < T ^ b := Real.rpow_pos_of_pos hT0 b
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hf U hU1)
      ((hf U hU1).symm.trans (hf T hT1))
    have hwU : 0 ≤ ∫ u in (1 : ℝ)..U, w u :=
      intervalIntegral.integral_nonneg hU1 fun u hu => hw0 u hu.1
    have hsplitw := intervalIntegral.integral_add_adjacent_intervals (hwi U hU1)
      ((hwi U hU1).symm.trans (hwi T hT1))
    have htail : ‖∫ u in U..T, (w u * ψ u - c * w u)‖ ≤ ∫ u in U..T, ε * w u := by
      refine intervalIntegral.norm_integral_le_of_norm_le hTU
        (Eventually.of_forall fun u hu => ?_) (((hwi U hU1).symm.trans (hwi T hT1)).const_mul ε)
      have huU : U ≤ u := hu.1.le
      have hu0 : U0 ≤ u := (le_max_left _ _).trans huU
      have hwu : 0 ≤ w u := hw0 u (hU1.trans huU)
      have hd := hU0 u hu0
      rw [Real.dist_eq] at hd
      rw [show w u * ψ u - c * w u = w u * (ψ u - c) by ring, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hwu, mul_comm ε]
      exact mul_le_mul_of_nonneg_left hd hwu
    rw [intervalIntegral.integral_const_mul] at htail
    have hbound : |∫ u in (1 : ℝ)..T, (w u * ψ u - c * w u)| ≤
        K + ε * ∫ u in (1 : ℝ)..T, w u := by
      rw [← hsplit, ← hsplitw]
      refine (abs_add_le _ _).trans ?_
      rw [← Real.norm_eq_abs (∫ u in U..T, _)]
      nlinarith
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hTb0, div_lt_iff₀ hTb0]
    rw [div_lt_iff₀ hTb0] at h1 h2
    have hεW : ε * (|W| + 1) = δ / 2 := by rw [hε]; field_simp
    have h3 : ε * ∫ u in (1 : ℝ)..T, w u ≤ δ / 2 * T ^ b := by
      rw [← hεW, mul_assoc]; exact mul_le_mul_of_nonneg_left h2.le hε0.le
    nlinarith
  have hc := hd.add (hW.const_mul c)
  rw [zero_add] at hc
  refine hc.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  rw [intervalIntegral.integral_sub (hwψ T hT) ((hwi T hT).const_mul c),
    intervalIntegral.integral_const_mul]
  ring

lemma mem_uIcc_one {T x : ℝ} (hT : 1 ≤ T) (hx : x ∈ uIcc 1 T) : 1 ≤ x := by
  rw [uIcc_of_le hT] at hx; exact hx.1

lemma continuousOn_rpow_uIcc (α : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    ContinuousOn (fun x : ℝ => x ^ α) (uIcc 1 T) := fun x hx =>
  (Real.continuousAt_rpow_const x α
    (Or.inl (by have := mem_uIcc_one hT hx; positivity))).continuousWithinAt

/-- `(∫₁ᵀ t^α)/T^{α+1} → 1/(α+1)`. -/
lemma tendsto_integral_rpow {α : ℝ} (hα : 0 < α) :
    Tendsto (fun T => (∫ u in (1 : ℝ)..T, u ^ α) / T ^ (α + 1)) atTop (𝓝 (1 / (α + 1))) := by
  have hTb : Tendsto (fun T : ℝ => T ^ (α + 1)) atTop atTop := tendsto_rpow_atTop (by linarith)
  have h := (tendsto_const_nhds (x := 1 / (α + 1))).sub
    ((tendsto_const_nhds (x := 1 / (α + 1))).mul hTb.inv_tendsto_atTop)
  rw [mul_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  rw [integral_rpow (Or.inl (by linarith)), Real.one_rpow]
  have : 0 < T ^ (α + 1) := Real.rpow_pos_of_pos hT _
  simp only [Pi.inv_apply]
  field_simp

/-- **Abelian lemma for the weight `t^α`.** -/
theorem abel_rpow {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t) {A α : ℝ} (hα : 0 < α)
    (hA : Tendsto (fun T => (∫ t in (0 : ℝ)..T, g t) / T) atTop (𝓝 A)) :
    Tendsto (fun T => (∫ t in (1 : ℝ)..T, g t * t ^ α) / T ^ (α + 1)) atTop
      (𝓝 (A / (α + 1))) := by
  set G : ℝ → ℝ := fun T => ∫ t in (0 : ℝ)..T, g t with hG
  have hGc : Continuous G := by
    rw [hG]; exact intervalIntegral.continuous_primitive (fun a b => hg.intervalIntegrable a b) 0
  have hG0 : ∀ x, 0 ≤ x → 0 ≤ G x := fun x hx =>
    intervalIntegral.integral_nonneg hx fun t _ => hg0 t
  have hTb : Tendsto (fun T : ℝ => T ^ (α + 1)) atTop atTop := tendsto_rpow_atTop (by linarith)
  -- the integrated term
  have hK : Tendsto (fun T => (∫ u in (1 : ℝ)..T, u ^ α * (G u / u)) / T ^ (α + 1)) atTop
      (𝓝 (A * (1 / (α + 1)))) := by
    refine tendsto_weighted (by linarith) (fun u hu => by positivity)
      (fun T hT => (continuousOn_rpow_uIcc α hT).intervalIntegrable)
      (fun T hT => ?_) (tendsto_integral_rpow hα) hA
    refine ContinuousOn.intervalIntegrable ?_
    refine (continuousOn_rpow_uIcc α hT).mul ?_
    exact hGc.continuousOn.div continuous_id.continuousOn fun x hx => by
      have := mem_uIcc_one hT hx; simp; linarith
  have h := (hA.sub ((tendsto_const_nhds (x := G 1)).div_atTop hTb)).sub (hK.const_mul α)
  have e : A - 0 - α * (A * (1 / (α + 1))) = A / (α + 1) := by
    field_simp; ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hT0 : 0 < T := by linarith
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 1) (b := T)
    (u := fun x : ℝ => x ^ α) (u' := fun x => α * x ^ (α - 1)) (v := G) (v' := g)
    (fun x hx => Real.hasDerivAt_rpow_const (Or.inl (by have := mem_uIcc_one hT hx; positivity)))
    (fun x _ => (hg.integral_hasStrictDerivAt 0 x).hasDerivAt)
    (ContinuousOn.intervalIntegrable (continuousOn_const.mul (fun x hx =>
      (Real.continuousAt_rpow_const x (α - 1)
        (Or.inl (by have := mem_uIcc_one hT hx; positivity))).continuousWithinAt)))
    (hg.intervalIntegrable 1 T)
  have e1 : ∫ x in (1 : ℝ)..T, g x * x ^ α = ∫ x in (1 : ℝ)..T, x ^ α * g x :=
    intervalIntegral.integral_congr fun x _ => mul_comm _ _
  have e2 : ∫ x in (1 : ℝ)..T, α * x ^ (α - 1) * G x =
      α * ∫ x in (1 : ℝ)..T, x ^ α * (G x / x) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hx0 : x ≠ 0 := by have := mem_uIcc_one hT hx; positivity
    rw [Real.rpow_sub_one hx0]; field_simp
  have hTa : T ^ (α + 1) = T ^ α * T := Real.rpow_add_one hT0.ne' α
  have hTa0 : 0 < T ^ α := Real.rpow_pos_of_pos hT0 α
  simp only at hibp
  rw [e1, hibp, e2, Real.one_rpow, hTa]
  field_simp
  ring

/-- **Abelian lemma, general weight.**  If `g ≥ 0` is continuous with `(1/T)∫₀ᵀ g → A`,
`F` is continuous with `F = g·h` on `[1,∞)`, and `h(t)/t^α → c` (`α > 0`), then
`(∫₀ᵀ F)/T^{α+1} → c·A/(α+1)`. -/
theorem abel_mean {g F h : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t) (hF : Continuous F)
    {A α c : ℝ} (hα : 0 < α)
    (hA : Tendsto (fun T => (∫ t in (0 : ℝ)..T, g t) / T) atTop (𝓝 A))
    (hFgh : ∀ t, 1 ≤ t → F t = g t * h t)
    (hh : Tendsto (fun t => h t / t ^ α) atTop (𝓝 c)) :
    Tendsto (fun T => (∫ t in (0 : ℝ)..T, F t) / T ^ (α + 1)) atTop
      (𝓝 (c * (A / (α + 1)))) := by
  have hTb : Tendsto (fun T : ℝ => T ^ (α + 1)) atTop atTop := tendsto_rpow_atTop (by linarith)
  have hFw : ∀ t, 1 ≤ t → F t = g t * t ^ α * (h t / t ^ α) := by
    intro t ht
    have : 0 < t ^ α := Real.rpow_pos_of_pos (by linarith) α
    rw [hFgh t ht]; field_simp
  have hW := tendsto_weighted (w := fun t => g t * t ^ α) (ψ := fun t => h t / t ^ α)
    (by linarith : (0:ℝ) < α + 1)
    (fun u hu => by have := hg0 u; positivity)
    (fun T hT => (hg.continuousOn.mul (continuousOn_rpow_uIcc α hT)).intervalIntegrable)
    (fun T hT => by
      refine ContinuousOn.intervalIntegrable ?_
      refine hF.continuousOn.congr fun x hx => ?_
      exact (hFw x (mem_uIcc_one hT hx)).symm)
    (abel_rpow hg hg0 hα hA) hh
  have h2 := ((tendsto_const_nhds (x := ∫ t in (0 : ℝ)..1, F t)).div_atTop hTb).add hW
  rw [zero_add] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1) (hF.intervalIntegrable 0 1)
    (hF.intervalIntegrable 1 T), add_div]
  congr 2
  refine intervalIntegral.integral_congr fun x hx => ?_
  exact (hFw x (mem_uIcc_one hT hx)).symm

end RamanujanTau.MeanSquareLeft
