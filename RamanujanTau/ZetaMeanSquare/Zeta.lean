/-
# Headlines: the Hardy–Littlewood–Landau mean square of `ζ` on `1/2 < σ ≤ 1`

* `zeta_mean_value_uniform`: uniformly for `σ₀ ≤ σ ≤ 1` (`σ₀ > 1/2`), `T ≥ 1`,
  `|∫_1^T |ζ(σ+it)|² dt − ζ(2σ)T| ≤ C (T^{3/2−σ} + T^{2−2σ}(1+log T)²)`;
* `zeta_mean_value_dyadic`: the same on `[T, 2T]`;
* `zeta_mean_square_tendsto`: `(1/T)∫_1^T |ζ(σ+it)|² dt → ζ(2σ)` for `1/2 < σ ≤ 1`;
* `zeta_mean_square_tendsto_zero`: `(1/T)∫_0^T |ζ(σ+it)|² dt → ζ(2σ)` for `1/2 < σ < 1`
  (at `σ = 1` the integral over `[0,1]` diverges because of the pole).
-/
import RamanujanTau.ZetaMeanSquare.MeanValue

set_option autoImplicit false

namespace RamanujanTau.ZetaMeanSquare

open Complex MeasureTheory Set Filter Topology

lemma continuousAt_zeta_line_plus (σ : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt (fun t : ℝ => riemannZeta ((σ : ℂ) + t * I)) t := by
  have hne : (σ : ℂ) + t * I ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; exact ht this
  exact (differentiableAt_riemannZeta hne).continuousAt.comp
    (f := fun t : ℝ => (σ : ℂ) + t * I) (x := t) (by fun_prop)

lemma line_ne_one (σ : ℝ) {t : ℝ} (ht : t ≠ 0) : (σ : ℂ) - t * I ≠ 1 := by
  intro h; have := congrArg Complex.im h; simp at this; exact ht this

lemma integral_plus_eq_minus (σ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 =
      ∫ t in a..b, ‖riemannZeta ((σ : ℂ) - t * I)‖ ^ 2 := by
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hab] at ht
  rw [norm_riemannZeta_conj σ t (line_ne_one σ (by linarith [ht.1]))]

lemma intervalIntegrable_plus (σ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2) volume a b := by
  refine ContinuousOn.intervalIntegrable fun t ht => ?_
  rw [uIcc_of_le hab] at ht
  exact ((continuousAt_zeta_line_plus σ (by linarith [ht.1] : t ≠ 0)).norm.pow 2).continuousWithinAt

/-- The error profile `E_σ(T) = T^{3/2−σ} + T^{2−2σ}(1+log T)²`. -/
noncomputable def Eσ (σ T : ℝ) : ℝ := T ^ ((3 : ℝ) / 2 - σ) + T ^ (2 - 2 * σ) * (1 + Real.log T) ^ 2

lemma Eσ_nonneg (σ : ℝ) {T : ℝ} (hT : 0 ≤ T) : 0 ≤ Eσ σ T := by unfold Eσ; positivity

/-- **Mean-value theorem for `ζ` off the critical line**, uniform on `[σ₀, 1]`, `σ₀ > 1/2`. -/
theorem zeta_mean_value_uniform {σ₀ : ℝ} (hσ₀ : 1 / 2 < σ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 1 → ∀ T : ℝ, 1 ≤ T →
      |(∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2) -
          (riemannZeta (2 * (σ : ℂ))).re * T| ≤
        C * (T ^ ((3 : ℝ) / 2 - σ) + T ^ (2 - 2 * σ) * (1 + Real.log T) ^ 2) := by
  obtain ⟨C, hC, h⟩ := mean_value_minus hσ₀
  refine ⟨C, hC, fun σ h1 h2 T hT => ?_⟩
  rw [integral_plus_eq_minus σ one_pos hT]
  exact h σ h1 h2 T hT

lemma Eσ_two_mul {σ : ℝ} (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 1) {T : ℝ} (hT : 1 ≤ T) :
    Eσ σ (2 * T) ≤ 8 * Eσ σ T := by
  have hT0 : 0 < T := by linarith
  unfold Eσ
  have a1 : (2 * T) ^ ((3 : ℝ) / 2 - σ) ≤ 2 * T ^ ((3 : ℝ) / 2 - σ) := by
    rw [Real.mul_rpow (by norm_num) hT0.le]
    have : (2 : ℝ) ^ ((3 : ℝ) / 2 - σ) ≤ 2 ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_one] at this
    have : 0 ≤ T ^ ((3 : ℝ) / 2 - σ) := by positivity
    nlinarith
  have a2 : (2 * T) ^ (2 - 2 * σ) ≤ 2 * T ^ (2 - 2 * σ) := by
    rw [Real.mul_rpow (by norm_num) hT0.le]
    have : (2 : ℝ) ^ (2 - 2 * σ) ≤ 2 ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_one] at this
    have : 0 ≤ T ^ (2 - 2 * σ) := by positivity
    nlinarith
  have hL0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have a3 : (1 + Real.log (2 * T)) ^ 2 ≤ 4 * (1 + Real.log T) ^ 2 := by
    rw [Real.log_mul (by norm_num) hT0.ne']
    have := Real.log_two_lt_d9
    have h0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  have hp1 : 0 ≤ T ^ ((3 : ℝ) / 2 - σ) := by positivity
  have hp2 : 0 ≤ T ^ (2 - 2 * σ) := by positivity
  have hp3 : 0 ≤ (1 + Real.log (2 * T)) ^ 2 := by positivity
  have hp4 : 0 ≤ (2 * T) ^ (2 - 2 * σ) := by positivity
  calc (2 * T) ^ ((3 : ℝ) / 2 - σ) + (2 * T) ^ (2 - 2 * σ) * (1 + Real.log (2 * T)) ^ 2
      ≤ 2 * T ^ ((3 : ℝ) / 2 - σ) + (2 * T ^ (2 - 2 * σ)) * (4 * (1 + Real.log T) ^ 2) := by
        gcongr
    _ ≤ 8 * (T ^ ((3 : ℝ) / 2 - σ) + T ^ (2 - 2 * σ) * (1 + Real.log T) ^ 2) := by nlinarith

/-- **Dyadic form**: `∫_T^{2T} |ζ(σ+it)|² dt = ζ(2σ) T + O(T^{3/2−σ} + T^{2−2σ}(1+log T)²)`,
uniformly on `[σ₀, 1]`. -/
theorem zeta_mean_value_dyadic {σ₀ : ℝ} (hσ₀ : 1 / 2 < σ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, σ₀ ≤ σ → σ ≤ 1 → ∀ T : ℝ, 1 ≤ T →
      |(∫ t in T..2 * T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2) -
          (riemannZeta (2 * (σ : ℂ))).re * T| ≤
        C * (T ^ ((3 : ℝ) / 2 - σ) + T ^ (2 - 2 * σ) * (1 + Real.log T) ^ 2) := by
  obtain ⟨C, hC, h⟩ := zeta_mean_value_uniform hσ₀
  refine ⟨9 * C, by positivity, fun σ h1 h2 T hT => ?_⟩
  have hσ' : 1 / 2 ≤ σ := by linarith
  have hA := h σ h1 h2 (2 * T) (by linarith)
  have hB := h σ h1 h2 T hT
  have e := intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_plus σ one_pos (show (1 : ℝ) ≤ 2 * T by linarith))
    (intervalIntegrable_plus σ one_pos hT)
  rw [← e]
  have hE := Eσ_two_mul hσ' h2 hT
  unfold Eσ at hE
  have hE0 := Eσ_nonneg σ (show (0 : ℝ) ≤ T by linarith)
  unfold Eσ at hE0
  set ζR := (riemannZeta (2 * (σ : ℂ))).re
  have : (∫ t in (1 : ℝ)..2 * T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2) -
      (∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2) - ζR * T =
      ((∫ t in (1 : ℝ)..2 * T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2) - ζR * (2 * T)) -
      ((∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2) - ζR * T) := by ring
  rw [this]
  refine (abs_sub _ _).trans ?_
  have hC8 := mul_le_mul_of_nonneg_left hE hC
  nlinarith

/-- `E_σ(T)/T ≤ c T^{−(σ−1/2)}`. -/
lemma Eσ_div_le {σ : ℝ} (h1 : 1 / 2 < σ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ T : ℝ, 1 ≤ T → Eσ σ T / T ≤ c * T ^ (-(σ - 1 / 2)) := by
  set a : ℝ := σ - 1 / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  set a' : ℝ := a / 2 with ha'
  have ha'0 : 0 < a' := by positivity
  refine ⟨1 + (1 + 1 / a') ^ 2, by positivity, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hlog : 1 + Real.log T ≤ (1 + 1 / a') * T ^ a' := by
    have h := Real.log_le_rpow_div hT0.le ha'0
    have h1 : 1 ≤ T ^ a' := Real.one_le_rpow hT ha'0.le
    have : T ^ a' / a' = 1 / a' * T ^ a' := by ring
    nlinarith
  have hL0 : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT]
  have hsq : (1 + Real.log T) ^ 2 ≤ (1 + 1 / a') ^ 2 * T ^ a := by
    have := pow_le_pow_left₀ hL0 hlog 2
    have e : ((1 + 1 / a') * T ^ a') ^ 2 = (1 + 1 / a') ^ 2 * T ^ a := by
      rw [mul_pow, ← Real.rpow_mul_natCast hT0.le]; congr 2; push_cast; rw [ha']; ring
    linarith
  unfold Eσ
  have e1 : T ^ ((3 : ℝ) / 2 - σ) / T = T ^ (-a) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hT0]; congr 1; rw [ha]; ring
  have e2 : T ^ (2 - 2 * σ) * T ^ a / T = T ^ (-a) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hT0, ← Real.rpow_add hT0]
    congr 1; rw [ha]; ring
  rw [add_div, e1]
  have hp : 0 ≤ T ^ (2 - 2 * σ) := by positivity
  have h3 : T ^ (2 - 2 * σ) * (1 + Real.log T) ^ 2 / T ≤ (1 + 1 / a') ^ 2 * T ^ (-a) := by
    rw [div_le_iff₀ hT0]
    have : T ^ (2 - 2 * σ) * (1 + Real.log T) ^ 2 ≤ T ^ (2 - 2 * σ) * ((1 + 1 / a') ^ 2 * T ^ a) := by
      gcongr
    have e3 : T ^ (2 - 2 * σ) * ((1 + 1 / a') ^ 2 * T ^ a) = (1 + 1 / a') ^ 2 * T ^ (-a) * T := by
      have := e2
      rw [div_eq_iff hT0.ne'] at this
      rw [show T ^ (2 - 2 * σ) * ((1 + 1 / a') ^ 2 * T ^ a) =
        (1 + 1 / a') ^ 2 * (T ^ (2 - 2 * σ) * T ^ a) by ring, this]; ring
    linarith
  linarith

/-- **The classical mean-square asymptotic** `(1/T)∫_1^T |ζ(σ+it)|² dt → ζ(2σ)`, `1/2 < σ ≤ 1`. -/
theorem zeta_mean_square_tendsto {σ : ℝ} (h1 : 1 / 2 < σ) (h2 : σ ≤ 1) :
    Tendsto (fun T : ℝ => (∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2) / T) atTop
      (𝓝 (riemannZeta (2 * (σ : ℂ))).re) := by
  obtain ⟨C, hC, h⟩ := zeta_mean_value_uniform h1
  obtain ⟨c, hc, hE⟩ := Eσ_div_le h1
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun T : ℝ => C * c * T ^ (-(σ - 1 / 2))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (show 0 < σ - 1 / 2 by linarith)).const_mul (C * c)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hT0 : 0 < T := by linarith
  have hb := h σ le_rfl h2 T hT
  rw [Real.norm_eq_abs]
  have e : (∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2) / T -
      (riemannZeta (2 * (σ : ℂ))).re =
      ((∫ t in (1 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2) -
        (riemannZeta (2 * (σ : ℂ))).re * T) / T := by rw [sub_div, mul_div_cancel_right₀ _ hT0.ne']
  rw [e, abs_div, abs_of_pos hT0, div_le_iff₀ hT0]
  have hET := hE T hT
  unfold Eσ at hET
  rw [div_le_iff₀ hT0] at hET
  calc _ ≤ C * (T ^ ((3 : ℝ) / 2 - σ) + T ^ (2 - 2 * σ) * (1 + Real.log T) ^ 2) := hb
    _ ≤ C * (c * T ^ (-(σ - 1 / 2)) * T) := by gcongr
    _ = C * c * T ^ (-(σ - 1 / 2)) * T := by ring

/-- **From `0`**: `(1/T)∫_0^T |ζ(σ+it)|² dt → ζ(2σ)` for `1/2 < σ < 1`. -/
theorem zeta_mean_square_tendsto_zero {σ : ℝ} (h1 : 1 / 2 < σ) (h2 : σ < 1) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2) / T) atTop
      (𝓝 (riemannZeta (2 * (σ : ℂ))).re) := by
  have hc : Continuous (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2) := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    have hne : (σ : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    exact ((differentiableAt_riemannZeta hne).continuousAt.comp
      (f := fun t : ℝ => (σ : ℂ) + t * I) (x := t) (by fun_prop)).norm.pow 2
  set I0 := ∫ t in (0 : ℝ)..1, ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2
  have hlim0 : Tendsto (fun T : ℝ => I0 / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have := (zeta_mean_square_tendsto h1 h2.le).add hlim0
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  rw [← add_div, add_comm, intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]

/-- `ζ(2σ)` is real, so the limit is the real number `ζ(2σ) = ∑ n^{−2σ}`. -/
lemma riemannZeta_two_mul_real (σ : ℝ) (h : 1 / 2 < σ) :
    riemannZeta (2 * (σ : ℂ)) = (((riemannZeta (2 * (σ : ℂ))).re : ℝ) : ℂ) := by
  have e : 2 * (σ : ℂ) = ((2 * σ : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  exact riemannZeta_ofReal_eq_re (by linarith)

end RamanujanTau.ZetaMeanSquare
