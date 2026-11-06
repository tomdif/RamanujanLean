/-
# From the Mellin mean square to the log-averaged mean square (Ω form)

`lintegral_weight_le` (Tonelli): for `f ≥ 0` with `∫_{(1,y)} f ≤ Φ(y)`,

    ∫₁^∞ f(x) x^{−p} dx ≤ ∫₁^∞ p y^{−p−1} Φ(y) dy.

`log_mean_sq_omega`: with `f = |R|² x^{−7/4}`, `p = 2δ`, `Φ = κ log y + B`, the Mellin lower
bound `≥ K/δ` (`mellin_mean_sq_lower`) contradicts `∫₁^X |R|² x^{−7/4} ≤ κ log X` (all large `X`)
for `κ = K/4`. Hence `∫₁^X |R(x)|² x^{−7/4} dx ≥ κ log X` for **arbitrarily large** `X`.

The bound for *all* large `X` (`≫ log X`) does not follow from a Mellin (Laplace-type) lower bound
alone; it would follow from it together with the (open) upper bound `∫₁^X |R|² x^{−7/4} ≪ log X`.
See `docs/RANKIN_OMEGA_PM.md` §2.
-/
import RamanujanTau.RankinOmegaPM.MeanSq

set_option autoImplicit false

namespace RamanujanTau.RankinOmegaPM

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral RamanujanTau.RankinSharpGeneral
open RamanujanTau.RankinOmega
open scoped Real Interval ENNReal

/-- `x^{−p} = ∫_x^∞ p y^{−p−1} dy` as lower integrals. -/
lemma ofReal_rpow_eq_lintegral {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    ENNReal.ofReal (x ^ (-p)) = ∫⁻ y in Ioi x, ENNReal.ofReal (p * y ^ (-p - 1)) := by
  have hi : IntegrableOn (fun y : ℝ => p * y ^ (-p - 1)) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hx).const_mul p
  rw [← ofReal_integral_eq_lintegral_ofReal hi ((ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall fun y hy => by
      have : 0 < y := lt_trans hx hy
      have := Real.rpow_pos_of_pos this (-p - 1)
      positivity))]
  congr 1
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hx]
  have e : -p - 1 + 1 = -p := by ring
  rw [e]; field_simp

/-- **Tonelli / partial integration**, in lower-integral form. -/
lemma lintegral_weight_le {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfm : Measurable f) {p : ℝ}
    (hp : 0 < p) {Φ : ℝ → ℝ≥0∞}
    (hG : ∀ y, 1 < y → ∫⁻ x in Ioo 1 y, ENNReal.ofReal (f x) ≤ Φ y) :
    ∫⁻ x in Ioi 1, ENNReal.ofReal (f x * x ^ (-p)) ≤
      ∫⁻ y in Ioi 1, ENNReal.ofReal (p * y ^ (-p - 1)) * Φ y := by
  set k : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (p * y ^ (-p - 1)) with hk
  have hkm : Measurable k :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_id.pow_const _))
  set S : Set (ℝ × ℝ) := {q | 1 < q.1 ∧ q.1 < q.2} with hS
  have hSm : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)
  set H : ℝ → ℝ → ℝ≥0∞ := fun x y =>
    S.indicator (fun q : ℝ × ℝ => ENNReal.ofReal (f q.1) * k q.2) (x, y) with hH
  have hHm : Measurable (Function.uncurry H) := by
    have : Function.uncurry H = S.indicator (fun q : ℝ × ℝ => ENNReal.ofReal (f q.1) * k q.2) := by
      funext q; rfl
    rw [this]
    exact ((ENNReal.measurable_ofReal.comp (hfm.comp measurable_fst)).mul
      (hkm.comp measurable_snd)).indicator hSm
  have hL : ∫⁻ x in Ioi 1, ENNReal.ofReal (f x * x ^ (-p)) = ∫⁻ x, ∫⁻ y, H x y := by
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem hx]
      have hx0 : 0 < x := lt_trans zero_lt_one hx
      rw [ENNReal.ofReal_mul (hf0 x), ofReal_rpow_eq_lintegral hp hx0,
        ← lintegral_const_mul _ hkm, ← lintegral_indicator measurableSet_Ioi]
      refine lintegral_congr fun y => ?_
      by_cases hy : y ∈ Ioi x
      · rw [indicator_of_mem hy]
        exact (Set.indicator_of_mem (show (x, y) ∈ S from ⟨hx, hy⟩)
          (fun q : ℝ × ℝ => ENNReal.ofReal (f q.1) * k q.2)).symm
      · rw [Set.indicator_of_notMem hy (fun y => ENNReal.ofReal (f x) * k y)]
        exact (Set.indicator_of_notMem (show (x, y) ∉ S from fun h => hy h.2)
          (fun q : ℝ × ℝ => ENNReal.ofReal (f q.1) * k q.2)).symm
    · rw [indicator_of_notMem hx]
      have h0 : ∀ y, H x y = 0 := fun y =>
        indicator_of_notMem (show (x, y) ∉ S from fun h => hx h.1) _
      simp [h0]
  rw [hL, lintegral_lintegral_swap hHm.aemeasurable, ← lintegral_indicator measurableSet_Ioi]
  refine lintegral_mono fun y => ?_
  by_cases hy : y ∈ Ioi (1 : ℝ)
  · rw [indicator_of_mem hy]
    have e : ∀ x, H x y = (Ioo 1 y).indicator (fun x => ENNReal.ofReal (f x) * k y) x := by
      intro x
      by_cases hx : x ∈ Ioo 1 y
      · rw [indicator_of_mem hx]
        exact indicator_of_mem (show (x, y) ∈ S from ⟨hx.1, hx.2⟩) _
      · rw [indicator_of_notMem hx]
        exact indicator_of_notMem (show (x, y) ∉ S from fun h => hx ⟨h.1, h.2⟩) _
    simp_rw [e]
    rw [lintegral_indicator measurableSet_Ioo,
      lintegral_mul_const _ hfm.ennreal_ofReal, mul_comm]
    exact mul_le_mul_right (hG y hy) _
  · rw [indicator_of_notMem hy]
    have h0 : ∀ x, H x y = 0 := by
      intro x
      refine indicator_of_notMem (show (x, y) ∉ S from fun h => hy ?_) _
      exact lt_trans h.1 h.2
    simp [h0]

section Data

variable {m : ℕ} {a : ℕ → ℝ} {κ : ℝ} (d : RSDataM m a κ)
variable (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))

/-- The log-weighted square `|R(x)|² x^{−7/4}`. -/
noncomputable def gsq (a : ℕ → ℝ) (c : ℝ) (x : ℝ) : ℝ := ‖Rf a c x‖ ^ 2 * x ^ (-(7 / 4 : ℝ))

lemma measurable_gsq (c : ℝ) : Measurable (gsq a c) := by
  unfold gsq
  exact ((measurable_Rf c).norm.pow_const 2).mul (measurable_id.pow_const _)

lemma gsq_nonneg' (c : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ gsq a c x := by
  unfold gsq; have := Real.rpow_nonneg hx (-(7 / 4 : ℝ)); positivity

/-- `g = |R|² x^{−7/4}` (extended by `0` on `x < 0`). -/
noncomputable def gsq0 (a : ℕ → ℝ) (c : ℝ) (x : ℝ) : ℝ := (Ici (0 : ℝ)).indicator (gsq a c) x

lemma gsq0_nonneg (c : ℝ) (x : ℝ) : 0 ≤ gsq0 a c x := by
  unfold gsq0
  by_cases hx : x ∈ Ici (0 : ℝ)
  · rw [indicator_of_mem hx]; exact gsq_nonneg' c hx
  · rw [indicator_of_notMem hx]

lemma measurable_gsq0 (c : ℝ) : Measurable (gsq0 a c) :=
  (measurable_gsq c).indicator measurableSet_Ici

lemma integrableOn_gsq (c : ℝ) (y : ℝ) : IntegrableOn (gsq a c) (Ioc 1 y) := by
  refine Measure.integrableOn_of_bounded (M := (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ‖(a n : ℂ)‖ + |c| * y) ^ 2)
    measure_Ioc_lt_top.ne (measurable_gsq c).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun x hx => ?_
  have hx1 : 1 < x := hx.1
  have hx0 : 0 ≤ x := by linarith
  have hb := norm_Rf_le (a := a) c hx0 hx.2
  have hp : x ^ (-(7 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)
  have hp0 : 0 ≤ x ^ (-(7 / 4 : ℝ)) := Real.rpow_nonneg hx0 _
  rw [Real.norm_of_nonneg (gsq_nonneg' c hx0), gsq]
  have h2 : ‖Rf a c x‖ ^ 2 ≤ (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ‖(a n : ℂ)‖ + |c| * y) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 2
  calc ‖Rf a c x‖ ^ 2 * x ^ (-(7 / 4 : ℝ)) ≤ ‖Rf a c x‖ ^ 2 * 1 := by
        gcongr
    _ ≤ _ := by rw [mul_one]; exact h2

lemma log_le_rpow_div {y δ : ℝ} (hy : 0 < y) (hδ : 0 < δ) : Real.log y ≤ y ^ δ / δ := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy δ)
  rw [Real.log_rpow hy] at h
  rw [le_div_iff₀ hδ]
  nlinarith

include d habs in
/-- **The log-averaged mean square is not `o(log X)`.** There is `κ > 0` such that
`∫₁^X |R(x)|² x^{−7/4} dx ≥ κ log X` for arbitrarily large `X`. -/
theorem log_mean_sq_omega (hm : 1 ≤ m) (hne : ∃ n, 0 < n ∧ a n ≠ 0) (c : ℝ) :
    ∃ κ' : ℝ, 0 < κ' ∧ ∀ X0 : ℝ, ∃ X : ℝ, X0 ≤ X ∧
      κ' * Real.log X ≤ ∫ x in (1 : ℝ)..X, ‖Rf a c x‖ ^ 2 * x ^ (-(7 / 4 : ℝ)) := by
  obtain ⟨K, hK, hlow⟩ := mellin_mean_sq_lower d habs hm hne c
  refine ⟨K / 4, by positivity, fun X0 => ?_⟩
  by_contra hcon
  push Not at hcon
  set X1 : ℝ := max X0 2 with hX1
  have hX11 : 1 ≤ X1 := le_trans (by norm_num) (le_max_right _ _)
  set B : ℝ := ∫ x in (1 : ℝ)..X1, gsq a c x with hB
  have hint : ∀ y, IntegrableOn (gsq0 a c) (Ioo 1 y) := by
    intro y
    refine ((integrableOn_gsq (a := a) c y).mono_set Ioo_subset_Ioc_self).congr_fun
      (fun x hx => ?_) measurableSet_Ioo
    have : x ∈ Ici (0 : ℝ) := le_of_lt (lt_trans zero_lt_one hx.1)
    simp [gsq0, indicator_of_mem this]
  have hIoo : ∀ y, 1 ≤ y → ∫ x in Ioo 1 y, gsq0 a c x = ∫ x in (1 : ℝ)..y, gsq a c x := by
    intro y hy
    rw [intervalIntegral.integral_of_le hy, ← integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    have : x ∈ Ici (0 : ℝ) := le_of_lt (lt_trans zero_lt_one hx.1)
    simp [gsq0, indicator_of_mem this]
  have hB0 : 0 ≤ B := by
    rw [hB, ← hIoo X1 hX11]
    exact setIntegral_nonneg measurableSet_Ioo fun x _ => gsq0_nonneg c x
  have hG : ∀ y, 1 < y → ∫⁻ x in Ioo 1 y, ENNReal.ofReal (gsq0 a c x) ≤
      ENNReal.ofReal (K / 4 * Real.log y + B) := by
    intro y hy
    rw [← ofReal_integral_eq_lintegral_ofReal (hint y)
      (Eventually.of_forall fun x => gsq0_nonneg c x)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hIoo y hy.le]
    have hlog : 0 ≤ Real.log y := Real.log_nonneg hy.le
    rcases le_or_gt y X1 with hyX | hyX
    · have hmono : ∫ x in (1 : ℝ)..y, gsq a c x ≤ B := by
        rw [hB, ← hIoo X1 hX11, ← hIoo y hy.le]
        exact setIntegral_mono_set (hint X1) (Eventually.of_forall fun x => gsq0_nonneg c x)
          (Eventually.of_forall (Ioo_subset_Ioo_right hyX))
      have : 0 ≤ K / 4 * Real.log y := by positivity
      linarith
    · have hyX0 : X0 ≤ y := le_trans (le_max_left _ _) hyX.le
      have := (hcon y hyX0).le
      have e : ∫ x in (1 : ℝ)..y, gsq a c x =
          ∫ x in (1 : ℝ)..y, ‖Rf a c x‖ ^ 2 * x ^ (-(7 / 4 : ℝ)) := rfl
      linarith
  -- choose δ
  set δ : ℝ := min (1 / 32) (K / (4 * (B + 1))) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 32 := min_le_left _ _
  have hδ2 : δ ≤ K / (4 * (B + 1)) := min_le_right _ _
  have hW := lintegral_weight_le (f := gsq0 a c) (fun x => gsq0_nonneg c x) (measurable_gsq0 c)
    (p := 2 * δ) (by positivity) hG
  -- left side is the Mellin mean square
  have hLeq : ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (gsq0 a c x * x ^ (-(2 * δ))) =
      ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (‖Rf a c x‖ ^ 2 * x ^ (-(2 * (3 / 8 + δ)) - 1)) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have : x ∈ Ici (0 : ℝ) := hx0.le
    simp only [gsq0, indicator_of_mem this, gsq]
    rw [mul_assoc, ← Real.rpow_add hx0]
    congr 3; ring
  -- right side is explicit
  have hRle : ∫⁻ y in Ioi (1 : ℝ), ENNReal.ofReal (2 * δ * y ^ (-(2 * δ) - 1)) *
      ENNReal.ofReal (K / 4 * Real.log y + B) ≤ ENNReal.ofReal (K / (2 * δ) + B) := by
    have hi1 : IntegrableOn (fun y : ℝ => y ^ (-δ - 1)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    have hi2 : IntegrableOn (fun y : ℝ => y ^ (-(2 * δ) - 1)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    have hI : IntegrableOn (fun y : ℝ => K / 2 * y ^ (-δ - 1) + 2 * δ * B * y ^ (-(2 * δ) - 1))
        (Ioi 1) := (hi1.const_mul _).add (hi2.const_mul _)
    have hval : ∫ y in Ioi (1 : ℝ), (K / 2 * y ^ (-δ - 1) + 2 * δ * B * y ^ (-(2 * δ) - 1)) =
        K / (2 * δ) + B := by
      rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,
        integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
      simp only [Real.one_rpow]
      have hδne : δ ≠ 0 := hδ0.ne'
      rw [show -δ - 1 + 1 = -δ by ring, show -(2 * δ) - 1 + 1 = -(2 * δ) by ring]
      field_simp
    rw [← hval, ofReal_integral_eq_lintegral_ofReal hI ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun y hy => by
        have hy0 : 0 < y := lt_trans zero_lt_one hy
        have := Real.rpow_pos_of_pos hy0 (-δ - 1)
        have := Real.rpow_pos_of_pos hy0 (-(2 * δ) - 1)
        positivity))]
    refine setLIntegral_mono' measurableSet_Ioi fun y hy => ?_
    have hy0 : 0 < y := lt_trans zero_lt_one hy
    have hp1 : 0 < y ^ (-(2 * δ) - 1) := Real.rpow_pos_of_pos hy0 _
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hl := log_le_rpow_div hy0 hδ0
    have e : y ^ (-(2 * δ) - 1) * y ^ δ = y ^ (-δ - 1) := by
      rw [← Real.rpow_add hy0]; ring_nf
    have : 2 * δ * y ^ (-(2 * δ) - 1) * (K / 4 * Real.log y + B) ≤
        2 * δ * y ^ (-(2 * δ) - 1) * (K / 4 * (y ^ δ / δ) + B) := by
      gcongr
    calc _ ≤ 2 * δ * y ^ (-(2 * δ) - 1) * (K / 4 * (y ^ δ / δ) + B) := this
      _ = K / 2 * (y ^ (-(2 * δ) - 1) * y ^ δ) + 2 * δ * B * y ^ (-(2 * δ) - 1) := by
          field_simp; ring
      _ = _ := by rw [e]
  have hchain := (hlow δ hδ0 hδ1).trans (hLeq ▸ hW |>.trans hRle)
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
  -- `K/δ ≤ K/(2δ) + B` but `K/(2δ) ≥ 2(B+1)`
  have h1 : K / (2 * δ) ≤ B := by
    have : K / δ = K / (2 * δ) + K / (2 * δ) := by field_simp; ring
    linarith
  have h2 : 2 * (B + 1) ≤ K / (2 * δ) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hδ2 (show (0 : ℝ) ≤ 4 * (B + 1) by positivity)
    have e : 4 * (B + 1) * (K / (4 * (B + 1))) = K := by field_simp
    nlinarith
  linarith

end Data

end RamanujanTau.RankinOmegaPM
