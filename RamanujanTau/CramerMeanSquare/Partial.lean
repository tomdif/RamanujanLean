/-
# What the logarithmic asymptotic says about `∫₁^X S(x)² dx`

Write `I(X) = ∫₁^X S²`, `J(X) = ∫₁^X S² x^{−25/2}`, `C₀ = B/(50π²) = (2/25)·B/(4π²)`.

* `J_identity` (summation by parts; `I` has right derivative `S²` everywhere because `S` is a
  right-continuous step function):  `J(X) = X^{−25/2} I(X) + (25/2) ∫₁^X x^{−27/2} I(x) dx`.
* `frequently_gt`: for every `c < C₀`, `I(X) > c X^{25/2}` for arbitrarily large `X`;
* `frequently_lt`: for every `c > C₀`, `I(X) < c X^{25/2}` for arbitrarily large `X`;

i.e. `liminf I(X)/X^{25/2} ≤ C₀ ≤ limsup I(X)/X^{25/2}`, and in particular
`const_of_tendsto`: **if** `I(X)/X^{25/2}` has a limit, the limit is `C₀`.  The existence of the
limit (the classical Cramér–Tong theorem `I(X) ~ C₀ X^{25/2}`) is **not** proved here: it needs
regularity of `I` beyond the logarithmic mean (e.g. the truncated Voronoi formula).
-/
import RamanujanTau.CramerMeanSquare.Tauber

set_option autoImplicit false

namespace RamanujanTau.CramerMeanSquare

open Real MeasureTheory Set Filter Topology
open RamanujanTau.Voronoi (S psiR psiR_nonneg iI_psiR measurable_S intOn_S2)

/-- `I(X) = ∫₁^X S(x)² dx`. -/
noncomputable def Isq (x : ℝ) : ℝ := ∫ t in (1 : ℝ)..x, S t ^ 2

lemma iI_S2 {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => S x ^ 2) volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    ((intOn_S2 b).mono_set (Ioc_subset_Ioc_left ha))

lemma Isq_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ Isq x :=
  intervalIntegral.integral_nonneg hx fun t _ => sq_nonneg _

lemma S_right_const {x : ℝ} (hx : 0 ≤ x) : ∀ᶠ y in 𝓝[>] x, S y = S x := by
  have hmem : Ioo x ((⌊x⌋₊ : ℝ) + 1) ∈ 𝓝[>] x := Ioo_mem_nhdsGT (Nat.lt_floor_add_one x)
  filter_upwards [hmem] with y hy
  unfold S
  have : ⌊y⌋₊ = ⌊x⌋₊ := by
    rw [Nat.floor_eq_iff (by linarith [hy.1])]
    exact ⟨(Nat.floor_le hx).trans hy.1.le, hy.2⟩
  rw [this]

lemma hasDerivWithin_Isq {x : ℝ} (hx : 1 < x) : HasDerivWithinAt Isq (S x ^ 2) (Ioi x) x := by
  have hint : IntervalIntegrable (fun t => S t ^ 2) volume 1 x := iI_S2 le_rfl hx.le
  have hc : ContinuousWithinAt (fun t => S t ^ 2) (Ioi x) x := by
    have h := S_right_const (by linarith : (0 : ℝ) ≤ x)
    refine (continuousWithinAt_const (b := S x ^ 2)).congr_of_eventuallyEq ?_ rfl
    filter_upwards [h] with y hy
    rw [hy]
  have hm : StronglyMeasurableAtFilter (fun t => S t ^ 2) (𝓝[>] x) :=
    ((measurable_S.pow_const 2).stronglyMeasurable).stronglyMeasurableAtFilter
  exact (intervalIntegral.integral_hasDerivWithinAt_right (s := Ici x) (t := Ioi x) hint hm
    hc).mono Ioi_subset_Ici_self

lemma continuousOn_Isq {X : ℝ} (hX : 1 ≤ X) : ContinuousOn Isq (Icc 1 X) := by
  have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 1) (b := X)
    (f := fun t => S t ^ 2) (by
      rw [uIcc_of_le hX]
      exact (integrableOn_Icc_iff_integrableOn_Ioc).2 ((intOn_S2 X)))
  rw [uIcc_of_le hX] at h
  exact h

lemma continuousOn_rpow_Icc (p : ℝ) {X : ℝ} : ContinuousOn (fun x : ℝ => x ^ p) (Icc 1 X) :=
  fun x hx => (Real.continuousAt_rpow_const x p (Or.inl (by linarith [hx.1]))).continuousWithinAt

lemma iI_weighted {X : ℝ} (hX : 1 ≤ X) :
    IntervalIntegrable (fun x => x ^ (-(27 / 2 : ℝ)) * Isq x) volume 1 X := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hX]
  exact (continuousOn_rpow_Icc _).mul (continuousOn_Isq hX)

/-- **Summation by parts.** -/
theorem J_identity {X : ℝ} (hX : 1 ≤ X) :
    ∫ x in (1 : ℝ)..X, psiR x =
      X ^ (-(25 / 2 : ℝ)) * Isq X + 25 / 2 * ∫ x in (1 : ℝ)..X, x ^ (-(27 / 2 : ℝ)) * Isq x := by
  have hF := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (a := 1) (b := X)
    (f := fun x => x ^ (-(25 / 2 : ℝ)) * Isq x)
    (f' := fun x => (-(25 / 2 : ℝ)) * x ^ (-(25 / 2 : ℝ) - 1) * Isq x +
      x ^ (-(25 / 2 : ℝ)) * S x ^ 2) hX
    ((continuousOn_rpow_Icc _).mul (continuousOn_Isq hX))
    (fun x hx => by
      have hx0 : x ≠ 0 := by linarith [hx.1]
      exact ((Real.hasDerivAt_rpow_const (p := -(25 / 2 : ℝ)) (Or.inl hx0)).hasDerivWithinAt).mul
        (hasDerivWithin_Isq hx.1))
    (by
      refine IntervalIntegrable.add ?_ ?_
      · refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hX]
        exact (continuousOn_const.mul (continuousOn_rpow_Icc _)).mul (continuousOn_Isq hX)
      · refine (iI_psiR le_rfl hX).congr ?_
        intro x _
        simp only [psiR]; ring)
  have hI1 : Isq 1 = 0 := intervalIntegral.integral_same
  simp only [hI1, mul_zero, sub_zero] at hF
  rw [intervalIntegral.integral_add ?_ ?_] at hF
  · have e1 : ∫ x in (1 : ℝ)..X, (-(25 / 2 : ℝ)) * x ^ (-(25 / 2 : ℝ) - 1) * Isq x =
        -(25 / 2 * ∫ x in (1 : ℝ)..X, x ^ (-(27 / 2 : ℝ)) * Isq x) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [show -(25 / 2 : ℝ) - 1 = -(27 / 2) by norm_num]; ring
    have e2 : ∫ x in (1 : ℝ)..X, x ^ (-(25 / 2 : ℝ)) * S x ^ 2 = ∫ x in (1 : ℝ)..X, psiR x :=
      intervalIntegral.integral_congr fun x _ => by simp only [psiR]; ring
    rw [e1, e2] at hF
    linarith
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hX]
    exact (continuousOn_const.mul (continuousOn_rpow_Icc _)).mul (continuousOn_Isq hX)
  · refine (iI_psiR le_rfl hX).congr ?_
    intro x _
    simp only [psiR]; ring

lemma rpow_cancel {x : ℝ} (hx : 0 < x) : x ^ (-(27 / 2 : ℝ)) * x ^ (25 / 2 : ℝ) = x⁻¹ := by
  rw [← Real.rpow_add hx, show -(27 / 2 : ℝ) + 25 / 2 = -1 by norm_num, Real.rpow_neg_one]

lemma rpow_cancel' {x : ℝ} (hx : 0 < x) : x ^ (-(25 / 2 : ℝ)) * x ^ (25 / 2 : ℝ) = 1 := by
  rw [← Real.rpow_add hx, show -(25 / 2 : ℝ) + 25 / 2 = 0 by norm_num, Real.rpow_zero]

lemma J_upper {c x0 : ℝ} (hx0 : 1 ≤ x0) (h : ∀ x, x0 ≤ x → Isq x ≤ c * x ^ (25 / 2 : ℝ)) :
    ∀ X, x0 ≤ X → ∫ x in (1 : ℝ)..X, psiR x ≤
      c + 25 / 2 * ((∫ x in (1 : ℝ)..x0, x ^ (-(27 / 2 : ℝ)) * Isq x) + c * Real.log X) := by
  intro X hX
  have hX1 : 1 ≤ X := hx0.trans hX
  have hX0 : 0 < X := by linarith
  have hc : 0 ≤ c := by
    have h1 := h x0 le_rfl
    have h2 := Isq_nonneg hx0
    have h3 : 0 < x0 ^ (25 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    by_contra hneg
    push Not at hneg
    have : c * x0 ^ (25 / 2 : ℝ) < 0 := mul_neg_of_neg_of_pos hneg h3
    linarith
  rw [J_identity hX1]
  have hF : X ^ (-(25 / 2 : ℝ)) * Isq X ≤ c := by
    have := mul_le_mul_of_nonneg_left (h X hX) (Real.rpow_pos_of_pos hX0 (-(25 / 2 : ℝ))).le
    calc X ^ (-(25 / 2 : ℝ)) * Isq X ≤ X ^ (-(25 / 2 : ℝ)) * (c * X ^ (25 / 2 : ℝ)) := this
      _ = c * (X ^ (-(25 / 2 : ℝ)) * X ^ (25 / 2 : ℝ)) := by ring
      _ = c := by rw [rpow_cancel' hX0, mul_one]
  rw [← intervalIntegral.integral_add_adjacent_intervals (iI_weighted hx0)
    ((iI_weighted hx0).symm.trans (iI_weighted hX1))]
  have htail : ∫ x in x0..X, x ^ (-(27 / 2 : ℝ)) * Isq x ≤ c * Real.log X := by
    have hmono : ∫ x in x0..X, x ^ (-(27 / 2 : ℝ)) * Isq x ≤ ∫ x in x0..X, c * x⁻¹ := by
      refine intervalIntegral.integral_mono_on hX ((iI_weighted hx0).symm.trans (iI_weighted hX1))
        ?_ fun x hx => ?_
      · refine (ContinuousOn.intervalIntegrable ?_)
        exact continuousOn_const.mul (continuousOn_inv₀.mono fun y hy => by
          rw [uIcc_of_le hX] at hy; exact (show (0 : ℝ) < y by linarith [hy.1]).ne')
      · have hx0' : 0 < x := by linarith [hx.1]
        have := mul_le_mul_of_nonneg_left (h x hx.1) (Real.rpow_pos_of_pos hx0' (-(27 / 2 : ℝ))).le
        calc x ^ (-(27 / 2 : ℝ)) * Isq x ≤ x ^ (-(27 / 2 : ℝ)) * (c * x ^ (25 / 2 : ℝ)) := this
          _ = c * (x ^ (-(27 / 2 : ℝ)) * x ^ (25 / 2 : ℝ)) := by ring
          _ = c * x⁻¹ := by rw [rpow_cancel hx0']
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (by linarith) hX0,
      Real.log_div hX0.ne' (by linarith)] at hmono
    have := Real.log_nonneg hx0
    nlinarith
  nlinarith

lemma J_lower {c x0 : ℝ} (hx0 : 1 ≤ x0) (h : ∀ x, x0 ≤ x → c * x ^ (25 / 2 : ℝ) ≤ Isq x) :
    ∀ X, x0 ≤ X → 25 / 2 * (c * (Real.log X - Real.log x0)) ≤ ∫ x in (1 : ℝ)..X, psiR x := by
  intro X hX
  have hX1 : 1 ≤ X := hx0.trans hX
  have hX0 : 0 < X := by linarith
  rw [J_identity hX1]
  have hF : 0 ≤ X ^ (-(25 / 2 : ℝ)) * Isq X :=
    mul_nonneg (Real.rpow_pos_of_pos hX0 _).le (Isq_nonneg hX1)
  rw [← intervalIntegral.integral_add_adjacent_intervals (iI_weighted hx0)
    ((iI_weighted hx0).symm.trans (iI_weighted hX1))]
  have hhead : 0 ≤ ∫ x in (1 : ℝ)..x0, x ^ (-(27 / 2 : ℝ)) * Isq x :=
    intervalIntegral.integral_nonneg hx0 fun x hx =>
      mul_nonneg (Real.rpow_pos_of_pos (by linarith [hx.1]) _).le (Isq_nonneg hx.1)
  have htail : c * (Real.log X - Real.log x0) ≤ ∫ x in x0..X, x ^ (-(27 / 2 : ℝ)) * Isq x := by
    have hmono : ∫ x in x0..X, c * x⁻¹ ≤ ∫ x in x0..X, x ^ (-(27 / 2 : ℝ)) * Isq x := by
      refine intervalIntegral.integral_mono_on hX ?_
        ((iI_weighted hx0).symm.trans (iI_weighted hX1)) fun x hx => ?_
      · refine (ContinuousOn.intervalIntegrable ?_)
        exact continuousOn_const.mul (continuousOn_inv₀.mono fun y hy => by
          rw [uIcc_of_le hX] at hy; exact (show (0 : ℝ) < y by linarith [hy.1]).ne')
      · have hx0' : 0 < x := by linarith [hx.1]
        have := mul_le_mul_of_nonneg_left (h x hx.1) (Real.rpow_pos_of_pos hx0' (-(27 / 2 : ℝ))).le
        calc c * x⁻¹ = c * (x ^ (-(27 / 2 : ℝ)) * x ^ (25 / 2 : ℝ)) := by rw [rpow_cancel hx0']
          _ = x ^ (-(27 / 2 : ℝ)) * (c * x ^ (25 / 2 : ℝ)) := by ring
          _ ≤ _ := this
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (by linarith) hX0,
      Real.log_div hX0.ne' (by linarith)] at hmono
    exact hmono
  nlinarith

/-- The Cramér constant `C₀ = B/(50π²)`. -/
noncomputable def C0 : ℝ := RamanujanTau.MeanSquare.RS (25 / 2) / (50 * π ^ 2)

lemma C0_eq : C0 = 2 / 25 * (RamanujanTau.MeanSquare.RS (25 / 2) / (4 * π ^ 2)) := by
  unfold C0
  have : π ≠ 0 := Real.pi_ne_zero
  field_simp; ring

/-- `I(X) > c X^{25/2}` for arbitrarily large `X`, whenever `c < C₀`. -/
theorem frequently_gt {c : ℝ} (hc : c < C0) :
    ∃ᶠ X in atTop, c * X ^ (25 / 2 : ℝ) < Isq X := by
  set A := RamanujanTau.MeanSquare.RS (25 / 2) / (4 * π ^ 2) with hA
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  obtain ⟨x1, hx1⟩ := eventually_atTop.1 hcon
  set x0 := max x1 1 with hx0
  have hx01 : 1 ≤ x0 := le_max_right _ _
  have h : ∀ x, x0 ≤ x → Isq x ≤ c * x ^ (25 / 2 : ℝ) := fun x hx =>
    not_lt.1 (hx1 x ((le_max_left _ _).trans hx))
  set K0 := ∫ x in (1 : ℝ)..x0, x ^ (-(27 / 2 : ℝ)) * Isq x
  have hb : Tendsto (fun X => (c + 25 / 2 * K0) / Real.log X + 25 / 2 * c) atTop
      (𝓝 (0 + 25 / 2 * c)) :=
    (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop).add tendsto_const_nhds
  rw [zero_add] at hb
  have hle : A ≤ 25 / 2 * c := by
    refine le_of_tendsto_of_tendsto tau_cramer_log_core hb ?_
    filter_upwards [eventually_ge_atTop (max x0 (Real.exp 1))] with X hX
    have hXx0 : x0 ≤ X := (le_max_left _ _).trans hX
    have hl1 : 1 ≤ Real.log X := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hX)
    have hJ := J_upper hx01 h X hXx0
    rw [div_add' _ _ _ (by linarith), div_le_div_iff_of_pos_right (by linarith)]
    linarith
  rw [C0_eq] at hc
  linarith

/-- `I(X) < c X^{25/2}` for arbitrarily large `X`, whenever `c > C₀`. -/
theorem frequently_lt {c : ℝ} (hc : C0 < c) :
    ∃ᶠ X in atTop, Isq X < c * X ^ (25 / 2 : ℝ) := by
  set A := RamanujanTau.MeanSquare.RS (25 / 2) / (4 * π ^ 2) with hA
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  obtain ⟨x1, hx1⟩ := eventually_atTop.1 hcon
  set x0 := max x1 1 with hx0
  have hx01 : 1 ≤ x0 := le_max_right _ _
  have h : ∀ x, x0 ≤ x → c * x ^ (25 / 2 : ℝ) ≤ Isq x := fun x hx =>
    not_lt.1 (hx1 x ((le_max_left _ _).trans hx))
  have hb : Tendsto (fun X => 25 / 2 * c - 25 / 2 * c * Real.log x0 / Real.log X) atTop
      (𝓝 (25 / 2 * c - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)
  rw [sub_zero] at hb
  have hle : 25 / 2 * c ≤ A := by
    refine le_of_tendsto_of_tendsto hb tau_cramer_log_core ?_
    filter_upwards [eventually_ge_atTop (max x0 (Real.exp 1))] with X hX
    have hXx0 : x0 ≤ X := (le_max_left _ _).trans hX
    have hl1 : 1 ≤ Real.log X := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hX)
    have hJ := J_lower hx01 h X hXx0
    rw [sub_div' (by linarith), div_le_div_iff_of_pos_right (by linarith)]
    linarith
  rw [C0_eq] at hc
  linarith

/-- **If** `I(X)/X^{25/2}` converges, its limit is `C₀ = B/(50π²)`. -/
theorem const_of_tendsto {C : ℝ}
    (h : Tendsto (fun X => Isq X / X ^ (25 / 2 : ℝ)) atTop (𝓝 C)) : C = C0 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `C < C₀`: eventually `I < c X^{25/2}` with `c = (C + C₀)/2 < C₀`
    have hc : (C + C0) / 2 < C0 := by linarith
    have hev := h.eventually (gt_mem_nhds (show C < (C + C0) / 2 by linarith))
    have hfr := frequently_gt hc
    obtain ⟨X, hX2, hX3, hX1⟩ := (hfr.and_eventually (hev.and (eventually_gt_atTop 0))).exists
    have hp : 0 < X ^ (25 / 2 : ℝ) := Real.rpow_pos_of_pos hX1 _
    rw [div_lt_iff₀ hp] at hX3
    linarith
  · have hc : C0 < (C + C0) / 2 := by linarith
    have hev := h.eventually (lt_mem_nhds (show (C + C0) / 2 < C by linarith))
    have hfr := frequently_lt hc
    obtain ⟨X, hX2, hX3, hX1⟩ := (hfr.and_eventually (hev.and (eventually_gt_atTop 0))).exists
    have hp : 0 < X ^ (25 / 2 : ℝ) := Real.rpow_pos_of_pos hX1 _
    rw [lt_div_iff₀ hp] at hX3
    linarith

end RamanujanTau.CramerMeanSquare
