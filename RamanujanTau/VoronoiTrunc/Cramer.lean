/-
# Consequence: existence of the Cramér–Tong limit

`tau_cramer_exists`: `X^{−25/2} ∫₁^X S(x)² dx → B/(50π²)`, `B = Σ τ(n)² n^{−25/2}`.

1. `V_N` with `N = ⌊X^{1/4}⌋` has dyadic mean square `(B/4π²) ∫_X^{2X} x^{23/2} dx (1 + o(1))`
   (`mean_value`, off-diagonal `≪ X^{12} √N log N`).
2. `S = V_N + D` with `∫_X^{2X} D² = o(X^{25/2})` (`voronoi_L2`), and `2|V D| ≤ εV² + D²/ε`.
3. Dyadic blocks `∫_Y^{2Y} S² ~ c(2^{25/2}−1) Y^{25/2}` sum to `∫₁^X S² ~ c X^{25/2}`.
-/
import RamanujanTau.VoronoiTrunc.Final

set_option autoImplicit false

namespace RamanujanTau.VoronoiTrunc

open Complex Real MeasureTheory Set Filter Topology

lemma measurable_Sre : Measurable Sre := by
  have h : Sre = (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ((tau n : ℤ) : ℝ)) ∘ (fun x : ℝ => ⌊x⌋₊) := rfl
  rw [h]
  exact (measurable_from_nat).comp Nat.measurable_floor

lemma abs_Sre_le {x b : ℝ} (hxb : x ≤ b) :
    |Sre x| ≤ ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, |((tau n : ℤ) : ℝ)| := by
  unfold Sre
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hxb))
    (fun _ _ _ => abs_nonneg _)

lemma integrableOn_bounded_meas {f : ℝ → ℝ} (hf : Measurable f) {a b K : ℝ}
    (hK : ∀ x ∈ Ioc a b, |f x| ≤ K) : IntegrableOn f (Ioc a b) := by
  refine Measure.integrableOn_of_bounded (M := K) (by simp) hf.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs]; exact hK x hx

lemma integrableOn_Sre_sq (a b : ℝ) : IntegrableOn (fun x => Sre x ^ 2) (Ioc a b) := by
  set K := ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, |((tau n : ℤ) : ℝ)|
  refine integrableOn_bounded_meas (measurable_Sre.pow_const 2) (K := K ^ 2) fun x hx => ?_
  rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_Sre_le hx.2) 2

lemma integrableOn_D_sq (N : ℕ) (a b : ℝ) : IntegrableOn (fun x => (Sre x - Vth N x) ^ 2) (Ioc a b) := by
  obtain ⟨Kv, hKv⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (continuous_Vth N).continuousOn
  set K := ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, |((tau n : ℤ) : ℝ)|
  refine integrableOn_bounded_meas ((measurable_Sre.sub (continuous_Vth N).measurable).pow_const 2)
    (K := (K + Kv) ^ 2) fun x hx => ?_
  rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
  refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
  have h1 := abs_Sre_le hx.2
  have h2 := hKv x (Ioc_subset_Icc_self hx)
  rw [Real.norm_eq_abs] at h2
  calc |Sre x - Vth N x| ≤ |Sre x| + |Vth N x| := abs_sub _ _
    _ ≤ K + Kv := add_le_add h1 h2

lemma integrableOn_V_sq (N : ℕ) (a b : ℝ) : IntegrableOn (fun x => Vth N x ^ 2) (Ioc a b) :=
  (((continuous_Vth N).pow 2).continuousOn (s := Icc a b)).integrableOn_Icc (μ := volume)
    |>.mono_set Ioc_subset_Icc_self

/-- `|∫S² − ∫V²| ≤ ε ∫V² + (1 + 1/ε) ∫(S−V)²`. -/
lemma abs_integral_S_sq_sub_le (N : ℕ) {a b ε : ℝ} (hε : 0 < ε) :
    |(∫ x in Ioc a b, Sre x ^ 2) - ∫ x in Ioc a b, Vth N x ^ 2| ≤
      ε * (∫ x in Ioc a b, Vth N x ^ 2) + (1 + 1 / ε) * ∫ x in Ioc a b, (Sre x - Vth N x) ^ 2 := by
  have hS := integrableOn_Sre_sq a b
  have hV := integrableOn_V_sq N a b
  have hD := integrableOn_D_sq N a b
  rw [← integral_sub hS hV, ← integral_const_mul, ← integral_const_mul, ← integral_add (hV.const_mul _)
    (hD.const_mul _)]
  refine (abs_integral_le_integral_abs).trans (integral_mono (hS.sub hV).abs
    ((hV.const_mul _).add (hD.const_mul _)) fun x => ?_)
  simp only
  set V := Vth N x
  set D := Sre x - Vth N x
  have hSx : Sre x = V + D := by simp [V, D]
  rw [hSx]
  have e : (V + D) ^ 2 - V ^ 2 = 2 * V * D + D ^ 2 := by ring
  rw [e]
  have h1 : 2 * V * D ≤ ε * V ^ 2 + D ^ 2 / ε := by
    have := sq_nonneg (ε * V - D)
    rw [div_eq_mul_inv]
    have hi : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε.ne'
    nlinarith [mul_nonneg (inv_nonneg.2 hε.le) this]
  have h2 : -(2 * V * D) ≤ ε * V ^ 2 + D ^ 2 / ε := by
    have := sq_nonneg (ε * V + D)
    rw [div_eq_mul_inv]
    have hi : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε.ne'
    nlinarith [mul_nonneg (inv_nonneg.2 hε.le) this]
  rw [abs_le]
  constructor
  · have : 0 ≤ D ^ 2 := sq_nonneg _
    have : (1 + 1 / ε) * D ^ 2 = D ^ 2 + D ^ 2 / ε := by field_simp
    nlinarith
  · have : (1 + 1 / ε) * D ^ 2 = D ^ 2 + D ^ 2 / ε := by field_simp
    nlinarith


/-! ### The mean square of `V_N` on a dyadic block -/

lemma Vth_sq (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Vth N x ^ 2 = 1 / (2 * π ^ 2) * (wt x * (∑ n ∈ Finset.Icc 1 N, bco n * Real.cos (th n x)) ^ 2) := by
  unfold Vth
  rw [mul_pow, div_pow, wt_eq x hx, mul_pow, Real.sq_sqrt (by norm_num)]
  field_simp

lemma integral_wt {X : ℝ} (hX : 0 < X) :
    ∫ x in X..2 * X, wt x = (2 ^ (25 / 2 : ℝ) - 1) / (25 / 2) * X ^ (25 / 2 : ℝ) := by
  have e : ∀ x ∈ Set.uIcc X (2 * X), wt x = x ^ (23 / 2 : ℝ) := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have hx0 : 0 ≤ x := by linarith [hx.1]
    rw [← wt_eq x hx0, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  rw [intervalIntegral.integral_congr e, integral_rpow (Or.inl (by norm_num)),
    Real.mul_rpow (by norm_num) hX.le]
  norm_num
  ring

lemma Vsq_bound {X : ℝ} (hX : 1 ≤ X) (N : ℕ) :
    |(∫ x in X..2 * X, Vth N x ^ 2) -
        1 / (4 * π ^ 2) * (∑ n ∈ Finset.Icc 1 N, bco n ^ 2) * ∫ x in X..2 * X, wt x| ≤
      1 / (2 * π ^ 2) * ((2 * X) ^ 12 * √(N : ℝ) * (2 * Hs N + 1) * ∑ n ∈ Finset.Icc 1 N, bco n ^ 2) := by
  have hF : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n ∧ n ≤ N := fun n hn => Finset.mem_Icc.1 hn
  have hmv := mean_value (Finset.Icc 1 N) hF bco (a := X) (b := 2 * X) hX (by linarith)
  have e : ∫ x in X..2 * X, Vth N x ^ 2 =
      1 / (2 * π ^ 2) * ∫ x in X..2 * X, wt x * (∑ n ∈ Finset.Icc 1 N, bco n * Real.cos (th n x)) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    exact Vth_sq N (by linarith [hx.1])
  rw [e]
  have e2 : 1 / (4 * π ^ 2) * (∑ n ∈ Finset.Icc 1 N, bco n ^ 2) * ∫ x in X..2 * X, wt x =
      1 / (2 * π ^ 2) * ((1 / 2) * (∑ n ∈ Finset.Icc 1 N, bco n ^ 2) * ∫ x in X..2 * X, wt x) := by
    field_simp; ring
  rw [e2, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
  gcongr


/-! ### Dyadic limits -/

/-- `B = Σ bₙ²`. -/
noncomputable def Bsum : ℝ := ∑' n : ℕ, bco n ^ 2

lemma bco_zero : bco 0 = 0 := by simp [bco, tau_zero]

lemma tendsto_partial_bco : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, bco n ^ 2) atTop (𝓝 Bsum) := by
  have h := (summable_bco_sq.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  refine h.congr fun N => ?_
  simp only [Function.comp]
  rw [sum_Icc_eq_range (g := fun n => bco n ^ 2) (by simp [bco_zero]) N]

lemma partial_bco_le (N : ℕ) : ∑ n ∈ Finset.Icc 1 N, bco n ^ 2 ≤ Bsum :=
  summable_bco_sq.sum_le_tsum _ fun _ _ => sq_nonneg _

/-- The dyadic constant `κ = (B/4π²) (2^{25/2} − 1)/(25/2)`. -/
noncomputable def kap : ℝ := 1 / (4 * π ^ 2) * Bsum * ((2 ^ (25 / 2 : ℝ) - 1) / (25 / 2))

lemma tendsto_v :
    Tendsto (fun X : ℝ => (∫ x in X..2 * X, Vth ⌊X ^ (1 / 4 : ℝ)⌋₊ x ^ 2) / X ^ (25 / 2 : ℝ))
      atTop (𝓝 kap) := by
  set cw : ℝ := (2 ^ (25 / 2 : ℝ) - 1) / (25 / 2)
  set m : ℝ → ℝ := fun X => 1 / (4 * π ^ 2) * (∑ n ∈ Finset.Icc 1 ⌊X ^ (1 / 4 : ℝ)⌋₊, bco n ^ 2) * cw
  have hm : Tendsto m atTop (𝓝 kap) := by
    have h := (tendsto_partial_bco.comp (tendsto_nat_floor_atTop.comp
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4))))
    have := (h.const_mul (1 / (4 * π ^ 2))).mul_const cw
    simpa [m, kap, Function.comp] using this
  -- the error
  set g : ℝ → ℝ := fun X => 1 / (2 * π ^ 2) * (2 ^ 12 * 35 * Bsum) * X ^ (-(5 / 16) : ℝ)
  have hg : Tendsto g atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5 / 16)).const_mul
      (1 / (2 * π ^ 2) * (2 ^ 12 * 35 * Bsum))
    simpa [g] using this
  have hB0 : 0 ≤ Bsum := tsum_nonneg fun _ => sq_nonneg _
  have hle : ∀ᶠ X in atTop, ‖(∫ x in X..2 * X, Vth ⌊X ^ (1 / 4 : ℝ)⌋₊ x ^ 2) / X ^ (25 / 2 : ℝ) - m X‖ ≤ g X := by
    filter_upwards [eventually_ge_atTop 1] with X hX
    have hX0 : 0 < X := by linarith
    set N := ⌊X ^ (1 / 4 : ℝ)⌋₊
    have hN : (N : ℝ) ≤ X ^ (1 / 4 : ℝ) := floor_rpow_le hX0
    have hNX : (N : ℝ) ≤ X := hN.trans (by simpa using rpow_le_of_le hX (show (1 / 4 : ℝ) ≤ 1 by norm_num))
    have hb := Vsq_bound hX N
    rw [integral_wt hX0] at hb
    have hXp : 0 < X ^ (25 / 2 : ℝ) := by positivity
    have hmX : m X = (1 / (4 * π ^ 2) * (∑ n ∈ Finset.Icc 1 N, bco n ^ 2) *
        ((2 ^ (25 / 2 : ℝ) - 1) / (25 / 2) * X ^ (25 / 2 : ℝ))) / X ^ (25 / 2 : ℝ) := by
      simp only [m, cw]; field_simp; ring
    rw [hmX, ← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos hXp, div_le_iff₀ hXp]
    refine hb.trans ?_
    have hs : √(N : ℝ) ≤ X ^ (1 / 8 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      calc (N : ℝ) ^ (1 / 2 : ℝ) ≤ (X ^ (1 / 4 : ℝ)) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by norm_num)
        _ = X ^ (1 / 8 : ℝ) := by rw [← Real.rpow_mul hX0.le]; norm_num
    have hH := Hs_bound hX hNX
    have hH0 : 0 ≤ 2 * Hs N + 1 := by have := Hs_nonneg N; linarith
    have hS := partial_bco_le N
    have hS0 : 0 ≤ ∑ n ∈ Finset.Icc 1 N, bco n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc 1 / (2 * π ^ 2) * ((2 * X) ^ 12 * √(N : ℝ) * (2 * Hs N + 1) * ∑ n ∈ Finset.Icc 1 N, bco n ^ 2)
        ≤ 1 / (2 * π ^ 2) * ((2 * X) ^ 12 * X ^ (1 / 8 : ℝ) * (35 * X ^ (1 / 16 : ℝ)) * Bsum) := by
          gcongr
      _ = 1 / (2 * π ^ 2) * (2 ^ 12 * 35 * Bsum) * (X ^ (12 : ℝ) * X ^ (1 / 8 : ℝ) * X ^ (1 / 16 : ℝ)) := by
          rw [mul_pow, show X ^ 12 = X ^ (12 : ℝ) by norm_cast]; ring
      _ = g X * X ^ (25 / 2 : ℝ) := by
          have e1 : X ^ (12 : ℝ) * X ^ (1 / 8 : ℝ) * X ^ (1 / 16 : ℝ) =
              X ^ (-(5 / 16) : ℝ) * X ^ (25 / 2 : ℝ) := by
            rw [← Real.rpow_add hX0, ← Real.rpow_add hX0, ← Real.rpow_add hX0]; norm_num
          rw [e1]; simp only [g]; ring
  have hd : Tendsto (fun X => (∫ x in X..2 * X, Vth ⌊X ^ (1 / 4 : ℝ)⌋₊ x ^ 2) / X ^ (25 / 2 : ℝ) - m X)
      atTop (𝓝 0) := squeeze_zero_norm' hle hg
  simpa using hd.add hm

lemma tendsto_d :
    Tendsto (fun X : ℝ => (∫ x in Ioc X (2 * X), (Sre x - Vth ⌊X ^ (1 / 4 : ℝ)⌋₊ x) ^ 2) / X ^ (25 / 2 : ℝ))
      atTop (𝓝 0) := by
  have h := voronoi_L2 (θ := 1 / 4) (by norm_num) le_rfl
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with X hX
  rw [intervalIntegral.integral_of_le (by linarith)]

lemma tendsto_s :
    Tendsto (fun X : ℝ => (∫ x in Ioc X (2 * X), Sre x ^ 2) / X ^ (25 / 2 : ℝ)) atTop (𝓝 kap) := by
  have hv : Tendsto (fun X : ℝ => (∫ x in Ioc X (2 * X), Vth ⌊X ^ (1 / 4 : ℝ)⌋₊ x ^ 2) / X ^ (25 / 2 : ℝ))
      atTop (𝓝 kap) := by
    refine tendsto_v.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with X hX
    rw [intervalIntegral.integral_of_le (by linarith)]
  have hd := tendsto_d
  set v := fun X : ℝ => (∫ x in Ioc X (2 * X), Vth ⌊X ^ (1 / 4 : ℝ)⌋₊ x ^ 2) / X ^ (25 / 2 : ℝ)
  set d := fun X : ℝ => (∫ x in Ioc X (2 * X), (Sre x - Vth ⌊X ^ (1 / 4 : ℝ)⌋₊ x) ^ 2) / X ^ (25 / 2 : ℝ)
  set sf := fun X : ℝ => (∫ x in Ioc X (2 * X), Sre x ^ 2) / X ^ (25 / 2 : ℝ)
  have hbound : ∀ ε > 0, ∀ᶠ X in atTop, |sf X - v X| ≤ ε * v X + (1 + 1 / ε) * d X := by
    intro ε hε
    filter_upwards [eventually_gt_atTop 0] with X hX
    have hXp : 0 < X ^ (25 / 2 : ℝ) := by positivity
    have h := abs_integral_S_sq_sub_le ⌊X ^ (1 / 4 : ℝ)⌋₊ (a := X) (b := 2 * X) hε
    simp only [sf, v, d]
    rw [← sub_div, abs_div, abs_of_pos hXp, div_le_iff₀ hXp]
    calc _ ≤ _ := h
      _ = _ := by field_simp
  have hdiff : Tendsto (fun X => |sf X - v X|) atTop (𝓝 0) := by
    rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun X => lt_of_lt_of_le ha (abs_nonneg _), fun a ha => ?_⟩
    set ε := a / (2 * (|kap| + 1)) with hεdef
    have hε : 0 < ε := by positivity
    have hlim : Tendsto (fun X => ε * v X + (1 + 1 / ε) * d X) atTop (𝓝 (ε * kap + (1 + 1 / ε) * 0)) :=
      (hv.const_mul ε).add (hd.const_mul _)
    have hlt : ε * kap + (1 + 1 / ε) * 0 < a := by
      rw [mul_zero, add_zero]
      calc ε * kap ≤ ε * |kap| := mul_le_mul_of_nonneg_left (le_abs_self _) hε.le
        _ < ε * (2 * (|kap| + 1)) := by
            apply mul_lt_mul_of_pos_left _ hε; linarith [abs_nonneg kap]
        _ = a := by rw [hεdef]; field_simp
    filter_upwards [(tendsto_order.1 hlim).2 a hlt, hbound ε hε] with X h1 h2
    exact lt_of_le_of_lt h2 h1
  have h2 : Tendsto (fun X => sf X - v X) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]; simpa [Real.norm_eq_abs] using hdiff
  have := h2.add hv
  simpa using this


/-! ### From dyadic blocks to `∫₁^X` -/

lemma intervalIntegrable_Sre_sq (a b : ℝ) : IntervalIntegrable (fun x => Sre x ^ 2) volume a b := by
  rcases le_total a b with h | h
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h).2 (integrableOn_Sre_sq a b)
  · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le h).2 (integrableOn_Sre_sq b a)).symm

/-- `I(X) = ∫₁^X S²`. -/
noncomputable def Iq (X : ℝ) : ℝ := ∫ x in (1 : ℝ)..X, Sre x ^ 2

lemma Iq_block {Y : ℝ} (hY : 0 ≤ Y) : Iq (2 * Y) - Iq Y = ∫ x in Ioc Y (2 * Y), Sre x ^ 2 := by
  unfold Iq
  rw [intervalIntegral.integral_interval_sub_left (intervalIntegrable_Sre_sq _ _)
    (intervalIntegrable_Sre_sq _ _), intervalIntegral.integral_of_le (by linarith)]

lemma Iq_nonneg {Y : ℝ} (hY : 1 ≤ Y) : 0 ≤ Iq Y :=
  intervalIntegral.integral_nonneg hY fun _ _ => sq_nonneg _

lemma Iq_mono {Y Z : ℝ} (hY : 1 ≤ Y) (hYZ : Y ≤ Z) : Iq Y ≤ Iq Z :=
  intervalIntegral.integral_mono_interval le_rfl hY hYZ (Eventually.of_forall fun _ => sq_nonneg _)
    (intervalIntegrable_Sre_sq _ _)

lemma two_rpow_p : (2 : ℝ) ≤ 2 ^ (25 / 2 : ℝ) := by
  calc (2 : ℝ) = 2 ^ (1 : ℝ) := by norm_num
    _ ≤ 2 ^ (25 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

/-- **Dyadic summation**: if `(I(2Y) − I(Y))/Y^p → κ` then `I(X)/X^p → κ/(2^p − 1)`. -/
theorem tendsto_Iq :
    Tendsto (fun X => Iq X / X ^ (25 / 2 : ℝ)) atTop (𝓝 (kap / (2 ^ (25 / 2 : ℝ) - 1))) := by
  set p : ℝ := 25 / 2 with hp
  have hq : 1 ≤ (2 : ℝ) ^ p - 1 := by linarith [two_rpow_p]
  set c := kap / (2 ^ p - 1) with hcdef
  have hB0 : 0 ≤ Bsum := tsum_nonneg fun _ => sq_nonneg _
  have hkap0 : 0 ≤ kap := by
    unfold kap; have := two_rpow_p; have : 0 ≤ (2 : ℝ) ^ (25 / 2 : ℝ) - 1 := by linarith
    positivity
  have hc0 : 0 ≤ c := div_nonneg hkap0 (by linarith)
  have hkapc : kap = c * (2 ^ p - 1) := by rw [hcdef]; field_simp
  have hs := tendsto_s
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set ε := δ / 3 with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨Y1, hY1⟩ := Metric.tendsto_atTop.1 hs ε hε0
  set Y0 := max Y1 1
  have hY01 : 1 ≤ Y0 := le_max_right _ _
  have hY00 : 0 < Y0 := by linarith
  -- dyadic estimate
  have hdy : ∀ Z, Y0 ≤ Z → |Iq (2 * Z) - Iq Z - kap * Z ^ p| ≤ ε * Z ^ p := by
    intro Z hZ
    have hZ0 : 0 < Z := by linarith
    have hZp : 0 < Z ^ p := by positivity
    have h := hY1 Z (le_trans (le_max_left _ _) hZ)
    rw [Real.dist_eq, ← Iq_block hZ0.le] at h
    have : |Iq (2 * Z) - Iq Z - kap * Z ^ p| = |(Iq (2 * Z) - Iq Z) / Z ^ p - kap| * Z ^ p := by
      rw [← abs_of_pos hZp, ← abs_mul, abs_of_pos hZp]; congr 1; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right h.le hZp.le
  set K0 := Iq (2 * Y0) + c * (2 * Y0) ^ p
  have hclaim : ∀ n : ℕ, ∀ Y, Y0 ≤ Y → Y ≤ 2 ^ n * Y0 → |Iq Y - c * Y ^ p| ≤ K0 + ε * Y ^ p := by
    intro n
    induction n with
    | zero =>
      intro Y hY1' hY2
      have hY : Y = Y0 := le_antisymm (by simpa using hY2) hY1'
      subst hY
      have h1 := Iq_nonneg hY01
      have h2 : Iq Y0 ≤ Iq (2 * Y0) := Iq_mono hY01 (by linarith)
      have h3 : c * Y0 ^ p ≤ c * (2 * Y0) ^ p :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hY00.le (by linarith) (by norm_num)) hc0
      have h4 : 0 ≤ c * Y0 ^ p := by positivity
      have h5 : 0 ≤ ε * Y0 ^ p := by positivity
      rw [abs_le]; constructor <;> linarith
    | succ n ih =>
      intro Y hY1' hY2
      have hY0' : 0 < Y := by linarith
      by_cases hsmall : Y ≤ 2 * Y0
      · have h1 := Iq_nonneg (le_trans hY01 hY1')
        have h2 : Iq Y ≤ Iq (2 * Y0) := Iq_mono (le_trans hY01 hY1') hsmall
        have h3 : c * Y ^ p ≤ c * (2 * Y0) ^ p :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hY0'.le hsmall (by norm_num)) hc0
        have h4 : 0 ≤ c * Y ^ p := by positivity
        have h5 : 0 ≤ ε * Y ^ p := by positivity
        rw [abs_le]; constructor <;> linarith
      · push Not at hsmall
        set Z := Y / 2 with hZ
        have hZ1 : Y0 ≤ Z := by rw [hZ]; linarith
        have hZ2 : Z ≤ 2 ^ n * Y0 := by
          rw [hZ, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
          calc Y ≤ 2 ^ (n + 1) * Y0 := hY2
            _ = 2 ^ n * Y0 * 2 := by rw [pow_succ]; ring
        have hih := ih Z hZ1 hZ2
        have hd := hdy Z hZ1
        have h2Z : 2 * Z = Y := by rw [hZ]; ring
        rw [h2Z] at hd
        have hZ0 : 0 ≤ Z := by linarith
        have hYp : Y ^ p = 2 ^ p * Z ^ p := by
          rw [← h2Z, Real.mul_rpow (by norm_num) hZ0]
        have hZp : 0 ≤ Z ^ p := by positivity
        have e : Iq Y - c * Y ^ p = (Iq Z - c * Z ^ p) + (Iq Y - Iq Z - kap * Z ^ p) := by
          rw [hYp, hkapc]; ring
        rw [e]
        have h2p := two_rpow_p
        calc |(Iq Z - c * Z ^ p) + (Iq Y - Iq Z - kap * Z ^ p)|
            ≤ |Iq Z - c * Z ^ p| + |Iq Y - Iq Z - kap * Z ^ p| := abs_add_le _ _
          _ ≤ (K0 + ε * Z ^ p) + ε * Z ^ p := add_le_add hih hd
          _ ≤ K0 + ε * Y ^ p := by
              rw [hYp]
              have : 2 * (ε * Z ^ p) ≤ ε * (2 ^ p * Z ^ p) := by
                have := mul_le_mul_of_nonneg_right h2p (mul_nonneg hε0.le hZp)
                nlinarith
              linarith
  have hK0 : 0 ≤ K0 := by have := Iq_nonneg (show (1 : ℝ) ≤ 2 * Y0 by linarith); positivity
  refine ⟨max Y0 (K0 / ε + 1), fun X hX => ?_⟩
  have hXY : Y0 ≤ X := le_trans (le_max_left _ _) hX
  have hXK : K0 / ε + 1 ≤ X := le_trans (le_max_right _ _) hX
  have hX1 : 1 ≤ X := le_trans hY01 hXY
  have hX0 : 0 < X := by linarith
  have hXp : 0 < X ^ p := by positivity
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (X / Y0) (by norm_num : (1 : ℝ) < 2)
  have hXn : X ≤ 2 ^ n * Y0 := by
    have := (div_lt_iff₀ hY00).1 hn; linarith
  have hb := hclaim n X hXY hXn
  rw [Real.dist_eq]
  have e : Iq X / X ^ p - c = (Iq X - c * X ^ p) / X ^ p := by field_simp
  rw [e, abs_div, abs_of_pos hXp, div_lt_iff₀ hXp]
  have hXpX : X ≤ X ^ p := by
    calc X = X ^ (1 : ℝ) := (Real.rpow_one X).symm
      _ ≤ X ^ p := Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hK : K0 < ε * X ^ p := by
    have : K0 < ε * X := by
      have := (div_lt_iff₀ hε0).1 (by linarith : K0 / ε < X)
      linarith
    nlinarith
  calc |Iq X - c * X ^ p| ≤ K0 + ε * X ^ p := hb
    _ < ε * X ^ p + ε * X ^ p := by linarith
    _ < δ * X ^ p := by rw [hε]; nlinarith

lemma kap_div : kap / (2 ^ (25 / 2 : ℝ) - 1) = Bsum / (50 * π ^ 2) := by
  have h : (2 : ℝ) ^ (25 / 2 : ℝ) - 1 ≠ 0 := by linarith [two_rpow_p]
  unfold kap; field_simp; ring

/-- **The Cramér–Tong theorem for `τ`** (internal form). -/
theorem tau_cramer_core :
    Tendsto (fun X => Iq X / X ^ (25 / 2 : ℝ)) atTop (𝓝 (Bsum / (50 * π ^ 2))) := by
  rw [← kap_div]; exact tendsto_Iq

end RamanujanTau.VoronoiTrunc
