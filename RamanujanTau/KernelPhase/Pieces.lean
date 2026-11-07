/-
# The contour pieces: integral bounds

Each of the ten pieces of the bent contour for `∫ G(1/2+it) dt` is `≪ Y⁹ = y^{9/8}`.
Helpers: Cauchy on a rectangle in difference form (`rect_diff`), an even-integrand identity,
and two elementary power integrals.
-/
import RamanujanTau.KernelPhase.Bounds

set_option autoImplicit false

namespace RamanujanTau.KernelPhase

open Complex Real MeasureTheory Set Filter
open scoped Interval
open RamanujanTau.RankinErrorGeneral RamanujanTau.RankinLandau

/-! ### Helpers -/

/-- Cauchy on a rectangle: the two vertical sides differ by at most the two horizontal ones. -/
lemma rect_diff (f : ℂ → ℂ) (x₁ x₂ y₁ y₂ : ℝ)
    (H : DifferentiableOn ℂ f ([[x₁, x₂]] ×ℂ [[y₁, y₂]])) :
    ‖(∫ y in y₁..y₂, f (x₂ + y * I)) - ∫ y in y₁..y₂, f (x₁ + y * I)‖ ≤
      ‖∫ x in x₁..x₂, f (x + y₁ * I)‖ + ‖∫ x in x₁..x₂, f (x + y₂ * I)‖ := by
  have h : (∫ x : ℝ in x₁..x₂, f (x + y₁ * I)) - (∫ x : ℝ in x₁..x₂, f (x + y₂ * I)) +
      I • (∫ y : ℝ in y₁..y₂, f (x₂ + y * I)) - I • (∫ y : ℝ in y₁..y₂, f (x₁ + y * I)) = 0 :=
    integral_boundary_rect_eq_zero_of_differentiableOn f ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ H
  simp only [smul_eq_mul] at h
  set H1 := ∫ x : ℝ in x₁..x₂, f (x + y₁ * I)
  set H2 := ∫ x : ℝ in x₁..x₂, f (x + y₂ * I)
  set V1 := ∫ y : ℝ in y₁..y₂, f (x₁ + y * I)
  set V2 := ∫ y : ℝ in y₁..y₂, f (x₂ + y * I)
  have e : V2 - V1 = -I * (H2 - H1) := by
    linear_combination (-I) * h + (V2 - V1) * Complex.I_sq
  rw [e, norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact (norm_sub_le _ _).trans (le_of_eq (add_comm _ _))

lemma integral_symm_abs {g : ℝ → ℝ} (hg : Continuous g) {a : ℝ} (ha : 0 ≤ a) :
    ∫ t in -a..a, g |t| = 2 * ∫ t in (0 : ℝ)..a, g t := by
  have hc : Continuous fun t => g |t| := hg.comp continuous_abs
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h1 : ∫ t in (0 : ℝ)..a, g |t| = ∫ t in (0 : ℝ)..a, g t := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le ha] at ht
    simp only [abs_of_nonneg ht.1]
  have h2 : ∫ t in -a..0, g |t| = ∫ t in (0 : ℝ)..a, g |t| := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := a) (fun t => g |t|)
    simp only [abs_neg, neg_zero] at this
    exact this.symm
  rw [h2, h1]; ring

lemma integral_shift_pow_le {τ c : ℝ} (hτ : 0 < τ) (hc : 0 ≤ c) (N : ℕ)
    (hN : (N : ℝ) + 1 ≤ τ) :
    ∫ u in (0 : ℝ)..τ, ((u + c) / τ) ^ N ≤ τ * Real.exp c / ((N : ℝ) + 1) := by
  have e : ∫ u in (0 : ℝ)..τ, ((u + c) / τ) ^ N =
      ((τ + c) ^ (N + 1) - c ^ (N + 1)) / ((N : ℝ) + 1) / τ ^ N := by
    simp_rw [div_pow]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_add_right (fun x => x ^ N) c,
      integral_pow]
    simp
  rw [e]
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h1 : ((τ + c) ^ (N + 1) - c ^ (N + 1)) / ((N : ℝ) + 1) / τ ^ N ≤
      (τ + c) ^ (N + 1) / ((N : ℝ) + 1) / τ ^ N := by
    gcongr; linarith [pow_nonneg hc (N + 1)]
  refine h1.trans ?_
  have h2 : (τ + c) ^ (N + 1) = τ ^ N * τ * (1 + c / τ) ^ (N + 1) := by
    have : τ * (1 + c / τ) = τ + c := by field_simp
    rw [← this, mul_pow, pow_succ]
  have h3 : (1 + c / τ) ^ (N + 1) ≤ Real.exp c := by
    have hx : 0 ≤ c / τ := by positivity
    calc (1 + c / τ) ^ (N + 1) ≤ (Real.exp (c / τ)) ^ (N + 1) := by
          gcongr; linarith [Real.add_one_le_exp (c / τ)]
      _ = Real.exp (((N + 1 : ℕ) : ℝ) * (c / τ)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp c := by
          refine Real.exp_le_exp.2 ?_
          rw [mul_div_assoc', div_le_iff₀ hτ]; push_cast; nlinarith
  rw [h2]
  have hτN : 0 < τ ^ N := by positivity
  calc τ ^ N * τ * (1 + c / τ) ^ (N + 1) / ((N : ℝ) + 1) / τ ^ N =
      τ * (1 + c / τ) ^ (N + 1) / ((N : ℝ) + 1) := by field_simp
    _ ≤ τ * Real.exp c / ((N : ℝ) + 1) := by gcongr

lemma integral_rpow_tail_le {τ U p : ℝ} (hτ : 0 < τ) (hU : τ ≤ U) (hp : 1 < p) :
    ∫ t in τ..U, τ ^ p * t ^ (-p) ≤ τ / (p - 1) := by
  have h0 : (0 : ℝ) ∉ [[τ, U]] := by
    rw [uIcc_of_le hU]; intro h; linarith [h.1]
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, h0⟩)]
  have hU0 : 0 ≤ U ^ (-p + 1) := Real.rpow_nonneg (by linarith) _
  have e : τ ^ p * τ ^ (-p + 1) = τ := by
    rw [← Real.rpow_add hτ]; simp
  have hp1 : 0 < p - 1 := by linarith
  have e2 : (U ^ (-p + 1) - τ ^ (-p + 1)) / (-p + 1) = (τ ^ (-p + 1) - U ^ (-p + 1)) / (p - 1) := by
    rw [show -p + 1 = -(p - 1) by ring, div_neg, ← neg_div, neg_sub]
  rw [e2]
  calc τ ^ p * ((τ ^ (-p + 1) - U ^ (-p + 1)) / (p - 1)) ≤ τ ^ p * (τ ^ (-p + 1) / (p - 1)) := by
        gcongr; linarith
    _ = τ / (p - 1) := by rw [mul_div_assoc', e]

/-! ### Parameters -/

variable {m : ℕ} {K Y : ℝ}

lemma params (hm : 1 ≤ m) (hY : 9 + (m : ℝ) ^ 2 ≤ Y) :
    1 ≤ Y ∧ 2 ≤ Y ∧ Y ≤ (⌈Y⌉₊ : ℝ) ∧ (⌈Y⌉₊ : ℝ) ≤ Y + 1 ∧ 0 < 2 * π * Y ^ 2 ∧
      2 * π * Y ^ 2 ≤ Y ^ 8 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hY2 : 2 ≤ Y := by nlinarith
  have hpi := Real.pi_lt_d2
  refine ⟨by linarith, hY2, Nat.le_ceil _, (Nat.ceil_lt_add_one (by linarith)).le, by positivity, ?_⟩
  have h6 : (2 : ℝ) ^ 6 ≤ Y ^ 6 := pow_le_pow_left₀ (by norm_num) hY2 6
  have : 2 * π ≤ Y ^ 6 := by nlinarith
  calc 2 * π * Y ^ 2 ≤ Y ^ 6 * Y ^ 2 := by gcongr
    _ = Y ^ 8 := by ring

/-! ### The tail `|t| ≥ U = Y⁸` of the original line -/

lemma piece_tail (hm : 1 ≤ m) (hSB : StripBound m K) (hY : 9 + (m : ℝ) ^ 2 ≤ Y) :
    ‖(∫ t : ℝ, G m (Y ^ 8) (((1 / 2 : ℝ) : ℂ) + t * I)) -
        ∫ t in -(Y ^ 8)..(Y ^ 8), G m (Y ^ 8) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      K * Y ^ 8 * ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ) := by
  obtain ⟨hY1, -, -, -, -, -⟩ := params hm hY
  have hY0 : 0 < Y := by linarith
  set U : ℝ := Y ^ 8 with hU
  have hU1 : 1 ≤ U := one_le_pow₀ hY1
  set F : ℝ → ℂ := fun t => G m (Y ^ 8) (((1 / 2 : ℝ) : ℂ) + t * I) with hF
  have hFi : Integrable F := integrable_jint m 1 hm (σ := 1 / 2) (by norm_num) (by norm_num)
    (y := Y ^ 8) (by positivity)
  have hb : Integrable fun t : ℝ => (1 + |t|) ^ (-(3 / 2) : ℝ) :=
    integrable_rpow_line (p := 3 / 2) (by norm_num) 1 |>.congr
      (Eventually.of_forall fun t => by simp)
  set s : Set ℝ := Ioc (-U) U
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_add_compl measurableSet_Ioc hFi,
    add_sub_cancel_left]
  have hpt : ∀ t ∈ sᶜ, ‖F t‖ ≤ K * Y ^ 8 * (1 + |t|) ^ (-(3 / 2) : ℝ) := by
    intro t ht
    have hUt : U ≤ |t| := by
      simp only [s, mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have h1 := bound_half hSB hY1 t
    have ht0 : 0 < 1 + |t| := by positivity
    have e : (1 + |t|) ^ (-2 : ℝ) = (1 + |t|) ^ (-(3 / 2) : ℝ) * (1 + |t|) ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_add ht0]; norm_num
    have h2 : (1 + |t|) ^ (-(1 / 2) : ℝ) ≤ (Y ^ 4)⁻¹ := by
      refine (Real.rpow_le_rpow_of_nonpos (by linarith) (show U ≤ 1 + |t| by linarith)
        (by norm_num)).trans (le_of_eq ?_)
      rw [hU, rpow8 hY0.le, show 8 * (-(1 / 2) : ℝ) = -((4 : ℕ) : ℝ) by norm_num,
        Real.rpow_neg hY0.le, Real.rpow_natCast]
    calc ‖F t‖ ≤ K * Y ^ 12 * (1 + |t|) ^ (-2 : ℝ) := h1
      _ = K * Y ^ 12 * (1 + |t|) ^ (-(1 / 2) : ℝ) * (1 + |t|) ^ (-(3 / 2) : ℝ) := by rw [e]; ring
      _ ≤ K * Y ^ 12 * (Y ^ 4)⁻¹ * (1 + |t|) ^ (-(3 / 2) : ℝ) := by
          have := hSB.1; gcongr
      _ = K * Y ^ 8 * (1 + |t|) ^ (-(3 / 2) : ℝ) := by field_simp
  have hK8 : 0 ≤ K * Y ^ 8 := by have := hSB.1; positivity
  calc ‖∫ t in sᶜ, F t‖ ≤ ∫ t in sᶜ, K * Y ^ 8 * (1 + |t|) ^ (-(3 / 2) : ℝ) := by
        refine norm_integral_le_of_norm_le ((hb.const_mul _).integrableOn) ?_
        exact (ae_restrict_iff' measurableSet_Ioc.compl).2 (Eventually.of_forall hpt)
    _ ≤ ∫ t : ℝ, K * Y ^ 8 * (1 + |t|) ^ (-(3 / 2) : ℝ) :=
        setIntegral_le_integral (hb.const_mul _) (Eventually.of_forall fun t => by positivity)
    _ = K * Y ^ 8 * ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ) := integral_const_mul _ _

/-! ### The left vertical line -/

lemma piece_left (hm : 1 ≤ m) (hSB : StripBound m K) (hY : 9 + (m : ℝ) ^ 2 ≤ Y) :
    ‖∫ t in -(2 * π * Y ^ 2)..(2 * π * Y ^ 2),
        G m (Y ^ 8) (((1 / 2 - (⌈Y⌉₊ : ℕ) : ℝ) : ℂ) + t * I)‖ ≤
      K * (Real.exp ((9 + (m : ℝ) ^ 2) / (2 * π)) + 480 * π) * Y ^ 9 := by
  obtain ⟨hY1, hY2, hYn, hnY, hτ0, -⟩ := params hm hY
  have hY0 : 0 < Y := by linarith
  have hK := hSB.1
  have hpi := Real.pi_gt_three
  set n : ℕ := ⌈Y⌉₊ with hn
  set τ : ℝ := 2 * π * Y ^ 2 with hτ
  set c₁ : ℝ := (9 + (m : ℝ) ^ 2) / (2 * π) with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  set h : ℝ → ℝ := fun u => 4 / τ ^ 2 * ((u + c₁) / τ) ^ (2 * n) + Real.exp (-Y) with hh
  have hhc : Continuous h := by rw [hh]; fun_prop
  have hpt : ∀ t, |t| ≤ τ → ‖G m (Y ^ 8) (((1 / 2 - n : ℝ) : ℂ) + t * I)‖ ≤ K * Y ^ 12 * h |t| := by
    intro t ht
    have h1 := bound_left_line hm hSB hY1 t n
    have h2 := left_pointwise hm hY1 hY ht
    calc _ ≤ _ := h1
      _ = K * Y ^ 12 * ((1 + |t|) ^ (-2 : ℝ) *
          ((((n : ℝ) + 1) ^ 2 + (m : ℝ) ^ 2 + t ^ 2) ^ 2 / (16 * π ^ 4 * Y ^ 8)) ^ n) := by ring
      _ ≤ K * Y ^ 12 * h |t| := by gcongr
  have hI : ‖∫ t in -τ..τ, G m (Y ^ 8) (((1 / 2 - n : ℝ) : ℂ) + t * I)‖ ≤
      ∫ t in -τ..τ, K * Y ^ 12 * h |t| := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Eventually.of_forall fun t ht => hpt t ?_)
      ((continuous_const.mul (hhc.comp continuous_abs)).intervalIntegrable _ _)
    rw [abs_le]; exact ⟨ht.1.le, ht.2⟩
  refine hI.trans ?_
  rw [intervalIntegral.integral_const_mul,
    integral_symm_abs (g := h) hhc hτ0.le]
  have hN : ((2 * n : ℕ) : ℝ) + 1 ≤ τ := by
    push_cast
    have : 2 * (n : ℝ) + 1 ≤ 5 * Y := by linarith
    have : 5 * Y ≤ τ := by rw [hτ]; nlinarith
    linarith
  have hint : ∫ u in (0 : ℝ)..τ, h u ≤
      4 / τ ^ 2 * (τ * Real.exp c₁ / (((2 * n : ℕ) : ℝ) + 1)) + τ * Real.exp (-Y) := by
    rw [hh]
    rw [intervalIntegral.integral_add (by
        exact (Continuous.intervalIntegrable (by fun_prop) _ _))
      (intervalIntegrable_const), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    gcongr
    exact integral_shift_pow_le hτ0 hc₁0 (2 * n) hN
  -- final arithmetic
  have hn2 : 2 * Y ≤ ((2 * n : ℕ) : ℝ) + 1 := by push_cast; linarith
  have hexpY : Y ^ 5 ≤ 120 * Real.exp Y := by
    have := Real.pow_div_factorial_le_exp Y hY0.le 5
    norm_num [Nat.factorial] at this
    linarith
  have hA : 4 / τ ^ 2 * (τ * Real.exp c₁ / (((2 * n : ℕ) : ℝ) + 1)) * Y ^ 3 ≤ Real.exp c₁ / 2 := by
    have hτY : 8 * Y ^ 3 ≤ τ * (((2 * n : ℕ) : ℝ) + 1) := by
      have h1 : τ * (2 * Y) ≤ τ * (((2 * n : ℕ) : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hn2 hτ0.le
      have h2 : 8 * Y ^ 3 ≤ τ * (2 * Y) := by
        rw [hτ]; have : 0 ≤ Y ^ 3 := by positivity
        nlinarith
      linarith
    have e : 4 / τ ^ 2 * (τ * Real.exp c₁ / (((2 * n : ℕ) : ℝ) + 1)) =
        4 * Real.exp c₁ / (τ * (((2 * n : ℕ) : ℝ) + 1)) := by
      field_simp
    rw [e, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have hec := Real.exp_pos c₁
    calc 4 * Real.exp c₁ * Y ^ 3 * 2 = Real.exp c₁ * (8 * Y ^ 3) := by ring
      _ ≤ Real.exp c₁ * (τ * (((2 * n : ℕ) : ℝ) + 1)) := mul_le_mul_of_nonneg_left hτY hec.le
  have hB : τ * Real.exp (-Y) * Y ^ 3 ≤ 240 * π := by
    rw [hτ, Real.exp_neg]
    have hey := Real.exp_pos Y
    rw [show 2 * π * Y ^ 2 * (Real.exp Y)⁻¹ * Y ^ 3 = 2 * π * Y ^ 5 / Real.exp Y by
      field_simp, div_le_iff₀ hey]
    have hp0 := Real.pi_pos
    calc 2 * π * Y ^ 5 ≤ 2 * π * (120 * Real.exp Y) := by gcongr
      _ = 240 * π * Real.exp Y := by ring
  have hY3 : 0 < Y ^ 3 := by positivity
  set A := 4 / τ ^ 2 * (τ * Real.exp c₁ / (((2 * n : ℕ) : ℝ) + 1))
  set B := τ * Real.exp (-Y)
  calc K * Y ^ 12 * (2 * ∫ u in (0 : ℝ)..τ, h u) ≤ K * Y ^ 12 * (2 * (A + B)) := by
        gcongr
    _ = 2 * K * Y ^ 9 * (A * Y ^ 3 + B * Y ^ 3) := by ring
    _ ≤ 2 * K * Y ^ 9 * (Real.exp c₁ / 2 + 240 * π) := by gcongr
    _ = K * (Real.exp c₁ + 480 * π) * Y ^ 9 := by ring

/-! ### The right vertical line -/

lemma right_pointwise (hSB : StripBound m K) (hY1 : 1 ≤ Y) {t : ℝ}
    (ht : 2 * π * Y ^ 2 ≤ |t|) (n : ℕ) :
    ‖G m (Y ^ 8) (((1 / 2 + n : ℝ) : ℂ) + t * I)‖ ≤
      K * Y ^ 12 * ((2 * π * Y ^ 2) ^ 2)⁻¹ *
        ((2 * π * Y ^ 2) ^ ((4 * n : ℕ) : ℝ) * |t| ^ (-((4 * n : ℕ) : ℝ))) := by
  set τ : ℝ := 2 * π * Y ^ 2 with hτ
  have hτ0 : 0 < τ := by have := Real.pi_pos; positivity
  have ht0 : 0 < |t| := by linarith
  have ht0' : t ≠ 0 := abs_pos.1 ht0
  have h1 := bound_right_line hSB hY1 ht0' n
  have e1 : (16 * π ^ 4 * Y ^ 8 / t ^ 4) ^ n = τ ^ ((4 * n : ℕ) : ℝ) * |t| ^ (-((4 * n : ℕ) : ℝ)) := by
    rw [Real.rpow_neg ht0.le, Real.rpow_natCast, Real.rpow_natCast, show t ^ 4 = |t| ^ 4 by
      rw [show |t| ^ 4 = (|t| ^ 2) ^ 2 by ring, sq_abs]; ring, show (16 * π ^ 4 * Y ^ 8 : ℝ) = τ ^ 4 by
      rw [hτ]; ring, div_pow, ← pow_mul, ← pow_mul, div_eq_mul_inv]
  have e2 : (1 + |t|) ^ (-2 : ℝ) ≤ (τ ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
      Real.rpow_natCast]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hτ0.le (by linarith) 2)
  rw [e1] at h1
  refine h1.trans ?_
  have := hSB.1
  gcongr

lemma piece_right_top (hm : 1 ≤ m) (hSB : StripBound m K) (hY : 9 + (m : ℝ) ^ 2 ≤ Y) :
    ‖∫ t in (2 * π * Y ^ 2)..(Y ^ 8), G m (Y ^ 8) (((1 / 2 + (⌈Y⌉₊ : ℕ) : ℝ) : ℂ) + t * I)‖ ≤
      K * Y ^ 9 := by
  obtain ⟨hY1, hY2, hYn, hnY, hτ0, hτU⟩ := params hm hY
  have hY0 : 0 < Y := by linarith
  have hK := hSB.1
  set n : ℕ := ⌈Y⌉₊ with hn
  set τ : ℝ := 2 * π * Y ^ 2 with hτ
  set p : ℝ := ((4 * n : ℕ) : ℝ) with hp
  have hp1 : 1 < p := by rw [hp]; push_cast; linarith
  have hI : ‖∫ t in τ..(Y ^ 8), G m (Y ^ 8) (((1 / 2 + n : ℝ) : ℂ) + t * I)‖ ≤
      ∫ t in τ..(Y ^ 8), K * Y ^ 12 * (τ ^ 2)⁻¹ * (τ ^ p * t ^ (-p)) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hτU
      (Eventually.of_forall fun t ht => ?_) ?_
    · have h := right_pointwise hSB hY1 (t := t) (by rw [abs_of_pos (by linarith [ht.1])]; exact ht.1.le) n
      rwa [abs_of_pos (by linarith [ht.1])] at h
    · refine ((intervalIntegral.intervalIntegrable_rpow (Or.inr ?_)).const_mul (τ ^ p)).const_mul _
      rw [uIcc_of_le hτU]; intro h; linarith [h.1]
  refine hI.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have h2 := integral_rpow_tail_le hτ0 hτU hp1
  calc K * Y ^ 12 * (τ ^ 2)⁻¹ * ∫ t in τ..(Y ^ 8), τ ^ p * t ^ (-p) ≤
      K * Y ^ 12 * (τ ^ 2)⁻¹ * (τ / (p - 1)) := by gcongr
    _ ≤ K * Y ^ 9 := by
        have hpY : 3 * Y ≤ p - 1 := by rw [hp]; push_cast; linarith
        have e : K * Y ^ 12 * (τ ^ 2)⁻¹ * (τ / (p - 1)) = K * Y ^ 9 * (Y ^ 3 / (τ * (p - 1))) := by
          field_simp
        rw [e]
        have hpi := Real.pi_gt_three
        have : Y ^ 3 / (τ * (p - 1)) ≤ 1 := by
          rw [div_le_one (mul_pos hτ0 (by linarith))]
          calc Y ^ 3 = 1 * Y ^ 2 * Y := by ring
            _ ≤ (2 * π) * Y ^ 2 * (3 * Y) := by gcongr <;> nlinarith
            _ ≤ τ * (p - 1) := by rw [hτ]; gcongr
        calc K * Y ^ 9 * (Y ^ 3 / (τ * (p - 1))) ≤ K * Y ^ 9 * 1 := by gcongr
          _ = K * Y ^ 9 := mul_one _

lemma piece_right_bot (hm : 1 ≤ m) (hSB : StripBound m K) (hY : 9 + (m : ℝ) ^ 2 ≤ Y) :
    ‖∫ t in -(Y ^ 8)..-(2 * π * Y ^ 2),
        G m (Y ^ 8) (((1 / 2 + (⌈Y⌉₊ : ℕ) : ℝ) : ℂ) + t * I)‖ ≤ K * Y ^ 9 := by
  obtain ⟨hY1, hY2, hYn, hnY, hτ0, hτU⟩ := params hm hY
  have hY0 : 0 < Y := by linarith
  have hK := hSB.1
  set n : ℕ := ⌈Y⌉₊ with hn
  set τ : ℝ := 2 * π * Y ^ 2 with hτ
  set p : ℝ := ((4 * n : ℕ) : ℝ) with hp
  have hp1 : 1 < p := by rw [hp]; push_cast; linarith
  rw [← intervalIntegral.integral_comp_neg
    (fun t : ℝ => G m (Y ^ 8) (((1 / 2 + n : ℝ) : ℂ) + t * I))]
  have hI : ‖∫ t in τ..(Y ^ 8), G m (Y ^ 8) (((1 / 2 + n : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ ≤
      ∫ t in τ..(Y ^ 8), K * Y ^ 12 * (τ ^ 2)⁻¹ * (τ ^ p * t ^ (-p)) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hτU
      (Eventually.of_forall fun t ht => ?_) ?_
    · have h := right_pointwise hSB hY1 (t := -t)
        (by rw [abs_neg, abs_of_pos (by linarith [ht.1])]; exact ht.1.le) n
      rwa [abs_neg, abs_of_pos (by linarith [ht.1])] at h
    · refine ((intervalIntegral.intervalIntegrable_rpow (Or.inr ?_)).const_mul (τ ^ p)).const_mul _
      rw [uIcc_of_le hτU]; intro h; linarith [h.1]
  have hI' : ‖∫ t in τ..(Y ^ 8), G m (Y ^ 8) (((1 / 2 + n : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ ≤
      K * Y ^ 9 := by
    refine hI.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have h2 := integral_rpow_tail_le hτ0 hτU hp1
    calc K * Y ^ 12 * (τ ^ 2)⁻¹ * ∫ t in τ..(Y ^ 8), τ ^ p * t ^ (-p) ≤
        K * Y ^ 12 * (τ ^ 2)⁻¹ * (τ / (p - 1)) := by gcongr
      _ ≤ K * Y ^ 9 := by
          have hpY : 3 * Y ≤ p - 1 := by rw [hp]; push_cast; linarith
          have e : K * Y ^ 12 * (τ ^ 2)⁻¹ * (τ / (p - 1)) =
              K * Y ^ 9 * (Y ^ 3 / (τ * (p - 1))) := by
            field_simp
          rw [e]
          have hpi := Real.pi_gt_three
          have : Y ^ 3 / (τ * (p - 1)) ≤ 1 := by
            rw [div_le_one (mul_pos hτ0 (by linarith))]
            calc Y ^ 3 = 1 * Y ^ 2 * Y := by ring
              _ ≤ (2 * π) * Y ^ 2 * (3 * Y) := by gcongr <;> nlinarith
              _ ≤ τ * (p - 1) := by rw [hτ]; gcongr
          calc K * Y ^ 9 * (Y ^ 3 / (τ * (p - 1))) ≤ K * Y ^ 9 * 1 := by gcongr
            _ = K * Y ^ 9 := mul_one _
  simpa using hI'

/-! ### The horizontal segments -/

lemma piece_h_left (hm : 1 ≤ m) (hSB : StripBound m K) (hY : 9 + (m : ℝ) ^ 2 ≤ Y) {t : ℝ}
    (ht : |t| = 2 * π * Y ^ 2) :
    ‖∫ x in (1 / 2 - (⌈Y⌉₊ : ℕ) : ℝ)..(1 / 2 : ℝ), G m (Y ^ 8) ((x : ℂ) + t * I)‖ ≤
      128 * K * Real.exp (9 + (m : ℝ) ^ 2) * Y ^ 9 := by
  obtain ⟨hY1, hY2, hYn, hnY, hτ0, hτU⟩ := params hm hY
  have hK := hSB.1
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 / 2 - (⌈Y⌉₊ : ℕ) : ℝ)) (b := 1 / 2)
    (f := fun x : ℝ => G m (Y ^ 8) ((x : ℂ) + t * I))
    (C := 64 * K * Y ^ 8 * Real.exp (9 + (m : ℝ) ^ 2)) (fun x hx => by
      rw [uIoc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) ⌈Y⌉₊])] at hx
      exact bound_tau_left hm hSB hY1 (by linarith [hx.1]) hx.2 ht)
  refine h.trans ?_
  rw [show (1 / 2 : ℝ) - (1 / 2 - (⌈Y⌉₊ : ℕ)) = (⌈Y⌉₊ : ℝ) by ring,
    abs_of_nonneg (Nat.cast_nonneg _)]
  have hE := Real.exp_pos (9 + (m : ℝ) ^ 2)
  calc 64 * K * Y ^ 8 * Real.exp (9 + (m : ℝ) ^ 2) * (⌈Y⌉₊ : ℝ) ≤
      64 * K * Y ^ 8 * Real.exp (9 + (m : ℝ) ^ 2) * (2 * Y) := by gcongr; linarith
    _ = 128 * K * Real.exp (9 + (m : ℝ) ^ 2) * Y ^ 9 := by ring

lemma piece_h_right (hm : 1 ≤ m) (hSB : StripBound m K) (hY : 9 + (m : ℝ) ^ 2 ≤ Y) {t : ℝ}
    (ht : |t| = 2 * π * Y ^ 2) :
    ‖∫ x in (1 / 2 : ℝ)..(1 / 2 + (⌈Y⌉₊ : ℕ) : ℝ), G m (Y ^ 8) ((x : ℂ) + t * I)‖ ≤
      128 * K * Y ^ 9 := by
  obtain ⟨hY1, hY2, hYn, hnY, hτ0, hτU⟩ := params hm hY
  have hK := hSB.1
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 1 / 2) (b := (1 / 2 + (⌈Y⌉₊ : ℕ) : ℝ))
    (f := fun x : ℝ => G m (Y ^ 8) ((x : ℂ) + t * I))
    (C := 64 * K * Y ^ 8) (fun x hx => by
      rw [uIoc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) ⌈Y⌉₊])] at hx
      exact bound_tau_right hSB hY1 hx.1.le ht)
  refine h.trans ?_
  rw [show (1 / 2 + (⌈Y⌉₊ : ℕ) : ℝ) - 1 / 2 = (⌈Y⌉₊ : ℝ) by ring,
    abs_of_nonneg (Nat.cast_nonneg _)]
  calc 64 * K * Y ^ 8 * (⌈Y⌉₊ : ℝ) ≤ 64 * K * Y ^ 8 * (2 * Y) := by gcongr; linarith
    _ = 128 * K * Y ^ 9 := by ring

lemma piece_h_top (hm : 1 ≤ m) (hSB : StripBound m K) (hY : 9 + (m : ℝ) ^ 2 ≤ Y) {t : ℝ}
    (ht : |t| = Y ^ 8) :
    ‖∫ x in (1 / 2 : ℝ)..(1 / 2 + (⌈Y⌉₊ : ℕ) : ℝ), G m (Y ^ 8) ((x : ℂ) + t * I)‖ ≤
      128 * π ^ 4 * K * Y ^ 9 := by
  obtain ⟨hY1, hY2, hYn, hnY, hτ0, hτU⟩ := params hm hY
  have hK := hSB.1
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 1 / 2) (b := (1 / 2 + (⌈Y⌉₊ : ℕ) : ℝ))
    (f := fun x : ℝ => G m (Y ^ 8) ((x : ℂ) + t * I))
    (C := 64 * π ^ 4 * K * Y ^ 4) (fun x hx => by
      rw [uIoc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) ⌈Y⌉₊])] at hx
      exact bound_U hSB hY2 hx.1 ht)
  refine h.trans ?_
  rw [show (1 / 2 + (⌈Y⌉₊ : ℕ) : ℝ) - 1 / 2 = (⌈Y⌉₊ : ℝ) by ring,
    abs_of_nonneg (Nat.cast_nonneg _)]
  have hY45 : Y ^ 5 ≤ Y ^ 9 := pow_le_pow_right₀ hY1 (by norm_num)
  have hpi4 : 0 ≤ π ^ 4 := by positivity
  calc 64 * π ^ 4 * K * Y ^ 4 * (⌈Y⌉₊ : ℝ) ≤ 64 * π ^ 4 * K * Y ^ 4 * (2 * Y) := by
        gcongr; linarith
    _ = 128 * π ^ 4 * K * Y ^ 5 := by ring
    _ ≤ 128 * π ^ 4 * K * Y ^ 9 := by gcongr

end RamanujanTau.KernelPhase
