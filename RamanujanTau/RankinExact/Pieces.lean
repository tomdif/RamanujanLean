/-
# The contour pieces for `J_{r+1}`: each is `≪ Y^{9+6r}`

Generalises `KernelPhase/Pieces.lean` (the case `r = 0`). Helpers (`rect_diff`,
`integral_symm_abs`, `integral_shift_pow_le`, `integral_rpow_tail_le`, `params`) are reused.
-/
import RamanujanTau.RankinExact.Bounds
import RamanujanTau.KernelPhase.Pieces

set_option autoImplicit false

namespace RamanujanTau.RankinExact

open Complex Real MeasureTheory Set Filter
open scoped Interval
open RamanujanTau.RankinErrorGeneral RamanujanTau.RankinLandau RamanujanTau.KernelPhase

variable {m r : ℕ} {K Y : ℝ}

lemma paramsJ (hm : 1 ≤ m) (hY : Dc m r ≤ Y) :
    1 ≤ Y ∧ 2 ≤ Y ∧ Y ≤ (⌈Y⌉₊ : ℝ) ∧ (⌈Y⌉₊ : ℝ) ≤ Y + 1 ∧ 0 < 2 * π * Y ^ 2 ∧
      2 * π * Y ^ 2 ≤ Y ^ 8 := by
  refine params hm (le_trans ?_ hY)
  unfold Dc; nlinarith [Nat.cast_nonneg (α := ℝ) r]

lemma tau_pow_ge (hY1 : 1 ≤ Y) (k : ℕ) : Y ^ (2 * k) ≤ (2 * π * Y ^ 2) ^ k := by
  rw [pow_mul]
  have hpi := Real.pi_gt_three
  exact pow_le_pow_left₀ (by positivity) (by nlinarith [sq_nonneg Y]) k

/-! ### The tail `|t| ≥ U = Y⁸` of the original line -/

lemma piece_tailJ (hm : 1 ≤ m) (hSB : StripBoundJ m r K) (hY : Dc m r ≤ Y) :
    ‖(∫ t : ℝ, Gj m (r + 1) (Y ^ 8) (((1 / 2 : ℝ) : ℂ) + t * I)) -
        ∫ t in -(Y ^ 8)..(Y ^ 8), Gj m (r + 1) (Y ^ 8) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      K * Y ^ 8 * ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ) := by
  obtain ⟨hY1, -, -, -, -, -⟩ := paramsJ hm hY
  have hY0 : 0 < Y := by linarith
  set U : ℝ := Y ^ 8 with hU
  have hU1 : 1 ≤ U := one_le_pow₀ hY1
  set F : ℝ → ℂ := fun t => Gj m (r + 1) (Y ^ 8) (((1 / 2 : ℝ) : ℂ) + t * I) with hF
  have hFi : Integrable F := integrable_jint m (r + 1) hm (σ := 1 / 2) (by norm_num)
    (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) r]) (y := Y ^ 8) (by positivity)
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
    have h1 := bound_halfJ hSB hY1 t
    have ht0 : 0 < 1 + |t| := by positivity
    have e : (1 + |t|) ^ (-((r + 2 : ℕ) : ℝ)) =
        (1 + |t|) ^ (-(3 / 2) : ℝ) * (1 + |t|) ^ (-(1 / 2 + (r : ℝ))) := by
      rw [← Real.rpow_add ht0]; push_cast; ring_nf
    have h2 : (1 + |t|) ^ (-(1 / 2 + (r : ℝ))) ≤ (Y ^ (4 + 8 * r))⁻¹ := by
      refine (Real.rpow_le_rpow_of_nonpos (by linarith) (show U ≤ 1 + |t| by linarith)
        (by linarith [Nat.cast_nonneg (α := ℝ) r])).trans (le_of_eq ?_)
      rw [hU, rpow8 hY0.le, show 8 * (-(1 / 2 + (r : ℝ))) = -((4 + 8 * r : ℕ) : ℝ) by
        push_cast; ring, Real.rpow_neg hY0.le, Real.rpow_natCast]
    have e2 : Y ^ (12 + 8 * r) * (Y ^ (4 + 8 * r))⁻¹ = Y ^ 8 := by
      rw [show 12 + 8 * r = 8 + (4 + 8 * r) by ring, pow_add]; field_simp
    calc ‖F t‖ ≤ K * Y ^ (12 + 8 * r) * (1 + |t|) ^ (-((r + 2 : ℕ) : ℝ)) := h1
      _ = K * Y ^ (12 + 8 * r) * (1 + |t|) ^ (-(1 / 2 + (r : ℝ))) *
          (1 + |t|) ^ (-(3 / 2) : ℝ) := by rw [e]; ring
      _ ≤ K * Y ^ (12 + 8 * r) * (Y ^ (4 + 8 * r))⁻¹ * (1 + |t|) ^ (-(3 / 2) : ℝ) := by
          have := hSB.1; gcongr
      _ = K * Y ^ 8 * (1 + |t|) ^ (-(3 / 2) : ℝ) := by rw [mul_assoc K, e2]
  have hK8 : 0 ≤ K * Y ^ 8 := by have := hSB.1; positivity
  calc ‖∫ t in sᶜ, F t‖ ≤ ∫ t in sᶜ, K * Y ^ 8 * (1 + |t|) ^ (-(3 / 2) : ℝ) := by
        refine norm_integral_le_of_norm_le ((hb.const_mul _).integrableOn) ?_
        exact (ae_restrict_iff' measurableSet_Ioc.compl).2 (Eventually.of_forall hpt)
    _ ≤ ∫ t : ℝ, K * Y ^ 8 * (1 + |t|) ^ (-(3 / 2) : ℝ) :=
        setIntegral_le_integral (hb.const_mul _) (Eventually.of_forall fun t => by positivity)
    _ = K * Y ^ 8 * ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ) := integral_const_mul _ _

/-! ### The left vertical line -/

lemma piece_leftJ (hm : 1 ≤ m) (hSB : StripBoundJ m r K) (hY : Dc m r ≤ Y) :
    ‖∫ t in -(2 * π * Y ^ 2)..(2 * π * Y ^ 2),
        Gj m (r + 1) (Y ^ 8) (((1 / 2 - (⌈Y⌉₊ : ℕ) : ℝ) : ℂ) + t * I)‖ ≤
      2 * K * (2 ^ (r + 1) * Real.exp (Dc m r / (2 * π)) +
        2 * π * ((5 + 2 * r).factorial : ℝ)) * Y ^ (9 + 6 * r) := by
  obtain ⟨hY1, hY2, hYn, hnY, hτ0, -⟩ := paramsJ hm hY
  have hY0 : 0 < Y := by linarith
  have hK := hSB.1
  have hpi := Real.pi_gt_three
  set n : ℕ := ⌈Y⌉₊ with hn
  set τ : ℝ := 2 * π * Y ^ 2 with hτ
  set c₁ : ℝ := Dc m r / (2 * π) with hc₁
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; have := Dc_ge m r; positivity
  set h : ℝ → ℝ := fun u => (2 / τ) ^ (r + 2) * ((u + c₁) / τ) ^ (2 * n) + Real.exp (-Y)
    with hh
  have hhc : Continuous h := by rw [hh]; fun_prop
  have hpt : ∀ t, |t| ≤ τ → ‖Gj m (r + 1) (Y ^ 8) (((1 / 2 - n : ℝ) : ℂ) + t * I)‖ ≤
      K * Y ^ (12 + 8 * r) * h |t| := by
    intro t ht
    have h1 := bound_left_lineJ hm hSB hY1 t n
    have h2 := left_pointwiseJ (m := m) (r := r) hY1 hY ht
    calc _ ≤ _ := h1
      _ = K * Y ^ (12 + 8 * r) * ((1 + |t|) ^ (-((r + 2 : ℕ) : ℝ)) *
          ((((n : ℝ) + r + 2) ^ 2 + (m : ℝ) ^ 2 + t ^ 2) ^ 2 / (16 * π ^ 4 * Y ^ 8)) ^ n) := by
          ring
      _ ≤ K * Y ^ (12 + 8 * r) * h |t| := by gcongr
  have hI : ‖∫ t in -τ..τ, Gj m (r + 1) (Y ^ 8) (((1 / 2 - n : ℝ) : ℂ) + t * I)‖ ≤
      ∫ t in -τ..τ, K * Y ^ (12 + 8 * r) * h |t| := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Eventually.of_forall fun t ht => hpt t ?_)
      ((continuous_const.mul (hhc.comp continuous_abs)).intervalIntegrable _ _)
    rw [abs_le]; exact ⟨ht.1.le, ht.2⟩
  refine hI.trans ?_
  rw [intervalIntegral.integral_const_mul, integral_symm_abs (g := h) hhc hτ0.le]
  have hN : ((2 * n : ℕ) : ℝ) + 1 ≤ τ := by
    push_cast
    have : 2 * (n : ℝ) + 1 ≤ 5 * Y := by linarith
    have : 5 * Y ≤ τ := by rw [hτ]; nlinarith
    linarith
  have hint : ∫ u in (0 : ℝ)..τ, h u ≤
      (2 / τ) ^ (r + 2) * (τ * Real.exp c₁ / (((2 * n : ℕ) : ℝ) + 1)) + τ * Real.exp (-Y) := by
    rw [hh]
    rw [intervalIntegral.integral_add (by
        exact (Continuous.intervalIntegrable (by fun_prop) _ _))
      (intervalIntegrable_const), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    gcongr
    exact integral_shift_pow_le hτ0 hc₁0 (2 * n) hN
  -- final arithmetic
  have hn2 : 2 * Y ≤ ((2 * n : ℕ) : ℝ) + 1 := by push_cast; linarith
  have hexpY : Y ^ (5 + 2 * r) ≤ ((5 + 2 * r).factorial : ℝ) * Real.exp Y := by
    have := Real.pow_div_factorial_le_exp Y hY0.le (5 + 2 * r)
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hA : (2 / τ) ^ (r + 2) * (τ * Real.exp c₁ / (((2 * n : ℕ) : ℝ) + 1)) * Y ^ (3 + 2 * r) ≤
      2 ^ (r + 1) * Real.exp c₁ := by
    have hτp : Y ^ (2 * (r + 1)) ≤ τ ^ (r + 1) := tau_pow_ge hY1 (r + 1)
    have key : 2 * Y ^ (3 + 2 * r) ≤ τ ^ (r + 1) * (((2 * n : ℕ) : ℝ) + 1) := by
      calc 2 * Y ^ (3 + 2 * r) = Y ^ (2 * (r + 1)) * (2 * Y) := by ring
        _ ≤ τ ^ (r + 1) * (((2 * n : ℕ) : ℝ) + 1) :=
            mul_le_mul hτp hn2 (by positivity) (by positivity)
    have e : (2 / τ) ^ (r + 2) * (τ * Real.exp c₁ / (((2 * n : ℕ) : ℝ) + 1)) * Y ^ (3 + 2 * r) =
        2 ^ (r + 2) * Real.exp c₁ * Y ^ (3 + 2 * r) / (τ ^ (r + 1) * (((2 * n : ℕ) : ℝ) + 1)) := by
      rw [div_pow, show r + 2 = (r + 1) + 1 by ring, pow_succ τ]
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have hec := Real.exp_pos c₁
    calc 2 ^ (r + 2) * Real.exp c₁ * Y ^ (3 + 2 * r) =
        2 ^ (r + 1) * Real.exp c₁ * (2 * Y ^ (3 + 2 * r)) := by ring
      _ ≤ 2 ^ (r + 1) * Real.exp c₁ * (τ ^ (r + 1) * (((2 * n : ℕ) : ℝ) + 1)) := by gcongr
  have hB : τ * Real.exp (-Y) * Y ^ (3 + 2 * r) ≤ 2 * π * ((5 + 2 * r).factorial : ℝ) := by
    rw [hτ, Real.exp_neg]
    have hey := Real.exp_pos Y
    have e5 : 2 * π * Y ^ 2 * (Real.exp Y)⁻¹ * Y ^ (3 + 2 * r) =
        2 * π * Y ^ (5 + 2 * r) / Real.exp Y := by
      rw [div_eq_mul_inv, show 5 + 2 * r = 2 + (3 + 2 * r) by ring, pow_add]; ring
    rw [e5, div_le_iff₀ hey]
    have hp0 := Real.pi_pos
    calc 2 * π * Y ^ (5 + 2 * r) ≤ 2 * π * (((5 + 2 * r).factorial : ℝ) * Real.exp Y) := by
          gcongr
      _ = 2 * π * ((5 + 2 * r).factorial : ℝ) * Real.exp Y := by ring
  set A := (2 / τ) ^ (r + 2) * (τ * Real.exp c₁ / (((2 * n : ℕ) : ℝ) + 1))
  set B := τ * Real.exp (-Y)
  have eY : Y ^ (12 + 8 * r) = Y ^ (9 + 6 * r) * Y ^ (3 + 2 * r) := by rw [← pow_add]; ring_nf
  calc K * Y ^ (12 + 8 * r) * (2 * ∫ u in (0 : ℝ)..τ, h u) ≤
        K * Y ^ (12 + 8 * r) * (2 * (A + B)) := by gcongr
    _ = 2 * K * Y ^ (9 + 6 * r) * (A * Y ^ (3 + 2 * r) + B * Y ^ (3 + 2 * r)) := by
        rw [eY]; ring
    _ ≤ 2 * K * Y ^ (9 + 6 * r) * (2 ^ (r + 1) * Real.exp c₁ +
          2 * π * ((5 + 2 * r).factorial : ℝ)) := by gcongr
    _ = _ := by ring

/-! ### The right vertical line -/

lemma right_pointwiseJ (hSB : StripBoundJ m r K) (hY1 : 1 ≤ Y) {t : ℝ}
    (ht : 2 * π * Y ^ 2 ≤ |t|) (n : ℕ) :
    ‖Gj m (r + 1) (Y ^ 8) (((1 / 2 + n : ℝ) : ℂ) + t * I)‖ ≤
      K * Y ^ (12 + 8 * r) * ((2 * π * Y ^ 2) ^ (r + 2))⁻¹ *
        ((2 * π * Y ^ 2) ^ ((4 * n : ℕ) : ℝ) * |t| ^ (-((4 * n : ℕ) : ℝ))) := by
  set τ : ℝ := 2 * π * Y ^ 2 with hτ
  have hτ0 : 0 < τ := by have := Real.pi_pos; positivity
  have ht0 : 0 < |t| := by linarith
  have ht0' : t ≠ 0 := abs_pos.1 ht0
  have h1 := bound_right_lineJ hSB hY1 ht0' n
  have e1 : (16 * π ^ 4 * Y ^ 8 / t ^ 4) ^ n =
      τ ^ ((4 * n : ℕ) : ℝ) * |t| ^ (-((4 * n : ℕ) : ℝ)) := by
    rw [Real.rpow_neg ht0.le, Real.rpow_natCast, Real.rpow_natCast, show t ^ 4 = |t| ^ 4 by
      rw [show |t| ^ 4 = (|t| ^ 2) ^ 2 by ring, sq_abs]; ring,
      show (16 * π ^ 4 * Y ^ 8 : ℝ) = τ ^ 4 by rw [hτ]; ring, div_pow, ← pow_mul, ← pow_mul,
      div_eq_mul_inv]
  have e2 : (1 + |t|) ^ (-((r + 2 : ℕ) : ℝ)) ≤ (τ ^ (r + 2))⁻¹ := by
    rw [rpow_negNat (by positivity)]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hτ0.le (by linarith) _)
  rw [e1] at h1
  refine h1.trans ?_
  have := hSB.1
  gcongr

lemma right_arith (hY1 : 1 ≤ Y) (hK : 0 ≤ K) {p : ℝ} (hpY : 3 * Y ≤ p - 1) :
    K * Y ^ (12 + 8 * r) * ((2 * π * Y ^ 2) ^ (r + 2))⁻¹ * (2 * π * Y ^ 2 / (p - 1)) ≤
      K * Y ^ (9 + 6 * r) := by
  set τ : ℝ := 2 * π * Y ^ 2 with hτ
  have hY0 : 0 < Y := by linarith
  have hτ0 : 0 < τ := by have := Real.pi_pos; positivity
  have hp : 0 < p - 1 := by linarith
  have e : K * Y ^ (12 + 8 * r) * (τ ^ (r + 2))⁻¹ * (τ / (p - 1)) =
      K * Y ^ (9 + 6 * r) * (Y ^ (3 + 2 * r) / (τ ^ (r + 1) * (p - 1))) := by
    rw [show 12 + 8 * r = (9 + 6 * r) + (3 + 2 * r) by ring, pow_add,
      show r + 2 = (r + 1) + 1 by ring, pow_succ τ]
    field_simp
  rw [e]
  have : Y ^ (3 + 2 * r) / (τ ^ (r + 1) * (p - 1)) ≤ 1 := by
    rw [div_le_one (mul_pos (by positivity) hp)]
    have hτp : Y ^ (2 * (r + 1)) ≤ τ ^ (r + 1) := tau_pow_ge hY1 (r + 1)
    calc Y ^ (3 + 2 * r) = Y ^ (2 * (r + 1)) * Y := by ring
      _ ≤ τ ^ (r + 1) * (p - 1) := mul_le_mul hτp (by linarith) hY0.le (by positivity)
  calc K * Y ^ (9 + 6 * r) * (Y ^ (3 + 2 * r) / (τ ^ (r + 1) * (p - 1))) ≤
      K * Y ^ (9 + 6 * r) * 1 := by gcongr
    _ = K * Y ^ (9 + 6 * r) := mul_one _

lemma piece_right_topJ (hm : 1 ≤ m) (hSB : StripBoundJ m r K) (hY : Dc m r ≤ Y) :
    ‖∫ t in (2 * π * Y ^ 2)..(Y ^ 8),
        Gj m (r + 1) (Y ^ 8) (((1 / 2 + (⌈Y⌉₊ : ℕ) : ℝ) : ℂ) + t * I)‖ ≤
      K * Y ^ (9 + 6 * r) := by
  obtain ⟨hY1, hY2, hYn, hnY, hτ0, hτU⟩ := paramsJ hm hY
  have hY0 : 0 < Y := by linarith
  have hK := hSB.1
  set n : ℕ := ⌈Y⌉₊ with hn
  set τ : ℝ := 2 * π * Y ^ 2 with hτ
  set p : ℝ := ((4 * n : ℕ) : ℝ) with hp
  have hp1 : 1 < p := by rw [hp]; push_cast; linarith
  have hI : ‖∫ t in τ..(Y ^ 8), Gj m (r + 1) (Y ^ 8) (((1 / 2 + n : ℝ) : ℂ) + t * I)‖ ≤
      ∫ t in τ..(Y ^ 8), K * Y ^ (12 + 8 * r) * (τ ^ (r + 2))⁻¹ * (τ ^ p * t ^ (-p)) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hτU
      (Eventually.of_forall fun t ht => ?_) ?_
    · have h := right_pointwiseJ hSB hY1 (t := t)
        (by rw [abs_of_pos (by linarith [ht.1])]; exact ht.1.le) n
      rwa [abs_of_pos (by linarith [ht.1])] at h
    · refine ((intervalIntegral.intervalIntegrable_rpow (Or.inr ?_)).const_mul (τ ^ p)).const_mul _
      rw [uIcc_of_le hτU]; intro h; linarith [h.1]
  refine hI.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have h2 := integral_rpow_tail_le hτ0 hτU hp1
  have hpY : 3 * Y ≤ p - 1 := by rw [hp]; push_cast; linarith
  calc K * Y ^ (12 + 8 * r) * (τ ^ (r + 2))⁻¹ * ∫ t in τ..(Y ^ 8), τ ^ p * t ^ (-p) ≤
      K * Y ^ (12 + 8 * r) * (τ ^ (r + 2))⁻¹ * (τ / (p - 1)) := by gcongr
    _ ≤ K * Y ^ (9 + 6 * r) := right_arith hY1 hK hpY

lemma piece_right_botJ (hm : 1 ≤ m) (hSB : StripBoundJ m r K) (hY : Dc m r ≤ Y) :
    ‖∫ t in -(Y ^ 8)..-(2 * π * Y ^ 2),
        Gj m (r + 1) (Y ^ 8) (((1 / 2 + (⌈Y⌉₊ : ℕ) : ℝ) : ℂ) + t * I)‖ ≤
      K * Y ^ (9 + 6 * r) := by
  obtain ⟨hY1, hY2, hYn, hnY, hτ0, hτU⟩ := paramsJ hm hY
  have hY0 : 0 < Y := by linarith
  have hK := hSB.1
  set n : ℕ := ⌈Y⌉₊ with hn
  set τ : ℝ := 2 * π * Y ^ 2 with hτ
  set p : ℝ := ((4 * n : ℕ) : ℝ) with hp
  have hp1 : 1 < p := by rw [hp]; push_cast; linarith
  rw [← intervalIntegral.integral_comp_neg
    (fun t : ℝ => Gj m (r + 1) (Y ^ 8) (((1 / 2 + n : ℝ) : ℂ) + t * I))]
  have hI : ‖∫ t in τ..(Y ^ 8),
      Gj m (r + 1) (Y ^ 8) (((1 / 2 + n : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ ≤
      ∫ t in τ..(Y ^ 8), K * Y ^ (12 + 8 * r) * (τ ^ (r + 2))⁻¹ * (τ ^ p * t ^ (-p)) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hτU
      (Eventually.of_forall fun t ht => ?_) ?_
    · have h := right_pointwiseJ hSB hY1 (t := -t)
        (by rw [abs_neg, abs_of_pos (by linarith [ht.1])]; exact ht.1.le) n
      rwa [abs_neg, abs_of_pos (by linarith [ht.1])] at h
    · refine ((intervalIntegral.intervalIntegrable_rpow (Or.inr ?_)).const_mul (τ ^ p)).const_mul _
      rw [uIcc_of_le hτU]; intro h; linarith [h.1]
  have hpY : 3 * Y ≤ p - 1 := by rw [hp]; push_cast; linarith
  have hI' : ‖∫ t in τ..(Y ^ 8),
      Gj m (r + 1) (Y ^ 8) (((1 / 2 + n : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ ≤
      K * Y ^ (9 + 6 * r) := by
    refine hI.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have h2 := integral_rpow_tail_le hτ0 hτU hp1
    calc K * Y ^ (12 + 8 * r) * (τ ^ (r + 2))⁻¹ * ∫ t in τ..(Y ^ 8), τ ^ p * t ^ (-p) ≤
        K * Y ^ (12 + 8 * r) * (τ ^ (r + 2))⁻¹ * (τ / (p - 1)) := by gcongr
      _ ≤ K * Y ^ (9 + 6 * r) := right_arith hY1 hK hpY
  simpa using hI'

/-! ### The horizontal segments -/

lemma piece_h_leftJ (hm : 1 ≤ m) (hSB : StripBoundJ m r K) (hY : Dc m r ≤ Y) {t : ℝ}
    (ht : |t| = 2 * π * Y ^ 2) :
    ‖∫ x in (1 / 2 - (⌈Y⌉₊ : ℕ) : ℝ)..(1 / 2 : ℝ), Gj m (r + 1) (Y ^ 8) ((x : ℂ) + t * I)‖ ≤
      128 * K * Real.exp (Dc m r) * Y ^ (9 + 6 * r) := by
  obtain ⟨hY1, hY2, hYn, hnY, hτ0, hτU⟩ := paramsJ hm hY
  have hK := hSB.1
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 / 2 - (⌈Y⌉₊ : ℕ) : ℝ)) (b := 1 / 2)
    (f := fun x : ℝ => Gj m (r + 1) (Y ^ 8) ((x : ℂ) + t * I))
    (C := 64 * K * Y ^ (8 + 6 * r) * Real.exp (Dc m r)) (fun x hx => by
      rw [uIoc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) ⌈Y⌉₊])] at hx
      exact bound_tau_leftJ hm hSB hY1 (by linarith [hx.1]) hx.2 ht)
  refine h.trans ?_
  rw [show (1 / 2 : ℝ) - (1 / 2 - (⌈Y⌉₊ : ℕ)) = (⌈Y⌉₊ : ℝ) by ring,
    abs_of_nonneg (Nat.cast_nonneg _)]
  have hE := Real.exp_pos (Dc m r)
  calc 64 * K * Y ^ (8 + 6 * r) * Real.exp (Dc m r) * (⌈Y⌉₊ : ℝ) ≤
      64 * K * Y ^ (8 + 6 * r) * Real.exp (Dc m r) * (2 * Y) := by gcongr; linarith
    _ = 128 * K * Real.exp (Dc m r) * Y ^ (9 + 6 * r) := by ring

lemma piece_h_rightJ (hm : 1 ≤ m) (hSB : StripBoundJ m r K) (hY : Dc m r ≤ Y) {t : ℝ}
    (ht : |t| = 2 * π * Y ^ 2) :
    ‖∫ x in (1 / 2 : ℝ)..(1 / 2 + (⌈Y⌉₊ : ℕ) : ℝ), Gj m (r + 1) (Y ^ 8) ((x : ℂ) + t * I)‖ ≤
      128 * K * Y ^ (9 + 6 * r) := by
  obtain ⟨hY1, hY2, hYn, hnY, hτ0, hτU⟩ := paramsJ hm hY
  have hK := hSB.1
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 1 / 2) (b := (1 / 2 + (⌈Y⌉₊ : ℕ) : ℝ))
    (f := fun x : ℝ => Gj m (r + 1) (Y ^ 8) ((x : ℂ) + t * I))
    (C := 64 * K * Y ^ (8 + 6 * r)) (fun x hx => by
      rw [uIoc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) ⌈Y⌉₊])] at hx
      exact bound_tau_rightJ hSB hY1 hx.1.le ht)
  refine h.trans ?_
  rw [show (1 / 2 + (⌈Y⌉₊ : ℕ) : ℝ) - 1 / 2 = (⌈Y⌉₊ : ℝ) by ring,
    abs_of_nonneg (Nat.cast_nonneg _)]
  calc 64 * K * Y ^ (8 + 6 * r) * (⌈Y⌉₊ : ℝ) ≤ 64 * K * Y ^ (8 + 6 * r) * (2 * Y) := by
        gcongr; linarith
    _ = 128 * K * Y ^ (9 + 6 * r) := by ring

lemma piece_h_topJ (hm : 1 ≤ m) (hSB : StripBoundJ m r K) (hY : Dc m r ≤ Y) {t : ℝ}
    (ht : |t| = Y ^ 8) :
    ‖∫ x in (1 / 2 : ℝ)..(1 / 2 + (⌈Y⌉₊ : ℕ) : ℝ), Gj m (r + 1) (Y ^ 8) ((x : ℂ) + t * I)‖ ≤
      128 * π ^ 4 * K * Y ^ (9 + 6 * r) := by
  obtain ⟨hY1, hY2, hYn, hnY, hτ0, hτU⟩ := paramsJ hm hY
  have hK := hSB.1
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 1 / 2) (b := (1 / 2 + (⌈Y⌉₊ : ℕ) : ℝ))
    (f := fun x : ℝ => Gj m (r + 1) (Y ^ 8) ((x : ℂ) + t * I))
    (C := 64 * π ^ 4 * K * Y ^ 4) (fun x hx => by
      rw [uIoc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) ⌈Y⌉₊])] at hx
      exact bound_UJ hSB hY2 hx.1 ht)
  refine h.trans ?_
  rw [show (1 / 2 + (⌈Y⌉₊ : ℕ) : ℝ) - 1 / 2 = (⌈Y⌉₊ : ℝ) by ring,
    abs_of_nonneg (Nat.cast_nonneg _)]
  have hY45 : Y ^ 5 ≤ Y ^ (9 + 6 * r) := pow_le_pow_right₀ hY1 (by omega)
  have hpi4 : 0 ≤ π ^ 4 := by positivity
  calc 64 * π ^ 4 * K * Y ^ 4 * (⌈Y⌉₊ : ℝ) ≤ 64 * π ^ 4 * K * Y ^ 4 * (2 * Y) := by
        gcongr; linarith
    _ = 128 * π ^ 4 * K * Y ^ 5 := by ring
    _ ≤ 128 * π ^ 4 * K * Y ^ (9 + 6 * r) := by gcongr

end RamanujanTau.RankinExact
