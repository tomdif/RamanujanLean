/-
# The sharp bottom kernel: `‖J_0(y)‖ ≪ y^{k/2 − 1/4}`

Bent contour for `∫ G(b+it) dt`, `b = (k+1)/2`, `G(s) = y^s Q_0(s)`. With `y = Y⁴`,
`τ = 2πY²`, `n = ⌈Y⌉₊`, `U = Y⁶`:

    ∫_{Re s = b} = (tail |t| ≥ U) + ∫_{−U}^{−τ} + ∫_{−τ}^{τ} + ∫_{τ}^{U},

and Cauchy on the rectangles `[b−n, b]×[−τ, τ]`, `[b, b+n]×[τ, U]`, `[b, b+n]×[−U, −τ]`
(`KernelPhase.rect_diff`) moves the three finite pieces onto `Re s = b − n`, `Re s = b + n`
plus six horizontal segments. Every piece is `≪ Y^{2k−1}`, so `‖J_0(y)‖ ≪ y^{k/2−1/4}`:
the true (Bessel) size `y^{k/2}·y^{−1/4}`, a saving of `y^{1/4}` over the phase-free
`y^{(k+1)/2}`.
-/
import RamanujanTau.TauPartialSumsSharp.Phase
import RamanujanTau.KernelPhase.Pieces

set_option autoImplicit false

namespace RamanujanTau.TauPartialSumsSharp

open Complex Real MeasureTheory Set Filter
open scoped Interval

variable {k : ℕ} {K Y : ℝ}

lemma params (hk : 3 ≤ k) (hY : (k : ℝ) + 3 ≤ Y) :
    1 ≤ Y ∧ 3 ≤ Y ∧ Y ≤ (⌈Y⌉₊ : ℝ) ∧ (⌈Y⌉₊ : ℝ) ≤ Y + 1 ∧ 0 < 2 * π * Y ^ 2 ∧
      2 * π * Y ^ 2 ≤ Y ^ 6 := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hY3 : 3 ≤ Y := by linarith
  have hpi := Real.pi_lt_d2
  refine ⟨by linarith, hY3, Nat.le_ceil _, (Nat.ceil_lt_add_one (by linarith)).le, by positivity, ?_⟩
  have h4 : (3 : ℝ) ^ 4 ≤ Y ^ 4 := pow_le_pow_left₀ (by norm_num) hY3 4
  have : 2 * π ≤ Y ^ 4 := by nlinarith
  calc 2 * π * Y ^ 2 ≤ Y ^ 4 * Y ^ 2 := by gcongr
    _ = Y ^ 6 := by ring

lemma pow_split (hk : 3 ≤ k) (Y : ℝ) (a : ℕ) (e : ℕ) (he : e + (2 * k - 1) = a) :
    Y ^ a = Y ^ (2 * k - 1) * Y ^ e := by
  rw [← pow_add]; congr 1; omega

/-! ### The tail `|t| ≥ U = Y⁶` of the original line -/

lemma piece_tail (hk : 3 ≤ k) (hSB : StripB k K) (hY : (k : ℝ) + 3 ≤ Y) :
    ‖(∫ t : ℝ, G0 k (Y ^ 4) (((((k : ℝ) + 1) / 2 : ℝ) : ℂ) + t * I)) -
        ∫ t in -(Y ^ 6)..(Y ^ 6), G0 k (Y ^ 4) (((((k : ℝ) + 1) / 2 : ℝ) : ℂ) + t * I)‖ ≤
      K * Y ^ (2 * k - 1) * ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ) := by
  obtain ⟨hY1, -, -, -, -, -⟩ := params hk hY
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hY0 : 0 < Y := by linarith
  set U : ℝ := Y ^ 6 with hU
  have hU1 : 1 ≤ U := one_le_pow₀ hY1
  set F : ℝ → ℂ := fun t => G0 k (Y ^ 4) (((((k : ℝ) + 1) / 2 : ℝ) : ℂ) + t * I) with hF
  have hFi : Integrable F := integrable_jint k 0 (σ := ((k : ℝ) + 1) / 2) (by simp; linarith)
    (by linarith) (by simp; linarith) (y := Y ^ 4) (by positivity)
  have hb : Integrable fun t : ℝ => (1 + |t|) ^ (-(3 / 2) : ℝ) :=
    integrable_rpow_line (p := 3 / 2) (by norm_num) 1 |>.congr
      (Eventually.of_forall fun t => by simp)
  set s : Set ℝ := Ioc (-U) U
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_add_compl measurableSet_Ioc hFi,
    add_sub_cancel_left]
  have hpt : ∀ t ∈ sᶜ, ‖F t‖ ≤ K * Y ^ (2 * k - 1) * (1 + |t|) ^ (-(3 / 2) : ℝ) := by
    intro t ht
    have hUt : U ≤ |t| := by
      simp only [s, mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have h1 := bound_base_line hSB hY1 t
    have ht0 : 0 < 1 + |t| := by positivity
    have e : (1 + |t|) ^ (-2 : ℝ) = (1 + |t|) ^ (-(3 / 2) : ℝ) * (1 + |t|) ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_add ht0]; norm_num
    have h2 : (1 + |t|) ^ (-(1 / 2) : ℝ) ≤ (Y ^ 3)⁻¹ := by
      refine (Real.rpow_le_rpow_of_nonpos (by positivity) (show U ≤ 1 + |t| by linarith)
        (by norm_num)).trans (le_of_eq ?_)
      rw [hU, show (Y ^ 6 : ℝ) = (Y ^ 3) ^ (2 : ℕ) by ring, ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity), show ((2 : ℕ) : ℝ) * (-(1 / 2)) = -1 by norm_num,
        Real.rpow_neg_one]
    have hsp := pow_split hk Y (2 * k + 2) 3 (by omega)
    have hK := hSB.1
    calc ‖F t‖ ≤ K * Y ^ (2 * k + 2) * (1 + |t|) ^ (-2 : ℝ) := h1
      _ = K * Y ^ (2 * k - 1) * Y ^ 3 * (1 + |t|) ^ (-(1 / 2) : ℝ) *
            (1 + |t|) ^ (-(3 / 2) : ℝ) := by rw [e, hsp]; ring
      _ ≤ K * Y ^ (2 * k - 1) * Y ^ 3 * (Y ^ 3)⁻¹ * (1 + |t|) ^ (-(3 / 2) : ℝ) := by gcongr
      _ = K * Y ^ (2 * k - 1) * (1 + |t|) ^ (-(3 / 2) : ℝ) := by field_simp
  have hK8 : 0 ≤ K * Y ^ (2 * k - 1) := by have := hSB.1; positivity
  calc ‖∫ t in sᶜ, F t‖ ≤ ∫ t in sᶜ, K * Y ^ (2 * k - 1) * (1 + |t|) ^ (-(3 / 2) : ℝ) := by
        refine norm_integral_le_of_norm_le ((hb.const_mul _).integrableOn) ?_
        exact (ae_restrict_iff' measurableSet_Ioc.compl).2 (Eventually.of_forall hpt)
    _ ≤ ∫ t : ℝ, K * Y ^ (2 * k - 1) * (1 + |t|) ^ (-(3 / 2) : ℝ) :=
        setIntegral_le_integral (hb.const_mul _) (Eventually.of_forall fun t => by positivity)
    _ = K * Y ^ (2 * k - 1) * ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ) := integral_const_mul _ _

/-! ### The left vertical line -/

lemma piece_left (hk : 3 ≤ k) (hSB : StripB k K) (hY : (k : ℝ) + 3 ≤ Y) :
    ‖∫ t in -(2 * π * Y ^ 2)..(2 * π * Y ^ 2),
        G0 k (Y ^ 4) (((((k : ℝ) + 1) / 2 - (⌈Y⌉₊ : ℕ) : ℝ) : ℂ) + t * I)‖ ≤
      K * (4 + 480 * π) * Y ^ (2 * k - 1) := by
  obtain ⟨hY1, hY3, hYn, hnY, hτ0, -⟩ := params hk hY
  have hY0 : 0 < Y := by linarith
  have hK := hSB.1
  have hpi := Real.pi_gt_three
  set n : ℕ := ⌈Y⌉₊ with hn
  set τ : ℝ := 2 * π * Y ^ 2 with hτ
  set h : ℝ → ℝ := fun u => 4 / τ ^ 2 * ((u + 1) / τ) ^ n + Real.exp (-Y) with hh
  have hhc : Continuous h := by rw [hh]; fun_prop
  have hpt : ∀ t, |t| ≤ τ →
      ‖G0 k (Y ^ 4) (((((k : ℝ) + 1) / 2 - n : ℝ) : ℂ) + t * I)‖ ≤ K * Y ^ (2 * k + 2) * h |t| := by
    intro t ht
    have h1 := bound_left_line hk hSB hY1 t n
    have h2 := left_pointwise hk hY ht
    calc _ ≤ _ := h1
      _ = K * Y ^ (2 * k + 2) * ((1 + |t|) ^ (-2 : ℝ) *
          ((((n : ℝ) + k) ^ 2 + t ^ 2) / (4 * π ^ 2 * Y ^ 4)) ^ n) := by ring
      _ ≤ K * Y ^ (2 * k + 2) * h |t| := by gcongr
  have hI : ‖∫ t in -τ..τ, G0 k (Y ^ 4) (((((k : ℝ) + 1) / 2 - n : ℝ) : ℂ) + t * I)‖ ≤
      ∫ t in -τ..τ, K * Y ^ (2 * k + 2) * h |t| := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Eventually.of_forall fun t ht => hpt t ?_)
      ((continuous_const.mul (hhc.comp continuous_abs)).intervalIntegrable _ _)
    rw [abs_le]; exact ⟨ht.1.le, ht.2⟩
  refine hI.trans ?_
  rw [intervalIntegral.integral_const_mul,
    RamanujanTau.KernelPhase.integral_symm_abs (g := h) hhc hτ0.le]
  have hN : (n : ℝ) + 1 ≤ τ := by
    have : 5 * Y ≤ τ := by rw [hτ]; nlinarith
    linarith
  have hint : ∫ u in (0 : ℝ)..τ, h u ≤
      4 / τ ^ 2 * (τ * Real.exp 1 / ((n : ℝ) + 1)) + τ * Real.exp (-Y) := by
    rw [hh]
    rw [intervalIntegral.integral_add (by
        exact (Continuous.intervalIntegrable (by fun_prop) _ _))
      (intervalIntegrable_const), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    gcongr
    exact RamanujanTau.KernelPhase.integral_shift_pow_le hτ0 zero_le_one n hN
  have hexpY : Y ^ 5 ≤ 120 * Real.exp Y := by
    have := Real.pow_div_factorial_le_exp Y hY0.le 5
    norm_num [Nat.factorial] at this
    linarith
  have hA : 4 / τ ^ 2 * (τ * Real.exp 1 / ((n : ℝ) + 1)) * Y ^ 3 ≤ 2 := by
    have hτY : 2 * π * Y ^ 3 ≤ τ * ((n : ℝ) + 1) := by
      rw [hτ]; have : 0 ≤ 2 * π * Y ^ 2 := by positivity
      nlinarith
    have e : 4 / τ ^ 2 * (τ * Real.exp 1 / ((n : ℝ) + 1)) =
        4 * Real.exp 1 / (τ * ((n : ℝ) + 1)) := by
      field_simp
    rw [e, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have he := Real.exp_one_lt_d9
    have hY3' : 0 < Y ^ 3 := by positivity
    calc 4 * Real.exp 1 * Y ^ 3 ≤ 4 * 2.7182818286 * Y ^ 3 := by gcongr
      _ ≤ 2 * (2 * π * Y ^ 3) := by nlinarith
      _ ≤ 2 * (τ * ((n : ℝ) + 1)) := by gcongr
  have hB : τ * Real.exp (-Y) * Y ^ 3 ≤ 240 * π := by
    rw [hτ, Real.exp_neg]
    have hey := Real.exp_pos Y
    rw [show 2 * π * Y ^ 2 * (Real.exp Y)⁻¹ * Y ^ 3 = 2 * π * Y ^ 5 / Real.exp Y by
      field_simp, div_le_iff₀ hey]
    have hp0 := Real.pi_pos
    calc 2 * π * Y ^ 5 ≤ 2 * π * (120 * Real.exp Y) := by gcongr
      _ = 240 * π * Real.exp Y := by ring
  have hsp := pow_split hk Y (2 * k + 2) 3 (by omega)
  set A := 4 / τ ^ 2 * (τ * Real.exp 1 / ((n : ℝ) + 1))
  set B := τ * Real.exp (-Y)
  have hYk : 0 ≤ Y ^ (2 * k - 1) := by positivity
  calc K * Y ^ (2 * k + 2) * (2 * ∫ u in (0 : ℝ)..τ, h u) ≤ K * Y ^ (2 * k + 2) * (2 * (A + B)) := by
        gcongr
    _ = 2 * K * Y ^ (2 * k - 1) * (A * Y ^ 3 + B * Y ^ 3) := by rw [hsp]; ring
    _ ≤ 2 * K * Y ^ (2 * k - 1) * (2 + 240 * π) := by gcongr
    _ = K * (4 + 480 * π) * Y ^ (2 * k - 1) := by ring

/-! ### The right vertical lines -/

lemma right_pointwise (hSB : StripB k K) (hY1 : 1 ≤ Y) {t : ℝ}
    (ht : 2 * π * Y ^ 2 ≤ |t|) (n : ℕ) :
    ‖G0 k (Y ^ 4) ((((k : ℝ) + 1) / 2 + n : ℝ) + t * I)‖ ≤
      K * Y ^ (2 * k + 2) * ((2 * π * Y ^ 2) ^ 2)⁻¹ *
        ((2 * π * Y ^ 2) ^ ((2 * n : ℕ) : ℝ) * |t| ^ (-((2 * n : ℕ) : ℝ))) := by
  set τ : ℝ := 2 * π * Y ^ 2 with hτ
  have hτ0 : 0 < τ := by have := Real.pi_pos; positivity
  have ht0 : 0 < |t| := by linarith
  have ht0' : t ≠ 0 := abs_pos.1 ht0
  have h1 := bound_right_line hSB hY1 ht0' n
  have e1 : (4 * π ^ 2 * Y ^ 4 / t ^ 2) ^ n = τ ^ ((2 * n : ℕ) : ℝ) * |t| ^ (-((2 * n : ℕ) : ℝ)) := by
    rw [Real.rpow_neg ht0.le, Real.rpow_natCast, Real.rpow_natCast, show t ^ 2 = |t| ^ 2 by
      rw [sq_abs], show (4 * π ^ 2 * Y ^ 4 : ℝ) = τ ^ 2 by rw [hτ]; ring, div_pow, ← pow_mul,
      ← pow_mul, div_eq_mul_inv]
  have e2 : (1 + |t|) ^ (-2 : ℝ) ≤ (τ ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
      Real.rpow_natCast]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hτ0.le (by linarith) 2)
  rw [e1] at h1
  refine h1.trans ?_
  have := hSB.1
  gcongr

lemma right_final (hk : 3 ≤ k) (hK : 0 ≤ K) (hY : (k : ℝ) + 3 ≤ Y) {p : ℝ}
    (hp : p = ((2 * ⌈Y⌉₊ : ℕ) : ℝ)) :
    K * Y ^ (2 * k + 2) * ((2 * π * Y ^ 2) ^ 2)⁻¹ * ((2 * π * Y ^ 2) / (p - 1)) ≤
      K * Y ^ (2 * k - 1) := by
  obtain ⟨hY1, hY3, hYn, hnY, hτ0, -⟩ := params hk hY
  have hY0 : 0 < Y := by linarith
  have hpY : Y ≤ p - 1 := by rw [hp]; push_cast; linarith
  have hp1 : 0 < p - 1 := by linarith
  have hsp := pow_split hk Y (2 * k + 2) 3 (by omega)
  have e : K * Y ^ (2 * k + 2) * ((2 * π * Y ^ 2) ^ 2)⁻¹ * ((2 * π * Y ^ 2) / (p - 1)) =
      K * Y ^ (2 * k - 1) * (Y ^ 3 / ((2 * π * Y ^ 2) * (p - 1))) := by
    rw [hsp]; field_simp
  rw [e]
  have hpi := Real.pi_gt_three
  have : Y ^ 3 / ((2 * π * Y ^ 2) * (p - 1)) ≤ 1 := by
    rw [div_le_one (mul_pos hτ0 hp1)]
    calc Y ^ 3 = 1 * Y ^ 2 * Y := by ring
      _ ≤ (2 * π) * Y ^ 2 * (p - 1) := by gcongr <;> nlinarith
  have h0 : 0 ≤ K * Y ^ (2 * k - 1) := by positivity
  calc K * Y ^ (2 * k - 1) * (Y ^ 3 / ((2 * π * Y ^ 2) * (p - 1))) ≤ K * Y ^ (2 * k - 1) * 1 := by
        gcongr
    _ = K * Y ^ (2 * k - 1) := mul_one _

lemma piece_right_top (hk : 3 ≤ k) (hSB : StripB k K) (hY : (k : ℝ) + 3 ≤ Y) :
    ‖∫ t in (2 * π * Y ^ 2)..(Y ^ 6),
        G0 k (Y ^ 4) (((((k : ℝ) + 1) / 2 + (⌈Y⌉₊ : ℕ) : ℝ) : ℂ) + t * I)‖ ≤ K * Y ^ (2 * k - 1) := by
  obtain ⟨hY1, hY3, hYn, hnY, hτ0, hτU⟩ := params hk hY
  have hK := hSB.1
  set n : ℕ := ⌈Y⌉₊ with hn
  set τ : ℝ := 2 * π * Y ^ 2 with hτ
  set p : ℝ := ((2 * n : ℕ) : ℝ) with hp
  have hp1 : 1 < p := by rw [hp]; push_cast; linarith
  have hI : ‖∫ t in τ..(Y ^ 6), G0 k (Y ^ 4) (((((k : ℝ) + 1) / 2 + n : ℝ) : ℂ) + t * I)‖ ≤
      ∫ t in τ..(Y ^ 6), K * Y ^ (2 * k + 2) * (τ ^ 2)⁻¹ * (τ ^ p * t ^ (-p)) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hτU
      (Eventually.of_forall fun t ht => ?_) ?_
    · have h := right_pointwise hSB hY1 (t := t)
        (by rw [abs_of_pos (by linarith [ht.1])]; exact ht.1.le) n
      rwa [abs_of_pos (by linarith [ht.1])] at h
    · refine ((intervalIntegral.intervalIntegrable_rpow (Or.inr ?_)).const_mul (τ ^ p)).const_mul _
      rw [uIcc_of_le hτU]; intro h; linarith [h.1]
  refine hI.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have h2 := RamanujanTau.KernelPhase.integral_rpow_tail_le hτ0 hτU hp1
  calc K * Y ^ (2 * k + 2) * (τ ^ 2)⁻¹ * ∫ t in τ..(Y ^ 6), τ ^ p * t ^ (-p) ≤
      K * Y ^ (2 * k + 2) * (τ ^ 2)⁻¹ * (τ / (p - 1)) := by gcongr
    _ ≤ K * Y ^ (2 * k - 1) := right_final hk hK hY hp

lemma piece_right_bot (hk : 3 ≤ k) (hSB : StripB k K) (hY : (k : ℝ) + 3 ≤ Y) :
    ‖∫ t in -(Y ^ 6)..-(2 * π * Y ^ 2),
        G0 k (Y ^ 4) (((((k : ℝ) + 1) / 2 + (⌈Y⌉₊ : ℕ) : ℝ) : ℂ) + t * I)‖ ≤ K * Y ^ (2 * k - 1) := by
  obtain ⟨hY1, hY3, hYn, hnY, hτ0, hτU⟩ := params hk hY
  have hK := hSB.1
  set n : ℕ := ⌈Y⌉₊ with hn
  set τ : ℝ := 2 * π * Y ^ 2 with hτ
  set p : ℝ := ((2 * n : ℕ) : ℝ) with hp
  have hp1 : 1 < p := by rw [hp]; push_cast; linarith
  rw [← intervalIntegral.integral_comp_neg
    (fun t : ℝ => G0 k (Y ^ 4) (((((k : ℝ) + 1) / 2 + n : ℝ) : ℂ) + t * I))]
  have hI : ‖∫ t in τ..(Y ^ 6), G0 k (Y ^ 4) (((((k : ℝ) + 1) / 2 + n : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ ≤
      ∫ t in τ..(Y ^ 6), K * Y ^ (2 * k + 2) * (τ ^ 2)⁻¹ * (τ ^ p * t ^ (-p)) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hτU
      (Eventually.of_forall fun t ht => ?_) ?_
    · have h := right_pointwise hSB hY1 (t := -t)
        (by rw [abs_neg, abs_of_pos (by linarith [ht.1])]; exact ht.1.le) n
      rwa [abs_neg, abs_of_pos (by linarith [ht.1])] at h
    · refine ((intervalIntegral.intervalIntegrable_rpow (Or.inr ?_)).const_mul (τ ^ p)).const_mul _
      rw [uIcc_of_le hτU]; intro h; linarith [h.1]
  have hI' : ‖∫ t in τ..(Y ^ 6), G0 k (Y ^ 4) (((((k : ℝ) + 1) / 2 + n : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ ≤
      K * Y ^ (2 * k - 1) := by
    refine hI.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have h2 := RamanujanTau.KernelPhase.integral_rpow_tail_le hτ0 hτU hp1
    calc K * Y ^ (2 * k + 2) * (τ ^ 2)⁻¹ * ∫ t in τ..(Y ^ 6), τ ^ p * t ^ (-p) ≤
        K * Y ^ (2 * k + 2) * (τ ^ 2)⁻¹ * (τ / (p - 1)) := by gcongr
      _ ≤ K * Y ^ (2 * k - 1) := right_final hk hK hY hp
  simpa using hI'

/-! ### The horizontal segments -/

lemma len_bound (hk : 3 ≤ k) (hY : (k : ℝ) + 3 ≤ Y) {C : ℝ} (hC : 0 ≤ C) :
    C * Y ^ (2 * k - 2) * (⌈Y⌉₊ : ℝ) ≤ 2 * C * Y ^ (2 * k - 1) := by
  obtain ⟨hY1, hY3, hYn, hnY, -, -⟩ := params hk hY
  have hsp : Y ^ (2 * k - 1) = Y ^ (2 * k - 2) * Y := by
    rw [← pow_succ]; congr 1; omega
  rw [hsp]
  have : 0 ≤ C * Y ^ (2 * k - 2) := by positivity
  nlinarith

lemma piece_h_left (hk : 3 ≤ k) (hSB : StripB k K) (hY : (k : ℝ) + 3 ≤ Y) {t : ℝ}
    (ht : |t| = 2 * π * Y ^ 2) :
    ‖∫ x in (((k : ℝ) + 1) / 2 - (⌈Y⌉₊ : ℕ) : ℝ)..(((k : ℝ) + 1) / 2 : ℝ),
        G0 k (Y ^ 4) ((x : ℂ) + t * I)‖ ≤ 2 * (K * Real.exp 1) * Y ^ (2 * k - 1) := by
  have hK := hSB.1
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (((k : ℝ) + 1) / 2 - (⌈Y⌉₊ : ℕ) : ℝ)) (b := ((k : ℝ) + 1) / 2)
    (f := fun x : ℝ => G0 k (Y ^ 4) ((x : ℂ) + t * I))
    (C := K * Y ^ (2 * k - 2) * Real.exp 1) (fun x hx => by
      rw [uIoc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) ⌈Y⌉₊])] at hx
      exact bound_tau_left hk hSB hY (by linarith [hx.1]) hx.2 ht)
  refine h.trans ?_
  rw [show ((k : ℝ) + 1) / 2 - (((k : ℝ) + 1) / 2 - (⌈Y⌉₊ : ℕ)) = (⌈Y⌉₊ : ℝ) by ring,
    abs_of_nonneg (Nat.cast_nonneg _)]
  have := len_bound hk hY (C := K * Real.exp 1) (by positivity)
  calc K * Y ^ (2 * k - 2) * Real.exp 1 * (⌈Y⌉₊ : ℝ) =
      K * Real.exp 1 * Y ^ (2 * k - 2) * (⌈Y⌉₊ : ℝ) := by ring
    _ ≤ _ := this

lemma piece_h_right (hk : 3 ≤ k) (hSB : StripB k K) (hY : (k : ℝ) + 3 ≤ Y) {t : ℝ}
    (ht : |t| = 2 * π * Y ^ 2) :
    ‖∫ x in (((k : ℝ) + 1) / 2 : ℝ)..(((k : ℝ) + 1) / 2 + (⌈Y⌉₊ : ℕ) : ℝ),
        G0 k (Y ^ 4) ((x : ℂ) + t * I)‖ ≤ 2 * K * Y ^ (2 * k - 1) := by
  obtain ⟨hY1, -, -, -, -, -⟩ := params hk hY
  have hK := hSB.1
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := ((k : ℝ) + 1) / 2) (b := (((k : ℝ) + 1) / 2 + (⌈Y⌉₊ : ℕ) : ℝ))
    (f := fun x : ℝ => G0 k (Y ^ 4) ((x : ℂ) + t * I))
    (C := K * Y ^ (2 * k - 2)) (fun x hx => by
      rw [uIoc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) ⌈Y⌉₊])] at hx
      exact bound_tau_right (by omega) hSB hY1 hx.1.le ht)
  refine h.trans ?_
  rw [show (((k : ℝ) + 1) / 2 + (⌈Y⌉₊ : ℕ) : ℝ) - ((k : ℝ) + 1) / 2 = (⌈Y⌉₊ : ℝ) by ring,
    abs_of_nonneg (Nat.cast_nonneg _)]
  exact len_bound hk hY hK

lemma piece_h_top (hk : 3 ≤ k) (hSB : StripB k K) (hY : (k : ℝ) + 3 ≤ Y) {t : ℝ}
    (ht : |t| = Y ^ 6) :
    ‖∫ x in (((k : ℝ) + 1) / 2 : ℝ)..(((k : ℝ) + 1) / 2 + (⌈Y⌉₊ : ℕ) : ℝ),
        G0 k (Y ^ 4) ((x : ℂ) + t * I)‖ ≤ 2 * K * Y ^ (2 * k - 1) := by
  obtain ⟨hY1, hY3, -, -, -, -⟩ := params hk hY
  have hK := hSB.1
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := ((k : ℝ) + 1) / 2) (b := (((k : ℝ) + 1) / 2 + (⌈Y⌉₊ : ℕ) : ℝ))
    (f := fun x : ℝ => G0 k (Y ^ 4) ((x : ℂ) + t * I))
    (C := K * Y ^ (2 * k - 2)) (fun x hx => by
      rw [uIoc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) ⌈Y⌉₊])] at hx
      exact bound_U (by omega) hSB hY3 hx.1 ht)
  refine h.trans ?_
  rw [show (((k : ℝ) + 1) / 2 + (⌈Y⌉₊ : ℕ) : ℝ) - ((k : ℝ) + 1) / 2 = (⌈Y⌉₊ : ℝ) by ring,
    abs_of_nonneg (Nat.cast_nonneg _)]
  exact len_bound hk hY hK

/-! ### Assembly -/

/-- **The contour bound** `‖∫ G(b+it) dt‖ ≤ C Y^{2k−1}` for `Y ≥ k + 3` (`y = Y⁴`). -/
theorem integral_G0_le (hk : 3 ≤ k) : ∃ C : ℝ, ∀ Y : ℝ, (k : ℝ) + 3 ≤ Y →
    ‖∫ t : ℝ, G0 k (Y ^ 4) (((((k : ℝ) + 1) / 2 : ℝ) : ℂ) + t * I)‖ ≤ C * Y ^ (2 * k - 1) := by
  obtain ⟨K, hSB⟩ := exists_stripB k hk
  set I₃ : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ) with hI₃
  have hI₃0 : 0 ≤ I₃ := integral_nonneg fun t => by positivity
  refine ⟨K * I₃ + K * (4 + 480 * π) + 2 * (2 * (K * Real.exp 1)) + 2 * K + 2 * (2 * K) +
    2 * (2 * K), fun Y hY => ?_⟩
  obtain ⟨hY1, hY3, hYn, hnY, hT00, hT0U⟩ := params hk hY
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hY0 : 0 < Y := by linarith
  have hK := hSB.1
  have hy0 : (0 : ℝ) < Y ^ 4 := by positivity
  set b : ℝ := ((k : ℝ) + 1) / 2 with hb
  set n : ℕ := ⌈Y⌉₊ with hn
  set T0 : ℝ := 2 * π * Y ^ 2 with hT0
  set U : ℝ := Y ^ 6 with hU
  have hU0 : 0 < U := by positivity
  set f : ℂ → ℂ := G0 k (Y ^ 4) with hf
  set F : ℝ → ℂ := fun t => f ((b : ℂ) + t * I) with hF
  have hFc : Continuous F := continuous_jint k 0 (σ := b) (by rw [hb]; linarith) (y := Y ^ 4) hy0
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have htail := piece_tail hk hSB hY
  have hsplit : ∫ t in -U..U, F t =
      (∫ t in -U..-T0, F t) + (∫ t in -T0..T0, F t) + ∫ t in T0..U, F t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable _ _)
      (hFc.intervalIntegrable _ _), intervalIntegral.integral_add_adjacent_intervals
      (hFc.intervalIntegrable _ _) (hFc.intervalIntegrable _ _)]
  have H1 : DifferentiableOn ℂ f ([[(b - n : ℝ), b]] ×ℂ [[-T0, T0]]) := by
    intro s hs
    rw [mem_reProdIm, uIcc_of_le (show (b - n : ℝ) ≤ b by linarith)] at hs
    exact (differentiableAt_G0 k hy0 (Or.inl (by rw [hb] at hs; linarith [hs.1.2]))).differentiableWithinAt
  have H2 : DifferentiableOn ℂ f ([[b, (b + n : ℝ)]] ×ℂ [[T0, U]]) := by
    intro s hs
    rw [mem_reProdIm, uIcc_of_le hT0U] at hs
    exact (differentiableAt_G0 k hy0 (Or.inr (by linarith [hs.2.1]))).differentiableWithinAt
  have H3 : DifferentiableOn ℂ f ([[b, (b + n : ℝ)]] ×ℂ [[-U, -T0]]) := by
    intro s hs
    rw [mem_reProdIm, uIcc_of_le (show -U ≤ -T0 by linarith)] at hs
    exact (differentiableAt_G0 k hy0 (Or.inr (by linarith [hs.2.2]))).differentiableWithinAt
  have R1 := RamanujanTau.KernelPhase.rect_diff f (b - n : ℝ) b (-T0) T0 H1
  have R2 := RamanujanTau.KernelPhase.rect_diff f b (b + n : ℝ) T0 U H2
  have R3 := RamanujanTau.KernelPhase.rect_diff f b (b + n : ℝ) (-U) (-T0) H3
  have P1 := piece_left hk hSB hY
  have P2 := piece_right_top hk hSB hY
  have P3 := piece_right_bot hk hSB hY
  have P4 := piece_h_left hk hSB hY (t := -T0) (by rw [abs_neg, abs_of_pos hT00])
  have P5 := piece_h_left hk hSB hY (t := T0) (abs_of_pos hT00)
  have P6 := piece_h_right hk hSB hY (t := T0) (abs_of_pos hT00)
  have P7 := piece_h_right hk hSB hY (t := -T0) (by rw [abs_neg, abs_of_pos hT00])
  have P8 := piece_h_top hk hSB hY (t := U) (abs_of_pos hU0)
  have P9 := piece_h_top hk hSB hY (t := -U) (by rw [abs_neg, abs_of_pos hU0])
  set S := ∫ t : ℝ, F t
  set A := ∫ t in -U..-T0, F t
  set B := ∫ t in -T0..T0, F t
  set Cc := ∫ t in T0..U, F t
  set VL := ∫ t in -T0..T0, f (((b - n : ℝ) : ℂ) + t * I)
  set VT := ∫ t in T0..U, f (((b + n : ℝ) : ℂ) + t * I)
  set VB := ∫ t in -U..-T0, f (((b + n : ℝ) : ℂ) + t * I)
  have e1 := norm_sub_norm_le S (∫ t in -U..U, F t)
  have e2 : ‖∫ t in -U..U, F t‖ ≤ ‖A‖ + ‖B‖ + ‖Cc‖ := by
    rw [hsplit]; exact norm_add₃_le
  have e3 := norm_sub_norm_le B VL
  have e4 := norm_sub_norm_le Cc VT
  have e5 := norm_sub_norm_le A VB
  rw [norm_sub_rev] at e4 e5
  push_cast at R1 R2 R3 P1 P2 P3 P4 P5 P6 P7 P8 P9
  simp only [hf] at R1 R2 R3
  have hYk : 0 ≤ Y ^ (2 * k - 1) := by positivity
  nlinarith

/-- **The sharp bottom kernel bound** `‖J_0(y)‖ ≤ C y^{k/2 − 1/4}` for `y ≥ 1`,
on the line `Re s = (k+1)/2`. -/
theorem kernelZero_sharp (hk : 3 ≤ k) :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y →
      ‖Jc k 0 (((k : ℝ) + 1) / 2) y‖ ≤ C * y ^ ((k : ℝ) / 2 - 1 / 4) := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨C, hC⟩ := integral_G0_le hk
  obtain ⟨K₀, hK₀, hK₀b⟩ := norm_Jc_le k 0 (σ := ((k : ℝ) + 1) / 2) (by simp; linarith)
    (by linarith) (by simp; linarith)
  set Y₀ : ℝ := (k : ℝ) + 3 with hY₀
  have hY₀1 : 1 ≤ Y₀ := by rw [hY₀]; linarith
  refine ⟨1 / (2 * π) * |C| + K₀ * Y₀ ^ 3, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  set Y : ℝ := y ^ ((1 : ℝ) / 4) with hYdef
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hy0 _
  have hY1 : 1 ≤ Y := Real.one_le_rpow hy (by norm_num)
  have hyY : Y ^ 4 = y := by
    rw [hYdef, ← Real.rpow_mul_natCast hy0.le]; norm_num
  have hyk : y ^ ((k : ℝ) / 2 - 1 / 4) = Y ^ (2 * k - 1) := by
    rw [hYdef, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    congr 1
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hyk]
  have hpi := Real.pi_pos
  have hYk : 0 ≤ Y ^ (2 * k - 1) := by positivity
  rcases le_or_gt Y₀ Y with hbig | hsmall
  · have h := hC Y hbig
    rw [hyY] at h
    rw [Jc_eq_G0, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
    calc 1 / (2 * π) * ‖∫ t : ℝ, G0 k y (((((k : ℝ) + 1) / 2 : ℝ) : ℂ) + t * I)‖ ≤
        1 / (2 * π) * (|C| * Y ^ (2 * k - 1)) := by
          gcongr; exact h.trans (by gcongr; exact le_abs_self C)
      _ ≤ (1 / (2 * π) * |C| + K₀ * Y₀ ^ 3) * Y ^ (2 * k - 1) := by
          have : 0 ≤ K₀ * Y₀ ^ 3 * Y ^ (2 * k - 1) := by positivity
          nlinarith
  · have h := hK₀b y hy0
    have e : y ^ (((k : ℝ) + 1) / 2 + ((0 : ℕ) : ℝ)) = Y ^ (2 * k + 2) := by
      rw [← hyY, rpow4 hY0.le, ← Real.rpow_natCast]; congr 1; push_cast; ring
    rw [e] at h
    have hsp := pow_split hk Y (2 * k + 2) 3 (by omega)
    have h12 : Y ^ (2 * k + 2) ≤ Y₀ ^ 3 * Y ^ (2 * k - 1) := by
      have : Y ^ 3 ≤ Y₀ ^ 3 := pow_le_pow_left₀ hY0.le hsmall.le 3
      rw [hsp]
      calc Y ^ (2 * k - 1) * Y ^ 3 ≤ Y ^ (2 * k - 1) * Y₀ ^ 3 := by gcongr
        _ = Y₀ ^ 3 * Y ^ (2 * k - 1) := by ring
    have : 0 ≤ 1 / (2 * π) * |C| * Y ^ (2 * k - 1) := by positivity
    calc ‖Jc k 0 (((k : ℝ) + 1) / 2) y‖ ≤ K₀ * Y ^ (2 * k + 2) := h
      _ ≤ K₀ * (Y₀ ^ 3 * Y ^ (2 * k - 1)) := by gcongr
      _ ≤ (1 / (2 * π) * |C| + K₀ * Y₀ ^ 3) * Y ^ (2 * k - 1) := by nlinarith

end RamanujanTau.TauPartialSumsSharp
