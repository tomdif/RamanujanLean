/-
# The ray integral: blocks, summation, change of variables

`ray_lower`: for `0 < β < π/2`, `κ = cot β`, and integers `N₁ ≤ N₂` with `κN₂ ≤ 1`,

    ∫ |Λ(6+it)|² e^{2βt} dt ≥ a κ^{-12} (log N₂ − log N₁).
-/
import RamanujanTau.CriticalMeanSquareLower.Ray

set_option autoImplicit false

namespace RamanujanTau.CriticalMeanSquareLower

open Complex MeasureTheory Set Filter Topology
open UpperHalfPlane hiding I
open RamanujanTau.HeckeL RamanujanTau.HardyZeros RamanujanTau.HardyCountHafner
  RamanujanTau.CriticalMeanSquare
open scoped Real

/-- The ray integrand in the variable `w = sin β · e^u`: `w¹¹ |Δ(−w + iκw)|²`. -/
noncomputable def Gw (κ w : ℝ) : ℝ := w ^ 11 * ‖Dc (pt (-w) (κ * w))‖ ^ 2

lemma continuous_pt₂ (y : ℝ) : Continuous fun w : ℝ => pt (-w) y := by
  unfold pt; fun_prop

lemma continuousOn_Gw {κ : ℝ} (hκ : 0 < κ) : ContinuousOn (Gw κ) (Ioi 0) := by
  have hc : Continuous fun w : ℝ => pt (-w) (κ * w) := by unfold pt; fun_prop
  have h1 : ContinuousOn (fun w : ℝ => Dc (pt (-w) (κ * w))) (Ioi 0) :=
    continuousOn_Dc.comp hc.continuousOn (fun w hw => by
      show 0 < (pt (-w) (κ * w)).im
      rw [pt_im]; exact mul_pos hκ hw)
  exact (continuousOn_pow 11).mul (h1.norm.pow 2)

lemma continuous_Dc_horiz {y : ℝ} (hy : 0 < y) : Continuous fun w : ℝ => Dc (pt (-w) y) :=
  continuousOn_Dc.comp_continuous (continuous_pt₂ y) (fun w => by
    show 0 < (pt (-w) y).im
    rw [pt_im]; exact hy)

lemma Gw_nonneg {κ w : ℝ} (hw : 0 ≤ w) : 0 ≤ Gw κ w := by unfold Gw; positivity

/-- **One block** `[N, N+1]`. -/
lemma block_lower {k A : ℝ} (hA0 : 0 ≤ A) (hk : ∀ y : ℝ, 0 < y → y ≤ 1 → k / y ^ 12 ≤ Hh y)
    (hA : ∀ x y₁ y₂ y₀ : ℝ, 0 < y₀ → y₀ ≤ y₁ → y₀ ≤ y₂ →
      ‖Dc (pt x y₁) - Dc (pt x y₂)‖ ≤ A * |y₁ - y₂| / y₀ ^ 7)
    {κ N : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N) (hκN : κ * N ≤ 1) :
    k / 2 / (κ ^ 12 * N) - A ^ 2 / (κ ^ 12 * N ^ 3) ≤ ∫ w in N..N + 1, Gw κ w := by
  have hN0 : 0 < N := by linarith
  set y₀ : ℝ := κ * N with hy₀
  have hy₀0 : 0 < y₀ := mul_pos hκ hN0
  set E : ℝ := (A * κ / y₀ ^ 7) ^ 2 with hE
  set f : ℝ → ℝ := fun w => ‖Dc (pt (-w) y₀)‖ ^ 2 with hf
  have hfc : Continuous f := (continuous_Dc_horiz hy₀0).norm.pow 2
  -- pointwise comparison
  have hpt : ∀ w ∈ Icc N (N + 1), N ^ 11 / 2 * f w - N ^ 11 * E ≤ Gw κ w := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hwpos : 0 ≤ w := by linarith
    set a := Dc (pt (-w) (κ * w))
    set b := Dc (pt (-w) y₀)
    have hab : ‖a - b‖ ≤ A * κ / y₀ ^ 7 := by
      have h := hA (-w) (κ * w) y₀ y₀ hy₀0 (by rw [hy₀]; gcongr) le_rfl
      have habs : |κ * w - y₀| ≤ κ := by
        rw [hy₀, ← mul_sub, abs_of_nonneg (by nlinarith)]
        nlinarith
      refine h.trans ?_
      rw [div_le_div_iff_of_pos_right (by positivity)]
      exact mul_le_mul_of_nonneg_left habs hA0
    have hb : ‖b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖a - b‖ ^ 2 := by
      have h1 : ‖b‖ ≤ ‖a‖ + ‖a - b‖ := by
        calc ‖b‖ = ‖a - (a - b)‖ := by ring_nf
          _ ≤ ‖a‖ + ‖a - b‖ := norm_sub_le _ _
      have h0 : 0 ≤ ‖b‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖a‖ - ‖a - b‖), norm_nonneg a, norm_nonneg (a - b)]
    have hab2 : ‖a - b‖ ^ 2 ≤ E := by
      rw [hE]; exact pow_le_pow_left₀ (norm_nonneg _) hab 2
    have hfa : f w / 2 - E ≤ ‖a‖ ^ 2 := by
      show ‖b‖ ^ 2 / 2 - E ≤ ‖a‖ ^ 2
      linarith
    have hN11 : (0 : ℝ) ≤ N ^ 11 := by positivity
    have hw11 : N ^ 11 ≤ w ^ 11 := pow_le_pow_left₀ (by linarith) hw1 11
    calc N ^ 11 / 2 * f w - N ^ 11 * E = N ^ 11 * (f w / 2 - E) := by ring
      _ ≤ N ^ 11 * ‖a‖ ^ 2 := mul_le_mul_of_nonneg_left hfa hN11
      _ ≤ w ^ 11 * ‖a‖ ^ 2 := mul_le_mul_of_nonneg_right hw11 (sq_nonneg _)
      _ = Gw κ w := rfl
  have hint1 : IntervalIntegrable (fun w => N ^ 11 / 2 * f w - N ^ 11 * E) volume N (N + 1) :=
    ((hfc.const_mul _).sub continuous_const).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (Gw κ) volume N (N + 1) := by
    refine ContinuousOn.intervalIntegrable ((continuousOn_Gw hκ).mono ?_)
    rw [uIcc_of_le (by linarith)]
    intro w hw; exact lt_of_lt_of_le hN0 hw.1
  have hmono := intervalIntegral.integral_mono_on (by linarith) hint1 hint2 hpt
  have hval : ∫ w in N..N + 1, (N ^ 11 / 2 * f w - N ^ 11 * E) = N ^ 11 / 2 * Hh y₀ - N ^ 11 * E := by
    rw [intervalIntegral.integral_sub ((hfc.const_mul _).intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    rw [hf, integral_period]
    simp
  rw [hval] at hmono
  -- numerics
  have hH := hk y₀ hy₀0 hκN
  have h1 : k / 2 / (κ ^ 12 * N) ≤ N ^ 11 / 2 * Hh y₀ := by
    have e : k / 2 / (κ ^ 12 * N) = N ^ 11 / 2 * (k / y₀ ^ 12) := by
      rw [hy₀]; field_simp
    rw [e]; gcongr
  have h2 : N ^ 11 * E = A ^ 2 / (κ ^ 12 * N ^ 3) := by
    rw [hE, hy₀]; field_simp
  linarith

/-- **Summing the blocks** `N₁ ≤ N < N₁ + m`. -/
lemma sum_lower {k A : ℝ} (hk0 : 0 < k) (hA0 : 0 ≤ A) (hk : ∀ y : ℝ, 0 < y → y ≤ 1 → k / y ^ 12 ≤ Hh y)
    (hA : ∀ x y₁ y₂ y₀ : ℝ, 0 < y₀ → y₀ ≤ y₁ → y₀ ≤ y₂ →
      ‖Dc (pt x y₁) - Dc (pt x y₂)‖ ≤ A * |y₁ - y₂| / y₀ ^ 7)
    {κ : ℝ} (hκ : 0 < κ) {N₁ : ℕ} (hN₁ : 1 ≤ N₁) (hkN : 4 * A ^ 2 ≤ k * (N₁ : ℝ) ^ 2) :
    ∀ m : ℕ, κ * ((N₁ : ℝ) + m) ≤ 1 →
      k / 4 / κ ^ 12 * (Real.log ((N₁ : ℝ) + m) - Real.log N₁) ≤
        ∫ w in (N₁ : ℝ)..(N₁ : ℝ) + m, Gw κ w := by
  have hN₁r : (1 : ℝ) ≤ N₁ := by exact_mod_cast hN₁
  have hii : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b → IntervalIntegrable (Gw κ) volume a b := by
    intro a b ha hb
    refine ContinuousOn.intervalIntegrable ((continuousOn_Gw hκ).mono ?_)
    intro w hw
    have := hw.1
    show 0 < w
    have : (1 : ℝ) ≤ min a b := le_min ha hb
    linarith [hw.1, min_le_left a b]
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    push_cast at hm ⊢
    set n : ℝ := (N₁ : ℝ) + m with hn
    have hn1 : 1 ≤ n := by rw [hn]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hn0 : 0 < n := by linarith
    have hm' : κ * n ≤ 1 := by nlinarith
    have hIH := ih hm'
    have hblock := block_lower hA0 hk hA hκ hn1 (by nlinarith)
    have hsplit : ∫ w in (N₁ : ℝ)..n + 1, Gw κ w =
        (∫ w in (N₁ : ℝ)..n, Gw κ w) + ∫ w in n..n + 1, Gw κ w :=
      (intervalIntegral.integral_add_adjacent_intervals (hii _ _ hN₁r hn1)
        (hii _ _ hn1 (by linarith))).symm
    have hκ12 : 0 < κ ^ 12 := by positivity
    have hnN : (N₁ : ℝ) ≤ n := by rw [hn]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hA2 : A ^ 2 / (κ ^ 12 * n ^ 3) ≤ k / 4 / (κ ^ 12 * n) := by
      have hkn : 4 * A ^ 2 ≤ k * n ^ 2 := hkN.trans (by gcongr)
      have e : A ^ 2 / (κ ^ 12 * n ^ 3) = (A ^ 2 / n ^ 2) * (1 / (κ ^ 12 * n)) := by
        field_simp
      have e' : k / 4 / (κ ^ 12 * n) = (k / 4) * (1 / (κ ^ 12 * n)) := by ring
      have h : A ^ 2 / n ^ 2 ≤ k / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
      rw [e, e']; exact mul_le_mul_of_nonneg_right h (by positivity)
    have hlog : Real.log (n + 1) - Real.log n ≤ 1 / n := by
      rw [← Real.log_div (by linarith) hn0.ne']
      have := Real.log_le_sub_one_of_pos (show 0 < (n + 1) / n by positivity)
      have e : (n + 1) / n - 1 = 1 / n := by field_simp; ring
      linarith
    have hkk : 0 ≤ k / 4 / κ ^ 12 := by positivity
    have e1 : k / 4 / κ ^ 12 * (1 / n) = k / 4 / (κ ^ 12 * n) := by field_simp
    rw [show (N₁ : ℝ) + ((m : ℝ) + 1) = n + 1 by rw [hn]; ring]
    rw [hsplit]
    have hmul := mul_le_mul_of_nonneg_left hlog hkk
    rw [e1] at hmul
    have e2 : k / 2 / (κ ^ 12 * n) = 2 * (k / 4 / (κ ^ 12 * n)) := by ring
    have e3 : k / 4 / κ ^ 12 * (Real.log (n + 1) - Real.log N₁) =
        k / 4 / κ ^ 12 * (Real.log n - Real.log N₁) +
          k / 4 / κ ^ 12 * (Real.log (n + 1) - Real.log n) := by ring
    linarith

/-- The ray integrand in the `u`-variable. -/
noncomputable def Ru (β u : ℝ) : ℝ :=
  ‖cexp (6 * ((u : ℂ) + β * I)) * Dc (cexp ((u : ℂ) + β * I) * I)‖ ^ 2

lemma ray_point (β u : ℝ) (hs : 0 < Real.sin β) :
    cexp ((u : ℂ) + β * I) * I =
      pt (-(Real.sin β * Real.exp u)) (Real.cos β / Real.sin β * (Real.sin β * Real.exp u)) := by
  rw [Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  unfold pt
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    ring
  · simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    field_simp
    ring

lemma Ru_eq {β : ℝ} (hs : 0 < Real.sin β) (u : ℝ) :
    Ru β u = Gw (Real.cos β / Real.sin β) (Real.sin β * Real.exp u) / Real.sin β ^ 12 *
      (Real.sin β * Real.exp u) := by
  unfold Ru Gw
  rw [ray_point β u hs, norm_mul, mul_pow, Complex.norm_exp]
  have hre : (6 * ((u : ℂ) + β * I)).re = 6 * u := by simp
  rw [hre]
  have he : Real.exp (6 * u) ^ 2 = Real.exp u ^ 12 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; push_cast; ring_nf
  rw [he]
  field_simp

/-- **Change of variables** `w = sin β · e^u`. -/
lemma integral_Ru_eq {β : ℝ} (hs : 0 < Real.sin β) (hc : 0 < Real.cos β) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    ∫ u in Real.log (a / Real.sin β)..Real.log (b / Real.sin β), Ru β u =
      (∫ w in a..b, Gw (Real.cos β / Real.sin β) w) / Real.sin β ^ 12 := by
  set s := Real.sin β with hsdef
  set κ := Real.cos β / s with hκdef
  have hκ : 0 < κ := div_pos hc hs
  have hcv := intervalIntegral.integral_comp_mul_deriv'
    (a := Real.log (a / s)) (b := Real.log (b / s))
    (f := fun u => s * Real.exp u) (f' := fun u => s * Real.exp u)
    (g := fun w => Gw κ w / s ^ 12)
    (fun u _ => (Real.hasDerivAt_exp u).const_mul s) (continuous_const.mul Real.continuous_exp).continuousOn
    ((continuousOn_Gw hκ).div_const _ |>.mono (by
      rintro _ ⟨u, _, rfl⟩; show 0 < s * Real.exp u; positivity))
  simp only [Function.comp_apply] at hcv
  rw [Real.exp_log (div_pos ha hs), Real.exp_log (div_pos hb hs),
    mul_div_cancel₀ _ hs.ne', mul_div_cancel₀ _ hs.ne'] at hcv
  rw [← intervalIntegral.integral_div, ← hcv]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  exact Ru_eq hs u

/-- `Ru β` is integrable (it is `|Φ₆|²/(2π)²` on the line `Im = β`). -/
lemma integrable_Ru {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < π / 2) : Integrable (Ru β) := by
  obtain ⟨M, hM0, hM⟩ := exists_Delta_bound_exp
  have hc0 : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ⟩
  have hβabs : |β| < π / 2 := by rw [abs_of_nonneg hβ0]; exact hβ
  set Bd : ℝ := 2 * π * (M / Real.cos β ^ 6) * 7 with hBd
  have hbd : ∀ ξ, ‖gS 6 β ξ‖ ≤ Bd := by
    intro ξ
    refine (norm_gS_six_le hM0 hM hβ0 hβ ξ).trans ?_
    rw [hBd]
    have : 0 ≤ 2 * π * (M / Real.cos β ^ 6) := by positivity
    exact mul_le_mul_of_nonneg_left ((min_le_maj hc0 ξ).trans (maj_le_seven _ _)) this
  set R : ℝ := -1 / (2 * π) with hR
  have hR0 : R ≠ 0 := by rw [hR]; have := Real.pi_pos; positivity
  have hgi := (integrable_gS_six hβ0 hβ).comp_mul_left' hR0
  have heq : Ru β = fun u => ‖gS 6 β (R * u)‖ ^ 2 / (2 * π) ^ 2 := by
    funext u
    have hu : ((-2 * π * (R * u) : ℝ) : ℂ) = (u : ℂ) := by
      congr 1; rw [hR]; field_simp
    have hstrip : ((u : ℂ) + β * I) ∈ strip := by
      show |((u : ℂ) + β * I).im| < π / 2; simpa using hβabs
    rw [gS, hu, Phis_eq_strip (le_refl 6) (by norm_num) hstrip, Gs, Ru]
    simp only [norm_mul, mul_pow, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.ofReal_ofNat]
    have hπ : (2 * π) ^ 2 ≠ 0 := by positivity
    field_simp
  rw [heq]
  refine (hgi.norm.const_mul (Bd / (2 * π) ^ 2)).mono'
    (((hgi.aestronglyMeasurable.aemeasurable.norm).pow_const 2).div_const _).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  have h1 := hbd (R * u)
  have h0 := norm_nonneg (gS 6 β (R * u))
  rw [div_le_iff₀ (by positivity)]
  have : ‖gS 6 β (R * u)‖ ^ 2 ≤ Bd * ‖gS 6 β (R * u)‖ := by nlinarith
  calc ‖gS 6 β (R * u)‖ ^ 2 ≤ Bd * ‖gS 6 β (R * u)‖ := this
    _ = Bd / (2 * π) ^ 2 * ‖gS 6 β (R * u)‖ * (2 * π) ^ 2 := by field_simp

lemma Ru_nonneg (β u : ℝ) : 0 ≤ Ru β u := by unfold Ru; positivity

/-- **Ray lower bound.** -/
theorem ray_lower : ∃ a : ℝ, 0 < a ∧ ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ β : ℝ, 0 < β → β < π / 2 →
    ∀ N₂ : ℕ, N₁ ≤ N₂ → Real.cos β / Real.sin β * N₂ ≤ 1 →
      a / (Real.cos β / Real.sin β) ^ 12 * (Real.log N₂ - Real.log N₁) ≤
        ∫ t : ℝ, ‖heckeLambda (6 + t * I)‖ ^ 2 * Real.exp (2 * β * t) := by
  obtain ⟨k, hk0, hk⟩ := exists_Hh_lower
  obtain ⟨A, hA0, hA⟩ := exists_Dc_lip
  set N₁ : ℕ := ⌈4 * A ^ 2 / k⌉₊ + 1 with hN₁def
  have hN₁ : 1 ≤ N₁ := by omega
  have hN₁r : (1 : ℝ) ≤ N₁ := by exact_mod_cast hN₁
  have hkN : 4 * A ^ 2 ≤ k * (N₁ : ℝ) ^ 2 := by
    have h1 : 4 * A ^ 2 / k ≤ N₁ := by
      have := Nat.le_ceil (4 * A ^ 2 / k)
      rw [hN₁def]; push_cast; linarith
    have h2 : (N₁ : ℝ) ≤ (N₁ : ℝ) ^ 2 := by nlinarith
    rw [div_le_iff₀ hk0] at h1
    nlinarith
  refine ⟨2 * π * (k / 4), by positivity, N₁, hN₁, fun β hβ0 hβ N₂ hN₂ hκN => ?_⟩
  have hs : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ0 (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ⟩
  set κ := Real.cos β / Real.sin β with hκdef
  have hκ : 0 < κ := div_pos hc hs
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN₂
  have hsum := sum_lower hk0 hA0 hk hA hκ hN₁ hkN m (by push_cast at hκN; exact hκN)
  push_cast
  have hlog : 0 ≤ Real.log ((N₁ : ℝ) + m) - Real.log N₁ := by
    have := Real.log_le_log (by linarith) (show (N₁ : ℝ) ≤ N₁ + m by
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    linarith
  have hG0 : 0 ≤ ∫ w in (N₁ : ℝ)..(N₁ : ℝ) + m, Gw κ w :=
    le_trans (by positivity) hsum
  -- ray integral ≥ the block integral
  have hP := weighted_parseval hβ0.le hβ
  have hcv := integral_Ru_eq hs hc (a := N₁) (b := (N₁ : ℝ) + m) (by linarith) (by linarith)
  have hle : Real.log (N₁ / Real.sin β) ≤ Real.log (((N₁ : ℝ) + m) / Real.sin β) :=
    Real.log_le_log (by positivity) (by
      gcongr; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  have hsub : ∫ u in Real.log (N₁ / Real.sin β)..Real.log (((N₁ : ℝ) + m) / Real.sin β), Ru β u ≤
      ∫ u, Ru β u := by
    rw [intervalIntegral.integral_of_le hle]
    exact setIntegral_le_integral (integrable_Ru hβ0.le hβ)
      (Eventually.of_forall fun u => Ru_nonneg β u)
  have hs12 : Real.sin β ^ 12 ≤ 1 := pow_le_one₀ hs.le (Real.sin_le_one β)
  have hdiv : (∫ w in (N₁ : ℝ)..(N₁ : ℝ) + m, Gw κ w) ≤
      (∫ w in (N₁ : ℝ)..(N₁ : ℝ) + m, Gw κ w) / Real.sin β ^ 12 := by
    rw [le_div_iff₀ (by positivity)]
    exact mul_le_of_le_one_right hG0 hs12
  have hRu : ∫ u, Ru β u = ∫ u : ℝ, ‖cexp (6 * ((u : ℂ) + β * I)) *
      Dc (cexp ((u : ℂ) + β * I) * I)‖ ^ 2 := rfl
  rw [hP, ← hRu]
  calc 2 * π * (k / 4) / κ ^ 12 * (Real.log ((N₁ : ℝ) + m) - Real.log N₁)
      = 2 * π * (k / 4 / κ ^ 12 * (Real.log ((N₁ : ℝ) + m) - Real.log N₁)) := by ring
    _ ≤ 2 * π * ∫ u, Ru β u := by
      gcongr
      exact hsum.trans (hdiv.trans (le_of_eq hcv.symm |>.trans hsub))

end RamanujanTau.CriticalMeanSquareLower
