/-
# The Riemann–von Mangoldt formula for `L(Δ,s)`

`N(T) = (T/π) log(T/(2πe)) + O(log T)`  (`riemann_von_mangoldt`).

For a non-ordinate `T` (`rvm_nonordinate`):
`π N(T) = Re ∫₀ᵀ φ(σ₁+iy) dy − Im ∫₆^{σ₁} φ(x+iT) dx` (`pi_count_eq`, `sum_order_eq_zeroCount`),
`φ = −log 2π + ψ + L'/L` (`phi_eq`), the `ψ` part is `∫₀ᵀ Re ψ(6+iy) dy = T log T − T + O(log T)`
(`gamma_cauchy`, `integral_re_digamma_six`), the vertical `L'/L` part is `≤ π` (`Re L ≥ 1/2` on
`Re s = σ₁`) and the horizontal one is `O(log T)` (`backlund`).  A general `T` is moved to a
non-ordinate `T' ∈ (T, T+1)` at cost `N(T+1) − N(T) = O(log T)` (`zeroCount_window`).
-/
import RamanujanTau.ZeroCountRvM.Decomp
import RamanujanTau.ZeroCountRvM.Backlund
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

namespace RamanujanTau.ZeroCountRvM

open Complex Set Filter Topology Metric intervalIntegral MeasureTheory
open RamanujanTau.HeckeL RamanujanTau.HeckeZeros RamanujanTau.ZeroCount
open scoped ComplexConjugate Real Interval

/-- `ℓ = L'/L`. -/
noncomputable def ell (s : ℂ) : ℂ := deriv tauL s / tauL s

lemma continuousAt_ell {s : ℂ} (hs : tauL s ≠ 0) : ContinuousAt ell s :=
  continuous_deriv_tauL.continuousAt.div tauLSeries_entire.continuous.continuousAt hs

/-- The vertical `L'/L` contribution: `|Re ∫₀ᵀ ℓ(σ₁+iy) dy| ≤ π` when `Re L ≥ 1/2` on the line. -/
lemma abs_re_integral_ell_vert {σ₁ T : ℝ} (hT : 0 ≤ T) (hre : ∀ y : ℝ, 1 / 2 ≤ (tauL (σ₁ + y * I)).re) :
    |(∫ y in (0 : ℝ)..T, ell (σ₁ + y * I)).re| ≤ π := by
  have hne : ∀ y : ℝ, tauL (σ₁ + y * I) ≠ 0 := by
    intro y h; have := hre y; rw [h] at this; simp at this; linarith
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => tauL (σ₁ + y * I)) (deriv tauL (σ₁ + y * I) * I) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => (σ₁ : ℂ) + (y : ℂ) * I) I y := by
      simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (σ₁ : ℂ)
    exact (tauLSeries_entire _).hasDerivAt.comp y h1
  have h := abs_im_integral_logDeriv_le (f := fun y : ℝ => tauL (σ₁ + y * I))
    (f' := fun y : ℝ => deriv tauL (σ₁ + y * I) * I) 0 0 T hT (fun y _ => hd y)
    ((continuous_deriv_tauL.comp (by fun_prop)).mul continuous_const).continuousOn
    (fun y _ => hne y) ∅ le_rfl (fun y _ h0 => by
      have := hre y; rw [h0] at this; norm_num at this)
  simp only [Finset.card_empty, Nat.cast_zero, zero_add, mul_one] at h
  have heq : ∫ y in (0 : ℝ)..T, deriv tauL (σ₁ + y * I) * I / tauL (σ₁ + y * I) =
      I * ∫ y in (0 : ℝ)..T, ell (σ₁ + y * I) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr; intro y _
    simp only [ell]; ring
  rw [heq, I_mul_im] at h
  exact h

/-- **Riemann–von Mangoldt at a non-ordinate `T ≥ 1`.** -/
theorem rvm_nonordinate : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
    (∀ u : ℂ, tauL u = 0 → 11 / 2 < u.re → u.re < 13 / 2 → u.im ≠ T) →
    |π * (zeroCount T : ℝ) - (T * Real.log T - T - T * Real.log (2 * π))| ≤
      C * Real.log (T + 5) := by
  obtain ⟨σ₁, hσ₁, hre, CB, hCB0, hCB⟩ := backlund
  refine ⟨π + CB + 70, by positivity, fun T hT1 hnon => ?_⟩
  have hT0 : 0 < T := by linarith
  -- non-vanishing on the top side
  have hΛT : ∀ x : ℝ, heckeLambda (x + T * I) ≠ 0 := by
    intro x h0
    have h1 : 11 / 2 ≤ x := by
      by_contra h; push Not at h
      exact heckeLambda_ne_zero_of_lt (by simpa using h) h0
    have h2 : x ≤ 13 / 2 := by
      by_contra h; push Not at h
      exact heckeLambda_ne_zero_of_gt (by simpa using h) h0
    have hpos : 0 < ((x : ℂ) + T * I).re := by simp; linarith
    have htau := (lambda_zero_iff hpos).mp h0
    have hmem : ((x : ℂ) + T * I) ∈ zeroSet 0 T := by
      rw [zeroSet_eq_of_nonneg le_rfl]; exact ⟨htau, by simpa using hT0, by simp⟩
    obtain ⟨_, h3, h4, _, _⟩ := hmem
    exact hnon _ htau h3 h4 (by simp)
  have htop : ∀ x ∈ Icc (6 : ℝ) σ₁, tauL (x + T * I) ≠ 0 := by
    intro x hx h0
    have hpos : 0 < ((x : ℂ) + T * I).re := by simp; linarith [hx.1]
    exact hΛT x ((lambda_zero_iff hpos).mpr h0)
  obtain ⟨S, hS, hpi⟩ := pi_count_eq hσ₁ hT0 hΛT
  rw [sum_order_eq_zeroCount hσ₁ hT0 hnon S hS] at hpi
  -- decompose the vertical integral
  set c : ℂ := (Real.log (2 * π) : ℂ)
  have hvne : ∀ y : ℝ, tauL (σ₁ + y * I) ≠ 0 :=
    fun y => tauL_ne_zero_of_gt (by simp; linarith)
  have hcontV : Continuous fun y : ℝ => ell (σ₁ + y * I) := by
    rw [continuous_iff_continuousAt]; intro y
    exact ContinuousAt.comp (g := ell) (continuousAt_ell (hvne y)) (by fun_prop)
  have hψV := continuous_digamma_vert (σ := σ₁) (by linarith)
  have hV : ∫ y in (0 : ℝ)..T, phi (σ₁ + y * I) =
      (∫ y in (0 : ℝ)..T, (-c)) + (∫ y in (0 : ℝ)..T, digamma (σ₁ + y * I)) +
        ∫ y in (0 : ℝ)..T, ell (σ₁ + y * I) := by
    have h0 : ∫ y in (0 : ℝ)..T, phi (σ₁ + y * I) =
        ∫ y in (0 : ℝ)..T, ((-c + digamma (σ₁ + y * I)) + ell (σ₁ + y * I)) := by
      apply integral_congr; intro y _
      simp only []
      rw [phi_eq (by simp; linarith) (hvne y)]; rfl
    rw [h0, intervalIntegral.integral_add (f := fun y : ℝ => -c + digamma (σ₁ + y * I))
      (g := fun y : ℝ => ell (σ₁ + y * I))
      ((continuous_const.add hψV).intervalIntegrable _ _)
      (hcontV.intervalIntegrable _ _),
      intervalIntegral.integral_add (f := fun _ : ℝ => -c) (g := fun y : ℝ => digamma (σ₁ + y * I))
        (continuous_const.intervalIntegrable _ _) (hψV.intervalIntegrable _ _)]
  -- decompose the horizontal integral
  have hcontH : ContinuousOn (fun x : ℝ => ell (x + T * I)) (Icc 6 σ₁) := by
    intro x hx
    exact (ContinuousAt.comp (g := ell) (f := fun x : ℝ => (x : ℂ) + T * I)
      (continuousAt_ell (htop x hx)) (by fun_prop)).continuousWithinAt
  have hψH := continuousOn_digamma_horiz (a := 6) (b := σ₁) (T := T) (by norm_num)
  have h6σ : (6 : ℝ) ≤ σ₁ := by linarith
  have hiψ : IntervalIntegrable (fun x : ℝ => digamma (x + T * I)) volume 6 σ₁ :=
    (hψH.mono (by rw [uIcc_of_le h6σ])).intervalIntegrable
  have hiℓ : IntervalIntegrable (fun x : ℝ => ell (x + T * I)) volume 6 σ₁ :=
    (hcontH.mono (by rw [uIcc_of_le h6σ])).intervalIntegrable
  have hH : ∫ x in (6 : ℝ)..σ₁, phi (x + T * I) =
      (∫ x in (6 : ℝ)..σ₁, (-c)) + (∫ x in (6 : ℝ)..σ₁, digamma (x + T * I)) +
        ∫ x in (6 : ℝ)..σ₁, ell (x + T * I) := by
    have h0 : ∫ x in (6 : ℝ)..σ₁, phi (x + T * I) =
        ∫ x in (6 : ℝ)..σ₁, ((-c + digamma (x + T * I)) + ell (x + T * I)) := by
      apply integral_congr; intro x hx
      rw [uIcc_of_le h6σ] at hx
      simp only []
      rw [phi_eq (by simp; linarith [hx.1]) (htop x hx)]; rfl
    rw [h0, intervalIntegral.integral_add (f := fun x : ℝ => -c + digamma (x + T * I))
      (g := fun x : ℝ => ell (x + T * I))
      ((continuous_const.intervalIntegrable 6 σ₁).add hiψ) hiℓ,
      intervalIntegral.integral_add (f := fun _ : ℝ => -c) (g := fun x : ℝ => digamma (x + T * I))
        (continuous_const.intervalIntegrable 6 σ₁) hiψ]
  rw [hV, hH] at hpi
  simp only [intervalIntegral.integral_const, add_re, add_im] at hpi
  have hcre : (-c).re = -Real.log (2 * π) := by simp [c]
  have hcim : (-c).im = 0 := by simp [c]
  simp only [real_smul, mul_re, mul_im, ofReal_re, ofReal_im, hcre, hcim, zero_mul, mul_zero,
    sub_zero, add_zero, zero_add] at hpi
  -- the pieces
  have hG := gamma_cauchy (T := T) h6σ
  have hGa := integral_re_digamma_six hT1
  have hLv := abs_re_integral_ell_vert (σ₁ := σ₁) hT0.le hre
  have hLh := hCB T htop
  have hLh' : |(∫ x in (6 : ℝ)..σ₁, ell (x + T * I)).im| ≤ CB * Real.log (|T| + 2) := hLh
  rw [abs_of_pos hT0] at hLh'
  have hlog : Real.log (T + 2) ≤ Real.log (T + 5) := Real.log_le_log (by linarith) (by linarith)
  have hlog1 : 1 ≤ Real.log (T + 5) := by
    have h : Real.exp 1 ≤ T + 5 := by linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) h
    rwa [Real.log_exp] at this
  have hpi' : π * (zeroCount T : ℝ) = (T - 0) * (-Real.log (2 * π)) +
      ((∫ y in (0 : ℝ)..T, (digamma (6 + y * I)).re) +
        ((∫ y in (0 : ℝ)..T, ell (σ₁ + y * I)).re - (∫ x in (6 : ℝ)..σ₁, ell (x + T * I)).im)) := by
    rw [hpi, ← hG]; ring
  rw [hpi']
  set G := ∫ y in (0 : ℝ)..T, (digamma (6 + y * I)).re
  set Ev := (∫ y in (0 : ℝ)..T, ell (σ₁ + y * I)).re
  set Eh := (∫ x in (6 : ℝ)..σ₁, ell (x + T * I)).im
  have hEv := abs_le.mp hLv
  have hEh := abs_le.mp hLh'
  have hGG := abs_le.mp hGa
  rw [abs_le]
  constructor <;> nlinarith [Real.pi_pos]

lemma log_two_pi_le : Real.log (2 * π) ≤ 7 := by
  have := Real.log_le_sub_one_of_pos (x := 2 * π) (by positivity)
  linarith [Real.pi_le_four]

/-- **Riemann–von Mangoldt formula for `L(Δ,s)`**:
`N(T) = (T/π) log(T/(2πe)) + O(log T)` for `T ≥ 2`. -/
theorem riemann_von_mangoldt : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
    |(zeroCount T : ℝ) - T / π * Real.log (T / (2 * π * Real.exp 1))| ≤ C * Real.log T := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := rvm_nonordinate
  obtain ⟨Cw, hCw0, -, hCw⟩ := zeroCount_window
  refine ⟨2 * Cw + 3 * C₁ / π + 16 / π, by positivity, fun T hT2 => ?_⟩
  have hT0 : 0 < T := by linarith
  -- a non-ordinate `T' ∈ (T, T+1)`
  have hfin : ((fun u : ℂ => u.im) '' zeroSet T (T + 1)).Finite := (zeroSet_finite T (T + 1)).image _
  obtain ⟨T', hT'mem, hT'not⟩ := (Set.Ioo_infinite (by linarith : T < T + 1)).exists_notMem_finite hfin
  have hnon : ∀ u : ℂ, tauL u = 0 → 11 / 2 < u.re → u.re < 13 / 2 → u.im ≠ T' := by
    intro u h0 h1 h2 h3
    apply hT'not
    exact ⟨u, ⟨h0, h1, h2, by rw [h3]; exact hT'mem.1, by rw [h3]; exact hT'mem.2.le⟩, h3⟩
  have hT'1 : 1 ≤ T' := by linarith [hT'mem.1]
  have hR := hC₁ T' hT'1 hnon
  -- `N(T) ≤ N(T') ≤ N(T) + Cw log(T+2)`
  have hmono1 : (zeroCount T : ℝ) ≤ zeroCount T' := by
    have := zeroCountAB_add (le_of_lt hT0) hT'mem.1.le
    unfold zeroCount; rw [this]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) (zeroCountAB T T')]
  have hmono2 : (zeroCount T' : ℝ) ≤ zeroCount (T + 1) := by
    have := zeroCountAB_add (le_of_lt (by linarith [hT'mem.1] : (0 : ℝ) < T')) hT'mem.2.le
    unfold zeroCount; rw [this]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) (zeroCountAB T' (T + 1))]
  have hwin := hCw T hT0.le
  -- logs
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT2
  have hl2 : (2 : ℝ) / 3 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hp2 : Real.log (T ^ 2) = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
  have hp3 : Real.log (T ^ 3) = 3 * Real.log T := by rw [Real.log_pow]; push_cast; ring
  have hlogT2 : Real.log (T + 2) ≤ 2 * Real.log T := by
    rw [← hp2]; apply Real.log_le_log (by linarith); nlinarith
  have hlogT1 : Real.log (T + 1) ≤ 2 * Real.log T := by
    rw [← hp2]; apply Real.log_le_log (by linarith); nlinarith
  have hlogT5 : Real.log (T' + 5) ≤ 3 * Real.log T := by
    rw [← hp3]; apply Real.log_le_log (by linarith [hT'mem.1])
    nlinarith [hT'mem.2]
  -- main-term comparison
  have hmain : ∀ x : ℝ, 0 < x → x / π * Real.log (x / (2 * π * Real.exp 1)) =
      (x * Real.log x - x - x * Real.log (2 * π)) / π := by
    intro x hx
    rw [Real.log_div hx.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp]
    field_simp; ring
  rw [hmain T hT0]
  have hTT' : T < T' := hT'mem.1
  have hT'T : T' < T + 1 := hT'mem.2
  have hd1 : 0 ≤ T' * Real.log T' - T * Real.log T := by
    have : Real.log T ≤ Real.log T' := Real.log_le_log hT0 hTT'.le
    have h0 : 0 ≤ Real.log T := by linarith
    nlinarith
  have hd2 : T' * Real.log T' - T * Real.log T ≤ Real.log (T + 1) + 1 := by
    have hq : Real.log T' - Real.log T ≤ T' / T - 1 := by
      rw [← Real.log_div (by linarith) hT0.ne']
      exact Real.log_le_sub_one_of_pos (by positivity)
    have hTq : T * (T' / T - 1) = T' - T := by field_simp
    have hq' : T * (Real.log T' - Real.log T) ≤ T' - T := by
      have := mul_le_mul_of_nonneg_left hq hT0.le
      linarith
    have hlT' : Real.log T' ≤ Real.log (T + 1) := Real.log_le_log (by linarith) hT'T.le
    have hlT'0 : 0 ≤ Real.log T' := Real.log_nonneg (by linarith)
    have : (T' - T) * Real.log T' ≤ Real.log T' := by
      have : T' - T ≤ 1 := by linarith
      nlinarith
    nlinarith
  have hl2π : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hl2π' := log_two_pi_le
  have hpi := Real.pi_pos
  have hR' := abs_le.mp hR
  have hprod1 : 0 ≤ (T' - T) * Real.log (2 * π) := mul_nonneg (by linarith) hl2π
  have hprod2 : (T' - T) * Real.log (2 * π) ≤ 7 := by nlinarith
  have hz1 : π * (zeroCount T : ℝ) ≤ π * (zeroCount T' : ℝ) := mul_le_mul_of_nonneg_left hmono1 hpi.le
  have hz2 : π * (zeroCount T' : ℝ) ≤ π * (zeroCount T : ℝ) + π * Cw * Real.log (T + 2) := by
    have := mul_le_mul_of_nonneg_left (show (zeroCount T' : ℝ) ≤ zeroCount T + Cw * Real.log (T + 2)
      by linarith) hpi.le
    linarith
  have hlT1 : 0 ≤ Real.log (T + 1) := Real.log_nonneg (by linarith)
  have hCwl : 0 ≤ π * Cw * Real.log (T + 2) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ T + 2 by linarith); positivity
  have hX : |π * (zeroCount T : ℝ) - (T * Real.log T - T - T * Real.log (2 * π))| ≤
      π * Cw * Real.log (T + 2) + C₁ * Real.log (T' + 5) + (Real.log (T + 1) + 9) := by
    have hM : (T' * Real.log T' - T' - T' * Real.log (2 * π)) -
        (T * Real.log T - T - T * Real.log (2 * π)) =
        (T' * Real.log T' - T * Real.log T) - (T' - T) - (T' - T) * Real.log (2 * π) := by ring
    rw [abs_le]; constructor <;> linarith
  have key : |(zeroCount T : ℝ) - (T * Real.log T - T - T * Real.log (2 * π)) / π| ≤
      Cw * Real.log (T + 2) + C₁ * Real.log (T' + 5) / π + (Real.log (T + 1) + 9) / π := by
    have e : (zeroCount T : ℝ) - (T * Real.log T - T - T * Real.log (2 * π)) / π =
        (π * (zeroCount T : ℝ) - (T * Real.log T - T - T * Real.log (2 * π))) / π := by
      field_simp
    have e2 : Cw * Real.log (T + 2) + C₁ * Real.log (T' + 5) / π + (Real.log (T + 1) + 9) / π =
        (π * Cw * Real.log (T + 2) + C₁ * Real.log (T' + 5) + (Real.log (T + 1) + 9)) / π := by
      field_simp
    rw [e, e2, abs_div, abs_of_pos hpi]
    exact div_le_div_of_nonneg_right hX hpi.le
  refine key.trans ?_
  have hlT0 : 0 ≤ Real.log T := by linarith
  have e1 : Cw * Real.log (T + 2) ≤ 2 * Cw * Real.log T := by
    have := mul_le_mul_of_nonneg_left hlogT2 hCw0; linarith
  have e2 : C₁ * Real.log (T' + 5) / π ≤ 3 * C₁ / π * Real.log T := by
    have : 3 * C₁ / π * Real.log T = (3 * C₁ * Real.log T) / π := by ring
    rw [this]
    exact div_le_div_of_nonneg_right (by have := mul_le_mul_of_nonneg_left hlogT5 hC₁0; linarith)
      hpi.le
  have e3 : (Real.log (T + 1) + 9) / π ≤ 16 / π * Real.log T := by
    have : 16 / π * Real.log T = (16 * Real.log T) / π := by ring
    rw [this]; exact div_le_div_of_nonneg_right (by linarith) hpi.le
  have : (2 * Cw + 3 * C₁ / π + 16 / π) * Real.log T =
      2 * Cw * Real.log T + 3 * C₁ / π * Real.log T + 16 / π * Real.log T := by ring
  linarith

/-- **Lower bound `N(T) ≫ T log T`**: `N(T) ≥ (T/(2π)) log T` for all large `T`. -/
theorem zeroCount_ge_T_log_T : ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
    T / (2 * π) * Real.log T ≤ zeroCount T := by
  obtain ⟨C, hC0, hC⟩ := riemann_von_mangoldt
  set K := Real.log (2 * π) + 1 with hK
  have hK0 : 0 ≤ K := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * π by linarith [Real.pi_gt_three]); linarith
  refine ⟨max (max 2 (Real.exp (4 * K))) (4 * π * C), le_max_of_le_left (le_max_left _ _),
    fun T hT => ?_⟩
  have hT2 : 2 ≤ T := le_trans (le_max_of_le_left (le_max_left _ _)) hT
  have hTe : Real.exp (4 * K) ≤ T := le_trans (le_max_of_le_left (le_max_right _ _)) hT
  have hTC : 4 * π * C ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : 0 < T := by linarith
  have hlogT : 4 * K ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos _) hTe; rwa [Real.log_exp] at this
  have hlT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have h := abs_le.mp (hC T hT2)
  have hmain : T / π * Real.log (T / (2 * π * Real.exp 1)) = T / π * (Real.log T - K) := by
    rw [Real.log_div hT0.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp, hK]
  rw [hmain] at h
  have hpi := Real.pi_pos
  set A : ℝ := T * Real.log T / π with hA
  have eA : T / π * (Real.log T - K) = A - T / π * K := by rw [hA]; ring
  have h1 : T / π * K ≤ A / 4 := by
    have : T / π * K ≤ T / π * (Real.log T / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : T / π * (Real.log T / 4) = A / 4 := by rw [hA]; ring
    linarith
  have h2 : C * Real.log T ≤ A / 4 := by
    have e : A / 4 = (T / (4 * π)) * Real.log T := by rw [hA]; field_simp
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hlT0
    rw [le_div_iff₀ (by positivity)]; linarith
  have e2 : T / (2 * π) * Real.log T = A / 2 := by rw [hA]; field_simp
  rw [e2]
  linarith

end RamanujanTau.ZeroCountRvM
