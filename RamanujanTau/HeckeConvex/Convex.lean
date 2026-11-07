/-
# The convexity bound for `L(Δ,s)`

Unnormalized coordinates: critical line `Re s = 6`, absolute convergence for `Re s > 13/2`
(`LSeriesSummable_tau_of_gt_13_2`).  Fix `0 < ε ≤ 1/2` and put `a = 11/2 − ε`, `b = 13/2 + ε`.
The Phragmén–Lindelöf function is

    f_ε(s) = L(Δ,s) Γ(s/2) / Γ((13 + 2ε − s)/2),

whose `Γ`-weight has modulus `≍ |t|^{σ − b}` (slope `1` in `σ`).

* Right edge `Re s = b`: `(13+2ε−s)/2 = conj(s/2)`, so the weight has modulus `1` and
  `‖L(Δ,s)‖ ≤ ∑ |τ(n)| n^{−b}` (`fC_right`).
* Left edge `Re s = a`: the functional equation gives
  `L(Δ,s) = (2π)^{2s−12} Γ(12−s)/Γ(s) · L(Δ,12−s)` with `Re(12−s) = b`. Both `Γ`-pairs have
  real parts differing by `θ = 1+2ε`: `12 − s = s̄ + θ` and `(13+2ε−s)/2 = conj(s/2) + θ`, so
  `Stirling.norm_Gamma_add_le` and `Stirling.norm_Gamma_mul_rpow_le_add` bound the product by
  `2e¹⁰‖s‖^θ · e¹⁰‖s/2‖^{−θ} = 2^{1+θ}e²⁰ ≤ 8e²⁰` (`fC_left`).
* Inside the strip, `f_ε` grows at most like `e^{2π|t|}` (`fC_growth`), so `pl_strip`
  bounds `f_ε` on the closed strip (`fC_bound`).
* On a line `a ≤ σ ≤ b`, `(13+2ε−s)/2 = conj(s/2) + (b − σ)`, so
  `‖L(Δ,s)‖ ≤ 2e¹⁰ C ‖s/2‖^{b−σ}` (`tauL_line`), the convexity bound.
-/
import RamanujanTau.HeckeConvex.Summable
import RamanujanTau.Stirling.GammaRatio
import RamanujanTau.RankinSharp.PL
import RamanujanTau.RankinError.GammaBound

set_option autoImplicit false

namespace RamanujanTau.HeckeConvex

open Complex LSeries Set Filter Topology
open RamanujanTau.HeckeL
open scoped Real

/-! ### `L(Δ,s)` on `Re s > 13/2` -/

lemma abscissaOfAbsConv_tau_le : abscissaOfAbsConv tauC ≤ ((13 / 2 : ℝ) : EReal) :=
  abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    LSeriesSummable_tau_of_gt_13_2 (by simpa using hy)

/-- `tauL = L(Δ,·)` on the whole half-plane of absolute convergence `Re s > 13/2`. -/
theorem tauL_eq_LSeries_of_gt {s : ℂ} (hs : 13 / 2 < s.re) : tauL s = LSeries tauC s := by
  set U : Set ℂ := {z : ℂ | 13 / 2 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ tauL U :=
    tauLSeries_entire.differentiableOn.analyticOnNhd hUo
  have hg : AnalyticOnNhd ℂ (LSeries tauC) U := by
    refine (LSeries_analyticOnNhd tauC).mono fun z hz => ?_
    simp only [hU, mem_setOf_eq] at hz ⊢
    exact lt_of_le_of_lt abscissaOfAbsConv_tau_le (by exact_mod_cast hz)
  have hpc : IsPreconnected U := (convex_halfSpace_re_gt (13 / 2 : ℝ)).isPreconnected
  have h8 : (8 : ℂ) ∈ U := by simp [hU]; norm_num
  have hev : tauL =ᶠ[𝓝 (8 : ℂ)] LSeries tauC := by
    have ho : IsOpen {z : ℂ | 7 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (by simp; norm_num)] with z hz
    exact tauL_eq_LSeries hz
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hpc h8 hev hs

lemma norm_LSeries_le' {f : ℕ → ℂ} {σ : ℝ} (hσ : LSeriesSummable f σ) {s : ℂ} (h : σ ≤ s.re) :
    ‖LSeries f s‖ ≤ ∑' n, ‖LSeries.term f σ n‖ := by
  have hs : LSeriesSummable f s := hσ.of_re_le_re (by simpa using h)
  refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
  exact hs.norm.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re f (by simpa using h) n)
    hσ.norm

/-- `‖L(Δ,s)‖ ≤ ∑ |τ(n)| n^{−σ}` for `Re s ≥ σ > 13/2`. -/
lemma exists_norm_tauL_le {σ : ℝ} (hσ : 13 / 2 < σ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℂ, σ ≤ s.re → ‖tauL s‖ ≤ D := by
  have hsum : LSeriesSummable tauC (σ : ℂ) := LSeriesSummable_tau_of_gt_13_2 (by simpa using hσ)
  refine ⟨∑' n, ‖LSeries.term tauC σ n‖, tsum_nonneg fun _ => norm_nonneg _, fun s hs => ?_⟩
  rw [tauL_eq_LSeries_of_gt (by linarith)]
  exact norm_LSeries_le' hsum hs

/-! ### Elementary `Γ` facts -/

/-- `1/Γ(w) ≪ e^{π|Im w|}` uniformly for `0 ≤ Re w ≤ 10` (all `Im w`). -/
lemma exists_norm_inv_Gamma_le_strip : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 10 →
    ‖(Complex.Gamma w)⁻¹‖ ≤ C * Real.exp (π * |w.im|) := by
  obtain ⟨C1, hC1, h1⟩ := RamanujanTau.RankinError.exists_norm_inv_Gamma_le (A := 1 / 2)
    (by norm_num)
  have hc : Continuous fun w : ℂ => (Complex.Gamma w)⁻¹ := by
    simpa [one_div] using Complex.differentiable_one_div_Gamma.continuous
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 11).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C1 M, le_max_of_le_left hC1, fun w h0 h10 => ?_⟩
  have he : 1 ≤ Real.exp (π * |w.im|) := Real.one_le_exp (by positivity)
  rcases le_or_gt 1 |w.im| with hi | hi
  · calc ‖(Complex.Gamma w)⁻¹‖ ≤ C1 * Real.exp (π * |w.im|) := h1 w (by linarith) hi
      _ ≤ max C1 M * Real.exp (π * |w.im|) := by gcongr; exact le_max_left _ _
  · have hw : w ∈ Metric.closedBall (0 : ℂ) 11 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
      rw [abs_of_nonneg h0]; linarith
    have := hM w hw
    have hM0 : 0 ≤ M := (norm_nonneg _).trans this
    calc ‖(Complex.Gamma w)⁻¹‖ ≤ M := this
      _ ≤ max C1 M := le_max_right _ _
      _ ≤ max C1 M * Real.exp (π * |w.im|) := le_mul_of_one_le_right (by positivity) he

@[simp] lemma re_conj_half (s : ℂ) : (starRingEnd ℂ (s / 2)).re = s.re / 2 := by
  rw [map_div₀, map_ofNat]; simp

@[simp] lemma im_conj_half (s : ℂ) : (starRingEnd ℂ (s / 2)).im = -(s.im / 2) := by
  rw [map_div₀, map_ofNat]; simp; ring

/-- `(13+2ε−s)/2 = conj(s/2) + θ`, `θ = (13+2ε−2 Re s)/2`. -/
lemma half_eq_conj_add (ε : ℝ) (s : ℂ) :
    (13 + 2 * (ε : ℂ) - s) / 2 = starRingEnd ℂ (s / 2) + (((13 + 2 * ε - 2 * s.re) / 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.add_re, re_conj_half, Complex.ofReal_re]; simp; ring
  · simp only [Complex.add_im, im_conj_half, Complex.ofReal_im]; simp; ring

/-- `12 − s = conj s + (12 − 2 Re s)`. -/
lemma twelve_sub_eq_conj_add (s : ℂ) :
    12 - s = starRingEnd ℂ s + ((12 - 2 * s.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp <;> ring

lemma norm_two_pi_cpow' (s : ℂ) : ‖(2 * π : ℂ) ^ s‖ = (2 * π) ^ s.re := by
  have h : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
  rw [h, norm_cpow_eq_rpow_re_of_pos (by positivity)]

/-! ### The Phragmén–Lindelöf function -/

/-- `f_ε(s) = L(Δ,s) Γ(s/2) / Γ((13+2ε−s)/2)`. -/
noncomputable def fC (ε : ℝ) (s : ℂ) : ℂ :=
  tauL s * Complex.Gamma (s / 2) * (Complex.Gamma ((13 + 2 * ε - s) / 2))⁻¹

lemma differentiableOn_fC (ε : ℝ) : DifferentiableOn ℂ (fC ε) {s : ℂ | 4 < s.re} := by
  intro s hs
  simp only [mem_setOf_eq] at hs
  have hG : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) s := by
    refine (Complex.differentiableAt_Gamma (s / 2) fun m h => ?_).comp s
      (differentiableAt_id.div_const (2 : ℂ))
    have := congrArg re h; simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hG2 : DifferentiableAt ℂ (fun s : ℂ => (Complex.Gamma ((13 + 2 * ε - s) / 2))⁻¹) s := by
    have := (Complex.differentiable_one_div_Gamma ((13 + 2 * ε - s) / 2)).comp s
      (((differentiableAt_const (13 + 2 * (ε : ℂ))).sub differentiableAt_id).div_const (2 : ℂ))
    simpa [Function.comp_def] using this
  unfold fC
  exact (((tauLSeries_entire s).mul hG).mul hG2).differentiableWithinAt

lemma fC_growth {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    ∃ K L : ℝ, ∀ s : ℂ, 11 / 2 - ε < s.re → s.re < 13 / 2 + ε → 1 ≤ |s.im| →
      ‖fC ε s‖ ≤ K * Real.exp (L * |s.im|) := by
  obtain ⟨C0, hC0, hC⟩ := exists_norm_inv_Gamma_le_strip
  obtain ⟨L0, hL0⟩ := heckeLambda_bdd_strip 5 7
  have hcont : ContinuousOn Real.Gamma (Icc (5 / 2 : ℝ) (7 / 2)) := by
    intro x hx
    refine (Real.differentiableAt_Gamma (fun m => ?_)).continuousAt.continuousWithinAt
    intro h; have := hx.1; rw [h] at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith
  obtain ⟨G, hG⟩ := (isCompact_Icc).exists_bound_of_continuousOn hcont
  refine ⟨(2 * π) ^ (7 : ℝ) * C0 * |L0| * |G| * C0, 2 * π, fun s h1 h2 _ => ?_⟩
  have hre5 : 5 ≤ s.re := by linarith
  have hre7 : s.re ≤ 7 := by linarith
  -- `tauL`
  have hT : ‖tauL s‖ ≤ (2 * π) ^ (7 : ℝ) * (C0 * Real.exp (π * |s.im|)) * |L0| := by
    unfold tauL
    rw [norm_mul, norm_mul, norm_two_pi_cpow']
    have hp : (2 * π) ^ s.re ≤ (2 * π) ^ (7 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hre7
    have hg := hC s (by linarith) (by linarith)
    have hl := (hL0 s hre5 hre7).trans (le_abs_self L0)
    gcongr
  -- `Γ(s/2)`
  have hg1 : ‖Complex.Gamma (s / 2)‖ ≤ |G| := by
    refine (RamanujanTau.RankinError.norm_Gamma_le_Gamma_re (by simp; linarith)).trans ?_
    have := hG (s / 2).re ⟨by simp; linarith, by simp; linarith⟩
    rw [Real.norm_eq_abs] at this
    exact ((le_abs_self _).trans this).trans (le_abs_self G)
  -- `1/Γ((13+2ε−s)/2)`
  have hg2 : ‖(Complex.Gamma ((13 + 2 * ε - s) / 2))⁻¹‖ ≤ C0 * Real.exp (π * |s.im|) := by
    refine (hC _ (by simp; linarith) (by simp; linarith)).trans ?_
    have him : |((13 + 2 * (ε : ℂ) - s) / 2).im| = |s.im| / 2 := by simp [abs_div]
    rw [him]
    gcongr
    have : 0 ≤ |s.im| := abs_nonneg _
    linarith
  have hexp : Real.exp (2 * π * |s.im|) = Real.exp (π * |s.im|) * Real.exp (π * |s.im|) := by
    rw [← Real.exp_add]; ring_nf
  unfold fC
  rw [norm_mul, norm_mul]
  calc ‖tauL s‖ * ‖Complex.Gamma (s / 2)‖ * ‖(Complex.Gamma ((13 + 2 * ε - s) / 2))⁻¹‖
      ≤ ((2 * π) ^ (7 : ℝ) * (C0 * Real.exp (π * |s.im|)) * |L0|) * |G| *
          (C0 * Real.exp (π * |s.im|)) := by gcongr
    _ = _ := by rw [hexp]; ring

/-- **Right edge** `Re s = 13/2 + ε`. -/
lemma fC_right {ε : ℝ} (hε0 : 0 < ε) {D : ℝ} (hD : ∀ z : ℂ, 13 / 2 + ε ≤ z.re → ‖tauL z‖ ≤ D) {s : ℂ}
    (hs : s.re = 13 / 2 + ε) : ‖fC ε s‖ ≤ D := by
  have hc : (13 + 2 * (ε : ℂ) - s) / 2 = starRingEnd ℂ (s / 2) := by
    rw [half_eq_conj_add, hs]; simp; ring_nf
  have hG0 := Complex.Gamma_ne_zero_of_re_pos (s := s / 2) (by simp [hs]; linarith)
  have hrat : ‖Complex.Gamma (s / 2) * (Complex.Gamma ((13 + 2 * ε - s) / 2))⁻¹‖ = 1 := by
    rw [hc, norm_mul, norm_inv, RamanujanTau.RankinError.norm_Gamma_conj,
      mul_inv_cancel₀ (norm_ne_zero_iff.2 hG0)]
  unfold fC
  rw [mul_assoc, norm_mul, hrat, mul_one]
  exact hD s hs.ge

/-- **Left edge** `Re s = 11/2 − ε`, via the functional equation. -/
lemma fC_left {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) {D : ℝ}
    (hD : ∀ z : ℂ, 13 / 2 + ε ≤ z.re → ‖tauL z‖ ≤ D) {s : ℂ}
    (hs : s.re = 11 / 2 - ε) : ‖fC ε s‖ ≤ 8 * Real.exp 20 * D := by
  set θ : ℝ := 1 + 2 * ε with hθ
  have hs0 : ∀ n : ℕ, 12 - s ≠ -n := by
    intro n h; have := congrArg re h; simp [hs] at this
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hT : tauL s = ((2 * π : ℂ) ^ s * (2 * π : ℂ) ^ (-(12 - s))) *
      (Complex.Gamma (12 - s) * (Complex.Gamma s)⁻¹) * tauL (12 - s) := by
    conv_lhs => rw [tauL, ← heckeLambda_functional_equation s, heckeLambda_eq_tauL hs0]
    ring
  have e1 : 12 - s = starRingEnd ℂ s + (θ : ℂ) := by
    rw [twelve_sub_eq_conj_add, hs, hθ]; congr 1; push_cast; ring
  have e2 : (13 + 2 * (ε : ℂ) - s) / 2 = starRingEnd ℂ (s / 2) + (θ : ℂ) := by
    rw [half_eq_conj_add, hs, hθ]; congr 1; push_cast; ring
  have hcs1 : 1 ≤ (starRingEnd ℂ s).re := by simp [hs]; linarith
  have hcs2 : 1 ≤ (starRingEnd ℂ (s / 2)).re := by rw [re_conj_half, hs]; linarith
  have I1 := RamanujanTau.Stirling.norm_Gamma_add_le hcs1 1 (θ := θ) (by positivity)
    (by rw [hθ]; push_cast; linarith)
  rw [← e1, RamanujanTau.RankinError.norm_Gamma_conj, Complex.norm_conj] at I1
  have hf2 : ((1 + 1).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [hf2] at I1
  have I2 := RamanujanTau.Stirling.norm_Gamma_mul_rpow_le_add hcs2 (θ := θ) (by positivity)
  rw [← e2, RamanujanTau.RankinError.norm_Gamma_conj, Complex.norm_conj] at I2
  -- norms
  set R : ℝ := ‖s‖ with hR
  have hR0 : 0 < R := by
    rw [hR, norm_pos_iff]; intro h; rw [h] at hs; simp at hs; linarith
  have hs2 : ‖s / 2‖ = R / 2 := by rw [norm_div]; simp [hR]
  rw [hs2] at I2
  set A : ℝ := ‖Complex.Gamma s‖
  set B : ℝ := ‖Complex.Gamma (s / 2)‖
  set W : ℝ := ‖Complex.Gamma ((13 + 2 * (ε : ℂ) - s) / 2)‖
  have hA : 0 < A := norm_pos_iff.2 (Complex.Gamma_ne_zero_of_re_pos (by rw [hs]; linarith))
  have hW : 0 < W := norm_pos_iff.2 (Complex.Gamma_ne_zero_of_re_pos (by simp [hs]; linarith))
  have hB : 0 ≤ B := norm_nonneg _
  have hRθ : (R / 2) ^ θ * 2 ^ θ = R ^ θ := by
    rw [← Real.mul_rpow (by positivity) (by norm_num)]; congr 1; ring
  have h2θ : (2 : ℝ) ^ θ ≤ 4 := by
    calc (2 : ℝ) ^ θ ≤ 2 ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hθ]; linarith)
      _ = 4 := by norm_num
  have hP : ‖(2 * π : ℂ) ^ s * (2 * π : ℂ) ^ (-(12 - s))‖ ≤ 1 := by
    rw [norm_mul, norm_two_pi_cpow', norm_two_pi_cpow', ← Real.rpow_add (by positivity)]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp [hs]; linarith
  -- the `Γ`-quotient
  have hQ : ‖(Complex.Gamma (12 - s) * (Complex.Gamma s)⁻¹) *
      (Complex.Gamma (s / 2) * (Complex.Gamma ((13 + 2 * ε - s) / 2))⁻¹)‖ ≤ 8 * Real.exp 20 := by
    rw [norm_mul, norm_mul, norm_mul, norm_inv, norm_inv]
    have q1 : ‖Complex.Gamma (12 - s)‖ * A⁻¹ ≤ 2 * Real.exp 10 * R ^ θ := by
      rw [mul_inv_le_iff₀ hA]; linarith
    have q2 : B * W⁻¹ * (R / 2) ^ θ ≤ Real.exp 10 := by
      rw [mul_comm B, mul_assoc, inv_mul_le_iff₀ hW]; linarith
    have hBW : 0 ≤ B * W⁻¹ := by positivity
    have e20 : Real.exp 20 = Real.exp 10 * Real.exp 10 := by rw [← Real.exp_add]; norm_num
    calc ‖Complex.Gamma (12 - s)‖ * A⁻¹ * (B * W⁻¹)
        ≤ (2 * Real.exp 10 * R ^ θ) * (B * W⁻¹) := by gcongr
      _ = 2 * Real.exp 10 * 2 ^ θ * (B * W⁻¹ * (R / 2) ^ θ) := by rw [← hRθ]; ring
      _ ≤ 2 * Real.exp 10 * 4 * Real.exp 10 := by gcongr
      _ = 8 * Real.exp 20 := by rw [e20]; ring
  have hL := hD (12 - s) (by simp [hs]; linarith)
  have hsplit : fC ε s = ((2 * π : ℂ) ^ s * (2 * π : ℂ) ^ (-(12 - s))) *
      ((Complex.Gamma (12 - s) * (Complex.Gamma s)⁻¹) *
        (Complex.Gamma (s / 2) * (Complex.Gamma ((13 + 2 * ε - s) / 2))⁻¹)) * tauL (12 - s) := by
    unfold fC; rw [hT]; ring
  rw [hsplit, norm_mul, norm_mul]
  calc _ ≤ 1 * (8 * Real.exp 20) * D := by gcongr
    _ = 8 * Real.exp 20 * D := by ring

/-- **Phragmén–Lindelöf**: `f_ε` is bounded on the closed strip `[11/2−ε, 13/2+ε]`. -/
theorem fC_bound {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 11 / 2 - ε ≤ s.re → s.re ≤ 13 / 2 + ε → ‖fC ε s‖ ≤ C := by
  obtain ⟨D, hD0, hD⟩ := exists_norm_tauL_le (σ := 13 / 2 + ε) (by linarith)
  obtain ⟨K, L, hKL⟩ := fC_growth hε0 hε
  have h8 : 1 ≤ 8 * Real.exp 20 := by
    have := Real.one_le_exp (show (0:ℝ) ≤ 20 by norm_num); linarith
  refine ⟨8 * Real.exp 20 * D, by positivity, fun s h1 h2 => ?_⟩
  refine RamanujanTau.RankinSharp.pl_strip (a' := 4) (by linarith) (by linarith)
    (by linarith [Real.pi_gt_three]) (differentiableOn_fC ε) hKL
    (fun z hz => fC_left hε0 hε hD hz) (fun z hz => (fC_right hε0 hD hz).trans ?_) h1 h2
  nlinarith

/-- **The convexity bound on a line** `11/2 − ε ≤ σ ≤ 13/2 + ε`:
`‖L(Δ,s)‖ ≤ 2e¹⁰ C ‖s/2‖^{13/2+ε−σ}`. -/
lemma tauL_line {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) {C : ℝ}
    (hC : ∀ s : ℂ, 11 / 2 - ε ≤ s.re → s.re ≤ 13 / 2 + ε → ‖fC ε s‖ ≤ C) {s : ℂ}
    (h1 : 11 / 2 - ε ≤ s.re) (h2 : s.re ≤ 13 / 2 + ε) :
    ‖tauL s‖ ≤ 2 * Real.exp 10 * C * ‖s / 2‖ ^ (13 / 2 + ε - s.re) := by
  set θ : ℝ := (13 + 2 * ε - 2 * s.re) / 2 with hθ
  have hθ' : θ = 13 / 2 + ε - s.re := by rw [hθ]; ring
  have e3 := half_eq_conj_add ε s
  rw [← hθ] at e3
  have hcs : 1 ≤ (starRingEnd ℂ (s / 2)).re := by rw [re_conj_half]; linarith
  have I3 := RamanujanTau.Stirling.norm_Gamma_add_le hcs 1 (θ := θ) (by rw [hθ']; linarith)
    (by rw [hθ']; push_cast; linarith)
  rw [← e3, RamanujanTau.RankinError.norm_Gamma_conj, Complex.norm_conj] at I3
  have hf2 : ((1 + 1).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [hf2] at I3
  have hG0 := Complex.Gamma_ne_zero_of_re_pos (s := s / 2) (by simp; linarith)
  have hW0 := Complex.Gamma_ne_zero_of_re_pos (s := (13 + 2 * (ε : ℂ) - s) / 2)
    (by simp; linarith)
  have hT : tauL s = fC ε s * Complex.Gamma ((13 + 2 * ε - s) / 2) *
      (Complex.Gamma (s / 2))⁻¹ := by
    unfold fC; field_simp
  have hfa := hC s h1 h2
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hfa
  have hpos : 0 < ‖Complex.Gamma (s / 2)‖ := norm_pos_iff.2 hG0
  rw [hT, norm_mul, norm_mul, norm_inv, ← hθ']
  have hq : ‖Complex.Gamma ((13 + 2 * (ε : ℂ) - s) / 2)‖ * ‖Complex.Gamma (s / 2)‖⁻¹ ≤
      2 * Real.exp 10 * ‖s / 2‖ ^ θ := by
    rw [mul_inv_le_iff₀ hpos]; linarith
  calc ‖fC ε s‖ * ‖Complex.Gamma ((13 + 2 * (ε : ℂ) - s) / 2)‖ * ‖Complex.Gamma (s / 2)‖⁻¹
      = ‖fC ε s‖ * (‖Complex.Gamma ((13 + 2 * (ε : ℂ) - s) / 2)‖ *
          ‖Complex.Gamma (s / 2)‖⁻¹) := by ring
    _ ≤ C * (2 * Real.exp 10 * ‖s / 2‖ ^ θ) := by gcongr
    _ = _ := by ring

/-! ### Headline theorems -/

/-- **Convexity bound, uniform in the strip** `11/2 ≤ σ ≤ 13/2`: for every `ε > 0`,
`‖L(Δ, σ+it)‖ ≤ C (1+|t|)^{13/2 − σ + ε}`. -/
theorem tauL_convexity_strip {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 11 / 2 ≤ σ → σ ≤ 13 / 2 →
      ‖tauL ((σ : ℂ) + t * I)‖ ≤ C * (1 + |t|) ^ (13 / 2 - σ + ε) := by
  set ε' : ℝ := min ε (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  obtain ⟨C, hC0, hC⟩ := fC_bound hε'0 hε'1
  refine ⟨2 * Real.exp 10 * C * 16, by positivity, fun σ t h1 h2 => ?_⟩
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have hL := tauL_line hε'0 hε'1 hC (s := s) (by rw [hsre]; linarith) (by rw [hsre]; linarith)
  rw [hsre] at hL
  set θ : ℝ := 13 / 2 + ε' - σ with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  have ht0 : 0 ≤ |t| := abs_nonneg t
  have hn : ‖s / 2‖ ≤ 4 * (1 + |t|) := by
    rw [norm_div, Complex.norm_two, div_le_iff₀ (by norm_num)]
    refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
    rw [hsre, hsim, abs_of_nonneg (by linarith : (0:ℝ) ≤ σ)]; linarith
  have hb1 : (1 : ℝ) ≤ 1 + |t| := by linarith
  have hp1 : ‖s / 2‖ ^ θ ≤ (4 * (1 + |t|)) ^ θ :=
    Real.rpow_le_rpow (norm_nonneg _) hn hθ0
  have hp2 : (4 * (1 + |t|)) ^ θ = 4 ^ θ * (1 + |t|) ^ θ :=
    Real.mul_rpow (by norm_num) (by linarith)
  have hp3 : (4 : ℝ) ^ θ ≤ 16 := by
    calc (4 : ℝ) ^ θ ≤ 4 ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hθ]; linarith)
      _ = 16 := by norm_num
  have hp4 : (1 + |t|) ^ θ ≤ (1 + |t|) ^ (13 / 2 - σ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hb1 (by rw [hθ]; linarith)
  have hK : 0 ≤ 2 * Real.exp 10 * C := by positivity
  calc ‖tauL s‖ ≤ 2 * Real.exp 10 * C * ‖s / 2‖ ^ θ := hL
    _ ≤ 2 * Real.exp 10 * C * (4 ^ θ * (1 + |t|) ^ θ) := by rw [← hp2]; gcongr
    _ ≤ 2 * Real.exp 10 * C * (16 * (1 + |t|) ^ (13 / 2 - σ + ε)) := by gcongr
    _ = _ := by ring

/-- **The convexity bound on the critical line** `Re s = 6`: for every `ε > 0`,
`‖L(Δ, 6+it)‖ ≤ C (1+|t|)^{1/2+ε}`. -/
theorem tauL_convexity {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖tauL (6 + t * I)‖ ≤ C * (1 + |t|) ^ (1 / 2 + ε) := by
  obtain ⟨C, hC0, hC⟩ := tauL_convexity_strip hε
  refine ⟨C, hC0, fun t => ?_⟩
  have := hC 6 t (by norm_num) (by norm_num)
  have e : (13 / 2 - 6 + ε : ℝ) = 1 / 2 + ε := by ring
  rw [e] at this
  simpa using this

/-- **Boundedness to the right of the convexity strip**: for `σ > 13/2`, `L(Δ,s)` is bounded on
`Re s ≥ σ`. -/
theorem tauL_bounded_of_gt {σ : ℝ} (hσ : 13 / 2 < σ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℂ, σ ≤ s.re → ‖tauL s‖ ≤ D :=
  exists_norm_tauL_le hσ

end RamanujanTau.HeckeConvex
