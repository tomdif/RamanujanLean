/-
# Dragonette's asymptotic formula for the coefficients of Ramanujan's mock theta function `f(q)`

  **`α(n) ~ (−1)^{n−1} e^{π√(n/6)} / (2√n)`**,  `f(q) = Σ q^{n²}/(−q;q)_n² = Σ α(n) qⁿ`
(Dragonette 1952; Ramanujan's claim), where `α(n) = N(0,2,n) − N(1,2,n)` (`MockTheta3.f3_rank`).
Equivalently `α(n) ~ (−1)^{n−1} e^{π√(n/6 − 1/144)}/(2√(n − 1/24))`.

Circle method at the cusp `q = −1`: with `q = −e^{−z}`, `z = t + iθ`, `t = π/√(24n)`,
* Watson: `f(q) = 2φ(−q) − b(q)`; `b(−e^{−z}) = (z/π)^{−1/2} e^{π²/(24z) − z/24}(1 + O(e^{−Re π²/z}))`;
* `φ` is uniformly `O(e^{π²/(24t)}·t^{−1}e^{−1/(2400t)})` on the whole circle (`phi_bound`);
* `(−s;s²)_∞` decays by `e^{−1/(160t)}` off the major arc (`Oz_minor`);
* Laplace's method on the major arc (`Jneg_tendsto`).
-/
import RamanujanTau.Dragonette.Setup

set_option autoImplicit false

namespace Dragonette
open Complex Filter Metric MeasureTheory intervalIntegral HardyRamanujan
open scoped Real Topology

/-- the integrand `G(θ) = f(−e^{−z}) e^{nz}`. -/
noncomputable def GD (n : ℕ) (t θ : ℝ) : ℂ := MockTheta3.Radial.fA (-cexp (-zt t θ)) * cexp (n * zt t θ)

lemma GD_cont (n : ℕ) {t : ℝ} (ht : 0 < t) : Continuous (GD n t) := by
  unfold GD
  have hm : ∀ θ : ℝ, -cexp (-zt t θ) ∈ ball (0 : ℂ) 1 := fun θ =>
    neg_mem_ball (norm_cexp_neg_lt_one (re_zt_pos ht))
  have h1 : Continuous fun θ : ℝ => MockTheta3.Radial.fA (-cexp (-zt t θ)) :=
    MockTheta3.Radial.fA_T.1.continuousOn.comp_continuous (by fun_prop) hm
  exact h1.mul (by fun_prop)

lemma MD_cont (n : ℕ) {t : ℝ} (ht : 0 < t) : Continuous (MD n t) := by
  unfold MD
  have hslit : ∀ θ : ℝ, zt t θ / π ∈ slitPlane := fun θ => by
    refine mem_slitPlane_iff.mpr (Or.inl ?_)
    rw [div_ofReal_re]; exact div_pos (re_zt_pos ht) Real.pi_pos
  have hl : Continuous fun θ : ℝ => log (zt t θ / π) :=
    continuous_iff_continuousAt.mpr fun θ =>
      ContinuousAt.clog (f := fun θ : ℝ => zt t θ / π) (by fun_prop) (hslit θ)
  have hd : Continuous fun θ : ℝ => (π : ℂ) ^ 2 / (24 * zt t θ) :=
    continuous_const.div (by fun_prop) fun θ => mul_ne_zero (by norm_num) (zt_ne_zero ht)
  fun_prop

lemma norm_s {t θ : ℝ} : ‖cexp (-zt t θ)‖ = Real.exp (-t) := by
  rw [norm_exp]; simp [zt]

lemma norm_cexp_nz (n : ℕ) (t θ : ℝ) : ‖cexp (n * zt t θ)‖ = Real.exp (n * t) := by
  rw [norm_exp]; simp [zt]

/-- `‖M(θ)‖ ≤ (π/t) e^{2A}` for all `θ`. -/
lemma norm_MD_le {n : ℕ} (hn : 1 ≤ n) (ht1 : tD n ≤ 1) (θ : ℝ) :
    ‖MD n (tD n) θ‖ ≤ π / tD n * Real.exp (2 * AD n) := by
  set t := tD n with htdef
  have ht := tD_pos hn
  have hnz : 0 < t ^ 2 + θ ^ 2 := by positivity
  unfold MD
  rw [norm_mul, norm_mul, norm_exp, norm_exp, norm_exp]
  have hz0 := zt_ne_zero (θ := θ) ht
  have h1 : (-(log (zt t θ / π) / 2)).re ≤ Real.log (π / t) := by
    rw [neg_re, Complex.div_ofNat_re, log_re]
    have hnorm : t / π ≤ ‖zt t θ / π‖ := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      gcongr
      have := Complex.abs_re_le_norm (zt t θ)
      simp [zt] at this ⊢; rw [abs_of_pos ht] at this; exact this
    have hl : Real.log (t / π) ≤ Real.log ‖zt t θ / π‖ := Real.log_le_log (by positivity) hnorm
    have hl2 : Real.log (t / π) ≤ 0 := Real.log_nonpos (by positivity)
      (by rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three])
    have : Real.log (π / t) = -Real.log (t / π) := by
      rw [show π / t = (t / π)⁻¹ by field_simp, Real.log_inv]
    linarith
  have hRe1 : (π ^ 2 / (24 * zt t θ) - zt t θ / 24).re ≤ AD n := by
    have e : (π : ℂ) ^ 2 / (24 * zt t θ) = (((π ^ 2 / 24 : ℝ)) : ℂ) / zt t θ := by push_cast; field_simp
    rw [sub_re, e, re_div_zt, ← AD_eq hn, ← htdef]
    have : (zt t θ / 24).re = t / 24 := by rw [Complex.div_ofNat_re]; simp [zt]
    rw [this]
    have h1 : π ^ 2 / 24 * t / (t ^ 2 + θ ^ 2) ≤ π ^ 2 / (24 * t) := by
      rw [div_le_div_iff₀ hnz (by positivity)]; nlinarith [sq_nonneg θ, Real.pi_pos, sq_nonneg t]
    linarith
  have hRe2 : ((n : ℂ) * zt t θ).re = AD n := by simp [zt, AD, ← htdef]
  rw [hRe2]
  calc Real.exp (-(log (zt t θ / π) / 2)).re * Real.exp (π ^ 2 / (24 * zt t θ) - zt t θ / 24).re *
        Real.exp (AD n) ≤ Real.exp (Real.log (π / t)) * Real.exp (AD n) * Real.exp (AD n) := by gcongr
    _ = π / t * Real.exp (2 * AD n) := by
        rw [Real.exp_log (by positivity), mul_assoc, ← Real.exp_add]; ring_nf

/-- the size of `φ` at the saddle radius. -/
lemma gA_bound {n : ℕ} (hn : 1 ≤ n) (ht32 : tD n ≤ 1 / 32)
    (hη : (4 * C0 + 4) * Real.exp (-(π ^ 2 / (2 * tD n))) ≤ 1 / 15) (θ : ℝ) :
    ‖MockTheta3.Radial.gA (-cexp (-zt (tD n) θ))‖ ≤
      2 * Real.exp (AD n) * (1 / tD n) * Real.exp (-(1 / (2400 * tD n))) := by
  set t := tD n
  have ht := tD_pos hn
  have hφ := phi_bound ht ht32 (norm_s (θ := θ))
  have hO := Oz_real_le ht (by rw [le_div_iff₀ ht]; nlinarith [Real.pi_gt_three]) (by
    refine le_trans ?_ hη
    gcongr
    · linarith [C0_nonneg]
    · show tD n ≤ 2 * tD n
      linarith)
  rw [AD_eq hn] at hO
  refine hφ.trans ?_
  gcongr

lemma cusp_error {n : ℕ} (hn : 1 ≤ n) (ht32 : tD n ≤ 1 / 32)
    (hη : (4 * C0 + 4) * Real.exp (-(π ^ 2 / (2 * tD n))) ≤ 1 / 15) {θ : ℝ} (hθ : |θ| ≤ tD n) :
    ‖Fr (zt (tD n) θ) * Jt (π ^ 2 / zt (tD n) θ) - 1‖ ≤
      31 * ((4 * C0 + 4) * Real.exp (-(π ^ 2 / (2 * tD n)))) := by
  set t := tD n
  have ht := tD_pos hn
  have hnz : 0 < t ^ 2 + θ ^ 2 := by positivity
  have hθ2 : θ ^ 2 ≤ t ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hθ 2
  have hre : π ^ 2 / (2 * t) ≤ ((π : ℂ) ^ 2 / zt t θ).re := by
    rw [show (π : ℂ) ^ 2 / zt t θ = ((π ^ 2 : ℝ) : ℂ) / zt t θ by push_cast; ring, re_div_zt,
      div_le_div_iff₀ (by positivity) hnz]
    nlinarith [Real.pi_pos, sq_nonneg π]
  have hπt : 1 ≤ π ^ 2 / (2 * t) := by rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
  have hE : Real.exp (-((π : ℂ) ^ 2 / zt t θ).re) ≤ Real.exp (-(π ^ 2 / (2 * t))) :=
    Real.exp_le_exp.mpr (by linarith)
  have hC : 0 ≤ 4 * C0 + 4 := by linarith [C0_nonneg]
  have h := (Fr_near (re_zt_pos ht) (by linarith) (le_trans (by gcongr) (hη.trans (by norm_num)))).2
  refine h.trans ?_
  gcongr

/-- **the major-arc remainder**. -/
lemma major_bound {n : ℕ} (hn : 1 ≤ n) (ht32 : tD n ≤ 1 / 32)
    (hη : (4 * C0 + 4) * Real.exp (-(π ^ 2 / (2 * tD n))) ≤ 1 / 15) {θ : ℝ} (hθ : |θ| ≤ tD n) :
    ‖GD n (tD n) θ + MD n (tD n) θ‖ ≤ Real.exp (2 * AD n) *
      (4 * (1 / tD n) * Real.exp (-(1 / (2400 * tD n))) +
        31 * (4 * C0 + 4) * (π / tD n) * Real.exp (-(π ^ 2 / (2 * tD n)))) := by
  set t := tD n
  have ht := tD_pos hn
  have e : GD n t θ + MD n t θ = 2 * MockTheta3.Radial.gA (-cexp (-zt t θ)) * cexp (n * zt t θ) -
      MD n t θ * (Fr (zt t θ) * Jt (π ^ 2 / zt t θ) - 1) := by
    rw [GD, integrand_eq n ht θ]; ring
  rw [e]
  have h1 := gA_bound hn ht32 hη θ
  have h2 := norm_MD_le hn (by linarith) θ
  have h3 := cusp_error hn ht32 hη hθ
  have hnz := norm_cexp_nz n t θ
  have hAn : (n : ℝ) * t = AD n := rfl
  rw [hAn] at hnz
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, hnz, Complex.norm_ofNat]
  have hC := C0_nonneg
  calc 2 * ‖MockTheta3.Radial.gA (-cexp (-zt t θ))‖ * Real.exp (AD n) +
        ‖MD n t θ‖ * ‖Fr (zt t θ) * Jt (π ^ 2 / zt t θ) - 1‖
      ≤ 2 * (2 * Real.exp (AD n) * (1 / t) * Real.exp (-(1 / (2400 * t)))) * Real.exp (AD n) +
        (π / t * Real.exp (2 * AD n)) * (31 * ((4 * C0 + 4) * Real.exp (-(π ^ 2 / (2 * t))))) := by
        gcongr
    _ = _ := by rw [show 2 * AD n = AD n + AD n by ring, Real.exp_add]; ring

/-- **the minor-arc integrand**. -/
lemma minor_bound_D {n : ℕ} (hn : 1 ≤ n) (ht32 : tD n ≤ 1 / 32)
    (hη : (4 * C0 + 4) * Real.exp (-(π ^ 2 / (2 * tD n))) ≤ 1 / 15) {θ : ℝ} (hθ1 : tD n ≤ |θ|)
    (hθ2 : |θ| ≤ π) :
    ‖GD n (tD n) θ‖ ≤ Real.exp (2 * AD n) *
      (4 * (1 / tD n) * Real.exp (-(1 / (2400 * tD n))) +
        2 * Real.exp (-(1 / (160 * tD n))) * (1 + 2 / tD n)) := by
  set t := tD n
  have ht := tD_pos hn
  have hz := re_zt_pos (θ := θ) ht
  have hb : -cexp (-zt t θ) ∈ ball (0 : ℂ) 1 := neg_mem_ball (norm_cexp_neg_lt_one hz)
  have hW := MockTheta3.Radial.watson_disc hb
  have e : GD n t θ = (2 * MockTheta3.Radial.gA (-cexp (-zt t θ)) -
      Oz (cexp (-zt t θ)) * Jt (zt t θ)) * cexp (n * zt t θ) := by
    rw [GD, ← bA_neg hz]; congr 1; linear_combination hW
  rw [e, norm_mul, norm_cexp_nz]
  have hAn : (n : ℝ) * t = AD n := rfl
  rw [hAn]
  have h1 := gA_bound hn ht32 hη θ
  have hO := Oz_minor ht (by linarith) hθ1 hθ2
  have hOr := Oz_real_le ht (by rw [le_div_iff₀ ht]; nlinarith [Real.pi_gt_three]) (by
    refine le_trans ?_ hη
    gcongr
    · linarith [C0_nonneg]
    · show tD n ≤ 2 * tD n
      linarith)
  rw [AD_eq hn] at hOr
  have hJ : ‖Jt (zt t θ)‖ ≤ 1 + 2 / t := by
    have := norm_Jt_le hz; simpa [zt] using this
  have hOs : ‖Oz (cexp (-zt t θ))‖ ≤ 2 * Real.exp (AD n) * Real.exp (-(1 / (160 * t))) :=
    hO.trans (by gcongr)
  calc ‖2 * MockTheta3.Radial.gA (-cexp (-zt t θ)) - Oz (cexp (-zt t θ)) * Jt (zt t θ)‖ * Real.exp (AD n)
      ≤ (2 * ‖MockTheta3.Radial.gA (-cexp (-zt t θ))‖ + ‖Oz (cexp (-zt t θ))‖ * ‖Jt (zt t θ)‖) *
          Real.exp (AD n) := by
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_ofNat]
    _ ≤ (2 * (2 * Real.exp (AD n) * (1 / t) * Real.exp (-(1 / (2400 * t)))) +
          (2 * Real.exp (AD n) * Real.exp (-(1 / (160 * t)))) * (1 + 2 / t)) * Real.exp (AD n) := by
        gcongr
    _ = _ := by rw [show 2 * AD n = AD n + AD n by ring, Real.exp_add]; ring

/-! ### assembly -/

/-- the error function of `u = 1/t`. -/
noncomputable def Err (u : ℝ) : ℝ :=
  2 * (4 * u * Real.exp (-(u / 2400)) + 31 * (4 * C0 + 4) * (π * u) * Real.exp (-(π ^ 2 * u / 2))) +
    2 * π * u * (4 * u * Real.exp (-(u / 2400)) + 2 * Real.exp (-(u / 160)) * (1 + 2 * u))

/-- **the decomposition** `K_n (−1)^{n+1} α(n) = (1/√π) J_n + E_n` with `‖E_n‖ ≤ Err(1/t)`. -/
lemma decomp_D {n : ℕ} (hn : 1 ≤ n) (ht32 : tD n ≤ 1 / 32)
    (hη : (4 * C0 + 4) * Real.exp (-(π ^ 2 / (2 * tD n))) ≤ 1 / 15) :
    ‖((KD n * ((-1) ^ (n + 1) * (α n : ℝ)) : ℝ) : ℂ) -
      ((1 / √π : ℝ) : ℂ) * ∫ v in (-√(AD n))..√(AD n), hneg (v / √(AD n)) (tD n) v‖ ≤ Err (1 / tD n) := by
  set t := tD n with htdef
  have ht := tD_pos hn
  have htπ : t ≤ π := by linarith [Real.pi_gt_three]
  have hcoef := coeff_integral_f n ht
  have hGc := GD_cont n ht
  have hMc := MD_cont n ht
  have hint : ∀ a b : ℝ, IntervalIntegrable (GD n t) volume a b := fun a b => hGc.intervalIntegrable a b
  have hintM : ∀ a b : ℝ, IntervalIntegrable (MD n t) volume a b := fun a b => hMc.intervalIntegrable a b
  set R : ℂ := (∫ θ in (-t)..t, (GD n t θ + MD n t θ)) + ((∫ θ in (-π)..(-t), GD n t θ) +
    ∫ θ in t..π, GD n t θ) with hR
  have hsplit : (2 * π : ℂ) * ((-1) ^ n * (α n : ℂ)) = -(∫ θ in (-t)..t, MD n t θ) + R := by
    have e : ∫ θ in (-π)..π, GD n t θ = (∫ θ in (-π)..(-t), GD n t θ) + (∫ θ in (-t)..t, GD n t θ) +
        ∫ θ in t..π, GD n t θ := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
        intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
    have e2 : ∫ θ in (-t)..t, (GD n t θ + MD n t θ) = (∫ θ in (-t)..t, GD n t θ) + ∫ θ in (-t)..t, MD n t θ :=
      intervalIntegral.integral_add (hint _ _) (hintM _ _)
    rw [hcoef]
    change ∫ θ in (-π)..π, GD n t θ = _
    rw [e, hR, e2]; ring
  have hπ : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  have hmain := major_main_D hn
  rw [← htdef] at hmain
  have hP := PD_eq hn
  rw [← htdef] at hP
  have hK : ((KD n * ((-1) ^ (n + 1) * (α n : ℝ)) : ℝ) : ℂ) =
      -((KD n / (2 * π) : ℝ) : ℂ) * ((2 * π : ℂ) * ((-1) ^ n * (α n : ℂ))) := by
    push_cast; field_simp; ring
  have hmain' : ((KD n / (2 * π) : ℝ) : ℂ) * ∫ θ in (-t)..t, MD n t θ =
      ((1 / √π : ℝ) : ℂ) * ∫ v in (-√(AD n))..√(AD n), hneg (v / √(AD n)) t v := by
    rw [hmain, ← mul_assoc, ← Complex.ofReal_mul, hP]
  rw [hK, hsplit, show -((KD n / (2 * π) : ℝ) : ℂ) * (-(∫ θ in (-t)..t, MD n t θ) + R) =
    ((KD n / (2 * π) : ℝ) : ℂ) * (∫ θ in (-t)..t, MD n t θ) - ((KD n / (2 * π) : ℝ) : ℂ) * R by ring, hmain',
    sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_real]
  -- bounds on the three pieces
  set B1 := 4 * (1 / t) * Real.exp (-(1 / (2400 * t))) +
    31 * (4 * C0 + 4) * (π / t) * Real.exp (-(π ^ 2 / (2 * t)))
  set B2 := 4 * (1 / t) * Real.exp (-(1 / (2400 * t))) + 2 * Real.exp (-(1 / (160 * t))) * (1 + 2 / t)
  have hB1 : 0 ≤ B1 := by have := C0_nonneg; positivity
  have hB2 : 0 ≤ B2 := by positivity
  have r1 : ‖∫ θ in (-t)..t, (GD n t θ + MD n t θ)‖ ≤ Real.exp (2 * AD n) * B1 * (2 * t) := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := Real.exp (2 * AD n) * B1)
      fun θ hθ => ?_).trans (le_of_eq ?_)
    · refine major_bound hn ht32 hη ?_
      rw [Set.uIoc_of_le (by linarith)] at hθ
      rw [abs_le]; exact ⟨hθ.1.le, hθ.2⟩
    · rw [show t - -t = 2 * t by ring, abs_of_pos (by linarith)]
  have hmin : ∀ a b : ℝ, (∀ θ ∈ Set.uIoc a b, t ≤ |θ| ∧ |θ| ≤ π) → |b - a| ≤ π →
      ‖∫ θ in a..b, GD n t θ‖ ≤ Real.exp (2 * AD n) * B2 * π := by
    intro a b hab hba
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := Real.exp (2 * AD n) * B2)
      fun θ hθ => ?_).trans ?_
    · exact minor_bound_D hn ht32 hη (hab θ hθ).1 (hab θ hθ).2
    · gcongr
  have r2 := hmin (-π) (-t) (fun θ hθ => by
      rw [Set.uIoc_of_le (by linarith)] at hθ
      obtain ⟨hθ1, hθ2⟩ := hθ
      rw [abs_of_neg (by linarith)]; constructor <;> linarith)
    (by rw [abs_of_nonneg (by linarith)]; linarith)
  have r3 := hmin t π (fun θ hθ => by
      rw [Set.uIoc_of_le (by linarith)] at hθ
      obtain ⟨hθ1, hθ2⟩ := hθ
      rw [abs_of_pos (by linarith)]; constructor <;> linarith)
    (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hRb : ‖R‖ ≤ Real.exp (2 * AD n) * (B1 * (2 * t) + 2 * π * B2) := by
    rw [hR]
    refine (norm_add_le _ _).trans ?_
    have := norm_add_le (∫ θ in (-π)..(-t), GD n t θ) (∫ θ in t..π, GD n t θ)
    nlinarith
  have hK0 : 0 ≤ KD n / (2 * π) := by unfold KD; positivity
  have hKe : KD n / (2 * π) * Real.exp (2 * AD n) ≤ 1 / t := by
    have e : KD n / (2 * π) * Real.exp (2 * AD n) = √(n : ℝ) / π := by
      unfold KD; field_simp
    rw [e, div_le_iff₀ Real.pi_pos]
    have := tD_inv hn
    rw [← htdef] at this
    linarith
  rw [Real.norm_of_nonneg hK0]
  calc KD n / (2 * π) * ‖R‖ ≤ KD n / (2 * π) * (Real.exp (2 * AD n) * (B1 * (2 * t) + 2 * π * B2)) := by gcongr
    _ = (KD n / (2 * π) * Real.exp (2 * AD n)) * (B1 * (2 * t) + 2 * π * B2) := by ring
    _ ≤ (1 / t) * (B1 * (2 * t) + 2 * π * B2) := by gcongr
    _ = Err (1 / t) := by
        unfold Err
        simp only [B1, B2]
        rw [show (1 : ℝ) / t / 2400 = 1 / (2400 * t) by ring, show π ^ 2 * (1 / t) / 2 = π ^ 2 / (2 * t) by ring,
          show (1 : ℝ) / t / 160 = 1 / (160 * t) by ring]
        have ht0 : t ≠ 0 := ht.ne'
        field_simp

lemma tendsto_pow_exp {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Tendsto (fun u : ℝ => u ^ k * Real.exp (-(c * u))) atTop (𝓝 0) := by
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
    (tendsto_id.const_mul_atTop hc)).const_mul (1 / c ^ k)
  rw [mul_zero] at h
  refine h.congr fun u => ?_
  simp only [Function.comp, id]
  rw [mul_pow]
  field_simp

lemma Err_tendsto : Tendsto Err atTop (𝓝 0) := by
  have a1 := tendsto_pow_exp (c := 1 / 2400) (by norm_num) 1
  have a2 := tendsto_pow_exp (c := π ^ 2 / 2) (by positivity) 1
  have a3 := tendsto_pow_exp (c := 1 / 2400) (by norm_num) 2
  have a4 := tendsto_pow_exp (c := 1 / 160) (by norm_num) 0
  have a5 := tendsto_pow_exp (c := 1 / 160) (by norm_num) 1
  have a6 := tendsto_pow_exp (c := 1 / 160) (by norm_num) 2
  have h := ((((a1.const_mul 8).add (a2.const_mul (62 * (4 * C0 + 4) * π))).add
    (a3.const_mul (8 * π))).add (a5.const_mul (4 * π))).add (a6.const_mul (8 * π))
  simp only [mul_zero, add_zero] at h
  refine h.congr fun u => ?_
  unfold Err
  rw [show u / 2400 = 1 / 2400 * u by ring, show π ^ 2 * u / 2 = π ^ 2 / 2 * u by ring,
    show u / 160 = 1 / 160 * u by ring]
  simp only [pow_one]
  ring

lemma tD_tendsto : Tendsto tD atTop (𝓝 0) := by
  have : Tendsto (fun n : ℕ => √(24 * (n : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp ((tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num))
  exact tendsto_const_nhds.div_atTop this

lemma AD_tendsto : Tendsto AD atTop atTop := by
  have h : ∀ n : ℕ, 1 ≤ n → AD n = π / √24 * √(n : ℝ) := by
    intro n hn
    unfold AD tD
    rw [Real.sqrt_mul (by norm_num)]
    have : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    field_simp
    rw [this]
  have h2 : Tendsto (fun n : ℕ => π / √24 * √(n : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (h n hn).symm

lemma eventually_small : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ tD n ≤ 1 / 32 ∧
    (4 * C0 + 4) * Real.exp (-(π ^ 2 / (2 * tD n))) ≤ 1 / 15 := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < tD n := by
    filter_upwards [eventually_ge_atTop 1] with n hn; exact tD_pos hn
  have h1 := tD_tendsto.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 32))
  -- `π²/(2t) → ∞`
  have hinv : Tendsto (fun n => π ^ 2 / (2 * tD n)) atTop atTop := by
    refine (AD_tendsto.atTop_mul_const (by norm_num : (0 : ℝ) < 12)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [← AD_eq hn]
    have := tD_pos hn
    field_simp; ring
  have h2 : Tendsto (fun n => (4 * C0 + 4) * Real.exp (-(π ^ 2 / (2 * tD n)))) atTop (𝓝 0) := by
    simpa using ((Real.tendsto_exp_neg_atTop_nhds_zero.comp hinv).const_mul (4 * C0 + 4))
  have h3 := h2.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 15))
  filter_upwards [eventually_ge_atTop 1, h1, h3] with n hn a b
  exact ⟨hn, a, b⟩

/-- **Dragonette's theorem** (1952): `(−1)^{n+1} α(n) · 2√n / e^{π√(n/6)} → 1`, where
`α(n) = [qⁿ] f(q) = N(0,2,n) − N(1,2,n)`. -/
theorem dragonette :
    Tendsto (fun n : ℕ => (-1) ^ (n + 1) * (α n : ℝ) * (2 * √(n : ℝ)) / Real.exp (π * √(n / 6)))
      atTop (𝓝 1) := by
  have hJ := Jneg_tendsto (A := fun n => AD (n + 1)) (t := fun n => tD (n + 1))
    (AD_tendsto.comp (tendsto_add_atTop_nat 1)) (fun n => AD_pos (by omega))
    (tD_tendsto.comp (tendsto_add_atTop_nat 1)) (fun n => (tD_pos (by omega)).le)
  simp only at hJ
  rw [← tendsto_add_atTop_iff_nat 1]
  have hmain : Tendsto (fun n : ℕ => ((1 / √π : ℝ) : ℂ) * ∫ v in (-√(AD (n + 1)))..√(AD (n + 1)),
      hneg (v / √(AD (n + 1))) (tD (n + 1)) v) atTop (𝓝 1) := by
    have := hJ.const_mul ((1 / √π : ℝ) : ℂ)
    convert this using 2
    have : (√π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
    push_cast; field_simp
  have hinvt : Tendsto (fun n : ℕ => 1 / tD (n + 1)) atTop atTop := by
    have h := AD_tendsto.comp (tendsto_add_atTop_nat 1)
    have e : ∀ n : ℕ, 1 / tD (n + 1) = AD (n + 1) * (24 / π ^ 2) := by
      intro n
      have := AD_eq (n := n + 1) (by omega)
      have ht := tD_pos (n := n + 1) (by omega)
      rw [← this]; field_simp
    simp only [e]
    exact h.atTop_mul_const (by positivity)
  have hE := Err_tendsto.comp hinvt
  have hdiff : Tendsto (fun n : ℕ => ((KD (n + 1) * ((-1) ^ (n + 1 + 1) * (α (n + 1) : ℝ)) : ℝ) : ℂ) -
      ((1 / √π : ℝ) : ℂ) * ∫ v in (-√(AD (n + 1)))..√(AD (n + 1)), hneg (v / √(AD (n + 1))) (tD (n + 1)) v)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hE
    have hev := (tendsto_add_atTop_nat 1).eventually eventually_small
    filter_upwards [hev] with n hn
    exact decomp_D hn.1 hn.2.1 hn.2.2
  have hC := hdiff.add hmain
  rw [zero_add] at hC
  have hC' : Tendsto (fun n : ℕ => ((KD (n + 1) * ((-1) ^ (n + 1 + 1) * (α (n + 1) : ℝ)) : ℝ) : ℂ))
      atTop (𝓝 1) := hC.congr fun n => sub_add_cancel _ _
  have hR : Tendsto (fun n : ℕ => KD (n + 1) * ((-1) ^ (n + 1 + 1) * (α (n + 1) : ℝ))) atTop (𝓝 1) := by
    have := (Complex.continuous_re.tendsto _).comp hC'
    simpa only [Function.comp_def, Complex.ofReal_re, Complex.one_re] using this
  refine hR.congr fun n => ?_
  unfold KD
  rw [two_AD (by omega)]
  push_cast
  ring

/-- **Dragonette's theorem, in the form of Ramanujan/Dragonette**:
`α(n) ~ (−1)^{n−1} e^{π√(n/6 − 1/144)} / (2√(n − 1/24))`. -/
theorem dragonette_isEquivalent :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => (α n : ℝ))
      (fun n : ℕ => (-1) ^ (n + 1) * Real.exp (π * √(n / 6)) / (2 * √(n : ℝ))) := by
  refine Asymptotics.isEquivalent_of_tendsto_one ?_
  · refine dragonette.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have h2 : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    simp only [Pi.div_apply]
    field_simp
    rw [h2, one_mul]

/-- **the sign pattern**: `(−1)^{n−1} α(n) > 0`, i.e. `N(0,2,n) > N(1,2,n)` for odd `n` and `<` for even `n`,
for all sufficiently large `n`. -/
theorem dragonette_sign : ∀ᶠ n : ℕ in atTop, 0 < (-1) ^ (n + 1) * (α n : ℝ) := by
  have h := dragonette.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h, eventually_ge_atTop 1] with n hn h1
  have hs : 0 < 2 * √(n : ℝ) := by positivity
  have he := Real.exp_pos (π * √(n / 6))
  have h2 : 0 < (-1) ^ (n + 1) * (α n : ℝ) * (2 * √(n : ℝ)) := (div_pos_iff_of_pos_right he).mp hn
  by_contra hc
  push Not at hc
  have := mul_nonpos_of_nonpos_of_nonneg hc hs.le
  linarith

/-- **rank parity** (Dragonette's theorem in partition language): for all large `n`,
`(−1)^{n+1}(N(0,2,n) − N(1,2,n)) > 0`; i.e. partitions of odd `n` with even rank outnumber those with odd rank,
and the reverse holds for even `n`. -/
theorem rank_parity_sign : ∀ᶠ n : ℕ in atTop,
    0 < (-1) ^ (n + 1) * (((Finset.univ.filter fun l : n.Partition => Even (CrankProof.rank l)).card : ℝ) -
      ((Finset.univ.filter fun l : n.Partition => ¬ Even (CrankProof.rank l)).card : ℝ)) := by
  filter_upwards [dragonette_sign] with n hn
  have h := MockTheta3.f3_rank n
  have : (α n : ℝ) = (((Finset.univ.filter fun l : n.Partition => Even (CrankProof.rank l)).card : ℤ) -
      ((Finset.univ.filter fun l : n.Partition => ¬ Even (CrankProof.rank l)).card : ℤ) : ℤ) := by
    rw [← h]
  rw [this] at hn; push_cast at hn; exact hn

end Dragonette
