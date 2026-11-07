/-
# Gamma ratios in vertical strips (a Stirling substitute)

Mathlib has no complex Stirling formula. This file proves the part of it needed for
convexity bounds: for `Re z ≥ 1` and real `θ ≥ 0`,

    ‖Γ(z)‖ ‖z‖^θ ≤ e¹⁰ ‖Γ(z+θ)‖,             (`norm_Gamma_mul_rpow_le_add`)
    ‖Γ(z+θ)‖ ≤ (n+1)! e¹⁰ ‖z‖^θ ‖Γ(z)‖   (θ ≤ n+1),   (`norm_Gamma_add_le`)

so `|Γ(α+it)/Γ(β+it)| ≍ |β+it|^{α−β}` for real `α, β ≥ 1`, with explicit constants and with
no integrality condition on `α − β`.

Route (Gauss product, no integrals). `Γ(z) = lim n^z n!/∏_{j≤n}(z+j)` (Mathlib
`Complex.GammaSeq_tendsto_Gamma`), so `Γ(z)/Γ(z+θ) = lim n^{−θ} ∏_{j≤n} (z+θ+j)/(z+j)`.
The function `x ↦ log|x+iy|` is "almost concave": for `Re w = x ≥ 1`, `0 ≤ θ ≤ 1`,

    |w+θ| ≤ exp(θ(5/(x−½) − 5/(x+½))) |w+1|^θ |w|^{1−θ}      (`norm_add_ofReal_le`)

(`log(1+θu) ≤ θu`, `log(1+u) ≥ u/(1+u)`). The defects telescope, the geometric means
telescope to `(|z+n+1|/|z|)^θ`, and `(|z+n+1|/n)^θ → 1`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.Stirling

open Complex Real Filter Topology

lemma sq_norm_eq (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

lemma one_le_norm_of_re {z : ℂ} (hz : 1 ≤ z.re) : 1 ≤ ‖z‖ := by
  have := Complex.abs_re_le_norm z; rw [abs_of_pos (by linarith)] at this; linarith

/-- **Almost log-concavity of `x ↦ |x+iy|`.** -/
lemma norm_add_ofReal_le {w : ℂ} (hw : 1 ≤ w.re) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ‖w + θ‖ ≤ Real.exp (θ * (5 / (w.re - 1 / 2) - 5 / (w.re + 1 / 2))) * ‖w + 1‖ ^ θ *
      ‖w‖ ^ (1 - θ) := by
  set x := w.re with hx
  set y := w.im with hy
  have hA : ‖w‖ ^ 2 = x ^ 2 + y ^ 2 := sq_norm_eq w
  have hB : ‖w + 1‖ ^ 2 = (x + 1) ^ 2 + y ^ 2 := by rw [sq_norm_eq]; simp [hx, hy]
  have hM : ‖w + θ‖ ^ 2 = (x + θ) ^ 2 + y ^ 2 := by rw [sq_norm_eq]; simp [hx, hy]
  set A := x ^ 2 + y ^ 2 with hAdef
  set B := (x + 1) ^ 2 + y ^ 2 with hBdef
  set M := (x + θ) ^ 2 + y ^ 2 with hMdef
  have hx2 : x ^ 2 ≤ A := by nlinarith [sq_nonneg y]
  have hxB : x ^ 2 ≤ B := by nlinarith [sq_nonneg y]
  have hA0 : 0 < A := by nlinarith
  have hB0 : 0 < B := by nlinarith
  have hM0 : 0 < M := by nlinarith [sq_nonneg y]
  have nw : 0 < ‖w‖ := lt_of_lt_of_le one_pos (one_le_norm_of_re hw)
  have nw1 : 0 < ‖w + 1‖ := lt_of_lt_of_le one_pos (one_le_norm_of_re (by simp; linarith))
  have nwθ : 0 < ‖w + θ‖ := lt_of_lt_of_le one_pos (one_le_norm_of_re (by simp; linarith))
  -- logarithmic inequalities
  have l1 : Real.log M - Real.log A ≤ θ * (2 * x + 1) / A := by
    rw [← Real.log_div hM0.ne' hA0.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos hM0 hA0)).trans ?_
    rw [div_sub_one hA0.ne', div_le_div_iff_of_pos_right hA0]
    nlinarith
  have l2 : (2 * x + 1) / B ≤ Real.log B - Real.log A := by
    have := Real.log_le_sub_one_of_pos (div_pos hA0 hB0)
    rw [Real.log_div hA0.ne' hB0.ne'] at this
    have e : (2 * x + 1) / B = 1 - A / B := by
      field_simp; rw [hAdef, hBdef]; ring
    rw [e]; linarith
  have hx1 : (1:ℝ) ≤ x := hw
  have l3 : (2 * x + 1) / A - (2 * x + 1) / B ≤ 10 / (x ^ 2 - 1 / 4) := by
    have e : (2 * x + 1) / A - (2 * x + 1) / B = (2 * x + 1) ^ 2 / (A * B) := by
      field_simp; rw [hAdef, hBdef]; ring
    rw [e]
    have h9 : (2 * x + 1) ^ 2 / (A * B) ≤ 9 / x ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : x ^ 2 * x ^ 2 ≤ A * B := mul_le_mul hx2 hxB (by positivity) hA0.le
      nlinarith
    refine h9.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
    nlinarith
  have hg : 5 / (x - 1 / 2) - 5 / (x + 1 / 2) = 5 / (x ^ 2 - 1 / 4) := by
    have h1' : x - 1 / 2 ≠ 0 := by intro h; linarith
    have h2' : x + 1 / 2 ≠ 0 := by intro h; linarith
    have h3' : x ^ 2 - 1 / 4 ≠ 0 := by intro h; nlinarith
    rw [div_sub_div _ _ h1' h2', show 5 * (x + 1 / 2) - (x - 1 / 2) * 5 = 5 by ring,
      show (x - 1 / 2) * (x + 1 / 2) = x ^ 2 - 1 / 4 by ring]
  -- in terms of logs of norms
  have eM : Real.log M = 2 * Real.log ‖w + θ‖ := by
    rw [← hM, Real.log_pow]; push_cast; ring
  have eA : Real.log A = 2 * Real.log ‖w‖ := by rw [← hA, Real.log_pow]; push_cast; ring
  have eB : Real.log B = 2 * Real.log ‖w + 1‖ := by rw [← hB, Real.log_pow]; push_cast; ring
  have key : Real.log ‖w + θ‖ ≤ θ * (5 / (x - 1 / 2) - 5 / (x + 1 / 2)) +
      Real.log ‖w + 1‖ * θ + Real.log ‖w‖ * (1 - θ) := by
    rw [hg]
    have hθl : θ * ((2 * x + 1) / A) - θ * ((2 * x + 1) / B) ≤ θ * (10 / (x ^ 2 - 1 / 4)) := by
      rw [← mul_sub]; exact mul_le_mul_of_nonneg_left l3 h0
    have l2' : θ * ((2 * x + 1) / B) ≤ θ * (Real.log B - Real.log A) :=
      mul_le_mul_of_nonneg_left l2 h0
    have e10 : θ * (10 / (x ^ 2 - 1 / 4)) = 2 * (θ * (5 / (x ^ 2 - 1 / 4))) := by ring
    have l1' : Real.log M - Real.log A ≤ θ * ((2 * x + 1) / A) := by
      rw [mul_div_assoc'] ; exact l1
    rw [eM, eA, eB] at *
    nlinarith
  calc ‖w + θ‖ = Real.exp (Real.log ‖w + θ‖) := (Real.exp_log nwθ).symm
    _ ≤ Real.exp (θ * (5 / (x - 1 / 2) - 5 / (x + 1 / 2)) +
          Real.log ‖w + 1‖ * θ + Real.log ‖w‖ * (1 - θ)) := Real.exp_le_exp.2 key
    _ = _ := by
        rw [Real.rpow_def_of_pos nw1, Real.rpow_def_of_pos nw, ← Real.exp_add, ← Real.exp_add]

/-- The telescoped product bound. -/
lemma prod_norm_add_le {z : ℂ} (hz : 1 ≤ z.re) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (n : ℕ) :
    (∏ j ∈ Finset.range n, ‖z + θ + j‖) * ‖z‖ ^ θ ≤
      Real.exp (θ * (5 / (z.re - 1 / 2) - 5 / (z.re + n - 1 / 2))) * ‖z + n‖ ^ θ *
        ∏ j ∈ Finset.range n, ‖z + j‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hre : (z + n).re = z.re + n := by simp
    have key := norm_add_ofReal_le (w := z + n) (by rw [hre]; linarith) h0 h1
    rw [hre] at key
    have e1 : z + (n : ℂ) + (θ : ℂ) = z + θ + n := by ring
    have e2 : z + (n : ℂ) + 1 = z + ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e1, e2] at key
    have hzn : 0 < ‖z + n‖ := by
      have := Complex.abs_re_le_norm (z + n); rw [hre] at this
      have : 0 < |z.re + n| := by rw [abs_of_pos (by linarith)]; linarith
      linarith
    have hP : 0 ≤ ∏ j ∈ Finset.range n, ‖z + j‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
    calc (∏ j ∈ Finset.range n, ‖z + θ + j‖) * ‖z + θ + n‖ * ‖z‖ ^ θ
        = ((∏ j ∈ Finset.range n, ‖z + θ + j‖) * ‖z‖ ^ θ) * ‖z + θ + n‖ := by ring
      _ ≤ (Real.exp (θ * (5 / (z.re - 1 / 2) - 5 / (z.re + n - 1 / 2))) * ‖z + n‖ ^ θ *
            ∏ j ∈ Finset.range n, ‖z + j‖) *
          (Real.exp (θ * (5 / (z.re + n - 1 / 2) - 5 / (z.re + n + 1 / 2))) *
            ‖z + ((n + 1 : ℕ) : ℂ)‖ ^ θ * ‖z + n‖ ^ (1 - θ)) := by
          gcongr
      _ = Real.exp (θ * (5 / (z.re - 1 / 2) - 5 / (z.re + n - 1 / 2)) +
            θ * (5 / (z.re + n - 1 / 2) - 5 / (z.re + n + 1 / 2))) *
            ‖z + ((n + 1 : ℕ) : ℂ)‖ ^ θ * ((∏ j ∈ Finset.range n, ‖z + j‖) *
              (‖z + n‖ ^ θ * ‖z + n‖ ^ (1 - θ))) := by rw [Real.exp_add]; ring
      _ = _ := by
          rw [← Real.rpow_add hzn, show θ + (1 - θ) = 1 by ring, Real.rpow_one]
          congr 2
          · congr 1; push_cast; ring

/-- **Core inequality.** For `Re z ≥ 1` and `0 ≤ θ ≤ 1`: `‖Γ(z)‖ ‖z‖^θ ≤ e¹⁰ ‖Γ(z+θ)‖`. -/
theorem norm_Gamma_mul_rpow_le {z : ℂ} (hz : 1 ≤ z.re) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ‖Complex.Gamma z‖ * ‖z‖ ^ θ ≤ Real.exp 10 * ‖Complex.Gamma (z + θ)‖ := by
  set c : ℝ := ‖z + 1‖ with hc
  have hlimL : Tendsto (fun n : ℕ => ‖Complex.GammaSeq z n‖ * ‖z‖ ^ θ) atTop
      (𝓝 (‖Complex.Gamma z‖ * ‖z‖ ^ θ)) :=
    ((Complex.GammaSeq_tendsto_Gamma z).norm).mul_const _
  have hlimR : Tendsto (fun n : ℕ => Real.exp 10 * (1 + c / n) * ‖Complex.GammaSeq (z + θ) n‖) atTop
      (𝓝 (Real.exp 10 * (1 + 0) * ‖Complex.Gamma (z + θ)‖)) :=
    ((tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat c)).const_mul _).mul
      (Complex.GammaSeq_tendsto_Gamma (z + θ)).norm
  rw [add_zero, mul_one] at hlimR
  refine le_of_tendsto_of_tendsto hlimL hlimR ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : 0 < n := hn
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hzpos : ∀ j : ℕ, 0 < ‖z + j‖ := by
    intro j
    have := Complex.abs_re_le_norm (z + j)
    have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
    simp only [add_re, natCast_re] at this
    rw [abs_of_pos (by linarith)] at this; linarith
  have hzθpos : ∀ j : ℕ, 0 < ‖z + θ + j‖ := by
    intro j
    have := Complex.abs_re_le_norm (z + θ + j)
    have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
    simp only [add_re, natCast_re, ofReal_re] at this
    rw [abs_of_pos (by linarith)] at this; linarith
  set P := ∏ j ∈ Finset.range (n + 1), ‖z + j‖ with hPdef
  set Q := ∏ j ∈ Finset.range (n + 1), ‖z + θ + j‖ with hQdef
  have hP : 0 < P := Finset.prod_pos fun j _ => hzpos j
  have hQ : 0 < Q := Finset.prod_pos fun j _ => hzθpos j
  have gz : ‖Complex.GammaSeq z n‖ = (n : ℝ) ^ z.re * (n.factorial : ℝ) / P := by
    unfold Complex.GammaSeq
    rw [norm_div, norm_mul, norm_natCast_cpow_of_pos hn0, norm_prod, Complex.norm_natCast]
  have gzθ : ‖Complex.GammaSeq (z + θ) n‖ = (n : ℝ) ^ z.re * (n : ℝ) ^ θ * (n.factorial : ℝ) / Q := by
    unfold Complex.GammaSeq
    rw [norm_div, norm_mul, norm_natCast_cpow_of_pos hn0, norm_prod, Complex.norm_natCast]
    simp only [add_re, ofReal_re]
    rw [Real.rpow_add hnR]
  -- the product bound at `n+1`
  have hprod := prod_norm_add_le hz h0 h1 (n + 1)
  rw [← hPdef, ← hQdef] at hprod
  have hexp : θ * (5 / (z.re - 1 / 2) - 5 / (z.re + ((n + 1 : ℕ) : ℝ) - 1 / 2)) ≤ 10 := by
    have hn1 : (0:ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have a1 : 5 / (z.re - 1 / 2) ≤ 10 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have a2 : 0 ≤ 5 / (z.re + ((n + 1 : ℕ) : ℝ) - 1 / 2) := div_nonneg (by norm_num) (by linarith)
    have a3 : 5 / (z.re + ((n + 1 : ℕ) : ℝ) - 1 / 2) ≤ 5 / (z.re - 1 / 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    nlinarith
  have hprod' : Q * ‖z‖ ^ θ ≤ Real.exp 10 * ‖z + ((n + 1 : ℕ) : ℂ)‖ ^ θ * P := by
    refine hprod.trans ?_
    gcongr
  -- `‖z + n + 1‖^θ ≤ n^θ (1 + c/n)`
  have hnorm : ‖z + ((n + 1 : ℕ) : ℂ)‖ ≤ (n : ℝ) * (1 + c / n) := by
    rw [mul_add, mul_one, mul_div_cancel₀ _ hnR.ne']
    have : z + ((n + 1 : ℕ) : ℂ) = (z + 1) + (n : ℂ) := by push_cast; ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_natCast]; linarith
  have hc0 : 0 ≤ c := norm_nonneg _
  have h1c : 1 ≤ 1 + c / n := by have : 0 ≤ c / n := by positivity
                                 linarith
  have hpow : ‖z + ((n + 1 : ℕ) : ℂ)‖ ^ θ ≤ (n : ℝ) ^ θ * (1 + c / n) := by
    calc ‖z + ((n + 1 : ℕ) : ℂ)‖ ^ θ ≤ ((n : ℝ) * (1 + c / n)) ^ θ :=
          Real.rpow_le_rpow (norm_nonneg _) hnorm h0
      _ = (n : ℝ) ^ θ * (1 + c / n) ^ θ := Real.mul_rpow hnR.le (by linarith)
      _ ≤ (n : ℝ) ^ θ * (1 + c / n) := by
          gcongr
          calc (1 + c / n) ^ θ ≤ (1 + c / n) ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le h1c h1
            _ = 1 + c / n := Real.rpow_one _
  rw [gz, gzθ]
  have hnx : 0 < (n : ℝ) ^ z.re * (n.factorial : ℝ) := by positivity
  calc (n : ℝ) ^ z.re * (n.factorial : ℝ) / P * ‖z‖ ^ θ
      = ((n : ℝ) ^ z.re * (n.factorial : ℝ) / (P * Q)) * (Q * ‖z‖ ^ θ) := by
        field_simp
    _ ≤ ((n : ℝ) ^ z.re * (n.factorial : ℝ) / (P * Q)) *
          (Real.exp 10 * ((n : ℝ) ^ θ * (1 + c / n)) * P) := by
        exact mul_le_mul_of_nonneg_left (hprod'.trans (by gcongr)) (by positivity)
    _ = Real.exp 10 * (1 + c / n) * ((n : ℝ) ^ z.re * (n : ℝ) ^ θ * (n.factorial : ℝ) / Q) := by
        field_simp

lemma norm_le_norm_add_ofReal {z : ℂ} (hz : 0 ≤ z.re) {θ : ℝ} (h0 : 0 ≤ θ) : ‖z‖ ≤ ‖z + θ‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), sq_norm_eq, sq_norm_eq]; simp; nlinarith

/-- **Upper bound, `0 ≤ θ ≤ 1`.** `‖Γ(z+θ)‖ ≤ e¹⁰ ‖z‖^θ ‖Γ(z)‖` for `Re z ≥ 1`. -/
theorem norm_Gamma_add_le_one {z : ℂ} (hz : 1 ≤ z.re) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ‖Complex.Gamma (z + θ)‖ ≤ Real.exp 10 * ‖z‖ ^ θ * ‖Complex.Gamma z‖ := by
  have hzθ : 1 ≤ (z + θ).re := by simp; linarith
  have hc := norm_Gamma_mul_rpow_le hzθ (θ := 1 - θ) (by linarith) (by linarith)
  have e : z + (θ : ℂ) + ((1 - θ : ℝ) : ℂ) = z + 1 := by push_cast; ring
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz; linarith
  rw [e, Complex.Gamma_add_one z hz0, norm_mul] at hc
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos (one_le_norm_of_re hz)
  have hmono : ‖z‖ ^ (1 - θ) ≤ ‖z + θ‖ ^ (1 - θ) :=
    Real.rpow_le_rpow (norm_nonneg _) (norm_le_norm_add_ofReal (by linarith) h0) (by linarith)
  have hsplit : ‖z‖ = ‖z‖ ^ θ * ‖z‖ ^ (1 - θ) := by
    rw [← Real.rpow_add hzpos, show θ + (1 - θ) = 1 by ring, Real.rpow_one]
  have hpos : 0 < ‖z‖ ^ (1 - θ) := Real.rpow_pos_of_pos hzpos _
  have : ‖Complex.Gamma (z + θ)‖ * ‖z‖ ^ (1 - θ) ≤
      (Real.exp 10 * ‖z‖ ^ θ * ‖Complex.Gamma z‖) * ‖z‖ ^ (1 - θ) := by
    calc ‖Complex.Gamma (z + θ)‖ * ‖z‖ ^ (1 - θ)
        ≤ ‖Complex.Gamma (z + θ)‖ * ‖z + θ‖ ^ (1 - θ) := by gcongr
      _ ≤ Real.exp 10 * (‖z‖ * ‖Complex.Gamma z‖) := hc
      _ = Real.exp 10 * ((‖z‖ ^ θ * ‖z‖ ^ (1 - θ)) * ‖Complex.Gamma z‖) := by rw [← hsplit]
      _ = _ := by ring
  exact le_of_mul_le_mul_right this hpos

/-- **Lower bound, every real `θ ≥ 0`.** `‖Γ(z)‖ ‖z‖^θ ≤ e¹⁰ ‖Γ(z+θ)‖` for `Re z ≥ 1`. -/
theorem norm_Gamma_mul_rpow_le_add {z : ℂ} (hz : 1 ≤ z.re) {θ : ℝ} (h0 : 0 ≤ θ) :
    ‖Complex.Gamma z‖ * ‖z‖ ^ θ ≤ Real.exp 10 * ‖Complex.Gamma (z + θ)‖ := by
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos (one_le_norm_of_re hz)
  suffices H : ∀ n : ℕ, ∀ θ : ℝ, 0 ≤ θ → θ ≤ n + 1 →
      ‖Complex.Gamma z‖ * ‖z‖ ^ θ ≤ Real.exp 10 * ‖Complex.Gamma (z + θ)‖ by
    obtain ⟨n, hn⟩ := exists_nat_ge θ
    exact H n θ h0 (by linarith)
  intro n
  induction n with
  | zero => intro θ h0 h1; exact norm_Gamma_mul_rpow_le hz h0 (by simpa using h1)
  | succ n ih =>
    intro θ h0 h1
    rcases le_or_gt θ (n + 1) with h | h
    · exact ih θ h0 h
    · have hθ1 : 0 ≤ θ - 1 := by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
      have hIH := ih (θ - 1) hθ1 (by push_cast at h1; linarith)
      have hne : z + ((θ - 1 : ℝ) : ℂ) ≠ 0 := by
        intro h'; have := congrArg re h'; simp at this; linarith
      have hG : Complex.Gamma (z + θ) = (z + ((θ - 1 : ℝ) : ℂ)) *
          Complex.Gamma (z + ((θ - 1 : ℝ) : ℂ)) := by
        rw [← Complex.Gamma_add_one _ hne]; congr 1; push_cast; ring
      have hnorm : ‖z‖ ≤ ‖z + ((θ - 1 : ℝ) : ℂ)‖ := norm_le_norm_add_ofReal (by linarith) hθ1
      have hsplit : ‖z‖ ^ θ = ‖z‖ ^ (θ - 1) * ‖z‖ := by
        rw [← Real.rpow_add_one hzpos.ne']; ring_nf
      rw [hG, norm_mul, hsplit]
      calc ‖Complex.Gamma z‖ * (‖z‖ ^ (θ - 1) * ‖z‖)
          = (‖Complex.Gamma z‖ * ‖z‖ ^ (θ - 1)) * ‖z‖ := by ring
        _ ≤ (Real.exp 10 * ‖Complex.Gamma (z + ((θ - 1 : ℝ) : ℂ))‖) *
            ‖z + ((θ - 1 : ℝ) : ℂ)‖ := by gcongr
        _ = _ := by ring

/-- **Upper bound, every real `0 ≤ θ ≤ n+1`.** `‖Γ(z+θ)‖ ≤ (n+1)! e¹⁰ ‖z‖^θ ‖Γ(z)‖`
for `Re z ≥ 1`. -/
theorem norm_Gamma_add_le {z : ℂ} (hz : 1 ≤ z.re) (n : ℕ) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ n + 1) :
    ‖Complex.Gamma (z + θ)‖ ≤ ((n + 1).factorial : ℝ) * Real.exp 10 * ‖z‖ ^ θ *
      ‖Complex.Gamma z‖ := by
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos (one_le_norm_of_re hz)
  have hz1 : 1 ≤ ‖z‖ := one_le_norm_of_re hz
  induction n generalizing θ with
  | zero =>
    have := norm_Gamma_add_le_one hz h0 (by simpa using h1)
    simpa using this
  | succ n ih =>
    rcases le_or_gt θ (n + 1) with h | h
    · refine (ih h0 h).trans ?_
      have hf : ((n + 1).factorial : ℝ) ≤ ((n + 1 + 1).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_le (by omega)
      gcongr
    · have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
      have hθ1 : 0 ≤ θ - 1 := by linarith
      have hIH := ih hθ1 (by push_cast at h1; linarith)
      have hne : z + ((θ - 1 : ℝ) : ℂ) ≠ 0 := by
        intro h'; have := congrArg re h'; simp at this; linarith
      have hG : Complex.Gamma (z + θ) = (z + ((θ - 1 : ℝ) : ℂ)) *
          Complex.Gamma (z + ((θ - 1 : ℝ) : ℂ)) := by
        rw [← Complex.Gamma_add_one _ hne]; congr 1; push_cast; ring
      have hnorm : ‖z + ((θ - 1 : ℝ) : ℂ)‖ ≤ (n + 2) * ‖z‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ1]
        push_cast at h1
        nlinarith
      have hsplit : ‖z‖ ^ θ = ‖z‖ ^ (θ - 1) * ‖z‖ := by
        rw [← Real.rpow_add_one hzpos.ne']; ring_nf
      have hfac : ((n + 1 + 1).factorial : ℝ) = (n + 2) * ((n + 1).factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      rw [hG, norm_mul, hsplit, hfac]
      calc ‖z + ((θ - 1 : ℝ) : ℂ)‖ * ‖Complex.Gamma (z + ((θ - 1 : ℝ) : ℂ))‖
          ≤ ((n + 2) * ‖z‖) * (((n + 1).factorial : ℝ) * Real.exp 10 * ‖z‖ ^ (θ - 1) *
            ‖Complex.Gamma z‖) := by gcongr
        _ = _ := by ring

/-! ### The ratio in `t`-form -/

/-- `‖Γ(α+it)‖ ≤ (n+1)! e¹⁰ ‖β+it‖^{α−β} ‖Γ(β+it)‖` for `1 ≤ β ≤ α ≤ β+n+1`. -/
theorem norm_Gamma_ratio_le_of_le {α β : ℝ} (hβ : 1 ≤ β) (hαβ : β ≤ α) (n : ℕ)
    (hn : α - β ≤ n + 1) (t : ℝ) :
    ‖Complex.Gamma (α + t * I)‖ ≤ ((n + 1).factorial : ℝ) * Real.exp 10 *
      ‖(β : ℂ) + t * I‖ ^ (α - β) * ‖Complex.Gamma (β + t * I)‖ := by
  have h := norm_Gamma_add_le (z := (β : ℂ) + t * I) (by simpa using hβ) n
    (θ := α - β) (by linarith) hn
  have e : (β : ℂ) + t * I + ((α - β : ℝ) : ℂ) = α + t * I := by push_cast; ring
  rwa [e] at h

/-- `‖Γ(α+it)‖ ≤ e¹⁰ ‖α+it‖^{α−β} ‖Γ(β+it)‖` for `1 ≤ α ≤ β` (the exponent is `≤ 0`). -/
theorem norm_Gamma_ratio_le_of_ge {α β : ℝ} (hα : 1 ≤ α) (hαβ : α ≤ β) (t : ℝ) :
    ‖Complex.Gamma (α + t * I)‖ ≤ Real.exp 10 * ‖(α : ℂ) + t * I‖ ^ (α - β) *
      ‖Complex.Gamma (β + t * I)‖ := by
  have hz : 1 ≤ ((α : ℂ) + t * I).re := by simpa using hα
  have h := norm_Gamma_mul_rpow_le_add hz (θ := β - α) (by linarith)
  have e : (α : ℂ) + t * I + ((β - α : ℝ) : ℂ) = β + t * I := by push_cast; ring
  rw [e] at h
  have hpos : 0 < ‖(α : ℂ) + t * I‖ := lt_of_lt_of_le one_pos (one_le_norm_of_re hz)
  have hp : 0 < ‖(α : ℂ) + t * I‖ ^ (β - α) := Real.rpow_pos_of_pos hpos _
  have hinv : ‖(α : ℂ) + t * I‖ ^ (α - β) * ‖(α : ℂ) + t * I‖ ^ (β - α) = 1 := by
    rw [← Real.rpow_add hpos]; simp
  rw [← le_div_iff₀ hp] at h
  calc ‖Complex.Gamma (α + t * I)‖ ≤ Real.exp 10 * ‖Complex.Gamma (β + t * I)‖ /
        ‖(α : ℂ) + t * I‖ ^ (β - α) := h
    _ = _ := by field_simp; rw [mul_assoc, mul_comm (‖(α : ℂ) + t * I‖ ^ (β - α)), hinv, mul_one]

end RamanujanTau.Stirling

#print axioms RamanujanTau.Stirling.norm_Gamma_mul_rpow_le
#print axioms RamanujanTau.Stirling.norm_Gamma_mul_rpow_le_add
#print axioms RamanujanTau.Stirling.norm_Gamma_add_le
#print axioms RamanujanTau.Stirling.norm_Gamma_ratio_le_of_le
#print axioms RamanujanTau.Stirling.norm_Gamma_ratio_le_of_ge
