/-
# `ζ` to the left of `1/2` in mean square, via the functional equation

* `norm_zeta_fe_le`: for `0 < v ≤ 1/2`, `τ ≥ 2`,
  `|ζ(v − iτ)| ≤ K τ^{1/2−v} |ζ(1−v+iτ)|` (`Λ(s) = Λ(1−s)`, uniform Stirling ratio
  `RankinLandau.norm_Gamma_ratio_unif'`);
* `zeta_dyadic_upper`: `∫_T^{2T} |ζ(u+it)|² ≤ C T` for fixed `1/2 < u ≤ 1` (from `zeta_mean_value_dyadic`);
* `zeta_two_s_mean_sq`: for `0 < σ < 1/4`, `∫_Y^{2Y} |ζ(2(σ − iy))|² dy ≤ K Y^{2−4σ}` (`Y ≥ 1`).
-/
import RamanujanTau.ZetaMeanSquare.Zeta
import RamanujanTau.RankinLandau.GammaUnif

set_option autoImplicit false

namespace RamanujanTau.ZetaMeanSquare

open Complex MeasureTheory Set Filter Topology

lemma norm_Gammaℝ (s : ℂ) : ‖Gammaℝ s‖ = Real.pi ^ (-s.re / 2) * ‖Complex.Gamma (s / 2)‖ := by
  rw [Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 2; simp

/-- **Functional-equation bound** for `ζ` left of the critical line. -/
theorem norm_zeta_fe_le : ∃ K : ℝ, 0 < K ∧ ∀ v τ : ℝ, 0 < v → v ≤ 1 / 2 → 2 ≤ τ →
    ‖riemannZeta ((v : ℂ) - τ * I)‖ ≤
      K * τ ^ ((1 : ℝ) / 2 - v) * ‖riemannZeta (((1 - v : ℝ) : ℂ) + τ * I)‖ := by
  obtain ⟨C, hC0, hC⟩ := RamanujanTau.RankinLandau.norm_Gamma_ratio_unif' (R := 2) (by norm_num)
  refine ⟨2 * C, by positivity, fun v τ hv0 hv τ2 => ?_⟩
  have hτ0 : 0 < τ := by linarith
  set z : ℂ := (v : ℂ) - τ * I with hz
  have hzre : z.re = v := by simp [hz]
  have hzim : z.im = -τ := by simp [hz]
  have h1z : 1 - z = ((1 - v : ℝ) : ℂ) + τ * I := by rw [hz]; push_cast; ring
  have hz0 : z ≠ 0 := by intro h; rw [h] at hzim; simp at hzim; linarith
  have h1z0 : 1 - z ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [h1z] at this; simp at this; linarith
  have hre1 : 0 < (1 - z).re := by rw [h1z]; simp; linarith
  have e1 := riemannZeta_def_of_ne_zero hz0
  have e2 := riemannZeta_def_of_ne_zero h1z0
  have hG1 : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hzre]; exact hv0)
  have hG2 : Gammaℝ (1 - z) ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre1
  have hfe : riemannZeta z * Gammaℝ z = riemannZeta (1 - z) * Gammaℝ (1 - z) := by
    rw [e1, e2, completedRiemannZeta_one_sub, div_mul_cancel₀ _ hG1, div_mul_cancel₀ _ hG2]
  have hn := congrArg norm hfe
  simp only [norm_mul] at hn
  rw [norm_Gammaℝ, norm_Gammaℝ] at hn
  -- the Γ ratio
  set z1 : ℂ := (1 - z) / 2 with hz1
  set z2 : ℂ := z / 2 with hz2
  have hz1re : z1.re = (1 - v) / 2 := by rw [hz1, h1z]; simp
  have hz1im : z1.im = τ / 2 := by rw [hz1, h1z]; simp
  have hz2re : z2.re = v / 2 := by rw [hz2]; simp [hzre]
  have hz2im : z2.im = -(τ / 2) := by rw [hz2]; simp [hzim]; ring
  have hz10 : z1 ≠ 0 := by intro h; rw [h] at hz1im; simp at hz1im; linarith
  have hz20 : z2 ≠ 0 := by intro h; rw [h] at hz2im; simp at hz2im; linarith
  have g := hC (z1 + 1) (z2 + 1) (by simp [hz1re]; linarith) (by simp [hz1re]; linarith)
    (by simp [hz2re]; linarith) (by simp [hz2re]; linarith) (by simp [hz1im, hz2im, abs_neg])
  rw [Complex.Gamma_add_one z1 hz10, Complex.Gamma_add_one z2 hz20, norm_mul, norm_mul] at g
  have ex : (z1 + 1).re - (z2 + 1).re = 1 / 2 - v := by simp [hz1re, hz2re]; ring
  have eim : |(z2 + 1).im| = τ / 2 := by
    rw [show (z2 + 1).im = -(τ / 2) by simp [hz2im], abs_neg, abs_of_pos (by linarith)]
  rw [ex, eim] at g
  have hp : (1 + τ / 2) ^ ((1 : ℝ) / 2 - v) ≤ τ ^ ((1 : ℝ) / 2 - v) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
  have hn1 : τ / 2 ≤ ‖z1‖ := by
    have := Complex.abs_im_le_norm z1; rw [hz1im, abs_of_pos (by linarith)] at this; exact this
  have hn2 : ‖z2‖ ≤ τ := by
    refine (Complex.norm_le_abs_re_add_abs_im z2).trans ?_
    rw [hz2re, hz2im, abs_neg, abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
  have hGz2 : 0 < ‖Complex.Gamma z2‖ :=
    norm_pos_iff.2 (Complex.Gamma_ne_zero_of_re_pos (by rw [hz2re]; linarith))
  have hGz1 : 0 ≤ ‖Complex.Gamma z1‖ := norm_nonneg _
  have hτp : 0 ≤ τ ^ ((1 : ℝ) / 2 - v) := by positivity
  have hratio : ‖Complex.Gamma z1‖ ≤ 2 * C * τ ^ ((1 : ℝ) / 2 - v) * ‖Complex.Gamma z2‖ := by
    have hz1p : 0 < ‖z1‖ := by linarith
    have : ‖z1‖ * ‖Complex.Gamma z1‖ ≤ ‖z1‖ * (2 * C * τ ^ ((1 : ℝ) / 2 - v) * ‖Complex.Gamma z2‖) := by
      calc ‖z1‖ * ‖Complex.Gamma z1‖
          ≤ C * (1 + τ / 2) ^ ((1 : ℝ) / 2 - v) * (‖z2‖ * ‖Complex.Gamma z2‖) := g
        _ ≤ C * τ ^ ((1 : ℝ) / 2 - v) * (τ * ‖Complex.Gamma z2‖) := by gcongr
        _ = (τ / 2) * (2 * C * τ ^ ((1 : ℝ) / 2 - v) * ‖Complex.Gamma z2‖) := by ring
        _ ≤ ‖z1‖ * (2 * C * τ ^ ((1 : ℝ) / 2 - v) * ‖Complex.Gamma z2‖) := by gcongr
    exact le_of_mul_le_mul_left this hz1p
  -- π factors
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hP : Real.pi ^ (-(1 - z).re / 2) ≤ Real.pi ^ (-z.re / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le hpi1
    have h1re : (1 - z).re = 1 - v := by rw [h1z]; simp
    rw [h1re, hzre]
    linarith
  have hP0 : 0 < Real.pi ^ (-z.re / 2) := by positivity
  have hP10 : 0 ≤ Real.pi ^ (-(1 - z).re / 2) := by positivity
  rw [← h1z]
  set A := ‖riemannZeta z‖
  set B := ‖riemannZeta (1 - z)‖
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  have key : A * (Real.pi ^ (-z.re / 2) * ‖Complex.Gamma z2‖) ≤
      (2 * C * τ ^ ((1 : ℝ) / 2 - v) * B) * (Real.pi ^ (-z.re / 2) * ‖Complex.Gamma z2‖) := by
    rw [hn]
    calc B * (Real.pi ^ (-(1 - z).re / 2) * ‖Complex.Gamma z1‖)
        ≤ B * (Real.pi ^ (-z.re / 2) * (2 * C * τ ^ ((1 : ℝ) / 2 - v) * ‖Complex.Gamma z2‖)) := by
          gcongr
      _ = _ := by ring
  exact le_of_mul_le_mul_right key (by positivity)

/-- `∫_T^{2T} |ζ(u+it)|² ≤ C T` for fixed `1/2 < u ≤ 1`. -/
theorem zeta_dyadic_upper {u : ℝ} (h1 : 1 / 2 < u) (h2 : u ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      ∫ t in T..2 * T, ‖riemannZeta ((u : ℂ) + t * I)‖ ^ 2 ≤ C * T := by
  obtain ⟨C, hC, h⟩ := zeta_mean_value_dyadic h1
  obtain ⟨c, hc, hE⟩ := Eσ_div_le h1
  refine ⟨|(riemannZeta (2 * (u : ℂ))).re| + C * c, by positivity, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hb := (abs_le.1 (h u le_rfl h2 T hT)).2
  have hET := hE T hT
  unfold Eσ at hET
  rw [div_le_iff₀ hT0] at hET
  have hr : T ^ (-(u - 1 / 2)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT (by linarith)
  have h3 : C * (T ^ ((3 : ℝ) / 2 - u) + T ^ (2 - 2 * u) * (1 + Real.log T) ^ 2) ≤ C * c * T := by
    calc _ ≤ C * (c * T ^ (-(u - 1 / 2)) * T) := by gcongr
      _ ≤ C * (c * 1 * T) := by gcongr
      _ = C * c * T := by ring
  have h4 : (riemannZeta (2 * (u : ℂ))).re * T ≤ |(riemannZeta (2 * (u : ℂ))).re| * T :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hT0.le
  nlinarith

/-- **Mean square of `ζ(2s)` on `Re s = σ ∈ (0, 1/4)`**, below the real axis. -/
theorem zeta_two_s_mean_sq {σ : ℝ} (h1 : 0 < σ) (h2 : σ < 1 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 1 ≤ Y →
      ∫ y in Y..2 * Y, ‖riemannZeta (2 * ((σ : ℂ) - y * I))‖ ^ 2 ≤ K * Y ^ (2 - 4 * σ) := by
  obtain ⟨Kχ, hKχ, hfe⟩ := norm_zeta_fe_le
  obtain ⟨Cu, hCu, hup⟩ := zeta_dyadic_upper (u := 1 - 2 * σ) (by linarith) (by linarith)
  refine ⟨Kχ ^ 2 * 4 ^ (1 - 4 * σ) * Cu, by positivity, fun Y hY => ?_⟩
  have hY0 : 0 < Y := by linarith
  set e : ℝ := 1 - 4 * σ with he
  have he0 : 0 ≤ e := by rw [he]; linarith
  -- pointwise
  have hpt : ∀ y ∈ Icc Y (2 * Y), ‖riemannZeta (2 * ((σ : ℂ) - y * I))‖ ^ 2 ≤
      Kχ ^ 2 * (4 * Y) ^ e * ‖riemannZeta (((1 - 2 * σ : ℝ) : ℂ) + ((2 * y : ℝ) : ℂ) * I)‖ ^ 2 := by
    intro y hy
    have hy1 : 1 ≤ y := le_trans hY hy.1
    have h := hfe (2 * σ) (2 * y) (by linarith) (by linarith) (by linarith)
    have e1 : ((2 * σ : ℝ) : ℂ) - ((2 * y : ℝ) : ℂ) * I = 2 * ((σ : ℂ) - y * I) := by push_cast; ring
    rw [e1, show (1 : ℝ) / 2 - 2 * σ = (1 / 2) * e by rw [he]; ring] at h
    have hq : (2 * y) ^ ((1 / 2) * e) ≤ (4 * Y) ^ ((1 / 2) * e) :=
      Real.rpow_le_rpow (by linarith) (by linarith [hy.2]) (by linarith)
    have hsq : ((4 * Y) ^ ((1 / 2) * e)) ^ 2 = (4 * Y) ^ e := by
      rw [← Real.rpow_mul_natCast (by linarith)]; congr 1; push_cast; ring
    have h0 := norm_nonneg (riemannZeta (2 * ((σ : ℂ) - y * I)))
    set Z := ‖riemannZeta (((1 - 2 * σ : ℝ) : ℂ) + ((2 * y : ℝ) : ℂ) * I)‖
    have hZ0 : 0 ≤ Z := norm_nonneg _
    have h' : ‖riemannZeta (2 * ((σ : ℂ) - y * I))‖ ≤ Kχ * (4 * Y) ^ ((1 / 2) * e) * Z := by
      refine h.trans ?_; gcongr
    have := pow_le_pow_left₀ h0 h' 2
    calc _ ≤ (Kχ * (4 * Y) ^ ((1 / 2) * e) * Z) ^ 2 := this
      _ = Kχ ^ 2 * ((4 * Y) ^ ((1 / 2) * e)) ^ 2 * Z ^ 2 := by ring
      _ = _ := by rw [hsq]
  -- continuity
  have hc1 : ContinuousOn (fun y : ℝ => ‖riemannZeta (2 * ((σ : ℂ) - y * I))‖ ^ 2)
      (uIcc Y (2 * Y)) := by
    intro y hy
    rw [uIcc_of_le (by linarith)] at hy
    have hne : 2 * ((σ : ℂ) - y * I) ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith [hy.1]
    exact ((((differentiableAt_riemannZeta hne).continuousAt.comp
      (f := fun y : ℝ => 2 * ((σ : ℂ) - y * I)) (x := y) (by fun_prop)).norm).pow 2).continuousWithinAt
  have hc2 : ContinuousOn (fun y : ℝ =>
      ‖riemannZeta (((1 - 2 * σ : ℝ) : ℂ) + ((2 * y : ℝ) : ℂ) * I)‖ ^ 2) (uIcc Y (2 * Y)) := by
    intro y hy
    rw [uIcc_of_le (by linarith)] at hy
    have hne : ((1 - 2 * σ : ℝ) : ℂ) + ((2 * y : ℝ) : ℂ) * I ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith [hy.1]
    exact ((((differentiableAt_riemannZeta hne).continuousAt.comp
      (f := fun y : ℝ => ((1 - 2 * σ : ℝ) : ℂ) + ((2 * y : ℝ) : ℂ) * I) (x := y)
      (by fun_prop)).norm).pow 2).continuousWithinAt
  have hmono := intervalIntegral.integral_mono_on (by linarith) (hc1.intervalIntegrable (μ := volume))
    ((hc2.intervalIntegrable (μ := volume)).const_mul (Kχ ^ 2 * (4 * Y) ^ e)) hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  -- change of variables `t = 2y`
  have hsub := intervalIntegral.integral_comp_mul_left (a := Y) (b := 2 * Y)
    (fun t : ℝ => ‖riemannZeta (((1 - 2 * σ : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2)
    (show (2 : ℝ) ≠ 0 by norm_num)
  simp only [smul_eq_mul] at hsub
  rw [hsub, show (2 : ℝ) * (2 * Y) = 2 * (2 * Y) by ring] at hmono
  have hU := hup (2 * Y) (by linarith)
  have hp4 : (4 * Y) ^ e = 4 ^ e * Y ^ e := Real.mul_rpow (by norm_num) hY0.le
  have hYe : Y ^ e * Y = Y ^ (2 - 4 * σ) := by
    rw [show 2 - 4 * σ = e + 1 by rw [he]; ring, Real.rpow_add hY0, Real.rpow_one]
  calc ∫ y in Y..2 * Y, ‖riemannZeta (2 * ((σ : ℂ) - y * I))‖ ^ 2
      ≤ Kχ ^ 2 * (4 * Y) ^ e * (2⁻¹ * ∫ t in 2 * Y..2 * (2 * Y),
          ‖riemannZeta (((1 - 2 * σ : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) := hmono
    _ ≤ Kχ ^ 2 * (4 * Y) ^ e * (2⁻¹ * (Cu * (2 * Y))) := by gcongr
    _ = Kχ ^ 2 * 4 ^ e * Cu * (Y ^ e * Y) := by rw [hp4]; ring
    _ = _ := by rw [hYe]

end RamanujanTau.ZetaMeanSquare
