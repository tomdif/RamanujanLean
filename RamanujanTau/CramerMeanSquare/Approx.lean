/-
# Uniform approximation of `L(Δ,σ+it)` by Dirichlet polynomials

`approx_tauL_unif` is `MeanSquare.approx_tauL` with the constant `C` chosen **before** `σ`:
the proof there produces `C = K_c (3 + A J/π)`, which depends only on the Perron shift `δ`
and the convexity exponent `ε`, not on `σ`.  The proof below is that proof verbatim, with the
quantifier over `σ` moved inside.
-/
import RamanujanTau.MeanSquare.Main

set_option autoImplicit false

namespace RamanujanTau.CramerMeanSquare

open Complex Real MeasureTheory Set Filter Topology Finset LSeries
open RamanujanTau.RankinError RamanujanTau.HeckeL RamanujanTau.MeanSquare

/-- **Uniform smoothed-polynomial approximation** (constant independent of `σ`). -/
theorem approx_tauL_unif {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 6 ≤ σ → σ ≤ 13 / 2 → 11 / 2 ≤ σ - δ →
      13 / 2 - σ + δ + ε ≤ 2 → ∀ X : ℝ, 1 ≤ X → ∀ t : ℝ,
      ‖tauL ((σ : ℂ) + t * I) - dpoly (bsm σ X) ⌊X⌋₊ t‖ ≤
        C * X ^ (-δ) * (1 + |t|) ^ (13 / 2 - σ + δ + ε) := by
  obtain ⟨K0, hK00, hK0⟩ := tauL_growth
  obtain ⟨Kc, hKc0, hKc⟩ := RamanujanTau.HeckeConvex.tauL_convexity_strip hε
  set A : ℝ := 6 * (2 / min (-(-δ)) (1 + -δ)) ^ 4 with hA
  have hA0 : 0 ≤ A := by
    have : 0 < min (-(-δ)) (1 + -δ) := lt_min (by linarith) (by linarith)
    positivity
  set J : ℝ := ∫ y : ℝ, 1 / (1 + |y|) ^ 2 with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun y => by positivity
  refine ⟨Kc * (3 + A * J / π), by positivity, fun σ hσ1 hσ2 hσδ hθ X hX t => ?_⟩
  set θ := 13 / 2 - σ + δ + ε with hθdef
  have hX0 : 0 < X := by linarith
  set s : ℂ := (σ : ℂ) + t * I with hs
  set c : ℝ := 7 - σ with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  set F : ℂ → ℂ := fun w => tauL (s + w) with hF
  have hFd : Differentiable ℂ F := tauLSeries_entire.comp (differentiable_const _ |>.add
    differentiable_id)
  have ht1 : (0 : ℝ) < 1 + |t| := by positivity
  -- growth of `F` in the strip
  have hK : ∀ w : ℂ, -δ ≤ w.re → w.re ≤ c → ‖F w‖ ≤ (K0 * (1 + |t|) ^ 2) * (1 + |w.im|) ^ 2 := by
    intro w h1 h2
    have hre : (s + w).re = σ + w.re := by simp [hsre]
    have him : (s + w).im = t + w.im := by simp [hsim]
    have := hK0 (s + w) (by rw [hre]; linarith) (by rw [hre]; linarith)
    rw [him] at this
    refine this.trans ?_
    have h3 := one_add_abs_add_le t w.im
    calc K0 * (1 + |t + w.im|) ^ 2 ≤ K0 * ((1 + |t|) * (1 + |w.im|)) ^ 2 := by
          gcongr
      _ = _ := by ring
  -- Perron
  have hP := perron_c (aS s) (aS_zero s) (k := 3) (by norm_num) hc0 hX0
    (summable_aS (by rw [hsre, hc]; ring))
  have hLS : (fun y : ℝ => (X : ℂ) ^ ln c y * Pk 3 (ln c y) * LSeries (aS s) (ln c y)) =
      fun y : ℝ => (X : ℂ) ^ ln c y * Pk 3 (ln c y) * F (ln c y) := by
    funext y
    rw [LSeries_aS (by simp [hsre, ln, hc]; norm_num)]
  rw [hLS, shift_identity hFd hX hc0 hδ0 hδ1 hK, tsum_eq_dpoly hX0 t] at hP
  -- notation
  set D := dpoly (bsm σ X) ⌊X⌋₊ t with hD
  set Ig := ∫ y : ℝ, (X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y) * F (ln (-δ) y) with hIg
  set IX := ∫ y : ℝ, (X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y) with hIX
  have hF0 : F 0 = tauL s := by simp [hF]
  have h2π : (2 * π : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  have hkey : tauL s - D = -(F 0 * ((phi 3 (1 / X) : ℂ) - 1)) - (Ig - F 0 * IX) / (2 * π) := by
    rw [hF0] at hP ⊢
    field_simp
    linear_combination (-1 : ℂ) * hP
  -- bounds
  have hXδ : X ^ (-δ) * X ^ (-δ) ≥ 0 := by positivity
  have hθ1 : 13 / 2 - σ + ε ≤ θ := by rw [hθdef]; linarith
  have hF0b : ‖F 0‖ ≤ Kc * (1 + |t|) ^ θ := by
    rw [hF0]
    have := hKc σ t (by linarith) hσ2
    refine this.trans ?_
    gcongr
    · linarith [abs_nonneg t]
  have hphi : ‖((phi 3 (1 / X) : ℂ) - 1)‖ ≤ 3 * X ^ (-δ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h1X : 1 / X ≤ X ^ (-δ) := by
      rw [one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    calc |phi 3 (1 / X) - 1| ≤ 3 / X := one_sub_phi_le hX
      _ = 3 * (1 / X) := by ring
      _ ≤ 3 * X ^ (-δ) := by gcongr
  have hlineP : ∀ y : ℝ, ‖(X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y)‖ ≤ X ^ (-δ) * A / (1 + |y|) ^ 4 := by
    intro y
    rw [norm_mul, norm_X_cpow hX0]
    have hre : (ln (-δ) y).re = -δ := by simp [ln]
    rw [hre]
    have := norm_Pk3_le_left (σ := -δ) (by linarith) (by linarith) y
    rw [mul_div_assoc]
    gcongr
  have hIX : ‖IX‖ ≤ X ^ (-δ) * A * J := by
    have hb : ∀ y : ℝ, ‖(X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y)‖ ≤ X ^ (-δ) * A / (1 + |y|) ^ 2 := by
      intro y
      refine (hlineP y).trans ?_
      have h1y : (1 : ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]
      have : (1 + |y|) ^ 2 ≤ (1 + |y|) ^ 4 := pow_le_pow_right₀ h1y (by norm_num)
      gcongr
    refine (norm_integral_le_of_norm_le (integrable_div_sq _) (ae_of_all _ hb)).trans
      (le_of_eq ?_)
    rw [hJ, ← integral_const_mul]
    congr 1; funext y; ring
  have hIg : ‖Ig‖ ≤ X ^ (-δ) * A * Kc * (1 + |t|) ^ θ * J := by
    have hb : ∀ y : ℝ, ‖(X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y) * F (ln (-δ) y)‖ ≤
        X ^ (-δ) * A * Kc * (1 + |t|) ^ θ / (1 + |y|) ^ 2 := by
      intro y
      rw [norm_mul]
      have hFy : ‖F (ln (-δ) y)‖ ≤ Kc * (1 + |t|) ^ θ * (1 + |y|) ^ θ := by
        have e : s + ln (-δ) y = ((σ - δ : ℝ) : ℂ) + ((t + y : ℝ) : ℂ) * I := by
          simp only [hs, ln]; push_cast; ring
        simp only [hF]
        rw [e]
        have := hKc (σ - δ) (t + y) hσδ (by linarith)
        have he : 13 / 2 - (σ - δ) + ε = θ := by rw [hθdef]; ring
        rw [he] at this
        refine this.trans ?_
        have h3 := one_add_abs_add_le t y
        have hθ0 : 0 ≤ θ := by rw [hθdef]; linarith
        calc Kc * (1 + |t + y|) ^ θ ≤ Kc * ((1 + |t|) * (1 + |y|)) ^ θ := by
              gcongr
          _ = Kc * (1 + |t|) ^ θ * (1 + |y|) ^ θ := by
              rw [Real.mul_rpow ht1.le (by positivity)]; ring
      have hy1 : (0 : ℝ) < 1 + |y| := by positivity
      have hyθ : (1 + |y|) ^ θ ≤ (1 + |y|) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y]) hθ
      rw [Real.rpow_two] at hyθ
      calc ‖(X : ℂ) ^ ln (-δ) y * Pk 3 (ln (-δ) y)‖ * ‖F (ln (-δ) y)‖
          ≤ (X ^ (-δ) * A / (1 + |y|) ^ 4) * (Kc * (1 + |t|) ^ θ * (1 + |y|) ^ θ) :=
            mul_le_mul (hlineP y) hFy (norm_nonneg _) (by positivity)
        _ ≤ (X ^ (-δ) * A / (1 + |y|) ^ 4) * (Kc * (1 + |t|) ^ θ * (1 + |y|) ^ 2) := by
            gcongr
        _ = X ^ (-δ) * A * Kc * (1 + |t|) ^ θ / (1 + |y|) ^ 2 := by
            field_simp
    refine (norm_integral_le_of_norm_le (integrable_div_sq _) (ae_of_all _ hb)).trans
      (le_of_eq ?_)
    rw [hJ, ← integral_const_mul]
    congr 1; funext y; ring
  -- combine
  rw [hkey]
  have hnorm2π : ‖(2 * π : ℂ)‖ = 2 * π := by
    rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hπ : 0 < π := Real.pi_pos
  calc ‖-(F 0 * ((phi 3 (1 / X) : ℂ) - 1)) - (Ig - F 0 * IX) / (2 * π)‖
      ≤ ‖F 0‖ * ‖((phi 3 (1 / X) : ℂ) - 1)‖ + (‖Ig‖ + ‖F 0‖ * ‖IX‖) / (2 * π) := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg, norm_mul, norm_div, hnorm2π]
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ (Kc * (1 + |t|) ^ θ) * (3 * X ^ (-δ)) +
          (X ^ (-δ) * A * Kc * (1 + |t|) ^ θ * J + (Kc * (1 + |t|) ^ θ) * (X ^ (-δ) * A * J)) /
            (2 * π) := by
        gcongr
    _ = Kc * (3 + A * J / π) * X ^ (-δ) * (1 + |t|) ^ θ := by
        field_simp; ring

end RamanujanTau.CramerMeanSquare
