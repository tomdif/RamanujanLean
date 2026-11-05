/-
# The real edge point, and the case `f = Δ`

The positivity argument of `EdgeNonvanishing` does not reach `s = (k+1)/2` itself (for `t = 0`
the auxiliary product has a pole of order 5 against a zero of order 4).  For `Δ` the real point
was handled by `Δ(iy) > 0`.  Here:

* `fL_real_ne_zero_of_imagAxis_nonneg`: if `f(iy) ≥ 0` for all `y > 0` (and `a_f(1) = 1`),
  then `L(f,σ) ≠ 0` for every real `σ > 0` — the Mellin transform of a nonnegative function
  that is not a.e. zero (else every `a_f(n)` would vanish);
* `isNormalizedEigenform_discriminant`: `Δ` is a normalized eigenform;
* `discriminant_imagAxis_nonneg`: `Δ(iy) ≥ 0` (`HeckeL.heckeU_pos`);
* `fL_discriminant_ne_zero_edge`: the Δ edge theorem recovered from the general one.
-/
import RamanujanTau.EigenformEdge.Eigenform
import RamanujanTau.HeckeL.Positivity

set_option autoImplicit false

namespace RamanujanTau.EigenformEdge

open Complex Filter LSeries ModularForm MeasureTheory Set
open RamanujanTau.HeckeConvexGeneral
open scoped MatrixGroups ComplexConjugate Real

variable {k : ℕ}

/-- **Real-point non-vanishing from positivity on the imaginary axis.** -/
theorem fL_real_ne_zero_of_imagAxis_nonneg {f : CuspForm 𝒮ℒ (k : ℤ)} (hf : IsNormalizedEigenform f)
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ (heckeF f t).re) {σ : ℝ} (hσ : 0 < σ) : fL f σ ≠ 0 := by
  have hk := hf.one_le
  set u : ℝ → ℝ := fun t => (heckeF f t).re
  have hR : ∀ t : ℝ, 0 < t → heckeF f t = (u t : ℂ) := fun t ht =>
    HardyZerosGeneral.heckeF_real f hf.real ht
  have hval : heckeLambda f σ = ((∫ t in Ioi (0:ℝ), t ^ (σ - 1) * u t : ℝ) : ℂ) := by
    have hI := integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Ioi (0:ℝ)))
      (f := fun t => t ^ (σ - 1) * u t)
    rw [heckeLambda, mellin]
    refine Eq.trans ?_ hI
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    simp only [smul_eq_mul]
    rw [hR t ht, show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow ht.le, ← Complex.ofReal_mul]
    rfl
  have hconv : MellinConvergent (heckeF f) (σ : ℂ) := ((heckePair f hk).hasMellin σ).1
  have hint : IntegrableOn (fun t : ℝ => t ^ (σ - 1) * u t) (Ioi 0) := by
    refine hconv.re.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    show Complex.re _ = _
    rw [smul_eq_mul, hR t ht, show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow ht.le, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] fun t => t ^ (σ - 1) * u t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    exact mul_nonneg (Real.rpow_pos_of_pos ht _).le (hpos t ht)
  have hΛ : heckeLambda f σ ≠ 0 := by
    intro h0
    rw [hval, Complex.ofReal_eq_zero] at h0
    have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp h0
    -- `f(it) = 0` for a.e. `t > 0`, so `Λ ≡ 0`, so `L(f,·) ≡ 0`, so `a_f(1) = 0`
    have hF : ∀ᵐ t ∂(volume.restrict (Ioi (0:ℝ))), heckeF f t = 0 := by
      filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with t h (ht : 0 < t)
      have h' : t ^ (σ - 1) * u t = 0 := h
      have hu : u t = 0 :=
        (mul_eq_zero.mp h').resolve_left (Real.rpow_pos_of_pos ht _).ne'
      rw [hR t ht, hu, Complex.ofReal_zero]
    have hall : ∀ s : ℂ, fL f s = 0 := by
      intro s
      have : heckeLambda f s = 0 := by
        rw [heckeLambda, mellin]
        rw [setIntegral_congr_ae measurableSet_Ioi (g := fun _ => (0 : ℂ)) ?_]
        · simp
        · rw [← ae_restrict_iff' measurableSet_Ioi]
          filter_upwards [hF] with t ht
          rw [ht, smul_zero]
      rw [fL, this, mul_zero]
    have hev : (fun x : ℝ => LSeries (coef f) x) =ᶠ[atTop] 0 := by
      filter_upwards [eventually_gt_atTop (((k : ℝ) + 1) / 2)] with x hx
      rw [← fL_eq_LSeries f hk (by simpa using hx), hall]
      rfl
    have hsum : LSeriesSummable (coef f) ((k : ℂ) + 1) :=
      LSeriesSummable_coef f hk (by simp; linarith)
    have hab : abscissaOfAbsConv (coef f) ≠ ⊤ :=
      ne_top_of_le_ne_top (EReal.coe_ne_top _) hsum.abscissaOfAbsConv_le
    have := (LSeries_eventually_eq_zero_iff'.mp hev).resolve_right hab 1 one_ne_zero
    rw [hf.one] at this
    exact one_ne_zero this
  rw [fL]
  have hG : Gamma (σ : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hσ)
  exact mul_ne_zero (mul_ne_zero (two_pi_cpow_ne_zero _) (inv_ne_zero hG)) hΛ

/-- The real edge value under imaginary-axis positivity. -/
theorem fL_edge_real_ne_zero_of_imagAxis_nonneg {f : CuspForm 𝒮ℒ (k : ℤ)}
    (hf : IsNormalizedEigenform f) (hpos : ∀ t : ℝ, 0 < t → 0 ≤ (heckeF f t).re) :
    fL f (((k : ℂ) + 1) / 2) ≠ 0 := by
  have := fL_real_ne_zero_of_imagAxis_nonneg hf hpos (σ := ((k : ℝ) + 1) / 2) (by positivity)
  simpa using this

/-! ## `Δ` -/

/-- `Δ` as a weight-`(12 : ℕ)` cusp form. -/
noncomputable abbrev DeltaF : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ) := CuspForm.discriminant

/-- **`Δ` is a normalized Hecke eigenform** (Mordell). -/
theorem isNormalizedEigenform_discriminant : IsNormalizedEigenform (k := 12) DeltaF where
  real n := by rw [coef_discriminant]; simp [tauC]
  one := by rw [coef_discriminant]; simp [tauC, tau_one]
  mul h := by
    simp only [coef_discriminant, tauC]
    rw [tau_mul_coprime h]; push_cast; ring
  hecke hp e := by
    simp only [coef_discriminant, tauC]
    rw [show e + 2 = (e + 1) + 1 by ring, tau_hecke_recurrence hp (r := e + 1) (by omega),
      show e + 1 - 1 = e by omega]
    push_cast
    norm_num

/-- `Δ(it) ≥ 0`. -/
theorem discriminant_imagAxis_nonneg : ∀ t : ℝ, 0 < t → 0 ≤ (heckeF (k := 12) DeltaF t).re :=
  fun _ ht => (HeckeL.heckeU_pos ht).le

/-- **The Δ edge theorem, recovered from the general one.** -/
theorem fL_discriminant_ne_zero_edge (t : ℝ) : fL (k := 12) DeltaF (13 / 2 + t * I) ≠ 0 := by
  have h := fL_ne_zero_edge isNormalizedEigenform_discriminant
    (fL_edge_real_ne_zero_of_imagAxis_nonneg isNormalizedEigenform_discriminant
      discriminant_imagAxis_nonneg) t
  have e : (((12 : ℕ) : ℂ) + 1) / 2 = 13 / 2 := by norm_num
  rwa [e] at h

end RamanujanTau.EigenformEdge
