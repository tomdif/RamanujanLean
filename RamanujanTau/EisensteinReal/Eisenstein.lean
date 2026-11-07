/-
# The real-analytic Eisenstein series for `SL₂(ℤ)` (milestone E1, real `s > 1`)

    E(z,s) = ½ ∑_{gcd(c,d)=1} y^s / |cz+d|^{2s}  =  ∑_{γ ∈ Γ∞\Γ} (Im γz)^s.

* `summable_eSummand`: absolute convergence for `s > 1` (Mathlib's
  `EisensteinSeries.summand_bound` and `summable_one_div_norm_rpow`, with `k = 2s > 2`);
* `E_smul`: `E(γz, s) = E(z, s)` for `γ ∈ SL₂(ℤ)` (reindexing by `v ↦ vγ`, using
  `Im γz = Im z/|j(γ,z)|²` and `(v₀γz + v₁) = ((vγ)₀z + (vγ)₁)/j(γ,z)`);
* `E_ge`: `E(z,s) ≥ y^s` (the two terms `(0, ±1)`), and `E_pos`.
-/
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs

set_option autoImplicit false

namespace RamanujanTau.EisensteinReal

open UpperHalfPlane EisensteinSeries Matrix
open scoped MatrixGroups

/-- The summand `y^s |cz+d|^{-2s}`. -/
noncomputable def eSummand (s : ℝ) (z : ℍ) (v : Fin 2 → ℤ) : ℝ :=
  z.im ^ s * ‖(v 0 : ℂ) * (z : ℂ) + v 1‖ ^ (-(2 * s))

lemma eSummand_nonneg (s : ℝ) (z : ℍ) (v : Fin 2 → ℤ) : 0 ≤ eSummand s z v := by
  unfold eSummand
  exact mul_nonneg (Real.rpow_nonneg z.im_pos.le _) (Real.rpow_nonneg (norm_nonneg _) _)

/-- Absolute convergence over all of `ℤ²` for `s > 1`. -/
theorem summable_eSummand {s : ℝ} (hs : 1 < s) (z : ℍ) :
    Summable (eSummand s z) := by
  have hk : (0 : ℝ) ≤ 2 * s := by linarith
  refine Summable.of_nonneg_of_le (eSummand_nonneg s z) (fun v => ?_)
    (((summable_one_div_norm_rpow (k := 2 * s) (by linarith)).mul_left
      (r z ^ (-(2 * s)))).mul_left (z.im ^ s))
  unfold eSummand
  rw [← mul_assoc (z.im ^ s)]
  have := summand_bound z hk v
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left this (Real.rpow_nonneg z.im_pos.le _)

/-- **The real-analytic Eisenstein series** `E(z,s) = ½ ∑_{(c,d)=1} y^s |cz+d|^{-2s}`. -/
noncomputable def E (z : ℍ) (s : ℝ) : ℝ :=
  (1 / 2) * ∑' v : gammaSet 1 1 0, eSummand s z v

lemma summable_E {s : ℝ} (hs : 1 < s) (z : ℍ) :
    Summable (fun v : gammaSet 1 1 0 => eSummand s z v) :=
  (summable_eSummand hs z).subtype _

/-- The summand transforms by `v ↦ vγ`. -/
lemma eSummand_smul (s : ℝ) (γ : SL(2, ℤ)) (z : ℍ) (v : Fin 2 → ℤ) :
    eSummand s (γ • z) v = eSummand s z (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
  have h := eisSummand_SL2_apply 1 v γ z
  simp only [eisSummand, zpow_neg, zpow_one] at h
  have hj : denom γ z ≠ 0 := denom_ne_zero γ z
  have hjn : 0 < ‖denom γ z‖ := norm_pos_iff.2 hj
  have hn : ‖(v 0 : ℂ) * ((γ • z : ℍ) : ℂ) + v 1‖⁻¹ =
      ‖denom γ z‖ * ‖((v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) 0 : ℂ) * (z : ℂ) +
        (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) 1‖⁻¹ := by
    rw [← norm_inv, h, norm_mul, norm_inv]
  have him : (γ • z).im = z.im / ‖denom γ z‖ ^ 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
  unfold eSummand
  rw [Real.rpow_neg (norm_nonneg _), Real.rpow_neg (norm_nonneg _), ← Real.inv_rpow (norm_nonneg _),
    ← Real.inv_rpow (norm_nonneg _), hn, him,
    Real.mul_rpow hjn.le (inv_nonneg.2 (norm_nonneg _)),
    Real.div_rpow z.im_pos.le (by positivity)]
  have e2 : (‖denom γ z‖ ^ 2) ^ s = ‖denom γ z‖ ^ (2 * s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hjn.le]; norm_num
  rw [e2]
  have : 0 < ‖denom γ z‖ ^ (2 * s) := Real.rpow_pos_of_pos hjn _
  field_simp

/-- **`Γ`-invariance**: `E(γz, s) = E(z, s)`. -/
theorem E_smul (s : ℝ) (γ : SL(2, ℤ)) (z : ℍ) : E (γ • z) s = E z s := by
  unfold E
  congr 1
  simp_rw [eSummand_smul]
  exact ((gammaSetEquiv 0 γ).trans (gammaSet_one_equiv 1 _ 0)).tsum_eq
    (fun v : gammaSet 1 1 0 => eSummand s z v)

lemma mem_gammaSet_pm (b : ℤ) (hb : b = 1 ∨ b = -1) : ![0, b] ∈ gammaSet 1 1 0 := by
  rw [mem_gammaSet_one]
  rcases hb with rfl | rfl
  · simpa using isCoprime_zero_left.2 isUnit_one
  · simpa using isCoprime_zero_left.2 isUnit_one.neg

/-- `E(z,s) ≥ y^s`: the terms `(c,d) = (0, ±1)`. -/
theorem E_ge {s : ℝ} (hs : 1 < s) (z : ℍ) : z.im ^ s ≤ E z s := by
  unfold E
  let v₁ : gammaSet 1 1 0 := ⟨![0, 1], mem_gammaSet_pm 1 (Or.inl rfl)⟩
  let v₂ : gammaSet 1 1 0 := ⟨![0, -1], mem_gammaSet_pm (-1) (Or.inr rfl)⟩
  have hne : v₁ ≠ v₂ := by
    intro h
    have := congrArg (fun w : gammaSet 1 1 0 => (w : Fin 2 → ℤ) 1) h
    simp [v₁, v₂] at this
  have hval : ∀ w : gammaSet 1 1 0, w = v₁ ∨ w = v₂ → eSummand s z w = z.im ^ s := by
    rintro w (rfl | rfl) <;> simp [eSummand, v₁, v₂]
  have hsum := Summable.sum_le_tsum ({v₁, v₂} : Finset (gammaSet 1 1 0))
    (fun w _ => eSummand_nonneg s z w) (summable_E hs z)
  rw [Finset.sum_pair hne, hval v₁ (Or.inl rfl), hval v₂ (Or.inr rfl)] at hsum
  linarith

theorem E_pos {s : ℝ} (hs : 1 < s) (z : ℍ) : 0 < E z s :=
  (Real.rpow_pos_of_pos z.im_pos s).trans_le (E_ge hs z)

end RamanujanTau.EisensteinReal

#print axioms RamanujanTau.EisensteinReal.summable_eSummand
#print axioms RamanujanTau.EisensteinReal.E_smul
#print axioms RamanujanTau.EisensteinReal.E_ge
