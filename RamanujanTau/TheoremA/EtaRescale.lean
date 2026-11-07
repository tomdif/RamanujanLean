import RamanujanTau.TheoremA.EtaSquared

/-!
# Scaling eta transformations

For d dividing the lower-left entry of γ, conjugating γ by diag(d,1)
is integral. Its eta-squared multiplier gives the weight-one transformation
of eta(dz)^2. This is the bridge from finite word certificates to eta quotients.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.EtaSquared
open Matrix ModularForm
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm

noncomputable def scale (d : ℕ) (hd : 0 < d) (z : ℍ) : ℍ :=
  ⟨(d : ℂ) * z, by simpa using mul_pos (by exact_mod_cast hd : (0 : ℝ) < d) z.im_pos⟩

def rescale (d : ℕ) (γ : SL(2, ℤ)) (h : (d : ℤ) ∣ γ 1 0) : SL(2, ℤ) :=
  ⟨!![γ 0 0, (d : ℤ) * γ 0 1; γ 1 0 / (d : ℤ), γ 1 1], by
    have he := Int.ediv_mul_cancel h
    have hg := γ.property
    rw [det_fin_two] at hg ⊢
    change γ 0 0 * γ 1 1 - ((d : ℤ) * γ 0 1) * (γ 1 0 / (d : ℤ)) = 1
    linear_combination hg - γ 0 1 * he⟩

lemma rescale_denom (d : ℕ) (hd : 0 < d) (γ : SL(2, ℤ))
    (h : (d : ℤ) ∣ γ 1 0) (z : ℍ) :
    denom (rescale d γ h) (scale d hd z) = denom γ z := by
  have he : ((γ 1 0 / (d : ℤ) : ℤ) : ℂ) * (d : ℂ) = (γ 1 0 : ℂ) := by
    exact_mod_cast Int.ediv_mul_cancel h
  change ((γ 1 0 / (d : ℤ) : ℤ) : ℂ) * ((d : ℂ) * z) + γ 1 1 = _
  rw [← mul_assoc, he]
  rfl

lemma scale_smul (d : ℕ) (hd : 0 < d) (γ : SL(2, ℤ))
    (h : (d : ℤ) ∣ γ 1 0) (z : ℍ) :
    scale d hd (γ • z) = rescale d γ h • scale d hd z := by
  apply UpperHalfPlane.ext
  change (d : ℂ) * (↑(γ • z) : ℂ) = ↑(rescale d γ h • scale d hd z)
  rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply]
  have he : ((γ 1 0 / (d : ℤ) : ℤ) : ℂ) * (d : ℂ) = (γ 1 0 : ℂ) := by
    exact_mod_cast Int.ediv_mul_cancel h
  simp only [rescale, scale, algebraMap_int_eq, Int.coe_castRingHom,
    Complex.ofReal_intCast, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  push_cast
  change (d : ℂ) * (((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)) =
    ((γ 0 0 : ℂ) * ((d : ℂ) * z) + (d : ℂ) * γ 0 1) /
      (((γ 1 0 / (d : ℤ) : ℤ) : ℂ) * ((d : ℂ) * z) + γ 1 1)
  simp only [← mul_assoc, he]
  ring

noncomputable def scaledEta (d : ℕ) (hd : 0 < d) (z : ℍ) : ℂ :=
  etaSquared (scale d hd z)

theorem scaled_slash_of_rescale (d : ℕ) (hd : 0 < d) (γ : SL(2, ℤ))
    (h : (d : ℤ) ∣ γ 1 0) (α : ℂ)
    (hα : etaSquared ∣[(1 : ℤ)] rescale d γ h = α • etaSquared) :
    scaledEta d hd ∣[(1 : ℤ)] γ = α • scaledEta d hd := by
  ext z
  have he := congrFun hα (scale d hd z)
  rw [SL_slash_apply] at he ⊢
  change etaSquared (scale d hd (γ • z)) * denom γ z ^ (-1 : ℤ) =
    α * etaSquared (scale d hd z)
  rw [scale_smul d hd γ h z]
  simpa only [rescale_denom, Pi.smul_apply, smul_eq_mul] using he

end RamanujanTau.TheoremA.EtaSquared
