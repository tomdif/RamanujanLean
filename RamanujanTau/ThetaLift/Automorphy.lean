import RamanujanTau.ThetaLift.StripClosed
import RamanujanTau.ThetaLift.EtaProduct

/-!
# The automorphy of the integrand

For `γ` with `N ∣ c`, the function `v^(λ+1/2) conj 𝔽` transforms with the factor `(η(z)/η(γz)) j^(-λ) (d/N)`.
This is where the character of the kernel cancels.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex
open UpperHalfPlane hiding I
open scoped Real ComplexConjugate MatrixGroups ModularForm
open Rademacher ModularForm

noncomputable section

variable {k' : ℤ} (G : CuspForm 𝒮ℒ k') (j : ℕ) {N : ℕ} (hN : 0 < N)

/-- The action on `Nz` by the conjugate matrix. -/
lemma nP_smul (γ : SL(2, ℤ)) (h : (N : ℤ) ∣ γ 1 0) (z : ℍ) :
    nP hN (γ • z) = conjT N γ h • nP hN z := by
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNZ : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  apply UpperHalfPlane.ext
  have h1 : ((nP hN (γ • z) : ℍ) : ℂ) = (N : ℂ) * mob γ z := by
    change (N : ℂ) * ((γ • z : ℍ) : ℂ) = _
    rw [mob_eq]
  rw [h1, ← mob_eq]
  have hz : ((nP hN z : ℍ) : ℂ) = (N : ℂ) * z := rfl
  obtain ⟨c, hc⟩ := h
  have hd : (γ 1 0) / (N : ℤ) = c := by rw [hc, Int.mul_ediv_cancel_left _ hNZ]
  have hcC : ((γ 1 0 : ℤ) : ℂ) = (N : ℂ) * c := by rw [hc]; push_cast; rfl
  unfold mob
  rw [hz, coe_conj_00, coe_conj_01, coe_conj_10, coe_conj_11, hd, hcC]
  push_cast
  have hne : (N : ℂ) * c * z + γ 1 1 ≠ 0 := by
    have := denom_ne_zero' γ z.2
    rwa [hcC] at this
  have hne2 : (c : ℂ) * ((N : ℂ) * z) + γ 1 1 ≠ 0 := by
    rw [show (c : ℂ) * ((N : ℂ) * z) = (N : ℂ) * c * z by ring]
    exact hne
  field_simp

/-- The transformation of `G` under `Nz`. -/
lemma G_nP (γ : SL(2, ℤ)) (h : (N : ℤ) ∣ γ 1 0) (z : ℍ) :
    G (nP hN (γ • z)) = lin γ z ^ k' * G (nP hN z) := by
  have hNZ : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [nP_smul hN γ h z]
  have hmem : ((conjT N γ h : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨conjT N γ h, rfl⟩
  have hG := SlashInvariantForm.slash_action_eqn'' G hmem (nP hN z)
  have hden : denom ((conjT N γ h : SL(2, ℤ)) : GL (Fin 2) ℝ) (nP hN z) = lin γ z := by
    obtain ⟨c, hc⟩ := h
    have hd : (γ 1 0) / (N : ℤ) = c := by rw [hc, Int.mul_ediv_cancel_left _ hNZ]
    have hcC : ((γ 1 0 : ℤ) : ℂ) = (N : ℂ) * c := by rw [hc]; push_cast; rfl
    change ((conjT N γ ⟨c, hc⟩ 1 0 : ℤ) : ℂ) * ((N : ℂ) * z) + (conjT N γ ⟨c, hc⟩ 1 1 : ℤ) = _
    rw [coe_conj_10, coe_conj_11, hd]
    unfold lin
    rw [hcC]
    ring
  rw [hden] at hG
  exact hG

/-- The transformation of `|η|`. -/
lemma eta_norm_sq (γ : SL(2, ℤ)) (z : ℍ) :
    ‖η (mob γ z)‖ ^ 2 = ‖lin γ z‖ * ‖η (z : ℂ)‖ ^ 2 := by
  have hmem : ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hD := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hmem z
  have hD' : discriminant (γ • z) = lin γ z ^ (12 : ℤ) * discriminant z := hD
  have h1 : η (mob γ z) ^ 24 = lin γ z ^ 12 * η (z : ℂ) ^ 24 := by
    have := hD'
    unfold discriminant at this
    rw [← mob_eq] at this
    exact_mod_cast this
  have h2 := congrArg norm h1
  simp only [norm_pow, norm_mul] at h2
  have h3 : (‖η (mob γ z)‖ ^ 2) ^ 12 = (‖lin γ z‖ * ‖η (z : ℂ)‖ ^ 2) ^ 12 := by
    rw [← pow_mul, mul_pow, ← pow_mul]
    exact h2
  exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num)).mp h3

variable {w lam : ℕ}

/-- The transformation of `𝔽`. -/
lemma fF_smul (ht2 : ¬ 2 ∣ N) (ht3 : ¬ 3 ∣ N) (htj : 24 ∣ N + j) (hjw : j + 1 = 2 * w)
    (hk : k' = ((lam + w : ℕ) : ℤ)) (γ : SL(2, ℤ)) (h : (N : ℤ) ∣ γ 1 0) (z : ℍ) :
    ((jacobiSym (γ 1 1) N : ℤ) : ℂ) * fF G j hN (γ • z) =
      lin γ z ^ lam * fF G j hN z * (η (mob γ z) / η (z : ℂ)) := by
  have hL := zLaw (t := N) (j := j) (w := w) ht2 ht3 htj hjw γ h z z.2
  have hη1 : η (z : ℂ) ≠ 0 := eta_ne_zero z.2
  have hη2 : η (mob γ z) ≠ 0 := eta_ne_zero (mob_im_pos γ z.2)
  have hη3 : η ((nP hN z : ℍ) : ℂ) ≠ 0 := eta_ne_zero (nP hN z).2
  have hη4 : η ((nP hN (γ • z) : ℍ) : ℂ) ≠ 0 := eta_ne_zero (nP hN (γ • z)).2
  have hj : lin γ z ≠ 0 := denom_ne_zero' γ z.2
  have hN1 : ((nP hN z : ℍ) : ℂ) = (N : ℂ) * z := rfl
  have hN2 : ((nP hN (γ • z) : ℍ) : ℂ) = (N : ℂ) * mob γ z := by
    change (N : ℂ) * ((γ • z : ℍ) : ℂ) = _
    rw [mob_eq]
  unfold Zprod at hL
  rw [← hN1, ← hN2] at hL
  unfold fF
  have hz : lin γ z ^ k' = lin γ z ^ lam * lin γ z ^ w := by
    rw [hk, zpow_natCast, pow_add]
  rw [G_nP G hN γ h z, hz]
  have hp3 := pow_ne_zero j hη3
  have hp4 := pow_ne_zero j hη4
  field_simp
  linear_combination (-(G (nP hN z))) * hL

/-- The character value squares to one. -/
lemma jacobi_sq (γ : SL(2, ℤ)) (h : (N : ℤ) ∣ γ 1 0) :
    ((jacobiSym (γ 1 1) N : ℤ) : ℂ) * ((jacobiSym (γ 1 1) N : ℤ) : ℂ) = 1 := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.property
    rwa [Matrix.det_fin_two] at h
  obtain ⟨c, hc⟩ := h
  have hcop : IsCoprime (γ 1 1) (N : ℤ) := ⟨γ 0 0, -(γ 0 1 * c), by rw [hc] at hdet; linear_combination hdet⟩
  have h1 := jacobiSym.sq_one (a := γ 1 1) (b := N) (Int.isCoprime_iff_gcd_eq_one.mp hcop)
  have h2 : ((jacobiSym (γ 1 1) N ^ 2 : ℤ) : ℂ) = 1 := by rw [h1]; simp
  push_cast at h2
  rw [← pow_two]
  exact h2

/-- **The automorphy of the integrand.** -/
theorem autom (ht2 : ¬ 2 ∣ N) (ht3 : ¬ 3 ∣ N) (htj : 24 ∣ N + j) (hjw : j + 1 = 2 * w)
    (hk : k' = ((lam + w : ℕ) : ℤ)) (γ : SL(2, ℤ)) (h : (N : ℤ) ∣ γ 1 0) (z : ℍ) :
    ((z.im ^ ((lam : ℝ) + 1 / 2) : ℝ) : ℂ) * conj (fF G j hN z) * (η (z : ℂ) / η (mob γ z)) *
        (lin γ z)⁻¹ ^ lam * ((jacobiSym (γ 1 1) N : ℤ) : ℂ) =
      (((γ • z : ℍ).im ^ ((lam : ℝ) + 1 / 2) : ℝ) : ℂ) * conj (fF G j hN (γ • z)) := by
  have hF := fF_smul G j hN ht2 ht3 htj hjw hk γ h z
  have hJ := jacobi_sq (N := N) γ h
  set J : ℂ := ((jacobiSym (γ 1 1) N : ℤ) : ℂ) with hJdef
  have hJc : conj J = J := by rw [hJdef]; simp
  have hF2 : fF G j hN (γ • z) = J * (lin γ z ^ lam * fF G j hN z * (η (mob γ z) / η (z : ℂ))) := by
    rw [← hF, ← mul_assoc, hJ, one_mul]
  have hη1 : η (z : ℂ) ≠ 0 := eta_ne_zero z.2
  have hη2 : η (mob γ z) ≠ 0 := eta_ne_zero (mob_im_pos γ z.2)
  have hj : lin γ z ≠ 0 := denom_ne_zero' γ z.2
  have hjb : conj (lin γ z) ≠ 0 := by simpa using hj
  set R : ℝ := ‖lin γ z‖ with hR
  have hRpos : 0 < R := norm_pos_iff.mpr hj
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
  have hRsq : ((R : ℂ)) ^ 2 = lin γ z * conj (lin γ z) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have hconj : conj (η (mob γ z) / η (z : ℂ)) = R * (η (z : ℂ) / η (mob γ z)) := by
    have h1 : conj (η (mob γ z)) = ((‖η (mob γ z)‖ ^ 2 : ℝ) : ℂ) / η (mob γ z) := by
      rw [eq_div_iff hη2, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h2 : conj (η (z : ℂ)) = ((‖η (z : ℂ)‖ ^ 2 : ℝ) : ℂ) / η (z : ℂ) := by
      rw [eq_div_iff hη1, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h3 : ((‖η (z : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have : ‖η (z : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hη1
      exact_mod_cast pow_ne_zero 2 this
    have h4 : ((‖η (z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by
      have : ‖η (z : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hη1
      exact_mod_cast this
    rw [map_div₀, h1, h2, eta_norm_sq, ← hR]
    push_cast
    field_simp
  have him : (γ • z : ℍ).im = z.im / R ^ 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
    have hd : UpperHalfPlane.denom γ z = lin γ z := by simp [UpperHalfPlane.denom, lin]
    rw [hd]
  have hv := z.im_pos
  have hpow : (((γ • z : ℍ).im ^ ((lam : ℝ) + 1 / 2) : ℝ) : ℂ) =
      ((z.im ^ ((lam : ℝ) + 1 / 2) : ℝ) : ℂ) * ((lin γ z)⁻¹ * (conj (lin γ z))⁻¹) ^ lam * (R : ℂ)⁻¹ := by
    have hr : (R ^ 2) ^ ((lam : ℝ) + 1 / 2) = (R ^ 2) ^ lam * R := by
      rw [Real.rpow_add (by positivity), Real.rpow_natCast, ← Real.sqrt_eq_rpow, Real.sqrt_sq hRpos.le]
    rw [him, Real.div_rpow hv.le (by positivity), hr]
    push_cast
    rw [hRsq, ← mul_inv, inv_pow, div_eq_mul_inv, mul_inv]
    ring
  rw [hpow, hF2, map_mul, map_mul, map_mul, hJc, hconj, map_pow]
  have hcancel : ((lin γ z)⁻¹ * (conj (lin γ z))⁻¹) ^ lam * conj (lin γ z) ^ lam = (lin γ z)⁻¹ ^ lam := by
    rw [← mul_pow]
    congr 1
    field_simp
  calc _ = ((z.im ^ ((lam : ℝ) + 1 / 2) : ℝ) : ℂ) * (((lin γ z)⁻¹ * (conj (lin γ z))⁻¹) ^ lam *
        conj (lin γ z) ^ lam) * J * conj (fF G j hN z) * (η (z : ℂ) / η (mob γ z)) := by
        rw [hcancel]
        ring
    _ = _ := by
      field_simp

end

end RamanujanTau.ThetaLift
