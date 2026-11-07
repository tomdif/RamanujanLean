import RamanujanTau.BLBound.Filtration

/-!
# Integral forms reduce to polynomials in `E₄, E₆`

The reduction of an integral level-one form of weight `k` is an isobaric polynomial of weight `k` in
`E₄, E₆`. This is the converse of `BoylanWebb.lift_iso`.
-/

set_option autoImplicit false

namespace RamanujanTau.BLBound
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane ModP BoylanWebb
open scoped MatrixGroups
open RamanujanTau.DiscriminantBridge (Δmod)
open RamanujanTau.Mod691 (p4 p6)

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- **The reduction of an integral form is isobaric.** -/
theorem formBar_of_intForm (h5 : 5 ≤ ℓ) : ∀ (N k : ℕ), k < 12 * N → ∀ a : PowerSeries ℤ,
    IntForm (k : ℤ) a → FormBar ℓ k (Ψ ℓ a) := by
  intro N
  induction N with
  | zero => intro k hk; omega
  | succ N ih =>
    intro k hk a ⟨F, hF⟩
    have hzero : (F : ℍ → ℂ) = 0 → FormBar ℓ k (Ψ ℓ a) := by
      intro h0
      have h1 := Ψ_eq_zero_of_form_zero ℓ F hF h0
      rw [h1]
      exact ⟨0, MvPolynomial.isWeightedHomogeneous_zero _ _ _, map_zero _⟩
    rcases Nat.even_or_odd k with hev | hodd
    swap
    · refine hzero (by
        rw [levelOne_odd_weight_eq_zero (by exact_mod_cast hodd) F, ModularForm.coe_zero])
    by_cases h2 : k = 2
    · subst h2
      have := levelOne_weight_two_rank_zero
      rw [rank_zero_iff_forall_zero] at this
      exact hzero (by rw [this F, ModularForm.coe_zero])
    have hn' : 4 * bexp0 k + 6 * bexp1 k = k := by
      obtain ⟨m, hm⟩ := hev
      unfold bexp0 bexp1
      omega
    set m := p4 ^ bexp0 k * p6 ^ bexp1 k with hm
    have hmF : IntForm (k : ℤ) m := (IntForm.mono _ _).cast (by rw [hn'])
    have hm0 : PowerSeries.constantCoeff m = 1 := by
      rw [hm, map_mul, map_pow, map_pow]
      have h4 : PowerSeries.constantCoeff p4 = 1 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, RamanujanTau.Mod691.coeff_p4]; simp
      have h6 : PowerSeries.constantCoeff p6 = 1 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, RamanujanTau.Mod691.coeff_p6]; simp
      rw [h4, h6, one_pow, one_pow, one_mul]
    set c := PowerSeries.coeff 0 a with hc
    set r := a - PowerSeries.C c * m with hr
    have hrF : IntForm (k : ℤ) r := (IntForm.sub ⟨F, hF⟩ (hmF.C_mul c))
    have hr0 : PowerSeries.constantCoeff r = 0 := by
      rw [hr, map_sub, map_mul, PowerSeries.constantCoeff_C, hm0, mul_one,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, sub_self]
    obtain ⟨r', hr'⟩ := PowerSeries.X_dvd_iff.mpr hr0
    obtain ⟨Fr, hFr⟩ := hrF
    have hFr0 : (qExpansion 1 Fr).coeff 0 = 0 := by
      rw [hFr, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hr0, map_zero]
    set gc := ModularForm.toCuspForm Fr hFr0 with hgc
    set h := CuspForm.divDiscriminant gc with hh
    have hfun : (Fr : ℍ → ℂ) = (Δmod : ℍ → ℂ) * (h : ℍ → ℂ) := by
      ext z
      have := congrArg (fun F : CuspForm 𝒮ℒ (k : ℤ) => F z) (CuspForm.discriminantEquiv.left_inv gc)
      simp only at this
      change _ = Δmod z * h z
      rw [← ModularForm.toCuspForm_apply Fr hFr0 z, ← hgc]
      exact this.symm
    have hqgh : qExpansion 1 Fr = PowerSeries.map (Int.castRingHom ℂ)
        (PowerSeries.X * MockTheta5.JTP.qfacInf ^ 24) * qExpansion 1 h := by
      rw [hfun, UpperHalfPlane.qExpansion_mul (analytic _ Δmod) (analytic _ h),
        RamanujanTau.TauModular.qExpansion_discriminant_eq]
    obtain ⟨W, hW⟩ := exists_inv_U
    set b := W * r' with hb
    have hbq : qExpansion 1 h = PowerSeries.map (Int.castRingHom ℂ) b := by
      have e1 : PowerSeries.map (Int.castRingHom ℂ) r =
          PowerSeries.X * (PowerSeries.map (Int.castRingHom ℂ) (MockTheta5.JTP.qfacInf ^ 24) *
            qExpansion 1 h) := by
        rw [← hFr, hqgh, map_mul, PowerSeries.map_X, mul_assoc]
      rw [hr', map_mul, PowerSeries.map_X] at e1
      have e2 := PowerSeries.X_mul_cancel e1
      have hW' : PowerSeries.map (Int.castRingHom ℂ) W *
          PowerSeries.map (Int.castRingHom ℂ) (MockTheta5.JTP.qfacInf ^ 24) = 1 := by
        rw [← map_mul, mul_comm, hW, map_one]
      rw [hb, map_mul, e2, ← mul_assoc, hW', one_mul]
    have hr'b : r' = MockTheta5.JTP.qfacInf ^ 24 * b := by
      rw [hb, ← mul_assoc, hW, one_mul]
    have hae : a = PowerSeries.C c * m + PowerSeries.X * (MockTheta5.JTP.qfacInf ^ 24 * b) := by
      rw [← hr'b, ← hr', hr]
      ring
    have hmbar : FormBar ℓ k (Ψ ℓ (PowerSeries.C c * m)) := by
      refine ⟨MvPolynomial.C (c : ZMod ℓ) * (MvPolynomial.X 0 ^ bexp0 k * MvPolynomial.X 1 ^ bexp1 k), ?_, ?_⟩
      · exact (iso_of_eq (iso_mono (bexp0 k) (bexp1 k)) hn').C_mul _
      · rw [map_mul, ev_C, map_mul, map_pow, map_pow, ev_X0, ev_X1, map_mul, PowerSeries.map_C, hm,
          map_mul, map_pow, map_pow]
        simp [E4, E6]
    by_cases hk12 : k < 12
    · have hh0 : (h : ℍ → ℂ) = 0 := levelOne_neg_weight_eq_zero (by push_cast; omega) h
      have hb0 : b = 0 := map_injC (by rw [← hbq, hh0, qExpansion_zero, map_zero])
      rw [hae, hb0, mul_zero, mul_zero, add_zero]
      exact hmbar
    · have hk' : ((k - 12 : ℕ) : ℤ) = (k : ℤ) - 12 := by omega
      have hbF : IntForm ((k - 12 : ℕ) : ℤ) b := IntForm.cast hk'.symm ⟨h, hbq⟩
      obtain ⟨Q, hQ, hQe⟩ := ih (k - 12) (by omega) b hbF
      obtain ⟨P₁, hP₁, hP₁e⟩ := hmbar
      have h1728 : (1728 : ZMod ℓ) ≠ 0 := ne_zero_1728 h5
      have hdisc : Iso (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) (ZMod ℓ)) 12 := by
        have h3 := iso_mono (R := ZMod ℓ) 3 0
        have h4 := iso_mono (R := ZMod ℓ) 0 2
        simp only [pow_zero, mul_one, one_mul] at h3 h4
        exact iso_sub h3 h4
      refine ⟨P₁ + MvPolynomial.C (1728 : ZMod ℓ)⁻¹ * ((MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2) * Q), ?_, ?_⟩
      · refine hP₁.add (MvPolynomial.IsWeightedHomogeneous.C_mul ?_ _)
        exact iso_of_eq (hdisc.mul hQ) (by omega)
      · have hd := ev_disc (R := ZMod ℓ)
        have hu : PowerSeries.C (1728 : ZMod ℓ)⁻¹ * (1728 : PowerSeries (ZMod ℓ)) = 1 := by
          have : (1728 : PowerSeries (ZMod ℓ)) = PowerSeries.C (1728 : ZMod ℓ) :=
            (map_ofNat (PowerSeries.C (R := ZMod ℓ)) 1728).symm
          rw [this, ← map_mul, inv_mul_cancel₀ h1728, map_one]
        have hE : ev (ZMod ℓ) (MvPolynomial.C (1728 : ZMod ℓ)⁻¹ *
            ((MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2) * Q)) =
            Ψ ℓ (PowerSeries.X * (MockTheta5.JTP.qfacInf ^ 24 * b)) := by
          rw [map_mul, ev_C, map_mul, hd, hQe, ← mul_assoc, ← mul_assoc, hu, one_mul]
          simp only [Dq, map_mul, map_pow, PowerSeries.map_X]
          ring
        calc _ = Ψ ℓ (PowerSeries.C c * m) + Ψ ℓ (PowerSeries.X * (MockTheta5.JTP.qfacInf ^ 24 * b)) := by
              rw [map_add, hP₁e, hE]
          _ = Ψ ℓ a := by rw [← map_add, ← hae]

end RamanujanTau.BLBound
