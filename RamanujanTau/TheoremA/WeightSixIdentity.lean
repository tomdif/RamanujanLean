import RamanujanTau.TheoremA.EtaQExpansion
import RamanujanTau.TheoremA.WeightSixCertificate

/-!
# The unconditional level-six, weight-six Hecke identity

The actual eta cusp forms supply the finite certificate. Thus
(U₃ + 9)(U₂² + 6U₂ + 32) vanishes on the entire classical cusp space.
The same identity descends to any coefficient reduction of this space.
This closes the classical small-weight obstruction in the proposed Theorem A;
the characteristic-prime geometric and Shimura comparison steps remain separate.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open UpperHalfPlane PowerSeries EtaSquared

noncomputable def weightSixH : ClassicalWeightSix :=
  basisCuspForm 0 + (10 : ℂ) • basisCuspForm 1 - (18 : ℂ) • basisCuspForm 2

noncomputable def weightSixForms (i : Fin 3) : ClassicalWeightSix :=
  match i.val with
  | 0 => basisCuspForm 0
  | 1 => basisCuspForm 1
  | _ => weightSixH

theorem weightSixForms_coefficients (i : Fin 3) (n : Fin 9) :
    (qExpansion 1 (weightSixForms i)).coeff (n.val + 1) = (weightSixCoefficients i n : ℂ) := by
  have hn : n.val + 1 < 10 := by omega
  fin_cases i
  · change (qExpansion 1 (basisCuspForm 0)).coeff (n.val + 1) = _
    rw [g_coeff hn]
    fin_cases n <;> norm_num [gCoefficients, coeffList, weightSixCoefficients]
  · change (qExpansion 1 (basisCuspForm 1)).coeff (n.val + 1) = _
    rw [v_coeff hn]
    fin_cases n <;> norm_num [vCoefficients, coeffList, weightSixCoefficients]
  · change (qExpansion 1 weightSixH).coeff (n.val + 1) = _
    have he : qExpansion 1 weightSixH = qExpansion 1 (basisCuspForm 0) +
        (10 : ℂ) • qExpansion 1 (basisCuspForm 1) - (18 : ℂ) • qExpansion 1 (basisCuspForm 2) := by
      change BadPrime.cuspExpansionLinear 6 6 weightSixH = _
      rw [weightSixH, map_sub, map_add, map_smul, map_smul]
      rfl
    rw [he, map_sub, map_add, coeff_smul, coeff_smul, g_coeff hn, v_coeff hn, w_coeff hn]
    fin_cases n <;> norm_num [gCoefficients, vCoefficients, wCoefficients, coeffList,
      weightSixCoefficients]

/-- The entire actual classical cusp space satisfies the Hecke annihilator. -/
theorem classicalWeightSixAnnihilator_eq_zero (f : ClassicalWeightSix) :
    classicalWeightSixAnnihilator f = 0 :=
  weightSix_identity_of_coefficient_certificate weightSixForms weightSixForms_coefficients f

theorem LevelSix.firstThree_surjective : Function.Surjective LevelSix.firstThree := by
  intro c
  refine ⟨c 0 • basisCuspForm 0 + (c 1 + 6 * c 0) • basisCuspForm 1 +
    (c 2 - 9 * c 0) • basisCuspForm 2, ?_⟩
  rw [map_add, map_add, map_smul, map_smul, map_smul]
  ext i
  change c 0 * (qExpansion 1 (basisCuspForm 0)).coeff (i.val + 1) +
    (c 1 + 6 * c 0) * (qExpansion 1 (basisCuspForm 1)).coeff (i.val + 1) +
    (c 2 - 9 * c 0) * (qExpansion 1 (basisCuspForm 2)).coeff (i.val + 1) = c i
  rw [g_coeff (by omega), v_coeff (by omega), w_coeff (by omega)]
  fin_cases i <;> norm_num [gCoefficients, vCoefficients, wCoefficients, coeffList] <;> (first | rfl | ring_nf <;> rfl)

/-- The first three positive coefficients are coordinates on the actual cusp space. -/
noncomputable def weightSixCoefficientEquiv : ClassicalWeightSix ≃ₗ[ℂ] (Fin 3 → ℂ) :=
  LinearEquiv.ofBijective LevelSix.firstThree
    ⟨LevelSix.firstThree_injective, LevelSix.firstThree_surjective⟩

theorem weightSix_finrank_eq_three : Module.finrank ℂ ClassicalWeightSix = 3 := by
  rw [weightSixCoefficientEquiv.finrank_eq]
  simp

/-- Unconditional annihilation for a reduction of an integral classical cusp expansion. -/
theorem IsReducedCuspExpansion.weightSix_annihilator_unconditional
    {R S : Type*} [CommRing R] [CommRing S] {φ : R →+* ℂ} {ψ : R →+* S}
    (hφ : Function.Injective φ) {a : PowerSeries S}
    (ha : IsReducedCuspExpansion φ ψ 6 6 a) : weightSixAnnihilator a = 0 :=
  ha.weightSix_annihilator hφ classicalWeightSixAnnihilator_eq_zero

end RamanujanTau.TheoremA
