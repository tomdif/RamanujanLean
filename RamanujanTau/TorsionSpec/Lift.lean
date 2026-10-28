import Mathlib

/-!
# Extending a ring map along an integral extension into an algebraically closed field

`exists_lift_of_isIntegral`: for an integral ring extension `R → S` (injective) and any ring map
`φ : R → K` into an algebraically closed field, there is `ψ : S → K` with `ψ ∘ algebraMap = φ`
(lying over `ker φ`, then `IsAlgClosed.lift` on the quotient domains).
-/

set_option autoImplicit false

namespace TorsionSpec

theorem exists_lift_of_isIntegral {R S K : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [Field K] [IsAlgClosed K] (φ : R →+* K)
    (hinj : Function.Injective (algebraMap R S)) :
    ∃ ψ : S →+* K, ψ.comp (algebraMap R S) = φ := by
  classical
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker φ) (⊥ : Ideal S)
    (by
      intro r hr
      have : algebraMap R S r = 0 := by simpa using hr
      rw [show r = 0 from hinj (by rw [this, map_zero])]; exact zero_mem _)
  set R' := R ⧸ Q.comap (algebraMap R S)
  set S' := S ⧸ Q
  have hle : ∀ r ∈ Q.comap (algebraMap R S), φ r = 0 := by
    intro r hr; rw [hQc] at hr; exact hr
  let φ' : R' →+* K := Ideal.Quotient.lift _ φ hle
  have hφ'inj : Function.Injective φ' := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [Ideal.Quotient.eq_zero_iff_mem, hQc]
    exact hr
  letI : Algebra R' K := φ'.toAlgebra
  haveI : IsDomain S' := Ideal.Quotient.isDomain Q
  haveI : FaithfulSMul R' S' :=
    (faithfulSMul_iff_algebraMap_injective R' S').mpr Ideal.algebraMap_quotient_injective
  haveI : FaithfulSMul R' K := (faithfulSMul_iff_algebraMap_injective R' K).mpr hφ'inj
  haveI : IsDomain R' := (FaithfulSMul.algebraMap_injective R' K).isDomain _
  haveI : Module.IsTorsionFree R' S' := FaithfulSMul.to_isTorsionFree R' S'
  haveI : Module.IsTorsionFree R' K := FaithfulSMul.to_isTorsionFree R' K
  haveI : Algebra.IsIntegral R' S' := Algebra.IsIntegral.quotient
  haveI : Algebra.IsAlgebraic R' S' := Algebra.IsIntegral.isAlgebraic
  let L : S' →ₐ[R'] K := IsAlgClosed.lift (M := K) (R := R') (S := S')
  refine ⟨L.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  have e : Ideal.Quotient.mk Q (algebraMap R S r) =
      algebraMap R' S' (Ideal.Quotient.mk _ r) := rfl
  rw [e, L.commutes]
  rfl

end TorsionSpec
