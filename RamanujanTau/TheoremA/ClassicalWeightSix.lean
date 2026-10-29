import RamanujanTau.TheoremA.IntegralCusp
import RamanujanTau.TheoremA.Reduction

/-!
# Transport of the weight-six relation from actual classical cusp forms

We define the polynomial in the actual analytic `U₂`, `U₃` operators and
identify its q-expansion action. If that polynomial vanishes on the classical
space, its relation passes to every reduced cusp expansion over a coefficient
ring embedded in `ℂ`. No integral splitting into old and new eigenspaces is used.

The classical polynomial identity itself remains unproved: the previously
checked integer matrices have not yet been identified with this analytic space.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open PowerSeries CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups

section Series
variable {R S : Type*} [CommRing R] [CommRing S]

/-- The annihilator is a six-term relation between actual q-coefficients. -/
theorem coeff_weightSixAnnihilator (a : PowerSeries R) (n : ℕ) :
    coeff n (weightSixAnnihilator a) = coeff (12 * n) a + 6 * coeff (6 * n) a +
      32 * coeff (3 * n) a + 9 * coeff (4 * n) a + 54 * coeff (2 * n) a + 288 * coeff n a := by
  simp [weightSixAnnihilator, pow_two, Module.End.mul_apply, uOperator_apply,
    BoylanWebb.coeff_U, ← Nat.mul_assoc]
  ring

/-- Coefficient reduction commutes with the polynomial, including over integral rings. -/
theorem map_weightSixAnnihilator (ψ : R →+* S) (a : PowerSeries R) :
    PowerSeries.map ψ (weightSixAnnihilator a) = weightSixAnnihilator (PowerSeries.map ψ a) := by
  ext n
  simp [coeff_weightSixAnnihilator, map_ofNat]

end Series

/-- The actual weight-six, level-six complex cusp space. -/
abbrev ClassicalWeightSix := CuspForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) 6

/-- The candidate annihilator on actual forms, using the constructed bad-prime Hecke operators. -/
noncomputable def classicalWeightSixAnnihilator : Module.End ℂ ClassicalWeightSix :=
  (BadPrime.cuspULinear (p := 3) (by decide : 3 ∣ 6) + (9 : ℂ) • 1) *
    (BadPrime.cuspULinear (p := 2) (by decide : 2 ∣ 6) ^ 2 +
      (6 : ℂ) • BadPrime.cuspULinear (p := 2) (by decide : 2 ∣ 6) + (32 : ℂ) • 1)

/-- The analytic polynomial and the formal-series polynomial agree. -/
theorem qExpansion_classicalWeightSixAnnihilator (f : ClassicalWeightSix) :
    qExpansion 1 (classicalWeightSixAnnihilator f) = weightSixAnnihilator (qExpansion 1 f) := by
  let E := BadPrime.cuspExpansionLinear 6 6
  have h2 : ∀ g : ClassicalWeightSix,
      E (BadPrime.cuspULinear (p := 2) (by decide : 2 ∣ 6) g) = uOperator 2 (E g) := by
    intro g
    exact BadPrime.qExpansion_cuspU (by decide : 2 ∣ 6) g
  have h3 : ∀ g : ClassicalWeightSix,
      E (BadPrime.cuspULinear (p := 3) (by decide : 3 ∣ 6) g) = uOperator 3 (E g) := by
    intro g
    exact BadPrime.qExpansion_cuspU (by decide : 3 ∣ 6) g
  change E (classicalWeightSixAnnihilator f) = weightSixAnnihilator (E f)
  simp only [classicalWeightSixAnnihilator, weightSixAnnihilator, pow_two, Module.End.mul_apply,
    LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul, h2, h3]

/-- The classical identity is equivalent to the full six-term coefficient
relation, for every form and every coefficient. A finite prefix is not enough
without a separately proved bound. -/
theorem classicalWeightSixAnnihilator_eq_zero_iff :
    (∀ f : ClassicalWeightSix, classicalWeightSixAnnihilator f = 0) ↔
      ∀ (f : ClassicalWeightSix) (n : ℕ),
        (qExpansion 1 f).coeff (12 * n) + 6 * (qExpansion 1 f).coeff (6 * n) +
          32 * (qExpansion 1 f).coeff (3 * n) + 9 * (qExpansion 1 f).coeff (4 * n) +
          54 * (qExpansion 1 f).coeff (2 * n) + 288 * (qExpansion 1 f).coeff n = 0 := by
  constructor
  · intro h f n
    have he := congrArg (PowerSeries.coeff n) (qExpansion_classicalWeightSixAnnihilator f)
    rw [h, CuspForm.coe_zero, qExpansion_zero, map_zero, coeff_weightSixAnnihilator] at he
    exact he.symm
  · intro h f
    apply BadPrime.cuspExpansionLinear_injective
    change qExpansion 1 _ = qExpansion 1 (0 : ClassicalWeightSix)
    rw [qExpansion_classicalWeightSixAnnihilator, CuspForm.coe_zero, qExpansion_zero]
    ext n
    rw [coeff_weightSixAnnihilator, map_zero]
    exact h f n

/-- A classical weight-six operator identity descends through every embedded
coefficient ring and every residue-ring map. The hypothesis is the identity on
the actual classical space, not an identity on unrelated numerical matrices. -/
theorem IsReducedCuspExpansion.weightSix_annihilator
    {R S : Type*} [CommRing R] [CommRing S] {φ : R →+* ℂ} {ψ : R →+* S}
    (hφ : Function.Injective φ)
    (hclassical : ∀ f : ClassicalWeightSix, classicalWeightSixAnnihilator f = 0)
    {a : PowerSeries S} (ha : IsReducedCuspExpansion φ ψ 6 6 a) :
    weightSixAnnihilator a = 0 := by
  obtain ⟨b, ⟨f, hf⟩, rfl⟩ := ha
  have hc : weightSixAnnihilator (PowerSeries.map φ b) = 0 := by
    rw [← hf, ← qExpansion_classicalWeightSixAnnihilator, hclassical,
      CuspForm.coe_zero, qExpansion_zero]
  have hb : weightSixAnnihilator b = 0 := by
    apply PowerSeries.map_injective φ hφ
    rw [map_weightSixAnnihilator, hc, map_zero]
  rw [← map_weightSixAnnihilator, hb, map_zero]

end RamanujanTau.TheoremA
