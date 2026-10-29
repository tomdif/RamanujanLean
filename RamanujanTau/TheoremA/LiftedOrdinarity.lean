import RamanujanTau.TheoremA.WeightSixIdentity

/-!
# Ordinarity reduced to geometric filtration and lifting

The weight-six Hecke identity is now proved on the actual classical cusp space.
Its place in the earlier reduction can therefore be taken by a lifting input:
every weight-six theta iterate in question is a reduction of a classical cusp
expansion. The filtration laws, lifting, and initial eigenvalue formulas are
still explicit hypotheses. This conditional theorem is not Theorem A.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open PowerSeries

/-- A reduction of a classical weight-six cusp expansion cannot have the
forbidden eigenpair in characteristic at least five, unless it is zero. -/
theorem eq_zero_of_reduced_weightSix_eigenpair (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {K R : Type*} [Field K] [CharP K p] [CommRing R]
    {φ : R →+* ℂ} {ψ : R →+* K} (hφ : Function.Injective φ)
    {f : PowerSeries K} (hf : IsReducedCuspExpansion φ ψ 6 6 f)
    (h2 : BoylanWebb.U 2 f = (4 : K) • f)
    (h3 : BoylanWebb.U 3 f = (9 : K) • f) : f = 0 :=
  eigenvector_eq_zero_of_annihilated (uOperator 2) (uOperator 3) f
    (hf.weightSix_annihilator_unconditional hφ) (obstruction_scalar_ne_zero p hp) h2 h3

/-- The proved classical identity leaves only the geometric and newform inputs
in the proposed ordinarity argument. -/
theorem U_ne_zero_of_lifted_filtration_data (p : ℕ) [Fact p.Prime] (hp : 13 ≤ p)
    {K R : Type*} [Field K] [CharP K p] [CommRing R]
    {φ : R →+* ℂ} {ψ : R →+* K} (hφ : Function.Injective φ)
    (f : PowerSeries K) (hf : coeff 1 f ≠ 0)
    (filtration : PowerSeries K → ℤ) (drop : ℕ → ℤ)
    (hstart : filtration f = (p : ℤ) - 3)
    (hweight : ∀ i ≤ p - 1, 0 ≤ filtration ((theta ^ i) f))
    (hdrop_nonneg : ∀ i < p - 1, 0 ≤ drop i)
    (hstep : ∀ i < p - 1, filtration ((theta ^ (i + 1)) f) =
      filtration ((theta ^ i) f) + p + 1 - drop i * (p - 1 : ℤ))
    (hdrop : ∀ i < p - 1, ¬ (p : ℤ) ∣ filtration ((theta ^ i) f) → drop i = 0)
    (hlift : ∀ i, filtration ((theta ^ i) f) = 6 →
      IsReducedCuspExpansion φ ψ 6 6 ((theta ^ i) f))
    (hU2 : BoylanWebb.U 2 f =
      ((legendreSym p 2 : K) * (2 : K) ^ ((p - 5) / 2)) • f)
    (hU3 : BoylanWebb.U 3 f =
      ((legendreSym p 3 : K) * (3 : K) ^ ((p - 5) / 2)) • f) :
    BoylanWebb.U p f ≠ 0 :=
  U_ne_zero_of_filtration_data p hp f hf filtration drop hstart hweight hdrop_nonneg
    hstep hdrop (fun i hi => (hlift i hi).weightSix_annihilator_unconditional hφ) hU2 hU3

end RamanujanTau.TheoremA
