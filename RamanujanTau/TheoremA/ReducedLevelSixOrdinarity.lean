import RamanujanTau.TheoremA.BinaryOrdinarity

/-!
# Ordinarity for reductions of actual level-six forms with the specified eigenvalues

Integral descent identifies reductions of actual complex modular forms with
the binary model. The newform Atkin–Lehner eigenvalue formulas are still
explicit inputs; no newform classification or Shimura correspondence is
assumed silently.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open ModularForm CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups

theorem binaryRep_of_reduced_modularForm {R F : Type*} [CommRing R] [Field F]
    (φ : R →+* ℂ) (hφ : Function.Injective φ) (ψ : R →+* F) (n : ℕ)
    (a : PowerSeries R)
    (g : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) (2 * n : ℕ))
    (ha : PowerSeries.map φ a = qExpansion 1 g) : BinaryRep (PowerSeries.map ψ a) n := by
  let c := evenCoordinates n (fun i : Fin (2 * n + 1) => a.coeff i.val)
  refine ⟨binaryPolynomial n (fun i => ψ (c i)), binaryPolynomial_homogeneous _ _, ?_⟩
  rw [binaryEv_binaryPolynomial, ← evenCombination_map]
  exact congrArg (PowerSeries.map ψ) (even_expansion_descent φ hφ n a g ha).symm

/-- The universal sign-eigenvalue result for reductions of actual classical forms. -/
theorem U_ne_zero_of_reduced_levelSix_sign_eigenvalues
    (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p)
    {R F : Type*} [CommRing R] [Field F] [CharP F p]
    (φ : R →+* ℂ) (hφ : Function.Injective φ) (ψ : R →+* F)
    (a : PowerSeries R)
    (g : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) ((p : ℤ) - 3))
    (ha : PowerSeries.map φ a = qExpansion 1 g)
    (hf0 : PowerSeries.map ψ a ≠ 0)
    (hU2 : BoylanWebb.U 2 (PowerSeries.map ψ a) =
      ((legendreSym p 2 : F) * (2 : F) ^ ((p - 5) / 2)) • PowerSeries.map ψ a)
    (hU3 : BoylanWebb.U 3 (PowerSeries.map ψ a) =
      ((legendreSym p 3 : F) * (3 : F) ^ ((p - 5) / 2)) • PowerSeries.map ψ a) :
    BoylanWebb.U p (PowerSeries.map ψ a) ≠ 0 := by
  have hd := hasse_degree_even (by omega : 5 ≤ p)
  have hk : (p : ℤ) - 3 = (2 * ((p - 3) / 2) : ℕ) := by omega
  have hrep := binaryRep_of_reduced_modularForm φ hφ ψ ((p - 3) / 2) a
    (ModularForm.mcast hk g) ha
  exact U_ne_zero_of_binary_sign_eigenvalues p hp13 _ hrep hf0 hU2 hU3

end RamanujanTau.TheoremA
