import RamanujanTau.TheoremA.BadPrimeQExpansion

/-!
# Bad-prime operators on integral and reduced cusp expansions

The spaces here are defined by q-expansions of actual complex cusp forms.
They are not an abstract matrix model. The reduction predicate does not claim
that every Katz cusp form lifts to this classical space; that comparison is
a separate obligation for Theorem A.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open PowerSeries CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A coefficient-ring series represented by an actual level-`N` cusp form
under the specified map into the complex numbers. -/
def IsCuspExpansion (φ : R →+* ℂ) (N : ℕ) (k : ℤ) (a : PowerSeries R) : Prop :=
  ∃ f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k,
    qExpansion 1 f = PowerSeries.map φ a

/-- Reduction of a classical cusp expansion along a ring homomorphism.
For reduction modulo a prime, the source can be an integral coefficient ring
and the target its residue field. -/
def IsReducedCuspExpansion (φ : R →+* ℂ) (ψ : R →+* S) (N : ℕ) (k : ℤ)
    (a : PowerSeries S) : Prop :=
  ∃ b : PowerSeries R, IsCuspExpansion φ N k b ∧ PowerSeries.map ψ b = a

theorem map_U_series (ψ : R →+* S) (p : ℕ) (a : PowerSeries R) :
    PowerSeries.map ψ (BoylanWebb.U p a) = BoylanWebb.U p (PowerSeries.map ψ a) := by
  ext n
  simp [BoylanWebb.coeff_U]

/-- Bad-prime coefficient extraction preserves actual classical cusp expansions. -/
theorem IsCuspExpansion.U {φ : R →+* ℂ} {N p : ℕ} [NeZero N] [Fact p.Prime]
    {k : ℤ} {a : PowerSeries R} (ha : IsCuspExpansion φ N k a) (hN : p ∣ N) :
    IsCuspExpansion φ N k (BoylanWebb.U p a) := by
  obtain ⟨f, hf⟩ := ha
  refine ⟨BadPrime.cuspU hN f, ?_⟩
  rw [BadPrime.qExpansion_cuspU, hf, map_U_series]

/-- This closure survives coefficient reduction, over arbitrary residue rings. -/
theorem IsReducedCuspExpansion.U {φ : R →+* ℂ} {ψ : R →+* S}
    {N p : ℕ} [NeZero N] [Fact p.Prime] {k : ℤ} {a : PowerSeries S}
    (ha : IsReducedCuspExpansion φ ψ N k a) (hN : p ∣ N) :
    IsReducedCuspExpansion φ ψ N k (BoylanWebb.U p a) := by
  obtain ⟨b, hb, rfl⟩ := ha
  exact ⟨BoylanWebb.U p b, hb.U hN, map_U_series ψ p b⟩

end RamanujanTau.TheoremA
