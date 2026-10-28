import RamanujanTau.TorsionSpec.Valuation
import RamanujanTau.SubgroupSum.Integral

/-!
# `R1`: torsion abscissae are integral

For a `ℚ`-algebra `R` (no further hypothesis: no domain / integrally closed assumption is needed),
a field `L` with `Algebra R L`, `a, b ∈ R`, and a subgroup `G` of order `n ≥ 1` of
`E(L)`, `E : y² = x³ + ax + b`, every `x(P)`, `P ∈ G`, is integral over `R`
(**`R1`**, the exact statement of `SubgroupSum.WIP.R1`), and hence the universal subgroup sum lies in
`ℚ[A, B]` unconditionally (**`universal_subSum_mem'`**).
-/

set_option autoImplicit false

namespace TorsionSpec

open Velu SubgroupSum

/-- Lagrange: a point of a subgroup of order `n` is killed by `n`. -/
lemma nsmul_eq_zero_of_mem_subs {K : Type*} [Field K] [DecidableEq K] {A B : K} {n : ℕ}
    {G : Finset (short A B).Point} (hG : G ∈ subs A B n) {P : (short A B).Point} (hP : P ∈ G) :
    n • P = 0 := by
  obtain ⟨hS, hc⟩ := hG
  have hfin : Finite hS.toAddSubgroup := (G.finite_toSet).to_subtype
  have hcard : Nat.card hS.toAddSubgroup = n := by
    change Nat.card (G : Set (short A B).Point) = n
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, hc]
  have := card_nsmul_eq_zero' (G := hS.toAddSubgroup) (x := ⟨P, hP⟩)
  rw [hcard] at this
  exact congrArg Subtype.val this

/-- **R1.** Exactly the statement of `SubgroupSum.WIP.R1` (the `IsDomain` hypothesis is unused). -/
theorem R1 {R L : Type*} [CommRing R] [Algebra ℚ R] [IsDomain R] [Field L] [Algebra R L]
    [DecidableEq L] (a b : R) (n : ℕ) (hn : 0 < n)
    (G : Finset (short (algebraMap R L a) (algebraMap R L b)).Point)
    (hG : G ∈ subs (algebraMap R L a) (algebraMap R L b) n) :
    ∀ P ∈ G, IsIntegral R (xc P) := fun _ hP =>
  isIntegral_xc_of_nsmul_eq_zero a b hn (nsmul_eq_zero_of_mem_subs hG hP)

/-- **The universal subgroup sum is a polynomial**, unconditionally. -/
theorem universal_subSum_mem' [DecidableEq LU] (n : ℕ) (hn : 0 < n) (Φ : MvPolynomial (Fin 2) RU) :
    subSum n (fun x y => MvPolynomial.aeval (HeckeQExp.ptR (short x y : WeierstrassCurve LU)) Φ)
      (algebraMap RU LU (MvPolynomial.X 0)) (algebraMap RU LU (MvPolynomial.X 1)) ∈
      Set.range (algebraMap RU LU) :=
  universal_subSum_mem n Φ (fun G hG => R1 _ _ n hn G hG)

end TorsionSpec
