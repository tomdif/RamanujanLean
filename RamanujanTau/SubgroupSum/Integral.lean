import RamanujanTau.SubgroupSum.Galois

/-!
# Polynomiality of the generic subgroup sum, modulo integrality of torsion abscissae

Let `R` be an integrally closed domain with `2` a unit, `F = Frac R`, `L/F` Galois, and
`E : y² = x³ + ax + b` with `a, b ∈ R`. If the `x`-coordinates of the points of the subgroups of
order `n` of `E(L)` are integral over `R`, then for every `Φ ∈ R[X₀, X₁]`,
`Σ_{|G| = n} Φ(c₄(E/G), −c₆(E/G)) ∈ R` (**`subSum_mem_range_of_integral`**).

For the universal curve, `R = ℚ[A, B]` and `L = AlgebraicClosure (Frac R)`
(**`universal_subSum_mem`**): the generic subgroup sum is a polynomial in `A, B`, *provided* the
integrality hypothesis `hint` (which is the standard fact that `x(P)` is a root of the
`p`-division polynomial `ψ_p ∈ ℤ[A,B][x]`, leading coefficient `p`; not formalized here).
-/

set_option autoImplicit false

namespace SubgroupSum

open Velu WeierstrassCurve

variable {R F L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field F] [Algebra R F]
  [IsFractionRing R F] [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L] [DecidableEq L]

omit [IsDomain R] [IsIntegrallyClosed R] [DecidableEq L] in
lemma aeval_mem_integralClosure {v : Fin 2 → L} (hv : ∀ i, v i ∈ integralClosure R L)
    (Φ : MvPolynomial (Fin 2) R) : MvPolynomial.aeval v Φ ∈ integralClosure R L := by
  induction Φ using MvPolynomial.induction_on with
  | C r => rw [MvPolynomial.aeval_C]; exact Subalgebra.algebraMap_mem _ r
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp => rw [map_mul, MvPolynomial.aeval_X]; exact mul_mem hp (hv i)

omit [IsDomain R] in
theorem subSum_mem_range_of_integral [IsGalois F L] (h2 : IsUnit (2 : R)) (n : ℕ) (a b : R)
    (Φ : MvPolynomial (Fin 2) R)
    (hint : ∀ G ∈ subs (algebraMap R L a) (algebraMap R L b) n, ∀ P ∈ G, IsIntegral R (xc P)) :
    subSum n (fun x y => MvPolynomial.aeval (HeckeQExp.ptR (short x y : WeierstrassCurve L)) Φ)
      (algebraMap R L a) (algebraMap R L b) ∈ Set.range (algebraMap R L) := by
  classical
  set A := algebraMap R L a
  set B := algebraMap R L b
  set s := subSum n (fun x y => MvPolynomial.aeval (HeckeQExp.ptR (short x y : WeierstrassCurve L)) Φ)
    A B with hs
  -- Step 1: `s ∈ F` (Galois descent).
  have hF : s ∈ Set.range (algebraMap F L) := by
    have := subSum_mem_range (F := F) (L := L) n (algebraMap R F a) (algebraMap R F b)
      (MvPolynomial.map (algebraMap R F) Φ)
    simp only [MvPolynomial.aeval_map_algebraMap] at this
    rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
  -- Step 2: `s` is integral over `R`.
  have hI : s ∈ integralClosure R L := by
    rw [hs]; unfold subSum
    split_ifs with h
    · refine Subalgebra.sum_mem _ fun G hG => ?_
      rw [Set.Finite.mem_toFinset] at hG
      have hx : ∀ P ∈ G, xc P ∈ integralClosure R L := hint G hG
      have hAm : A ∈ integralClosure R L := Subalgebra.algebraMap_mem _ a
      have hBm : B ∈ integralClosure R L := Subalgebra.algebraMap_mem _ b
      have hy : ∀ P ∈ G.erase 0, yc P ^ 2 ∈ integralClosure R L := by
        intro P hP
        rw [equation_xc_yc (Finset.ne_of_mem_erase hP)]
        have := hx P (Finset.mem_of_mem_erase hP)
        exact add_mem (add_mem (pow_mem this 3) (mul_mem hAm this)) hBm
      have hhalf : (2 : L)⁻¹ ∈ integralClosure R L := by
        have e : algebraMap R L ↑h2.unit⁻¹ * 2 = 1 := by
          have : (2 : L) = algebraMap R L (h2.unit : R) := by rw [IsUnit.unit_spec, map_ofNat]
          rw [this, ← map_mul, Units.inv_mul, map_one]
        rw [← eq_inv_of_mul_eq_one_left e]; exact Subalgebra.algebraMap_mem _ _
      have hnat : ∀ m : ℕ, (m : L) ∈ integralClosure R L := fun m => natCast_mem _ m
      have ht : tSum G ∈ integralClosure R L := by
        refine Subalgebra.sum_mem _ fun P hP => ?_
        rw [Kernel.tQ]
        have := hx P (Finset.mem_of_mem_erase hP)
        exact add_mem (mul_mem (hnat 6) (pow_mem this 2)) (mul_mem (hnat 2) hAm)
      have hw : wSum G ∈ integralClosure R L := by
        refine Subalgebra.sum_mem _ fun P hP => ?_
        rw [Kernel.tQ, Kernel.uQ]
        have := hx P (Finset.mem_of_mem_erase hP)
        exact add_mem (mul_mem (hnat 4) (hy P hP))
          (mul_mem this (add_mem (mul_mem (hnat 6) (pow_mem this 2)) (mul_mem (hnat 2) hAm)))
      have ha : aC G ∈ integralClosure R L := by
        rw [aC, div_eq_mul_inv]; exact sub_mem hAm (mul_mem (mul_mem (hnat 5) ht) hhalf)
      have hb : bC G ∈ integralClosure R L := by
        rw [bC, div_eq_mul_inv]; exact sub_mem hBm (mul_mem (mul_mem (hnat 7) hw) hhalf)
      refine aeval_mem_integralClosure (fun i => ?_) Φ
      rw [ptR_short]
      fin_cases i
      · simpa using neg_mem (mul_mem (hnat 48) ha)
      · simpa using mul_mem (hnat 864) hb
    · exact zero_mem _
  -- Step 3: `F ∩ (integral over R) = R`.
  obtain ⟨y, hy⟩ := hF
  rw [← hy] at hI ⊢
  have hyI : IsIntegral R y :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R F L) (algebraMap F L).injective).1 hI
  obtain ⟨r, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hyI
  exact ⟨r, IsScalarTower.algebraMap_apply R F L r⟩

/-- The universal base ring `ℚ[A, B]`. -/
abbrev RU := MvPolynomial (Fin 2) ℚ

/-- `(ℚ(A, B))^alg`. -/
abbrev LU := AlgebraicClosure (FractionRing RU)

lemma isUnit_two_RU : IsUnit (2 : RU) := by
  have : IsUnit (algebraMap ℚ RU 2) := (isUnit_iff_ne_zero.mpr two_ne_zero).map _
  rwa [map_ofNat] at this

/-- **The universal subgroup sum is a polynomial (modulo integrality of torsion abscissae).**
Over `L = (ℚ(A, B))^alg`, for the universal curve `y² = x³ + Ax + B` and `Φ ∈ ℚ[A,B][X₀, X₁]`. -/
theorem universal_subSum_mem [DecidableEq LU] (n : ℕ) (Φ : MvPolynomial (Fin 2) RU)
    (hint : ∀ G ∈ subs (algebraMap RU LU (MvPolynomial.X 0)) (algebraMap RU LU (MvPolynomial.X 1)) n,
      ∀ P ∈ G, IsIntegral RU (xc P)) :
    subSum n (fun x y => MvPolynomial.aeval (HeckeQExp.ptR (short x y : WeierstrassCurve LU)) Φ)
      (algebraMap RU LU (MvPolynomial.X 0)) (algebraMap RU LU (MvPolynomial.X 1)) ∈
      Set.range (algebraMap RU LU) :=
  subSum_mem_range_of_integral (F := FractionRing RU) isUnit_two_RU n _ _ Φ hint

end SubgroupSum
