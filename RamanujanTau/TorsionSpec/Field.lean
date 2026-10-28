import RamanujanTau.TorsionSpec.Final

/-!
# `R2` over an arbitrary field of characteristic `0`

For a field `F` of characteristic `0` (e.g. `K((t))`, `FractionRing K⟦t⟧`) and `a, b ∈ F` with
`4a³ + 27b² ≠ 0`, the subgroup sum is taken over the subgroups of `E(F̄)`, `F̄ = AlgebraicClosure F`.

* **`R2_field`**: with `s ∈ ℚ[A,B]` the universal subgroup sum of `Φ ∈ ℚ[X₀,X₁]`,
  `Σ_{G ≤ E(F̄), |G| = p} Φ(ptR(E/G)) = s(a, b)` (an element of `F`).
* **`exists_universal`**: such `s` exists for every `Φ ∈ ℚ[X₀,X₁]`.
* **`exists_poly_field`**: for `Φ ∈ F[X₀,X₁]` there is one `S ∈ F[A,B]` (independent of `a, b`)
  with `Σ_{G ≤ E(F̄), |G| = p} Φ(ptR(E/G)) = S(a, b)` for all nonsingular `(a, b)`.
-/

set_option autoImplicit false

namespace TorsionSpec

open Velu SubgroupSum

/-- **R2 over any field of characteristic `0`.** -/
theorem R2_field {F : Type*} [Field F] [CharZero F] [DecidableEq (AlgebraicClosure F)]
    [DecidableEq LU] (p : ℕ) [hp : Fact p.Prime] (Φ : MvPolynomial (Fin 2) ℚ) (s : RU)
    (hs : algebraMap RU LU s = subSum p (fun x y => MvPolynomial.aeval
      (HeckeQExp.ptR (short x y : WeierstrassCurve LU)) Φ)
      (algebraMap RU LU (MvPolynomial.X 0)) (algebraMap RU LU (MvPolynomial.X 1)))
    (a b : F) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
    subSum p (fun x y => MvPolynomial.aeval
        (HeckeQExp.ptR (short x y : WeierstrassCurve (AlgebraicClosure F))) Φ)
      (algebraMap F (AlgebraicClosure F) a) (algebraMap F (AlgebraicClosure F) b) =
      algebraMap F (AlgebraicClosure F) (MvPolynomial.aeval ![a, b] s) := by
  have : CharZero (AlgebraicClosure F) :=
    charZero_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective
  have hΔ' : 4 * algebraMap F (AlgebraicClosure F) a ^ 3 +
      27 * algebraMap F (AlgebraicClosure F) b ^ 2 ≠ 0 := by
    intro h; apply hΔ; apply (algebraMap F (AlgebraicClosure F)).injective
    simpa [map_ofNat] using h
  rw [R2' p Φ s hs _ _ hΔ', ← MvPolynomial.aeval_algebraMap_apply]
  congr 2
  funext i; fin_cases i <;> rfl

/-- The universal subgroup sum of `Φ ∈ ℚ[X₀, X₁]` lies in `ℚ[A, B]`. -/
theorem exists_universal [DecidableEq LU] (p : ℕ) [hp : Fact p.Prime]
    (Φ : MvPolynomial (Fin 2) ℚ) : ∃ s : RU, algebraMap RU LU s = subSum p (fun x y =>
      MvPolynomial.aeval (HeckeQExp.ptR (short x y : WeierstrassCurve LU)) Φ)
      (algebraMap RU LU (MvPolynomial.X 0)) (algebraMap RU LU (MvPolynomial.X 1)) := by
  obtain ⟨s, hs⟩ := universal_subSum_mem' p hp.out.pos (MvPolynomial.map (algebraMap ℚ RU) Φ)
  refine ⟨s, hs.trans ?_⟩
  simp only [MvPolynomial.aeval_map_algebraMap]

/-! ### Linearity of the subgroup sum -/

section Lin
variable {K : Type*} [Field K] [DecidableEq K]

lemma subSum_add (n : ℕ) (f g : K → K → K) (A B : K) :
    subSum n (fun x y => f x y + g x y) A B = subSum n f A B + subSum n g A B := by
  unfold subSum; split_ifs <;> simp [Finset.sum_add_distrib]

lemma subSum_mul (n : ℕ) (c : K) (f : K → K → K) (A B : K) :
    subSum n (fun x y => c * f x y) A B = c * subSum n f A B := by
  unfold subSum; split_ifs <;> simp [Finset.mul_sum]

end Lin

/-- **Polynomiality over any field of characteristic `0`**, with coefficients in that field. -/
theorem exists_poly_field {F : Type*} [Field F] [CharZero F] [DecidableEq (AlgebraicClosure F)]
    (p : ℕ) [hp : Fact p.Prime] (Φ : MvPolynomial (Fin 2) F) :
    ∃ S : MvPolynomial (Fin 2) F, ∀ a b : F, 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 →
      subSum p (fun x y => MvPolynomial.aeval
          (HeckeQExp.ptR (short x y : WeierstrassCurve (AlgebraicClosure F))) Φ)
        (algebraMap F (AlgebraicClosure F) a) (algebraMap F (AlgebraicClosure F) b) =
        algebraMap F (AlgebraicClosure F) (MvPolynomial.aeval ![a, b] S) := by
  classical
  induction Φ using MvPolynomial.induction_on' with
  | monomial d c =>
    obtain ⟨s, hs⟩ := exists_universal p (MvPolynomial.monomial d (1 : ℚ))
    refine ⟨MvPolynomial.C c * MvPolynomial.map (algebraMap ℚ F) s, fun a b hΔ => ?_⟩
    have e : ∀ x y : AlgebraicClosure F, MvPolynomial.aeval
        (HeckeQExp.ptR (short x y : WeierstrassCurve (AlgebraicClosure F)))
        (MvPolynomial.monomial d c) = algebraMap F (AlgebraicClosure F) c *
        MvPolynomial.aeval (HeckeQExp.ptR (short x y : WeierstrassCurve (AlgebraicClosure F)))
          (MvPolynomial.monomial d (1 : ℚ)) := by
      intro x y; simp [MvPolynomial.aeval_monomial]
    simp only [e]
    rw [subSum_mul, R2_field p _ s hs a b hΔ, map_mul, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.aeval_map_algebraMap, Algebra.algebraMap_self, RingHom.id_apply]
  | add P Q hP hQ =>
    obtain ⟨S₁, h₁⟩ := hP
    obtain ⟨S₂, h₂⟩ := hQ
    refine ⟨S₁ + S₂, fun a b hΔ => ?_⟩
    simp only [map_add]
    rw [subSum_add, h₁ a b hΔ, h₂ a b hΔ]

end TorsionSpec

/-! ### Instances for the Tate-curve base fields -/

namespace TorsionSpec

instance charZero_fractionRing_powerSeries {K : Type*} [Field K] [CharZero K] :
    CharZero (FractionRing (PowerSeries K)) :=
  charZero_of_injective_algebraMap (algebraMap K (FractionRing (PowerSeries K))).injective

instance charZero_laurentSeries {K : Type*} [Field K] [CharZero K] : CharZero (LaurentSeries K) :=
  charZero_of_injective_algebraMap (algebraMap K (LaurentSeries K)).injective

example {K : Type} [Field K] [CharZero K]
    [DecidableEq (AlgebraicClosure (FractionRing (PowerSeries K)))]
    (p : ℕ) [Fact p.Prime] (Φ : MvPolynomial (Fin 2) (FractionRing (PowerSeries K))) :=
  exists_poly_field (F := FractionRing (PowerSeries K)) p Φ

example {K : Type} [Field K] [CharZero K] [DecidableEq (AlgebraicClosure (LaurentSeries K))]
    (p : ℕ) [Fact p.Prime] (Φ : MvPolynomial (Fin 2) (LaurentSeries K)) :=
  exists_poly_field (F := LaurentSeries K) p Φ

end TorsionSpec
