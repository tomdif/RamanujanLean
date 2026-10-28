import RamanujanTau.HeckeBridge.Count
import RamanujanTau.TorsionSpec.Field

/-!
# One isobaric polynomial for every algebraically closed field

For `P ∈ K[X₀, X₁]` (`K` of characteristic `0`) we build, from the universal subgroup sums of the
monomials (`TorsionSpec.exists_universal`), explicit polynomials
* `SP p P ∈ K[A, B]` with `Σ_{|G| = p} P(ptR(E/G)) = (f SP)(a, b)`,
* `Siso p k P ∈ K[X₀, X₁]`, isobaric of weight `k` (`iso_Siso`), with
  `Σ_{|G| = p} P(ptR(E/G)) = (f Siso)(ptR E)` (`subSum_Siso`, for `P` isobaric of weight `k`),

for **every** algebraically closed field `L` of characteristic `0`, **every** ring map `f : K → L`
and every nonsingular short curve `E = short a b` over `L`. The point is that `Siso p k P` does not
depend on `L`: the same polynomial serves for `L = K` (`hAlg`) and for `L ⊇ K⟦t⟧` (`hT`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HeckeBridge

open Velu SubgroupSum MvPolynomial TorsionSpec ModP

/-! ### Linearity of the subgroup sum in the summand -/

lemma subSum_finsetSum {K : Type*} [Field K] [DecidableEq K] {ι : Type*} (s : Finset ι) (n : ℕ)
    (g : ι → K → K → K) (A B : K) :
    subSum n (fun x y => ∑ i ∈ s, g i x y) A B = ∑ i ∈ s, subSum n (g i) A B := by
  unfold subSum
  split_ifs
  · exact Finset.sum_comm
  · simp

variable (p : ℕ) [hp : Fact p.Prime]

/-- The universal subgroup sum (in `ℚ[A, B]`) of the monomial `X^d`. -/
noncomputable def univ (d : Fin 2 →₀ ℕ) : RU := by
  classical exact Classical.choose (exists_universal p (monomial d (1 : ℚ)))

lemma univ_spec [DecidableEq LU] (d : Fin 2 →₀ ℕ) :
    algebraMap RU LU (univ p d) = subSum p (fun x y =>
      aeval (HeckeQExp.ptR (short x y : WeierstrassCurve LU)) (monomial d (1 : ℚ)))
      (algebraMap RU LU (X 0)) (algebraMap RU LU (X 1)) := by
  classical
  have := Classical.choose_spec (exists_universal p (monomial d (1 : ℚ)))
  rw [univ]
  convert this

variable {K : Type*} [Field K] [CharZero K]

/-- `SP p P ∈ K[A, B]`: the subgroup sum of `P` as a polynomial in the short coefficients. -/
noncomputable def SP (P : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  ∑ d ∈ P.support, C (coeff d P) * map (algebraMap ℚ K) (univ p d)

/-- **The subgroup sum is `SP`**, over any algebraically closed `L` of characteristic `0`. -/
theorem subSum_SP {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] [DecidableEq L]
    (f : K →+* L) (P : MvPolynomial (Fin 2) K) (a b : L) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
    subSum p (fun x y => eval (HeckeQExp.ptR (short x y : WeierstrassCurve L)) (map f P)) a b =
      eval ![a, b] (map f (SP p P)) := by
  classical
  have hfun : (fun x y => eval (HeckeQExp.ptR (short x y : WeierstrassCurve L)) (map f P)) =
      fun x y => ∑ d ∈ P.support, f (coeff d P) *
        aeval (HeckeQExp.ptR (short x y : WeierstrassCurve L)) (monomial d (1 : ℚ)) := by
    funext x y
    conv_lhs => rw [P.as_sum]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_monomial, eval_monomial, aeval_monomial, map_one, one_mul]
  rw [hfun, subSum_finsetSum, SP, map_sum, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [subSum_mul, R2' p _ (univ p d) (univ_spec p d) a b hΔ, map_mul, map_C, map_mul, eval_C, map_map,
    eval_map]
  congr 1
  rw [aeval_def, show f.comp (algebraMap ℚ K) = algebraMap ℚ L from Subsingleton.elim _ _]

/-- `SP` rewritten in the variables `(c₄, −c₆) = (−48 A, 864 B)`. -/
noncomputable def Spt (P : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  aeval ![C (-1 / 48 : K) * X 0, C (1 / 864 : K) * X 1] (SP p P)

lemma eval_map_Spt {L : Type*} [Field L] [CharZero L] (f : K →+* L) (P : MvPolynomial (Fin 2) K)
    (a b : L) : eval ![-48 * a, 864 * b] (map f (Spt p P)) = eval ![a, b] (map f (SP p P)) := by
  set g : MvPolynomial (Fin 2) K →+* L := (eval ![-48 * a, 864 * b]).comp (map f)
  change g (aeval _ (SP p P)) = _
  rw [aeval_def, eval₂_comp_left, eval_map]
  congr 1
  · ext c; simp [g]
  · funext i; fin_cases i
    · simp [g, map_ofNat]; try field_simp
    · simp [g, map_ofNat]; try field_simp

/-- The isobaric polynomial: the weight-`k` component of `Spt p P`. -/
noncomputable def Siso (k : ℕ) (P : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  weightedHomogeneousComponent wt k (Spt p P)

lemma iso_Siso (k : ℕ) (P : MvPolynomial (Fin 2) K) : Iso (Siso p k P) k :=
  weightedHomogeneousComponent_isWeightedHomogeneous k _

omit [CharZero K] in
lemma map_whc {L : Type*} [Field L] (f : K →+* L) (k : ℕ) (Q : MvPolynomial (Fin 2) K) :
    map f (weightedHomogeneousComponent wt k Q) = weightedHomogeneousComponent wt k (map f Q) := by
  classical
  ext d
  rw [coeff_map, coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent, coeff_map]
  split_ifs <;> simp

omit [CharZero K] in
lemma iso_map {L : Type*} [Field L] (f : K →+* L) {k : ℕ} {P : MvPolynomial (Fin 2) K}
    (hP : Iso P k) : Iso (map f P) k := by
  intro d hd
  apply hP
  rw [coeff_map] at hd
  intro h; exact hd (by rw [h, map_zero])

/-- **The isobaric subgroup-sum polynomial.** For `P` isobaric of weight `k`, every algebraically
closed `L` of characteristic `0`, every `f : K →+* L` and every nonsingular short curve over `L`:
`Σ_{|G| = p} (fP)(ptR(E/G)) = (f Siso)(ptR E)`. -/
theorem subSum_Siso {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] [DecidableEq L]
    (f : K →+* L) {k : ℕ} {P : MvPolynomial (Fin 2) K} (hP : Iso P k) (a b : L)
    (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
    subSum p (fun x y => eval (HeckeQExp.ptR (short x y : WeierstrassCurve L)) (map f P)) a b =
      eval (HeckeQExp.ptR (short a b : WeierstrassCurve L)) (map f (Siso p k P)) := by
  haveI : Infinite L := CharZero.infinite L
  rw [Siso, map_whc, ptR_short]
  refine eval_eq_component_of_scaling k _ (fun u hu a b => subSum_ptR_scale hu a b p (iso_map f hP))
    (fun a b => 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (fun u hu a b h => disc_scale hu h) _
    (fun a b h => ?_) a b hΔ
  rw [subSum_SP p f P a b h, eval_map_Spt]

end HeckeBridge
