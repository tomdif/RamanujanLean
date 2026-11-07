/-
# Matching the von Mangoldt sums with Kloosterman sums over an extension

For a finite extension `L/F` of finite fields of degree `k ≥ 1`,
`vM_eq_klL`: `V_k = Σ_{x ∈ L^×} ψ(Tr_{L/F}(a x + b x⁻¹))`.

Ingredients: every monic irreducible `P` with `deg P ∣ k` has exactly `deg P` roots in `L`
(an `F`-embedding `F[X]/(P) → L` exists since `deg P ∣ k`, `L/F` is normal, `P` separable);
`Tr x = (k/d)·(−c₁)` from the minimal polynomial; `minpoly x⁻¹` is the normalized reverse of
`minpoly x`, so `Tr x⁻¹ = (k/d)·(−P₁/P₀)`.
-/
import RamanujanTau.KloostermanL.Newton

set_option autoImplicit false

namespace RamanujanTau.KloostermanL

open Polynomial Finset IntermediateField
open scoped Classical

variable {F : Type*} [Field F] [Fintype F]
variable {L : Type*} [Field L] [Fintype L] [Algebra F L]

/-- The Kloosterman sum over an extension `L`, with the trace `L → F`. -/
noncomputable def klL (L : Type*) [Field L] [Fintype L] [Algebra F L] (ψ : AddChar F ℂ)
    (a b : F) : ℂ :=
  ∑ x : Lˣ, ψ (Algebra.trace F L (algebraMap F L a * x + algebraMap F L b * ((x⁻¹ : Lˣ) : L)))

omit [Fintype F] [Fintype L] in
/-- `minpoly x⁻¹` is the normalized reverse of `minpoly x`. -/
theorem minpoly_inv_eq {x : L} (hx : x ≠ 0) (hint : IsIntegral F x) :
    minpoly F x⁻¹ = C ((minpoly F x).coeff 0)⁻¹ * (minpoly F x).reverse := by
  set P := minpoly F x
  have hc0 : P.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx
  have htr : P.natTrailingDegree = 0 := natTrailingDegree_eq_zero.2 (Or.inr hc0)
  have hrdeg : P.reverse.natDegree = P.natDegree := by rw [reverse_natDegree, htr]; rfl
  have hP0 : P ≠ 0 := minpoly.ne_zero hint
  haveI : Invertible x := invertibleOfNonzero hx
  refine (minpoly.unique F x⁻¹ ?_ ?_ ?_).symm
  · rw [Monic, leadingCoeff_mul, leadingCoeff_C, reverse_leadingCoeff, trailingCoeff, htr,
      inv_mul_cancel₀ hc0]
  · have h0 : eval₂ (algebraMap F L) (⅟x) P.reverse = 0 := by
      rw [eval₂_reverse_eq_zero_iff, ← aeval_def, minpoly.aeval]
    rw [map_mul, aeval_C, aeval_def, ← invOf_eq_inv x, h0, mul_zero]
  · intro q hqm hq
    haveI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
    have hq' : aeval x q.reverse = 0 := by
      have : x = ⅟(x⁻¹) := by rw [invOf_eq_inv, inv_inv]
      rw [this, aeval_def, eval₂_reverse_eq_zero_iff, ← aeval_def, hq]
    have hdvd := minpoly.dvd F x hq'
    have hle := natDegree_le_of_dvd hdvd (by rw [Ne, reverse_eq_zero]; exact hqm.ne_zero)
    have hle2 := q.reverse_natDegree_le
    rw [degree_eq_natDegree (mul_ne_zero (by simpa using hc0) (by rwa [Ne, reverse_eq_zero])),
      degree_eq_natDegree hqm.ne_zero, natDegree_C_mul (inv_ne_zero hc0), hrdeg]
    exact_mod_cast hle.trans hle2

omit [Fintype F] [Fintype L] in
theorem natDegree_minpoly_inv {x : L} (hx : x ≠ 0) (hint : IsIntegral F x) :
    (minpoly F x⁻¹).natDegree = (minpoly F x).natDegree := by
  have hc0 : (minpoly F x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx
  rw [minpoly_inv_eq hx hint, natDegree_C_mul (inv_ne_zero hc0), reverse_natDegree,
    natTrailingDegree_eq_zero.2 (Or.inr hc0)]
  rfl

omit [Fintype F] [Fintype L] in
theorem nextCoeff_minpoly_inv {x : L} (hx : x ≠ 0) (hint : IsIntegral F x) :
    (minpoly F x⁻¹).nextCoeff = (minpoly F x).coeff 1 / (minpoly F x).coeff 0 := by
  have hc0 : (minpoly F x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx
  have hd := natDegree_minpoly_inv hx hint
  have hpos := minpoly.natDegree_pos hint
  rw [nextCoeff_of_natDegree_pos (by omega), hd, minpoly_inv_eq hx hint, coeff_C_mul,
    coeff_reverse, revAt_le (by omega), Nat.sub_sub_self (by omega), div_eq_inv_mul]

omit [Fintype F] in
/-- `finrank F⟮x⟯ L = k / deg(minpoly x)`. -/
theorem finrank_adjoin_eq {x : L} :
    Module.finrank F⟮x⟯ L = Module.finrank F L / (minpoly F x).natDegree := by
  haveI : FiniteDimensional F L := Module.Finite.of_finite
  have hint : IsIntegral F x := .of_finite F x
  rw [← Module.finrank_mul_finrank F F⟮x⟯ L, adjoin.finrank hint,
    Nat.mul_div_cancel_left _ (minpoly.natDegree_pos hint)]

omit [Fintype F] in
theorem natDegree_minpoly_dvd (x : L) :
    (minpoly F x).natDegree ∣ Module.finrank F L := by
  haveI : FiniteDimensional F L := Module.Finite.of_finite
  rw [← Module.finrank_mul_finrank F F⟮x⟯ L, adjoin.finrank (.of_finite F x)]
  exact dvd_mul_right _ _

variable (ψ : AddChar F ℂ) (a b : F)

omit [Fintype F] in
/-- For `x ≠ 0`: `λ(minpoly x)^{k/d} = ψ(Tr(a x + b x⁻¹))`. -/
theorem lam_minpoly_pow {x : L} (hx : x ≠ 0) :
    lam ψ a b (minpoly F x) ^ (Module.finrank F L / (minpoly F x).natDegree) =
      ψ (Algebra.trace F L (algebraMap F L a * x + algebraMap F L b * x⁻¹)) := by
  haveI : FiniteDimensional F L := Module.Finite.of_finite
  have hint : IsIntegral F x := .of_finite F x
  have hc0 : (minpoly F x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx
  set m := Module.finrank F L / (minpoly F x).natDegree
  have htx : Algebra.trace F L x = (m : F) * -(minpoly F x).nextCoeff := by
    rw [trace_eq_finrank_mul_minpoly_nextCoeff (K := F), finrank_adjoin_eq]
  have htxi : Algebra.trace F L x⁻¹ =
      (m : F) * -((minpoly F x).coeff 1 / (minpoly F x).coeff 0) := by
    rw [trace_eq_finrank_mul_minpoly_nextCoeff (K := F), finrank_adjoin_eq,
      natDegree_minpoly_inv hx hint, nextCoeff_minpoly_inv hx hint]
  have hlin : Algebra.trace F L (algebraMap F L a * x + algebraMap F L b * x⁻¹) =
      a * Algebra.trace F L x + b * Algebra.trace F L x⁻¹ := by
    rw [map_add, ← Algebra.smul_def, ← Algebra.smul_def, LinearMap.map_smul,
      LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
  rw [hlin, htx, htxi, lam, if_neg hc0, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  congr 1
  ring

/-- A monic irreducible `P` with `deg P ∣ [L:F]` has exactly `deg P` roots in `L`. -/
theorem card_minpoly_fiber {P : F[X]} (hPm : P.Monic) (hPi : Irreducible P)
    (hd : P.natDegree ∣ Module.finrank F L) :
    (univ.filter (fun x : L => minpoly F x = P)).card = P.natDegree := by
  haveI : Fact (Irreducible P) := ⟨hPi⟩
  have hfr : Module.finrank F (AdjoinRoot P) = P.natDegree :=
    (AdjoinRoot.powerBasis hPi.ne_zero).finrank.trans (AdjoinRoot.powerBasis_dim hPi.ne_zero)
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := F) (K := AdjoinRoot P) (L := L)
    (hfr ▸ hd)
  set x₀ := φ (AdjoinRoot.root P)
  have hx₀ : aeval x₀ P = 0 := by
    rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  have hPx₀ : P = minpoly F x₀ := minpoly.eq_of_irreducible_of_monic hPi hx₀ hPm
  have hsplit : Splits (P.map (algebraMap F L)) := by
    rw [hPx₀]; exact Normal.splits inferInstance x₀
  have hsep : P.Separable := PerfectField.separable_of_irreducible hPi
  have hfib : univ.filter (fun x : L => minpoly F x = P) = (P.aroots L).toFinset := by
    ext x
    rw [mem_filter, Multiset.mem_toFinset, mem_aroots]
    constructor
    · rintro ⟨-, rfl⟩
      exact ⟨minpoly.ne_zero (.of_finite F x), minpoly.aeval F x⟩
    · rintro ⟨-, h⟩
      exact ⟨mem_univ _, (minpoly.eq_of_irreducible_of_monic hPi h hPm).symm⟩
  rw [hfib, ← card_rootSet_eq_natDegree hsep hsplit]
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]

/-- **Root side.** For `[L:F] = k ≥ 1`: `V_k = Σ_{x ∈ L^×} ψ(Tr(ax + b/x))`. -/
theorem vM_eq_klL (hk : 1 ≤ Module.finrank F L) :
    vM ψ a b (Module.finrank F L) = klL L ψ a b := by
  set k := Module.finrank F L
  -- the sum over units as a sum over `L` of a function of the minimal polynomial
  have h1 : klL L ψ a b = ∑ x : L, lam ψ a b (minpoly F x) ^ (k / (minpoly F x).natDegree) := by
    rw [klL]
    simp_rw [Units.val_inv_eq_inv_val]
    rw [← sum_ne_zero_eq_sum_units (fun x : L =>
      ψ (Algebra.trace F L (algebraMap F L a * x + algebraMap F L b * x⁻¹)))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    split_ifs with hx
    · subst hx
      rw [minpoly.zero, lam_X, natDegree_X, Nat.div_one, zero_pow (by omega)]
    · exact (lam_minpoly_pow ψ a b hx).symm
  rw [h1, vM]
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ)
    (t := (irrLe k).filter (fun P : F[X] => P.natDegree ∣ k)) (g := fun x : L => minpoly F x)]
  · refine Finset.sum_congr rfl (fun P hP => ?_)
    rw [mem_filter, mem_irrLe] at hP
    rw [Finset.sum_congr rfl (fun x hx => by rw [(mem_filter.mp hx).2]), Finset.sum_const,
      card_minpoly_fiber hP.1.1 hP.1.2.1 hP.2, nsmul_eq_mul]
  · intro x _
    have hint : IsIntegral F x := .of_finite F x
    rw [mem_filter, mem_irrLe]
    have hdvd := natDegree_minpoly_dvd (F := F) x
    exact ⟨⟨minpoly.monic hint, minpoly.irreducible hint, Nat.le_of_dvd (by omega) hdvd⟩, hdvd⟩

end RamanujanTau.KloostermanL
