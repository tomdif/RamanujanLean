/-
# Step 2 of I2: `v(Lie π̌) = v`

* `coeff_one_comp`: the linear coefficient of a composite is the product of the linear coefficients.
* `norm_coeff_one_of_factor`: if `f = ∏_{h∈H}(X − h) · U` with exactly one root `0` and `‖U₀‖ = 1`, then
  `‖f'(0)‖ = ∏_{h≠0} ‖h‖`.
* `lie_dual`: given homomorphisms with `π̌ ∘ π = [p]`, whose kernel `H` is the canonical subgroup
  (`Canonical.canonical_subgroup`: `‖a‖ · ∏_{h≠0} ‖h‖ = ‖p‖`), we get `‖Lie π̌‖ = ‖a‖`, i.e.
  `v(Lie π̌) = v`.
-/
import RamanujanTau.AtkinOBrien.Canonical

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AtkinOBrien.Lie
open MvPowerSeries

variable {R : Type*} [CommRing R]

lemma coeff_one_eq (f : MvPowerSeries Unit R) :
    coeff (Finsupp.single () 1) f = constantCoeff (pd () f) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pd, zero_add]; simp

/-- linear coefficient of `f(g(T))`. -/
theorem coeff_one_comp (f g : MvPowerSeries Unit R) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    coeff (Finsupp.single () 1) (subst (fun _ : Unit => g) f) =
      coeff (Finsupp.single () 1) f * coeff (Finsupp.single () 1) g := by
  have h1 : ∀ s : Unit, constantCoeff ((fun _ : Unit => g) s) = 0 := fun _ => hg
  rw [coeff_one_eq, pd_subst h1, Fintype.sum_unique, map_mul, FGL.cc_subst _ h1, ← coeff_one_eq,
    ← coeff_one_eq]

/-- the derivative at `0` of `X · Q(X) · U(X)` is `Q(0) U(0)`. -/
theorem coeff_one_X_mul {K : Type*} [Field K] (Q : Polynomial K) (U : PowerSeries K) :
    PowerSeries.coeff 1 (((Polynomial.X * Q : Polynomial K) : PowerSeries K) * U) =
      Q.coeff 0 * PowerSeries.constantCoeff U := by
  rw [Polynomial.coe_mul, Polynomial.coe_X, mul_assoc, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, Polynomial.constantCoeff_coe]

variable {K : Type*} [NormedField K]

/-- `‖f'(0)‖ = ∏_{h ≠ 0} ‖h‖` for `f = X · ∏_{h∈H'} (X − h) · U`, `‖U₀‖ = 1`. -/
theorem norm_coeff_one_of_factor {κ : Type*} [Fintype κ] (r : κ → K) (U : PowerSeries K)
    (hU0 : ‖PowerSeries.constantCoeff U‖ = 1) :
    ‖PowerSeries.coeff 1 (((Polynomial.X * ∏ i, (Polynomial.X - Polynomial.C (r i)) : Polynomial K) :
      PowerSeries K) * U)‖ = ∏ i, ‖r i‖ := by
  rw [coeff_one_X_mul, norm_mul, hU0, mul_one, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod,
    norm_prod]
  simp

/-- **`v(Lie π̌) = v`**. Let `ι : R → K` and let `π, π̌` be series over `R` with `π̌ ∘ π = [p]`. Suppose
`ι(π) = X · ∏_{h ∈ H∖0} (X − h) · U` with `‖U₀‖ = 1`, and that the canonical-subgroup relation
`‖a‖ · ∏_{h≠0} ‖h‖ = ‖p‖` holds. Then `‖ι(π̌'(0))‖ = ‖a‖`. -/
theorem lie_dual (ι : R →+* K) (p : ℕ) (F : FormalGroup R) (π πd : MvPowerSeries Unit R)
    (hπ : constantCoeff π = 0) (hπd : constantCoeff πd = 0)
    (hcomp : subst (fun _ : Unit => π) πd = FGL.nmul F p)
    {κ : Type*} [Fintype κ] (r : κ → K) (U : PowerSeries K) (hU0 : ‖PowerSeries.constantCoeff U‖ = 1)
    (hW : MvPowerSeries.map ι π =
      (((Polynomial.X * ∏ i, (Polynomial.X - Polynomial.C (r i)) : Polynomial K) : PowerSeries K) * U))
    (a : K) (hcan : ‖a‖ * ∏ i, ‖r i‖ = ‖(p : K)‖) (hp : (p : K) ≠ 0) :
    ‖ι (coeff (Finsupp.single () 1) πd)‖ = ‖a‖ := by
  have hlin := congrArg ι (coeff_one_comp πd π hπd hπ)
  rw [hcomp, FGL.coeff_one_nmul, map_natCast, map_mul] at hlin
  have hμ : ‖ι (coeff (Finsupp.single () 1) π)‖ = ∏ i, ‖r i‖ := by
    have := congrArg (fun f : PowerSeries K => ‖PowerSeries.coeff 1 f‖) hW
    simp only at this
    rw [norm_coeff_one_of_factor r U hU0] at this
    rw [← this]; rfl
  have hn := congrArg norm hlin
  rw [norm_mul, hμ, ← hcan] at hn
  have hprod : 0 < ∏ i, ‖r i‖ := by
    rcases eq_or_lt_of_le (Finset.prod_nonneg fun i _ => norm_nonneg (r i)) with h | h
    · exfalso; rw [← h, mul_zero] at hcan; exact hp (norm_eq_zero.mp hcan.symm)
    · exact h
  exact mul_right_cancel₀ hprod.ne' hn.symm

end AtkinOBrien.Lie
