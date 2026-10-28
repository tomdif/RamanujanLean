/-
# The multivariable chain rule for substitution of power series

For `a : σ → R⟦τ⟧` with zero constant coefficients (`σ` finite):
  `∂ⱼ (f(a)) = Σ_s (∂ₛ f)(a) · ∂ⱼ aₛ`.
Proof: for polynomials by induction (`aeval`); in general by truncating `f` in total degree.
-/
import RamanujanTau.FormalGroupLayer.PDeriv

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace MvPowerSeries
open Finsupp

variable {σ τ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ] [DecidableEq τ]

/-- polynomial chain rule. -/
lemma pd_aeval (a : σ → MvPowerSeries τ R) (j : τ) (p : MvPolynomial σ R) :
    pd j (MvPolynomial.aeval a p) = ∑ s, MvPolynomial.aeval a (MvPolynomial.pderiv s p) * pd j (a s) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.aeval_C, MvPolynomial.pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
    rw [show (algebraMap R (MvPowerSeries τ R)) c = C c from rfl, pd_C]
  | add p q hp hq =>
    simp only [map_add, pd_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p s₀ hp =>
    simp only [map_mul, MvPolynomial.aeval_X, pd_mul, hp, Derivation.leibniz, MvPolynomial.pderiv_X,
      smul_eq_mul, map_add, add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · rw [Finset.sum_eq_single s₀ (fun s _ hs => by simp [Pi.single_apply, Ne.symm hs])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp
    · rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => by ring

variable {a : σ → MvPowerSeries τ R}

lemma hasSubst_of_zero (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a :=
  hasSubst_of_constantCoeff_zero ha

/-- substitution respects agreement in low total degree. -/
lemma coeff_subst_congr (ha : ∀ s, constantCoeff (a s) = 0) (N : ℕ) (g₁ g₂ : MvPowerSeries σ R)
    (h : ∀ d : σ →₀ ℕ, degree d < N → coeff d g₁ = coeff d g₂) (e : τ →₀ ℕ) (he : degree e < N) :
    coeff e (subst a g₁) = coeff e (subst a g₂) := by
  have hS := hasSubst_of_zero ha
  rw [← sub_eq_zero, ← map_sub, ← subst_sub hS]
  apply coeff_of_lt_order
  refine lt_of_lt_of_le ?_ (le_order_subst hS _)
  have hord : (N : ℕ∞) ≤ (g₁ - g₂).order :=
    le_order fun d hd => by rw [map_sub, h d (by exact_mod_cast hd), sub_self]
  have hmin : (1 : ℕ∞) ≤ ⨅ s, (a s).order := le_iInf fun s => by
    rw [one_le_order_iff_constCoeff_eq_zero]; exact ha s
  calc ((degree e : ℕ) : ℕ∞) < N := by exact_mod_cast he
    _ = 1 * N := (one_mul _).symm
    _ ≤ (⨅ s, (a s).order) * (g₁ - g₂).order := mul_le_mul' hmin hord

/-- **chain rule**. -/
theorem pd_subst (ha : ∀ s, constantCoeff (a s) = 0) (j : τ) (f : MvPowerSeries σ R) :
    pd j (subst a f) = ∑ s, subst a (pd s f) * pd j (a s) := by
  ext e
  set N := degree e + 2
  set P := truncTotal N f
  have hfP : ∀ d : σ →₀ ℕ, degree d < N → coeff d f = coeff d (P : MvPowerSeries σ R) := fun d hd => by
    rw [MvPolynomial.coeff_coe, coeff_truncTotal _ hd]
  -- left side
  have hL : coeff e (pd j (subst a f)) = coeff e (pd j (MvPolynomial.aeval a P)) := by
    rw [coeff_pd, coeff_pd, ← subst_coe]
    congr 1
    exact coeff_subst_congr ha N _ _ hfP _ (by simp only [N, map_add, degree_single]; omega)
  rw [hL, pd_aeval, map_sum, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  refine coeff_mul_congr e (fun m hm => ?_) fun m _ => rfl
  rw [← subst_coe]
  refine coeff_subst_congr ha (degree e + 1) _ _ (fun d hd => ?_) m ?_
  · rw [← pd_coe, coeff_pd, coeff_pd, hfP _ (by simp only [N, map_add, degree_single]; omega)]
  · have := degree_mono hm; omega

end MvPowerSeries
