/-
# Evaluating power series over a complete ultrametric field

`evK V t = ∑ₖ Vₖ tᵏ` for `V : K⟦X⟧` and `t : K`. For series whose terms are norm-summable at `t`
(e.g. bounded coefficients and `‖t‖ < 1`, or polynomials), `evK` is multiplicative, agrees with
`Polynomial.eval`, and a series with `‖V₀‖ = 1`, `‖Vₖ‖ ≤ 1` has `‖evK V t‖ = 1` for `‖t‖ < 1`.

Over a ring `O` mapping continuously to `K`, the evaluation `Lubin.pt` of a series at a
topologically nilpotent point is carried by `ι` to `evK`.
-/
import RamanujanTau.LubinQuotient.LieBridge

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CanonicalIsogeny
open Finset

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- `evK V t = ∑' k, Vₖ tᵏ`. -/
noncomputable def evK (V : PowerSeries K) (t : K) : K := ∑' k, PowerSeries.coeff k V * t ^ k

/-- norm-summability of the terms of `V` at `t`. -/
def SN (V : PowerSeries K) (t : K) : Prop := Summable fun k => ‖PowerSeries.coeff k V * t ^ k‖

lemma sn_of_bdd {V : PowerSeries K} {t : K} (C : ℝ) (hV : ∀ k, ‖PowerSeries.coeff k V‖ ≤ C)
    (ht : ‖t‖ < 1) : SN V t := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg t) ht).mul_left C)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hV k) (by positivity)

lemma sn_poly (P : Polynomial K) (t : K) : SN (P : PowerSeries K) t := by
  refine summable_of_ne_finset_zero (s := range (P.natDegree + 1)) fun k hk => ?_
  rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by simp at hk; omega)]
  simp

lemma bdd_mul {V W : PowerSeries K} {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hV : ∀ k, ‖PowerSeries.coeff k V‖ ≤ C) (hW : ∀ k, ‖PowerSeries.coeff k W‖ ≤ D) :
    ∀ k, ‖PowerSeries.coeff k (V * W)‖ ≤ C * D := fun k => by
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun x _ => ?_
  rw [norm_mul]; exact mul_le_mul (hV _) (hW _) (norm_nonneg _) hC

lemma bdd_poly (P : Polynomial K) : ∃ C : ℝ, 0 ≤ C ∧ ∀ k, ‖PowerSeries.coeff k (P : PowerSeries K)‖ ≤ C := by
  refine ⟨∑ i ∈ range (P.natDegree + 1), ‖P.coeff i‖, by positivity, fun k => ?_⟩
  rw [Polynomial.coeff_coe]
  by_cases hk : k ∈ range (P.natDegree + 1)
  · exact single_le_sum (f := fun i => ‖P.coeff i‖) (fun _ _ => norm_nonneg _) hk
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simp at hk; omega), norm_zero]; positivity

variable [CompleteSpace K]

lemma summable_of_sn {V : PowerSeries K} {t : K} (h : SN V t) :
    Summable fun k => PowerSeries.coeff k V * t ^ k := h.of_norm

/-- **multiplicativity** of `evK`. -/
theorem evK_mul {V W : PowerSeries K} {t : K} (hV : SN V t) (hW : SN W t) :
    evK (V * W) t = evK V t * evK W t := by
  rw [evK, evK, evK, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hV hW]
  refine tsum_congr fun n => ?_
  rw [PowerSeries.coeff_mul, sum_mul]
  refine sum_congr rfl fun x hx => ?_
  rw [← mem_antidiagonal.mp hx, pow_add]; ring

theorem evK_poly (P : Polynomial K) (t : K) : evK (P : PowerSeries K) t = P.eval t := by
  rw [evK, tsum_eq_sum (s := range (P.natDegree + 1)), Polynomial.eval_eq_sum_range]
  · exact sum_congr rfl fun k _ => by rw [Polynomial.coeff_coe]
  · intro k hk
    rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by simp at hk; omega), zero_mul]

/-- a unit with integral coefficients evaluates to a unit of norm one. -/
theorem norm_evK_unit {U : PowerSeries K} (hU0 : ‖PowerSeries.constantCoeff U‖ = 1)
    (hU : ∀ k, ‖PowerSeries.coeff k U‖ ≤ 1) {t : K} (ht : ‖t‖ < 1) : ‖evK U t‖ = 1 := by
  have hs := summable_of_sn (sn_of_bdd 1 hU ht)
  rw [evK, hs.tsum_eq_zero_add, pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have htail : ‖∑' k, PowerSeries.coeff (k + 1) U * t ^ (k + 1)‖ ≤ ‖t‖ := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k => ?_
    rw [norm_mul, norm_pow]
    calc ‖PowerSeries.coeff (k + 1) U‖ * ‖t‖ ^ (k + 1) ≤ 1 * ‖t‖ ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (hU _) (by positivity)
      _ ≤ ‖t‖ := by rw [one_mul]; exact pow_le_of_le_one (norm_nonneg _) ht.le (by omega)
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hU0]; linarith), hU0]
  exact max_eq_left (by linarith)

end CanonicalIsogeny
