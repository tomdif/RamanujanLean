/-
# `GoodSecondTerm/`: the χ-free symmetric AFE for `|L(Δ,6+it)|²` and Good's second term

Headlines (namespace `RamanujanTau.GoodSecondTerm`), all axiom-clean:

* `afe_exact_delta` — exact AFE `π|L(6+it)|² = Σ_{m,n} ∫ R_t(z)e^{z²}/z τ(m)m^{−6−z−it}τ(n)n^{−6−z+it} dy`.
* `delta_afe` — smoothed AFE with explicit main term and error `O(t^{−1/2})`:
  `|L(Δ,6+it)|² = Σ_{m,n} τ(m)τ(n)(mn)^{−6}(n/m)^{it} V(log(mn) − 2log(t/2π)) + O(t^{−1/2})`.
* `gamma_ratio_delta` — second-order Stirling: `R_t(c+iy)(t/2π)^{−2(c+iy)} = 1 + O(e^{y²/2}/t²)`.
* `AA_asymp`, `abs_DsumD_sub_le` — `Σ_{n≤N} τ(n)²/n¹² = c₀ log N + γ_Δ + O(N^{−1/5})` and the
  `V`-smoothed diagonal `= c₀L + 2γ_Δ + O((1+|L|)e^{−L/10})`.
* `good_reduction` — **unconditional**: `∫₀ᵀ|L(Δ,6+it)|² = 2c₀T log(T/2π) + (2γ_Δ − 2c₀)T + Off(T) + O(T^{9/10})`.
* `good_second_term_of_offdiag` — under `OffDiagHyp δ` (`|Off(T)| ≤ CT^{1−δ}`) the error is
  `O(T^{1−δ} + T^{9/10})`.
-/
import RamanujanTau.GoodSecondTerm.GoodMain

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm

open Complex RamanujanTau.ZetaAFE RamanujanTau.HeckeL

/-- **Smoothed χ-free AFE for `|L(Δ,6+it)|²`**, error `O(t^{−1/2})`. -/
theorem delta_afe : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 16 ≤ t →
    ‖((‖tauL (6 + t * I)‖ ^ 2 : ℝ) : ℂ) - ∑' p : ℕ × ℕ, bD t (2 * Real.log (t / (2 * Real.pi))) p‖ ≤
      C * t ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := pointwise_err_D
  refine ⟨C, hC0, fun t ht => ?_⟩
  have e := tsum_bD_split t
  unfold ellT at e
  rw [e, ← sub_sub]
  have := hC t ht
  unfold ellT at this
  exact this

end RamanujanTau.GoodSecondTerm

#print axioms RamanujanTau.GoodSecondTerm.afe_exact_delta
#print axioms RamanujanTau.GoodSecondTerm.delta_sq_approx
#print axioms RamanujanTau.GoodSecondTerm.norm_digamma_second
#print axioms RamanujanTau.GoodSecondTerm.norm_EfD_le
#print axioms RamanujanTau.GoodSecondTerm.gamma_ratio_delta
#print axioms RamanujanTau.GoodSecondTerm.delta_afe
#print axioms RamanujanTau.GoodSecondTerm.AA_asymp
#print axioms RamanujanTau.GoodSecondTerm.abs_DsumD_sub_le
#print axioms RamanujanTau.GoodSecondTerm.diag_err_D
#print axioms RamanujanTau.GoodSecondTerm.good_reduction
#print axioms RamanujanTau.GoodSecondTerm.good_second_term_of_offdiag
