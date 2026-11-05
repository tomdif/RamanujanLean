/-
# Riemann–von Mangoldt for `L(Δ,s)` — headline statements

`zeroCount T = N(T)` = number of zeros of `L(Δ,s) = Σ τ(n) n^{-s}` with `0 < Im ≤ T`, counted
with multiplicity (all lie in `11/2 < Re < 13/2`).  See `docs/ZERO_COUNT_RVM.md`.
-/
import RamanujanTau.ZeroCountRvM.RvM

namespace RamanujanTau.ZeroCountRvM

open RamanujanTau.ZeroCount
open scoped Real

/-- **Riemann–von Mangoldt**: `N(T) = (T/π) log(T/(2πe)) + O(log T)`. -/
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 2 ≤ T →
    |(zeroCount T : ℝ) - T / π * Real.log (T / (2 * π * Real.exp 1))| ≤ C * Real.log T :=
  riemann_von_mangoldt

/-- **`N(T) ≫ T log T`**. -/
example : ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → T / (2 * π) * Real.log T ≤ zeroCount T :=
  zeroCount_ge_T_log_T

end RamanujanTau.ZeroCountRvM

#print axioms RamanujanTau.ZeroCountRvM.riemann_von_mangoldt
#print axioms RamanujanTau.ZeroCountRvM.zeroCount_ge_T_log_T
#print axioms RamanujanTau.ZeroCountRvM.rvm_nonordinate
#print axioms RamanujanTau.ZeroCountRvM.arg_principle_rect
#print axioms RamanujanTau.ZeroCountRvM.rectInt_inv_of_mem
#print axioms RamanujanTau.ZeroCountRvM.Gamma_eq_exp_LG
#print axioms RamanujanTau.ZeroCountRvM.digamma_eq_series
#print axioms RamanujanTau.ZeroCountRvM.digamma_eq_log_add
#print axioms RamanujanTau.ZeroCountRvM.integral_re_digamma_six
#print axioms RamanujanTau.ZeroCountRvM.abs_im_integral_logDeriv_le
#print axioms RamanujanTau.ZeroCountRvM.backlund
#print axioms RamanujanTau.ZeroCountRvM.pi_count_eq
#print axioms RamanujanTau.ZeroCountRvM.phi_eq
#print axioms RamanujanTau.ZeroCountRvM.gamma_cauchy
#print axioms RamanujanTau.ZeroCountRvM.sum_order_eq_zeroCount
