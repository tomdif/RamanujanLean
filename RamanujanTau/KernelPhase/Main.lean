/-
# `KernelPhase/`: the kernel bound `KernelOneBound m`, and Rankin–Selberg with every `δ < 2/5`,
unconditionally

Build: `nice -n 10 lake build RamanujanTau.KernelPhase.Main`. See `docs/KERNEL_PHASE.md`.

* `kernelOne_sharp`: `‖J_1(y)‖ ≤ C y^{9/8}` for `y ≥ 1`, the sharp exponent, for every `m ≥ 1`;
* `kernelOneBound`: `KernelOneBound m` for every `m ≥ 1`;
* `rankinSelberg_landau_uncond` and `rankinSelberg_landau_61_100_uncond` (for `τ`), plus
  `rankinSelberg_landau_general_uncond` (every level-one cusp form of weight `k ≥ 2`).

Method: a bent contour through the stationary height `|t| = 2πy^{1/4}`. Only the modulus
of the integrand is used. Off the strip `|Re s| ≤ 1/2` it is controlled by the exact
recursion `Q_1(w+1)·P(w) = 16π⁴Q_1(w)`, so no complex Stirling formula or phase estimate
is needed.
-/
import RamanujanTau.KernelPhase.Contour
import RamanujanTau.RankinLandau.Main

set_option autoImplicit false

namespace RamanujanTau.KernelPhase

open Complex Real Finset ModularForm
open RamanujanTau.RankinLandau RamanujanTau.RankinSelbergGeneral
open scoped MatrixGroups

/-- **Rankin–Selberg for `τ`, every `δ < 2/5`, unconditionally**:
`|∑_{n≤N} τ(n)²/n¹¹ − (3/π)(4π)¹²‖Δ‖²/11! · N| ≤ C N^{1−δ}`. -/
theorem rankinSelberg_landau_uncond {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 2 / 5) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ (1 - δ) :=
  rankinSelberg_landau (kernelOneBound (by norm_num)) hδ0 hδ

/-- For `τ`, the concrete exponent `61/100`, unconditionally. -/
theorem rankinSelberg_landau_61_100_uncond :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ (61 / 100 : ℝ) :=
  rankinSelberg_landau_61_100 (kernelOneBound (by norm_num))

/-- **Every level-one cusp form of weight `k ≥ 2`, every `δ < 2/5`, unconditionally.** -/
theorem rankinSelberg_landau_general_uncond {k : ℕ} (hk : 2 ≤ k) (f : CuspForm 𝒮ℒ (k : ℤ))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 2 / 5) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1) - rsConst f * N| ≤
        C * (N : ℝ) ^ (1 - δ) :=
  rankinSelberg_landau_general f (kernelOneBound (by omega)) hδ0 hδ

end RamanujanTau.KernelPhase

#print axioms RamanujanTau.KernelPhase.Qk_add_one
#print axioms RamanujanTau.KernelPhase.norm_G_add_nat_le
#print axioms RamanujanTau.KernelPhase.norm_G_sub_nat_le
#print axioms RamanujanTau.KernelPhase.Qk_bound_sharp
#print axioms RamanujanTau.KernelPhase.rect_diff
#print axioms RamanujanTau.KernelPhase.integral_G_le
#print axioms RamanujanTau.KernelPhase.kernelOne_sharp
#print axioms RamanujanTau.KernelPhase.kernelOneBound
#print axioms RamanujanTau.KernelPhase.rankinSelberg_landau_uncond
#print axioms RamanujanTau.KernelPhase.rankinSelberg_landau_61_100_uncond
#print axioms RamanujanTau.KernelPhase.rankinSelberg_landau_general_uncond
