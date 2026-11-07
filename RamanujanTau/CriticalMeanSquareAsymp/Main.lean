/-
# `∫_0^T |L(Δ,6+it)|² dt ~ 2c · T log T` (Good 1982), and the weighted asymptotic

Headlines (namespace `RamanujanTau.CriticalMeanSquareAsymp`), see
`docs/CRITICAL_MEAN_SQUARE_ASYMP.md`:

* (A) `critical_mean_square_asymptotic`:
  `Tendsto (fun T => (∫ t in Icc 0 T, ‖tauL (6 + t*I)‖^2) / (T * log T)) atTop (𝓝 cDelta)`,
  `cDelta = 2 · (3/π)(4π)¹²‖Δ‖²/11!` (`cDelta_eq`), twice the constant of
  `RankinExact.rankinSelberg_exact` (`rankin_normalization`).
* (B) `weighted_asymptotic`: `κ¹² ∫ |Λ(6+it)|² e^{2βt} dt / log(1/κ) → 12‖Δ‖²`, `κ = cot β → 0⁺`.
* (B′) `laplace_asymptotic`: `λ¹² ∫_0^∞ t¹¹ e^{−λt} |L(6+it)|² dt / log(1/λ) → Kc`.
-/
import RamanujanTau.CriticalMeanSquareAsymp.Final

namespace RamanujanTau.CriticalMeanSquareAsymp

#print axioms critical_mean_square_asymptotic
#print axioms cDelta_eq
#print axioms rankin_normalization
#print axioms weighted_asymptotic
#print axioms weighted_lambda
#print axioms laplace_asymptotic
#print axioms convC_gKQ
#print axioms convC_of_continuous
#print axioms ray_tendsto
#print axioms harm_tendsto
#print axioms sum_sharp
#print axioms block_sharp
#print axioms norm_Gamma_six_sq
#print axioms weight_eq
#print axioms tendsto_kG_ratio

end RamanujanTau.CriticalMeanSquareAsymp
