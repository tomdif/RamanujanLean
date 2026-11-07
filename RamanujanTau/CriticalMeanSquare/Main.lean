/-
# Mean square of `L(Δ, s)` on the critical line `Re s = 6`

Headlines (see `docs/CRITICAL_MEAN_SQUARE.md`):

* `critical_mean_square_upper` : `∫_0^T |L(Δ,6+it)|² dt ≤ C T log T` for `T ≥ e`;
* `dyadic_mean_square_upper`   : `∫_T^{2T} |L(Δ,6+it)|² dt ≤ C T log T` for `T ≥ e`;
* `dyadic_upper`, `cumulative_upper` : the same with `T (1 + log T)`, for `T ≥ 1`;
* `weighted_parseval` : exact identity, for `0 ≤ β < π/2`,
  `∫_ℝ |Λ(Δ,6+it)|² e^{2βt} dt = 2π ∫_ℝ |e^{6w}Δ(ie^w)|² du`, `w = u+iβ`;
* `parseval` : Plancherel for continuous integrable `F` with integrable `𝓕F`.

The upper bound is the Rankin (1939) / Good (1982) order `T log T`.  The matching lower bound and
the asymptotic constant are not formalized.
-/
import RamanujanTau.CriticalMeanSquare.Cumulative
import RamanujanTau.CriticalMeanSquare.Parseval

namespace RamanujanTau.CriticalMeanSquare

open Complex MeasureTheory Set
open RamanujanTau.HeckeL

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, Real.exp 1 ≤ T →
    ∫ t in Icc 0 T, ‖tauL (6 + t * I)‖ ^ 2 ≤ C * T * Real.log T := critical_mean_square_upper

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, Real.exp 1 ≤ T →
    ∫ t in Icc T (2 * T), ‖tauL (6 + t * I)‖ ^ 2 ≤ C * T * Real.log T := dyadic_mean_square_upper

end RamanujanTau.CriticalMeanSquare

#print axioms RamanujanTau.CriticalMeanSquare.critical_mean_square_upper
#print axioms RamanujanTau.CriticalMeanSquare.dyadic_mean_square_upper
#print axioms RamanujanTau.CriticalMeanSquare.dyadic_upper
#print axioms RamanujanTau.CriticalMeanSquare.cumulative_upper
#print axioms RamanujanTau.CriticalMeanSquare.mean_sq_Fs_six
#print axioms RamanujanTau.CriticalMeanSquare.weighted_parseval
#print axioms RamanujanTau.CriticalMeanSquare.parseval
