/-
# Good's mean-square asymptotic for every nonzero level-one cusp form

See `docs/GENERAL_CUSP_MOMENTS.md`.  Headlines (namespace `RamanujanTau.GeneralCuspMoments`):

* `fL_critical_mean_square_asymptotic f hf`:
  `Tendsto (fun T => (∫ t in Icc 0 T, ‖fL f (k/2 + t*I)‖^2) / (T * log T)) atTop (𝓝 (cF f))`,
  `cF f = 2 · rsConst f = 2 · (3/π)(4π)^k ‖f‖² / (k−1)!` (`cF_eq`, `cF_pos`);
* `fL_critical_mean_square_two_sided`: `c₁ T log T ≤ ∫_0^T |L(f,k/2+it)|² ≤ c₂ T log T`;
* `fL_weighted_asymptotic`, `fL_laplace_asymptotic`: the weighted / Laplace forms;
* `fL_discriminant_critical_mean_square_asymptotic`: at `f = Δ`, the constant is
  `CriticalMeanSquareAsymp.cDelta`;
* abstract tools: `tendsto_of_laplace` (Tauberian step with a-priori bound), `ray_tendsto`
  (ray integral of `|D|²` for any periodic holomorphic `D` with horocycle limit).
-/
import RamanujanTau.GeneralCuspMoments.Moments

#print axioms RamanujanTau.GeneralCuspMoments.fL_critical_mean_square_asymptotic
#print axioms RamanujanTau.GeneralCuspMoments.cF_eq
#print axioms RamanujanTau.GeneralCuspMoments.cF_pos
#print axioms RamanujanTau.GeneralCuspMoments.fL_critical_mean_square_two_sided
#print axioms RamanujanTau.GeneralCuspMoments.fL_weighted_asymptotic
#print axioms RamanujanTau.GeneralCuspMoments.fL_laplace_asymptotic
#print axioms RamanujanTau.GeneralCuspMoments.fL_discriminant_critical_mean_square_asymptotic
#print axioms RamanujanTau.GeneralCuspMoments.critical_mean_square_asymptotic_f
#print axioms RamanujanTau.GeneralCuspMoments.weighted_parseval_f
#print axioms RamanujanTau.GeneralCuspMoments.weighted_asymptotic_f
#print axioms RamanujanTau.GeneralCuspMoments.laplace_asymptotic_f
#print axioms RamanujanTau.GeneralCuspMoments.tendsto_of_laplace
#print axioms RamanujanTau.GeneralCuspMoments.upper_of_laplace
#print axioms RamanujanTau.GeneralCuspMoments.ray_tendsto
#print axioms RamanujanTau.GeneralCuspMoments.norm_Gamma_sq
#print axioms RamanujanTau.GeneralCuspMoments.tendsto_kG_ratio
#print axioms RamanujanTau.GeneralCuspMoments.exists_cusp_bound
