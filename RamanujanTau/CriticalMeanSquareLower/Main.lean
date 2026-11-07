/-
# `∫_0^T |L(Δ,6+it)|² dt ≍ T log T`

Headlines (namespace `RamanujanTau.CriticalMeanSquareLower`):

* `critical_mean_square_lower : ∃ c T₀, 0 < c ∧ ∀ T ≥ T₀,
    c * T * log T ≤ ∫ t in Icc 0 T, ‖tauL (6 + t*I)‖^2`
* `critical_mean_square_order` : the two-sided bound `c T log T ≤ ∫ ≤ C T log T`
* `critical_mean_square_isTheta` : `∫_0^T |L(6+it)|² =Θ[atTop] T log T`

Route (see `docs/CRITICAL_MEAN_SQUARE_LOWER.md`): exact weighted Parseval
(`CriticalMeanSquare.weighted_parseval`) → lower bound for `∫ |Δ|²` along the ray
`τ = −w + iκw` by unit blocks compared with horizontal periods (`Ray`, `RayBlock`) →
Stirling weight and dyadic tail control with the proven upper bound (`Weight`, `Tail`) →
bookkeeping (`Lower`).
-/
import RamanujanTau.CriticalMeanSquareLower.Lower

namespace RamanujanTau.CriticalMeanSquareLower

#print axioms critical_mean_square_lower
#print axioms critical_mean_square_order
#print axioms critical_mean_square_isTheta
#print axioms ray_lower
#print axioms exists_Hh_lower
#print axioms exists_Dc_lip
#print axioms exists_weight_bound
#print axioms lhs_le
#print axioms ioi_le

end RamanujanTau.CriticalMeanSquareLower
