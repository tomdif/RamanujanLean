/-
# Ramanujan's identity for the fifth power of the Rogers–Ramanujan continued fraction

With `R(q) = q^{1/5} (q;q⁵)_∞(q⁴;q⁵)_∞ / ((q²;q⁵)_∞(q³;q⁵)_∞)` (the continued fraction of `RRContinuedFraction`):

  `1/R(q)⁵ − 11 − R(q)⁵ = (q;q)_∞⁶ / (q (q⁵;q⁵)_∞⁶)`.

With `u = (q;q⁵)(q⁴;q⁵)`, `v = (q²;q⁵)(q³;q⁵)`, this says `(q⁵;q⁵)⁶ (v¹⁰ − 11q u⁵v⁵ − q² u¹⁰) = (q;q)⁶ u⁵ v⁵`.
It is the norm identity of the 5-dissection (`norm_identity`) together with Ramanujan's
`α = J_{5,2}/J_{5,1} = v/u` (`J5_relations`).
-/
import RamanujanTau.RamanujanMostBeautiful
import RamanujanTau.RankDissect

set_option autoImplicit false

namespace MockTheta5.JTP
open PowerSeries
open RankProof (Pinf)

/-- **Ramanujan's `R⁵` identity**: `(q⁵;q⁵)⁶ (v¹⁰ − 11q u⁵v⁵ − q² u¹⁰) = (q;q)⁶ u⁵ v⁵`, where
`u = (q;q⁵)_∞(q⁴;q⁵)_∞` and `v = (q²;q⁵)_∞(q³;q⁵)_∞`. Equivalently `1/R⁵ − 11 − R⁵ = (q;q)⁶/(q(q⁵;q⁵)⁶)`. -/
theorem ramanujan_R5 :
    eQ ^ 6 * ((Pinf 2 5 * Pinf 3 5) ^ 10 - 11 * X * (Pinf 1 5 * Pinf 4 5) ^ 5 * (Pinf 2 5 * Pinf 3 5) ^ 5
        - X ^ 2 * (Pinf 1 5 * Pinf 4 5) ^ 10)
      = qfacInf ^ 6 * (Pinf 1 5 * Pinf 4 5) ^ 5 * (Pinf 2 5 * Pinf 3 5) ^ 5 := by
  have hJ := CrankProof.J5_relations.2
  have hJ' := CrankProof.betaQ_eq
  simp only [CrankProof.Jab, show (5 : ℕ) - 2 = 3 from rfl, show (5 : ℕ) - 1 = 4 from rfl] at hJ hJ'
  have hP5 : IsUnit (Pinf 5 5) := by
    rw [RankProof.Pinf_aa 5 (by norm_num)]
    exact isUnit_qfacInf.map _
  -- `v = α u` and `u = β v`
  have hv : Pinf 2 5 * Pinf 3 5 = alphaQ * (Pinf 1 5 * Pinf 4 5) := by
    apply hP5.mul_right_cancel; linear_combination hJ
  have hu : Pinf 1 5 * Pinf 4 5 = betaQ * (Pinf 2 5 * Pinf 3 5) := by
    apply hP5.mul_right_cancel; linear_combination hJ'
  have hN := norm_identity
  set u := Pinf 1 5 * Pinf 4 5
  set v := Pinf 2 5 * Pinf 3 5
  rw [hv]
  have hab := alphaQ_mul_betaQ
  linear_combination u ^ 10 * alphaQ ^ 5 * hN
    + eQ ^ 6 * u ^ 10 * X ^ 2 * ((alphaQ * betaQ) ^ 4 + (alphaQ * betaQ) ^ 3 + (alphaQ * betaQ) ^ 2
      + alphaQ * betaQ + 1) * hab

end MockTheta5.JTP
