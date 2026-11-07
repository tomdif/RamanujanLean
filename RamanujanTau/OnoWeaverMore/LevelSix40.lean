import RamanujanTau.TheoremA.EtaTruncation
import RamanujanTau.TheoremA.EvenWeightProducts

/-!
# Level-six basis expansions through `q⁴⁰`

Copy of `AtkinSporadic.LevelSixPrecision` at precision 40 (needed for weights 26 and 28).

The three weight-two series `A, B, C` of `TheoremA` are certified through `q⁴⁰` by the same
eta-product list certificate as `TheoremA.ModularWeightSixData` (there through `q¹⁸`; `AtkinSporadic.LevelSixPrecision` through `q²⁸`). The basis
`evenSeries n i = A^a B^b C^c` of every even weight `2n` then has computable coefficients through
`q⁴⁰` (`evenSeries_coeff40`).
-/

set_option autoImplicit false

namespace RamanujanTau.OnoWeaverMore.LevelSix40
open PowerSeries RankProof RamanujanTau.TheoremA RamanujanTau.TheoremA.EtaSquared

def w2c (a : Fin 3) : List ℤ :=
  match a.val with
  | 0 => [1, 6, 15, 24, 33, 36, 33, 48, 69, 78, 90, 72, 51, 84, 120, 144, 141, 108, 87, 120, 198, 192, 180, 144, 87, 186, 210, 240, 264, 180, 198, 192, 285, 288, 270, 288, 105, 228, 300, 336, 414]
  | 1 => [0, 1, 2, 1, 4, 6, 2, 8, 8, 1, 12, 12, 4, 14, 16, 6, 16, 18, 2, 20, 24, 8, 24, 24, 8, 31, 28, 1, 32, 30, 12, 32, 32, 12, 36, 48, 4, 38, 40, 14, 48]
  | _ => [0, 0, 1, -2, 3, 0, -1, 0, 7, -8, 6, 0, 1, 0, 8, -12, 15, 0, -7, 0, 18, -16, 12, 0, 5, 0, 14, -26, 24, 0, -6, 0, 31, -24, 18, 0, -5, 0, 20, -28, 42]

theorem w2c_certificate (a : Fin 3) :
    let (d, k, e, r) := weightTwoDenominatorData a
    let (d', k', e', r') := weightTwoNumeratorData a
    truncList 40 (mulList (w2c a) (etaProductListTo 40 0 d k e r)) =
      etaProductListTo 40 a.val d' k' e' r' := by
  revert a
  decide +kernel

theorem pi_weightTwoSeries40 (a : Fin 3) :
    FourSquares.π 41 (weightTwoSeries a) = FourSquares.π 41 (toPS (w2c a)) := by
  have hc := congrArg (fun L => FourSquares.π 41 (toPS L)) (w2c_certificate a)
  change FourSquares.π 41 (toPS (truncList 40 (mulList (w2c a)
    (etaProductListTo 40 0 (weightTwoDenominatorData a).1 (weightTwoDenominatorData a).2.1
      (weightTwoDenominatorData a).2.2.1 (weightTwoDenominatorData a).2.2.2)))) =
    FourSquares.π 41 (toPS (etaProductListTo 40 a.val (weightTwoNumeratorData a).1
      (weightTwoNumeratorData a).2.1 (weightTwoNumeratorData a).2.2.1
      (weightTwoNumeratorData a).2.2.2)) at hc
  rw [π_truncList, toPS_mulList, map_mul,
    pi_etaProductListTo 40 _ _ _ _ _ (weightTwo_data_pos a).2.2.1 (weightTwo_data_pos a).2.2.2,
    pi_etaProductListTo 40 _ _ _ _ _ (weightTwo_data_pos a).1 (weightTwo_data_pos a).2.1] at hc
  apply ((weightTwoDenominator_isUnit a).map (FourSquares.π 41)).mul_right_cancel
  rw [← map_mul, weightTwoSeries_mul]
  exact hc.symm

/-- The basis element `evenSeries n i` through `q⁴⁰`, as a list. -/
def basisL (n i : ℕ) : List ℤ :=
  truncList 40 (mulList
    (mulList (truncPowList 40 (w2c 0) (normalExponentA n i))
      (truncPowList 40 (w2c 1) (normalExponentB i)))
    (truncPowList 40 (w2c 2) (normalExponentC i)))

theorem pi_basisL (n i : ℕ) (hi : i ≤ 2 * n) :
    FourSquares.π 41 (toPS (basisL n i)) = FourSquares.π 41 (evenSeries n i) := by
  rw [basisL, π_truncList, toPS_mulList, toPS_mulList, map_mul, map_mul,
    π_truncPow, π_truncPow, π_truncPow,
    ← pi_weightTwoSeries40, ← pi_weightTwoSeries40, ← pi_weightTwoSeries40,
    evenSeries_normalForm n i hi, map_mul, map_mul, map_pow, map_pow, map_pow]

theorem evenSeries_coeff40 (n i : ℕ) (hi : i ≤ 2 * n) {j : ℕ} (hj : j < 41) :
    (evenSeries n i).coeff j = coeffList (basisL n i) j := by
  simpa only [toPS, coeff_mk] using
    (FourSquares.coeff_eq_of_dvd (FourSquares.π_eq_iff.mp (pi_basisL n i hi)) hj).symm

end RamanujanTau.OnoWeaverMore.LevelSix40
