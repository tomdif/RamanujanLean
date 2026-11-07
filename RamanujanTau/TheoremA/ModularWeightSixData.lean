import RamanujanTau.TheoremA.EtaTruncation
import RamanujanTau.TheoremA.EvenWeightProducts

/-!
# Finite data for U₂ and U₃ on the full weight-six space

The three integer series A,B,C are certified through q¹⁸. Their normal
monomials provide the seven basis expansions. The displayed matrices and
their polynomial identity are finite integer certificates; their identification
with the actual analytic operators is proved in the next module.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open PowerSeries RankProof EtaSquared Matrix

def weightTwoCoefficients18 (a : Fin 3) : List ℤ :=
  match a.val with
  | 0 => [1, 6, 15, 24, 33, 36, 33, 48, 69, 78, 90, 72, 51, 84, 120, 144, 141, 108, 87]
  | 1 => [0, 1, 2, 1, 4, 6, 2, 8, 8, 1, 12, 12, 4, 14, 16, 6, 16, 18, 2]
  | _ => [0, 0, 1, -2, 3, 0, -1, 0, 7, -8, 6, 0, 1, 0, 8, -12, 15, 0, -7]

theorem weightTwo_list_certificate18 (a : Fin 3) :
    let (d, k, e, r) := weightTwoDenominatorData a
    let (d', k', e', r') := weightTwoNumeratorData a
    truncList 18 (mulList (weightTwoCoefficients18 a) (etaProductListTo 18 0 d k e r)) =
      etaProductListTo 18 a.val d' k' e' r' := by
  revert a
  decide +kernel

theorem pi_weightTwoSeries18 (a : Fin 3) :
    FourSquares.π 19 (weightTwoSeries a) = FourSquares.π 19 (toPS (weightTwoCoefficients18 a)) := by
  have hc := congrArg (fun L => FourSquares.π 19 (toPS L)) (weightTwo_list_certificate18 a)
  change FourSquares.π 19 (toPS (truncList 18 (mulList (weightTwoCoefficients18 a)
    (etaProductListTo 18 0 (weightTwoDenominatorData a).1 (weightTwoDenominatorData a).2.1
      (weightTwoDenominatorData a).2.2.1 (weightTwoDenominatorData a).2.2.2)))) =
    FourSquares.π 19 (toPS (etaProductListTo 18 a.val (weightTwoNumeratorData a).1
      (weightTwoNumeratorData a).2.1 (weightTwoNumeratorData a).2.2.1
      (weightTwoNumeratorData a).2.2.2)) at hc
  rw [π_truncList, toPS_mulList, map_mul,
    pi_etaProductListTo 18 _ _ _ _ _ (weightTwo_data_pos a).2.2.1 (weightTwo_data_pos a).2.2.2,
    pi_etaProductListTo 18 _ _ _ _ _ (weightTwo_data_pos a).1 (weightTwo_data_pos a).2.1] at hc
  apply ((weightTwoDenominator_isUnit a).map (FourSquares.π 19)).mul_right_cancel
  rw [← map_mul, weightTwoSeries_mul]
  exact hc.symm

def modularWeightSixCoefficients (i : Fin 7) : List ℤ :=
  truncList 18 (mulList
    (mulList (truncPowList 18 (weightTwoCoefficients18 0) (normalExponentA 3 i.val))
      (truncPowList 18 (weightTwoCoefficients18 1) (normalExponentB i.val)))
    (truncPowList 18 (weightTwoCoefficients18 2) (normalExponentC i.val)))

theorem pi_modularWeightSixCoefficients (i : Fin 7) :
    FourSquares.π 19 (toPS (modularWeightSixCoefficients i)) =
      FourSquares.π 19 (evenSeries 3 i.val) := by
  rw [modularWeightSixCoefficients, π_truncList, toPS_mulList, toPS_mulList, map_mul, map_mul,
    π_truncPow, π_truncPow, π_truncPow,
    ← pi_weightTwoSeries18, ← pi_weightTwoSeries18, ← pi_weightTwoSeries18,
    evenSeries_normalForm 3 i.val (by omega), map_mul, map_mul, map_pow, map_pow, map_pow]

theorem modularWeightSixSeries_coeff (i : Fin 7) {j : ℕ} (hj : j < 19) :
    (evenSeries 3 i.val).coeff j = coeffList (modularWeightSixCoefficients i) j := by
  simpa only [toPS, coeff_mk] using
    (FourSquares.coeff_eq_of_dvd (FourSquares.π_eq_iff.mp
      (pi_modularWeightSixCoefficients i)) hj).symm

def modularWeightSixU2 : Matrix (Fin 7) (Fin 7) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0;
    135, 14, 1, 0, 0, 0, 0;
    1215, 180, 31, 6, 1, 0, 0;
    729, -162, -81, -28, -9, -2, 1;
    0, 0, 81, 54, 31, 20, 15;
    0, 0, 0, 0, 9, 14, 15;
    0, 0, 0, 0, 0, 0, 1]

theorem modularWeightSixU2_certificate (i j : Fin 7) :
    coeffList (modularWeightSixCoefficients i) (2 * j.val) =
      ∑ t : Fin 7, modularWeightSixU2 t i * coeffList (modularWeightSixCoefficients t) j.val := by
  revert i j
  decide +kernel

def modularWeightSixU3 : Matrix (Fin 7) (Fin 7) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0;
    810, 91, 10, 1, 0, 0, 0;
    14499, 1638, 180, 18, 1, -2, 1;
    -17496, -2457, -270, -18, 0, 3, -54;
    -24057, 0, 81, 0, 0, 0, 297;
    39366, 729, 0, 0, 0, 0, -486;
    -13122, 0, 0, 0, 0, 0, 243]

theorem modularWeightSixU3_certificate (i j : Fin 7) :
    coeffList (modularWeightSixCoefficients i) (3 * j.val) =
      ∑ t : Fin 7, modularWeightSixU3 t i * coeffList (modularWeightSixCoefficients t) j.val := by
  revert i j
  decide +kernel

theorem modularWeightSix_matrix_identity :
    (modularWeightSixU2 - 1) * (modularWeightSixU2 - 32) * (modularWeightSixU3 + 9) *
      (modularWeightSixU2 ^ 2 + 6 * modularWeightSixU2 + 32) = 0 := by
  decide +kernel

end RamanujanTau.TheoremA
