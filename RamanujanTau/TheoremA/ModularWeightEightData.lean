import RamanujanTau.TheoremA.EtaTruncation
import RamanujanTau.TheoremA.EvenWeightProducts

/-!
# Finite data for U₂ and U₃ on the full weight-eight space

The three integer series A,B,C are certified through q²⁴. Their normal
monomials provide the nine basis expansions. The displayed matrices and
their polynomial identity are finite integer certificates; their identification
with the actual analytic operators is proved in the next module.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace RamanujanTau.TheoremA
open PowerSeries RankProof EtaSquared Matrix

def weightTwoCoefficients24 (a : Fin 3) : List ℤ :=
  match a.val with
  | 0 => [1, 6, 15, 24, 33, 36, 33, 48, 69, 78, 90, 72, 51, 84, 120, 144, 141, 108, 87, 120, 198, 192, 180, 144, 87]
  | 1 => [0, 1, 2, 1, 4, 6, 2, 8, 8, 1, 12, 12, 4, 14, 16, 6, 16, 18, 2, 20, 24, 8, 24, 24, 8]
  | _ => [0, 0, 1, -2, 3, 0, -1, 0, 7, -8, 6, 0, 1, 0, 8, -12, 15, 0, -7, 0, 18, -16, 12, 0, 5]

theorem weightTwo_list_certificate24 (a : Fin 3) :
    let (d, k, e, r) := weightTwoDenominatorData a
    let (d', k', e', r') := weightTwoNumeratorData a
    truncList 24 (mulList (weightTwoCoefficients24 a) (etaProductListTo 24 0 d k e r)) =
      etaProductListTo 24 a.val d' k' e' r' := by
  revert a
  decide +kernel

theorem pi_weightTwoSeries24 (a : Fin 3) :
    FourSquares.π 25 (weightTwoSeries a) = FourSquares.π 25 (toPS (weightTwoCoefficients24 a)) := by
  have hc := congrArg (fun L => FourSquares.π 25 (toPS L)) (weightTwo_list_certificate24 a)
  change FourSquares.π 25 (toPS (truncList 24 (mulList (weightTwoCoefficients24 a)
    (etaProductListTo 24 0 (weightTwoDenominatorData a).1 (weightTwoDenominatorData a).2.1
      (weightTwoDenominatorData a).2.2.1 (weightTwoDenominatorData a).2.2.2)))) =
    FourSquares.π 25 (toPS (etaProductListTo 24 a.val (weightTwoNumeratorData a).1
      (weightTwoNumeratorData a).2.1 (weightTwoNumeratorData a).2.2.1
      (weightTwoNumeratorData a).2.2.2)) at hc
  rw [π_truncList, toPS_mulList, map_mul,
    pi_etaProductListTo 24 _ _ _ _ _ (weightTwo_data_pos a).2.2.1 (weightTwo_data_pos a).2.2.2,
    pi_etaProductListTo 24 _ _ _ _ _ (weightTwo_data_pos a).1 (weightTwo_data_pos a).2.1] at hc
  apply ((weightTwoDenominator_isUnit a).map (FourSquares.π 25)).mul_right_cancel
  rw [← map_mul, weightTwoSeries_mul]
  exact hc.symm

def modularWeightEightCoefficients (i : Fin 9) : List ℤ :=
  truncList 24 (mulList
    (mulList (truncPowList 24 (weightTwoCoefficients24 0) (normalExponentA 4 i.val))
      (truncPowList 24 (weightTwoCoefficients24 1) (normalExponentB i.val)))
    (truncPowList 24 (weightTwoCoefficients24 2) (normalExponentC i.val)))

theorem pi_modularWeightEightCoefficients (i : Fin 9) :
    FourSquares.π 25 (toPS (modularWeightEightCoefficients i)) =
      FourSquares.π 25 (evenSeries 4 i.val) := by
  rw [modularWeightEightCoefficients, π_truncList, toPS_mulList, toPS_mulList, map_mul, map_mul,
    π_truncPow, π_truncPow, π_truncPow,
    ← pi_weightTwoSeries24, ← pi_weightTwoSeries24, ← pi_weightTwoSeries24,
    evenSeries_normalForm 4 i.val (by omega), map_mul, map_mul, map_pow, map_pow, map_pow]

theorem modularWeightEightSeries_coeff (i : Fin 9) {j : ℕ} (hj : j < 25) :
    (evenSeries 4 i.val).coeff j = coeffList (modularWeightEightCoefficients i) j := by
  simpa only [toPS, coeff_mk] using
    (FourSquares.coeff_eq_of_dvd (FourSquares.π_eq_iff.mp
      (pi_modularWeightEightCoefficients i)) hj).symm

def modularWeightEightU2 : Matrix (Fin 9) (Fin 9) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    252, 20, 1, 0, 0, 0, 0, 0, 0;
    5670, 756, 100, 12, 1, 0, 0, 0, 0;
    20412, 2268, 270, 44, 12, 4, 1, 0, 0;
    6561, -2916, -972, -252, -74, -28, -12, -4, 1;
    0, 0, 729, 324, 108, 44, 30, 28, 28;
    0, 0, 0, 0, 81, 108, 100, 84, 70;
    0, 0, 0, 0, 0, 0, 9, 20, 28;
    0, 0, 0, 0, 0, 0, 0, 0, 1]

theorem modularWeightEightU2_certificate (i j : Fin 9) :
    coeffList (modularWeightEightCoefficients i) (2 * j.val) =
      ∑ t : Fin 9, modularWeightEightU2 t i * coeffList (modularWeightEightCoefficients t) j.val := by
  revert i j
  decide +kernel

def modularWeightEightU3 : Matrix (Fin 9) (Fin 9) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    2016, 190, 16, 1, 0, 0, 0, 0, 0;
    120456, 14364, 1740, 216, 28, 4, 1, 0, 0;
    542376, 51300, 4320, 270, 0, -3, 0, 10, -8;
    -1885194, -184680, -15552, -972, -27, 0, 0, -36, 306;
    944784, 138510, 11664, 486, 0, 0, 0, 27, -2160;
    1338444, 0, -2187, 0, 0, 0, 0, 0, 5508;
    -1417176, -19683, 0, 0, 0, 0, 0, 0, -5832;
    354294, 0, 0, 0, 0, 0, 0, 0, 2187]

theorem modularWeightEightU3_certificate (i j : Fin 9) :
    coeffList (modularWeightEightCoefficients i) (3 * j.val) =
      ∑ t : Fin 9, modularWeightEightU3 t i * coeffList (modularWeightEightCoefficients t) j.val := by
  revert i j
  decide +kernel

/-- The vector of the newform `6.8.a.a` in the normal basis. -/
def modularWeightEightH : Fin 9 → ℤ := ![0, 1, -12, 29, 0, -261, 972, -729, 0]

/-- The functional in the rank-one relation. -/
def modularWeightEightV : Fin 9 → ℤ := ![-8817984, -428652, 0, 2268, 0, -252, 0, 588, 1344]

/-- The polynomial that kills every other eigensystem has rank one. -/
theorem modularWeightEight_matrix_identity :
    (modularWeightEightU2 - 1) * (modularWeightEightU2 - 128) * (modularWeightEightU2 + 8) *
      (modularWeightEightU3 + 27) = Matrix.vecMulVec modularWeightEightH modularWeightEightV := by
  decide +kernel

end RamanujanTau.TheoremA
