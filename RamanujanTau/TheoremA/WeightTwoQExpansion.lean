import RamanujanTau.TheoremA.WeightTwoForms
import RamanujanTau.TheoremA.EtaQExpansion

/-! Integral q-expansions and finite coefficient certificates for A, B, C. -/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.EtaSquared
open ModularForm Realize PowerSeries RankProof
open UpperHalfPlane hiding I
open Complex hiding eta
open scoped Real
local notation "𝕢" => Function.Periodic.qParam

theorem quotientFunction_qProduct (r : Fin 4 → ℤ) (s : ℕ)
    (hs : ∑ j : Fin 4, (dilation j : ℤ) * r j = 12 * (s : ℤ)) (z : ℍ) :
    quotientFunction r z = 𝕢 1 z ^ s *
      ∏ j : Fin 4, Pfun (dilation j) (dilation j) (𝕢 1 z) ^ (2 * r j) := by
  simp only [quotientFunction, scaledEta_qProduct, mul_zpow, Finset.prod_mul_distrib]
  congr 1
  · simp_rw [← Complex.exp_int_mul]
    rw [← Complex.exp_sum]
    simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
    rw [← Complex.exp_nat_mul]
    congr 1
    have hs' : (∑ j : Fin 4, (dilation j : ℂ) * r j) = 12 * s := by exact_mod_cast hs
    calc
      _ = (π * I * z / 6) * ∑ j : Fin 4, (dilation j : ℂ) * r j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hs']; ring
  · apply Finset.prod_congr rfl
    intro j _
    rw [← zpow_natCast, ← zpow_mul]
    norm_num

theorem weightTwo_weighted_exponent (a : Fin 3) :
    ∑ j : Fin 4, (dilation j : ℤ) * weightTwoExponent a j = 12 * (a.val : ℤ) := by
  revert a
  decide +kernel

def weightTwoNumeratorData (a : Fin 3) : ℕ × ℕ × ℕ × ℕ :=
  match a.val with | 0 => (2, 12, 3, 2) | 1 => (2, 4, 6, 4) | _ => (1, 2, 6, 12)

def weightTwoDenominatorData (a : Fin 3) : ℕ × ℕ × ℕ × ℕ :=
  match a.val with | 0 => (1, 6, 6, 4) | 1 => (1, 2, 3, 2) | _ => (2, 4, 3, 6)

theorem weightTwo_data_pos (a : Fin 3) :
    0 < (weightTwoNumeratorData a).1 ∧ 0 < (weightTwoNumeratorData a).2.2.1 ∧
    0 < (weightTwoDenominatorData a).1 ∧ 0 < (weightTwoDenominatorData a).2.2.1 := by
  revert a
  decide +kernel

noncomputable def weightTwoNumerator (a : Fin 3) : PowerSeries ℤ :=
  let (d, k, e, r) := weightTwoNumeratorData a
  etaProductSeries a.val d k e r

noncomputable def weightTwoDenominator (a : Fin 3) : PowerSeries ℤ :=
  let (d, k, e, r) := weightTwoDenominatorData a
  etaProductSeries 0 d k e r

noncomputable def weightTwoSeries (a : Fin 3) : PowerSeries ℤ :=
  weightTwoNumerator a * Ring.inverse (weightTwoDenominator a)

noncomputable def weightTwoNumeratorFunction (a : Fin 3) : ℂ → ℂ :=
  let (d, k, e, r) := weightTwoNumeratorData a
  etaProductFunction a.val d k e r

noncomputable def weightTwoDenominatorFunction (a : Fin 3) : ℂ → ℂ :=
  let (d, k, e, r) := weightTwoDenominatorData a
  etaProductFunction 0 d k e r

theorem weightTwoNumerator_realizes (a : Fin 3) :
    Realizes (weightTwoNumeratorFunction a) (weightTwoNumerator a) :=
  etaProduct_realizes _ _ _ _ _ (weightTwo_data_pos a).1 (weightTwo_data_pos a).2.1

theorem weightTwoDenominator_realizes (a : Fin 3) :
    Realizes (weightTwoDenominatorFunction a) (weightTwoDenominator a) :=
  etaProduct_realizes _ _ _ _ _ (weightTwo_data_pos a).2.2.1 (weightTwo_data_pos a).2.2.2

theorem weightTwoDenominator_isUnit (a : Fin 3) : IsUnit (weightTwoDenominator a) := by
  simp only [weightTwoDenominator, etaProductSeries, pow_zero, one_mul]
  exact ((isUnit_Pinf _ _ (weightTwo_data_pos a).2.2.1
    (weightTwo_data_pos a).2.2.1).pow _).mul
    ((isUnit_Pinf _ _ (weightTwo_data_pos a).2.2.2 (weightTwo_data_pos a).2.2.2).pow _)

theorem weightTwoSeries_mul (a : Fin 3) :
    weightTwoSeries a * weightTwoDenominator a = weightTwoNumerator a := by
  rw [weightTwoSeries, mul_assoc, Ring.inverse_mul_cancel _ (weightTwoDenominator_isUnit a),
    mul_one]

theorem weightTwo_qProduct_relation (a : Fin 3) (z : ℍ) :
    weightTwoForm a z * weightTwoDenominatorFunction a (𝕢 1 z) =
      weightTwoNumeratorFunction a (𝕢 1 z) := by
  rw [weightTwoForm_apply, quotientFunction_qProduct _ a.val (weightTwo_weighted_exponent a)]
  fin_cases a <;>
    norm_num [Fin.prod_univ_succ, dilation, weightTwoExponent,
      weightTwoNumeratorFunction, weightTwoDenominatorFunction,
      weightTwoNumeratorData, weightTwoDenominatorData, etaProductFunction] <;>
    field_simp [Pfun_qParam_ne_zero 1 (by decide) z,
      Pfun_qParam_ne_zero 2 (by decide) z, Pfun_qParam_ne_zero 3 (by decide) z,
      Pfun_qParam_ne_zero 6 (by decide) z]

theorem qExpansion_weightTwo_relation (a : Fin 3) :
    qExpansion 1 (weightTwoForm a) * PowerSeries.map (Int.castRingHom ℂ) (weightTwoDenominator a) =
      PowerSeries.map (Int.castRingHom ℂ) (weightTwoNumerator a) := by
  have hf : (weightTwoForm a : ℍ → ℂ) * qLift (weightTwoDenominatorFunction a) =
      qLift (weightTwoNumeratorFunction a) := funext (weightTwo_qProduct_relation a)
  have ha := ModularFormClass.analyticAt_cuspFunction_zero (weightTwoForm a)
    (one_pos : (0 : ℝ) < 1) (by simp [CongruenceSubgroup.strictPeriods_Gamma0])
  have hq := congrArg (qExpansion 1) hf
  rw [qExpansion_mul ha (qLift_analytic (weightTwoDenominator_realizes a)),
    qExpansion_qLift (weightTwoDenominator_realizes a),
    qExpansion_qLift (weightTwoNumerator_realizes a)] at hq
  exact hq

/-- All Fourier coefficients of the actual weight-two forms are integers. -/
theorem qExpansion_weightTwo (a : Fin 3) : qExpansion 1 (weightTwoForm a) =
    PowerSeries.map (Int.castRingHom ℂ) (weightTwoSeries a) := by
  apply ((weightTwoDenominator_isUnit a).map (PowerSeries.map (Int.castRingHom ℂ))).mul_right_cancel
  rw [qExpansion_weightTwo_relation, ← map_mul, weightTwoSeries_mul]

/-- The conic relation also holds over the integers, before reduction at any prime. -/
theorem weightTwoSeries_relation :
    weightTwoSeries 0 * weightTwoSeries 2 = weightTwoSeries 1 ^ 2 := by
  apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
  rw [map_mul, map_pow, ← qExpansion_weightTwo, ← qExpansion_weightTwo,
    ← qExpansion_weightTwo, pow_two]
  have ha (a : Fin 3) := ModularFormClass.analyticAt_cuspFunction_zero (weightTwoForm a)
    (one_pos : (0 : ℝ) < 1) (by simp [CongruenceSubgroup.strictPeriods_Gamma0])
  rw [← qExpansion_mul (ha 0) (ha 2), ← qExpansion_mul (ha 1) (ha 1)]
  congr 1
  ext z
  exact (weightTwoForm_relation z).trans (pow_two _)

def weightTwoCoefficients (a : Fin 3) : List ℤ :=
  match a.val with
  | 0 => [1, 6, 15, 24, 33, 36, 33, 48, 69, 78]
  | 1 => [0, 1, 2, 1, 4, 6, 2, 8, 8, 1]
  | _ => [0, 0, 1, -2, 3, 0, -1, 0, 7, -8]

theorem weightTwo_list_certificate (a : Fin 3) :
    let (d, k, e, r) := weightTwoDenominatorData a
    let (d', k', e', r') := weightTwoNumeratorData a
    truncList 9 (mulList (weightTwoCoefficients a) (etaProductList 0 d k e r)) =
      etaProductList a.val d' k' e' r' := by
  revert a
  decide +kernel

theorem pi_weightTwoSeries (a : Fin 3) :
    FourSquares.π 10 (weightTwoSeries a) = FourSquares.π 10 (toPS (weightTwoCoefficients a)) := by
  have hc := congrArg (fun L => FourSquares.π 10 (toPS L)) (weightTwo_list_certificate a)
  change FourSquares.π 10 (toPS (truncList 9 (mulList (weightTwoCoefficients a)
    (etaProductList 0 (weightTwoDenominatorData a).1 (weightTwoDenominatorData a).2.1
      (weightTwoDenominatorData a).2.2.1 (weightTwoDenominatorData a).2.2.2)))) =
    FourSquares.π 10 (toPS (etaProductList a.val (weightTwoNumeratorData a).1
      (weightTwoNumeratorData a).2.1 (weightTwoNumeratorData a).2.2.1
      (weightTwoNumeratorData a).2.2.2)) at hc
  rw [π_truncList, toPS_mulList, map_mul,
    pi_etaProductList _ _ _ _ _ (weightTwo_data_pos a).2.2.1 (weightTwo_data_pos a).2.2.2,
    pi_etaProductList _ _ _ _ _ (weightTwo_data_pos a).1 (weightTwo_data_pos a).2.1] at hc
  apply ((weightTwoDenominator_isUnit a).map (FourSquares.π 10)).mul_right_cancel
  rw [← map_mul, weightTwoSeries_mul]
  exact hc.symm

theorem weightTwoSeries_coeff (a : Fin 3) {n : ℕ} (hn : n < 10) :
    (weightTwoSeries a).coeff n = coeffList (weightTwoCoefficients a) n := by
  simpa only [toPS, coeff_mk] using
    FourSquares.coeff_eq_of_dvd (FourSquares.π_eq_iff.mp (pi_weightTwoSeries a)) hn

theorem weightTwo_coeff (a : Fin 3) {n : ℕ} (hn : n < 10) :
    (qExpansion 1 (weightTwoForm a)).coeff n = (coeffList (weightTwoCoefficients a) n : ℂ) := by
  rw [qExpansion_weightTwo, coeff_map, weightTwoSeries_coeff a hn]
  rfl

end RamanujanTau.TheoremA.EtaSquared
