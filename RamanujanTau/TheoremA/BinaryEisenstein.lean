import RamanujanTau.TheoremA.BinaryModel

/-!
# The level-one Eisenstein series in the level-six binary model

Finite integer coefficient certificates identify E₄ and E₆ using the proved
level-six coefficient bound. The resulting identities hold for the complete
power series over every commutative ring.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open MvPolynomial ModularForm CongruenceSubgroup UpperHalfPlane
open EtaSquared RankProof
open PowerSeries hiding X
open scoped MatrixGroups ModularForm

namespace LevelSix

/-- Restriction of an actual level-one modular form to level six. -/
noncomputable def restrictLevelOne {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k where
  toFun := f
  slash_action_eq' := by
    rintro _ ⟨γ, _, rfl⟩
    exact SlashInvariantFormClass.slash_action_eq f _ ⟨γ, rfl⟩
  holo' := ModularFormClass.holo f
  bdd_at_cusps' h := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at h
    exact ModularFormClass.bdd_at_cusps f h

@[simp] theorem qExpansion_restrictLevelOne {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    qExpansion 1 (restrictLevelOne f) = qExpansion 1 f := rfl

end LevelSix

/-- A computable truncation of each normal monomial, through degree nine. -/
def evenCoefficients (n i : ℕ) : List ℤ :=
  truncList 9 (mulList
    (mulList (truncPowList 9 (weightTwoCoefficients 0) (normalExponentA n i))
      (truncPowList 9 (weightTwoCoefficients 1) (normalExponentB i)))
    (truncPowList 9 (weightTwoCoefficients 2) (normalExponentC i)))

theorem pi_evenCoefficients (n i : ℕ) (hi : i ≤ 2 * n) :
    FourSquares.π 10 (toPS (evenCoefficients n i)) = FourSquares.π 10 (evenSeries n i) := by
  rw [evenCoefficients, π_truncList, toPS_mulList, toPS_mulList, map_mul, map_mul,
    π_truncPow, π_truncPow, π_truncPow,
    ← pi_weightTwoSeries, ← pi_weightTwoSeries, ← pi_weightTwoSeries,
    evenSeries_normalForm n i hi, map_mul, map_mul, map_pow, map_pow, map_pow]

theorem evenSeries_coeff_of_lt_ten (n i j : ℕ) (hi : i ≤ 2 * n) (hj : j < 10) :
    (evenSeries n i).coeff j = coeffList (evenCoefficients n i) j := by
  simpa only [toPS, coeff_mk] using
    (FourSquares.coeff_eq_of_dvd (FourSquares.π_eq_iff.mp
      (pi_evenCoefficients n i hi)) hj).symm

def binaryE4Coordinates : Fin 5 → ℤ := ![1, 228, 270, -972, 729]
def binaryE6Coordinates : Fin 7 → ℤ := ![1, -522, -9477, 18468, -24057, 39366, -19683]

theorem binaryE4_certificate (j : Fin 5) :
    (∑ i : Fin 5, binaryE4Coordinates i * coeffList (evenCoefficients 2 i.val) j.val) =
      if j.val = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 j.val : ℤ) := by
  revert j
  decide +kernel

theorem binaryE6_certificate (j : Fin 7) :
    (∑ i : Fin 7, binaryE6Coordinates i * coeffList (evenCoefficients 3 i.val) j.val) =
      if j.val = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 j.val : ℤ) := by
  revert j
  decide +kernel

theorem evenCombination_E4_coeff (j : Fin 5) :
    (evenCombination 2 binaryE4Coordinates).coeff j.val = Mod691.p4.coeff j.val := by
  simp only [evenCombination, map_sum, PowerSeries.coeff_smul, PowerSeries.coeff_map, Int.coe_castRingHom,
    Int.cast_id, smul_eq_mul]
  have hc (i : Fin 5) := evenSeries_coeff_of_lt_ten 2 i.val j.val (by omega) (by omega)
  simp_rw [hc]
  rw [Mod691.coeff_p4]
  exact binaryE4_certificate j

theorem evenCombination_E6_coeff (j : Fin 7) :
    (evenCombination 3 binaryE6Coordinates).coeff j.val = Mod691.p6.coeff j.val := by
  simp only [evenCombination, map_sum, PowerSeries.coeff_smul, PowerSeries.coeff_map, Int.coe_castRingHom,
    Int.cast_id, smul_eq_mul]
  have hc (i : Fin 7) := evenSeries_coeff_of_lt_ten 3 i.val j.val (by omega) (by omega)
  simp_rw [hc]
  rw [Mod691.coeff_p6]
  exact binaryE6_certificate j

theorem evenFormCombination_E4 :
    evenFormCombination 2 (fun i => (Int.castRingHom ℂ) (binaryE4Coordinates i)) =
      LevelSix.restrictLevelOne E₄ := by
  apply LevelSix.firstCoefficients_injective 4
  ext j
  change (qExpansion 1 (evenFormCombination 2 _)).coeff j.val =
    (qExpansion 1 (LevelSix.restrictLevelOne E₄)).coeff j.val
  rw [qExpansion_evenFormCombination, ← evenCombination_map (Int.castRingHom ℂ),
    PowerSeries.coeff_map, evenCombination_E4_coeff, LevelSix.qExpansion_restrictLevelOne,
    Mod691.qExpansion_E4_eq, PowerSeries.coeff_map]

theorem evenFormCombination_E6 :
    evenFormCombination 3 (fun i => (Int.castRingHom ℂ) (binaryE6Coordinates i)) =
      LevelSix.restrictLevelOne E₆ := by
  apply LevelSix.firstCoefficients_injective 6
  ext j
  change (qExpansion 1 (evenFormCombination 3 _)).coeff j.val =
    (qExpansion 1 (LevelSix.restrictLevelOne E₆)).coeff j.val
  rw [qExpansion_evenFormCombination, ← evenCombination_map (Int.castRingHom ℂ),
    PowerSeries.coeff_map, evenCombination_E6_coeff, LevelSix.qExpansion_restrictLevelOne,
    Mod691.qExpansion_E6_eq, PowerSeries.coeff_map]

theorem evenCombination_E4_int : evenCombination 2 binaryE4Coordinates = Mod691.p4 := by
  apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
  rw [evenCombination_map, ← qExpansion_evenFormCombination, evenFormCombination_E4,
    LevelSix.qExpansion_restrictLevelOne, Mod691.qExpansion_E4_eq]

theorem evenCombination_E6_int : evenCombination 3 binaryE6Coordinates = Mod691.p6 := by
  apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
  rw [evenCombination_map, ← qExpansion_evenFormCombination, evenFormCombination_E6,
    LevelSix.qExpansion_restrictLevelOne, Mod691.qExpansion_E6_eq]

noncomputable def binaryE4 (R : Type*) [CommRing R] : MvPolynomial (Fin 2) R :=
  binaryPolynomial 2 (fun i => (Int.castRingHom R) (binaryE4Coordinates i))

noncomputable def binaryE6 (R : Type*) [CommRing R] : MvPolynomial (Fin 2) R :=
  binaryPolynomial 3 (fun i => (Int.castRingHom R) (binaryE6Coordinates i))

theorem binaryE4_homogeneous (R : Type*) [CommRing R] : BinaryHomogeneous (binaryE4 R) 4 :=
  binaryPolynomial_homogeneous _ _

theorem binaryE6_homogeneous (R : Type*) [CommRing R] : BinaryHomogeneous (binaryE6 R) 6 :=
  binaryPolynomial_homogeneous _ _

theorem binaryEv_E4 (R : Type*) [CommRing R] : binaryEv R (binaryE4 R) = ModP.E4 R := by
  rw [binaryE4, binaryEv_binaryPolynomial, ← evenCombination_map (Int.castRingHom R),
    evenCombination_E4_int]
  rfl

theorem binaryEv_E6 (R : Type*) [CommRing R] : binaryEv R (binaryE6 R) = ModP.E6 R := by
  rw [binaryE6, binaryEv_binaryPolynomial, ← evenCombination_map (Int.castRingHom R),
    evenCombination_E6_int]
  rfl

theorem binaryE4_eq (R : Type*) [CommRing R] :
    binaryE4 R = X 0 ^ 4 + 228 * X 0 ^ 3 * X 1 + 270 * X 0 ^ 2 * X 1 ^ 2 -
      972 * X 0 * X 1 ^ 3 + 729 * X 1 ^ 4 := by
  simp only [binaryE4, binaryPolynomial, ModP.monomial_eq_two,
    binaryExponent_zero, binaryExponent_one]
  norm_num [Fin.sum_univ_succ, binaryE4Coordinates]
  ring

theorem binaryE6_eq (R : Type*) [CommRing R] :
    binaryE6 R = X 0 ^ 6 - 522 * X 0 ^ 5 * X 1 - 9477 * X 0 ^ 4 * X 1 ^ 2 +
      18468 * X 0 ^ 3 * X 1 ^ 3 - 24057 * X 0 ^ 2 * X 1 ^ 4 +
      39366 * X 0 * X 1 ^ 5 - 19683 * X 1 ^ 6 := by
  simp only [binaryE6, binaryPolynomial, ModP.monomial_eq_two,
    binaryExponent_zero, binaryExponent_one]
  norm_num [Fin.sum_univ_succ, binaryE6Coordinates]
  ring

/-- The discriminant has precisely the four level-six cusp factors. -/
theorem binaryEisenstein_discriminant (R : Type*) [CommRing R] :
    binaryE4 R ^ 3 - binaryE6 R ^ 2 =
      1728 * X 0 ^ 3 * X 1 * (X 0 - X 1) ^ 2 * (X 0 - 9 * X 1) ^ 6 := by
  rw [binaryE4_eq, binaryE6_eq]
  ring

end RamanujanTau.TheoremA
