import RamanujanTau.TheoremA.EvenWeightCoordinates

/-!
# Multiplication and polynomial normal forms at level six

The eta basis multiplies by adding both indices. Every basis element is a
monomial A^a B^b C^c with b < 2, and a+b+c equal to the half-weight. Together
with integral coordinates this proves generation and unique homogeneous
normal forms over every coefficient ring.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open ModularForm CongruenceSubgroup PowerSeries
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm
open EtaSquared

theorem evenSeries_mul (n m i j : ℕ) (hi : i ≤ 2 * n) (hj : j ≤ 2 * m) :
    evenSeries n i * evenSeries m j = evenSeries (n + m) (i + j) := by
  let a : Fin (2 * n + 1) := ⟨i, by omega⟩
  let b : Fin (2 * m + 1) := ⟨j, by omega⟩
  let c : Fin (2 * (n + m) + 1) := ⟨i + j, by omega⟩
  have hf : (evenForm n a : ℍ → ℂ) * (evenForm m b : ℍ → ℂ) = evenForm (n + m) c := by
    ext z
    simp only [Pi.mul_apply, evenForm_apply, a, b, c, evenExponent_add, quotientFunction_add]
  have ha := ModularFormClass.analyticAt_cuspFunction_zero (evenForm n a)
    (one_pos : (0 : ℝ) < 1) LevelSix.infinity_period
  have hb := ModularFormClass.analyticAt_cuspFunction_zero (evenForm m b)
    (one_pos : (0 : ℝ) < 1) LevelSix.infinity_period
  apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
  rw [map_mul, ← qExpansion_evenForm n a, ← qExpansion_evenForm m b,
    ← qExpansion_mul ha hb, hf, qExpansion_evenForm]

theorem evenSeries_zero : evenSeries 0 0 = 1 := by
  simp [evenSeries, quotientSeries, quotientUnitSeries, evenExponent,
    positiveExponent, negativeExponent, eulerPowerProduct]

lemma evenExponent_one (i : Fin 3) : evenExponent 1 i.val = weightTwoExponent i := by
  ext j
  revert i j
  decide +kernel

theorem evenSeries_one (i : Fin 3) : evenSeries 1 i.val = weightTwoSeries i := by
  apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
  rw [← qExpansion_evenForm 1 i, ← qExpansion_weightTwo]
  congr 1
  ext z
  simp only [evenForm_apply, weightTwoForm_apply, evenExponent_one]

theorem evenSeries_pow (n i t : ℕ) (hi : i ≤ 2 * n) :
    evenSeries (n * t) (i * t) = evenSeries n i ^ t := by
  induction t with
  | zero => simp [evenSeries_zero]
  | succ t ih =>
    rw [Nat.mul_succ, Nat.mul_succ, ← evenSeries_mul (n * t) n (i * t) i
      (by nlinarith [Nat.mul_le_mul_right t hi]) hi, ih, pow_succ]

theorem evenSeries_monomial (a b c : ℕ) :
    evenSeries (a + b + c) (b + 2 * c) =
      weightTwoSeries 0 ^ a * weightTwoSeries 1 ^ b * weightTwoSeries 2 ^ c := by
  have hA : evenSeries a 0 = weightTwoSeries 0 ^ a := by
    have h : evenSeries 1 0 = weightTwoSeries 0 := evenSeries_one 0
    simpa only [one_mul, zero_mul, h] using
      evenSeries_pow 1 0 a (by omega)
  have hB : evenSeries b b = weightTwoSeries 1 ^ b := by
    have h : evenSeries 1 1 = weightTwoSeries 1 := evenSeries_one 1
    simpa only [one_mul, h] using evenSeries_pow 1 1 b (by omega)
  have hC : evenSeries c (2 * c) = weightTwoSeries 2 ^ c := by
    have h : evenSeries 1 2 = weightTwoSeries 2 := evenSeries_one 2
    simpa only [one_mul, h] using evenSeries_pow 1 2 c (by omega)
  have hab : evenSeries (a + b) b = evenSeries a 0 * evenSeries b b := by
    simpa only [zero_add] using (evenSeries_mul a b 0 b (by omega) (by omega)).symm
  rw [← evenSeries_mul (a + b) c b (2 * c) (by omega) le_rfl, hab, hA, hB, hC]

def normalExponentA (n i : ℕ) : ℕ := n - i / 2 - i % 2
def normalExponentB (i : ℕ) : ℕ := i % 2
def normalExponentC (i : ℕ) : ℕ := i / 2

theorem normalExponent_weight (n i : ℕ) (hi : i ≤ 2 * n) :
    normalExponentA n i + normalExponentB i + normalExponentC i = n := by
  unfold normalExponentA normalExponentB normalExponentC
  omega

theorem normalExponent_order (i : ℕ) : normalExponentB i + 2 * normalExponentC i = i := by
  unfold normalExponentB normalExponentC
  omega

theorem normalExponentB_lt_two (i : ℕ) : normalExponentB i < 2 := Nat.mod_lt _ (by omega)

/-- The normal monomials use at most one factor B, in accordance with AC=B². -/
theorem evenSeries_normalForm (n i : ℕ) (hi : i ≤ 2 * n) :
    evenSeries n i = weightTwoSeries 0 ^ normalExponentA n i *
      weightTwoSeries 1 ^ normalExponentB i * weightTwoSeries 2 ^ normalExponentC i := by
  have h := evenSeries_monomial (normalExponentA n i) (normalExponentB i) (normalExponentC i)
  rwa [normalExponent_weight n i hi, normalExponent_order] at h

/-- Generation by A, B, C holds integrally for every actual even-weight expansion. -/
theorem even_expansion_polynomial {R : Type*} [CommRing R] (φ : R →+* ℂ)
    (hφ : Function.Injective φ) (n : ℕ) (a : PowerSeries R)
    (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) (2 * n : ℕ))
    (ha : PowerSeries.map φ a = qExpansion 1 f) :
    ∃ c : Fin (2 * n + 1) → R, a = ∑ i : Fin (2 * n + 1), c i •
      (PowerSeries.map (Int.castRingHom R) (weightTwoSeries 0) ^ normalExponentA n i.val *
       PowerSeries.map (Int.castRingHom R) (weightTwoSeries 1) ^ normalExponentB i.val *
       PowerSeries.map (Int.castRingHom R) (weightTwoSeries 2) ^ normalExponentC i.val) := by
  refine ⟨evenCoordinates n (fun i => a.coeff i.val), ?_⟩
  have he := even_expansion_descent φ hφ n a f ha
  rw [evenReconstruct, evenCombination] at he
  apply he.trans
  apply Finset.sum_congr rfl
  intro i _
  rw [evenSeries_normalForm n i.val (by omega), map_mul, map_mul, map_pow, map_pow, map_pow]

/-- The homogeneous polynomial normal form is unique over every commutative ring. -/
theorem even_normalForm_unique {R : Type*} [CommRing R] (n : ℕ)
    (c d : Fin (2 * n + 1) → R)
    (h : (∑ i : Fin (2 * n + 1), c i •
        (PowerSeries.map (Int.castRingHom R) (weightTwoSeries 0) ^ normalExponentA n i.val *
         PowerSeries.map (Int.castRingHom R) (weightTwoSeries 1) ^ normalExponentB i.val *
         PowerSeries.map (Int.castRingHom R) (weightTwoSeries 2) ^ normalExponentC i.val)) =
      ∑ i : Fin (2 * n + 1), d i •
        (PowerSeries.map (Int.castRingHom R) (weightTwoSeries 0) ^ normalExponentA n i.val *
         PowerSeries.map (Int.castRingHom R) (weightTwoSeries 1) ^ normalExponentB i.val *
         PowerSeries.map (Int.castRingHom R) (weightTwoSeries 2) ^ normalExponentC i.val)) : c = d := by
  apply evenCombination_injective n
  have he (x : Fin (2 * n + 1) → R) : evenCombination n x =
      ∑ i : Fin (2 * n + 1), x i •
        (PowerSeries.map (Int.castRingHom R) (weightTwoSeries 0) ^ normalExponentA n i.val *
         PowerSeries.map (Int.castRingHom R) (weightTwoSeries 1) ^ normalExponentB i.val *
         PowerSeries.map (Int.castRingHom R) (weightTwoSeries 2) ^ normalExponentC i.val) := by
    unfold evenCombination
    apply Finset.sum_congr rfl
    intro i _
    rw [evenSeries_normalForm n i.val (by omega), map_mul, map_mul, map_pow, map_pow, map_pow]
  rw [he c, he d]
  exact h

end RamanujanTau.TheoremA
