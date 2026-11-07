import RamanujanTau.TheoremA.ModularWeightEightData
import RamanujanTau.TheoremA.BadPrimeModular
import RamanujanTau.BoylanWebb.Series

/-! The finite weight-eight matrices act on the actual full modular-form space
and on its integral series model over every commutative coefficient ring. -/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open EtaSquared PowerSeries UpperHalfPlane Matrix

theorem modularWeightEight_form_action {d : ℕ} [Fact d.Prime] (hd : d ∣ 6)
    (M : Matrix (Fin 9) (Fin 9) ℤ)
    (hbound : ∀ j : Fin 9, d * j.val < 25)
    (hcert : ∀ i j : Fin 9, coeffList (modularWeightEightCoefficients i) (d * j.val) =
      ∑ t : Fin 9, M t i * coeffList (modularWeightEightCoefficients t) j.val)
    (i : Fin 9) :
    BadPrime.modularU hd (evenForm 4 i) =
      evenFormCombination 4 (fun t => (Int.castRingHom ℂ) (M t i)) := by
  apply LevelSix.firstCoefficients_injective 8
  ext j
  change (qExpansion 1 (BadPrime.modularU hd (evenForm 4 i))).coeff j.val =
    (qExpansion 1 (evenFormCombination 4 _)).coeff j.val
  rw [BadPrime.qExpansion_modularU, BoylanWebb.coeff_U, qExpansion_evenForm,
    coeff_map, modularWeightEightSeries_coeff i (hbound j), qExpansion_evenFormCombination]
  simp only [evenCombination, map_sum, coeff_smul, coeff_map, smul_eq_mul]
  have hj (t : Fin 9) := modularWeightEightSeries_coeff t (show j.val < 25 by omega)
  simp_rw [hj]
  simpa only [map_sum, map_mul] using congrArg (Int.castRingHom ℂ) (hcert i j)

theorem modularWeightEight_series_action_int {d : ℕ} [Fact d.Prime] (hd : d ∣ 6)
    (M : Matrix (Fin 9) (Fin 9) ℤ)
    (hbound : ∀ j : Fin 9, d * j.val < 25)
    (hcert : ∀ i j : Fin 9, coeffList (modularWeightEightCoefficients i) (d * j.val) =
      ∑ t : Fin 9, M t i * coeffList (modularWeightEightCoefficients t) j.val)
    (i : Fin 9) :
    BoylanWebb.U d (evenSeries 4 i.val) = evenCombination 4 (fun t => M t i) := by
  apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
  rw [BoylanWebb.map_U, evenCombination_map]
  have h := congrArg (LevelSix.modularExpansionLinear 8)
    (modularWeightEight_form_action hd M hbound hcert i)
  change qExpansion 1 (BadPrime.modularU hd (evenForm 4 i)) =
    qExpansion 1 (evenFormCombination 4 (fun t => (Int.castRingHom ℂ) (M t i))) at h
  rwa [BadPrime.qExpansion_modularU, qExpansion_evenForm, qExpansion_evenFormCombination] at h

theorem modularWeightEight_series_action {R : Type*} [CommRing R]
    {d : ℕ} [Fact d.Prime] (hd : d ∣ 6) (M : Matrix (Fin 9) (Fin 9) ℤ)
    (hbound : ∀ j : Fin 9, d * j.val < 25)
    (hcert : ∀ i j : Fin 9, coeffList (modularWeightEightCoefficients i) (d * j.val) =
      ∑ t : Fin 9, M t i * coeffList (modularWeightEightCoefficients t) j.val)
    (i : Fin 9) :
    BoylanWebb.U d (PowerSeries.map (Int.castRingHom R) (evenSeries 4 i.val)) =
      evenCombination 4 (fun t => (Int.castRingHom R) (M t i)) := by
  rw [← BoylanWebb.map_U, modularWeightEight_series_action_int hd M hbound hcert,
    evenCombination_map]

theorem modularWeightEight_combination_action {R : Type*} [CommRing R]
    {d : ℕ} [Fact d.Prime] (hd : d ∣ 6) (M : Matrix (Fin 9) (Fin 9) ℤ)
    (hbound : ∀ j : Fin 9, d * j.val < 25)
    (hcert : ∀ i j : Fin 9, coeffList (modularWeightEightCoefficients i) (d * j.val) =
      ∑ t : Fin 9, M t i * coeffList (modularWeightEightCoefficients t) j.val)
    (c : Fin 9 → R) :
    uOperator d (evenCombination 4 c) =
      evenCombination 4 (((Int.castRingHom R).mapMatrix M) *ᵥ c) := by
  let E := evenCombinationLinear (R := R) 4
  change uOperator d (∑ i : Fin 9, c i • PowerSeries.map (Int.castRingHom R) (evenSeries 4 i.val)) = _
  rw [map_sum]
  simp only [map_smul, uOperator_apply]
  simp_rw [modularWeightEight_series_action hd M hbound hcert]
  change (∑ i : Fin 9, c i • E (fun t => (Int.castRingHom R) (M t i))) = E _
  simp_rw [← map_smul E]
  rw [← map_sum E]
  congr 1
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    RingHom.mapMatrix_apply, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem modularWeightEight_U2_action {R : Type*} [CommRing R] (c : Fin 9 → R) :
    uOperator 2 (evenCombination 4 c) =
      evenCombination 4 (((Int.castRingHom R).mapMatrix modularWeightEightU2) *ᵥ c) :=
  modularWeightEight_combination_action (by decide : 2 ∣ 6) modularWeightEightU2
    (by intro j; omega) modularWeightEightU2_certificate c

theorem modularWeightEight_U3_action {R : Type*} [CommRing R] (c : Fin 9 → R) :
    uOperator 3 (evenCombination 4 c) =
      evenCombination 4 (((Int.castRingHom R).mapMatrix modularWeightEightU3) *ᵥ c) :=
  modularWeightEight_combination_action (by decide : 3 ∣ 6) modularWeightEightU3
    (by intro j; omega) modularWeightEightU3_certificate c

end RamanujanTau.TheoremA
