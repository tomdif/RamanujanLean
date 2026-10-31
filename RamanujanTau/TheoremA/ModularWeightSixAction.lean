import RamanujanTau.TheoremA.ModularWeightSixData
import RamanujanTau.TheoremA.BadPrimeModular
import RamanujanTau.BoylanWebb.Series

/-! The finite weight-six matrices act on the actual full modular-form space
and on its integral series model over every commutative coefficient ring. -/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open EtaSquared PowerSeries UpperHalfPlane Matrix

theorem modularWeightSix_form_action {d : ℕ} [Fact d.Prime] (hd : d ∣ 6)
    (M : Matrix (Fin 7) (Fin 7) ℤ)
    (hbound : ∀ j : Fin 7, d * j.val < 19)
    (hcert : ∀ i j : Fin 7, coeffList (modularWeightSixCoefficients i) (d * j.val) =
      ∑ t : Fin 7, M t i * coeffList (modularWeightSixCoefficients t) j.val)
    (i : Fin 7) :
    BadPrime.modularU hd (evenForm 3 i) =
      evenFormCombination 3 (fun t => (Int.castRingHom ℂ) (M t i)) := by
  apply LevelSix.firstCoefficients_injective 6
  ext j
  change (qExpansion 1 (BadPrime.modularU hd (evenForm 3 i))).coeff j.val =
    (qExpansion 1 (evenFormCombination 3 _)).coeff j.val
  rw [BadPrime.qExpansion_modularU, BoylanWebb.coeff_U, qExpansion_evenForm,
    coeff_map, modularWeightSixSeries_coeff i (hbound j), qExpansion_evenFormCombination]
  simp only [evenCombination, map_sum, coeff_smul, coeff_map, smul_eq_mul]
  have hj (t : Fin 7) := modularWeightSixSeries_coeff t (show j.val < 19 by omega)
  simp_rw [hj]
  simpa only [map_sum, map_mul] using congrArg (Int.castRingHom ℂ) (hcert i j)

theorem modularWeightSix_series_action_int {d : ℕ} [Fact d.Prime] (hd : d ∣ 6)
    (M : Matrix (Fin 7) (Fin 7) ℤ)
    (hbound : ∀ j : Fin 7, d * j.val < 19)
    (hcert : ∀ i j : Fin 7, coeffList (modularWeightSixCoefficients i) (d * j.val) =
      ∑ t : Fin 7, M t i * coeffList (modularWeightSixCoefficients t) j.val)
    (i : Fin 7) :
    BoylanWebb.U d (evenSeries 3 i.val) = evenCombination 3 (fun t => M t i) := by
  apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
  rw [BoylanWebb.map_U, evenCombination_map]
  have h := congrArg (LevelSix.modularExpansionLinear 6)
    (modularWeightSix_form_action hd M hbound hcert i)
  change qExpansion 1 (BadPrime.modularU hd (evenForm 3 i)) =
    qExpansion 1 (evenFormCombination 3 (fun t => (Int.castRingHom ℂ) (M t i))) at h
  rwa [BadPrime.qExpansion_modularU, qExpansion_evenForm, qExpansion_evenFormCombination] at h

theorem modularWeightSix_series_action {R : Type*} [CommRing R]
    {d : ℕ} [Fact d.Prime] (hd : d ∣ 6) (M : Matrix (Fin 7) (Fin 7) ℤ)
    (hbound : ∀ j : Fin 7, d * j.val < 19)
    (hcert : ∀ i j : Fin 7, coeffList (modularWeightSixCoefficients i) (d * j.val) =
      ∑ t : Fin 7, M t i * coeffList (modularWeightSixCoefficients t) j.val)
    (i : Fin 7) :
    BoylanWebb.U d (PowerSeries.map (Int.castRingHom R) (evenSeries 3 i.val)) =
      evenCombination 3 (fun t => (Int.castRingHom R) (M t i)) := by
  rw [← BoylanWebb.map_U, modularWeightSix_series_action_int hd M hbound hcert,
    evenCombination_map]

theorem modularWeightSix_combination_action {R : Type*} [CommRing R]
    {d : ℕ} [Fact d.Prime] (hd : d ∣ 6) (M : Matrix (Fin 7) (Fin 7) ℤ)
    (hbound : ∀ j : Fin 7, d * j.val < 19)
    (hcert : ∀ i j : Fin 7, coeffList (modularWeightSixCoefficients i) (d * j.val) =
      ∑ t : Fin 7, M t i * coeffList (modularWeightSixCoefficients t) j.val)
    (c : Fin 7 → R) :
    uOperator d (evenCombination 3 c) =
      evenCombination 3 (((Int.castRingHom R).mapMatrix M) *ᵥ c) := by
  let E := evenCombinationLinear (R := R) 3
  change uOperator d (∑ i : Fin 7, c i • PowerSeries.map (Int.castRingHom R) (evenSeries 3 i.val)) = _
  rw [map_sum]
  simp only [map_smul, uOperator_apply]
  simp_rw [modularWeightSix_series_action hd M hbound hcert]
  change (∑ i : Fin 7, c i • E (fun t => (Int.castRingHom R) (M t i))) = E _
  simp_rw [← map_smul E]
  rw [← map_sum E]
  congr 1
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    RingHom.mapMatrix_apply, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem modularWeightSix_U2_action {R : Type*} [CommRing R] (c : Fin 7 → R) :
    uOperator 2 (evenCombination 3 c) =
      evenCombination 3 (((Int.castRingHom R).mapMatrix modularWeightSixU2) *ᵥ c) :=
  modularWeightSix_combination_action (by decide : 2 ∣ 6) modularWeightSixU2
    (by intro j; omega) modularWeightSixU2_certificate c

theorem modularWeightSix_U3_action {R : Type*} [CommRing R] (c : Fin 7 → R) :
    uOperator 3 (evenCombination 3 c) =
      evenCombination 3 (((Int.castRingHom R).mapMatrix modularWeightSixU3) *ᵥ c) :=
  modularWeightSix_combination_action (by decide : 3 ∣ 6) modularWeightSixU3
    (by intro j; omega) modularWeightSixU3_certificate c

end RamanujanTau.TheoremA
