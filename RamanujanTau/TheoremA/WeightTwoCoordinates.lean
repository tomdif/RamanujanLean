import RamanujanTau.TheoremA.WeightTwoQExpansion
import RamanujanTau.TheoremA.LevelSixModularSturm

/-!
# Exact coordinates and integral descent in weight two

The first three coefficients give coordinates on the entire actual space
M₂(Γ₀(6)). Its eta basis is unit triangular over the integers, so a form
whose q-expansion lies in an embedded coefficient ring is a linear
combination of A, B, C over that ring, with no denominators introduced.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open ModularForm CongruenceSubgroup PowerSeries
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm
open EtaSquared

theorem LevelSix.weightTwo_firstCoefficients_surjective :
    Function.Surjective (firstCoefficients 2) := by
  intro c
  refine ⟨c 0 • weightTwoForm 0 + (c 1 - 6 * c 0) • weightTwoForm 1 +
    (c 2 - 2 * c 1 - 3 * c 0) • weightTwoForm 2, ?_⟩
  rw [map_add, map_add, map_smul, map_smul, map_smul]
  ext i
  change c 0 * (qExpansion 1 (weightTwoForm 0)).coeff i.val +
    (c 1 - 6 * c 0) * (qExpansion 1 (weightTwoForm 1)).coeff i.val +
    (c 2 - 2 * c 1 - 3 * c 0) * (qExpansion 1 (weightTwoForm 2)).coeff i.val = c i
  rw [weightTwo_coeff 0 (by omega), weightTwo_coeff 1 (by omega), weightTwo_coeff 2 (by omega)]
  fin_cases i <;> norm_num [weightTwoCoefficients, coeffList] <;>
    (first | rfl | ring_nf <;> rfl)

noncomputable def weightTwoCoefficientEquiv :
    ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) 2 ≃ₗ[ℂ] (Fin 3 → ℂ) :=
  LinearEquiv.ofBijective (LevelSix.firstCoefficients 2)
    ⟨LevelSix.firstCoefficients_injective 2, LevelSix.weightTwo_firstCoefficients_surjective⟩

theorem weightTwo_finrank_eq_three :
    Module.finrank ℂ (ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) 2) = 3 := by
  rw [weightTwoCoefficientEquiv.finrank_eq]
  simp

/-- Reconstruction from the constant, q, and q² coefficients, over any ring. -/
noncomputable def weightTwoReconstruct {R : Type*} [CommRing R] (c : Fin 3 → R) : PowerSeries R :=
  c 0 • PowerSeries.map (Int.castRingHom R) (weightTwoSeries 0) +
    (c 1 - 6 * c 0) • PowerSeries.map (Int.castRingHom R) (weightTwoSeries 1) +
    (c 2 - 2 * c 1 - 3 * c 0) • PowerSeries.map (Int.castRingHom R) (weightTwoSeries 2)

theorem weightTwoReconstruct_coeff {R : Type*} [CommRing R] (c : Fin 3 → R) (i : Fin 3) :
    (weightTwoReconstruct c).coeff i.val = c i := by
  simp only [weightTwoReconstruct, map_add, coeff_smul, coeff_map, smul_eq_mul,
    weightTwoSeries_coeff _ (show i.val < 10 by omega)]
  fin_cases i <;> norm_num [weightTwoCoefficients, coeffList] <;>
    (first | rfl | ring_nf <;> rfl)

theorem weightTwoReconstruct_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (c : Fin 3 → R) :
    PowerSeries.map φ (weightTwoReconstruct c) = weightTwoReconstruct (fun i => φ (c i)) := by
  ext n
  simp [weightTwoReconstruct, map_ofNat]

theorem weightTwo_reconstruct_qExpansion
    (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) 2) :
    qExpansion 1 f = weightTwoReconstruct (LevelSix.firstCoefficients 2 f) := by
  let c := LevelSix.firstCoefficients 2 f
  let g := c 0 • weightTwoForm 0 + (c 1 - 6 * c 0) • weightTwoForm 1 +
    (c 2 - 2 * c 1 - 3 * c 0) • weightTwoForm 2
  have hq : qExpansion 1 g = weightTwoReconstruct c := by
    change LevelSix.modularExpansionLinear 2
      (c 0 • weightTwoForm 0 + (c 1 - 6 * c 0) • weightTwoForm 1 +
        (c 2 - 2 * c 1 - 3 * c 0) • weightTwoForm 2) = _
    rw [map_add, map_add, map_smul, map_smul, map_smul]
    change c 0 • qExpansion 1 (weightTwoForm 0) +
      (c 1 - 6 * c 0) • qExpansion 1 (weightTwoForm 1) +
      (c 2 - 2 * c 1 - 3 * c 0) • qExpansion 1 (weightTwoForm 2) = _
    simp only [qExpansion_weightTwo, weightTwoReconstruct]
  have hfg : f = g := LevelSix.firstCoefficients_injective 2 (by
    ext i
    change c i = (qExpansion 1 g).coeff i.val
    rw [hq, weightTwoReconstruct_coeff])
  exact (congrArg (fun h : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) 2 =>
    qExpansion 1 h) hfg).trans hq

/-- Integral descent from actual complex modular forms, valid for any embedded ring. -/
theorem weightTwo_expansion_descent {R : Type*} [CommRing R] (φ : R →+* ℂ)
    (hφ : Function.Injective φ) (a : PowerSeries R)
    (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) 2)
    (ha : PowerSeries.map φ a = qExpansion 1 f) :
    a = weightTwoReconstruct (fun i : Fin 3 => a.coeff i.val) := by
  apply PowerSeries.map_injective φ hφ
  rw [ha, weightTwoReconstruct_map, weightTwo_reconstruct_qExpansion]
  congr 1
  ext i
  change (qExpansion 1 f).coeff i.val = φ (a.coeff i.val)
  rw [← ha, coeff_map]

end RamanujanTau.TheoremA
