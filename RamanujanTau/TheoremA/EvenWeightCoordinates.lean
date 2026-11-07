import RamanujanTau.TheoremA.EvenWeightForms
import RamanujanTau.TheoremA.LevelSixModularSturm
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Integral coordinates in every even weight at level six

The Fourier coefficient matrix of the eta family is lower triangular with
diagonal one. Its inverse is an integer matrix. This gives reconstruction
over arbitrary coefficient rings, commutes with reduction, and identifies
the entire actual complex modular-form space via the coefficient bound.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open ModularForm CongruenceSubgroup PowerSeries Matrix
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm
open EtaSquared

noncomputable def evenJet (n : ℕ) : Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) ℤ :=
  fun i j => (evenSeries n j.val).coeff i.val

theorem evenJet_det (n : ℕ) : (evenJet n).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (by
    intro i j hij
    exact evenSeries_coeff_lt n j.val i.val hij)]
  simp only [evenJet, evenSeries_coeff_self, Finset.prod_const_one]

lemma evenJet_det_isUnit (n : ℕ) : IsUnit (evenJet n).det := by
  rw [evenJet_det]
  exact isUnit_one

noncomputable def evenCoordinates {R : Type*} [CommRing R]
    (n : ℕ) (c : Fin (2 * n + 1) → R) : Fin (2 * n + 1) → R :=
  ((Int.castRingHom R).mapMatrix ((evenJet n)⁻¹)) *ᵥ c

noncomputable def evenCombination {R : Type*} [CommRing R]
    (n : ℕ) (c : Fin (2 * n + 1) → R) : PowerSeries R :=
  ∑ i : Fin (2 * n + 1), c i • PowerSeries.map (Int.castRingHom R) (evenSeries n i.val)

noncomputable def evenReconstruct {R : Type*} [CommRing R]
    (n : ℕ) (c : Fin (2 * n + 1) → R) : PowerSeries R :=
  evenCombination n (evenCoordinates n c)

noncomputable def evenCombinationLinear {R : Type*} [CommRing R] (n : ℕ) :
    (Fin (2 * n + 1) → R) →ₗ[R] PowerSeries R where
  toFun := evenCombination n
  map_add' c d := by simp [evenCombination, add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [evenCombination, Finset.smul_sum, smul_smul]

@[simp] theorem evenCombinationLinear_apply {R : Type*} [CommRing R]
    (n : ℕ) (c : Fin (2 * n + 1) → R) : evenCombinationLinear n c = evenCombination n c := rfl

theorem evenCombination_coeff {R : Type*} [CommRing R]
    (n : ℕ) (c : Fin (2 * n + 1) → R) (i : Fin (2 * n + 1)) :
    (evenCombination n c).coeff i.val =
      (((Int.castRingHom R).mapMatrix (evenJet n)) *ᵥ c) i := by
  simp only [evenCombination, map_sum, coeff_smul, coeff_map, smul_eq_mul,
    Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, evenJet]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem evenReconstruct_coeff {R : Type*} [CommRing R]
    (n : ℕ) (c : Fin (2 * n + 1) → R) (i : Fin (2 * n + 1)) :
    (evenReconstruct n c).coeff i.val = c i := by
  rw [evenReconstruct, evenCombination_coeff, evenCoordinates,
    Matrix.mulVec_mulVec, ← map_mul, Matrix.mul_nonsing_inv _ (evenJet_det_isUnit n),
    map_one, Matrix.one_mulVec]

theorem evenCombination_injective {R : Type*} [CommRing R] (n : ℕ) :
    Function.Injective (evenCombination (R := R) n) := by
  intro c d he
  have hc : (Int.castRingHom R).mapMatrix (evenJet n) *ᵥ c =
      (Int.castRingHom R).mapMatrix (evenJet n) *ᵥ d := by
    ext i
    simpa only [evenCombination_coeff] using congrArg (fun a : PowerSeries R => a.coeff i.val) he
  have h := congrArg (fun v => (Int.castRingHom R).mapMatrix ((evenJet n)⁻¹) *ᵥ v) hc
  simpa only [Matrix.mulVec_mulVec, ← map_mul,
    Matrix.nonsing_inv_mul _ (evenJet_det_isUnit n), map_one, Matrix.one_mulVec] using h

theorem evenCoordinates_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (n : ℕ) (c : Fin (2 * n + 1) → R) (i : Fin (2 * n + 1)) :
    φ (evenCoordinates n c i) = evenCoordinates n (fun j => φ (c j)) i := by
  simp [evenCoordinates, Matrix.mulVec, dotProduct]

theorem evenCombination_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (n : ℕ) (c : Fin (2 * n + 1) → R) :
    PowerSeries.map φ (evenCombination n c) = evenCombination n (fun i => φ (c i)) := by
  ext k
  simp [evenCombination]

theorem evenReconstruct_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (n : ℕ) (c : Fin (2 * n + 1) → R) :
    PowerSeries.map φ (evenReconstruct n c) = evenReconstruct n (fun i => φ (c i)) := by
  rw [evenReconstruct, evenCombination_map, evenReconstruct]
  congr 1
  ext i
  exact evenCoordinates_map φ n c i

noncomputable def evenFormCombination (n : ℕ) (c : Fin (2 * n + 1) → ℂ) :
    ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) (2 * n : ℕ) :=
  ∑ i : Fin (2 * n + 1), c i • evenForm n i

theorem qExpansion_evenFormCombination (n : ℕ) (c : Fin (2 * n + 1) → ℂ) :
    qExpansion 1 (evenFormCombination n c) = evenCombination n c := by
  change LevelSix.modularExpansionLinear _ (∑ i, c i • evenForm n i) = _
  rw [map_sum]
  simp only [map_smul]
  change (∑ i, c i • qExpansion 1 (evenForm n i)) = _
  simp only [qExpansion_evenForm, evenCombination]

theorem LevelSix.even_firstCoefficients_surjective (n : ℕ) :
    Function.Surjective (firstCoefficients (2 * n)) := by
  intro c
  refine ⟨evenFormCombination n (evenCoordinates n c), ?_⟩
  ext i
  change (qExpansion 1 (evenFormCombination n (evenCoordinates n c))).coeff i.val = c i
  rw [qExpansion_evenFormCombination]
  exact evenReconstruct_coeff n c i

/-- The first 2n+1 coefficients are coordinates on the entire weight-2n space. -/
noncomputable def evenCoefficientEquiv (n : ℕ) :
    ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) (2 * n : ℕ) ≃ₗ[ℂ]
      (Fin (2 * n + 1) → ℂ) :=
  LinearEquiv.ofBijective (LevelSix.firstCoefficients (2 * n))
    ⟨LevelSix.firstCoefficients_injective _, LevelSix.even_firstCoefficients_surjective n⟩

theorem evenWeight_finrank (n : ℕ) :
    Module.finrank ℂ (ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) (2 * n : ℕ)) =
      2 * n + 1 := by
  rw [(evenCoefficientEquiv n).finrank_eq]
  simp

theorem even_reconstruct_qExpansion (n : ℕ)
    (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) (2 * n : ℕ)) :
    qExpansion 1 f = evenReconstruct n (LevelSix.firstCoefficients (2 * n) f) := by
  let c := LevelSix.firstCoefficients (2 * n) f
  let g := evenFormCombination n (evenCoordinates n c)
  have hq : qExpansion 1 g = evenReconstruct n c := qExpansion_evenFormCombination _ _
  have hfg : f = g := LevelSix.firstCoefficients_injective (2 * n) (by
    ext i
    change c i = (qExpansion 1 g).coeff i.val
    rw [hq, evenReconstruct_coeff])
  exact (congrArg (fun h : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) (2 * n : ℕ) =>
    qExpansion 1 h) hfg).trans hq

/-- Integral descent in every even weight, without division in the coefficient ring. -/
theorem even_expansion_descent {R : Type*} [CommRing R] (φ : R →+* ℂ)
    (hφ : Function.Injective φ) (n : ℕ) (a : PowerSeries R)
    (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) (2 * n : ℕ))
    (ha : PowerSeries.map φ a = qExpansion 1 f) :
    a = evenReconstruct n (fun i : Fin (2 * n + 1) => a.coeff i.val) := by
  apply PowerSeries.map_injective φ hφ
  rw [ha, evenReconstruct_map, even_reconstruct_qExpansion]
  congr 1
  ext i
  change (qExpansion 1 f).coeff i.val = φ (a.coeff i.val)
  rw [← ha, coeff_map]

end RamanujanTau.TheoremA
