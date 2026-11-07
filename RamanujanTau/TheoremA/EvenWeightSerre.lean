import RamanujanTau.TheoremA.EvenWeightProducts
import RamanujanTau.TheoremA.LevelSixSerre

/-!
# Integral Serre differentiation in the level-six coordinate model

The operator 12θ - kE₂ preserves the integral model and raises its weight
by two, over every commutative coefficient ring. This follows from the
actual analytic Serre derivative and integral descent, and does not assume
any characteristic-p filtration law.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA
open ModularForm CongruenceSubgroup PowerSeries
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm
open EtaSquared

noncomputable def serreSeries {R : Type*} [CommRing R] (k : ℤ) (f : PowerSeries R) : PowerSeries R :=
  12 * Igusa.theta f - (k : PowerSeries R) * (Igusa.E2 R * f)

theorem map_serreSeries {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (k : ℤ) (f : PowerSeries R) :
    PowerSeries.map φ (serreSeries k f) = serreSeries k (PowerSeries.map φ f) := by
  simp [serreSeries, Igusa.map_theta, Igusa.map_E2, map_ofNat]

noncomputable def serreSeriesLinear {R : Type*} [CommRing R] (k : ℤ) :
    PowerSeries R →ₗ[R] PowerSeries R where
  toFun := serreSeries k
  map_add' f g := by simp only [serreSeries, Igusa.theta_add]; ring
  map_smul' c f := by
    simp only [serreSeries, PowerSeries.smul_eq_C_mul, Igusa.theta_mul, Igusa.theta_C,
      zero_mul, zero_add, RingHom.id_apply]
    ring

@[simp] theorem serreSeriesLinear_apply {R : Type*} [CommRing R]
    (k : ℤ) (f : PowerSeries R) : serreSeriesLinear k f = serreSeries k f := rfl

theorem serreSeries_mul {R : Type*} [CommRing R] (k l : ℤ) (f g : PowerSeries R) :
    serreSeries (k + l) (f * g) = serreSeries k f * g + f * serreSeries l g := by
  simp only [serreSeries, Igusa.theta_mul, Int.cast_add]
  ring

theorem LevelSix.qExpansion_integralSerreSeries {k : ℤ}
    (f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) k) :
    qExpansion 1 (integralSerreForm f) = serreSeries k (qExpansion 1 f) := by
  simpa only [serreSeries, PowerSeries.smul_eq_C_mul, map_ofNat, map_intCast] using
    qExpansion_integralSerreForm f

/-- The integral eta basis remains integral after scaled Serre differentiation. -/
theorem serreSeries_evenSeries (n : ℕ) (i : Fin (2 * n + 1)) :
    serreSeries (2 * n : ℕ) (evenSeries n i.val) = evenReconstruct (n + 1)
      (fun j : Fin (2 * (n + 1) + 1) =>
        (serreSeries (2 * n : ℕ) (evenSeries n i.val)).coeff j.val) := by
  let f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) (2 * (n + 1) : ℕ) :=
    ModularForm.mcast (by push_cast; ring) (LevelSix.integralSerreForm (evenForm n i))
  apply even_expansion_descent (Int.castRingHom ℂ) Int.cast_injective (n + 1) _ f
  rw [map_serreSeries, ← qExpansion_evenForm]
  exact (LevelSix.qExpansion_integralSerreSeries (evenForm n i)).symm

/-- Integer coefficients for the derivative of each basis element. -/
noncomputable def evenSerreColumn (n : ℕ) (i : Fin (2 * n + 1)) : Fin (2 * (n + 1) + 1) → ℤ :=
  evenCoordinates (n + 1) (fun j => (serreSeries (2 * n : ℕ) (evenSeries n i.val)).coeff j.val)

noncomputable def evenSerreCoordinates {R : Type*} [CommRing R]
    (n : ℕ) (c : Fin (2 * n + 1) → R) : Fin (2 * (n + 1) + 1) → R :=
  ∑ i : Fin (2 * n + 1), c i • (fun j => (evenSerreColumn n i j : R))

lemma serreSeries_evenBasis {R : Type*} [CommRing R] (n : ℕ) (i : Fin (2 * n + 1)) :
    serreSeries (2 * n : ℕ) (PowerSeries.map (Int.castRingHom R) (evenSeries n i.val)) =
      evenCombination (n + 1) (fun j => (evenSerreColumn n i j : R)) := by
  rw [← map_serreSeries, serreSeries_evenSeries, evenReconstruct, evenCombination_map]
  rfl

/-- Weight-raising and integrality in every residue ring, proved from actual modular forms. -/
theorem serreSeries_evenCombination {R : Type*} [CommRing R]
    (n : ℕ) (c : Fin (2 * n + 1) → R) :
    serreSeries (2 * n : ℕ) (evenCombination n c) =
      evenCombination (n + 1) (evenSerreCoordinates n c) := by
  change serreSeriesLinear (2 * n : ℕ)
    (∑ i, c i • PowerSeries.map (Int.castRingHom R) (evenSeries n i.val)) =
      evenCombinationLinear (n + 1) (∑ i, c i • (fun j => (evenSerreColumn n i j : R)))
  simp only [map_sum, map_smul, serreSeriesLinear_apply, evenCombinationLinear_apply,
    serreSeries_evenBasis]

end RamanujanTau.TheoremA
