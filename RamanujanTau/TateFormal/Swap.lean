import Mathlib.RingTheory.PowerSeries.Derivative
import RamanujanTau.FormalGroupLayer.PDeriv

/-!
# Swapping the two variables of `K⟦T⟧⟦q⟧`
-/

set_option autoImplicit false

noncomputable section

namespace TateFormal

open PowerSeries

variable {K : Type*} [CommRing K]

/-- `sw : K⟦T⟧⟦q⟧ → K⟦q⟧⟦T⟧` (the outer variable becomes the inner one). -/
def swF (f : PowerSeries (PowerSeries K)) : PowerSeries (PowerSeries K) :=
  mk fun j => mk fun N => coeff j (coeff N f)

lemma coeff_swF (f : PowerSeries (PowerSeries K)) (j N : ℕ) :
    coeff N (coeff j (swF f)) = coeff j (coeff N f) := by simp [swF]

/-- the swap as a ring homomorphism. -/
def sw : PowerSeries (PowerSeries K) →+* PowerSeries (PowerSeries K) where
  toFun := swF
  map_one' := by
    ext j N
    rw [coeff_swF, coeff_one, coeff_one]
    by_cases hN : N = 0 <;> by_cases hj : j = 0 <;> simp [hN, hj, coeff_one]
  map_mul' f g := by
    ext j N
    rw [coeff_swF, coeff_mul, coeff_mul, map_sum, map_sum]
    simp_rw [coeff_mul, coeff_swF]
    exact Finset.sum_comm
  map_zero' := by ext j N; simp [coeff_swF]
  map_add' f g := by ext j N; simp [coeff_swF]

lemma coeff_sw (f : PowerSeries (PowerSeries K)) (j N : ℕ) :
    coeff N (coeff j (sw f)) = coeff j (coeff N f) := coeff_swF f j N

lemma sw_C (g : PowerSeries K) : sw (C g) = PowerSeries.map (C (R := K)) g := by
  ext j N
  rw [coeff_sw, coeff_C, coeff_map, coeff_C]
  split_ifs <;> simp [coeff_C]

lemma sw_map_C (g : PowerSeries K) : sw (PowerSeries.map (C (R := K)) g) = C g := by
  ext j N
  rw [coeff_sw, coeff_map, coeff_C, coeff_C]
  split_ifs <;> simp

lemma sw_C_X : sw (C (X : PowerSeries K)) = X := by
  rw [sw_C]; ext j N; simp [coeff_X]

/-- the inner derivative. -/
def dI (f : PowerSeries (PowerSeries K)) : PowerSeries (PowerSeries K) :=
  mk fun N => derivative K (coeff N f)

lemma coeff_pd_unit {R : Type*} [CommRing R] (f : MvPowerSeries Unit R) (k : ℕ) :
    PowerSeries.coeff k (MvPowerSeries.pd () f : PowerSeries R) = PowerSeries.coeff (k + 1) f * ((k : R) + 1) := by
  show MvPowerSeries.coeff (Finsupp.single () k) _ = MvPowerSeries.coeff (Finsupp.single () (k + 1)) f * _
  rw [MvPowerSeries.coeff_pd, ← Finsupp.single_add, Finsupp.single_eq_same]

lemma pd_sw (f : PowerSeries (PowerSeries K)) :
    MvPowerSeries.pd () (sw f : MvPowerSeries Unit (PowerSeries K)) = sw (dI f) := by
  ext j N
  rw [coeff_pd_unit, coeff_sw, dI, coeff_mk, coeff_derivative, ← coeff_sw]
  rw [show ((j : PowerSeries K) + 1) = C ((j : K) + 1) by simp, coeff_mul_C]

end TateFormal
