import RamanujanTau.TateCurve.Expand
import Mathlib.RingTheory.LaurentSeries

/-!
# The Tate curve over `ℤ((q))` is elliptic

`Δ(Tate) = q · (q;q)_∞²⁴` with `(q;q)_∞` a unit of `ℤ⟦q⟧`, so `Δ` becomes a unit in `ℤ((q))`.
-/

set_option autoImplicit false

namespace TateCurve
open PowerSeries

lemma isUnit_qfacInf : IsUnit MockTheta5.JTP.qfacInf := by
  rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, MockTheta5.JTP.coeff_zero_qfacInf]
  exact isUnit_one

/-- `Δ(Tate) = q · u` with `u = (q;q)_∞²⁴` a unit of `ℤ⟦q⟧`. -/
theorem Δ_Tate_eq_X_mul_unit : ∃ u : (PowerSeries ℤ)ˣ, Tate.Δ = X * (u : PowerSeries ℤ) :=
  ⟨(isUnit_qfacInf.pow 24).unit, by rw [Δ_Tate, IsUnit.unit_spec]⟩

/-- The Tate curve over the Laurent series ring `ℤ((q))`. -/
noncomputable def TateLaurent : WeierstrassCurve (LaurentSeries ℤ) :=
  Tate.map (HahnSeries.ofPowerSeries ℤ ℤ)

lemma isUnit_single_one : IsUnit (HahnSeries.single (1 : ℤ) (1 : ℤ) : LaurentSeries ℤ) :=
  isUnit_iff_exists_inv.mpr ⟨HahnSeries.single (-1 : ℤ) (1 : ℤ), by
    rw [HahnSeries.single_mul_single, add_neg_cancel, mul_one, HahnSeries.single_zero_one]⟩

instance isElliptic_TateLaurent : TateLaurent.IsElliptic := by
  constructor
  rw [TateLaurent, WeierstrassCurve.map_Δ, Δ_Tate, map_mul, map_pow, HahnSeries.ofPowerSeries_X]
  exact isUnit_single_one.mul ((isUnit_qfacInf.map _).pow 24)

end TateCurve
