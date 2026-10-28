/-
# Cube roots of power series with constant term `1`

Over a commutative ring `R` in which `3` is a unit, every `e ∈ R⟦T⟧` with `e(0) = 1` has a cube
root `c` with `c(0) = 1` (`exists_cube_root`): `c = 1 + ψ(e - 1)`, where `ψ` is the compositional
inverse of `Φ(t) = (1 + t)³ - 1 = 3t + 3t² + t³` (Lie derivative `3`). Over a domain with `3 ≠ 0`
such cube roots are unique (`cube_root_unique`).
-/
import RamanujanTau.VeluLubin.Hom

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VeluDescent
open MvPowerSeries VeluLubin FGL

variable {R : Type*} [CommRing R]

local notation "R1" => MvPowerSeries Unit R

/-- `Φ(t) = 3t + 3t² + t³`. -/
noncomputable abbrev Phi3 : R1 := 3 * X () + 3 * X () ^ 2 + X () ^ 3

lemma cc_Phi3 : constantCoeff (Phi3 : R1) = 0 := by simp

lemma lie_Phi3 : coeff (Finsupp.single () 1) (Phi3 : R1) = 3 := by
  show PowerSeries.coeff 1 (3 * PowerSeries.X + 3 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3 :
    PowerSeries R) = 3
  rw [map_add, map_add, show (3 : PowerSeries R) = PowerSeries.C 3 from rfl,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  simp

lemma sb_Phi3 {u : R1} (hu : constantCoeff u = 0) : sb u (Phi3 : R1) = 3 * u + 3 * u ^ 2 + u ^ 3 := by
  rw [sb, ← coe_substAlgHom (hs (hc hu))]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  rw [coe_substAlgHom, sX _ (hc hu)]

/-- **cube roots**. -/
theorem exists_cube_root (h3 : IsUnit (3 : R)) (e : R1) (he : constantCoeff e = 1) :
    ∃ c : R1, c ^ 3 = e ∧ constantCoeff c = 1 := by
  have hlie : IsUnit (PowerSeries.coeff 1 (Phi3 : PowerSeries R)) := by
    show IsUnit (coeff (Finsupp.single () 1) (Phi3 : R1)); rw [lie_Phi3]; exact h3
  set ψ : R1 := PowerSeries.substInvOfIsUnit (Phi3 : PowerSeries R) hlie
  have hψ0 : constantCoeff ψ = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hψ : sb ψ (Phi3 : R1) = X () := by
    have := PowerSeries.subst_substInvOfIsUnit_right (Phi3 : PowerSeries R) cc_Phi3 hlie
    rw [PowerSeries.subst_def] at this; exact this
  have he1 : constantCoeff (e - 1) = 0 := by rw [map_sub, he, map_one, sub_self]
  set u : R1 := sb (e - 1) ψ
  have hu0 : constantCoeff u = 0 := cc0 _ (hc he1) hψ0
  have key : 3 * u + 3 * u ^ 2 + u ^ 3 = e - 1 := by
    rw [← sb_Phi3 hu0, ← sb_sb he1 hψ0, hψ, sb_X he1]
  refine ⟨1 + u, ?_, ?_⟩
  · linear_combination key
  · rw [map_add, map_one, hu0, add_zero]

/-- **uniqueness of cube roots**. -/
theorem cube_root_unique [IsDomain R] (h3 : (3 : R) ≠ 0) {c d : R1} (hc1 : constantCoeff c = 1)
    (hd1 : constantCoeff d = 1) (h : c ^ 3 = d ^ 3) : c = d := by
  have hne : c ^ 2 + c * d + d ^ 2 ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    simp only [map_add, map_mul, map_pow, hc1, hd1, map_zero] at this
    exact h3 (by linear_combination this)
  have : (c - d) * (c ^ 2 + c * d + d ^ 2) = 0 := by linear_combination h
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)

end VeluDescent
