/-
# Power-saving Rankin–Selberg: integer-coefficient instances (weights 16–26), axioms

Build: `nice -n 10 lake build RamanujanTau.RankinErrorGeneral.Main`.
-/
import RamanujanTau.RankinErrorGeneral.Cusp

set_option autoImplicit false

namespace RamanujanTau.RankinErrorGeneral

open Finset Real Filter Topology
open ModularForm BoylanWebb
open RamanujanTau.RankinSelbergGeneral
open UpperHalfPlane hiding I
open scoped MatrixGroups

/-- **Power-saving Rankin–Selberg for an integral cusp form given by its integer q-expansion.** -/
theorem rankinSelberg_power_saving_intForm {k : ℕ} {a : PowerSeries ℤ} (ha : IntForm (k : ℤ) a)
    (h0 : PowerSeries.coeff 0 a = 0) (hne : a ≠ 0) :
    ∃ F : CuspForm 𝒮ℒ (k : ℤ), qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) a ∧
      0 < rsConst F ∧ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        |∑ n ∈ Icc 1 N, ((PowerSeries.coeff n a : ℤ) : ℝ) ^ 2 / (n : ℝ) ^ (k - 1) -
          rsConst F * N| ≤ C * (N : ℝ) ^ (1 - 1 / 84 : ℝ) := by
  obtain ⟨F, hF⟩ := ha
  have hc0 : (qExpansion 1 F).coeff 0 = 0 := by
    rw [hF, PowerSeries.coeff_map, h0, map_zero]
  set f := ModularForm.toCuspForm F hc0
  have hqf : qExpansion 1 f = qExpansion 1 F := rfl
  have hf : f ≠ 0 := by
    intro h
    apply hne
    have hz : qExpansion 1 f = 0 := by
      rw [h]; exact qExpansion_zero 1
    rw [hqf, hF] at hz
    exact map_injC (by rw [hz, map_zero])
  refine ⟨f, hqf.trans hF, rsConst_pos f hf, ?_⟩
  obtain ⟨C, hC⟩ := rankinSelberg_power_saving_general f
  refine ⟨C, fun N hN => ?_⟩
  have e : ∑ n ∈ Icc 1 N, ((PowerSeries.coeff n a : ℤ) : ℝ) ^ 2 / (n : ℝ) ^ (k - 1) =
      ∑ n ∈ Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1) := by
    refine sum_congr rfl fun n _ => ?_
    unfold coeffSq
    rw [hqf, hF, PowerSeries.coeff_map, eq_intCast, Complex.norm_intCast, sq_abs]
  rw [e]
  exact hC N hN

/-- **`Δ·E₄ᵃE₆ᵇ`**, weight `k = 12 + 4a + 6b`. -/
theorem rankinSelberg_power_saving_deltaE (a b : ℕ) :
    ∃ F : CuspForm 𝒮ℒ ((12 + 4 * a + 6 * b : ℕ) : ℤ),
      qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) (deltaE a b) ∧ 0 < rsConst F ∧
      ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        |∑ n ∈ Icc 1 N, ((PowerSeries.coeff n (deltaE a b) : ℤ) : ℝ) ^ 2 /
          (n : ℝ) ^ (12 + 4 * a + 6 * b - 1) - rsConst F * N| ≤ C * (N : ℝ) ^ (1 - 1 / 84 : ℝ) :=
  rankinSelberg_power_saving_intForm (intForm_deltaE a b) (coeff_zero_deltaE a b)
    (deltaE_ne_zero a b)

/-- Weight 16: `f = ΔE₄`. -/
theorem rankinSelberg_power_saving_weight16 :
    ∃ F : CuspForm 𝒮ℒ ((16 : ℕ) : ℤ),
      qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) (deltaE 1 0) ∧ 0 < rsConst F ∧
      ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        |∑ n ∈ Icc 1 N, ((PowerSeries.coeff n (deltaE 1 0) : ℤ) : ℝ) ^ 2 / (n : ℝ) ^ 15 -
          rsConst F * N| ≤ C * (N : ℝ) ^ (1 - 1 / 84 : ℝ) :=
  rankinSelberg_power_saving_deltaE 1 0

/-- Weight 18: `f = ΔE₆`. -/
theorem rankinSelberg_power_saving_weight18 :
    ∃ F : CuspForm 𝒮ℒ ((18 : ℕ) : ℤ),
      qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) (deltaE 0 1) ∧ 0 < rsConst F ∧
      ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        |∑ n ∈ Icc 1 N, ((PowerSeries.coeff n (deltaE 0 1) : ℤ) : ℝ) ^ 2 / (n : ℝ) ^ 17 -
          rsConst F * N| ≤ C * (N : ℝ) ^ (1 - 1 / 84 : ℝ) :=
  rankinSelberg_power_saving_deltaE 0 1

/-- Weight 20: `f = ΔE₈ = ΔE₄²`. -/
theorem rankinSelberg_power_saving_weight20 :
    ∃ F : CuspForm 𝒮ℒ ((20 : ℕ) : ℤ),
      qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) (deltaE 2 0) ∧ 0 < rsConst F ∧
      ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        |∑ n ∈ Icc 1 N, ((PowerSeries.coeff n (deltaE 2 0) : ℤ) : ℝ) ^ 2 / (n : ℝ) ^ 19 -
          rsConst F * N| ≤ C * (N : ℝ) ^ (1 - 1 / 84 : ℝ) :=
  rankinSelberg_power_saving_deltaE 2 0

/-- Weight 22: `f = ΔE₁₀ = ΔE₄E₆`. -/
theorem rankinSelberg_power_saving_weight22 :
    ∃ F : CuspForm 𝒮ℒ ((22 : ℕ) : ℤ),
      qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) (deltaE 1 1) ∧ 0 < rsConst F ∧
      ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        |∑ n ∈ Icc 1 N, ((PowerSeries.coeff n (deltaE 1 1) : ℤ) : ℝ) ^ 2 / (n : ℝ) ^ 21 -
          rsConst F * N| ≤ C * (N : ℝ) ^ (1 - 1 / 84 : ℝ) :=
  rankinSelberg_power_saving_deltaE 1 1

/-- Weight 26: `f = ΔE₁₄ = ΔE₄²E₆`. -/
theorem rankinSelberg_power_saving_weight26 :
    ∃ F : CuspForm 𝒮ℒ ((26 : ℕ) : ℤ),
      qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) (deltaE 2 1) ∧ 0 < rsConst F ∧
      ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        |∑ n ∈ Icc 1 N, ((PowerSeries.coeff n (deltaE 2 1) : ℤ) : ℝ) ^ 2 / (n : ℝ) ^ 25 -
          rsConst F * N| ≤ C * (N : ℝ) ^ (1 - 1 / 84 : ℝ) :=
  rankinSelberg_power_saving_deltaE 2 1

end RamanujanTau.RankinErrorGeneral

#print axioms RamanujanTau.RankinErrorGeneral.gammaM_ratio_le
#print axioms RamanujanTau.RankinErrorGeneral.power_saving_84_of_RSDataM
#print axioms RamanujanTau.RankinErrorGeneral.lintegral_mellin_horocycleG
#print axioms RamanujanTau.RankinErrorGeneral.unfold_thetaG
#print axioms RamanujanTau.RankinErrorGeneral.lintegral_mellin_PhiG
#print axioms RamanujanTau.RankinErrorGeneral.rsUnfoldG
#print axioms RamanujanTau.RankinErrorGeneral.power_saving_RSFn
#print axioms RamanujanTau.RankinErrorGeneral.rankinSelberg_power_saving_general
#print axioms RamanujanTau.RankinErrorGeneral.rankinSelberg_power_saving_discriminant
#print axioms RamanujanTau.RankinErrorGeneral.rankinSelberg_power_saving_intForm
#print axioms RamanujanTau.RankinErrorGeneral.rankinSelberg_power_saving_deltaE
#print axioms RamanujanTau.RankinErrorGeneral.rankinSelberg_power_saving_weight16
#print axioms RamanujanTau.RankinErrorGeneral.rankinSelberg_power_saving_weight18
#print axioms RamanujanTau.RankinErrorGeneral.rankinSelberg_power_saving_weight20
#print axioms RamanujanTau.RankinErrorGeneral.rankinSelberg_power_saving_weight22
#print axioms RamanujanTau.RankinErrorGeneral.rankinSelberg_power_saving_weight26
