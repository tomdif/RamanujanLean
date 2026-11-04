/-
# Every exponent `δ < 1/5` for the Rankin–Selberg mean square of every level-one cusp form

**`rankinSelberg_power_saving_sharp_general`**: for every `f ∈ S_k(SL₂(ℤ))` and `0 < δ < 1/5`,

    |∑_{n≤N} |a_f(n)|²/n^{k−1} − c_f N| ≤ C N^{1−δ},   c_f = (3/π)(4π)^k ‖f‖²/(k−1)!.

For `k ≥ 12` this is `power_saving_sharp_RSFn` applied to `rsFnCusp f` (`m = k − 1 ≥ 11`);
for `k < 12`, `f = 0`. At `f = Δ` it is the statement of
`RankinSharp.rankinSelberg_power_saving_sharp`. Corollaries in weights 16–26.

Build: `nice -n 10 lake build RamanujanTau.RankinSharpGeneral.Main`.
-/
import RamanujanTau.RankinSharpGeneral.Sharp
import RamanujanTau.RankinErrorGeneral.Main

set_option autoImplicit false

namespace RamanujanTau.RankinSharpGeneral

open Finset Real Filter Topology MeasureTheory
open Complex ModularForm BoylanWebb
open RamanujanTau.RankinSelberg hiding G G_smul continuous_G G_pos
open RamanujanTau.RankinSelbergGeneral RamanujanTau.RankinErrorGeneral
open UpperHalfPlane hiding I
open scoped MatrixGroups

variable {k : ℕ}

/-- **Rankin–Selberg with error `O(N^{1−δ})`, every `δ < 1/5`, for every level-one cusp form.** -/
theorem rankinSelberg_power_saving_sharp_general (f : CuspForm 𝒮ℒ (k : ℤ)) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < 1 / 5) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1) - rsConst f * N| ≤
        C * (N : ℝ) ^ (1 - δ) := by
  rcases lt_or_ge k 12 with hk | hk
  · obtain rfl := cuspForm_eq_zero_of_lt f hk
    refine ⟨0, fun N _ => ?_⟩
    have h1 : ∀ n, coeffSq (0 : CuspForm 𝒮ℒ (k : ℤ)) n = 0 := fun n => by
      simp [coeffSq, qExpansion_zero]
    have h2 : rsConst (0 : CuspForm 𝒮ℒ (k : ℤ)) = 0 := by
      simp [rsConst, petNormSqF, Gf]
    simp [h1, h2]
  · letI := rsFnCusp f (by omega)
    obtain ⟨C, hC⟩ := power_saving_sharp_RSFn (show 2 ≤ k - 1 by omega) hδ0 hδ
    refine ⟨C, fun N hN => ?_⟩
    have h : |∑ n ∈ Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1) -
        petNormSqF f * rsConstM (k - 1) * N| ≤ C * (N : ℝ) ^ (1 - δ) := hC N hN
    rw [rsConst_eq f (by omega)] at h
    exact h

/-- The same with the explicit constant `(3/π)(4π)^k‖f‖²/(k−1)!`. -/
theorem rankinSelberg_power_saving_sharp_general' (f : CuspForm 𝒮ℒ (k : ℤ)) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < 1 / 5) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, ‖(qExpansion 1 f).coeff n‖ ^ 2 / (n : ℝ) ^ (k - 1) -
          3 / π * (4 * π) ^ k * petNormSqF f / (Nat.factorial (k - 1) : ℝ) * N| ≤
        C * (N : ℝ) ^ (1 - δ) :=
  rankinSelberg_power_saving_sharp_general f hδ0 hδ

/-- The concrete exponent `81/100` (`δ = 19/100`), every cusp form. -/
theorem rankinSelberg_power_saving_81_100_general (f : CuspForm 𝒮ℒ (k : ℤ)) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1) - rsConst f * N| ≤
        C * (N : ℝ) ^ (81 / 100 : ℝ) := by
  obtain ⟨C, hC⟩ := rankinSelberg_power_saving_sharp_general f (δ := 19 / 100)
    (by norm_num) (by norm_num)
  exact ⟨C, fun N hN => by have := hC N hN; norm_num at this ⊢; exact this⟩

/-! ### Consistency with `RankinSharp` at `f = Δ` -/

/-- **At `f = Δ` the general theorem gives `RankinSharp.rankinSelberg_power_saving_sharp`**
(same statement, same constant `(3/π)(4π)¹²‖Δ‖²/11!`). -/
theorem rankinSelberg_power_saving_sharp_discriminant {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 5) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ (1 - δ) := by
  obtain ⟨C, hC⟩ := rankinSelberg_power_saving_sharp_general (k := 12)
    (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) hδ0 hδ
  refine ⟨C, fun N hN => ?_⟩
  have h := hC N hN
  have e : ∀ n, coeffSq (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) n =
      ((tau n : ℝ)) ^ 2 := fun n => by
    unfold coeffSq
    have e := TauBound.qExpansion_discriminant_coeff_tau n
    erw [e, Complex.norm_intCast, sq_abs]
  simp only [e, rsConst, petNormSqF_discriminant] at h
  exact h

/-- The statement coincides with the one already proved in `RankinSharp/`. -/
example {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 5) : (∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ (1 - δ)) :=
  RankinSharp.rankinSelberg_power_saving_sharp hδ0 hδ

/-! ### Integer-coefficient instances -/

/-- **Every `δ < 1/5` for an integral cusp form given by its integer q-expansion.** -/
theorem rankinSelberg_power_saving_sharp_intForm {k : ℕ} {a : PowerSeries ℤ}
    (ha : IntForm (k : ℤ) a) (h0 : PowerSeries.coeff 0 a = 0) (hne : a ≠ 0) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < 1 / 5) :
    ∃ F : CuspForm 𝒮ℒ (k : ℤ), qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) a ∧
      0 < rsConst F ∧ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        |∑ n ∈ Icc 1 N, ((PowerSeries.coeff n a : ℤ) : ℝ) ^ 2 / (n : ℝ) ^ (k - 1) -
          rsConst F * N| ≤ C * (N : ℝ) ^ (1 - δ) := by
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
  obtain ⟨C, hC⟩ := rankinSelberg_power_saving_sharp_general f hδ0 hδ
  refine ⟨C, fun N hN => ?_⟩
  have e : ∑ n ∈ Icc 1 N, ((PowerSeries.coeff n a : ℤ) : ℝ) ^ 2 / (n : ℝ) ^ (k - 1) =
      ∑ n ∈ Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1) := by
    refine sum_congr rfl fun n _ => ?_
    unfold coeffSq
    rw [hqf, hF, PowerSeries.coeff_map, eq_intCast, Complex.norm_intCast, sq_abs]
  rw [e]
  exact hC N hN

/-- **`Δ·E₄ᵃE₆ᵇ`**, weight `k = 12 + 4a + 6b`. -/
theorem rankinSelberg_power_saving_sharp_deltaE (a b : ℕ) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ < 1 / 5) :
    ∃ F : CuspForm 𝒮ℒ ((12 + 4 * a + 6 * b : ℕ) : ℤ),
      qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) (deltaE a b) ∧ 0 < rsConst F ∧
      ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        |∑ n ∈ Icc 1 N, ((PowerSeries.coeff n (deltaE a b) : ℤ) : ℝ) ^ 2 /
          (n : ℝ) ^ (12 + 4 * a + 6 * b - 1) - rsConst F * N| ≤ C * (N : ℝ) ^ (1 - δ) :=
  rankinSelberg_power_saving_sharp_intForm (intForm_deltaE a b) (coeff_zero_deltaE a b)
    (deltaE_ne_zero a b) hδ0 hδ

/-- Weight 16: `f = ΔE₄`. -/
theorem rankinSelberg_power_saving_sharp_weight16 {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 5) :
    ∃ F : CuspForm 𝒮ℒ ((16 : ℕ) : ℤ),
      qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) (deltaE 1 0) ∧ 0 < rsConst F ∧
      ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        |∑ n ∈ Icc 1 N, ((PowerSeries.coeff n (deltaE 1 0) : ℤ) : ℝ) ^ 2 / (n : ℝ) ^ 15 -
          rsConst F * N| ≤ C * (N : ℝ) ^ (1 - δ) :=
  rankinSelberg_power_saving_sharp_deltaE 1 0 hδ0 hδ

/-- Weight 18: `f = ΔE₆`. -/
theorem rankinSelberg_power_saving_sharp_weight18 {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 5) :
    ∃ F : CuspForm 𝒮ℒ ((18 : ℕ) : ℤ),
      qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) (deltaE 0 1) ∧ 0 < rsConst F ∧
      ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        |∑ n ∈ Icc 1 N, ((PowerSeries.coeff n (deltaE 0 1) : ℤ) : ℝ) ^ 2 / (n : ℝ) ^ 17 -
          rsConst F * N| ≤ C * (N : ℝ) ^ (1 - δ) :=
  rankinSelberg_power_saving_sharp_deltaE 0 1 hδ0 hδ

/-- Weight 20: `f = ΔE₈ = ΔE₄²`. -/
theorem rankinSelberg_power_saving_sharp_weight20 {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 5) :
    ∃ F : CuspForm 𝒮ℒ ((20 : ℕ) : ℤ),
      qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) (deltaE 2 0) ∧ 0 < rsConst F ∧
      ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        |∑ n ∈ Icc 1 N, ((PowerSeries.coeff n (deltaE 2 0) : ℤ) : ℝ) ^ 2 / (n : ℝ) ^ 19 -
          rsConst F * N| ≤ C * (N : ℝ) ^ (1 - δ) :=
  rankinSelberg_power_saving_sharp_deltaE 2 0 hδ0 hδ

/-- Weight 22: `f = ΔE₁₀ = ΔE₄E₆`. -/
theorem rankinSelberg_power_saving_sharp_weight22 {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 5) :
    ∃ F : CuspForm 𝒮ℒ ((22 : ℕ) : ℤ),
      qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) (deltaE 1 1) ∧ 0 < rsConst F ∧
      ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        |∑ n ∈ Icc 1 N, ((PowerSeries.coeff n (deltaE 1 1) : ℤ) : ℝ) ^ 2 / (n : ℝ) ^ 21 -
          rsConst F * N| ≤ C * (N : ℝ) ^ (1 - δ) :=
  rankinSelberg_power_saving_sharp_deltaE 1 1 hδ0 hδ

/-- Weight 26: `f = ΔE₁₄ = ΔE₄²E₆`. -/
theorem rankinSelberg_power_saving_sharp_weight26 {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 5) :
    ∃ F : CuspForm 𝒮ℒ ((26 : ℕ) : ℤ),
      qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) (deltaE 2 1) ∧ 0 < rsConst F ∧
      ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        |∑ n ∈ Icc 1 N, ((PowerSeries.coeff n (deltaE 2 1) : ℤ) : ℝ) ^ 2 / (n : ℝ) ^ 25 -
          rsConst F * N| ≤ C * (N : ℝ) ^ (1 - δ) :=
  rankinSelberg_power_saving_sharp_deltaE 2 1 hδ0 hδ

end RamanujanTau.RankinSharpGeneral

#print axioms RamanujanTau.RankinSharpGeneral.ratioAM_le
#print axioms RamanujanTau.RankinSharpGeneral.Efun_bound
#print axioms RamanujanTau.RankinSharpGeneral.power_saving_fifth_of_RSDataM
#print axioms RamanujanTau.RankinSharpGeneral.power_saving_sharp_RSFn
#print axioms RamanujanTau.RankinSharpGeneral.rankinSelberg_power_saving_sharp_general
#print axioms RamanujanTau.RankinSharpGeneral.rankinSelberg_power_saving_sharp_general'
#print axioms RamanujanTau.RankinSharpGeneral.rankinSelberg_power_saving_81_100_general
#print axioms RamanujanTau.RankinSharpGeneral.rankinSelberg_power_saving_sharp_discriminant
#print axioms RamanujanTau.RankinSharpGeneral.rankinSelberg_power_saving_sharp_intForm
#print axioms RamanujanTau.RankinSharpGeneral.rankinSelberg_power_saving_sharp_deltaE
#print axioms RamanujanTau.RankinSharpGeneral.rankinSelberg_power_saving_sharp_weight16
#print axioms RamanujanTau.RankinSharpGeneral.rankinSelberg_power_saving_sharp_weight18
#print axioms RamanujanTau.RankinSharpGeneral.rankinSelberg_power_saving_sharp_weight20
#print axioms RamanujanTau.RankinSharpGeneral.rankinSelberg_power_saving_sharp_weight22
#print axioms RamanujanTau.RankinSharpGeneral.rankinSelberg_power_saving_sharp_weight26
