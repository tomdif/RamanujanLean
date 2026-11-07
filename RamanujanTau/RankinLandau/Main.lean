/-
# `RankinLandau/`: Rankin–Selberg with error `O(N^{1−δ})` for every `δ < 2/5`

Build: `nice -n 10 lake build RamanujanTau.RankinLandau.Main`. See `docs/RANKIN_LANDAU.md`.

Headlines (all conditional on the single named hypothesis `KernelOneBound m`, a bound for
an explicit `Γ`-integral; everything else is axiom-clean):

* `rankinSelberg_landau` (for `τ`, `m = 11`);
* `rankinSelberg_landau_general` (every level-one cusp form `f ∈ S_k(SL₂(ℤ))`, `m = k − 1`).
-/
import RamanujanTau.RankinLandau.Final
import RamanujanTau.RankinSharpGeneral.Main

set_option autoImplicit false

namespace RamanujanTau.RankinLandau

open Complex Real
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral RamanujanTau.RankinSharpGeneral

section RSFn

open RamanujanTau.RankinSelbergGeneral RamanujanTau.RankinSelbergGeneral.Horo HoroFn RSFn

variable [RSFn]

/-- Every `δ < 2/5` for an abstract `RSFn` of weight `m + 1 ≥ 3`, given `KernelOneBound m`. -/
theorem landau_RSFn (hm : 2 ≤ RSFn.m) (hK : KernelOneBound RSFn.m) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ < 2 / 5) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, aF n - petNormSq * rsConstM RSFn.m * N| ≤
        C * (N : ℝ) ^ (1 - δ) :=
  landau_of_RSDataM hm aF_nonneg aF_zero petNormSq_nonneg rsDataG (abscissa_aF_le_one hm) hK
    hδ0 hδ

end RSFn

section Cusp

open Finset ModularForm BoylanWebb
open RamanujanTau.RankinSelberg hiding G G_smul continuous_G G_pos
open RamanujanTau.RankinSelbergGeneral
open UpperHalfPlane hiding I
open scoped MatrixGroups

variable {k : ℕ}

/-- **Rankin–Selberg with error `O(N^{1−δ})`, every `δ < 2/5`, for every level-one cusp form**
`f ∈ S_k(SL₂(ℤ))`, conditional on `KernelOneBound (k − 1)`:
`|∑_{n≤N} |a_f(n)|²/n^{k−1} − c_f N| ≤ C N^{1−δ}`. -/
theorem rankinSelberg_landau_general (f : CuspForm 𝒮ℒ (k : ℤ)) (hK : KernelOneBound (k - 1))
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 2 / 5) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1) - rsConst f * N| ≤
        C * (N : ℝ) ^ (1 - δ) := by
  rcases lt_or_ge k 12 with hk | hk
  · obtain rfl := cuspForm_eq_zero_of_lt f hk
    refine ⟨0, fun N _ => ?_⟩
    have h1 : ∀ n, coeffSq (0 : CuspForm 𝒮ℒ (k : ℤ)) n = 0 := fun n => by
      simp [coeffSq, qExpansion_zero]
    have h2 : rsConst (0 : CuspForm 𝒮ℒ (k : ℤ)) = 0 := by
      simp [RankinSelbergGeneral.rsConst, petNormSqF, Gf]
    simp [h1, h2]
  · letI := rsFnCusp f (by omega)
    obtain ⟨C, hC⟩ := landau_RSFn (show 2 ≤ k - 1 by omega) hK hδ0 hδ
    refine ⟨C, fun N hN => ?_⟩
    have h : |∑ n ∈ Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1) -
        petNormSqF f * rsConstM (k - 1) * N| ≤ C * (N : ℝ) ^ (1 - δ) := hC N hN
    rw [rsConst_eq f (by omega)] at h
    exact h

/-- **For `τ`: every `δ < 2/5`, conditional on `KernelOneBound 11`.**
`|∑_{n≤N} τ(n)²/n¹¹ − (3/π)(4π)¹²‖Δ‖²/11! · N| ≤ C N^{1−δ}` (Rankin 1939 has `δ = 2/5`). -/
theorem rankinSelberg_landau (hK : KernelOneBound 11) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 2 / 5) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ (1 - δ) := by
  obtain ⟨C, hC⟩ := rankinSelberg_landau_general (k := 12)
    (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) hK hδ0 hδ
  refine ⟨C, fun N hN => ?_⟩
  have h := hC N hN
  have e : ∀ n, coeffSq (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) n =
      ((tau n : ℝ)) ^ 2 := fun n => by
    unfold coeffSq
    have e := TauBound.qExpansion_discriminant_coeff_tau n
    erw [e, Complex.norm_intCast, sq_abs]
  simp only [e, RankinSelbergGeneral.rsConst, petNormSqF_discriminant] at h
  exact h

/-- For `τ`, the concrete exponent `61/100` (`δ = 39/100 > 1/3`), conditional on
`KernelOneBound 11`. -/
theorem rankinSelberg_landau_61_100 (hK : KernelOneBound 11) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ (61 / 100 : ℝ) := by
  obtain ⟨C, hC⟩ := rankinSelberg_landau hK (δ := 39 / 100) (by norm_num) (by norm_num)
  exact ⟨C, fun N hN => by have := hC N hN; norm_num at this ⊢; exact this⟩

end Cusp

end RamanujanTau.RankinLandau

-- the unconditional ingredients
#print axioms RamanujanTau.RankinLandau.landau_core
#print axioms RamanujanTau.RankinLandau.Qk_bound
#print axioms RamanujanTau.RankinLandau.norm_Jc_le
#print axioms RamanujanTau.RankinLandau.Jc_shift
#print axioms RamanujanTau.RankinLandau.Jc_rel
#print axioms RamanujanTau.RankinLandau.integral_inv_sub_line
#print axioms RamanujanTau.RankinLandau.H_bound
#print axioms RamanujanTau.RankinLandau.dual_rep
#print axioms RamanujanTau.RankinLandau.exponents_ok
-- the headlines (conditional on the hypothesis `KernelOneBound`, which is an argument)
#print axioms RamanujanTau.RankinLandau.landau_of_RSDataM
#print axioms RamanujanTau.RankinLandau.landau_RSFn
#print axioms RamanujanTau.RankinLandau.rankinSelberg_landau_general
#print axioms RamanujanTau.RankinLandau.rankinSelberg_landau
#print axioms RamanujanTau.RankinLandau.rankinSelberg_landau_61_100
