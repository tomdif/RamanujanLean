/-
# `RankinExact/`: Rankin's theorem with the exact exponent `3/5`

Build: `nice -n 10 lake build RamanujanTau.RankinExact.Main`. See `docs/RANKIN_EXACT.md`.

Headlines (unconditional, no `ε`):

* `kernel_sharp`: `‖J_j(y)‖ ≤ C y^{3j/4+3/8}` for every `j ≥ 1` (bent contour, modulus only);
* `landau_sharp`: Landau's differencing with the ε-free constraints;
* `rankinSelberg_exact` (for `τ`) and `rankinSelberg_exact_general` (every level-one cusp
  form): `|∑_{n≤N} |a(n)|²/n^{k−1} − cN| ≤ C N^{3/5}`.
-/
import RamanujanTau.RankinExact.Final
import RamanujanTau.RankinLandau.Main

set_option autoImplicit false

namespace RamanujanTau.RankinExact

open Complex Real
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral RamanujanTau.RankinSharpGeneral
open RamanujanTau.RankinLandau

section RSFn

open RamanujanTau.RankinSelbergGeneral RamanujanTau.RankinSelbergGeneral.Horo HoroFn RSFn

variable [RSFn]

/-- Exponent `3/5` exactly for an abstract `RSFn` of weight `m + 1 ≥ 3`. -/
theorem landau_exact_RSFn (hm : 2 ≤ RSFn.m) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, aF n - petNormSq * rsConstM RSFn.m * N| ≤
        C * (N : ℝ) ^ ((3 : ℝ) / 5) :=
  landau_exact_of_RSDataM hm aF_nonneg aF_zero petNormSq_nonneg rsDataG (abscissa_aF_le_one hm)

end RSFn

section Cusp

open Finset ModularForm BoylanWebb
open RamanujanTau.RankinSelberg hiding G G_smul continuous_G G_pos
open RamanujanTau.RankinSelbergGeneral
open UpperHalfPlane hiding I
open scoped MatrixGroups

variable {k : ℕ}

/-- **Rankin's theorem, exactly, for every level-one cusp form** `f ∈ S_k(SL₂(ℤ))`
(every weight `k`; unconditional):
`|∑_{n≤N} |a_f(n)|²/n^{k−1} − c_f N| ≤ C N^{3/5}`. -/
theorem rankinSelberg_exact_general (f : CuspForm 𝒮ℒ (k : ℤ)) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1) - rsConst f * N| ≤
        C * (N : ℝ) ^ ((3 : ℝ) / 5) := by
  rcases lt_or_ge k 12 with hk | hk
  · obtain rfl := cuspForm_eq_zero_of_lt f hk
    refine ⟨0, fun N _ => ?_⟩
    have h1 : ∀ n, coeffSq (0 : CuspForm 𝒮ℒ (k : ℤ)) n = 0 := fun n => by
      simp [coeffSq, qExpansion_zero]
    have h2 : rsConst (0 : CuspForm 𝒮ℒ (k : ℤ)) = 0 := by
      simp [RankinSelbergGeneral.rsConst, petNormSqF, Gf]
    simp [h1, h2]
  · letI := rsFnCusp f (by omega)
    obtain ⟨C, hC⟩ := landau_exact_RSFn (show 2 ≤ k - 1 by omega)
    refine ⟨C, fun N hN => ?_⟩
    have h : |∑ n ∈ Icc 1 N, coeffSq f n / (n : ℝ) ^ (k - 1) -
        petNormSqF f * rsConstM (k - 1) * N| ≤ C * (N : ℝ) ^ ((3 : ℝ) / 5) := hC N hN
    rw [rsConst_eq f (by omega)] at h
    exact h

/-- **Rankin's theorem (1939), exactly, for `τ`** (unconditional):
`|∑_{n≤N} τ(n)²/n¹¹ − (3/π)(4π)¹²‖Δ‖²/11! · N| ≤ C N^{3/5}`. -/
theorem rankinSelberg_exact :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11 -
          3 / π * (4 * π) ^ 12 * EisensteinReal.petNormSq / (Nat.factorial 11 : ℝ) * N| ≤
        C * (N : ℝ) ^ ((3 : ℝ) / 5) := by
  obtain ⟨C, hC⟩ := rankinSelberg_exact_general (k := 12)
    (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ))
  refine ⟨C, fun N hN => ?_⟩
  have h := hC N hN
  have e : ∀ n, coeffSq (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) n =
      ((tau n : ℝ)) ^ 2 := fun n => by
    unfold coeffSq
    have e := TauBound.qExpansion_discriminant_coeff_tau n
    erw [e, Complex.norm_intCast, sq_abs]
  simp only [e, RankinSelbergGeneral.rsConst, petNormSqF_discriminant] at h
  exact h

end Cusp

end RamanujanTau.RankinExact

#print axioms RamanujanTau.RankinExact.norm_Gj_add_nat_le
#print axioms RamanujanTau.RankinExact.norm_Gj_sub_nat_le
#print axioms RamanujanTau.RankinExact.integral_Gj_le
#print axioms RamanujanTau.RankinExact.kernel_sharp
#print axioms RamanujanTau.RankinExact.majorize
#print axioms RamanujanTau.RankinExact.sum_wS_le
#print axioms RamanujanTau.RankinExact.sum_vT_le
#print axioms RamanujanTau.RankinExact.linear_bound
#print axioms RamanujanTau.RankinExact.landau_sharp
#print axioms RamanujanTau.RankinExact.landau_exact_of_RSDataM
#print axioms RamanujanTau.RankinExact.landau_exact_RSFn
#print axioms RamanujanTau.RankinExact.rankinSelberg_exact_general
#print axioms RamanujanTau.RankinExact.rankinSelberg_exact
