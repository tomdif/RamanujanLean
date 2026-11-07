/-
# The Poincaré series over `Γ_∞ \ SL₂(ℤ)` as a sum over coprime pairs, and its slash invariance

For a coprime pair `v = (c,d)` choose `γ_v ∈ SL₂(ℤ)` with bottom row `v` (`ModularGroup.bottom_row_surj`)
and put `pTerm v z = (cz+d)^{-12} e(γ_v z)`. The value `e(γ_v z)` does not depend on the choice of
`γ_v` (`ee_smul_eq_of_bottom_row`), which gives the covariance
`pTerm v (γ z) = j(γ,z)^{12} pTerm (vγ) z` (`pTerm_smul`), and hence (re-indexing by `v ↦ vγ`, exactly as for
Mathlib's `eisensteinSeries_slash_apply`) `pSeries (γ z) = j(γ,z)^{12} pSeries z` (`pSeries_smul`).
-/
import RamanujanTau.TauBound.Unfold
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
import Mathlib.NumberTheory.Modular

set_option autoImplicit false

namespace RamanujanTau.TauBound

open Complex UpperHalfPlane ModularGroup EisensteinSeries Matrix
open scoped MatrixGroups

/-- `e(g z)` only depends on the bottom row of `g ∈ SL₂(ℤ)`. -/
lemma ee_smul_eq_of_bottom_row (g h : SL(2, ℤ)) (h10 : g 1 0 = h 1 0) (h11 : g 1 1 = h 1 1)
    (z : ℍ) : ee ((h • z : ℍ) : ℂ) = ee ((g • z : ℍ) : ℂ) := by
  have hk : ((h * g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
    simp [Matrix.adjugate_fin_two]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp [← h10, ← h11]
    ring
  obtain ⟨n, hn⟩ := exists_eq_T_zpow_of_c_eq_zero hk
  have : h = (h * g⁻¹) * g := by group
  rw [this, mul_smul, hn, modular_T_zpow_smul]
  rw [show (((n : ℝ) +ᵥ (g • z) : ℍ) : ℂ) = (n : ℂ) + ((g • z : ℍ) : ℂ) by
    simp [UpperHalfPlane.coe_vadd]]
  rw [ee_add, ee_intCast, one_mul]

/-- A matrix in `SL₂(ℤ)` with bottom row `v` (for coprime `v`; `1` otherwise). -/
noncomputable def gOf (v : Fin 2 → ℤ) : SL(2, ℤ) :=
  if h : IsCoprime (v 0) (v 1) then (bottom_row_surj (R := ℤ) (Set.mem_setOf.mpr h)).choose else 1

lemma gOf_row (v : Fin 2 → ℤ) (h : IsCoprime (v 0) (v 1)) :
    (gOf v) 1 0 = v 0 ∧ (gOf v) 1 1 = v 1 := by
  have hs := (bottom_row_surj (R := ℤ) (Set.mem_setOf.mpr h)).choose_spec.2
  simp only [gOf, dif_pos h]
  exact ⟨congrFun hs 0, congrFun hs 1⟩

/-- The `v`-term of the Poincaré series over coprime pairs: `(cz+d)^{-12} e(γ_v z)`. -/
noncomputable def pTerm (v : Fin 2 → ℤ) (z : ℍ) : ℂ :=
  eisSummand 12 v z * ee ((gOf v • z : ℍ) : ℂ)

/-- `e(γ_v z) = e(g z)` for any `g` with bottom row `v`. -/
lemma ee_gOf (v : Fin 2 → ℤ) (hv : IsCoprime (v 0) (v 1)) (g : SL(2, ℤ)) (h10 : g 1 0 = v 0)
    (h11 : g 1 1 = v 1) (z : ℍ) : ee ((gOf v • z : ℍ) : ℂ) = ee ((g • z : ℍ) : ℂ) := by
  obtain ⟨a, b⟩ := gOf_row v hv
  exact ee_smul_eq_of_bottom_row g (gOf v) (by rw [h10, a]) (by rw [h11, b]) z

lemma pTerm_smul (v : Fin 2 → ℤ) (hv : v ∈ gammaSet 1 1 0) (γ : SL(2, ℤ)) (z : ℍ) :
    pTerm v (γ • z) = (denom γ z) ^ (12 : ℤ) * pTerm (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) z := by
  have hv' : IsCoprime (v 0) (v 1) := (mem_gammaSet_one v).mp hv
  have hw : v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ) ∈ gammaSet 1 1 0 := by
    have := vecMul_SL2_mem_gammaSet hv γ
    simpa using this
  have hw' : IsCoprime ((v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) 0) ((v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) 1) := (mem_gammaSet_one _).mp hw
  unfold pTerm
  rw [eisSummand_SL2_apply, ← mul_smul]
  obtain ⟨r0, r1⟩ := gOf_row v hv'
  have e := ee_gOf (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) hw' (gOf v * γ)
    (by simp [Matrix.mul_apply, Fin.sum_univ_two, vecMul,
      dotProduct, r0, r1])
    (by simp [Matrix.mul_apply, Fin.sum_univ_two, vecMul,
      dotProduct, r0, r1]) z
  rw [← e]; ring

/-- The Poincaré series as a sum over all coprime pairs (it equals `2 · poincare`). -/
noncomputable def pSeries (z : ℍ) : ℂ := ∑' v : gammaSet 1 1 0, pTerm v z

lemma pSeries_smul (γ : SL(2, ℤ)) (z : ℍ) :
    pSeries (γ • z) = (denom γ z) ^ (12 : ℤ) * pSeries z := by
  unfold pSeries
  rw [← tsum_mul_left]
  calc ∑' v : gammaSet 1 1 0, pTerm v (γ • z)
      = ∑' v : gammaSet 1 1 0, (denom γ z) ^ (12 : ℤ) * pTerm (v.1 ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) z :=
        tsum_congr fun v => pTerm_smul v.1 v.2 γ z
    _ = ∑' v : gammaSet 1 1 0, (denom γ z) ^ (12 : ℤ) * pTerm v.1 z :=
        ((gammaSetEquiv 0 γ).trans (gammaSet_one_equiv 1 _ 0)).tsum_eq
          (fun v => (denom γ z) ^ (12 : ℤ) * pTerm v.1 z)

end RamanujanTau.TauBound
