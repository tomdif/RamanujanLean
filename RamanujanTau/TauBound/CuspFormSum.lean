/-
# `pSeries = 2 · poincare`

Split the sum over coprime `(c,d) ∈ ℤ²` into `c = 0` (`d = ±1`, giving `2 e(z)`), `c > 0` (the terms
`poincareTerm c d z`, via `a ≡ d̄ mod c` for the top-left entry `a` of `γ_v`) and `c < 0`
(equal to the `c > 0` part since `pTerm (-v) = pTerm v`).
-/
import RamanujanTau.TauBound.CuspFormSlash
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.IsBoundedAtImInfty

set_option autoImplicit false

namespace RamanujanTau.TauBound

open Complex UpperHalfPlane ModularGroup EisensteinSeries Matrix
open scoped MatrixGroups

lemma norm_ee_smul_le_one (g : SL(2, ℤ)) (z : ℍ) : ‖ee ((g • z : ℍ) : ℂ)‖ ≤ 1 :=
  norm_ee_le_one (by rw [UpperHalfPlane.coe_im]; exact (g • z).im_pos.le)

lemma norm_pTerm_le (v : Fin 2 → ℤ) (z : ℍ) : ‖pTerm v z‖ ≤ ‖eisSummand 12 v z‖ := by
  unfold pTerm
  rw [norm_mul]
  calc ‖eisSummand 12 v z‖ * ‖ee ((gOf v • z : ℍ) : ℂ)‖ ≤ ‖eisSummand 12 v z‖ * 1 := by
        gcongr; exact norm_ee_smul_le_one _ _
    _ = _ := mul_one _

/-- `pTerm` restricted to coprime pairs (zero elsewhere). -/
noncomputable def pInd (v : Fin 2 → ℤ) (z : ℍ) : ℂ :=
  if IsCoprime (v 0) (v 1) then pTerm v z else 0

lemma summable_pInd (z : ℍ) : Summable (fun v => pInd v z) := by
  refine Summable.of_norm_bounded (summable_norm_eisSummand (k := 12) (by norm_num) z) (fun v => ?_)
  unfold pInd
  split_ifs
  · exact norm_pTerm_le v z
  · rw [norm_zero]; exact norm_nonneg _

lemma pSeries_eq_tsum_pInd (z : ℍ) : pSeries z = ∑' v, pInd v z := by
  unfold pSeries
  rw [tsum_subtype (gammaSet 1 1 0) (fun v => pTerm v z)]
  congr 1
  funext v
  unfold pInd
  by_cases h : IsCoprime (v 0) (v 1)
  · rw [if_pos h, Set.indicator_of_mem ((mem_gammaSet_one v).mpr h)]
  · rw [if_neg h, Set.indicator_of_notMem (fun h' => h ((mem_gammaSet_one v).mp h'))]

lemma pInd_neg (v : Fin 2 → ℤ) (z : ℍ) : pInd (-v) z = pInd v z := by
  unfold pInd
  simp only [Pi.neg_apply, IsCoprime.neg_neg_iff]
  split_ifs with hv
  · unfold pTerm
    have e1 : eisSummand 12 (-v) z = eisSummand 12 v z := by
      unfold eisSummand
      rw [show ((-v) 0 : ℂ) * (z : ℂ) + ((-v) 1 : ℂ) = -((v 0 : ℂ) * z + v 1) by
        simp; ring]
      exact Even.neg_zpow (by decide) _
    have hv' : IsCoprime ((-v) 0) ((-v) 1) := hv.neg_neg
    have e2 : ee ((gOf (-v) • z : ℍ) : ℂ) = ee ((gOf v • z : ℍ) : ℂ) := by
      obtain ⟨r0, r1⟩ := gOf_row v hv
      rw [ee_gOf (-v) hv' (-gOf v) (by simp [r0]) (by simp [r1]), SL_neg_smul]
    rw [e1, e2]
  · rfl

/-- The `c > 0` terms are the terms of `poincare`. -/
lemma pInd_pos (c : ℕ) (hc : c ≠ 0) (d : ℤ) (z : ℍ) :
    pInd ![(c : ℤ), d] z = poincareTerm c d z := by
  unfold pInd poincareTerm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  by_cases h : Int.gcd c d = 1
  · have hcop : IsCoprime (c : ℤ) d := Int.isCoprime_iff_gcd_eq_one.mpr h
    rw [if_pos hcop, if_pos h]
    unfold pTerm
    have e1 : eisSummand 12 ![(c : ℤ), d] z = ((c : ℂ) * z + d) ^ (-12 : ℤ) := by
      simp [eisSummand]
    rw [e1]
    congr 1
    -- the top-left entry `a` of `γ_v` satisfies `a d - b c = 1`
    obtain ⟨r0, r1⟩ := gOf_row ![(c : ℤ), d] (by simpa using hcop)
    set g := gOf ![(c : ℤ), d] with hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at r0 r1
    have hdet : g 0 0 * d - g 0 1 * c = 1 := by
      have := g.det_coe
      rw [Matrix.det_fin_two, r0, r1] at this
      exact this
    haveI : NeZero c := ⟨hc⟩
    set a' : ℕ := ((d : ZMod c)⁻¹).val
    have hinv : (d : ZMod c)⁻¹ = (g 0 0 : ZMod c) := by
      apply ZMod.inv_eq_of_mul_eq_one
      have : ((g 0 0 * d - g 0 1 * c : ℤ) : ZMod c) = 1 := by rw [hdet]; simp
      push_cast at this
      rw [ZMod.natCast_self, mul_zero, sub_zero] at this
      rw [mul_comm]; exact this
    have hdvd : (c : ℤ) ∣ g 0 0 - (a' : ℤ) := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      simp only [Int.cast_natCast, a', ZMod.natCast_zmod_val, hinv]
    obtain ⟨k, hk⟩ := hdvd
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    have hden : (c : ℂ) * (z : ℂ) + d ≠ 0 := by
      have := denom_ne_zero g z
      rw [denom_apply] at this
      simpa [r0, r1] using this
    have hval : ((g • z : ℍ) : ℂ) =
        ((a' : ℂ) / c - 1 / ((c : ℂ) * ((c : ℂ) * z + d))) + (k : ℂ) := by
      rw [coe_specialLinearGroup_apply]
      simp only [algebraMap_int_eq, eq_intCast, Int.cast_natCast] at *
      rw [show ((g 1 0 : ℝ) : ℂ) = c by simp [r0], show ((g 1 1 : ℝ) : ℂ) = d by simp [r1]]
      have ha : ((g 0 0 : ℝ) : ℂ) = a' + c * k := by
        have : (g 0 0 : ℤ) = a' + c * k := by linarith
        rw [this]; push_cast; ring
      have hdet' : ((g 0 0 : ℝ) : ℂ) * d - ((g 0 1 : ℝ) : ℂ) * c = 1 := by
        have : ((g 0 0 * d - g 0 1 * c : ℤ) : ℂ) = 1 := by rw [hdet]; simp
        push_cast at this; exact this
      rw [ha] at hdet' ⊢
      rw [div_eq_iff hden]
      field_simp
      linear_combination -hdet'
    rw [hval, ee_add, ee_intCast, mul_one]
  · have hcop : ¬ IsCoprime (c : ℤ) d := fun h' => h (Int.isCoprime_iff_gcd_eq_one.mp h')
    rw [if_neg hcop, if_neg h]

lemma pInd_zero_one (z : ℍ) : pInd ![0, 1] z = ee z := by
  unfold pInd
  rw [if_pos (by simp [isCoprime_one_right])]
  unfold pTerm
  have e1 : eisSummand 12 ![0, 1] z = 1 := by simp [eisSummand]
  rw [e1, one_mul, ee_gOf ![0, 1] (by simp [isCoprime_one_right]) 1 (by simp) (by simp), one_smul]

lemma pInd_zero (d : ℤ) (hd : d ≠ 1) (hd' : d ≠ -1) (z : ℍ) : pInd ![0, d] z = 0 := by
  unfold pInd
  rw [if_neg]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, isCoprime_zero_left,
    Int.isUnit_iff]
  tauto

/-- `pInd` on `ℤ × ℤ`. -/
noncomputable def pH (z : ℍ) (p : ℤ × ℤ) : ℂ := pInd ![p.1, p.2] z

lemma summable_pH (z : ℍ) : Summable (pH z) :=
  (summable_pInd z).comp_injective (finTwoArrowEquiv ℤ).symm.injective

lemma pSeries_eq_tsum_pH (z : ℍ) : pSeries z = ∑' p : ℤ × ℤ, pH z p := by
  rw [pSeries_eq_tsum_pInd, ← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  rfl

/-- The `c`-th row sum. -/
noncomputable def pF (z : ℍ) (c : ℤ) : ℂ := ∑' d : ℤ, pH z (c, d)

lemma pF_pos (z : ℍ) (n : ℕ) : pF z ((n : ℤ) + 1) = ∑' d : ℤ, poincareTerm (n + 1) d z := by
  refine tsum_congr fun d => ?_
  rw [← pInd_pos (n + 1) (by omega) d z]
  unfold pH
  push_cast
  rfl

lemma pF_neg (z : ℍ) (c : ℤ) : pF z (-c) = pF z c := by
  unfold pF
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun d => ?_
  unfold pH
  rw [← pInd_neg]
  congr 1
  ext i; fin_cases i <;> simp

lemma pF_zero (z : ℍ) : pF z 0 = 2 * ee z := by
  unfold pF
  rw [tsum_eq_sum (s := {1, -1})]
  · rw [Finset.sum_pair (by norm_num)]
    have e : pInd ![0, -1] z = pInd ![0, 1] z := by
      rw [← pInd_neg]; congr 1; ext i; fin_cases i <;> simp
    simp only [pH, e, pInd_zero_one]; ring
  · intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
    exact pInd_zero d hd.1 hd.2 z

/-- **`pSeries = 2 · poincare`.** -/
theorem pSeries_eq_two_mul_poincare (z : ℍ) : pSeries z = 2 * poincare z := by
  have hsum := summable_pH z
  have h2 : ∑' p : ℤ × ℤ, pH z p = ∑' c : ℤ, pF z c :=
    hsum.tsum_prod' (fun c => hsum.prod_factor c)
  have hFs : Summable (pF z) := hsum.prod
  have hs1 : Summable fun n : ℕ => pF z ((n : ℤ) + 1) :=
    hFs.comp_injective (fun a b h => by simpa using h)
  have hs2 : Summable fun n : ℕ => pF z (-((n : ℤ) + 1)) :=
    hFs.comp_injective (fun a b h => by simpa using h)
  rw [pSeries_eq_tsum_pH, h2, tsum_of_add_one_of_neg_add_one hs1 hs2, pF_zero]
  simp only [pF_neg, pF_pos]
  unfold poincare
  ring

end RamanujanTau.TauBound
