/-
# The 13-dissection of Euler's product, in `ℤ⟦q⟧`

`E(q) = E(q¹⁶⁹)·(c₀ + q c₁ + q² c₂ + q⁵ c₅ + q⁷ + q⁹ c₉ + q¹² c₁₂)(q¹³)` (`Atkin13Defs`).
Transported from `ALz13.E_dissect` (at `q = t`) along the injective embedding `ιN`.
-/
import RamanujanTau.Atkin13Dissect
import RamanujanTau.Atkin13Defs
import RamanujanTau.Atkin11DissectPS
import RamanujanTau.MTC.ProdId
import RamanujanTau.MTC.LemC
import RamanujanTau.MTC.Hecke373
import RamanujanTau.MTC.Final0
import RamanujanTau.ALNewForm

set_option autoImplicit false

namespace Atkin13
open PowerSeries ALz ALz13 RankProof
open Atkin11 (PS E1 h1' h3' ιN1_inv X_ι)

section Transfer
open MTC

lemma h169 : 1 ≤ 169 := by norm_num
lemma h507 : 1 ≤ 3 * 169 := by norm_num

lemma ιN1_V (f : PS) : ιN h1' (V f) = ιN (show 1 ≤ 13 by norm_num) f :=
  (ιN_Ea h1' (by norm_num) (by norm_num) f).symm

lemma ιN1_VV (f : PS) : ιN h1' (V (V f)) = ιN h169 f :=
  (ιN1_V (V f)).trans (ιN_Ea (show 1 ≤ 13 by norm_num) (by norm_num) (by norm_num : 1 ≤ 13 * 13) f).symm

lemma E169_ι : ιN h1' E169 = Pt h507 13 13 := by
  have h := θ_eq_ιN_prod (d := 169) (a := 3) (b := 1) h169 le_rfl (by norm_num) (by norm_num)
  rw [θ_congrN (show 169 * 3 = 3 * 169 by norm_num) _ h507] at h
  rw [show ((169 * 1 : ℕ) : ℤ) = ((13 : ℕ) : ℤ) * 13 by norm_num] at h
  rw [Pt, E169, ιN1_VV, Atkin11.E1, ← Pinf_one_one, ALz.Pinf_split3]
  simpa [Finset.prod_range_succ, mul_assoc] using h.symm

lemma hd169 : 169 = 13 * 13 := by norm_num
lemma hd13 : 13 = 13 * 1 := by norm_num

lemma J_ι (a : ℕ) (h0 : 1 ≤ a) (h1 : a < 13) :
    ALz13.Jt h169 hd169 (a : ℤ) = ιN h1' (V (ηP a)) * ιN h1' (V (Pinf 13 13)) := by
  have h := θ_eq_ιN_prod (d := 13) (a := 13) (b := a) (by norm_num) h0 h1 (by norm_num)
  rw [θ_congrN (show 13 * 13 = 169 by norm_num) _ h169] at h
  rw [ALz13.Jt, ← map_mul, ← map_mul V, ιN1_V, ηP, show ((13 : ℕ) : ℤ) * (a : ℤ) = ((13 * a : ℕ) : ℤ) by push_cast; ring, h]

lemma ιN1_V_inv {f : PS} (hf : IsUnit f) : ιN h1' (V (Ring.inverse f)) = (ιN h1' (V f))⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, ← map_mul, Ring.inverse_mul_cancel _ hf, map_one, map_one])

/-- **The 13-dissection of `E(q) = (q;q)_∞`** in `ℤ⟦q⟧`. -/
theorem E_dissect_PS :
    Atkin11.E1 = E169 * (V c0 + X * V c1 + X ^ 2 * V c2 + X ^ 5 * V c5 + X ^ 7 + X ^ 9 * V c9 + X ^ 12 * V c12) := by
  apply MTC.ιN_injective h1'
  have hL := E_dissect h169 hd169 hd13 h507 h3'
  have j1 := J_ι 1 le_rfl (by norm_num)
  have j2 := J_ι 2 (by norm_num) (by norm_num)
  have j3 := J_ι 3 (by norm_num) (by norm_num)
  have j4 := J_ι 4 (by norm_num) (by norm_num)
  have j5 := J_ι 5 (by norm_num) (by norm_num)
  have j6 := J_ι 6 (by norm_num) (by norm_num)
  push_cast at j1 j2 j3 j4 j5 j6
  have hX : mono ((1 : ℕ) : ℤ) 1 = ιN h1' X := (MTC.ιN_X h1').symm
  rw [← Atkin11.E1_ι, ← E169_ι, j1, j2, j3, j4, j5, j6, hX] at hL
  have hB : ιN h1' (V (Pinf 13 13)) ≠ 0 := ((isUnit_Pinf 13 13 (by norm_num) (by norm_num)).map _).map _ |>.ne_zero
  simp only [mul_div_mul_right _ _ hB] at hL
  simp only [c0, c1, c2, c5, c9, c12, map_mul, map_add, map_neg, map_pow,
    ιN1_V_inv (isUnit_ηP (a := 1) le_rfl (by norm_num)), ιN1_V_inv (isUnit_ηP (a := 2) (by norm_num) (by norm_num)),
    ιN1_V_inv (isUnit_ηP (a := 3) (by norm_num) (by norm_num)), ιN1_V_inv (isUnit_ηP (a := 4) (by norm_num) (by norm_num)),
    ιN1_V_inv (isUnit_ηP (a := 5) (by norm_num) (by norm_num)), ιN1_V_inv (isUnit_ηP (a := 6) (by norm_num) (by norm_num))]
  rw [hL]
  have hVX : ιN h1' (V X) = ιN h1' X ^ 13 := by
    rw [V_X, map_pow]
  rw [hVX]
  push_cast
  ring

end Transfer

end Atkin13
