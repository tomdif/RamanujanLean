/-
# The 11-dissection of Euler's product, in `ℤ⟦q⟧`

`E(q) = E(q¹²¹)·(c₀ + q c₁ + q² c₂ + q⁴ c₄ + q⁵ + q⁷ c₇)(q¹¹)` with `η_a = (Q^a;Q¹¹)(Q^{11−a};Q¹¹)` and
`c₀ = η₄/η₂`, `c₁ = −η₂/η₁`, `c₂ = −η₅/η₃`, `c₄ = −Q η₁/η₅`, `c₇ = η₃/η₄`.
Transported from `ALz11.E_dissect` (at `q = t`) along the injective embedding `ιN`.
-/
import RamanujanTau.Atkin11Dissect
import RamanujanTau.Atkin11Defs
import RamanujanTau.Atkin11CDefs
import RamanujanTau.MTC.ProdId
import RamanujanTau.MTC.LemC
import RamanujanTau.MTC.Hecke373
import RamanujanTau.MTC.Final0
import RamanujanTau.ALNewForm

set_option autoImplicit false

namespace Atkin11
open PowerSeries ALz ALz11 RankProof

section Transfer
open MTC

lemma h1' : 1 ≤ 1 := le_rfl
lemma h121 : 1 ≤ 121 := by norm_num
lemma h363 : 1 ≤ 3 * 121 := by norm_num
lemma h3' : 1 ≤ 3 * 1 := by norm_num

lemma ιN1_inv {f : PS} (hf : IsUnit f) : ιN h1' (Ring.inverse f) = (ιN h1' f)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, Ring.inverse_mul_cancel _ hf, map_one])

lemma ιN1_V (f : PS) : ιN h1' (V f) = ιN (show 1 ≤ 11 by norm_num) f :=
  (ιN_Ea h1' (by norm_num) (by norm_num) f).symm

lemma ιN1_VV (f : PS) : ιN h1' (V (V f)) = ιN h121 f :=
  (ιN1_V (V f)).trans (ιN_Ea (show 1 ≤ 11 by norm_num) (by norm_num) (by norm_num : 1 ≤ 11 * 11) f).symm

lemma E1_ι : ιN h1' E1 = θ h3' ((1 : ℕ) : ℤ) 1 := by
  have h := θ_eq_ιN_prod (d := 1) (a := 3) (b := 1) h1' le_rfl (by norm_num) (by norm_num)
  rw [θ_congrN (show 1 * 3 = 3 * 1 by norm_num) _ h3'] at h
  rw [show ((1 * 1 : ℕ) : ℤ) = (1 : ℕ) by norm_num] at h
  rw [E1, ← Pinf_one_one, ALz.Pinf_split3]
  simpa [Finset.prod_range_succ, mul_assoc] using h.symm

lemma E121_ι : ιN h1' E121 = Pt h363 11 11 := by
  have h := θ_eq_ιN_prod (d := 121) (a := 3) (b := 1) h121 le_rfl (by norm_num) (by norm_num)
  rw [θ_congrN (show 121 * 3 = 3 * 121 by norm_num) _ h363] at h
  rw [show ((121 * 1 : ℕ) : ℤ) = ((11 : ℕ) : ℤ) * 11 by norm_num] at h
  rw [Pt, E121, ιN1_VV, E1, ← Pinf_one_one, ALz.Pinf_split3]
  simpa [Finset.prod_range_succ, mul_assoc] using h.symm

lemma hd121 : 121 = 11 * 11 := by norm_num
lemma hd11 : 11 = 11 * 1 := by norm_num

lemma J_ι (a : ℕ) (h0 : 1 ≤ a) (h1 : a < 11) :
    ALz11.Jt h121 hd121 (a : ℤ) = ιN h1' (V (ηP a)) * ιN h1' (V (Pinf 11 11)) := by
  have h := θ_eq_ιN_prod (d := 11) (a := 11) (b := a) (by norm_num) h0 h1 (by norm_num)
  rw [θ_congrN (show 11 * 11 = 121 by norm_num) _ h121] at h
  rw [ALz11.Jt, ← map_mul, ← map_mul V, ιN1_V, ηP, show ((11 : ℕ) : ℤ) * (a : ℤ) = ((11 * a : ℕ) : ℤ) by push_cast; ring, h]

lemma X_ι : ιN h1' X = mono 1 1 := by
  have := MTC.ιN_X h1'
  simpa using this

lemma ιN1_V_inv {f : PS} (hf : IsUnit f) : ιN h1' (V (Ring.inverse f)) = (ιN h1' (V f))⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, ← map_mul, Ring.inverse_mul_cancel _ hf, map_one, map_one])

/-- **The 11-dissection of `E(q) = (q;q)_∞`** in `ℤ⟦q⟧`. -/
theorem E_dissect_PS :
    E1 = E121 * (V cP0 + X * V cP1 + X ^ 2 * V cP2 + X ^ 4 * V cP4 + X ^ 5 + X ^ 7 * V cP7) := by
  apply MTC.ιN_injective h1'
  have hL := E_dissect h121 hd121 hd11 h363 h3'
  have j1 := J_ι 1 le_rfl (by norm_num)
  have j2 := J_ι 2 (by norm_num) (by norm_num)
  have j3 := J_ι 3 (by norm_num) (by norm_num)
  have j4 := J_ι 4 (by norm_num) (by norm_num)
  have j5 := J_ι 5 (by norm_num) (by norm_num)
  push_cast at j1 j2 j3 j4 j5
  have hX : mono ((1 : ℕ) : ℤ) 1 = ιN h1' X := (MTC.ιN_X h1').symm
  rw [← E1_ι, ← E121_ι, j1, j2, j3, j4, j5, hX] at hL
  have hB : ιN h1' (V (Pinf 11 11)) ≠ 0 := ((isUnit_Pinf 11 11 (by norm_num) (by norm_num)).map _).map _ |>.ne_zero
  simp only [mul_div_mul_right _ _ hB] at hL
  simp only [cP0, cP1, cP2, cP4, cP7, map_mul, map_add, map_neg, map_pow, ιN1_V_inv (isUnit_ηP (a := 1) le_rfl (by norm_num)),
    ιN1_V_inv (isUnit_ηP (a := 2) (by norm_num) (by norm_num)), ιN1_V_inv (isUnit_ηP (a := 3) (by norm_num) (by norm_num)),
    ιN1_V_inv (isUnit_ηP (a := 4) (by norm_num) (by norm_num)), ιN1_V_inv (isUnit_ηP (a := 5) (by norm_num) (by norm_num))]
  rw [hL]
  have hVX : ιN h1' (V X) = ιN h1' X ^ 11 := by
    rw [show V X = X ^ 11 from by simp [ex], map_pow]
  rw [hVX]
  push_cast
  ring

end Transfer

end Atkin11
