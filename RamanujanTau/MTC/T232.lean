/-
# The theta-quotient term `θ_{2,1}(x, y, q)` of HM Theorem 0.3 and its functional equation

For `n = 2, p = 1` the double sum over `r*, s* < p` has the single term `r* = s* = 0` (`r = s = 1/2`):

`θ_{2,1} = J_5³ · Tn / Td`, `Tn = q² y² j(−x²/y²; q²) j(q⁸ x y; q⁵)`, `Td = j(−q⁴ y³/x²; q⁵) j(−q⁴ x³/y²; q⁵)`,

and `x ↦ q⁵x` maps `Tn/Td` to `μ_D x² Tn/Td` (`T_shift`, cross-multiplied; `thV_FE`).
-/
import RamanujanTau.MTC.F232

set_option autoImplicit false

namespace MTC.H232
open ALz HahnSeries Finset MTC

section T232
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

omit hqe in
lemma h5 (hqe : 1 ≤ qe) : 1 ≤ 5 * qe := by omega

def eTn : ℤ := qe * 2 + ey * 2
noncomputable def cTn : ℂ := cy ^ (2 : ℤ)
def e1T (ex : ℤ) : ℤ := 2 * ex - 2 * ey
noncomputable def c1T (cx : ℂ) : ℂ := -(cx ^ (2 : ℤ) * cy ^ (-2 : ℤ))
def e2T (ex : ℤ) : ℤ := qe * 8 + ex + ey
noncomputable def c2T (cx : ℂ) : ℂ := cx * cy
def eAT (ex : ℤ) : ℤ := qe * 4 + 3 * ey - 2 * ex
noncomputable def cAT (cx : ℂ) : ℂ := -(cy ^ (3 : ℤ) * cx ^ (-2 : ℤ))
def eBT (ex : ℤ) : ℤ := qe * 4 + 3 * ex - 2 * ey
noncomputable def cBT (cx : ℂ) : ℂ := -(cx ^ (3 : ℤ) * cy ^ (-2 : ℤ))

noncomputable def Tn (ex : ℤ) (cx : ℂ) : L :=
  mono (eTn (qe := qe) ey) (cTn cy) * θ (h2qe hqe) (e1T ey ex) (c1T cy cx) *
    θ (h5 hqe) (e2T (qe := qe) ey ex) (c2T cy cx)

noncomputable def Td (ex : ℤ) (cx : ℂ) : L :=
  θ (h5 hqe) (eAT (qe := qe) ey ex) (cAT cy cx) * θ (h5 hqe) (eBT (qe := qe) ey ex) (cBT cy cx)

lemma c1T_ne {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) : c1T cy cx ≠ 0 := by
  unfold c1T; exact neg_ne_zero.mpr (mul_ne_zero (zpow_ne_zero _ hcx) (zpow_ne_zero _ hcy))
lemma c2T_ne {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) : c2T cy cx ≠ 0 := by
  unfold c2T; exact mul_ne_zero hcx hcy
lemma cAT_ne {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) : cAT cy cx ≠ 0 := by
  unfold cAT; exact neg_ne_zero.mpr (mul_ne_zero (zpow_ne_zero _ hcy) (zpow_ne_zero _ hcx))
lemma cBT_ne {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) : cBT cy cx ≠ 0 := by
  unfold cBT; exact neg_ne_zero.mpr (mul_ne_zero (zpow_ne_zero _ hcx) (zpow_ne_zero _ hcy))

include hqe in
theorem T_shift (hcy : cy ≠ 0) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    Tn hqe ey cy (ex + 5 * qe) cx * Td hqe ey cy ex cx =
      muD (qe := qe) ey cy * mono (2 * ex) (cx ^ (2 : ℤ)) * Tn hqe ey cy ex cx * Td hqe ey cy (ex + 5 * qe) cx := by
  have hc1 := c1T_ne cy hcx hcy
  have hc2 := c2T_ne cy hcx hcy
  have hcA := cAT_ne cy hcx hcy
  have hcB := cBT_ne cy hcx hcy
  have r1 : e1T ey (ex + 5 * qe) = e1T ey ex + ((2 * qe : ℕ) : ℤ) * 5 := by unfold e1T; push_cast; ring
  have r2 : e2T (qe := qe) ey (ex + 5 * qe) = e2T (qe := qe) ey ex + ((5 * qe : ℕ) : ℤ) * 1 := by
    unfold e2T; push_cast; ring
  have rA : eAT (qe := qe) ey (ex + 5 * qe) = eAT (qe := qe) ey ex + ((5 * qe : ℕ) : ℤ) * (-2) := by
    unfold eAT; push_cast; ring
  have rB : eBT (qe := qe) ey (ex + 5 * qe) = eBT (qe := qe) ey ex + ((5 * qe : ℕ) : ℤ) * 3 := by
    unfold eBT; push_cast; ring
  unfold Tn Td
  rw [r1, r2, rA, rB, θ_qshift (h2qe hqe) _ hc1 5, θ_qshift (h5 hqe) _ hc2 1, θ_qshift (h5 hqe) _ hcA (-2),
    θ_qshift (h5 hqe) _ hcB 3]
  have hm : mono (eTn (qe := qe) ey) (cTn cy) *
      mono (-(((2 * qe : ℕ) : ℤ) * c2 (5 + 1)) - e1T ey ex * 5 + ((2 * qe : ℕ) : ℤ) * 5) ((-1) ^ (5 : ℤ) * c1T cy cx ^ (-(5 : ℤ))) *
      mono (-(((5 * qe : ℕ) : ℤ) * c2 (1 + 1)) - e2T (qe := qe) ey ex * 1 + ((5 * qe : ℕ) : ℤ) * 1)
        ((-1) ^ (1 : ℤ) * c2T cy cx ^ (-(1 : ℤ))) =
      muD (qe := qe) ey cy * mono (2 * ex) (cx ^ (2 : ℤ)) * mono (eTn (qe := qe) ey) (cTn cy) *
      mono (-(((5 * qe : ℕ) : ℤ) * c2 (-2 + 1)) - eAT (qe := qe) ey ex * (-2) + ((5 * qe : ℕ) : ℤ) * (-2))
        ((-1) ^ (-2 : ℤ) * cAT cy cx ^ (-(-2 : ℤ))) *
      mono (-(((5 * qe : ℕ) : ℤ) * c2 (3 + 1)) - eBT (qe := qe) ey ex * 3 + ((5 * qe : ℕ) : ℤ) * 3)
        ((-1) ^ (3 : ℤ) * cBT cy cx ^ (-(3 : ℤ))) := by
    unfold muD
    simp only [mono_mul]
    apply mono_ext
    · rw [show c2 (5 + 1) = 15 by decide, show c2 (1 + 1) = 1 by decide, show c2 (-2 + 1) = 1 by decide,
        show c2 (3 + 1) = 6 by decide]
      unfold eTn e1T e2T eAT eBT
      push_cast; ring
    · unfold cTn c1T c2T cAT cBT
      simp only [zpow_neg, neg_neg, zpow_ofNat, zpow_one]
      field_simp
      try ring
  linear_combination (θ (h2qe hqe) (e1T ey ex) (c1T cy cx) * θ (h5 hqe) (e2T (qe := qe) ey ex) (c2T cy cx) *
    θ (h5 hqe) (eAT (qe := qe) ey ex) (cAT cy cx) * θ (h5 hqe) (eBT (qe := qe) ey ex) (cBT cy cx)) * hm

/-- `θ_{2,1}(x, y, q) / J_5³`. -/
noncomputable def thV (ex : ℤ) (cx : ℂ) : L := Tn hqe ey cy ex cx / Td hqe ey cy ex cx

include hqe in
/-- **HM Lemma 5.9** for `θ_{2,1}`. -/
theorem thV_FE (hcy : cy ≠ 0) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0)
    (hd0 : Td hqe ey cy ex cx ≠ 0) (hd1 : Td hqe ey cy (ex + 5 * qe) cx ≠ 0) :
    thV hqe ey cy (ex + 5 * qe) cx = muD (qe := qe) ey cy * mono (2 * ex) (cx ^ (2 : ℤ)) * thV hqe ey cy ex cx := by
  unfold thV
  rw [← mul_div_assoc, div_eq_div_iff hd1 hd0]
  linear_combination T_shift hqe ey cy hcy ex hcx

end T232

end MTC.H232
