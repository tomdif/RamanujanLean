/-
# The theta-quotient term `θ_{3,4}(x, y, q)` of HM Theorem 0.3 and its functional equation

`θ_{3,4} = J_{160}³ Σ_{r,s=0}^{3} T(r,s)`, `T = Tn / Td` with

* `Tn r s = q^{3C(r−1,2)+7(r−1)(s+2)+3C(s+2,2)} (−x)^{r−1} (−y)^{s+2} j(−q^{12(s−r)} x³/y³; q^{48}) j(q^{40(r+s)+28} x⁴y⁴; q^{160})`
* `Td r s = j(q^{40r+14} y⁷/x³; q^{160}) j(q^{40s+14} x⁷/y³; q^{160})`.

The summand is `4`-periodic in `r` and in `s` (`T_per_r`, `T_per_s`), and `x ↦ q^{40}x` maps it to
`q^{66} y^{−7} x³ T(r+1, s+3)` (`T_shift`); all three in cross-multiplied form.
-/
import RamanujanTau.MTC.F373

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

section T373
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

omit hqe in
lemma h48 (hqe : 1 ≤ qe) : 1 ≤ 48 * qe := by omega
omit hqe in
lemma h160 (hqe : 1 ≤ qe) : 1 ≤ 160 * qe := by omega

def eTn (r s ex : ℤ) : ℤ := qe * (3 * c2 (r - 1) + 7 * (r - 1) * (s + 2) + 3 * c2 (s + 2)) + ex * (r - 1) + ey * (s + 2)
noncomputable def cTn (r s : ℤ) (cx : ℂ) : ℂ := (-cx) ^ (r - 1) * (-cy) ^ (s + 2)
def e1T (r s ex : ℤ) : ℤ := qe * (12 * (s - r)) + 3 * ex - 3 * ey
noncomputable def c1T (cx : ℂ) : ℂ := -(cx ^ (3 : ℤ) * cy ^ (-3 : ℤ))
def e2T (r s ex : ℤ) : ℤ := qe * (40 * (r + s) + 28) + 4 * ex + 4 * ey
noncomputable def c2T (cx : ℂ) : ℂ := cx ^ (4 : ℤ) * cy ^ (4 : ℤ)
def eAT (r ex : ℤ) : ℤ := qe * (40 * r + 14) + 7 * ey - 3 * ex
noncomputable def cAT (cx : ℂ) : ℂ := cy ^ (7 : ℤ) * cx ^ (-3 : ℤ)
def eBT (s ex : ℤ) : ℤ := qe * (40 * s + 14) + 7 * ex - 3 * ey
noncomputable def cBT (cx : ℂ) : ℂ := cx ^ (7 : ℤ) * cy ^ (-3 : ℤ)

/-- numerator of the `(r,s)` summand (without `J_{160}³`). -/
noncomputable def Tn (r s ex : ℤ) (cx : ℂ) : L :=
  mono (eTn (qe := qe) ey r s ex) (cTn cy r s cx) * θ (h48 hqe) (e1T (qe := qe) ey r s ex) (c1T cy cx) *
    θ (h160 hqe) (e2T (qe := qe) ey r s ex) (c2T cy cx)

/-- denominator of the `(r,s)` summand. -/
noncomputable def Td (r s ex : ℤ) (cx : ℂ) : L :=
  θ (h160 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx) * θ (h160 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)

lemma c2_val3 : c2 (2 + 1) = 3 := by decide
lemma c2_val0 : c2 (-1 + 1) = 0 := by decide
lemma c2_val2 : c2 (1 + 1) = 1 := by decide

include hqe in
/-- **`x ↦ q^{40} x` shifts the summand**, cross-multiplied. -/
theorem T_shift (hcy : cy ≠ 0) (r s ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    Tn hqe ey cy r s (ex + 40 * qe) cx * Td hqe ey cy (r + 1) (s + 3) ex cx =
      muD (qe := qe) ey cy * mono (3 * ex) (cx ^ (3 : ℤ)) * Tn hqe ey cy (r + 1) (s + 3) ex cx *
        Td hqe ey cy r s (ex + 40 * qe) cx := by
  have hc1 : c1T cy cx ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (zpow_ne_zero _ hcx) (zpow_ne_zero _ hcy))
  have hcA : cAT cy cx ≠ 0 := mul_ne_zero (zpow_ne_zero _ hcy) (zpow_ne_zero _ hcx)
  have hcB : cBT cy cx ≠ 0 := mul_ne_zero (zpow_ne_zero _ hcx) (zpow_ne_zero _ hcy)
  have r1 : e1T (qe := qe) ey r s (ex + 40 * qe) = e1T (qe := qe) ey (r + 1) (s + 3) ex + ((48 * qe : ℕ) : ℤ) * 2 := by
    unfold e1T; push_cast; ring
  have r2 : e2T (qe := qe) ey r s (ex + 40 * qe) = e2T (qe := qe) ey (r + 1) (s + 3) ex := by unfold e2T; ring
  have rA : eAT (qe := qe) ey r (ex + 40 * qe) = eAT (qe := qe) ey (r + 1) ex + ((160 * qe : ℕ) : ℤ) * (-1) := by
    unfold eAT; push_cast; ring
  have rB : eBT (qe := qe) ey s (ex + 40 * qe) = eBT (qe := qe) ey (s + 3) ex + ((160 * qe : ℕ) : ℤ) * 1 := by
    unfold eBT; push_cast; ring
  unfold Tn Td
  rw [r1, r2, rA, rB, θ_qshift (h48 hqe) _ hc1 2, θ_qshift (h160 hqe) _ hcA (-1), θ_qshift (h160 hqe) _ hcB 1]
  have hm : mono (eTn (qe := qe) ey r s (ex + 40 * qe)) (cTn cy r s cx) *
      mono (-(((48 * qe : ℕ) : ℤ) * c2 (2 + 1)) - e1T (qe := qe) ey (r + 1) (s + 3) ex * 2 + ((48 * qe : ℕ) : ℤ) * 2)
        ((-1) ^ (2 : ℤ) * c1T cy cx ^ (-(2 : ℤ))) =
      muD (qe := qe) ey cy * mono (3 * ex) (cx ^ (3 : ℤ)) * mono (eTn (qe := qe) ey (r + 1) (s + 3) ex) (cTn cy (r + 1) (s + 3) cx) *
      mono (-(((160 * qe : ℕ) : ℤ) * c2 (-1 + 1)) - eAT (qe := qe) ey (r + 1) ex * (-1) + ((160 * qe : ℕ) : ℤ) * (-1))
        ((-1) ^ (-1 : ℤ) * cAT cy cx ^ (-(-1 : ℤ))) *
      mono (-(((160 * qe : ℕ) : ℤ) * c2 (1 + 1)) - eBT (qe := qe) ey (s + 3) ex * 1 + ((160 * qe : ℕ) : ℤ) * 1)
        ((-1) ^ (1 : ℤ) * cBT cy cx ^ (-(1 : ℤ))) := by
    unfold muD
    simp only [mono_mul]
    apply mono_ext
    · rw [c2_val3, c2_val0, c2_val2]
      unfold eTn e1T eAT eBT
      have a1 := c2_succ (r - 1); have a2 := c2_succ (s + 2); have a3 := c2_succ (s + 3)
      have a4 := c2_succ (s + 4)
      rw [show r - 1 + 1 = r + 1 - 1 by ring] at a1
      rw [show s + 2 + 1 = s + 3 by ring] at a2
      rw [show s + 3 + 1 = s + 4 by ring] at a3
      rw [show s + 4 + 1 = s + 3 + 2 by ring] at a4
      push_cast
      linear_combination (-(3 * (qe : ℤ))) * a1 + (-(3 * (qe : ℤ))) * (a2 + a3 + a4)
    · unfold cTn c1T cAT cBT
      have e1 : (-cx) ^ (r + 1 - 1) = (-cx) ^ (r - 1) * (-cx) := by
        rw [show r + 1 - 1 = (r - 1) + 1 by ring, zpow_add_one₀ (neg_ne_zero.mpr hcx)]
      have e2 : (-cy) ^ (s + 3 + 2) = (-cy) ^ (s + 2) * (-cy) ^ (3 : ℤ) := by
        rw [show s + 3 + 2 = (s + 2) + 3 by ring, zpow_add₀ (neg_ne_zero.mpr hcy)]
      rw [e1, e2]
      simp only [zpow_neg, neg_neg, zpow_ofNat, zpow_one]
      field_simp
      try ring
  linear_combination (θ (h48 hqe) (e1T (qe := qe) ey (r + 1) (s + 3) ex) (c1T cy cx) *
    θ (h160 hqe) (e2T (qe := qe) ey (r + 1) (s + 3) ex) (c2T cy cx) *
    θ (h160 hqe) (eAT (qe := qe) ey (r + 1) ex) (cAT cy cx) *
    θ (h160 hqe) (eBT (qe := qe) ey (s + 3) ex) (cBT cy cx)) * hm

include hqe in
/-- `4`-periodicity in `r`, cross-multiplied. -/
theorem T_per_r (hcy : cy ≠ 0) (r s ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    Tn hqe ey cy (r + 4) s ex cx * Td hqe ey cy r s ex cx = Tn hqe ey cy r s ex cx * Td hqe ey cy (r + 4) s ex cx := by
  have hc1 : c1T cy cx ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (zpow_ne_zero _ hcx) (zpow_ne_zero _ hcy))
  have hc2 : c2T cy cx ≠ 0 := mul_ne_zero (zpow_ne_zero _ hcx) (zpow_ne_zero _ hcy)
  have hcA : cAT cy cx ≠ 0 := mul_ne_zero (zpow_ne_zero _ hcy) (zpow_ne_zero _ hcx)
  have r1 : e1T (qe := qe) ey (r + 4) s ex = e1T (qe := qe) ey r s ex + ((48 * qe : ℕ) : ℤ) * (-1) := by
    unfold e1T; push_cast; ring
  have r2 : e2T (qe := qe) ey (r + 4) s ex = e2T (qe := qe) ey r s ex + ((160 * qe : ℕ) : ℤ) * 1 := by
    unfold e2T; push_cast; ring
  have rA : eAT (qe := qe) ey (r + 4) ex = eAT (qe := qe) ey r ex + ((160 * qe : ℕ) : ℤ) * 1 := by
    unfold eAT; push_cast; ring
  unfold Tn Td
  rw [r1, r2, rA, θ_qshift (h48 hqe) _ hc1 (-1), θ_qshift (h160 hqe) _ hc2 1, θ_qshift (h160 hqe) _ hcA 1]
  have hm : mono (eTn (qe := qe) ey (r + 4) s ex) (cTn cy (r + 4) s cx) *
      mono (-(((48 * qe : ℕ) : ℤ) * c2 (-1 + 1)) - e1T (qe := qe) ey r s ex * (-1) + ((48 * qe : ℕ) : ℤ) * (-1))
        ((-1) ^ (-1 : ℤ) * c1T cy cx ^ (-(-1 : ℤ))) *
      mono (-(((160 * qe : ℕ) : ℤ) * c2 (1 + 1)) - e2T (qe := qe) ey r s ex * 1 + ((160 * qe : ℕ) : ℤ) * 1)
        ((-1) ^ (1 : ℤ) * c2T cy cx ^ (-(1 : ℤ))) =
      mono (eTn (qe := qe) ey r s ex) (cTn cy r s cx) *
      mono (-(((160 * qe : ℕ) : ℤ) * c2 (1 + 1)) - eAT (qe := qe) ey r ex * 1 + ((160 * qe : ℕ) : ℤ) * 1)
        ((-1) ^ (1 : ℤ) * cAT cy cx ^ (-(1 : ℤ))) := by
    simp only [mono_mul]
    apply mono_ext
    · rw [c2_val0, c2_val2]
      unfold eTn e1T e2T eAT
      have a1 := c2_succ (r - 1); have a2 := c2_succ r; have a3 := c2_succ (r + 1); have a4 := c2_succ (r + 2)
      rw [show r - 1 + 1 = r by ring] at a1
      rw [show r + 1 + 1 = r + 2 by ring] at a3
      rw [show r + 2 + 1 = r + 4 - 1 by ring] at a4
      push_cast
      linear_combination (3 * (qe : ℤ)) * (a1 + a2 + a3 + a4)
    · unfold cTn c1T c2T cAT
      rw [show r + 4 - 1 = (r - 1) + 4 by ring, zpow_add₀ (neg_ne_zero.mpr hcx)]
      simp only [zpow_neg]; field_simp; try ring
  linear_combination (θ (h48 hqe) (e1T (qe := qe) ey r s ex) (c1T cy cx) *
    θ (h160 hqe) (e2T (qe := qe) ey r s ex) (c2T cy cx) *
    θ (h160 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx) *
    θ (h160 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)) * hm

include hqe in
/-- `4`-periodicity in `s`, cross-multiplied. -/
theorem T_per_s (hcy : cy ≠ 0) (r s ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    Tn hqe ey cy r (s + 4) ex cx * Td hqe ey cy r s ex cx = Tn hqe ey cy r s ex cx * Td hqe ey cy r (s + 4) ex cx := by
  have hc1 : c1T cy cx ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (zpow_ne_zero _ hcx) (zpow_ne_zero _ hcy))
  have hc2 : c2T cy cx ≠ 0 := mul_ne_zero (zpow_ne_zero _ hcx) (zpow_ne_zero _ hcy)
  have hcB : cBT cy cx ≠ 0 := mul_ne_zero (zpow_ne_zero _ hcx) (zpow_ne_zero _ hcy)
  have r1 : e1T (qe := qe) ey r (s + 4) ex = e1T (qe := qe) ey r s ex + ((48 * qe : ℕ) : ℤ) * 1 := by
    unfold e1T; push_cast; ring
  have r2 : e2T (qe := qe) ey r (s + 4) ex = e2T (qe := qe) ey r s ex + ((160 * qe : ℕ) : ℤ) * 1 := by
    unfold e2T; push_cast; ring
  have rB : eBT (qe := qe) ey (s + 4) ex = eBT (qe := qe) ey s ex + ((160 * qe : ℕ) : ℤ) * 1 := by
    unfold eBT; push_cast; ring
  unfold Tn Td
  rw [r1, r2, rB, θ_qshift (h48 hqe) _ hc1 1, θ_qshift (h160 hqe) _ hc2 1, θ_qshift (h160 hqe) _ hcB 1]
  have hm : mono (eTn (qe := qe) ey r (s + 4) ex) (cTn cy r (s + 4) cx) *
      mono (-(((48 * qe : ℕ) : ℤ) * c2 (1 + 1)) - e1T (qe := qe) ey r s ex * 1 + ((48 * qe : ℕ) : ℤ) * 1)
        ((-1) ^ (1 : ℤ) * c1T cy cx ^ (-(1 : ℤ))) *
      mono (-(((160 * qe : ℕ) : ℤ) * c2 (1 + 1)) - e2T (qe := qe) ey r s ex * 1 + ((160 * qe : ℕ) : ℤ) * 1)
        ((-1) ^ (1 : ℤ) * c2T cy cx ^ (-(1 : ℤ))) =
      mono (eTn (qe := qe) ey r s ex) (cTn cy r s cx) *
      mono (-(((160 * qe : ℕ) : ℤ) * c2 (1 + 1)) - eBT (qe := qe) ey s ex * 1 + ((160 * qe : ℕ) : ℤ) * 1)
        ((-1) ^ (1 : ℤ) * cBT cy cx ^ (-(1 : ℤ))) := by
    simp only [mono_mul]
    apply mono_ext
    · rw [c2_val2]
      unfold eTn e1T e2T eBT
      have a1 := c2_succ (s + 2); have a2 := c2_succ (s + 3); have a3 := c2_succ (s + 4)
      have a4 := c2_succ (s + 5)
      rw [show s + 2 + 1 = s + 3 by ring] at a1
      rw [show s + 3 + 1 = s + 4 by ring] at a2
      rw [show s + 4 + 1 = s + 5 by ring] at a3
      rw [show s + 5 + 1 = s + 4 + 2 by ring] at a4
      push_cast
      linear_combination (3 * (qe : ℤ)) * (a1 + a2 + a3 + a4)
    · unfold cTn c1T c2T cBT
      rw [show s + 4 + 2 = (s + 2) + 4 by ring, zpow_add₀ (neg_ne_zero.mpr hcy)]
      simp only [zpow_neg]; field_simp; try ring
  linear_combination (θ (h48 hqe) (e1T (qe := qe) ey r s ex) (c1T cy cx) *
    θ (h160 hqe) (e2T (qe := qe) ey r s ex) (c2T cy cx) *
    θ (h160 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx) *
    θ (h160 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)) * hm

/-- reindexing a doubly `4`-periodic function. -/
lemma sum_reindex13 (T : ℤ → ℤ → L) (hr : ∀ r s, T (r + 4) s = T r s) (hs : ∀ r s, T r (s + 4) = T r s) :
    ∑ r ∈ Finset.Icc (0 : ℤ) 3, ∑ s ∈ Finset.Icc (0 : ℤ) 3, T (r + 1) (s + 3) =
      ∑ r ∈ Finset.Icc (0 : ℤ) 3, ∑ s ∈ Finset.Icc (0 : ℤ) 3, T r s := by
  have hI : Finset.Icc (0 : ℤ) 3 = {0, 1, 2, 3} := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; constructor <;> intro h <;> omega
  have h4 : ∀ s, T 4 s = T 0 s := fun s => by simpa using hr 0 s
  have k4 : ∀ r, T r 4 = T r 0 := fun r => by simpa using hs r 0
  have k5 : ∀ r, T r 5 = T r 1 := fun r => by simpa using hs r 1
  have k6 : ∀ r, T r 6 = T r 2 := fun r => by simpa using hs r 2
  rw [hI]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
    Int.reduceAdd, Int.reduceEq, or_self, or_false, false_or, not_false_eq_true, h4, k4, k5, k6]
  ring

/-- `θ_{3,4}(x, y, q) / J_{160}³`. -/
noncomputable def thV (ex : ℤ) (cx : ℂ) : L :=
  ∑ r ∈ Finset.Icc (0 : ℤ) 3, ∑ s ∈ Finset.Icc (0 : ℤ) 3, Tn hqe ey cy r s ex cx / Td hqe ey cy r s ex cx

include hqe in
/-- **HM Lemma 5.9**: `θ_{3,4}(q^{40}x) = q^{66} y^{−7} x³ θ_{3,4}(x)` at points where no denominator vanishes. -/
theorem thV_FE (hcy : cy ≠ 0) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0)
    (hd0 : ∀ r s, Td hqe ey cy r s ex cx ≠ 0) (hd1 : ∀ r s, Td hqe ey cy r s (ex + 40 * qe) cx ≠ 0) :
    thV hqe ey cy (ex + 40 * qe) cx = muD (qe := qe) ey cy * mono (3 * ex) (cx ^ (3 : ℤ)) * thV hqe ey cy ex cx := by
  set T : ℤ → ℤ → L := fun r s => Tn hqe ey cy r s ex cx / Td hqe ey cy r s ex cx
  have hT : ∀ r s, Tn hqe ey cy r s (ex + 40 * qe) cx / Td hqe ey cy r s (ex + 40 * qe) cx =
      muD (qe := qe) ey cy * mono (3 * ex) (cx ^ (3 : ℤ)) * T (r + 1) (s + 3) := by
    intro r s
    have h := T_shift hqe ey cy hcy r s ex hcx
    simp only [T]
    rw [← mul_div_assoc, div_eq_div_iff (hd1 r s) (hd0 (r + 1) (s + 3))]
    linear_combination h
  have hr : ∀ r s, T (r + 4) s = T r s := fun r s => by
    simp only [T]; rw [div_eq_div_iff (hd0 _ _) (hd0 _ _)]; exact T_per_r hqe ey cy hcy r s ex hcx
  have hs : ∀ r s, T r (s + 4) = T r s := fun r s => by
    simp only [T]; rw [div_eq_div_iff (hd0 _ _) (hd0 _ _)]; exact T_per_s hqe ey cy hcy r s ex hcx
  unfold thV
  simp only [hT, ← Finset.mul_sum]
  rw [sum_reindex13 T hr hs]

end T373

end MTC
