/-
# The theta-quotient term `θ_{1,3}(x, y, q)` of HM Theorem 0.3 and its functional equation

`θ_{1,3} = J_{45}³ Σ_{r,s=0}^{2} T(r,s)`, `T = Tn / Td` with

* `Tn r s = q^{C(r,2)+4r(s+1)+C(s+1,2)} (−x)^r (−y)^{s+1} j(−q^{3(s−r)} x/y; q^9) j(q^{15(r+s)+12} x³y³; q^{45})`
* `Td r s = j(−q^{15r+6} y⁴/x; q^{45}) j(−q^{15s+6} x⁴/y; q^{45})`.

The summand is `3`-periodic in `r` and in `s` (`T_per_r`, `T_per_s`), and `x ↦ q^{15}x` maps it to
`μ_D x T(r+2, s+1)` (`T_shift`); all three in cross-multiplied form.
-/
import RamanujanTau.MTC.F141
import RamanujanTau.MTC.UDecL

set_option autoImplicit false

namespace MTC.H141
open ALz HahnSeries Finset MTC

section T141
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

omit hqe in
lemma h9 (hqe : 1 ≤ qe) : 1 ≤ 9 * qe := by omega
omit hqe in
lemma h45 (hqe : 1 ≤ qe) : 1 ≤ 45 * qe := by omega

def eTn (r s ex : ℤ) : ℤ := qe * (c2 r + 4 * r * (s + 1) + c2 (s + 1)) + ex * r + ey * (s + 1)
noncomputable def cTn (r s : ℤ) (cx : ℂ) : ℂ := (-cx) ^ r * (-cy) ^ (s + 1)
def e1T (r s ex : ℤ) : ℤ := qe * (3 * (s - r)) + ex - ey
noncomputable def c1T (cx : ℂ) : ℂ := -(cx * cy ^ (-1 : ℤ))
def e2T (r s ex : ℤ) : ℤ := qe * (15 * (r + s) + 12) + 3 * ex + 3 * ey
noncomputable def c2T (cx : ℂ) : ℂ := cx ^ (3 : ℤ) * cy ^ (3 : ℤ)
def eAT (r ex : ℤ) : ℤ := qe * (15 * r + 6) + 4 * ey - ex
noncomputable def cAT (cx : ℂ) : ℂ := -(cy ^ (4 : ℤ) * cx ^ (-1 : ℤ))
def eBT (s ex : ℤ) : ℤ := qe * (15 * s + 6) + 4 * ex - ey
noncomputable def cBT (cx : ℂ) : ℂ := -(cx ^ (4 : ℤ) * cy ^ (-1 : ℤ))

/-- numerator of the `(r,s)` summand (without `J_{45}³`). -/
noncomputable def Tn (r s ex : ℤ) (cx : ℂ) : L :=
  mono (eTn (qe := qe) ey r s ex) (cTn cy r s cx) * θ (h9 hqe) (e1T (qe := qe) ey r s ex) (c1T cy cx) *
    θ (h45 hqe) (e2T (qe := qe) ey r s ex) (c2T cy cx)

/-- denominator of the `(r,s)` summand. -/
noncomputable def Td (r s ex : ℤ) (cx : ℂ) : L :=
  θ (h45 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx) * θ (h45 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)

lemma c1T_ne {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) : c1T cy cx ≠ 0 := by
  unfold c1T; exact neg_ne_zero.mpr (mul_ne_zero hcx (zpow_ne_zero _ hcy))
lemma c2T_ne {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) : c2T cy cx ≠ 0 := by
  unfold c2T; exact mul_ne_zero (zpow_ne_zero _ hcx) (zpow_ne_zero _ hcy)
lemma cAT_ne {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) : cAT cy cx ≠ 0 := by
  unfold cAT; exact neg_ne_zero.mpr (mul_ne_zero (zpow_ne_zero _ hcy) (zpow_ne_zero _ hcx))
lemma cBT_ne {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) : cBT cy cx ≠ 0 := by
  unfold cBT; exact neg_ne_zero.mpr (mul_ne_zero (zpow_ne_zero _ hcx) (zpow_ne_zero _ hcy))

lemma c2_add2 (r : ℤ) : c2 (r + 2) = c2 r + 2 * r + 1 := by rw [c2_add]; norm_num [c2]; ring
lemma c2_add1 (r : ℤ) : c2 (r + 1) = c2 r + r := by rw [c2_add]; norm_num [c2]
lemma c2_add3 (r : ℤ) : c2 (r + 3) = c2 r + 3 * r + 3 := by rw [c2_add]; norm_num [c2]; ring

include hqe in
/-- **`x ↦ q^{15} x` shifts the summand**, cross-multiplied. -/
theorem T_shift (hcy : cy ≠ 0) (r s ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    Tn hqe ey cy r s (ex + 15 * qe) cx * Td hqe ey cy (r + 2) (s + 1) ex cx =
      muD (qe := qe) ey cy * mono ex cx * Tn hqe ey cy (r + 2) (s + 1) ex cx *
        Td hqe ey cy r s (ex + 15 * qe) cx := by
  have hc1 := c1T_ne cy hcx hcy
  have hcA := cAT_ne cy hcx hcy
  have hcB := cBT_ne cy hcx hcy
  have r1 : e1T (qe := qe) ey r s (ex + 15 * qe) = e1T (qe := qe) ey (r + 2) (s + 1) ex + ((9 * qe : ℕ) : ℤ) * 2 := by
    unfold e1T; push_cast; ring
  have r2 : e2T (qe := qe) ey r s (ex + 15 * qe) = e2T (qe := qe) ey (r + 2) (s + 1) ex := by unfold e2T; ring
  have rA : eAT (qe := qe) ey r (ex + 15 * qe) = eAT (qe := qe) ey (r + 2) ex + ((45 * qe : ℕ) : ℤ) * (-1) := by
    unfold eAT; push_cast; ring
  have rB : eBT (qe := qe) ey s (ex + 15 * qe) = eBT (qe := qe) ey (s + 1) ex + ((45 * qe : ℕ) : ℤ) * 1 := by
    unfold eBT; push_cast; ring
  unfold Tn Td
  rw [r1, r2, rA, rB, θ_qshift (h9 hqe) _ hc1 2, θ_qshift (h45 hqe) _ hcA (-1), θ_qshift (h45 hqe) _ hcB 1]
  have hm : mono (eTn (qe := qe) ey r s (ex + 15 * qe)) (cTn cy r s cx) *
      mono (-(((9 * qe : ℕ) : ℤ) * c2 (2 + 1)) - e1T (qe := qe) ey (r + 2) (s + 1) ex * 2 + ((9 * qe : ℕ) : ℤ) * 2)
        ((-1) ^ (2 : ℤ) * c1T cy cx ^ (-(2 : ℤ))) =
      muD (qe := qe) ey cy * mono ex cx * mono (eTn (qe := qe) ey (r + 2) (s + 1) ex) (cTn cy (r + 2) (s + 1) cx) *
      mono (-(((45 * qe : ℕ) : ℤ) * c2 (-1 + 1)) - eAT (qe := qe) ey (r + 2) ex * (-1) + ((45 * qe : ℕ) : ℤ) * (-1))
        ((-1) ^ (-1 : ℤ) * cAT cy cx ^ (-(-1 : ℤ))) *
      mono (-(((45 * qe : ℕ) : ℤ) * c2 (1 + 1)) - eBT (qe := qe) ey (s + 1) ex * 1 + ((45 * qe : ℕ) : ℤ) * 1)
        ((-1) ^ (1 : ℤ) * cBT cy cx ^ (-(1 : ℤ))) := by
    unfold muD
    simp only [mono_mul]
    apply mono_ext
    · rw [show c2 (2 + 1) = 3 by decide, show c2 (-1 + 1) = 0 by decide, show c2 (1 + 1) = 1 by decide]
      unfold eTn e1T eAT eBT
      rw [c2_add2, show s + 1 + 1 = (s + 1) + 1 by ring, c2_add1 (s + 1)]
      push_cast; ring
    · unfold cTn c1T cAT cBT
      have e1 : (-cx) ^ (r + 2) = (-cx) ^ r * (-cx) ^ (2 : ℤ) := zpow_add₀ (neg_ne_zero.mpr hcx) r 2
      have e2 : (-cy) ^ (s + 1 + 1) = (-cy) ^ (s + 1) * (-cy) := zpow_add_one₀ (neg_ne_zero.mpr hcy) (s + 1)
      rw [e1, e2]
      simp only [zpow_neg, neg_neg, zpow_ofNat, zpow_one]
      field_simp
      try ring
  linear_combination (θ (h9 hqe) (e1T (qe := qe) ey (r + 2) (s + 1) ex) (c1T cy cx) *
    θ (h45 hqe) (e2T (qe := qe) ey (r + 2) (s + 1) ex) (c2T cy cx) *
    θ (h45 hqe) (eAT (qe := qe) ey (r + 2) ex) (cAT cy cx) *
    θ (h45 hqe) (eBT (qe := qe) ey (s + 1) ex) (cBT cy cx)) * hm

include hqe in
/-- `3`-periodicity in `r`, cross-multiplied. -/
theorem T_per_r (hcy : cy ≠ 0) (r s ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    Tn hqe ey cy (r + 3) s ex cx * Td hqe ey cy r s ex cx = Tn hqe ey cy r s ex cx * Td hqe ey cy (r + 3) s ex cx := by
  have hc1 := c1T_ne cy hcx hcy
  have hc2 := c2T_ne cy hcx hcy
  have hcA := cAT_ne cy hcx hcy
  have r1 : e1T (qe := qe) ey (r + 3) s ex = e1T (qe := qe) ey r s ex + ((9 * qe : ℕ) : ℤ) * (-1) := by
    unfold e1T; push_cast; ring
  have r2 : e2T (qe := qe) ey (r + 3) s ex = e2T (qe := qe) ey r s ex + ((45 * qe : ℕ) : ℤ) * 1 := by
    unfold e2T; push_cast; ring
  have rA : eAT (qe := qe) ey (r + 3) ex = eAT (qe := qe) ey r ex + ((45 * qe : ℕ) : ℤ) * 1 := by
    unfold eAT; push_cast; ring
  unfold Tn Td
  rw [r1, r2, rA, θ_qshift (h9 hqe) _ hc1 (-1), θ_qshift (h45 hqe) _ hc2 1, θ_qshift (h45 hqe) _ hcA 1]
  have hm : mono (eTn (qe := qe) ey (r + 3) s ex) (cTn cy (r + 3) s cx) *
      mono (-(((9 * qe : ℕ) : ℤ) * c2 (-1 + 1)) - e1T (qe := qe) ey r s ex * (-1) + ((9 * qe : ℕ) : ℤ) * (-1))
        ((-1) ^ (-1 : ℤ) * c1T cy cx ^ (-(-1 : ℤ))) *
      mono (-(((45 * qe : ℕ) : ℤ) * c2 (1 + 1)) - e2T (qe := qe) ey r s ex * 1 + ((45 * qe : ℕ) : ℤ) * 1)
        ((-1) ^ (1 : ℤ) * c2T cy cx ^ (-(1 : ℤ))) =
      mono (eTn (qe := qe) ey r s ex) (cTn cy r s cx) *
      mono (-(((45 * qe : ℕ) : ℤ) * c2 (1 + 1)) - eAT (qe := qe) ey r ex * 1 + ((45 * qe : ℕ) : ℤ) * 1)
        ((-1) ^ (1 : ℤ) * cAT cy cx ^ (-(1 : ℤ))) := by
    simp only [mono_mul]
    apply mono_ext
    · rw [show c2 (-1 + 1) = 0 by decide, show c2 (1 + 1) = 1 by decide]
      unfold eTn e1T e2T eAT
      rw [c2_add3]
      push_cast; ring
    · unfold cTn c1T c2T cAT
      rw [zpow_add₀ (neg_ne_zero.mpr hcx)]
      simp only [zpow_neg]; field_simp; try ring
  linear_combination (θ (h9 hqe) (e1T (qe := qe) ey r s ex) (c1T cy cx) *
    θ (h45 hqe) (e2T (qe := qe) ey r s ex) (c2T cy cx) *
    θ (h45 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx) *
    θ (h45 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)) * hm

include hqe in
/-- `3`-periodicity in `s`, cross-multiplied. -/
theorem T_per_s (hcy : cy ≠ 0) (r s ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) :
    Tn hqe ey cy r (s + 3) ex cx * Td hqe ey cy r s ex cx = Tn hqe ey cy r s ex cx * Td hqe ey cy r (s + 3) ex cx := by
  have hc1 := c1T_ne cy hcx hcy
  have hc2 := c2T_ne cy hcx hcy
  have hcB := cBT_ne cy hcx hcy
  have r1 : e1T (qe := qe) ey r (s + 3) ex = e1T (qe := qe) ey r s ex + ((9 * qe : ℕ) : ℤ) * 1 := by
    unfold e1T; push_cast; ring
  have r2 : e2T (qe := qe) ey r (s + 3) ex = e2T (qe := qe) ey r s ex + ((45 * qe : ℕ) : ℤ) * 1 := by
    unfold e2T; push_cast; ring
  have rB : eBT (qe := qe) ey (s + 3) ex = eBT (qe := qe) ey s ex + ((45 * qe : ℕ) : ℤ) * 1 := by
    unfold eBT; push_cast; ring
  unfold Tn Td
  rw [r1, r2, rB, θ_qshift (h9 hqe) _ hc1 1, θ_qshift (h45 hqe) _ hc2 1, θ_qshift (h45 hqe) _ hcB 1]
  have hm : mono (eTn (qe := qe) ey r (s + 3) ex) (cTn cy r (s + 3) cx) *
      mono (-(((9 * qe : ℕ) : ℤ) * c2 (1 + 1)) - e1T (qe := qe) ey r s ex * 1 + ((9 * qe : ℕ) : ℤ) * 1)
        ((-1) ^ (1 : ℤ) * c1T cy cx ^ (-(1 : ℤ))) *
      mono (-(((45 * qe : ℕ) : ℤ) * c2 (1 + 1)) - e2T (qe := qe) ey r s ex * 1 + ((45 * qe : ℕ) : ℤ) * 1)
        ((-1) ^ (1 : ℤ) * c2T cy cx ^ (-(1 : ℤ))) =
      mono (eTn (qe := qe) ey r s ex) (cTn cy r s cx) *
      mono (-(((45 * qe : ℕ) : ℤ) * c2 (1 + 1)) - eBT (qe := qe) ey s ex * 1 + ((45 * qe : ℕ) : ℤ) * 1)
        ((-1) ^ (1 : ℤ) * cBT cy cx ^ (-(1 : ℤ))) := by
    simp only [mono_mul]
    apply mono_ext
    · rw [show c2 (1 + 1) = 1 by decide]
      unfold eTn e1T e2T eBT
      rw [show s + 3 + 1 = (s + 1) + 3 by ring, c2_add3]
      push_cast; ring
    · unfold cTn c1T c2T cBT
      rw [show s + 3 + 1 = (s + 1) + 3 by ring, zpow_add₀ (neg_ne_zero.mpr hcy)]
      simp only [zpow_neg]; field_simp; try ring
  linear_combination (θ (h9 hqe) (e1T (qe := qe) ey r s ex) (c1T cy cx) *
    θ (h45 hqe) (e2T (qe := qe) ey r s ex) (c2T cy cx) *
    θ (h45 hqe) (eAT (qe := qe) ey r ex) (cAT cy cx) *
    θ (h45 hqe) (eBT (qe := qe) ey s ex) (cBT cy cx)) * hm

/-- reindexing a doubly `3`-periodic function. -/
lemma sum_reindex21 (T : ℤ → ℤ → L) (hr : ∀ r s, T (r + 3) s = T r s) (hs : ∀ r s, T r (s + 3) = T r s) :
    ∑ r ∈ Finset.Icc (0 : ℤ) 2, ∑ s ∈ Finset.Icc (0 : ℤ) 2, T (r + 2) (s + 1) =
      ∑ r ∈ Finset.Icc (0 : ℤ) 2, ∑ s ∈ Finset.Icc (0 : ℤ) 2, T r s := by
  have hI : Finset.Icc (0 : ℤ) 2 = {0, 1, 2} := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; constructor <;> intro h <;> omega
  have h3 : ∀ s, T 3 s = T 0 s := fun s => by simpa using hr 0 s
  have h4 : ∀ s, T 4 s = T 1 s := fun s => by simpa using hr 1 s
  have k3 : ∀ r, T r 3 = T r 0 := fun r => by simpa using hs r 0
  rw [hI]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
    Int.reduceAdd, Int.reduceEq, or_self, not_false_eq_true, h3, h4, k3]
  ring

/-- `θ_{1,3}(x, y, q) / J_{45}³`. -/
noncomputable def thV (ex : ℤ) (cx : ℂ) : L :=
  ∑ r ∈ Finset.Icc (0 : ℤ) 2, ∑ s ∈ Finset.Icc (0 : ℤ) 2, Tn hqe ey cy r s ex cx / Td hqe ey cy r s ex cx

include hqe in
/-- **HM Lemma 5.9**: `θ_{1,3}(q^{15}x) = μ_D x θ_{1,3}(x)` at points where no denominator vanishes. -/
theorem thV_FE (hcy : cy ≠ 0) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0)
    (hd0 : ∀ r s, Td hqe ey cy r s ex cx ≠ 0) (hd1 : ∀ r s, Td hqe ey cy r s (ex + 15 * qe) cx ≠ 0) :
    thV hqe ey cy (ex + 15 * qe) cx = muD (qe := qe) ey cy * mono ex cx * thV hqe ey cy ex cx := by
  set T : ℤ → ℤ → L := fun r s => Tn hqe ey cy r s ex cx / Td hqe ey cy r s ex cx
  have hT : ∀ r s, Tn hqe ey cy r s (ex + 15 * qe) cx / Td hqe ey cy r s (ex + 15 * qe) cx =
      muD (qe := qe) ey cy * mono ex cx * T (r + 2) (s + 1) := by
    intro r s
    have h := T_shift hqe ey cy hcy r s ex hcx
    simp only [T]
    rw [← mul_div_assoc, div_eq_div_iff (hd1 r s) (hd0 (r + 2) (s + 1))]
    linear_combination h
  have hr : ∀ r s, T (r + 3) s = T r s := fun r s => by
    simp only [T]; rw [div_eq_div_iff (hd0 _ _) (hd0 _ _)]; exact T_per_r hqe ey cy hcy r s ex hcx
  have hs : ∀ r s, T r (s + 3) = T r s := fun r s => by
    simp only [T]; rw [div_eq_div_iff (hd0 _ _) (hd0 _ _)]; exact T_per_s hqe ey cy hcy r s ex hcx
  unfold thV
  simp only [hT, ← Finset.mul_sum]
  rw [sum_reindex21 T hr hs]

end T141

end MTC.H141
