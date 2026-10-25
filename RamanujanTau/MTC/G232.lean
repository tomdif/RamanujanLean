/-
# The Appell–Lerch side `g_{2,3,2}(x, y, q, −1, −1)` and its functional equation in `x`

With `Q = q^{10}`, `A(X) = A(X, −1)` and `J̄ = j(−1; q^{10})`:

  `J̄ g = Σ_{t<2} (−y)^t q^{2C(t,2)} j(q^{3t}x; q²) A(X_t) + Σ_{t<2} (−x)^t q^{2C(t,2)} j(q^{3t}y; q²) A(Y_t)`,

`X_t = q^{6−5t} y² x^{−3}`, `Y_t = q^{6−5t} x² y^{−3}`. Under `x ↦ q⁵x` (`μ_D = −q⁶y^{−3}`):

* `g2_shift` — `G2_t(q⁵x) = Inh_t(x) J̄ + μ_D x² G2_t(x)`;
* `g1_shift` — `G1_t(q⁵x) = μ_D x² G1_{t+1}(x) − J̄ (Inh term u = t − 2)`;
* `g1_wrap` — `G1_2 = G1_0 − J̄ j(x; q²)`;
* `gNum_FE` — `J̄ g(q⁵x) = μ_D x² J̄ g(x) + J̄ Inh(x)`.
-/
import RamanujanTau.MTC.F232
import RamanujanTau.MTC.G373

set_option autoImplicit false

namespace MTC.H232
open ALz HahnSeries Finset MTC

section G232
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

lemma h10 (hqe : 1 ≤ qe) : 1 ≤ 10 * qe := by omega

/-- `J̄ = j(−1; q^{10})`. -/
noncomputable def Jb : L := θ (h10 hqe) 0 (-1)

def eX (t ex : ℤ) : ℤ := qe * (6 - 5 * t) + 2 * ey - 3 * ex
noncomputable def cX (cx : ℂ) : ℂ := cy ^ (2 : ℤ) * cx ^ (-3 : ℤ)
def eY (t ex : ℤ) : ℤ := qe * (6 - 5 * t) + 2 * ex - 3 * ey
noncomputable def cY (cx : ℂ) : ℂ := cx ^ (2 : ℤ) * cy ^ (-3 : ℤ)

noncomputable def g1 (t ex : ℤ) (cx : ℂ) : L :=
  mono (2 * qe * c2 t + ey * t) ((-cy) ^ t) * θ (h2qe hqe) (3 * qe * t + ex) cx *
    Av (h10 hqe) (eX (qe := qe) ey t ex) (cX cy cx) 0 (-1)

noncomputable def g2 (t ex : ℤ) (cx : ℂ) : L :=
  mono (2 * qe * c2 t + ex * t) ((-cx) ^ t) * θ (h2qe hqe) (3 * qe * t + ey) cy *
    Av (h10 hqe) (eY (qe := qe) ey t ex) (cY cy cx) 0 (-1)

def OKY (t ex : ℤ) (cx : ℂ) : Prop := LamOK (10 * qe) (eY (qe := qe) ey t ex) (cY cy cx) 0 (-1)
def OKX (t ex : ℤ) (cx : ℂ) : Prop := LamOK (10 * qe) (eX (qe := qe) ey t ex) (cX cy cx) 0 (-1)

lemma cX_ne {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) : cX cy cx ≠ 0 := by
  unfold cX; exact mul_ne_zero (zpow_ne_zero _ hcy) (zpow_ne_zero _ hcx)
lemma cY_ne {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) : cY cy cx ≠ 0 := by
  unfold cY; exact mul_ne_zero (zpow_ne_zero _ hcx) (zpow_ne_zero _ hcy)

include hqe in
theorem g2_shift (hcy : cy ≠ 0) (t ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hok : OKY (qe := qe) ey cy t ex cx) :
    g2 hqe ey cy t (ex + 5 * qe) cx =
      mono (5 * qe * t + 2 * qe * c2 t) ((-1) ^ t) * θ (h2qe hqe) (3 * qe * t + ey) cy *
        mono (ex * t) (cx ^ t) * Jb hqe +
      muD (qe := qe) ey cy * mono (2 * ex) (cx ^ (2 : ℤ)) * g2 hqe ey cy t ex cx := by
  have hY := cY_ne cy hcx hcy
  have hs := Av_qshift (h10 hqe) hY (by norm_num : (-1 : ℂ) ≠ 0) hok
  have he : eY (qe := qe) ey t (ex + 5 * qe) = eY (qe := qe) ey t ex + ((10 * qe : ℕ) : ℤ) := by
    unfold eY; push_cast; ring
  unfold g2
  rw [he, show Av (h10 hqe) (eY ey t ex + ((10 * qe : ℕ) : ℤ)) (cY cy cx) 0 (-1) =
    θ (h10 hqe) 0 (-1) - mono (eY ey t ex) (cY cy cx) * Av (h10 hqe) (eY ey t ex) (cY cy cx) 0 (-1) by
      linear_combination hs]
  have m1 : mono (2 * qe * c2 t + (ex + 5 * qe) * t) ((-cx) ^ t) =
      mono (5 * qe * t + 2 * qe * c2 t) ((-1) ^ t) * mono (ex * t) (cx ^ t) := by
    rw [mono_mul]; exact mono_ext (by ring) (by rw [neg_eq_neg_one_mul, mul_zpow])
  have m2 : mono (2 * qe * c2 t + (ex + 5 * qe) * t) ((-cx) ^ t) * mono (eY (qe := qe) ey t ex) (cY cy cx) =
      -(muD (qe := qe) ey cy * mono (2 * ex) (cx ^ (2 : ℤ)) * mono (2 * qe * c2 t + ex * t) ((-cx) ^ t)) := by
    unfold muD cY eY
    rw [mono_mul, mono_mul, mono_mul]
    rw [show -(mono (6 * qe - 3 * ey + 2 * ex + (2 * qe * c2 t + ex * t))
        (-cy ^ (-3 : ℤ) * cx ^ (2 : ℤ) * (-cx) ^ t) : L) =
        mono (6 * qe - 3 * ey + 2 * ex + (2 * qe * c2 t + ex * t))
        (-(-cy ^ (-3 : ℤ) * cx ^ (2 : ℤ) * (-cx) ^ t)) by simp [mono]]
    exact mono_ext (by ring) (by ring)
  rw [Jb]
  linear_combination θ (h2qe hqe) (3 * qe * t + ey) cy * θ (h10 hqe) 0 (-1) * m1 -
    θ (h2qe hqe) (3 * qe * t + ey) cy * Av (h10 hqe) (eY ey t ex) (cY cy cx) 0 (-1) * m2

lemma c2_sub2 (t : ℤ) : c2 (t - 2) = c2 t - 2 * t + 3 := by
  have e1 := two_c2 (t - 2); have e2 := two_c2 t
  exact mul_left_cancel₀ (two_ne_zero) (by linear_combination e1 - e2)

include hqe in
theorem g1_shift (hcy : cy ≠ 0) (t ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hok : OKX (qe := qe) ey cy (t + 1) ex cx) :
    g1 hqe ey cy t (ex + 5 * qe) cx =
      muD (qe := qe) ey cy * mono (2 * ex) (cx ^ (2 : ℤ)) * g1 hqe ey cy (t + 1) ex cx -
      Jb hqe * (mono (2 * qe * c2 (t - 2) + ey * (t - 2)) ((-1) ^ (t - 2) * cy ^ (t - 2)) *
          θ (h2qe hqe) (5 * qe + 3 * qe * (t - 2) + ex) cx) := by
  have hX := cX_ne cy hcx hcy
  have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
  set E := eX (qe := qe) ey (t + 1) ex with hE
  set c := cX cy cx
  have ok1 : LamOK (10 * qe) (E - ((10 * qe : ℕ) : ℤ)) c 0 (-1) := lamOK_down hok
  have a1 := Av_down (h10 hqe) hX hm1 ok1
  have he : eX (qe := qe) ey t (ex + 5 * qe) = E - ((10 * qe : ℕ) : ℤ) := by
    rw [hE]; unfold eX; push_cast; ring
  set e0 := 3 * qe * (t + 1) + ex
  have hθL := θ_qshift (h2qe hqe) e0 hcx 1
  have hθ1 := θ_qshift (h2qe hqe) e0 hcx (-2)
  have r0 : 3 * (qe : ℤ) * t + (ex + 5 * qe) = e0 + ((2 * qe : ℕ) : ℤ) * 1 := by push_cast; ring
  have r1 : 5 * (qe : ℤ) + 3 * qe * (t - 2) + ex = e0 + ((2 * qe : ℕ) : ℤ) * (-2) := by push_cast; ring
  unfold g1
  rw [he, a1, r0, hθL, r1, hθ1, show 3 * (qe : ℤ) * (t + 1) + ex = e0 from rfl, ← hE]
  unfold Jb
  have hcy' : -cy ≠ 0 := neg_ne_zero.mpr hcy
  have cs2 := c2_sub2 t
  have cs1 := c2_succ t
  have hcinv : c⁻¹ = cy ^ (-2 : ℤ) * cx ^ (3 : ℤ) := by
    simp only [c, cX]; rw [mul_inv, ← zpow_neg, ← zpow_neg]; simp
  have z1 : ((-1 : ℂ)) ^ (t - 2) * cy ^ (t - 2) = (-cy) ^ t * (-cy) ^ (-2 : ℤ) := by
    rw [← mul_zpow, neg_one_mul, sub_eq_add_neg, zpow_add₀ hcy']
  have z3 : (-cy) ^ (t + 1) = (-cy) ^ t * (-cy) := zpow_add_one₀ hcy' t
  have h1 : mono (2 * qe * c2 t + ey * t) ((-cy) ^ t) *
      mono (-(((2 * qe : ℕ) : ℤ) * c2 (1 + 1)) - e0 * 1 + ((2 * qe : ℕ) : ℤ) * 1) ((-1) ^ (1 : ℤ) * cx ^ (-(1 : ℤ))) *
      mono (((10 * qe : ℕ) : ℤ) - E) c⁻¹ =
      -(muD (qe := qe) ey cy * mono (2 * ex) (cx ^ (2 : ℤ)) * mono (2 * qe * c2 (t + 1) + ey * (t + 1)) ((-cy) ^ (t + 1))) := by
    unfold muD
    simp only [mono_mul]
    rw [show -(mono (6 * ↑qe - 3 * ey + 2 * ex + (2 * ↑qe * c2 (t + 1) + ey * (t + 1)))
        (-cy ^ (-3 : ℤ) * cx ^ (2 : ℤ) * (-cy) ^ (t + 1)) : L) =
      mono (6 * ↑qe - 3 * ey + 2 * ex + (2 * ↑qe * c2 (t + 1) + ey * (t + 1)))
        (-(-cy ^ (-3 : ℤ) * cx ^ (2 : ℤ) * (-cy) ^ (t + 1))) by simp [mono]]
    apply mono_ext
    · rw [show c2 (1 + 1) = 1 by decide, cs1]; simp only [hE, eX, e0]; push_cast; ring
    · rw [hcinv, z3]; simp only [zpow_neg]; field_simp; try ring
  have h2 : mono (2 * qe * c2 t + ey * t) ((-cy) ^ t) *
      mono (-(((2 * qe : ℕ) : ℤ) * c2 (1 + 1)) - e0 * 1 + ((2 * qe : ℕ) : ℤ) * 1) ((-1) ^ (1 : ℤ) * cx ^ (-(1 : ℤ))) *
      mono (((10 * qe : ℕ) : ℤ) - E) c⁻¹ =
      -(mono (2 * qe * c2 (t - 2) + ey * (t - 2)) ((-1) ^ (t - 2) * cy ^ (t - 2)) *
        mono (-(((2 * qe : ℕ) : ℤ) * c2 (-2 + 1)) - e0 * (-2) + ((2 * qe : ℕ) : ℤ) * (-2)) ((-1) ^ (-2 : ℤ) * cx ^ (-(-2 : ℤ)))) := by
    simp only [mono_mul]
    rw [show -(mono (2 * qe * c2 (t - 2) + ey * (t - 2) + (-(((2 * qe : ℕ) : ℤ) * c2 (-2 + 1)) - e0 * (-2) +
        ((2 * qe : ℕ) : ℤ) * (-2))) ((-1) ^ (t - 2) * cy ^ (t - 2) * ((-1) ^ (-2 : ℤ) * cx ^ (-(-2 : ℤ)))) : L) =
      mono (2 * qe * c2 (t - 2) + ey * (t - 2) + (-(((2 * qe : ℕ) : ℤ) * c2 (-2 + 1)) - e0 * (-2) +
        ((2 * qe : ℕ) : ℤ) * (-2))) (-((-1) ^ (t - 2) * cy ^ (t - 2) * ((-1) ^ (-2 : ℤ) * cx ^ (-(-2 : ℤ))))) by
      simp [mono]]
    apply mono_ext
    · rw [show c2 (1 + 1) = 1 by decide, show c2 (-2 + 1) = 1 by decide, cs2]; simp only [hE, eX, e0]; push_cast; ring
    · rw [hcinv, z1]; simp only [zpow_neg]; field_simp; try ring
  linear_combination θ (h2qe hqe) e0 cx * θ (h10 hqe) 0 (-1) * h2 - θ (h2qe hqe) e0 cx * Av (h10 hqe) E c 0 (-1) * h1

include hqe in
theorem g1_wrap (hcy : cy ≠ 0) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hok : OKX (qe := qe) ey cy 0 ex cx) :
    g1 hqe ey cy 2 ex cx = g1 hqe ey cy 0 ex cx - Jb hqe * θ (h2qe hqe) ex cx := by
  have hX := cX_ne cy hcx hcy
  have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
  have ok1 : LamOK (10 * qe) (eX (qe := qe) ey 0 ex - ((10 * qe : ℕ) : ℤ)) (cX cy cx) 0 (-1) := lamOK_down hok
  have a1 := Av_down (h10 hqe) hX hm1 ok1
  have he : eX (qe := qe) ey 2 ex = eX (qe := qe) ey 0 ex - ((10 * qe : ℕ) : ℤ) := by unfold eX; push_cast; ring
  have hθ := θ_qshift (h2qe hqe) ex hcx 3
  have r0 : 3 * (qe : ℤ) * 2 + ex = ex + ((2 * qe : ℕ) : ℤ) * 3 := by push_cast; ring
  unfold g1 Jb
  rw [he, a1, r0, hθ, show 3 * (qe : ℤ) * 0 + ex = ex by ring]
  have hcinv : (cX cy cx)⁻¹ = cy ^ (-2 : ℤ) * cx ^ (3 : ℤ) := by
    simp only [cX]; rw [mul_inv, ← zpow_neg, ← zpow_neg]; simp
  have hm : mono (2 * qe * c2 2 + ey * 2) ((-cy) ^ (2 : ℤ)) *
      mono (-(((2 * qe : ℕ) : ℤ) * c2 (3 + 1)) - ex * 3 + ((2 * qe : ℕ) : ℤ) * 3) ((-1) ^ (3 : ℤ) * cx ^ (-(3 : ℤ))) *
      mono (((10 * qe : ℕ) : ℤ) - eX (qe := qe) ey 0 ex) (cX cy cx)⁻¹ = mono 0 (-1) := by
    simp only [mono_mul]
    apply mono_ext
    · rw [show c2 (3 + 1) = 6 by decide, show c2 2 = 1 by decide]; unfold eX; push_cast; ring
    · rw [hcinv]; simp only [zpow_neg]; field_simp; try ring
  have h0 : mono (2 * qe * c2 0 + ey * 0) ((-cy) ^ (0 : ℤ)) = 1 := by simp [c2, mono]
  have hn : (mono 0 (-1) : L) = -1 := by simp [mono]
  rw [hn] at hm
  linear_combination θ (h2qe hqe) ex cx * θ (h10 hqe) 0 (-1) * hm -
    θ (h2qe hqe) ex cx * Av (h10 hqe) (eX (qe := qe) ey 0 ex) (cX cy cx) 0 (-1) * hm -
    θ (h2qe hqe) ex cx * Av (h10 hqe) (eX (qe := qe) ey 0 ex) (cX cy cx) 0 (-1) * h0

/-- `J̄ · g_{2,3,2}(x, y, q, −1, −1)`. -/
noncomputable def gNum (ex : ℤ) (cx : ℂ) : L :=
  g1 hqe ey cy 0 ex cx + g1 hqe ey cy 1 ex cx + (g2 hqe ey cy 0 ex cx + g2 hqe ey cy 1 ex cx)

include hqe in
lemma u3_term (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) :
    mono (2 * qe * c2 (-3) + ey * (-3)) ((-1) ^ (-3 : ℤ) * cy ^ (-3 : ℤ)) *
      θ (h2qe hqe) (5 * qe + 3 * qe * (-3) + ex) cx =
    muD (qe := qe) ey cy * mono (2 * ex) (cx ^ (2 : ℤ)) * θ (h2qe hqe) ex cx := by
  rw [show 5 * (qe : ℤ) + 3 * qe * (-3) + ex = ex + ((2 * qe : ℕ) : ℤ) * (-2) by push_cast; ring,
    θ_qshift (h2qe hqe) ex hcx (-2), ← mul_assoc]
  congr 1
  unfold muD
  simp only [mono_mul]
  apply mono_ext
  · have h1 : c2 (-3) = 6 := by decide
    have h2 : c2 (-1) = 1 := by decide
    push_cast; simp only [h1, h2]; ring
  · simp only [zpow_neg]; field_simp; try ring

include hqe in
/-- **HM Prop 5.5 for `g`**: `J̄ g(q⁵x) = μ_D x² J̄ g(x) + J̄ Inh(x)`. -/
theorem gNum_FE (hcy : cy ≠ 0) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0)
    (hX0 : OKX (qe := qe) ey cy 0 ex cx) (hX1 : OKX (qe := qe) ey cy 1 ex cx)
    (hY0 : OKY (qe := qe) ey cy 0 ex cx) (hY1 : OKY (qe := qe) ey cy 1 ex cx) :
    gNum hqe ey cy (ex + 5 * qe) cx =
      muD (qe := qe) ey cy * mono (2 * ex) (cx ^ (2 : ℤ)) * gNum hqe ey cy ex cx + Jb hqe * InhV hqe ey cy ex cx := by
  have hX2 : OKX (qe := qe) ey cy 2 ex cx := by
    have := lamOK_down (N := 10 * qe) hX0
    rwa [show eX (qe := qe) ey 0 ex - ((10 * qe : ℕ) : ℤ) = eX (qe := qe) ey 2 ex by unfold eX; push_cast; ring]
      at this
  unfold gNum
  rw [g1_shift hqe ey cy hcy 0 ex hcx (by simpa using hX1), g1_shift hqe ey cy hcy 1 ex hcx (by simpa using hX2),
    g2_shift hqe ey cy hcy 0 ex hcx hY0, g2_shift hqe ey cy hcy 1 ex hcx hY1]
  simp only [show (0 : ℤ) + 1 = 1 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num]
  rw [g1_wrap hqe ey cy hcy ex hcx hX0]
  have u3 := u3_term hqe ey cy ex hcx hcy
  have hI1 : Finset.Icc (0 : ℤ) 1 = {0, 1} := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; constructor <;> intro h <;> omega
  have hI3 : Finset.Icc (-3 : ℤ) (-1) = {-3, -2, -1} := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; constructor <;> intro h <;> omega
  unfold InhV
  rw [hI1, hI3]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
    Int.reduceEq, Int.reduceNeg, or_self, not_false_eq_true]
  norm_num at u3 ⊢
  ring_nf at u3 ⊢
  linear_combination (Jb hqe) * u3

end G232

end MTC.H232
