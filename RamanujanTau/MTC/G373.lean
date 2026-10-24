/-
# The Appell–Lerch side `g_{3,7,3}(x, y, q, −1, −1)` and its functional equation in `x`

With `Q = q^{120}`, `A(X) = A(X, −1)` the Lambert numerator and `J̄ = j(−1; Q)`:

  `J̄ · g = Σ_{t<3} (−y)^t q^{3C(t,2)} j(q^{7t} x; q³) A(X_t) + Σ_{t<3} (−x)^t q^{3C(t,2)} j(q^{7t} y; q³) A(Y_t)`,

`X_t = −q^{66−40t} y³ x^{−7}`, `Y_t = −q^{66−40t} x³ y^{−7}`. Under `x ↦ q^{40} x`:

* `g2_shift` — `G2_t(q^{40}x) = (inhomogeneous term) + q^{66} y^{−7} x³ G2_t(x)` for every `t`;
* `g1_shift` — `G1_t(q^{40}x) = q^{66} y^{−7} x³ G1_{t+1}(x) − (two inhomogeneous terms)`;
* `g1_wrap` — `G1_3 = G1_0 − J̄ j(x; q³)`.
-/
import RamanujanTau.MTC.F373

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

/-! ## Total Appell–Lerch numerator -/

section Av
variable {N : ℕ} (hN : 1 ≤ N)

/-- `A(x, z)` when defined (zero otherwise). -/
noncomputable def Av (ex : ℤ) (cx : ℂ) (ez : ℤ) (cz : ℂ) : L := by
  classical
  exact if h : cx ≠ 0 ∧ cz ≠ 0 ∧ LamOK N ex cx ez cz then Alam hN h.1 h.2.1 h.2.2 else 0

lemma Av_qshift {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (hx : cx ≠ 0) (hz : cz ≠ 0) (hok : LamOK N ex cx ez cz) :
    Av hN (ex + N) cx ez cz + mono ex cx * Av hN ex cx ez cz = θ hN ez cz := by
  unfold Av
  rw [dif_pos ⟨hx, hz, lamOK_shift hN hok⟩, dif_pos ⟨hx, hz, hok⟩]
  exact Alam_qshift hN hx hz hok

/-- the same, solved for the lower argument. -/
lemma Av_down {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (hx : cx ≠ 0) (hz : cz ≠ 0) (hok : LamOK N (ex - N) cx ez cz) :
    Av hN (ex - N) cx ez cz =
      mono (N - ex) cx⁻¹ * θ hN ez cz - mono (N - ex) cx⁻¹ * Av hN ex cx ez cz := by
  have h := Av_qshift hN hx hz hok
  rw [sub_add_cancel] at h
  have hm : mono (N - ex) cx⁻¹ * mono (ex - N) cx = 1 := by
    rw [mono_mul, show (N : ℤ) - ex + (ex - N) = 0 by ring, inv_mul_cancel₀ hx]; rfl
  linear_combination (mono (N - ex) cx⁻¹) * h - Av hN (ex - N) cx ez cz * hm

lemma lamOK_down {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (hok : LamOK N ex cx ez cz) :
    LamOK N (ex - N) cx ez cz := fun r h => hok (r - 1) ⟨by unfold wE at *; linarith [h.1], h.2⟩

end Av

/-! ## The six terms -/

section G373
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

lemma h120 (hqe : 1 ≤ qe) : 1 ≤ 120 * qe := by omega

/-- `J̄ = j(−1; q^{120})`. -/
noncomputable def Jb : L := θ (h120 hqe) 0 (-1)

/-- exponent and coefficient of `X_t`. -/
def eX (t ex : ℤ) : ℤ := qe * (66 - 40 * t) + 3 * ey - 7 * ex
noncomputable def cX (cx : ℂ) : ℂ := -(cy ^ (3 : ℤ) * cx ^ (-7 : ℤ))

/-- exponent and coefficient of `Y_t`. -/
def eY (t ex : ℤ) : ℤ := qe * (66 - 40 * t) + 3 * ex - 7 * ey
noncomputable def cY (cx : ℂ) : ℂ := -(cx ^ (3 : ℤ) * cy ^ (-7 : ℤ))

/-- `(−y)^t q^{3C(t,2)} j(q^{7t} x; q³) A(X_t)`. -/
noncomputable def g1 (t ex : ℤ) (cx : ℂ) : L :=
  mono (3 * qe * c2 t + ey * t) ((-cy) ^ t) * θ (h3qe hqe) (7 * qe * t + ex) cx *
    Av (h120 hqe) (eX (qe := qe) ey t ex) (cX cy cx) 0 (-1)

/-- `(−x)^t q^{3C(t,2)} j(q^{7t} y; q³) A(Y_t)`. -/
noncomputable def g2 (t ex : ℤ) (cx : ℂ) : L :=
  mono (3 * qe * c2 t + ex * t) ((-cx) ^ t) * θ (h3qe hqe) (7 * qe * t + ey) cy *
    Av (h120 hqe) (eY (qe := qe) ey t ex) (cY cy cx) 0 (-1)

/-- the hypothesis that the `Y_t` Lambert series is defined. -/
def OKY (t ex : ℤ) (cx : ℂ) : Prop := LamOK (120 * qe) (eY (qe := qe) ey t ex) (cY cy cx) 0 (-1)
def OKX (t ex : ℤ) (cx : ℂ) : Prop := LamOK (120 * qe) (eX (qe := qe) ey t ex) (cX cy cx) 0 (-1)

include hqe in
/-- **second family**: `G2_t(q^{40}x) = Inh_t(x) J̄ + q^{66} y^{−7} x³ G2_t(x)`. -/
theorem g2_shift (hcy : cy ≠ 0) (t ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hok : OKY (qe := qe) ey cy t ex cx) :
    g2 hqe ey cy t (ex + 40 * qe) cx =
      mono (40 * qe * t + 3 * qe * c2 t) ((-1) ^ t) * θ (h3qe hqe) (7 * qe * t + ey) cy *
        mono (ex * t) (cx ^ t) * Jb hqe +
      muD (qe := qe) ey cy * mono (3 * ex) (cx ^ (3 : ℤ)) * g2 hqe ey cy t ex cx := by
  have hY : cY cy cx ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (zpow_ne_zero _ hcx) (zpow_ne_zero _ hcy))
  have hs := Av_qshift (h120 hqe) hY (by norm_num : (-1 : ℂ) ≠ 0) hok
  have he : eY (qe := qe) ey t (ex + 40 * qe) = eY (qe := qe) ey t ex + ((120 * qe : ℕ) : ℤ) := by
    unfold eY; push_cast; ring
  unfold g2
  rw [he, show Av (h120 hqe) (eY ey t ex + ((120 * qe : ℕ) : ℤ)) (cY cy cx) 0 (-1) =
    θ (h120 hqe) 0 (-1) - mono (eY ey t ex) (cY cy cx) * Av (h120 hqe) (eY ey t ex) (cY cy cx) 0 (-1) by
      linear_combination hs]
  have m1 : mono (3 * qe * c2 t + (ex + 40 * qe) * t) ((-cx) ^ t) =
      mono (40 * qe * t + 3 * qe * c2 t) ((-1) ^ t) * mono (ex * t) (cx ^ t) := by
    rw [mono_mul]; exact mono_ext (by ring) (by rw [neg_eq_neg_one_mul, mul_zpow])
  have m2 : mono (3 * qe * c2 t + (ex + 40 * qe) * t) ((-cx) ^ t) * mono (eY (qe := qe) ey t ex) (cY cy cx) =
      -(muD (qe := qe) ey cy * mono (3 * ex) (cx ^ (3 : ℤ)) * mono (3 * qe * c2 t + ex * t) ((-cx) ^ t)) := by
    unfold muD cY eY
    rw [mono_mul, mono_mul, mono_mul]
    have : -(mono (66 * qe - 7 * ey + 3 * ex + (3 * qe * c2 t + ex * t))
        (cy ^ (-7 : ℤ) * cx ^ (3 : ℤ) * (-cx) ^ t) : L) =
        mono (66 * qe - 7 * ey + 3 * ex + (3 * qe * c2 t + ex * t))
        (-(cy ^ (-7 : ℤ) * cx ^ (3 : ℤ) * (-cx) ^ t)) := by simp [mono]
    rw [this]
    exact mono_ext (by ring) (by ring)
  rw [Jb]
  linear_combination θ (h3qe hqe) (7 * qe * t + ey) cy * θ (h120 hqe) 0 (-1) * m1 -
    θ (h3qe hqe) (7 * qe * t + ey) cy * Av (h120 hqe) (eY ey t ex) (cY cy cx) 0 (-1) * m2

lemma c2_sub3 (t : ℤ) : c2 (t - 3) = c2 t - 3 * t + 6 := by
  have e1 := two_c2 (t - 3); have e2 := two_c2 t
  exact mul_left_cancel₀ (two_ne_zero) (by linear_combination e1 - e2)
lemma c2_sub6 (t : ℤ) : c2 (t - 6) = c2 t - 6 * t + 21 := by
  have e1 := two_c2 (t - 6); have e2 := two_c2 t
  exact mul_left_cancel₀ (two_ne_zero) (by linear_combination e1 - e2)

include hqe in
/-- **first family**: `G1_t(q^{40}x) = q^{66}y^{−7}x³ G1_{t+1}(x) − J̄ (Inh terms u = t−3, t−6)`. -/
theorem g1_shift (hcy : cy ≠ 0) (t ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hok : OKX (qe := qe) ey cy (t + 1) ex cx) :
    g1 hqe ey cy t (ex + 40 * qe) cx =
      muD (qe := qe) ey cy * mono (3 * ex) (cx ^ (3 : ℤ)) * g1 hqe ey cy (t + 1) ex cx -
      Jb hqe * (mono (3 * qe * c2 (t - 3) + ey * (t - 3)) ((-1) ^ (t - 3) * cy ^ (t - 3)) *
          θ (h3qe hqe) (40 * qe + 7 * qe * (t - 3) + ex) cx +
        mono (3 * qe * c2 (t - 6) + ey * (t - 6)) ((-1) ^ (t - 6) * cy ^ (t - 6)) *
          θ (h3qe hqe) (40 * qe + 7 * qe * (t - 6) + ex) cx) := by
  have hX : cX cy cx ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (zpow_ne_zero _ hcy) (zpow_ne_zero _ hcx))
  have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
  set E := eX (qe := qe) ey (t + 1) ex with hE
  set c := cX cy cx
  have ok1 : LamOK (120 * qe) (E - ((120 * qe : ℕ) : ℤ)) c 0 (-1) := lamOK_down hok
  have ok2 : LamOK (120 * qe) (E - ((120 * qe : ℕ) : ℤ) - ((120 * qe : ℕ) : ℤ)) c 0 (-1) := lamOK_down ok1
  have a1 := Av_down (h120 hqe) hX hm1 ok1
  have a2 := Av_down (h120 hqe) hX hm1 ok2
  have he : eX (qe := qe) ey t (ex + 40 * qe) = E - ((120 * qe : ℕ) : ℤ) - ((120 * qe : ℕ) : ℤ) := by
    rw [hE]; unfold eX; push_cast; ring
  set e0 := 7 * qe * (t + 1) + ex
  have hθL := θ_qshift (h3qe hqe) e0 hcx 11
  have hθ1 := θ_qshift (h3qe hqe) e0 hcx 4
  have hθ2 := θ_qshift (h3qe hqe) e0 hcx (-3)
  have r0 : 7 * (qe : ℤ) * t + (ex + 40 * qe) = e0 + ((3 * qe : ℕ) : ℤ) * 11 := by push_cast; ring
  have r1 : 40 * (qe : ℤ) + 7 * qe * (t - 3) + ex = e0 + ((3 * qe : ℕ) : ℤ) * 4 := by push_cast; ring
  have r2 : 40 * (qe : ℤ) + 7 * qe * (t - 6) + ex = e0 + ((3 * qe : ℕ) : ℤ) * (-3) := by push_cast; ring
  unfold g1
  rw [he, a2, a1, r0, hθL, r1, hθ1, r2, hθ2, show 7 * (qe : ℤ) * (t + 1) + ex = e0 from rfl, ← hE]
  unfold Jb
  have hcy' : -cy ≠ 0 := neg_ne_zero.mpr hcy
  have e12 : c2 (11 + 1) = 66 := by decide
  have e5 : c2 (4 + 1) = 10 := by decide
  have em2 : c2 (-3 + 1) = 3 := by decide
  have cs1 := c2_succ t
  have cs3 := c2_sub3 t
  have cs6 := c2_sub6 t
  have hcinv : c⁻¹ = -(cy ^ (-3 : ℤ) * cx ^ (7 : ℤ)) := by
    simp only [c, cX]; field_simp; try (rw [zpow_neg, zpow_neg]; field_simp)
  have z1 : ((-1 : ℂ)) ^ (t - 3) * cy ^ (t - 3) = (-cy) ^ t * (-cy) ^ (-3 : ℤ) := by
    rw [← mul_zpow, neg_one_mul, sub_eq_add_neg, zpow_add₀ hcy']
  have z2 : ((-1 : ℂ)) ^ (t - 6) * cy ^ (t - 6) = (-cy) ^ t * (-cy) ^ (-6 : ℤ) := by
    rw [← mul_zpow, neg_one_mul, sub_eq_add_neg, zpow_add₀ hcy']
  have z3 : (-cy) ^ (t + 1) = (-cy) ^ t * (-cy) := zpow_add_one₀ hcy' t
  have h1 : mono (3 * qe * c2 t + ey * t) ((-cy) ^ t) *
      mono (-(((3 * qe : ℕ) : ℤ) * c2 (11 + 1)) - e0 * 11 + ((3 * qe : ℕ) : ℤ) * 11) ((-1) ^ (11 : ℤ) * cx ^ (-(11 : ℤ))) *
      mono (((120 * qe : ℕ) : ℤ) - (E - ((120 * qe : ℕ) : ℤ))) c⁻¹ * mono (((120 * qe : ℕ) : ℤ) - E) c⁻¹ =
      muD (qe := qe) ey cy * mono (3 * ex) (cx ^ (3 : ℤ)) * mono (3 * qe * c2 (t + 1) + ey * (t + 1)) ((-cy) ^ (t + 1)) := by
    unfold muD
    simp only [mono_mul]
    apply mono_ext
    · rw [e12, cs1]; simp only [hE, eX, e0]; push_cast; ring
    · rw [hcinv, z3]; simp only [zpow_neg]; field_simp; try ring
  have h2 : mono (3 * qe * c2 t + ey * t) ((-cy) ^ t) *
      mono (-(((3 * qe : ℕ) : ℤ) * c2 (11 + 1)) - e0 * 11 + ((3 * qe : ℕ) : ℤ) * 11) ((-1) ^ (11 : ℤ) * cx ^ (-(11 : ℤ))) *
      mono (((120 * qe : ℕ) : ℤ) - (E - ((120 * qe : ℕ) : ℤ))) c⁻¹ =
      -(mono (3 * qe * c2 (t - 3) + ey * (t - 3)) ((-1) ^ (t - 3) * cy ^ (t - 3)) *
        mono (-(((3 * qe : ℕ) : ℤ) * c2 (4 + 1)) - e0 * 4 + ((3 * qe : ℕ) : ℤ) * 4) ((-1) ^ (4 : ℤ) * cx ^ (-(4 : ℤ)))) := by
    simp only [mono_mul]
    rw [show -(mono (3 * qe * c2 (t - 3) + ey * (t - 3) + (-(((3 * qe : ℕ) : ℤ) * c2 (4 + 1)) - e0 * 4 +
        ((3 * qe : ℕ) : ℤ) * 4)) ((-1) ^ (t - 3) * cy ^ (t - 3) * ((-1) ^ (4 : ℤ) * cx ^ (-(4 : ℤ)))) : L) =
      mono (3 * qe * c2 (t - 3) + ey * (t - 3) + (-(((3 * qe : ℕ) : ℤ) * c2 (4 + 1)) - e0 * 4 +
        ((3 * qe : ℕ) : ℤ) * 4)) (-((-1) ^ (t - 3) * cy ^ (t - 3) * ((-1) ^ (4 : ℤ) * cx ^ (-(4 : ℤ))))) by
      simp [mono]]
    apply mono_ext
    · rw [e12, e5, cs3]; simp only [hE, eX, e0]; push_cast; ring
    · rw [hcinv, z1]; simp only [zpow_neg]; field_simp; try ring
  have h3 : mono (3 * qe * c2 t + ey * t) ((-cy) ^ t) *
      mono (-(((3 * qe : ℕ) : ℤ) * c2 (11 + 1)) - e0 * 11 + ((3 * qe : ℕ) : ℤ) * 11) ((-1) ^ (11 : ℤ) * cx ^ (-(11 : ℤ))) *
      mono (((120 * qe : ℕ) : ℤ) - (E - ((120 * qe : ℕ) : ℤ))) c⁻¹ * mono (((120 * qe : ℕ) : ℤ) - E) c⁻¹ =
      mono (3 * qe * c2 (t - 6) + ey * (t - 6)) ((-1) ^ (t - 6) * cy ^ (t - 6)) *
        mono (-(((3 * qe : ℕ) : ℤ) * c2 (-3 + 1)) - e0 * -3 + ((3 * qe : ℕ) : ℤ) * -3) ((-1) ^ (-3 : ℤ) * cx ^ (- -3 : ℤ)) := by
    simp only [mono_mul]
    apply mono_ext
    · rw [e12, em2, cs6]; simp only [hE, eX, e0]; push_cast; ring
    · rw [hcinv, z2]; simp only [zpow_neg]; field_simp; try ring
  linear_combination θ (h3qe hqe) e0 cx * θ (h120 hqe) 0 (-1) * h2 -
    θ (h3qe hqe) e0 cx * θ (h120 hqe) 0 (-1) * h3 + θ (h3qe hqe) e0 cx * Av (h120 hqe) E c 0 (-1) * h1

include hqe in
/-- **wrap-around**: `G1_3 = G1_0 − J̄ j(x; q³)`. -/
theorem g1_wrap (hcy : cy ≠ 0) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hok : OKX (qe := qe) ey cy 0 ex cx) :
    g1 hqe ey cy 3 ex cx = g1 hqe ey cy 0 ex cx - Jb hqe * θ (h3qe hqe) ex cx := by
  have hX : cX cy cx ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (zpow_ne_zero _ hcy) (zpow_ne_zero _ hcx))
  have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
  have ok1 : LamOK (120 * qe) (eX (qe := qe) ey 0 ex - ((120 * qe : ℕ) : ℤ)) (cX cy cx) 0 (-1) := lamOK_down hok
  have a1 := Av_down (h120 hqe) hX hm1 ok1
  have he : eX (qe := qe) ey 3 ex = eX (qe := qe) ey 0 ex - ((120 * qe : ℕ) : ℤ) := by unfold eX; push_cast; ring
  have hθ := θ_qshift (h3qe hqe) ex hcx 7
  have r0 : 7 * (qe : ℤ) * 3 + ex = ex + ((3 * qe : ℕ) : ℤ) * 7 := by push_cast; ring
  unfold g1 Jb
  rw [he, a1, r0, hθ, show 7 * (qe : ℤ) * 0 + ex = ex by ring]
  have e8 : c2 (7 + 1) = 28 := by decide
  have e3 : c2 3 = 3 := by decide
  have hcinv : (cX cy cx)⁻¹ = -(cy ^ (-3 : ℤ) * cx ^ (7 : ℤ)) := by
    simp only [cX]; field_simp; try (rw [zpow_neg, zpow_neg]; field_simp)
  have hm : mono (3 * qe * c2 3 + ey * 3) ((-cy) ^ (3 : ℤ)) *
      mono (-(((3 * qe : ℕ) : ℤ) * c2 (7 + 1)) - ex * 7 + ((3 * qe : ℕ) : ℤ) * 7) ((-1) ^ (7 : ℤ) * cx ^ (-(7 : ℤ))) *
      mono (((120 * qe : ℕ) : ℤ) - eX (qe := qe) ey 0 ex) (cX cy cx)⁻¹ = mono 0 (-1) := by
    simp only [mono_mul]
    apply mono_ext
    · rw [e8, e3]; unfold eX; push_cast; ring
    · rw [hcinv]; simp only [zpow_neg]; field_simp; try ring
  have h0 : mono (3 * qe * c2 0 + ey * 0) ((-cy) ^ (0 : ℤ)) = 1 := by simp [c2, mono]
  have hn : (mono 0 (-1) : L) = -1 := by simp [mono]
  rw [hn] at hm
  linear_combination θ (h3qe hqe) ex cx * θ (h120 hqe) 0 (-1) * hm -
    θ (h3qe hqe) ex cx * Av (h120 hqe) (eX (qe := qe) ey 0 ex) (cX cy cx) 0 (-1) * hm -
    θ (h3qe hqe) ex cx * Av (h120 hqe) (eX (qe := qe) ey 0 ex) (cX cy cx) 0 (-1) * h0

/-- `J̄ · g_{3,7,3}(x, y, q, −1, −1)`. -/
noncomputable def gNum (ex : ℤ) (cx : ℂ) : L :=
  g1 hqe ey cy 0 ex cx + g1 hqe ey cy 1 ex cx + g1 hqe ey cy 2 ex cx +
    (g2 hqe ey cy 0 ex cx + g2 hqe ey cy 1 ex cx + g2 hqe ey cy 2 ex cx)

include hqe in
lemma u7_term (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) :
    mono (3 * qe * c2 (-7) + ey * (-7)) ((-1) ^ (-7 : ℤ) * cy ^ (-7 : ℤ)) *
      θ (h3qe hqe) (40 * qe + 7 * qe * (-7) + ex) cx =
    muD (qe := qe) ey cy * mono (3 * ex) (cx ^ (3 : ℤ)) * θ (h3qe hqe) ex cx := by
  rw [show 40 * (qe : ℤ) + 7 * qe * (-7) + ex = ex + ((3 * qe : ℕ) : ℤ) * (-3) by push_cast; ring,
    θ_qshift (h3qe hqe) ex hcx (-3), ← mul_assoc]
  congr 1
  unfold muD
  simp only [mono_mul]
  apply mono_ext
  · have h1 : c2 (-7) = 28 := by decide
    have h2 : c2 (-3 + 1) = 3 := by decide
    have h3 : c2 (-2) = 3 := by decide
    push_cast; simp only [h1, h2, h3]; ring
  · simp only [zpow_neg]; field_simp; try ring

include hqe in
/-- **HM Prop 5.5 for `g`**: `J̄ g(q^{40}x) = q^{66}y^{−7}x³ J̄ g(x) + J̄ Inh(x)`. -/
theorem gNum_FE (hcy : cy ≠ 0) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0)
    (hX0 : OKX (qe := qe) ey cy 0 ex cx) (hX1 : OKX (qe := qe) ey cy 1 ex cx) (hX2 : OKX (qe := qe) ey cy 2 ex cx)
    (hY0 : OKY (qe := qe) ey cy 0 ex cx) (hY1 : OKY (qe := qe) ey cy 1 ex cx) (hY2 : OKY (qe := qe) ey cy 2 ex cx) :
    gNum hqe ey cy (ex + 40 * qe) cx =
      muD (qe := qe) ey cy * mono (3 * ex) (cx ^ (3 : ℤ)) * gNum hqe ey cy ex cx + Jb hqe * InhV hqe ey cy ex cx := by
  have hX3 : OKX (qe := qe) ey cy 3 ex cx := by
    have := lamOK_down (N := 120 * qe) hX0
    rwa [show eX (qe := qe) ey 0 ex - ((120 * qe : ℕ) : ℤ) = eX (qe := qe) ey 3 ex by unfold eX; push_cast; ring]
      at this
  unfold gNum
  rw [g1_shift hqe ey cy hcy 0 ex hcx (by simpa using hX1), g1_shift hqe ey cy hcy 1 ex hcx (by simpa using hX2),
    g1_shift hqe ey cy hcy 2 ex hcx (by simpa using hX3),
    g2_shift hqe ey cy hcy 0 ex hcx hY0, g2_shift hqe ey cy hcy 1 ex hcx hY1, g2_shift hqe ey cy hcy 2 ex hcx hY2]
  simp only [show (0 : ℤ) + 1 = 1 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num, show (2 : ℤ) + 1 = 3 by norm_num]
  rw [g1_wrap hqe ey cy hcy ex hcx hX0]
  have u7 := u7_term hqe ey cy ex hcx hcy
  have hI2 : Finset.Icc (0 : ℤ) 2 = {0, 1, 2} := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; constructor <;> intro h <;> omega
  have hI7 : Finset.Icc (-7 : ℤ) (-1) = {-7, -6, -5, -4, -3, -2, -1} := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; constructor <;> intro h <;> omega
  unfold InhV
  rw [hI2, hI7]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
    Int.reduceEq, Int.reduceNeg, or_self, or_false, false_or, not_false_eq_true]
  norm_num at u7 ⊢
  ring_nf at u7 ⊢
  linear_combination (Jb hqe) * u7

end G373

end MTC
