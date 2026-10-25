/-
# The Appell–Lerch side `g_{1,4,1}(x, y, q, −1, −1)` and its functional equation in `x`

With `Q = q^{15}`, `A(X) = A(X, −1)` the Lambert numerator and `J̄ = j(−1; Q)`:

  `J̄ · g = j(x; q) A(X) + j(y; q) A(Y)`,   `X = q⁹ y x^{−4}`, `Y = q⁹ x y^{−4}`.

Under `x ↦ q^{15} x`:

* `g2_shift` — `G2(q^{15}x) = j(y; q) J̄ + μ_D x G2(x)`;
* `g1_shift` — `G1(q^{15}x) = μ_D x G1(x) − J̄ Σ_{u=−4}^{−1} (−1)^u q^{C(u,2)} y^u j(q^{15+4u} x; q)`;
* `gNum_FE` — `J̄ g(q^{15}x) = μ_D x J̄ g(x) + J̄ Inh(x)`.
-/
import RamanujanTau.MTC.F141
import RamanujanTau.MTC.G373

set_option autoImplicit false

namespace MTC.H141
open ALz HahnSeries Finset MTC

section G141
variable {qe : ℕ} (hqe : 1 ≤ qe) (ey : ℤ) (cy : ℂ)

lemma h15 (hqe : 1 ≤ qe) : 1 ≤ 15 * qe := by omega

/-- `J̄ = j(−1; q^{15})`. -/
noncomputable def Jb : L := θ (h15 hqe) 0 (-1)

/-- exponent and coefficient of `X = q⁹ y x^{−4}`. -/
def eX (ex : ℤ) : ℤ := 9 * qe + ey - 4 * ex
noncomputable def cX (cx : ℂ) : ℂ := cy * cx ^ (-4 : ℤ)

/-- exponent and coefficient of `Y = q⁹ x y^{−4}`. -/
def eY (ex : ℤ) : ℤ := 9 * qe + ex - 4 * ey
noncomputable def cY (cx : ℂ) : ℂ := cx * cy ^ (-4 : ℤ)

/-- `j(x; q) A(X)`. -/
noncomputable def g1 (ex : ℤ) (cx : ℂ) : L :=
  θ hqe ex cx * Av (h15 hqe) (eX (qe := qe) ey ex) (cX cy cx) 0 (-1)

/-- `j(y; q) A(Y)`. -/
noncomputable def g2 (ex : ℤ) (cx : ℂ) : L :=
  θ hqe ey cy * Av (h15 hqe) (eY (qe := qe) ey ex) (cY cy cx) 0 (-1)

def OKY (ex : ℤ) (cx : ℂ) : Prop := LamOK (15 * qe) (eY (qe := qe) ey ex) (cY cy cx) 0 (-1)
def OKX (ex : ℤ) (cx : ℂ) : Prop := LamOK (15 * qe) (eX (qe := qe) ey ex) (cX cy cx) 0 (-1)

lemma cX_ne {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) : cX cy cx ≠ 0 := by
  unfold cX; exact mul_ne_zero hcy (zpow_ne_zero _ hcx)

lemma cY_ne {cx : ℂ} (hcx : cx ≠ 0) (hcy : cy ≠ 0) : cY cy cx ≠ 0 := by
  unfold cY; exact mul_ne_zero hcx (zpow_ne_zero _ hcy)

include hqe in
/-- **second term**. -/
theorem g2_shift (hcy : cy ≠ 0) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hok : OKY (qe := qe) ey cy ex cx) :
    g2 hqe ey cy (ex + 15 * qe) cx =
      θ hqe ey cy * Jb hqe + muD (qe := qe) ey cy * mono ex cx * g2 hqe ey cy ex cx := by
  have hY := cY_ne cy hcx hcy
  have hs := Av_qshift (h15 hqe) hY (by norm_num : (-1 : ℂ) ≠ 0) hok
  have he : eY (qe := qe) ey (ex + 15 * qe) = eY (qe := qe) ey ex + ((15 * qe : ℕ) : ℤ) := by
    unfold eY; push_cast; ring
  unfold g2
  rw [he, show Av (h15 hqe) (eY ey ex + ((15 * qe : ℕ) : ℤ)) (cY cy cx) 0 (-1) =
    θ (h15 hqe) 0 (-1) - mono (eY ey ex) (cY cy cx) * Av (h15 hqe) (eY ey ex) (cY cy cx) 0 (-1) by
      linear_combination hs]
  have m2 : muD (qe := qe) ey cy * mono ex cx = -mono (eY (qe := qe) ey ex) (cY cy cx) := by
    unfold muD cY eY
    rw [mono_mul]
    rw [show -(mono (9 * qe + ex - 4 * ey) (cx * cy ^ (-4 : ℤ)) : L) =
      mono (9 * qe + ex - 4 * ey) (-(cx * cy ^ (-4 : ℤ))) by simp [mono]]
    exact mono_ext (by ring) (by ring)
  rw [Jb]
  linear_combination -(θ hqe ey cy * Av (h15 hqe) (eY ey ex) (cY cy cx) 0 (-1)) * m2

/-- the multiplier `a_e = q^{15} … ` of `Av_down`. -/
noncomputable def aD (e : ℤ) (c : ℂ) : L := mono (((15 * qe : ℕ) : ℤ) - e) c⁻¹

include hqe in
/-- **first term**. -/
theorem g1_shift (hcy : cy ≠ 0) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0) (hok : OKX (qe := qe) ey cy ex cx) :
    g1 hqe ey cy (ex + 15 * qe) cx =
      muD (qe := qe) ey cy * mono ex cx * g1 hqe ey cy ex cx -
      Jb hqe * ∑ u ∈ Finset.Icc (-4 : ℤ) (-1),
        mono (qe * c2 u + ey * u) ((-1) ^ u * cy ^ u) * θ hqe (15 * qe + 4 * qe * u + ex) cx := by
  have hX := cX_ne cy hcx hcy
  have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
  set E := eX (qe := qe) ey ex with hE
  set c := cX cy cx with hc
  set N : ℤ := ((15 * qe : ℕ) : ℤ) with hN
  have ok1 : LamOK (15 * qe) (E - N) c 0 (-1) := lamOK_down hok
  have ok2 : LamOK (15 * qe) (E - N - N) c 0 (-1) := lamOK_down ok1
  have ok3 : LamOK (15 * qe) (E - N - N - N) c 0 (-1) := lamOK_down ok2
  have ok4 : LamOK (15 * qe) (E - N - N - N - N) c 0 (-1) := lamOK_down ok3
  have a1 := Av_down (h15 hqe) hX hm1 ok1
  have a2 := Av_down (h15 hqe) hX hm1 ok2
  have a3 := Av_down (h15 hqe) hX hm1 ok3
  have a4 := Av_down (h15 hqe) hX hm1 ok4
  rw [← hN] at a1 a2 a3 a4
  have he : eX (qe := qe) ey (ex + 15 * qe) = E - N - N - N - N := by
    rw [hE, hN]; unfold eX; push_cast; ring
  have hθ0 := θ_qshift hqe ex hcx 15
  have hθ1 := θ_qshift hqe ex hcx 11
  have hθ2 := θ_qshift hqe ex hcx 7
  have hθ3 := θ_qshift hqe ex hcx 3
  have hθ4 := θ_qshift hqe ex hcx (-1)
  have hI : Finset.Icc (-4 : ℤ) (-1) = {-4, -3, -2, -1} := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; constructor <;> intro h <;> omega
  rw [hI]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
    Int.reduceEq, Int.reduceNeg, or_self, not_false_eq_true]
  rw [show 15 * (qe : ℤ) + 4 * qe * (-4) + ex = ex + ((qe : ℕ) : ℤ) * (-1) by ring, hθ4,
    show 15 * (qe : ℤ) + 4 * qe * (-3) + ex = ex + ((qe : ℕ) : ℤ) * 3 by ring, hθ3,
    show 15 * (qe : ℤ) + 4 * qe * (-2) + ex = ex + ((qe : ℕ) : ℤ) * 7 by ring, hθ2,
    show 15 * (qe : ℤ) + 4 * qe * (-1) + ex = ex + ((qe : ℕ) : ℤ) * 11 by ring, hθ1]
  unfold g1
  rw [he, a4, a3, a2, a1, show ex + 15 * (qe : ℤ) = ex + ((qe : ℕ) : ℤ) * 15 by ring, hθ0, ← hE, ← hc]
  unfold Jb
  have hcinv : c⁻¹ = cy⁻¹ * cx ^ (4 : ℤ) := by
    rw [hc]; unfold cX; rw [mul_inv, zpow_neg, inv_inv]
  set M0 := mono (-((qe : ℤ) * c2 (15 + 1)) - ex * 15 + (qe : ℤ) * 15) ((-1) ^ (15 : ℤ) * cx ^ (-15 : ℤ))
  -- the homogeneous coefficient
  have hhom : M0 * (mono (N - (E - N - N - N)) c⁻¹ * (mono (N - (E - N - N)) c⁻¹ *
      (mono (N - (E - N)) c⁻¹ * mono (N - E) c⁻¹))) = muD (qe := qe) ey cy * mono ex cx := by
    simp only [M0, muD, mono_mul]
    apply mono_ext
    · rw [show c2 (15 + 1) = 120 by decide, hE, hN]; unfold eX; push_cast; ring
    · rw [hcinv]; simp only [zpow_neg]; field_simp; try norm_num; try field_simp; try ring
  have k1 : M0 * mono (N - (E - N - N - N)) c⁻¹ =
      -(mono (qe * c2 (-1) + ey * -1) ((-1) ^ (-1 : ℤ) * cy ^ (-1 : ℤ)) *
        mono (-((qe : ℤ) * c2 (11 + 1)) - ex * 11 + (qe : ℤ) * 11) ((-1) ^ (11 : ℤ) * cx ^ (-11 : ℤ))) := by
    simp only [M0, mono_mul]
    rw [show -(mono (qe * c2 (-1) + ey * -1 + (-((qe : ℤ) * c2 (11 + 1)) - ex * 11 + (qe : ℤ) * 11))
        ((-1) ^ (-1 : ℤ) * cy ^ (-1 : ℤ) * ((-1) ^ (11 : ℤ) * cx ^ (-11 : ℤ))) : L) =
      mono (qe * c2 (-1) + ey * -1 + (-((qe : ℤ) * c2 (11 + 1)) - ex * 11 + (qe : ℤ) * 11))
        (-((-1) ^ (-1 : ℤ) * cy ^ (-1 : ℤ) * ((-1) ^ (11 : ℤ) * cx ^ (-11 : ℤ)))) by simp [mono]]
    apply mono_ext
    · rw [show c2 (15 + 1) = 120 by decide, show c2 (11 + 1) = 66 by decide, show c2 (-1) = 1 by decide,
        hE, hN]; unfold eX; push_cast; ring
    · rw [hcinv]; simp only [zpow_neg]; field_simp; try norm_num; try field_simp; try ring
  have k2 : M0 * (mono (N - (E - N - N - N)) c⁻¹ * mono (N - (E - N - N)) c⁻¹) =
      mono (qe * c2 (-2) + ey * -2) ((-1) ^ (-2 : ℤ) * cy ^ (-2 : ℤ)) *
        mono (-((qe : ℤ) * c2 (7 + 1)) - ex * 7 + (qe : ℤ) * 7) ((-1) ^ (7 : ℤ) * cx ^ (-7 : ℤ)) := by
    simp only [M0, mono_mul]
    apply mono_ext
    · rw [show c2 (15 + 1) = 120 by decide, show c2 (7 + 1) = 28 by decide, show c2 (-2) = 3 by decide,
        hE, hN]; unfold eX; push_cast; ring
    · rw [hcinv]; simp only [zpow_neg]; field_simp; try norm_num; try field_simp; try ring
  have k3 : M0 * (mono (N - (E - N - N - N)) c⁻¹ * (mono (N - (E - N - N)) c⁻¹ * mono (N - (E - N)) c⁻¹)) =
      -(mono (qe * c2 (-3) + ey * -3) ((-1) ^ (-3 : ℤ) * cy ^ (-3 : ℤ)) *
        mono (-((qe : ℤ) * c2 (3 + 1)) - ex * 3 + (qe : ℤ) * 3) ((-1) ^ (3 : ℤ) * cx ^ (-3 : ℤ))) := by
    simp only [M0, mono_mul]
    rw [show -(mono (qe * c2 (-3) + ey * -3 + (-((qe : ℤ) * c2 (3 + 1)) - ex * 3 + (qe : ℤ) * 3))
        ((-1) ^ (-3 : ℤ) * cy ^ (-3 : ℤ) * ((-1) ^ (3 : ℤ) * cx ^ (-3 : ℤ))) : L) =
      mono (qe * c2 (-3) + ey * -3 + (-((qe : ℤ) * c2 (3 + 1)) - ex * 3 + (qe : ℤ) * 3))
        (-((-1) ^ (-3 : ℤ) * cy ^ (-3 : ℤ) * ((-1) ^ (3 : ℤ) * cx ^ (-3 : ℤ)))) by simp [mono]]
    apply mono_ext
    · rw [show c2 (15 + 1) = 120 by decide, show c2 (3 + 1) = 6 by decide, show c2 (-3) = 6 by decide,
        hE, hN]; unfold eX; push_cast; ring
    · rw [hcinv]; simp only [zpow_neg]; field_simp; try norm_num; try field_simp; try ring
  have k4 : M0 * (mono (N - (E - N - N - N)) c⁻¹ * (mono (N - (E - N - N)) c⁻¹ *
      (mono (N - (E - N)) c⁻¹ * mono (N - E) c⁻¹))) =
      mono (qe * c2 (-4) + ey * -4) ((-1) ^ (-4 : ℤ) * cy ^ (-4 : ℤ)) *
        mono (-((qe : ℤ) * c2 (-1 + 1)) - ex * -1 + (qe : ℤ) * -1) ((-1) ^ (-1 : ℤ) * cx ^ (- -1 : ℤ)) := by
    simp only [M0, mono_mul]
    apply mono_ext
    · rw [show c2 (15 + 1) = 120 by decide, show c2 (-1 + 1) = 0 by decide, show c2 (-4) = 10 by decide,
        hE, hN]; unfold eX; push_cast; ring
    · rw [hcinv]; simp only [zpow_neg]; field_simp; try norm_num; try field_simp; try ring
  linear_combination θ hqe ex cx * Av (h15 hqe) E c 0 (-1) * hhom +
    θ hqe ex cx * θ (h15 hqe) 0 (-1) * k1 - θ hqe ex cx * θ (h15 hqe) 0 (-1) * k2 +
    θ hqe ex cx * θ (h15 hqe) 0 (-1) * k3 - θ hqe ex cx * θ (h15 hqe) 0 (-1) * k4

/-- `J̄ · g_{1,4,1}(x, y, q, −1, −1)`. -/
noncomputable def gNum (ex : ℤ) (cx : ℂ) : L := g1 hqe ey cy ex cx + g2 hqe ey cy ex cx

include hqe in
/-- **HM Prop 5.5 for `g`**: `J̄ g(q^{15}x) = μ_D x J̄ g(x) + J̄ Inh(x)`. -/
theorem gNum_FE (hcy : cy ≠ 0) (ex : ℤ) {cx : ℂ} (hcx : cx ≠ 0)
    (hX : OKX (qe := qe) ey cy ex cx) (hY : OKY (qe := qe) ey cy ex cx) :
    gNum hqe ey cy (ex + 15 * qe) cx =
      muD (qe := qe) ey cy * mono ex cx * gNum hqe ey cy ex cx + Jb hqe * InhV hqe ey cy ex cx := by
  unfold gNum InhV
  rw [g1_shift hqe ey cy hcy ex hcx hX, g2_shift hqe ey cy hcy ex hcx hY]
  ring

end G141

end MTC.H141
