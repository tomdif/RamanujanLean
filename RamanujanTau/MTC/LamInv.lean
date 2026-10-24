/-
# HM (2.2b) for the Lambert numerator: `A(x⁻¹, z⁻¹) = −x z⁻¹ A(x, z)`

(Equivalently `m(x, q, z) = x⁻¹ m(x⁻¹, q, z⁻¹)`.) Termwise, `r ↦ 2 − r`: with `w = q^{r−1} x z`,
`(1 − w⁻¹)⁻¹ = −w (1 − w)⁻¹` and `C(2 − r, 2) = C(r, 2) − r + 1`.
-/
import RamanujanTau.MTC.LamAb

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

lemma inv_flipc {E : ℤ} {c : ℂ} (hc : c ≠ 0) (h : ¬(E = 0 ∧ c = 1)) :
    (1 - mono (-E) c⁻¹ : L)⁻¹ = -mono E c * (1 - mono E c)⁻¹ := by
  have hw : (mono E c : L) ≠ 0 := by simp [mono, hc]
  have h1 : (1 : L) - mono E c ≠ 0 := one_sub_mono_ne_zero h
  have h2 : (mono E c : L) - 1 ≠ 0 := fun h' => h1 (by linear_combination -h')
  have hm : (mono (-E) c⁻¹ : L) = (mono E c)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [mono_mul, show (1 : L) = mono 0 1 from rfl]
    exact mono_ext_b (by ring) (inv_mul_cancel₀ hc)
  rw [hm]
  field_simp
  ring

lemma c2_two_sub (i : ℤ) : c2 (2 - i) = c2 i - i + 1 := by
  have h1 := c2_one_sub (i - 1)
  have h2 := c2_succ (i - 1)
  rw [show 1 - (i - 1) = 2 - i by ring] at h1
  rw [show i - 1 + 1 = i by ring] at h2
  linarith

section Inv
variable {N : ℕ} (hN : 1 ≤ N)

lemma lamOK_inv {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (hok : LamOK N ex cx ez cz) :
    LamOK N (-ex) cx⁻¹ (-ez) cz⁻¹ := fun r h => hok (2 - r) ⟨by have h1 := h.1; unfold wE at *; linear_combination -h1, by
  have := h.2
  rw [← mul_inv] at this
  exact inv_eq_one.mp this⟩

lemma lamT_inv {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (hx : cx ≠ 0) (hz : cz ≠ 0) (hok : LamOK N ex cx ez cz)
    (i : ℤ) :
    lamT N (-ex) cx⁻¹ (-ez) cz⁻¹ (2 - i) = (-(mono ex cx * mono (-ez) cz⁻¹)) * lamT N ex cx ez cz i := by
  unfold lamT
  have hw : wE N (-ex) (-ez) (2 - i) = -wE N ex ez i := by unfold wE; ring
  rw [hw, show cx⁻¹ * cz⁻¹ = (cx * cz)⁻¹ by rw [mul_inv], inv_flipc (mul_ne_zero hx hz) (hok i)]
  have hM : (mono (N * c2 (2 - i) + -ez * (2 - i)) ((-1) ^ (2 - i) * cz⁻¹ ^ (2 - i)) : L) *
      mono (wE N ex ez i) (cx * cz) =
      mono ex cx * mono (-ez) cz⁻¹ * mono (N * c2 i + ez * i) ((-1) ^ i * cz ^ i) := by
    rw [mono_mul, mono_mul, mono_mul]
    refine mono_ext_b (by unfold wE; rw [c2_two_sub]; ring) ?_
    have e1 : ((-1 : ℂ)) ^ (2 - i) = (-1) ^ i := by
      rw [show (2 - i) = i + 2 * (1 - i) by ring, zpow_add₀ (by norm_num), zpow_mul]; norm_num
    have e2 : cz⁻¹ ^ (2 - i) * cz = cz⁻¹ * cz ^ i := by
      rw [inv_zpow', show -(2 - i) = i - 2 by ring, zpow_sub₀ hz]
      field_simp
      first | done | ring
    rw [e1]
    linear_combination ((-1 : ℂ) ^ i * cx) * e2
  linear_combination (-(1 - mono (wE N ex ez i) (cx * cz) : L)⁻¹) * hM

/-- **HM (2.2b)**: `A(x⁻¹, z⁻¹) = −x z⁻¹ A(x, z)`. -/
theorem Alam_inv {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (hx : cx ≠ 0) (hz : cz ≠ 0) (hok : LamOK N ex cx ez cz) :
    Alam hN (inv_ne_zero hx) (inv_ne_zero hz) (lamOK_inv hok) = -(mono ex cx * mono (-ez) cz⁻¹) * Alam hN hx hz hok := by
  unfold Alam
  exact hsum_reindex _ _ (Equiv.subLeft 2) _ fun i => by
    rw [Equiv.subLeft_apply]
    exact lamT_inv hx hz hok i

lemma lamOK_zshift {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (hok : LamOK N ex cx ez cz) :
    LamOK N ex cx (ez + N) cz := fun r h => hok (r + 1) ⟨by have h1 := h.1; unfold wE at *; linear_combination h1, h.2⟩

lemma lamT_zshift {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (hz : cz ≠ 0) (r : ℤ) :
    lamT N ex cx ez cz (r + 1) = -mono ez cz * lamT N ex cx (ez + N) cz r := by
  unfold lamT
  rw [show wE N ex ez (r + 1) = wE N ex (ez + N) r by unfold wE; ring]
  have h : (mono (N * c2 (r + 1) + ez * (r + 1)) ((-1) ^ (r + 1) * cz ^ (r + 1)) : L) =
      -(mono ez cz * mono (N * c2 r + (ez + N) * r) ((-1) ^ r * cz ^ r)) := by
    rw [mono_mul, show -(mono (ez + (N * c2 r + (ez + N) * r)) (cz * ((-1) ^ r * cz ^ r)) : L) =
      mono (ez + (N * c2 r + (ez + N) * r)) (-(cz * ((-1) ^ r * cz ^ r))) by simp [mono]]
    refine mono_ext_b (by rw [c2_succ]; ring) ?_
    rw [zpow_add_one₀ (by norm_num), zpow_add_one₀ hz]; ring
  rw [h]; ring

/-- **HM (2.2a)** for the numerator: `A(x, z) = −z A(x, qz)`, i.e. `m(x, q, qz) = m(x, q, z)`. -/
theorem Alam_zshift {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (hx : cx ≠ 0) (hz : cz ≠ 0) (hok : LamOK N ex cx ez cz) :
    Alam hN hx hz hok = -mono ez cz * Alam hN hx hz (lamOK_zshift hok) := by
  unfold Alam
  exact hsum_reindex _ _ (Equiv.addRight 1) _ fun r => by
    rw [Equiv.coe_addRight]
    exact lamT_zshift hz r

end Inv

end MTC
