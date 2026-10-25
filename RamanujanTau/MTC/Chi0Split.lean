/-
# The `n = 2` splitting of an Appell–Lerch numerator

For `A_N(x, z) = Σ_r (−1)^r z^r q^{C(r,2)} / (1 − q^{r−1} x z)` (`Alam`, `q = t^N`) with `x = t^{ex}`, `z = t^{ez}`:
splitting `r = 2s + ρ` and `1/(1 − u) = (1 + u)/(1 − u²)` gives four numerators in base `t^{4N}` with `z = −t^{…}`:

  `A_N(t^{ex}, t^{ez}) = Σ_{ρ∈{0,1}} (−1)^ρ t^{N C(ρ,2) + ez ρ}
      [A_{4N}(−t^{N+2ex}, −t^{N(1+2ρ)+2ez}) + t^{N(ρ−1)+ex+ez} A_{4N}(−t^{2ex−N}, −t^{N(3+2ρ)+2ez})]`  (`Av_split2`).
-/
import RamanujanTau.MTC.Chi0AL

set_option autoImplicit false

namespace MTC.Chi0L
open ALz HahnSeries Finset MTC

section Split2
variable {N : ℕ} (hN : 1 ≤ N)

include hN in
lemma h4N : 1 ≤ 4 * N := by omega

lemma lamOK_of_wE {M : ℕ} {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (h : ∀ r, wE M ex ez r ≠ 0) :
    LamOK M ex cx ez cz := fun r hr => h r hr.1

lemma inv_split (w : ℤ) (hw : w ≠ 0) :
    (1 - mono w 1 : L)⁻¹ = (1 - mono (2 * w) 1)⁻¹ + mono w 1 * (1 - mono (2 * w) 1)⁻¹ := by
  have h1 : (1 - mono w 1 : L) ≠ 0 := fun h => mono_ne_one hw (by linear_combination -h)
  have h2 : (1 + mono w 1 : L) ≠ 0 := by
    intro h
    have := congrArg (fun f : L => f.coeff w) h
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_one, mono, HahnSeries.coeff_single_same, if_neg hw,
      HahnSeries.coeff_zero] at this
    norm_num at this
  have hsq : (1 - mono (2 * w) 1 : L) = (1 - mono w 1) * (1 + mono w 1) := by
    rw [show (1 - mono w 1 : L) * (1 + mono w 1) = 1 - mono w 1 * mono w 1 by ring, mono_mul]
    congr 2 <;> ring
  rw [hsq, mul_inv]
  field_simp

variable (ex ez : ℤ) (hw : ∀ r, wE N ex ez r ≠ 0)
include hw

lemma hwA (ρ : ℤ) : ∀ s, wE (4 * N) (N + 2 * ex) (N * (1 + 2 * ρ) + 2 * ez) s ≠ 0 := fun s h => by
  apply hw (2 * s + ρ); unfold wE at *; push_cast at *; linarith

lemma hwB (ρ : ℤ) : ∀ s, wE (4 * N) (2 * ex - N) (N * (3 + 2 * ρ) + 2 * ez) s ≠ 0 := fun s h => by
  apply hw (2 * s + ρ); unfold wE at *; push_cast at *; linarith

/-- the `ρ`-part of the split, as a summable family over `s`. -/
noncomputable def splitF (ρ : ℤ) : SummableFamily ℤ ℂ ℤ :=
  lamF (h4N hN) (by norm_num : (-1 : ℂ) ≠ 0) (by norm_num : (-1 : ℂ) ≠ 0) (lamOK_of_wE (hwA ex ez hw ρ)) +
    (mono (N * (ρ - 1) + ex + ez) 1 : L) •
      lamF (h4N hN) (by norm_num : (-1 : ℂ) ≠ 0) (by norm_num : (-1 : ℂ) ≠ 0) (lamOK_of_wE (hwB ex ez hw ρ))

lemma lamT_split (ρ s : ℤ) (hρ : ρ = 0 ∨ ρ = 1) :
    lamT N ex 1 ez 1 (2 * s + ρ) = mono (N * c2 ρ + ez * ρ) ((-1) ^ ρ) * splitF hN ex ez hw ρ s := by
  unfold splitF
  simp only [SummableFamily.add_apply, SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul, lamF,
    ofSupp_apply]
  unfold lamT
  have hw0 := hw (2 * s + ρ)
  rw [one_mul, inv_split (wE N ex ez (2 * s + ρ)) hw0]
  have e1 : wE (4 * N) (N + 2 * ex) (N * (1 + 2 * ρ) + 2 * ez) s = 2 * wE N ex ez (2 * s + ρ) := by
    unfold wE; push_cast; ring
  have e2 : wE (4 * N) (2 * ex - N) (N * (3 + 2 * ρ) + 2 * ez) s = 2 * wE N ex ez (2 * s + ρ) := by
    unfold wE; push_cast; ring
  rw [e1, e2, show ((-1 : ℂ)) * (-1) = 1 by norm_num, mul_add]
  have hc2 : c2 (2 * s + ρ) = 4 * c2 s + s * (1 + 2 * ρ) + c2 ρ := by
    have := two_c2 (2 * s + ρ); have := two_c2 s; have := two_c2 ρ
    rcases hρ with rfl | rfl <;> nlinarith
  simp only [mul_add, ← mul_assoc, mono_mul]
  congr 1 <;> refine congrArg (· * _) (mono_ext ?_ ?_)
  · push_cast; rw [hc2]; ring
  · have := neg_one_zpow_sq s; rw [zpow_add₀ (by norm_num), zpow_mul]; norm_num; linear_combination -(-1 : ℂ) ^ ρ * this
  · unfold wE; push_cast; rw [hc2]; ring
  · have := neg_one_zpow_sq s; rw [zpow_add₀ (by norm_num), zpow_mul]; norm_num; linear_combination -(-1 : ℂ) ^ ρ * this

theorem Alam_split2 :
    Alam hN one_ne_zero one_ne_zero (lamOK_of_wE (cx := 1) (cz := 1) hw) =
      hs (splitF hN ex ez hw 0) + mono (ez) (-1) * hs (splitF hN ex ez hw 1) := by
  unfold Alam
  have h := hs_split (lamF hN one_ne_zero one_ne_zero (lamOK_of_wE (cx := 1) (cz := 1) hw))
    (splitF hN ex ez hw 0) ((mono ez (-1) : L) • splitF hN ex ez hw 1) eEO
    (fun m => by
      simp only [lamF, ofSupp_apply, eEO, Equiv.coe_fn_mk, Sum.elim_inl]
      rw [show 2 * m = 2 * m + 0 by ring, lamT_split hN ex ez hw 0 m (Or.inl rfl)]
      rw [show (mono (N * c2 0 + ez * 0) ((-1) ^ (0 : ℤ)) : L) = 1 by simp [c2, mono], one_mul])
    (fun m => by
      simp only [lamF, ofSupp_apply, eEO, Equiv.coe_fn_mk, Sum.elim_inr, SummableFamily.smul_apply,
        HahnSeries.of_symm_smul_of_eq_mul]
      rw [lamT_split hN ex ez hw 1 m (Or.inr rfl)]
      congr 1
      exact mono_ext (by simp [c2]) (by norm_num))
  rw [h, hs_eq (_ • _), SummableFamily.hsum_smul, ← hs_eq]

end Split2

/-! ## Change of `z` to `−1` in base `t^{360}` -/

/-- `j(c t^e; t^{360})`. -/
noncomputable def th360 (e : ℤ) (c : ℂ) : L := θ hN360 e c

lemma mono_ne_one' {e : ℤ} {c : ℂ} (h : e ≠ 0 ∨ c ≠ 1) : (mono e c : L) ≠ 1 := by
  intro hm
  have := congrArg (fun f : L => f.coeff 0) hm
  by_cases he : e = 0
  · subst he
    simp [mono] at this
    rcases h with h | h
    · exact h rfl
    · exact h this
  · simp [mono, HahnSeries.coeff_single_of_ne (Ne.symm he)] at this

lemma lamOK360 {e : ℤ} {cx cz : ℂ} (he : e % 360 ≠ 0) (ez : ℤ) (hz : ez = 0) : LamOK (10 * 36) e cx ez cz :=
  fun r ⟨h1, _⟩ => by
    apply he; unfold wE at h1; push_cast at h1; subst hz
    rw [show e = 360 * (1 - r) by linarith]; simp

lemma lamOK360' {a b : ℤ} {cx cz : ℂ} (h : (a + b) % 360 ≠ 0) : LamOK (10 * 36) a cx b cz :=
  fun r ⟨h1, _⟩ => by
    apply h; unfold wE at h1; push_cast at h1
    rw [show a + b = 360 * (1 - r) by linarith]; simp

/-- `J̄ A(−t^a, −t^{b₀}) = j(−t^{b₀}) A(−t^a, −1) + (theta quotient)`. -/
theorem czB {a b0 : ℤ} (h1 : -360 < a) (h2 : a < 360) (ha0 : a ≠ 0) (h3 : 1 ≤ a + b0) (h4 : a + b0 ≤ 359)
    (h5 : 1 ≤ b0) (h6 : b0 ≤ 359) (hθa : θ hN360 a 1 ≠ 0) :
    Jb6 * Av hN360 a (-1) b0 (-1) = th360 b0 (-1) * Bv a +
      mono b0 (-1) * hs (kF hN360 0) * θ hN360 (-b0) 1 * θ hN360 (a + b0) (-1) /
        (θ hN360 (a + b0) 1 * θ hN360 a 1) := by
  have h := change_of_z2 hN360 (a := a) (b₀ := b0) (b₁ := 0) (by push_cast; omega) (by push_cast; omega)
    (by omega) (by push_cast; omega) h5 (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)
    (cx := -1) (c₀ := -1) (c₁ := -1) (by norm_num) (by norm_num) (by norm_num)
    (mono_ne_one' (Or.inr (by norm_num))) (mono_ne_one' (Or.inl (by omega)))
  rw [← Av_eq_Ab' hN360 (by norm_num) (by norm_num) (lamOK360 (cx := -1) (cz := -1) (by omega) 0 rfl),
    ← Av_eq_Ab' hN360 (by norm_num) (by norm_num) (lamOK360' (cx := -1) (cz := -1) (by omega))] at h
  have hθb : θ hN360 (a + b0) 1 ≠ 0 := θ_ne hN360 (by omega) (by push_cast; omega) 1
  simp only [add_zero, show ((-1 : ℂ)) * (-1) = 1 by norm_num, inv_neg, inv_one, neg_neg,
    show (-b0 + 0) = -b0 by ring, show ((-1 : ℂ)) * (-1) * (-1) = -1 by norm_num,
    show (1 : ℂ) * (-1) = -1 by norm_num, show ((-1 : ℂ)) * 1 = -1 by norm_num] at h
  unfold Jb6 th360 Bv
  field_simp
  linear_combination -h
