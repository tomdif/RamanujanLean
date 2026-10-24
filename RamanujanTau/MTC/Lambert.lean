/-
# Appell–Lerch sums as Lambert series at monomial points

For `q = t^N`, `x = cx t^{ex}`, `z = cz t^{ez}` the Appell–Lerch numerator
`A(x, z) = Σ_r (−1)^r q^{C(r,2)} z^r / (1 − q^{r−1} x z)` is a convergent sum in `ℂ((t))` (every
`(1 − w)⁻¹` has nonnegative valuation). Then `m(x, q, z) = A(x, z) / j(z; q)`.

* `inv_one_sub_vge` — `(1 − c tᵉ)⁻¹` has nonnegative valuation.
* `Alam_qshift` — `A(qx, z) + x·A(x, z) = j(z; q)`, i.e. HM (2.2c) `m(qx) = 1 − x m(x)`.
-/
import RamanujanTau.MTC.ThFactor
import RamanujanTau.ALRank7
import RamanujanTau.ALSplitM

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

/-! ## Inverses of `1 − c tᵉ` -/

lemma one_sub_mono_ne_zero {e : ℤ} {c : ℂ} (h : ¬(e = 0 ∧ c = 1)) : (1 : L) - mono e c ≠ 0 := by
  intro h0
  by_cases he : e = 0
  · subst he
    have := congrArg (fun f : L => f.coeff 0) h0
    simp only [mono, coeff_sub, HahnSeries.coeff_one, if_true, coeff_single_same, HahnSeries.coeff_zero] at this
    exact h ⟨rfl, by linear_combination -this⟩
  · have := congrArg (fun f : L => f.coeff 0) h0
    simp only [mono, coeff_sub, HahnSeries.coeff_one, if_true, HahnSeries.coeff_zero] at this
    rw [coeff_single_of_ne (Ne.symm he)] at this
    simp at this

lemma inv_one_sub_vge {e : ℤ} {c : ℂ} (hc : c ≠ 0) (h : ¬(e = 0 ∧ c = 1)) : vge ((1 - mono e c)⁻¹) 0 := by
  rcases lt_trichotomy e 0 with he | rfl | he
  · -- `1 − w = −w (1 − w⁻¹)` with `w⁻¹` of positive order
    have hpos : 0 < -e := by omega
    have h1 : mono e c * mono (-e) c⁻¹ = 1 := by
      rw [mono_mul, add_neg_cancel, mul_inv_cancel₀ hc]; rfl
    have hg := hs_geoP (-e) c⁻¹ hpos
    have hinv : ((1 : L) - mono e c)⁻¹ = -mono (-e) c⁻¹ * hs (geoP (-e) c⁻¹ hpos) := by
      apply inv_eq_of_mul_eq_one_right
      linear_combination (hs (geoP (-e) c⁻¹ hpos)) * h1 + hg
    rw [hinv]
    refine vge_mono (vge_mul (vge_neg (vge_single _ _)) (vge_hs _ fun j => ?_)) (by omega : (0 : ℤ) ≤ -e + 0)
    rw [geoP_apply]
    split_ifs with hj
    · exact vge_mono (vge_single _ _) (by nlinarith)
    · exact vge_zero _
  · -- constant
    have hc1 : c ≠ 1 := fun h1 => h ⟨rfl, h1⟩
    have : ((1 : L) - mono 0 c)⁻¹ = mono 0 (1 - c)⁻¹ := by
      rw [show (1 : L) - mono 0 c = mono 0 (1 - c) by simp [mono, single_sub], mono, inv_single, neg_zero]
    rw [this]; exact vge_single _ _
  · have hg := hs_geoP e c he
    have hne : (1 : L) - mono e c ≠ 0 := one_sub_mono_ne_zero h
    have : ((1 : L) - mono e c)⁻¹ = hs (geoP e c he) := by
      rw [inv_eq_of_mul_eq_one_right hg]
    rw [this]
    refine vge_hs _ fun j => ?_
    rw [geoP_apply]
    split_ifs with hj
    · exact vge_mono (vge_single _ _) (by nlinarith)
    · exact vge_zero _

/-! ## The Lambert numerator -/

section Lam
variable {N : ℕ} (hN : 1 ≤ N)

/-- exponent of `q^{r−1} x z`. -/
def wE (N : ℕ) (ex ez r : ℤ) : ℤ := N * (r - 1) + ex + ez

/-- `x z` avoids the lattice `q^ℤ`, so every denominator `1 − q^{r−1} x z` is nonzero. -/
def LamOK (N : ℕ) (ex : ℤ) (cx : ℂ) (ez : ℤ) (cz : ℂ) : Prop := ∀ r : ℤ, ¬(wE N ex ez r = 0 ∧ cx * cz = 1)

/-- the `r`-th Lambert term `(−1)^r q^{C(r,2)} z^r (1 − q^{r−1} x z)⁻¹`. -/
noncomputable def lamT (N : ℕ) (ex : ℤ) (cx : ℂ) (ez : ℤ) (cz : ℂ) (r : ℤ) : L :=
  mono (N * c2 r + ez * r) ((-1) ^ r * cz ^ r) * (1 - mono (wE N ex ez r) (cx * cz))⁻¹

include hN in
lemma lamT_vge {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (hx : cx ≠ 0) (hz : cz ≠ 0) (hok : LamOK N ex cx ez cz)
    (r : ℤ) : vge (lamT N ex cx ez cz r) (N * c2 r + ez * r) := by
  have := vge_mul (vge_single (N * c2 r + ez * r) ((-1) ^ r * cz ^ r))
    (inv_one_sub_vge (mul_ne_zero hx hz) (hok r))
  simpa using this

/-- the Lambert family. -/
noncomputable def lamF {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (hx : cx ≠ 0) (hz : cz ≠ 0)
    (hok : LamOK N ex cx ez cz) : SummableFamily ℤ ℂ ℤ :=
  ofSupp (lamT N ex cx ez cz) (-(ez * ez) - 1)
    (fun r n hn => by
      by_contra h
      have h1 := lamT_vge hN hx hz hok r n h
      have := thE_lb (N := N) hN ez r
      unfold thE at this
      omega)
    (fun n => (Set.finite_Icc (-(2 * |n| + 2 * |ez| + 1)) (2 * |n| + 2 * |ez| + 1)).subset fun r hr => by
      have h1 := lamT_vge hN hx hz hok r n hr
      have := thE_le_bound (N := N) hN ez r n (by unfold thE; omega)
      exact ⟨by rw [abs_le] at this; exact this.1, by rw [abs_le] at this; exact this.2⟩)

include hN in
lemma lamOK_shift {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (hok : LamOK N ex cx ez cz) :
    LamOK N (ex + N) cx ez cz := fun r h => hok (r + 1) ⟨by unfold wE at *; linarith [h.1], h.2⟩

/-- the Appell–Lerch numerator `A(x, z) = j(z) m(x, q, z)`. -/
noncomputable def Alam {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (hx : cx ≠ 0) (hz : cz ≠ 0)
    (hok : LamOK N ex cx ez cz) : L := hs (lamF hN hx hz hok)

/-- **HM (2.2c)** for the numerator: `A(qx, z) + x A(x, z) = j(z)`. -/
theorem Alam_qshift {ex : ℤ} {cx : ℂ} {ez : ℤ} {cz : ℂ} (hx : cx ≠ 0) (hz : cz ≠ 0)
    (hok : LamOK N ex cx ez cz) :
    Alam hN hx hz (lamOK_shift hN hok) + mono ex cx * Alam hN hx hz hok = θ hN ez cz := by
  unfold Alam
  rw [hs, hs, ← SummableFamily.hsum_smul, ← SummableFamily.hsum_equiv (Equiv.addRight (-1))
    (mono ex cx • lamF hN hx hz hok), ← SummableFamily.hsum_add, θ, hs]
  congr 1
  ext r : 1
  simp only [SummableFamily.add_apply, SummableFamily.Equiv_toFun, SummableFamily.smul_apply,
    HahnSeries.of_symm_smul_of_eq_mul, Equiv.coe_addRight, Equiv.symm_apply_eq, lamF, ofSupp_apply,
    thF, monoFam_apply]
  rw [show (Equiv.addRight (-1 : ℤ)).symm r = r + 1 by simp]
  simp only [lamT]
  have hw : wE N (ex + N) ez r = wE N ex ez (r + 1) := by unfold wE; ring
  rw [hw]
  have hne := one_sub_mono_ne_zero (hok (r + 1))
  set w := mono (wE N ex ez (r + 1)) (cx * cz)
  have hE : mono ex cx * mono (N * c2 (r + 1) + ez * (r + 1)) ((-1) ^ (r + 1) * cz ^ (r + 1)) =
      -(mono (thE N ez r) (thC cz r) * w) := by
    have hr : -(mono (thE N ez r) (thC cz r) * w) =
        mono (thE N ez r + wE N ex ez (r + 1)) (-(thC cz r * (cx * cz))) := by
      simp only [w, mono_mul, mono, single_neg]
    rw [hr, mono_mul]
    simp only [thE, thC, wE, c2_succ]
    congr 1
    · ring
    · rw [zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_add_one₀ hz]; ring
  have : mono (N * c2 r + ez * r) ((-1) ^ r * cz ^ r) = mono (thE N ez r) (thC cz r) := rfl
  rw [this, ← mul_assoc, hE]
  field_simp
  ring

end Lam

end MTC
