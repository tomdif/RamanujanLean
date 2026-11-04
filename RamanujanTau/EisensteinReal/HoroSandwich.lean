/-
# Sandwiching `G` between rectangle counts

* `exists_smul_mem_U`: every orbit meets `U = {−½ ≤ Re < ½, |w| ≥ 1}`.
* `smul_mem_S_unique`: if `γz, γ'z ∈ S = {−½ ≤ Re < ½, |w| > 1}` then `γ' = ±γ`.
* `two_le_tsum`: `∑_γ f(γz) ≥ 2 f(γ₀z)`; `tsum_le_two`: if `f` is supported in `S` then
  `∑_γ f(γz) ≤ 2 sup_S f`-type bound.
* `cellInd`, `cellHoro`: the count for a box `[α,β) × [a,b)`, with
  `cellHoro = horo(a) − horo(b)` and limit `K₀(β−α)(1/a − 1/b)`.
-/
import RamanujanTau.EisensteinReal.HoroLimit
import RamanujanTau.RankinSelberg.Upper

set_option autoImplicit false

namespace RamanujanTau.EisensteinReal.Horo

open Finset Real Filter Topology MeasureTheory ModularGroup Matrix
open RamanujanTau.RankinSelberg
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal

/-! ### Fundamental-domain facts -/

/-- Upper set: `−½ ≤ Re w < ½`, `|w|² ≥ 1`. -/
def Uset : Set ℍ := {w | -(1 / 2 : ℝ) ≤ w.re ∧ w.re < 1 / 2 ∧ 1 ≤ Complex.normSq (w : ℂ)}

/-- Lower set: `−½ ≤ Re w < ½`, `|w|² > 1`. -/
def Sset : Set ℍ := {w | -(1 / 2 : ℝ) ≤ w.re ∧ w.re < 1 / 2 ∧ 1 < Complex.normSq (w : ℂ)}

lemma exists_smul_mem_U (z : ℍ) : ∃ γ : SL(2, ℤ), γ • z ∈ Uset := by
  obtain ⟨g, hg⟩ := exists_smul_mem_fd z
  obtain ⟨h1, h2⟩ := hg
  rcases lt_or_eq_of_le (abs_le.1 h2).2 with hlt | heq
  · exact ⟨g, (abs_le.1 h2).1, hlt, h1⟩
  · refine ⟨T ^ (-1 : ℤ) * g, ?_, ?_, ?_⟩
    · rw [mul_smul, modular_T_zpow_smul, UpperHalfPlane.vadd_re, heq]; norm_num
    · rw [mul_smul, modular_T_zpow_smul, UpperHalfPlane.vadd_re, heq]; norm_num
    · rw [mul_smul, modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
      have hre : (g • z).re = 1 / 2 := heq
      rw [Complex.normSq_apply] at h1 ⊢
      simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero]
      have e1 : ((g • z : ℍ) : ℂ).re = 1 / 2 := hre
      rw [e1] at h1 ⊢
      push_cast
      nlinarith

/-- For `w ∈ S` and integers `c ≠ 0`, `d`: `|cw + d|² > 1`. -/
lemma normSq_gt_one {w : ℍ} (hw : w ∈ Sset) {c d : ℤ} (hc : c ≠ 0) :
    1 < Complex.normSq ((c : ℂ) * w + d) := by
  obtain ⟨h1, h2, h3⟩ := hw
  rw [Complex.normSq_apply] at h3 ⊢
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    Complex.add_im, Complex.mul_im, zero_mul, sub_zero, add_zero, zero_add]
  set x := (w : ℂ).re
  set y := (w : ℂ).im
  have hx : x = w.re := rfl
  have hy3 : 3 / 4 < y ^ 2 := by nlinarith
  have hc1 : 1 ≤ (c : ℝ) ^ 2 := by
    have : 1 ≤ c ^ 2 := by nlinarith [Int.one_le_abs hc, sq_abs c]
    exact_mod_cast this
  rcases lt_or_ge 1 ((c : ℝ) ^ 2) with hc2 | hc2
  · -- `|c| ≥ 2`
    have hc4 : 4 ≤ (c : ℝ) ^ 2 := by
      have : (1 : ℤ) < c ^ 2 := by exact_mod_cast hc2
      have : 4 ≤ c ^ 2 := by
        have habs : 2 ≤ |c| := by
          by_contra h
          push_neg at h
          have : |c| ≤ 1 := by omega
          nlinarith [sq_abs c, abs_nonneg c]
        nlinarith [sq_abs c]
      exact_mod_cast this
    nlinarith [sq_nonneg ((c : ℝ) * x + d)]
  · have hcc : (c : ℝ) ^ 2 = 1 := le_antisymm hc2 hc1
    have e : ((c : ℝ) * x + d) ^ 2 = (x + c * d) ^ 2 := by
      linear_combination (x ^ 2 - (d : ℝ) ^ 2) * hcc
    rcases eq_or_ne d 0 with hd | hd
    · subst hd; simp only [Int.cast_zero, add_zero]; nlinarith
    · have hm : 1 ≤ ((c : ℝ) * d) ^ 2 := by
        have : (1 : ℤ) ≤ (c * d) ^ 2 := by
          have : c * d ≠ 0 := mul_ne_zero hc hd
          nlinarith [Int.one_le_abs this, sq_abs (c * d)]
        exact_mod_cast this
      have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
      -- `(x + m)² ≥ 1/4` when `m² ≥ 1`, `|x| ≤ 1/2`
      have hxm : 1 / 4 ≤ (x + c * d) ^ 2 := by
        set m := (c : ℝ) * d
        rcases le_or_gt 1 m with hm1 | hm1
        · nlinarith
        · have : m ≤ -1 := by nlinarith
          nlinarith
      nlinarith

lemma im_smul_lt {w : ℍ} (hw : w ∈ Sset) {g : SL(2, ℤ)} (hc : g 1 0 ≠ 0) :
    (g • w).im < w.im := by
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
  have h := normSq_gt_one hw (d := g 1 1) hc
  have hw0 := w.im_pos
  rw [div_lt_iff₀ (by linarith)]
  push_cast at h ⊢
  nlinarith

/-- **Uniqueness on `S`.** If `γz ∈ S` and `γ'z ∈ S` then `γ' = γ` or `γ' = −γ`. -/
lemma smul_mem_S_unique {z : ℍ} {γ γ' : SL(2, ℤ)} (h : γ • z ∈ Sset) (h' : γ' • z ∈ Sset) :
    γ' = γ ∨ γ' = -γ := by
  set g := γ' * γ⁻¹ with hg
  set w := γ • z with hw
  have hgw : g • w = γ' • z := by rw [hw, hg, ← mul_smul, inv_mul_cancel_right]
  have hc : g 1 0 = 0 := by
    by_contra hc
    have h1 := im_smul_lt h hc
    have hc' : (g⁻¹) 1 0 ≠ 0 := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      simpa using hc
    have h2 := im_smul_lt (w := g • w) (by rw [hgw]; exact h') hc'
    rw [← mul_smul, inv_mul_cancel, one_smul] at h2
    rw [hgw] at h1 h2
    linarith
  -- `g = ±T^n`, and both points have real part in `[−½, ½)`, so `n = 0`
  have hd := g.det_coe
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hd
  have hre : (g • w).re = w.re + (g 0 1 : ℝ) * (g 1 1 : ℝ) := by
    rw [UpperHalfPlane.re, coe_specialLinearGroup_apply]
    simp only [algebraMap_int_eq, eq_intCast, hc, Int.cast_zero, Complex.ofReal_zero,
      zero_mul, zero_add]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hd with ⟨ha, hd'⟩ | ⟨ha, hd'⟩ <;>
      simp [ha, hd', Complex.div_re] <;> ring
  have hb : g 0 1 = 0 := by
    have h1' := h'.1
    have h2' := h'.2.1
    rw [← hgw, hre] at h1' h2'
    have h2 := h.2.1
    have hdd : (g 1 1 : ℝ) = 1 ∨ (g 1 1 : ℝ) = -1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hd with ⟨_, hd'⟩ | ⟨_, hd'⟩ <;> simp [hd']
    have h1 := h.1
    have hn : |(g 0 1 : ℝ)| < 1 := by
      rw [abs_lt]
      rcases hdd with hdd | hdd <;> rw [hdd] at h1' h2' <;> constructor <;> linarith
    have : |g 0 1| < 1 := by exact_mod_cast hn
    exact Int.abs_lt_one_iff.mp this
  have hgpm : g = 1 ∨ g = -1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hd with ⟨ha, hd'⟩ | ⟨ha, hd'⟩
    · left; ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hd', hb, hc]
    · right; ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hd', hb, hc]
  rcases hgpm with h1 | h1
  · left; rw [hg] at h1; exact mul_inv_eq_one.mp h1
  · right
    rw [hg, mul_inv_eq_iff_eq_mul] at h1
    rw [h1, neg_one_mul]

lemma neg_ne_self (γ : SL(2, ℤ)) : -γ ≠ γ := by
  intro h
  have := congrArg (fun g : SL(2, ℤ) => g 0 0) h
  have h2 := congrArg (fun g : SL(2, ℤ) => g 1 0) h
  have hd := γ.det_coe
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] at this h2
  rw [Matrix.det_fin_two] at hd
  have h0 : γ 0 0 = 0 := by omega
  have h1 : γ 1 0 = 0 := by omega
  rw [h0, h1] at hd
  simp at hd

/-- `∑_γ f(γz) ≥ 2 f(γ₀z)`. -/
lemma two_le_tsum (f : ℍ → ℝ≥0∞) (z : ℍ) (γ₀ : SL(2, ℤ)) :
    2 * f (γ₀ • z) ≤ ∑' γ : SL(2, ℤ), f (γ • z) := by
  have hs := ENNReal.sum_le_tsum (f := fun γ : SL(2, ℤ) => f (γ • z)) ({γ₀, -γ₀} : Finset _)
  rw [Finset.sum_pair (neg_ne_self γ₀).symm, SL_neg_smul, ← two_mul] at hs
  exact hs

/-- If `f` vanishes off `S` and `f ≤ g` on `S` with `g` invariant, then `∑_γ f(γz) ≤ 2 g(z)`. -/
lemma tsum_le_two (f : ℍ → ℝ≥0∞) (g : ℍ → ℝ≥0∞) (hg : ∀ (γ : SL(2, ℤ)) w, g (γ • w) = g w)
    (hf0 : ∀ w, w ∉ Sset → f w = 0) (hfg : ∀ w ∈ Sset, f w ≤ g w) (z : ℍ) :
    ∑' γ : SL(2, ℤ), f (γ • z) ≤ 2 * g z := by
  by_cases hex : ∃ γ₀ : SL(2, ℤ), γ₀ • z ∈ Sset
  · obtain ⟨γ₀, h₀⟩ := hex
    rw [tsum_eq_sum (s := ({γ₀, -γ₀} : Finset _))]
    · rw [Finset.sum_pair (neg_ne_self γ₀).symm, SL_neg_smul, ← two_mul]
      gcongr
      rw [← hg γ₀ z]
      exact hfg _ h₀
    · intro γ hγ
      apply hf0
      intro hmem
      rcases smul_mem_S_unique h₀ hmem with h | h <;> simp [h] at hγ
  · push_neg at hex
    rw [ENNReal.tsum_eq_zero.2 (fun γ => hf0 _ (hex γ))]
    simp

/-! ### Box counts -/

/-- The box `[α, β) × [a, b)`. -/
def box (α β a b : ℝ) : Set ℍ := {w | α ≤ w.re ∧ w.re < β ∧ a ≤ w.im ∧ w.im < b}

lemma measurableSet_box (α β a b : ℝ) : MeasurableSet (box α β a b) := by
  have hre : Measurable (fun w : ℍ => w.re) := UpperHalfPlane.continuous_re.measurable
  have him : Measurable (fun w : ℍ => w.im) := UpperHalfPlane.continuous_im.measurable
  exact (measurableSet_le measurable_const hre).inter
    ((measurableSet_lt hre measurable_const).inter
      ((measurableSet_le measurable_const him).inter (measurableSet_lt him measurable_const)))

noncomputable def boxInd (α β a b : ℝ) (w : ℍ) : ℝ≥0∞ := (box α β a b).indicator 1 w

lemma measurable_boxInd (α β a b : ℝ) : Measurable (boxInd α β a b) :=
  measurable_one.indicator (measurableSet_box α β a b)

lemma boxInd_add {α β a b : ℝ} (hab : a ≤ b) (w : ℍ) :
    boxInd α β a b w + ind α β b w = ind α β a w := by
  unfold boxInd ind
  simp only [Set.indicator, box, rect, Set.mem_setOf_eq, Pi.one_apply]
  by_cases h1 : α ≤ w.re <;> by_cases h2 : w.re < β <;> by_cases h3 : a ≤ w.im <;>
    by_cases h4 : w.im < b <;> simp [h1, h2, h3, h4] <;> first | linarith | rfl

lemma measurable_cnt_hp {y : ℝ} (hy : 0 < y) {f : ℍ → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x : ℝ => ∑' γ : SL(2, ℤ), f (γ • hp hy x) :=
  Measurable.ennreal_tsum fun γ => hf.comp (measurable_smul_hp hy γ).measurable

/-- Horocycle mean of the box count. -/
noncomputable def boxHoro (α β a b : ℝ) {y : ℝ} (hy : 0 < y) : ℝ≥0∞ :=
  ∫⁻ x in Set.Ioc (0 : ℝ) 1, ∑' γ : SL(2, ℤ), boxInd α β a b (γ • hp hy x)

lemma boxHoro_add {α β a b : ℝ} (hab : a ≤ b) {y : ℝ} (hy : 0 < y) :
    boxHoro α β a b hy + horo α β b hy = horo α β a hy := by
  unfold boxHoro horo cnt
  rw [← lintegral_add_left (measurable_cnt_hp hy (measurable_boxInd α β a b))]
  congr 1
  funext x
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun γ => boxInd_add hab _

/-- Real horocycle mean of a box count (`0` for `y ≤ 0`). -/
noncomputable def boxR (α β a b : ℝ) (y : ℝ) : ℝ :=
  if hy : 0 < y then (boxHoro α β a b hy).toReal else 0

/-- `K₀ = 4κW` (`= 6/π`). -/
noncomputable def K0 : ℝ := 4 * (kappa * Wc)

lemma boxHoro_ne_top {α β a b : ℝ} (hαβ : α ≤ β) (ha : 0 < a) (hab : a ≤ b) {y : ℝ}
    (hy : 0 < y) (hya : y < a) : boxHoro α β a b hy ≠ ⊤ := by
  have h := boxHoro_add (α := α) (β := β) hab hy
  have hne := horo_ne_top hαβ ha hy hya
  intro htop
  rw [htop, top_add] at h
  exact hne h.symm

lemma boxR_eq {α β a b : ℝ} (hαβ : α ≤ β) (ha : 0 < a) (hab : a ≤ b) {y : ℝ}
    (hy : 0 < y) (hya : y < a) : boxR α β a b y = horoR α β a y - horoR α β b y := by
  have h := boxHoro_add (α := α) (β := β) hab hy
  have hb := horo_ne_top hαβ (ha.trans_le hab) hy (hya.trans_le hab)
  have hbx := boxHoro_ne_top hαβ ha hab hy hya
  unfold boxR horoR
  rw [dif_pos hy, dif_pos hy, dif_pos hy, ← h, ENNReal.toReal_add hbx hb]
  ring

/-- **Horocycle limit for a box count.** -/
theorem tendsto_boxR {α β a b : ℝ} (hαβ : α ≤ β) (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (boxR α β a b) (𝓝[>] 0) (𝓝 (K0 * ((β - α) * (1 / a - 1 / b)))) := by
  have h := (tendsto_horoR hαβ ha).sub (tendsto_horoR hαβ (ha.trans_le hab))
  have e : 4 * (β - α) / a * (kappa * Wc) - 4 * (β - α) / b * (kappa * Wc) =
      K0 * ((β - α) * (1 / a - 1 / b)) := by unfold K0; ring
  rw [e] at h
  refine h.congr' ?_
  have : ∀ᶠ y in 𝓝[>] (0 : ℝ), y < a := nhdsWithin_le_nhds (Iio_mem_nhds ha)
  filter_upwards [self_mem_nhdsWithin, this] with y hy hya
  exact (boxR_eq hαβ ha hab hy hya).symm

end RamanujanTau.EisensteinReal.Horo

#print axioms RamanujanTau.EisensteinReal.Horo.smul_mem_S_unique
#print axioms RamanujanTau.EisensteinReal.Horo.tendsto_boxR
