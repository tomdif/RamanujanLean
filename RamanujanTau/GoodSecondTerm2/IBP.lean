/-
# Second-order first-derivative test for one off-diagonal pair

`Ptil Λ λ T H = ∫_{16}^T e^{iλt} W(t) dt + (1/H)∫_T^{T+H} (T+H−t) e^{iλt} W(t) dt`, `W = WV Λ`
(the `u`-average over `[T,T+H]` of `∫_{16}^u e^{iλt}W`). Two integrations by parts give

    ‖Ptil‖ ≤ W(16)/|λ| + (7 Φ + 3 W(T+H)/H)/λ²,     Φ = sup_{[16,T+H]} φ,

using that `φ = W'` is unimodal (`φ' = (2/t²)g(L)(L−1)`, `L` decreasing), so `∫|φ'| ≤ 2Φ`.
-/
import RamanujanTau.GoodSecondTerm2.Bounds

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm2

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm
open scoped Interval

/-- **First-derivative test** for a general real `C¹` weight. -/
theorem norm_integral_osc_gen {a b lam : ℝ} (hab : a ≤ b) (hlam : lam ≠ 0) {f f' : ℝ → ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t) (hf' : ContinuousOn f' (Icc a b)) :
    ‖∫ t in a..b, cexp (t * I * lam) * (f t : ℂ)‖ ≤ (|f a| + |f b| + ∫ t in a..b, |f' t|) / |lam| := by
  have hIl : I * (lam : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hlam)
  set v : ℝ → ℂ := fun t => cexp (t * I * lam) / (I * lam) with hv
  set v' : ℝ → ℂ := fun t => cexp (t * I * lam) with hv'
  have huu : ∀ x ∈ [[a, b]], HasDerivAt (fun t => (f t : ℂ)) ((f' x : ℝ) : ℂ) x := fun x hx =>
    (hf x (by rwa [uIcc_of_le hab] at hx)).ofReal_comp
  have hvv : ∀ x ∈ [[a, b]], HasDerivAt v (v' x) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * I * lam) (I * lam) x := by
      simpa using (((hasDerivAt_id x).ofReal_comp).mul_const I).mul_const (lam : ℂ)
    have h2 := (h1.cexp).div_const (I * lam)
    simp only [hv, hv']
    convert h2 using 1
    have : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
    field_simp
  have hcu : ContinuousOn (fun t => ((f' t : ℝ) : ℂ)) [[a, b]] := by
    rw [uIcc_of_le hab]; exact Complex.continuous_ofReal.comp_continuousOn hf'
  have hu'i : IntervalIntegrable (fun t => ((f' t : ℝ) : ℂ)) volume a b := hcu.intervalIntegrable
  have hv'i : IntervalIntegrable v' volume a b := (by fun_prop : Continuous v').intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul huu hvv hu'i hv'i
  have heq : (∫ t in a..b, cexp (t * I * lam) * (f t : ℂ)) = ∫ t in a..b, (f t : ℂ) * v' t := by
    congr 1; funext t; simp only [hv']; ring
  rw [heq, hibp]
  have hnv : ∀ t : ℝ, ‖v t‖ = 1 / |lam| := by
    intro t; simp only [hv]
    rw [norm_div, Complex.norm_exp, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    simp
  have hint : ‖∫ t in a..b, ((f' t : ℝ) : ℂ) * v t‖ ≤ (∫ t in a..b, |f' t|) / |lam| := by
    refine (intervalIntegral.norm_integral_le_integral_norm hab).trans (le_of_eq ?_)
    have hpt : ∀ t ∈ [[a, b]], ‖((f' t : ℝ) : ℂ) * v t‖ = |f' t| / |lam| := by
      intro t _
      rw [norm_mul, hnv, Complex.norm_real, Real.norm_eq_abs]; ring
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_div]
  have h1 : ‖(f b : ℂ) * v b‖ = |f b| / |lam| := by
    rw [norm_mul, hnv, Complex.norm_real, Real.norm_eq_abs]; ring
  have h2 : ‖(f a : ℂ) * v a‖ = |f a| / |lam| := by
    rw [norm_mul, hnv, Complex.norm_real, Real.norm_eq_abs]; ring
  calc ‖(f b : ℂ) * v b - (f a : ℂ) * v a - ∫ t in a..b, ((f' t : ℝ) : ℂ) * v t‖
      ≤ ‖(f b : ℂ) * v b‖ + ‖(f a : ℂ) * v a‖ + ‖∫ t in a..b, ((f' t : ℝ) : ℂ) * v t‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr; exact norm_sub_le _ _
    _ ≤ |f b| / |lam| + |f a| / |lam| + (∫ t in a..b, |f' t|) / |lam| := by
        rw [h1, h2]; gcongr
    _ = _ := by ring

/-- `φ'(t) = (2/t²) g(L)(L − 1)`. -/
noncomputable def dphiD (Λ t : ℝ) : ℝ := 2 / t ^ 2 * gk (Λ - 2 * ellT t) * ((Λ - 2 * ellT t) - 1)

lemma continuousOn_dphiD (Λ : ℝ) {a b : ℝ} (ha : 0 < a) : ContinuousOn (dphiD Λ) (Icc a b) := by
  have hE : ContinuousOn ellT (Icc a b) := continuousOn_ellT ha
  unfold dphiD
  refine ContinuousOn.mul (ContinuousOn.mul ?_ (continuous_gk.comp_continuousOn
    (continuousOn_const.sub (continuousOn_const.mul hE)))) ((continuousOn_const.sub
      (continuousOn_const.mul hE)).sub continuousOn_const)
  exact continuousOn_const.div (continuousOn_id.pow 2) (fun x hx => by
    have : 0 < x := ha.trans_le hx.1; positivity)

lemma continuousOn_phiD (Λ : ℝ) {a b : ℝ} (ha : 0 < a) : ContinuousOn (phiD Λ) (Icc a b) := fun t ht =>
  (hasDerivAt_phiD Λ (ha.trans_le ht.1)).continuousAt.continuousWithinAt

lemma integral_dphiD_eq {Λ a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, dphiD Λ t = phiD Λ b - phiD Λ a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => by
      rw [uIcc_of_le hab] at ht; exact hasDerivAt_phiD Λ (ha.trans_le ht.1))
    ((continuousOn_dphiD Λ ha).intervalIntegrable_of_Icc hab)

lemma dphiD_nonneg_iff {Λ t : ℝ} (ht : 0 < t) :
    0 ≤ dphiD Λ t ↔ t ≤ 2 * Real.pi * Real.exp ((Λ - 1) / 2) := by
  have hp : 0 < 2 / t ^ 2 * gk (Λ - 2 * ellT t) := by have := gk_pos (Λ - 2 * ellT t); positivity
  have hL : t ≤ 2 * Real.pi * Real.exp ((Λ - 1) / 2) ↔ 0 ≤ (Λ - 2 * ellT t) - 1 := by
    unfold ellT
    rw [← div_le_iff₀' (by positivity), ← Real.log_le_iff_le_exp (by positivity)]
    constructor <;> intro h <;> linarith
  rw [hL]
  unfold dphiD
  constructor
  · intro h; by_contra hneg; push_neg at hneg
    have := mul_neg_of_pos_of_neg hp hneg; linarith
  · intro h; exact mul_nonneg hp.le h

lemma dphiD_nonpos_of {Λ t : ℝ} (ht : 0 < t) (h : 2 * Real.pi * Real.exp ((Λ - 1) / 2) ≤ t) :
    dphiD Λ t ≤ 0 := by
  have hp : 0 < 2 / t ^ 2 * gk (Λ - 2 * ellT t) := by have := gk_pos (Λ - 2 * ellT t); positivity
  have hL : (Λ - 2 * ellT t) - 1 ≤ 0 := by
    unfold ellT
    have h1 : Real.exp ((Λ - 1) / 2) ≤ t / (2 * Real.pi) := by rw [le_div_iff₀' (by positivity)]; exact h
    have := (Real.le_log_iff_exp_le (by positivity)).mpr h1
    linarith
  unfold dphiD
  exact mul_nonpos_of_nonneg_of_nonpos hp.le hL

lemma int_abs_of_nonneg {Λ a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (h : ∀ t ∈ Icc a b, 0 ≤ dphiD Λ t) :
    ∫ t in a..b, |dphiD Λ t| = phiD Λ b - phiD Λ a := by
  rw [← integral_dphiD_eq ha hab]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hab] at ht
  exact abs_of_nonneg (h t ht)

lemma int_abs_of_nonpos {Λ a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (h : ∀ t ∈ Icc a b, dphiD Λ t ≤ 0) :
    ∫ t in a..b, |dphiD Λ t| = phiD Λ a - phiD Λ b := by
  have : ∫ t in a..b, |dphiD Λ t| = ∫ t in a..b, -dphiD Λ t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hab] at ht
    exact abs_of_nonpos (h t ht)
  rw [this, intervalIntegral.integral_neg, integral_dphiD_eq ha hab]; ring

/-- Unimodality: `∫_a^b |φ'| ≤ 2 sup φ`. -/
theorem integral_abs_dphiD_le {Λ a b Φ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hΦ : ∀ t ∈ Icc a b, phiD Λ t ≤ Φ) : ∫ t in a..b, |dphiD Λ t| ≤ 2 * Φ := by
  set ts : ℝ := 2 * Real.pi * Real.exp ((Λ - 1) / 2) with hts
  have hφ0 : ∀ t ∈ Icc a b, 0 ≤ phiD Λ t := fun t ht => phiD_nonneg Λ t (ha.trans_le ht.1)
  have hΦ0 : 0 ≤ Φ := (hφ0 a ⟨le_rfl, hab⟩).trans (hΦ a ⟨le_rfl, hab⟩)
  rcases le_or_gt ts a with h1 | h1
  · rw [int_abs_of_nonpos ha hab (fun t ht => dphiD_nonpos_of (ha.trans_le ht.1) (h1.trans ht.1))]
    have := hΦ a ⟨le_rfl, hab⟩; have := hφ0 b ⟨hab, le_rfl⟩; linarith
  rcases le_or_gt b ts with h2 | h2
  · rw [int_abs_of_nonneg ha hab (fun t ht => (dphiD_nonneg_iff (ha.trans_le ht.1)).mpr (ht.2.trans h2))]
    have := hΦ b ⟨hab, le_rfl⟩; have := hφ0 a ⟨le_rfl, hab⟩; linarith
  · have hts0 : 0 < ts := ha.trans h1
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := ts)
      (((continuousOn_dphiD Λ ha).mono (Icc_subset_Icc le_rfl h2.le)).abs.intervalIntegrable_of_Icc h1.le)
      (((continuousOn_dphiD Λ hts0).mono (Icc_subset_Icc le_rfl le_rfl)).abs.intervalIntegrable_of_Icc h2.le)]
    rw [int_abs_of_nonneg ha h1.le (fun t ht => (dphiD_nonneg_iff (ha.trans_le ht.1)).mpr ht.2),
      int_abs_of_nonpos hts0 h2.le (fun t ht => dphiD_nonpos_of (hts0.trans_le ht.1) ht.1)]
    have := hΦ ts ⟨h1.le, h2.le⟩; have := hφ0 a ⟨le_rfl, hab⟩; have := hφ0 b ⟨hab, le_rfl⟩
    linarith

end RamanujanTau.GoodSecondTerm2

namespace RamanujanTau.GoodSecondTerm2

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm
open scoped Interval

/-- Integration by parts against `e^{iλt}`, as an identity. -/
lemma ibp_osc {a b lam : ℝ} (hab : a ≤ b) (hlam : lam ≠ 0) {f f' : ℝ → ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t) (hf' : ContinuousOn f' (Icc a b)) :
    ∫ t in a..b, cexp (t * I * lam) * (f t : ℂ) =
      ((f b : ℂ) * cexp (b * I * lam) - (f a : ℂ) * cexp (a * I * lam)) / (I * lam) -
        (1 / (I * lam)) * ∫ t in a..b, cexp (t * I * lam) * ((f' t : ℝ) : ℂ) := by
  have hIl : I * (lam : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hlam)
  set v : ℝ → ℂ := fun t => cexp (t * I * lam) / (I * lam) with hv
  set v' : ℝ → ℂ := fun t => cexp (t * I * lam) with hv'
  have huu : ∀ x ∈ [[a, b]], HasDerivAt (fun t => (f t : ℂ)) ((f' x : ℝ) : ℂ) x := fun x hx =>
    (hf x (by rwa [uIcc_of_le hab] at hx)).ofReal_comp
  have hvv : ∀ x ∈ [[a, b]], HasDerivAt v (v' x) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * I * lam) (I * lam) x := by
      simpa using (((hasDerivAt_id x).ofReal_comp).mul_const I).mul_const (lam : ℂ)
    have h2 := (h1.cexp).div_const (I * lam)
    simp only [hv, hv']
    convert h2 using 1
    have : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
    field_simp
  have hcu : ContinuousOn (fun t => ((f' t : ℝ) : ℂ)) [[a, b]] := by
    rw [uIcc_of_le hab]; exact Complex.continuous_ofReal.comp_continuousOn hf'
  have hu'i : IntervalIntegrable (fun t => ((f' t : ℝ) : ℂ)) volume a b := hcu.intervalIntegrable
  have hv'i : IntervalIntegrable v' volume a b := (by fun_prop : Continuous v').intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul huu hvv hu'i hv'i
  have heq : (∫ t in a..b, cexp (t * I * lam) * (f t : ℂ)) = ∫ t in a..b, (f t : ℂ) * v' t := by
    congr 1; funext t; simp only [hv']; ring
  rw [heq, hibp]
  have h2 : (∫ t in a..b, ((f' t : ℝ) : ℂ) * v t) =
      (1 / (I * lam)) * ∫ t in a..b, cexp (t * I * lam) * ((f' t : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; simp only [hv]; field_simp
  rw [h2]; simp only [hv]; field_simp

/-- The `u`-averaged pair integral `Ptil = (1/H)∫_T^{T+H} ∫_{16}^u e^{iλt}W`. -/
noncomputable def Ptil (Λ lam T H : ℝ) : ℂ :=
  (∫ t in (16 : ℝ)..T, cexp (t * I * lam) * (WV Λ t : ℂ)) +
    (1 / (H : ℂ)) * ∫ t in T..T + H, cexp (t * I * lam) * (((T + H - t) * WV Λ t : ℝ) : ℂ)

lemma continuousOn_WV (Λ : ℝ) {a b : ℝ} (ha : 0 < a) : ContinuousOn (WV Λ) (Icc a b) := fun t ht =>
  (hasDerivAt_WV Λ (ha.trans_le ht.1)).continuousAt.continuousWithinAt

lemma WV_mono (Λ : ℝ) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : WV Λ s ≤ WV Λ t := by
  unfold WV; exact antitone_V (by linarith [ellT_mono hs hst])

lemma integral_phiD_eq {Λ a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, phiD Λ t = WV Λ b - WV Λ a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => by rw [uIcc_of_le hab] at ht; exact hasDerivAt_WV Λ (ha.trans_le ht.1))
    ((continuousOn_phiD Λ ha).intervalIntegrable_of_Icc hab)

/-- **Second-order bound for one pair.** -/
theorem norm_Ptil_le {Λ lam T H Φ : ℝ} (hT : 16 ≤ T) (hH : 0 < H) (hlam : lam ≠ 0)
    (hΦ : ∀ t ∈ Icc 16 (T + H), phiD Λ t ≤ Φ) :
    ‖Ptil Λ lam T H‖ ≤ WV Λ 16 / |lam| + (7 * Φ + 3 * WV Λ (T + H) / H) / lam ^ 2 := by
  have h16 : (0 : ℝ) < 16 := by norm_num
  have hT0 : 0 < T := by linarith
  have hTH : T ≤ T + H := by linarith
  have hIl : I * (lam : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hlam)
  have hlpos : 0 < |lam| := abs_pos.mpr hlam
  have hΦ0 : 0 ≤ Φ := (phiD_nonneg Λ 16 h16).trans (hΦ 16 ⟨le_rfl, by linarith⟩)
  -- piece 1
  have e1 := ibp_osc (a := 16) (b := T) hT hlam (f := WV Λ) (f' := phiD Λ)
    (fun t ht => hasDerivAt_WV Λ (h16.trans_le ht.1)) (continuousOn_phiD Λ h16)
  -- piece 2, weight k(t) = (T+H-t) W(t)
  set k : ℝ → ℝ := fun t => (T + H - t) * WV Λ t with hk
  set k' : ℝ → ℝ := fun t => -WV Λ t + (T + H - t) * phiD Λ t with hk'
  have hkd : ∀ t ∈ Icc T (T + H), HasDerivAt k (k' t) t := by
    intro t ht
    have := ((hasDerivAt_const t (T + H)).sub (hasDerivAt_id t)).mul (hasDerivAt_WV Λ (hT0.trans_le ht.1))
    convert this using 1; simp only [hk', Pi.sub_apply, id_eq]; ring
  have hkc : ContinuousOn k' (Icc T (T + H)) :=
    ((continuousOn_WV Λ hT0).neg).add ((continuousOn_const.sub continuousOn_id).mul (continuousOn_phiD Λ hT0))
  have e2 := ibp_osc (a := T) (b := T + H) hTH hlam (f := k) (f' := k') hkd hkc
  have hkT' : k (T + H) = 0 := by simp [hk]
  have hkT : k T = H * WV Λ T := by simp [hk]
  -- combine: Ptil = -W(16)e(16)/(iλ) - (1/iλ)[∫φ + (1/H)∫k']
  have hP : Ptil Λ lam T H = -((WV Λ 16 : ℂ) * cexp ((16:ℝ) * I * lam)) / (I * lam) -
      (1 / (I * lam)) * ((∫ t in (16:ℝ)..T, cexp (t * I * lam) * ((phiD Λ t : ℝ) : ℂ)) +
        (1 / (H : ℂ)) * ∫ t in T..T + H, cexp (t * I * lam) * ((k' t : ℝ) : ℂ)) := by
    unfold Ptil
    rw [show (fun t : ℝ => cexp (t * I * lam) * (((T + H - t) * WV Λ t : ℝ) : ℂ)) =
      fun t : ℝ => cexp (t * I * lam) * (k t : ℂ) from rfl, e1, e2, hkT', hkT]
    have hH0 : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
    push_cast
    field_simp
    ring
  rw [hP]
  -- estimates
  have b1 := norm_integral_osc_gen (a := 16) (b := T) hT hlam (f := phiD Λ) (f' := dphiD Λ)
    (fun t ht => hasDerivAt_phiD Λ (h16.trans_le ht.1)) (continuousOn_dphiD Λ h16)
  have hJ1 := integral_abs_dphiD_le (Λ := Λ) h16 hT (Φ := Φ) (fun t ht => hΦ t ⟨ht.1, ht.2.trans hTH⟩)
  have hφ16 := hΦ 16 ⟨le_rfl, by linarith⟩
  have hφT := hΦ T ⟨hT, hTH⟩
  have hφ16' := phiD_nonneg Λ 16 h16
  have hφT' := phiD_nonneg Λ T hT0
  rw [abs_of_nonneg hφ16', abs_of_nonneg hφT'] at b1
  -- the k' integral: split k' = -W + (T+H-t)φ
  have hsplit : (∫ t in T..T + H, cexp (t * I * lam) * ((k' t : ℝ) : ℂ)) =
      (∫ t in T..T + H, cexp (t * I * lam) * (((T + H - t) * phiD Λ t : ℝ) : ℂ)) -
        ∫ t in T..T + H, cexp (t * I * lam) * (WV Λ t : ℂ) := by
    rw [← intervalIntegral.integral_sub]
    · congr 1; funext t; simp only [hk']; push_cast; ring
    · exact (ContinuousOn.intervalIntegrable_of_Icc hTH (by
        refine ContinuousOn.mul (by fun_prop) ?_
        exact Complex.continuous_ofReal.comp_continuousOn
          ((continuousOn_const.sub continuousOn_id).mul (continuousOn_phiD Λ hT0))))
    · exact (ContinuousOn.intervalIntegrable_of_Icc hTH (by
        refine ContinuousOn.mul (by fun_prop) ?_
        exact Complex.continuous_ofReal.comp_continuousOn (continuousOn_WV Λ hT0)))
  -- bound for (T+H-t)φ
  set m : ℝ → ℝ := fun t => (T + H - t) * phiD Λ t with hm
  set m' : ℝ → ℝ := fun t => -phiD Λ t + (T + H - t) * dphiD Λ t with hm'
  have hmd : ∀ t ∈ Icc T (T + H), HasDerivAt m (m' t) t := by
    intro t ht
    have := ((hasDerivAt_const t (T + H)).sub (hasDerivAt_id t)).mul (hasDerivAt_phiD Λ (hT0.trans_le ht.1))
    convert this using 1; simp only [hm', Pi.sub_apply, id_eq]; unfold dphiD; ring
  have hmc : ContinuousOn m' (Icc T (T + H)) :=
    ((continuousOn_phiD Λ hT0).neg).add ((continuousOn_const.sub continuousOn_id).mul (continuousOn_dphiD Λ hT0))
  have b2 := norm_integral_osc_gen hTH hlam hmd hmc
  have hmT : |m T| ≤ H * Φ := by
    simp only [hm]; rw [abs_of_nonneg (by nlinarith)]; nlinarith
  have hmT' : |m (T + H)| = 0 := by simp [hm]
  have hJm : ∫ t in T..T + H, |m' t| ≤ (WV Λ (T + H) - WV Λ T) + H * (2 * Φ) := by
    have hle : ∀ t ∈ Icc T (T + H), |m' t| ≤ phiD Λ t + H * |dphiD Λ t| := by
      intro t ht
      simp only [hm']
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_of_nonneg (phiD_nonneg Λ t (hT0.trans_le ht.1)), abs_mul,
        abs_of_nonneg (by linarith [ht.2])]
      gcongr; linarith [ht.1]
    have hint1 : IntervalIntegrable (fun t => phiD Λ t + H * |dphiD Λ t|) volume T (T + H) :=
      ((continuousOn_phiD Λ hT0).add (continuousOn_const.mul (continuousOn_dphiD Λ hT0).abs)).intervalIntegrable_of_Icc hTH
    refine (intervalIntegral.integral_mono_on hTH (hmc.abs.intervalIntegrable_of_Icc hTH) hint1 hle).trans ?_
    rw [intervalIntegral.integral_add ((continuousOn_phiD Λ hT0).intervalIntegrable_of_Icc hTH)
      (((continuousOn_dphiD Λ hT0).abs.intervalIntegrable_of_Icc hTH).const_mul H),
      intervalIntegral.integral_const_mul, integral_phiD_eq hT0 hTH]
    have := integral_abs_dphiD_le (Λ := Λ) hT0 hTH (Φ := Φ) (fun t ht => hΦ t ⟨hT.trans ht.1, ht.2⟩)
    gcongr
  -- bound for ∫ e W
  have b3 := norm_integral_osc_gen hTH hlam (f := WV Λ) (f' := phiD Λ)
    (fun t ht => hasDerivAt_WV Λ (hT0.trans_le ht.1)) (continuousOn_phiD Λ hT0)
  have hWT := V_nonneg (Λ - 2 * ellT T)
  have hWT' := V_nonneg (Λ - 2 * ellT (T + H))
  have hW16 := V_nonneg (Λ - 2 * ellT 16)
  have hWmono := WV_mono Λ hT0 hTH
  have hJW : ∫ t in T..T + H, |phiD Λ t| = WV Λ (T + H) - WV Λ T := by
    rw [← integral_phiD_eq hT0 hTH]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hTH] at ht; exact abs_of_nonneg (phiD_nonneg Λ t (hT0.trans_le ht.1))
  rw [hJW] at b3
  simp only [WV] at hWmono b3 ⊢
  rw [abs_of_nonneg hWT, abs_of_nonneg hWT'] at b3
  -- assemble the norm estimate
  have hn1 : ‖-((V (Λ - 2 * ellT 16) : ℂ) * cexp ((16:ℝ) * I * lam)) / (I * lam)‖ = V (Λ - 2 * ellT 16) / |lam| := by
    rw [norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW16,
      Complex.norm_exp, norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs]
    simp
  have hn2 : ‖1 / (I * (lam : ℂ))‖ = 1 / |lam| := by
    rw [norm_div, norm_one, norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
  have hHn : ‖1 / (H : ℂ)‖ = 1 / H := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
  simp only [WV] at hsplit hJm
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  rw [hn1, norm_mul, hn2]
  have hA : ‖(∫ t in (16:ℝ)..T, cexp (t * I * lam) * ((phiD Λ t : ℝ) : ℂ)) +
      (1 / (H : ℂ)) * ((∫ t in T..T + H, cexp (t * I * lam) * (((T + H - t) * phiD Λ t : ℝ) : ℂ)) -
        ∫ t in T..T + H, cexp (t * I * lam) * (V (Λ - 2 * ellT t) : ℂ))‖ ≤
      4 * Φ / |lam| + (1 / H) * ((H * Φ + ((V (Λ - 2 * ellT (T + H)) - V (Λ - 2 * ellT T)) + H * (2 * Φ))) / |lam| +
        (V (Λ - 2 * ellT T) + V (Λ - 2 * ellT (T + H)) + (V (Λ - 2 * ellT (T + H)) - V (Λ - 2 * ellT T))) / |lam|) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hHn]
    gcongr
    · refine b1.trans ?_
      rw [div_le_div_iff_of_pos_right hlpos]; linarith
    · refine (norm_sub_le _ _).trans ?_
      gcongr
      · refine b2.trans ?_
        rw [div_le_div_iff_of_pos_right hlpos]
        rw [hmT']; linarith [hmT, hJm]
  set VT := V (Λ - 2 * ellT T)
  set V' := V (Λ - 2 * ellT (T + H))
  have key : 4 * Φ / |lam| + (1 / H) * ((H * Φ + ((V' - VT) + H * (2 * Φ))) / |lam| +
      (VT + V' + (V' - VT)) / |lam|) ≤ (7 * Φ + 3 * V' / H) / |lam| := by
    rw [← add_div, ← mul_div_assoc, ← add_div, div_le_div_iff_of_pos_right hlpos]
    have : (1 / H) * (H * Φ + (V' - VT + H * (2 * Φ)) + (VT + V' + (V' - VT))) =
        3 * Φ + (3 * V' - VT) / H := by field_simp; ring
    rw [this]
    have : (3 * V' - VT) / H ≤ 3 * V' / H := by gcongr; linarith
    linarith
  have hsq : lam ^ 2 = |lam| * |lam| := by rw [← sq_abs]; ring
  calc V (Λ - 2 * ellT 16) / |lam| + 1 / |lam| * ‖_‖
      ≤ V (Λ - 2 * ellT 16) / |lam| + 1 / |lam| * ((7 * Φ + 3 * V' / H) / |lam|) := by
        gcongr; exact hA.trans key
    _ = _ := by rw [hsq]; field_simp

end RamanujanTau.GoodSecondTerm2
