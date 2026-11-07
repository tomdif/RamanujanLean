/-
# Selberg's method, abstract form

For a real continuous `Z` and a continuous weight `w ≥ 0` put

    I(t) = ∫_t^{t+h} Z(u) w(u) du,     J(t) = ∫_t^{t+h} |Z(u)| w(u) du.

If `|I(t)| < J(t)` then `Z` has a zero in `[t, t+h]` (otherwise `Z` has one sign there and
`|I(t)| = J(t)`).  Selberg's argument: from

    (H1) ∫_T^{2T} J ≥ a T h,   (H2) ∫_T^{2T} J² ≤ B T h²,   (H3) ∫_T^{2T} I² ≤ (a²/16) T h²

the set `S = {t ∈ [T,2T] : |I(t)| < J(t)}` has measure `≥ 5a²T/(16B)`, hence `Z` has at least
`5a²T/(16Bh)` distinct zeros in `[T, 2T+h]`.  Cauchy–Schwarz is replaced by the pointwise
inequality `|x| ≤ (λx² + 1/λ)/2`.  All of this is level 1 (no hypotheses beyond the stated ones).
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.HafnerProportion

open MeasureTheory Set Filter

/-- `I(t) = ∫_t^{t+h} Z w`. -/
noncomputable def selI (Z w : ℝ → ℝ) (h t : ℝ) : ℝ := ∫ u in t..t + h, Z u * w u

/-- `J(t) = ∫_t^{t+h} |Z| w`. -/
noncomputable def selJ (Z w : ℝ → ℝ) (h t : ℝ) : ℝ := ∫ u in t..t + h, |Z u| * w u

lemma continuous_shortInt {f : ℝ → ℝ} (hf : Continuous f) (h : ℝ) :
    Continuous fun t => ∫ u in t..t + h, f u := by
  have hF : Continuous fun x => ∫ u in (0 : ℝ)..x, f u :=
    intervalIntegral.continuous_primitive (fun a b => hf.intervalIntegrable a b) 0
  have e : (fun t => ∫ u in t..t + h, f u) =
      fun t => (∫ u in (0 : ℝ)..t + h, f u) - ∫ u in (0 : ℝ)..t, f u := by
    funext t
    exact (intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)).symm
  rw [e]
  exact (hF.comp (continuous_id.add continuous_const)).sub hF

lemma continuous_selI {Z w : ℝ → ℝ} (hZ : Continuous Z) (hw : Continuous w) (h : ℝ) :
    Continuous (selI Z w h) := continuous_shortInt (hZ.mul hw) h

lemma continuous_selJ {Z w : ℝ → ℝ} (hZ : Continuous Z) (hw : Continuous w) (h : ℝ) :
    Continuous (selJ Z w h) := continuous_shortInt (hZ.abs.mul hw) h

lemma selJ_nonneg {Z w : ℝ → ℝ} (hw0 : ∀ t, 0 ≤ w t) {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    0 ≤ selJ Z w h t :=
  intervalIntegral.integral_nonneg (by linarith) fun u _ => mul_nonneg (abs_nonneg _) (hw0 u)

/-- A continuous function without zeros on `[a,b]` has one sign there. -/
lemma const_sign' {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (h0 : ∀ t ∈ Icc a b, f t ≠ 0) :
    (∀ t ∈ Icc a b, 0 < f t) ∨ (∀ t ∈ Icc a b, f t < 0) := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨x, hx, hfx⟩, ⟨y, hy, hfy⟩⟩ := hc
  have hivt := intermediate_value_uIcc (a := x) (b := y) hf.continuousOn
  have h0mem : (0 : ℝ) ∈ uIcc (f x) (f y) := by
    rw [mem_uIcc]; left; exact ⟨hfx, hfy⟩
  obtain ⟨z, hz, hfz⟩ := hivt h0mem
  exact h0 z (uIcc_subset_Icc hx hy hz) hfz

/-- **Sign detection.** `|I(t)| < J(t)` forces a zero of `Z` in `[t, t+h]`. -/
theorem exists_zero_of_abs_lt {Z w : ℝ → ℝ} (hZ : Continuous Z) (hw0 : ∀ t, 0 ≤ w t)
    {h t : ℝ} (hh : 0 ≤ h) (hlt : |selI Z w h t| < selJ Z w h t) :
    ∃ u ∈ Icc t (t + h), Z u = 0 := by
  by_contra hne
  push Not at hne
  have hJ0 := selJ_nonneg (Z := Z) hw0 hh t
  have hu : uIcc t (t + h) = Icc t (t + h) := uIcc_of_le (by linarith)
  rcases const_sign' hZ hne with hs | hs
  · have e : selI Z w h t = selJ Z w h t := by
      unfold selI selJ
      refine intervalIntegral.integral_congr fun u hu' => ?_
      rw [hu] at hu'
      simp only [abs_of_pos (hs u hu')]
    rw [e, abs_of_nonneg hJ0] at hlt
    exact lt_irrefl _ hlt
  · have e : selI Z w h t = -selJ Z w h t := by
      unfold selI selJ
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun u hu' => ?_
      rw [hu] at hu'
      simp only [abs_of_neg (hs u hu')]
      ring
    rw [e, abs_neg, abs_of_nonneg hJ0] at hlt
    exact lt_irrefl _ hlt

/-- `|x| ≤ (λx² + 1/λ)/2`. -/
lemma abs_le_amgm (x : ℝ) {l : ℝ} (hl : 0 < l) : |x| ≤ (l * x ^ 2 + 1 / l) / 2 := by
  have h1 : 0 ≤ (l * |x| - 1) ^ 2 := sq_nonneg _
  have h2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have h3 : l * (l * x ^ 2 + 1 / l) = l ^ 2 * x ^ 2 + 1 := by field_simp
  have h4 : l * (2 * |x|) ≤ l * (l * x ^ 2 + 1 / l) := by rw [h3]; nlinarith
  have := le_of_mul_le_mul_left h4 hl
  linarith

/-- integral of the AM–GM majorant over a measurable subset of a compact interval. -/
lemma integral_amgm_le {f : ℝ → ℝ} (hf : Continuous f) {s : Set ℝ} {A B : ℝ}
    (hsub : s ⊆ Icc A B) {l : ℝ} (hl : 0 < l) :
    ∫ t in s, |f t| ≤ (l * (∫ t in s, f t ^ 2) + volume.real s / l) / 2 := by
  have hi2 : IntegrableOn (fun t => f t ^ 2) s volume :=
    ((hf.pow 2).integrableOn_Icc (a := A) (b := B)).mono_set hsub
  have hi1 : IntegrableOn (fun t => |f t|) s volume :=
    (hf.abs.integrableOn_Icc (a := A) (b := B)).mono_set hsub
  have hfin : volume s ≠ ⊤ := ((measure_mono hsub).trans_lt measure_Icc_lt_top).ne
  have hic : IntegrableOn (fun _ : ℝ => 1 / l) s volume := integrableOn_const hfin
  have hmaj : IntegrableOn (fun t => (l * f t ^ 2 + 1 / l) / 2) s volume :=
    ((hi2.const_mul l).add hic).div_const 2
  have e1 : ∫ t in s, (l * f t ^ 2 + 1 / l) / 2 =
      (∫ t in s, (l * f t ^ 2 + 1 / l)) / 2 := integral_div _ _
  have e2 : ∫ t in s, (l * f t ^ 2 + 1 / l) =
      (∫ t in s, l * f t ^ 2) + ∫ t in s, (1 / l) := integral_add (hi2.const_mul l) hic
  have e3 : ∫ t in s, l * f t ^ 2 = l * ∫ t in s, f t ^ 2 := integral_const_mul _ _
  have e4 : ∫ t in s, (1 / l) = volume.real s * (1 / l) := by
    rw [setIntegral_const, smul_eq_mul]
  have hle : ∫ t in s, |f t| ≤ ∫ t in s, (l * f t ^ 2 + 1 / l) / 2 :=
    setIntegral_mono hi1 hmaj fun t => abs_le_amgm (f t) hl
  rw [e1, e2, e3, e4] at hle
  calc ∫ t in s, |f t| ≤ (l * (∫ t in s, f t ^ 2) + volume.real s * (1 / l)) / 2 := hle
    _ = (l * (∫ t in s, f t ^ 2) + volume.real s / l) / 2 := by ring

/-- **Selberg's measure bound.**  Under (H1)–(H3) the detecting set
`S = {t ∈ [T,2T] : |I(t)| < J(t)}` has measure `≥ 5a²T/(16B)`. -/
theorem selberg_measure {Z w : ℝ → ℝ} (hZ : Continuous Z) (hw : Continuous w)
    (hw0 : ∀ t, 0 ≤ w t) {T h a B : ℝ} (hT : 0 < T) (hh : 0 < h) (ha : 0 < a) (hB : 0 < B)
    (H1 : a * T * h ≤ ∫ t in Icc T (2 * T), selJ Z w h t)
    (H2 : ∫ t in Icc T (2 * T), selJ Z w h t ^ 2 ≤ B * T * h ^ 2)
    (H3 : ∫ t in Icc T (2 * T), selI Z w h t ^ 2 ≤ a ^ 2 / 16 * T * h ^ 2) :
    5 * a ^ 2 / (16 * B) * T ≤
      volume.real (Icc T (2 * T) ∩ {t | |selI Z w h t| < selJ Z w h t}) := by
  set I := selI Z w h with hIdef
  set J := selJ Z w h with hJdef
  have hIc : Continuous I := continuous_selI hZ hw h
  have hJc : Continuous J := continuous_selJ hZ hw h
  have hJ0 : ∀ t, 0 ≤ J t := selJ_nonneg hw0 hh.le
  set S' : Set ℝ := {t | |I t| < J t} with hS'
  have hS'm : MeasurableSet S' := (isOpen_lt hIc.abs hJc).measurableSet
  set V := volume.real (Icc T (2 * T) ∩ S') with hV
  have hJint : IntegrableOn J (Icc T (2 * T)) volume := hJc.integrableOn_Icc
  have hsplit := integral_inter_add_diff (μ := volume) hS'm hJint
  -- off `S'`, `J ≤ |I|`
  have hdiff : ∫ t in Icc T (2 * T) \ S', J t ≤ ∫ t in Icc T (2 * T), |I t| := by
    have h1 : ∫ t in Icc T (2 * T) \ S', J t ≤ ∫ t in Icc T (2 * T) \ S', |I t| := by
      refine setIntegral_mono_on (hJint.mono_set diff_subset)
        (hIc.abs.integrableOn_Icc.mono_set diff_subset) (measurableSet_Icc.diff hS'm) ?_
      intro t ht
      have : ¬ (|I t| < J t) := ht.2
      linarith [not_lt.mp this]
    refine h1.trans (setIntegral_mono_set hIc.abs.integrableOn_Icc
      (Eventually.of_forall fun t => abs_nonneg (I t)) (Eventually.of_forall diff_subset))
  -- `∫ |I|` via AM–GM with `λ = 4/(ah)`
  have hIabs := integral_amgm_le hIc (subset_refl (Icc T (2 * T)))
    (show 0 < 4 / (a * h) by positivity)
  rw [Real.volume_real_Icc_of_le (by linarith)] at hIabs
  -- on `S'`, AM–GM with `μ = a/(4Bh)`
  have hSabs := integral_amgm_le hJc (inter_subset_left (s := Icc T (2 * T)) (t := S'))
    (show 0 < a / (4 * B * h) by positivity)
  have hJS : ∫ t in Icc T (2 * T) ∩ S', |J t| = ∫ t in Icc T (2 * T) ∩ S', J t :=
    integral_congr_ae (Eventually.of_forall fun t => abs_of_nonneg (hJ0 t))
  rw [hJS] at hSabs
  have hJ2 : ∫ t in Icc T (2 * T) ∩ S', J t ^ 2 ≤ ∫ t in Icc T (2 * T), J t ^ 2 :=
    setIntegral_mono_set (hJc.pow 2).integrableOn_Icc
      (Eventually.of_forall fun t => sq_nonneg (J t)) (Eventually.of_forall inter_subset_left)
  have e1 : 4 / (a * h) * (a ^ 2 / 16 * T * h ^ 2) = a * T * h / 4 := by
    field_simp; ring
  have e2 : (2 * T - T) / (4 / (a * h)) = a * T * h / 4 := by field_simp; ring
  have e3 : a / (4 * B * h) * (B * T * h ^ 2) = a * T * h / 4 := by field_simp
  have e4 : V / (a / (4 * B * h)) = 4 * B * h * V / a := by field_simp
  have hA : 4 / (a * h) * ∫ t in Icc T (2 * T), I t ^ 2 ≤ a * T * h / 4 := by
    rw [← e1]; exact mul_le_mul_of_nonneg_left H3 (by positivity)
  have hB' : a / (4 * B * h) * ∫ t in Icc T (2 * T) ∩ S', J t ^ 2 ≤ a * T * h / 4 := by
    rw [← e3]; exact mul_le_mul_of_nonneg_left (hJ2.trans H2) (by positivity)
  rw [e2] at hIabs
  rw [← hV, e4] at hSabs
  have key : a * T * h ≤ a * T * h / 8 + 2 * B * h * V / a + a * T * h / 4 := by
    have : 4 * B * h * V / a / 2 = 2 * B * h * V / a := by ring
    linarith
  have k2 : 5 * a * T * h / 8 * a ≤ 2 * B * h * V / a * a := by
    have := mul_le_mul_of_nonneg_right (show 5 * a * T * h / 8 ≤ 2 * B * h * V / a by linarith)
      ha.le
    exact this
  rw [div_mul_cancel₀ _ ha.ne'] at k2
  have k3 : (5 * a ^ 2 * T) * h ≤ (16 * B * V) * h := by nlinarith
  have k4 := le_of_mul_le_mul_right k3 hh
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith

/-- **Counting.**  If every `t ∈ S ⊆ [T,2T]` sees a zero of `Z` in `[t,t+h]`, then `Z` has at least
`|S|/h` distinct zeros in `[T, 2T+h]`. -/
theorem zeros_of_measure {Z : ℝ → ℝ} {S : Set ℝ} {T h V : ℝ} (hh : 0 < h)
    (hSsub : S ⊆ Icc T (2 * T)) (hS : ∀ t ∈ S, ∃ u ∈ Icc t (t + h), Z u = 0)
    (hV : V ≤ volume.real S) :
    ∃ F : Finset ℝ, (∀ γ ∈ F, γ ∈ Icc T (2 * T + h) ∧ Z γ = 0) ∧ V / h ≤ F.card := by
  classical
  set Z₀ : Set ℝ := {γ | γ ∈ Icc T (2 * T + h) ∧ Z γ = 0} with hZ₀
  by_cases hfin : Z₀.Finite
  swap
  · obtain ⟨F, hF, hcard⟩ := Set.Infinite.exists_subset_card_eq hfin ⌈V / h⌉₊
    exact ⟨F, fun γ hγ => hF hγ, by rw [hcard]; exact Nat.le_ceil _⟩
  set F := hfin.toFinset with hFdef
  refine ⟨F, fun γ hγ => (hfin.mem_toFinset).mp hγ, ?_⟩
  set U : Set ℝ := ⋃ γ ∈ F, Icc (γ - h) γ with hU
  have hcover : S ⊆ U := by
    intro t ht
    obtain ⟨u, hu, hzu⟩ := hS t ht
    have htI := hSsub ht
    have hmem : u ∈ F := by
      rw [hFdef, hfin.mem_toFinset]
      exact ⟨⟨by linarith [hu.1, htI.1], by linarith [hu.2, htI.2]⟩, hzu⟩
    simp only [hU, mem_iUnion]
    exact ⟨u, hmem, by linarith [hu.2], hu.1⟩
  have hUsub : U ⊆ Icc (T - h) (2 * T + h) := by
    intro x hx
    simp only [hU, mem_iUnion] at hx
    obtain ⟨γ, hγ, hx⟩ := hx
    have := (hfin.mem_toFinset).mp hγ
    exact ⟨by linarith [this.1.1, hx.1], by linarith [this.1.2, hx.2]⟩
  have hUfin : volume U ≠ ⊤ := ((measure_mono hUsub).trans_lt measure_Icc_lt_top).ne
  have h1 : volume.real S ≤ volume.real U := measureReal_mono hcover hUfin
  have h2 : volume.real U ≤ F.card * h := by
    refine (measureReal_biUnion_finset_le F _).trans ?_
    rw [Finset.sum_congr rfl fun γ _ => Real.volume_real_Icc_of_le (by linarith)]
    rw [Finset.sum_congr rfl fun _ _ => (show _ - (_ - h) = h by ring),
      Finset.sum_const, nsmul_eq_mul]
  rw [div_le_iff₀ hh]
  linarith

/-- **Selberg's method, abstract form.**  (H1)–(H3) give `≥ 5a²T/(16Bh)` distinct zeros of `Z`
in `[T, 2T+h]`. -/
theorem selberg_zeros {Z w : ℝ → ℝ} (hZ : Continuous Z) (hw : Continuous w)
    (hw0 : ∀ t, 0 ≤ w t) {T h a B : ℝ} (hT : 0 < T) (hh : 0 < h) (ha : 0 < a) (hB : 0 < B)
    (H1 : a * T * h ≤ ∫ t in Icc T (2 * T), selJ Z w h t)
    (H2 : ∫ t in Icc T (2 * T), selJ Z w h t ^ 2 ≤ B * T * h ^ 2)
    (H3 : ∫ t in Icc T (2 * T), selI Z w h t ^ 2 ≤ a ^ 2 / 16 * T * h ^ 2) :
    ∃ F : Finset ℝ, (∀ γ ∈ F, γ ∈ Icc T (2 * T + h) ∧ Z γ = 0) ∧
      5 * a ^ 2 / (16 * B) * T / h ≤ F.card :=
  zeros_of_measure hh inter_subset_left
    (fun _ ht => exists_zero_of_abs_lt hZ hw0 hh.le ht.2)
    (selberg_measure hZ hw hw0 hT hh ha hB H1 H2 H3)

end RamanujanTau.HafnerProportion
