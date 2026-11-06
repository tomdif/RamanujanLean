/-
# Perron + contour shift for the Riesz mean of `Λ_R = vR` (the von Mangoldt function of `ζ(2s)R(s)`)

`−H'/H(s) = Σ vR(n) n^{−s} = −KK'/KK(s) + 1/(s−1)` (`TauPNTUncond.negLogDerivK_eq`).

* `pole_integral`: `∫ x^s P₁(s)/(s−1) dy` on `Re s = 2` equals `π x (1 − 1/x)²` (Mellin inversion of
  the Riesz kernel `P₂`, since `P₁(s)/(s−1) = P₂(s−1)/2`).
* `perron_shiftK`: `2π Σ vR(n)(1 − n/x)₊ = ∫ gK x (1+iy) dy + π x(1 − 1/x)²`, where
  `gK x s = x^s P₁(s)(−KK'/KK)(s)` is holomorphic on `Re s ≥ 1` (the pole has been removed).
* `contour_boundK`: the contour estimate of `TauPNTError.contour_bound`, verbatim, for `KK`.
-/
import RamanujanTau.SelbergDelange.LogDeriv
import RamanujanTau.TauPNTError.Smoothed

set_option autoImplicit false

namespace RamanujanTau.SelbergDelange

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.EdgeNonvanishing RamanujanTau.TauPNTUncond RamanujanTau.RankinError
open RamanujanTau.TauPNTError (log_two_le_log log_pos_two reg_of_one_le logsq_le norm_Pk1_le)

/-- The Perron integrand. -/
noncomputable def gK (x : ℝ) (s : ℂ) : ℂ := (x : ℂ) ^ s * Pk 1 s * negLogDerivK s

/-- The conclusion of `logDerivKK_bound`, as a predicate. -/
def RegK (c C₀ : ℝ) : Prop := ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) ≤ s.re →
  KK s ≠ 0 ∧ ‖negLogDerivK s‖ ≤ C₀ * Real.log (|s.im| + 2) ^ 2

theorem regK_exists : ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 400 ∧ ∃ C₀ : ℝ, 0 ≤ C₀ ∧ RegK c C₀ := by
  obtain ⟨c, hc, hc4, C, hC, h⟩ := logDerivKK_bound
  refine ⟨c, hc, hc4, C, hC, fun s hs => ⟨(h s hs).1, ?_⟩⟩
  rw [negLogDerivK, neg_div, norm_neg]; exact (h s hs).2

lemma differentiableAt_negLogDerivK {s : ℂ} (hs0 : 0 < s.re) (hs : KK s ≠ 0) :
    DifferentiableAt ℂ negLogDerivK s := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd := differentiableOn_KK.deriv hopen
  show DifferentiableAt ℂ (fun s => -deriv KK s / KK s) s
  exact (hd.differentiableAt (hopen.mem_nhds hs0)).neg.div
    (differentiableOn_KK.differentiableAt (hopen.mem_nhds hs0)) hs

variable {c C₀ : ℝ}

lemma norm_gK_le (hreg : RegK c C₀) (hC₀ : 0 ≤ C₀) {x : ℝ} (hx : 0 < x) {s : ℂ}
    (h1 : 1 - c / Real.log (|s.im| + 2) ≤ s.re) (h2 : 1 / 2 ≤ s.re) :
    ‖gK x s‖ ≤ x ^ s.re * (16 * C₀ * Real.log (|s.im| + 2) ^ 2 / (1 + |s.im|) ^ 2) := by
  unfold gK
  rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
  have hP := norm_Pk1_le h2
  have hN := (hreg s h1).2
  have hxs : 0 ≤ x ^ s.re := by positivity
  calc x ^ s.re * ‖Pk 1 s‖ * ‖negLogDerivK s‖
      ≤ x ^ s.re * (16 / (1 + |s.im|) ^ 2) * (C₀ * Real.log (|s.im| + 2) ^ 2) := by
        gcongr
    _ = _ := by ring

lemma norm_gK_rpow (hreg : RegK c C₀) (hC₀ : 0 ≤ C₀) {x : ℝ} (hx : 0 < x) {s : ℂ}
    (h1 : 1 - c / Real.log (|s.im| + 2) ≤ s.re) (h2 : 1 / 2 ≤ s.re) :
    ‖gK x s‖ ≤ x ^ s.re * (512 * C₀) * (1 + |s.im|) ^ (-(3 / 2 : ℝ)) := by
  refine (norm_gK_le hreg hC₀ hx h1 h2).trans ?_
  have hv : (0 : ℝ) < 1 + |s.im| := by positivity
  have hL := logsq_le s.im
  have e : (1 + |s.im|) ^ (1 / 2 : ℝ) / (1 + |s.im|) ^ 2 = (1 + |s.im|) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub hv]; norm_num
  have hxs : 0 ≤ x ^ s.re := by positivity
  calc x ^ s.re * (16 * C₀ * Real.log (|s.im| + 2) ^ 2 / (1 + |s.im|) ^ 2)
      ≤ x ^ s.re * (16 * C₀ * (32 * (1 + |s.im|) ^ (1 / 2 : ℝ)) / (1 + |s.im|) ^ 2) := by
        gcongr
    _ = x ^ s.re * (512 * C₀) * ((1 + |s.im|) ^ (1 / 2 : ℝ) / (1 + |s.im|) ^ 2) := by ring
    _ = _ := by rw [e]

lemma differentiableAt_gK (hreg : RegK c C₀) {x : ℝ} (hx : 0 < x) {s : ℂ}
    (h1 : 1 - c / Real.log (|s.im| + 2) ≤ s.re) (h2 : 0 < s.re) :
    DifferentiableAt ℂ (gK x) s := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have e1 : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) s :=
    differentiableAt_id.const_cpow (Or.inl hxC)
  have e2 : DifferentiableAt ℂ (Pk 1) s :=
    (differentiableOn_Pk 1).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds h2)
  exact (e1.mul e2).mul (differentiableAt_negLogDerivK h2 (hreg s h1).1)

/-- The strip bound on `1 ≤ Re s ≤ 2`. -/
lemma gK_strip (hreg : RegK c C₀) (hc : 0 ≤ c) (hC₀ : 0 ≤ C₀) {x : ℝ} (hx : 1 ≤ x) :
    ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → ‖gK x s‖ ≤ (x ^ (2 : ℝ) * (512 * C₀)) *
      (1 + |s.im|) ^ (-(3 / 2 : ℝ)) := by
  intro s h1 h2
  refine (norm_gK_rpow hreg hC₀ (by linarith) (reg_of_one_le hc h1) (by linarith)).trans ?_
  have : x ^ s.re ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx h2
  gcongr

lemma gK_diffOn (hreg : RegK c C₀) (hc : 0 ≤ c) {x : ℝ} (hx : 1 ≤ x) :
    DifferentiableOn ℂ (gK x) {s : ℂ | 1 ≤ s.re ∧ s.re ≤ 2} := fun s hs =>
  (differentiableAt_gK hreg (by linarith) (reg_of_one_le hc hs.1) (by linarith [hs.1])).differentiableWithinAt

lemma vR_zero' : (vR 0 : ℂ) = 0 := by
  rw [vR_of_not (by simp [IsPrimePow])]; simp

lemma summable_vR_two :
    Summable fun n : ℕ => ‖(vR n : ℂ)‖ * (n : ℝ) ^ (-(2 : ℝ)) := by
  have hs := LSeriesSummable_vR (s := 2) (by norm_num)
  refine hs.norm.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [vR_zero']
  · rw [if_neg hpos.ne', Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
    norm_num

lemma LSeries_vR_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (vR n : ℂ)) s = negLogDerivK s + 1 / (s - 1) := by
  rw [negLogDerivK_eq hs]; ring

lemma Pk_one_div {w : ℂ} (hw : 0 < w.re) : Pk 1 (w + 1) * (1 / w) = Pk 2 w / 2 := by
  have h0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  have h1 : w + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : w + 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2' : w + 1 + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  simp only [Pk, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num
  field_simp
  ring

/-- The pole part on the line `Re s = 2`. -/
noncomputable def poleF (x : ℝ) (y : ℝ) : ℂ :=
  (x : ℂ) ^ RankinError.ln 2 y * Pk 1 (RankinError.ln 2 y) * (1 / (RankinError.ln 2 y - 1))

lemma poleF_eq {x : ℝ} (hx : 0 < x) (y : ℝ) :
    poleF x y = ((x / 2 : ℝ) : ℂ) * ((x : ℂ) ^ ((1 : ℂ) + y * I) * Pk 2 ((1 : ℂ) + y * I)) := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  set w : ℂ := (1 : ℂ) + y * I with hw
  have hl : RankinError.ln 2 y = w + 1 := by simp only [RankinError.ln, hw]; push_cast; ring
  have hwre : 0 < w.re := by simp [hw]
  rw [poleF, hl, add_sub_cancel_right, cpow_add _ _ hxC, cpow_one, mul_assoc,
    Pk_one_div hwre]
  push_cast
  ring

lemma integrable_poleF {x : ℝ} (hx : 0 < x) : Integrable (poleF x) := by
  have hc : Continuous fun y : ℝ => (x : ℂ) ^ ((1 : ℂ) + y * I) * Pk 2 ((1 : ℂ) + y * I) := by
    have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    refine Continuous.mul ?_ (by simpa using continuous_Pk_line 2 one_pos)
    exact continuous_const.cpow (by fun_prop) (fun _ => Or.inl (by simpa using hx))
  have hi : Integrable fun y : ℝ => (x : ℂ) ^ ((1 : ℂ) + y * I) * Pk 2 ((1 : ℂ) + y * I) := by
    have hP : Integrable fun y : ℝ => Pk 2 ((1 : ℂ) + y * I) := by
      simpa using integrable_Pk_line (k := 2) (by norm_num) one_pos
    refine (hP.norm.const_mul x).mono'
      hc.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
    simp
  have := hi.const_mul ((x / 2 : ℝ) : ℂ)
  refine this.congr (Eventually.of_forall fun y => ?_)
  simp only
  rw [poleF_eq hx]

lemma pole_integral {x : ℝ} (hx : 1 ≤ x) :
    ∫ y : ℝ, poleF x y = ((Real.pi * x * (1 - 1 / x) ^ 2 : ℝ) : ℂ) := by
  have hx0 : 0 < x := by linarith
  have hinv := mellinInv_Pk (k := 2) (by norm_num) (σ := 1) one_pos (u := 1 / x) (by positivity)
  unfold mellinInv at hinv
  rw [Complex.real_smul] at hinv
  simp_rw [cpow_div_neg zero_le_one hx0] at hinv
  simp only [ofReal_one, one_cpow, one_mul, smul_eq_mul] at hinv
  rw [phi_of_le (by rw [div_le_one hx0]; exact hx)] at hinv
  simp_rw [poleF_eq hx0]
  rw [integral_const_mul]
  have h2π : (2 * Real.pi : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  set J := ∫ y : ℝ, (x : ℂ) ^ ((1 : ℂ) + y * I) * Pk 2 ((1 : ℂ) + y * I) with hJ
  have hI : J = (2 * Real.pi : ℂ) * (((1 - 1 / x) ^ 2 : ℝ) : ℂ) := by
    rw [← hinv]
    push_cast
    field_simp
  rw [hI]
  push_cast
  ring

/-- **Perron + shift to `Re s = 1`**, with the pole term. -/
theorem perron_shiftK (hreg : RegK c C₀) (hc : 0 ≤ c) (hC₀ : 0 ≤ C₀) {x : ℝ} (hx : 1 ≤ x) :
    (2 * Real.pi : ℂ) * ∑' n : ℕ, (vR n : ℂ) * (phi 1 (n / x) : ℂ) =
      (∫ y : ℝ, gK x (1 + y * I)) + ((Real.pi * x * (1 - 1 / x) ^ 2 : ℝ) : ℂ) := by
  have hx0 : 0 < x := by linarith
  have hper := MeanSquare.perron_c (fun n => (vR n : ℂ)) vR_zero' (k := 1) le_rfl (c := 2)
    two_pos hx0 summable_vR_two
  rw [hper]
  have hsplit : ∀ y : ℝ, (x : ℂ) ^ RankinError.ln 2 y * Pk 1 (RankinError.ln 2 y) *
      LSeries (fun n => (vR n : ℂ)) (RankinError.ln 2 y) =
      gK x (((2 : ℝ) : ℂ) + y * I) + poleF x y := by
    intro y
    rw [LSeries_vR_eq (by simp [RankinError.ln])]
    simp only [gK, poleF, RankinError.ln]; ring
  simp_rw [hsplit]
  have hint1 : Integrable fun y : ℝ => gK x (((2 : ℝ) : ℂ) + y * I) :=
    Stirling.integrable_line_of_strip_rpow (p := 3 / 2) (by norm_num) (a := 1) (b := 2)
      (gK_diffOn hreg hc hx).continuousOn (gK_strip hreg hc hC₀ hx) (σ := 2) (by norm_num) le_rfl
  rw [integral_add hint1 (integrable_poleF hx0), pole_integral hx]
  have hshift := Stirling.integral_line_eq_rpow (p := 3 / 2) (by norm_num) (a := 1) (b := 2)
    (by norm_num) (gK_diffOn hreg hc hx) (gK_strip hreg hc hC₀ hx)
  rw [hshift]
  simp only [ofReal_one]

lemma integrable_line_one (hreg : RegK c C₀) (hc : 0 ≤ c) (hC₀ : 0 ≤ C₀) {x : ℝ} (hx : 1 ≤ x) :
    Integrable fun y : ℝ => gK x (1 + y * I) := by
  have := Stirling.integrable_line_of_strip_rpow (p := 3 / 2) (by norm_num) (a := 1) (b := 2)
    (gK_diffOn hreg hc hx).continuousOn (gK_strip hreg hc hC₀ hx) (σ := 1) le_rfl (by norm_num)
  simpa using this

/-- **The contour estimate.** -/
theorem contour_boundK (hreg : RegK c C₀) (hc : 0 < c) (hc32 : c ≤ 1 / 32) (hC₀ : 0 ≤ C₀)
    {x : ℝ} (hx : 1 ≤ x) {T : ℝ} (hT : 0 < T) :
    ‖∫ y : ℝ, gK x (1 + y * I)‖ ≤
      x ^ (1 - c / Real.log (T + 2)) * (16 * C₀ * Real.log (T + 2) ^ 2) *
          (∫ y : ℝ, 1 / (1 + |y|) ^ 2) +
        2 * (x * (16 * C₀ * Real.log (T + 2) ^ 2 / (1 + T) ^ 2)) +
        x * (512 * C₀) * (1 + T) ^ (-(1 / 4 : ℝ)) * ∫ y : ℝ, (1 + |y|) ^ (-(5 / 4 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  set ℓ : ℝ := Real.log (T + 2) with hℓ
  have hℓ2 : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by linarith)
  have hl2 : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hℓ0 : 0 < ℓ := by linarith
  set σ₀ : ℝ := 1 - c / ℓ with hσ₀
  have hcℓ : c / ℓ ≤ 1 / 16 := by rw [div_le_iff₀ hℓ0]; nlinarith
  have hcℓ0 : 0 < c / ℓ := by positivity
  have hσ₀1 : σ₀ ≤ 1 := by linarith
  have hσ₀h : 15 / 16 ≤ σ₀ := by linarith
  -- region facts
  have hregT : ∀ s : ℂ, |s.im| ≤ T → σ₀ ≤ s.re → 1 - c / Real.log (|s.im| + 2) ≤ s.re := by
    intro s h1 h2
    have hl : Real.log (|s.im| + 2) ≤ ℓ := Real.log_le_log (by positivity) (by linarith)
    have : c / ℓ ≤ c / Real.log (|s.im| + 2) :=
      div_le_div_of_nonneg_left hc.le (log_pos_two _) hl
    linarith
  set f1 : ℝ → ℂ := fun y => gK x (1 + y * I) with hf1
  have hint := integrable_line_one hreg hc.le hC₀ hx
  set S : Set ℝ := Ioc (-T) T with hS
  have hsplit := integral_add_compl (μ := volume) measurableSet_Ioc hint (s := S)
  -- the tail
  set I₅ : ℝ := ∫ y : ℝ, (1 + |y|) ^ (-(5 / 4 : ℝ)) with hI₅
  have hI5int : Integrable fun y : ℝ => (1 + |y|) ^ (-(5 / 4 : ℝ)) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 5 / 4) (by norm_num)
    simpa [Real.norm_eq_abs] using this
  set B : ℝ → ℝ := fun y => x * (512 * C₀) * (1 + T) ^ (-(1 / 4 : ℝ)) *
    (1 + |y|) ^ (-(5 / 4 : ℝ)) with hB
  have hBint : Integrable B := hI5int.const_mul _
  have hB0 : ∀ y, 0 ≤ B y := fun y => by simp only [hB]; positivity
  have htail : ‖∫ y in Sᶜ, f1 y‖ ≤ x * (512 * C₀) * (1 + T) ^ (-(1 / 4 : ℝ)) * I₅ := by
    have h1 : ‖∫ y in Sᶜ, f1 y‖ ≤ ∫ y in Sᶜ, B y := by
      refine norm_integral_le_of_norm_le hBint.integrableOn ?_
      refine (ae_restrict_iff' measurableSet_Ioc.compl).mpr (ae_of_all _ fun y hy => ?_)
      have hyT : T ≤ |y| := by
        simp only [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hy
        rcases hy with hy | hy
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have hre : (1 + (y : ℂ) * I).re = 1 := by simp
      have him : (1 + (y : ℂ) * I).im = y := by simp
      have := norm_gK_rpow hreg hC₀ hx0 (s := 1 + y * I) (reg_of_one_le hc.le (by rw [hre]))
        (by rw [hre]; norm_num)
      rw [hre, him, Real.rpow_one] at this
      refine this.trans ?_
      simp only [hB]
      have hv : (0 : ℝ) < 1 + |y| := by positivity
      have e : (1 + |y|) ^ (-(3 / 2 : ℝ)) =
          (1 + |y|) ^ (-(1 / 4 : ℝ)) * (1 + |y|) ^ (-(5 / 4 : ℝ)) := by
        rw [← Real.rpow_add hv]; norm_num
      have h4 : (1 + |y|) ^ (-(1 / 4 : ℝ)) ≤ (1 + T) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
      rw [e]
      have : 0 ≤ x * (512 * C₀) := by positivity
      have : 0 ≤ (1 + |y|) ^ (-(5 / 4 : ℝ)) := by positivity
      calc x * (512 * C₀) * ((1 + |y|) ^ (-(1 / 4 : ℝ)) * (1 + |y|) ^ (-(5 / 4 : ℝ)))
          ≤ x * (512 * C₀) * ((1 + T) ^ (-(1 / 4 : ℝ)) * (1 + |y|) ^ (-(5 / 4 : ℝ))) := by
            gcongr
        _ = _ := by ring
    have h2 : ∫ y in Sᶜ, B y ≤ ∫ y, B y := setIntegral_le_integral hBint (ae_of_all _ hB0)
    have h3 : ∫ y, B y = x * (512 * C₀) * (1 + T) ^ (-(1 / 4 : ℝ)) * I₅ := by
      simp only [hB]; rw [integral_const_mul]
    linarith
  -- the rectangle
  have hdiff : DifferentiableOn ℂ (gK x)
      (Set.uIcc ((σ₀ : ℂ) - T * I).re ((1 : ℂ) + T * I).re ×ℂ
        Set.uIcc ((σ₀ : ℂ) - T * I).im ((1 : ℂ) + T * I).im) := by
    intro s hs
    simp only [mem_reProdIm, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
      mul_one, sub_zero, add_re, one_re, sub_im, mul_im, zero_add, zero_sub, add_im, one_im,
      add_zero] at hs
    rw [uIcc_of_le hσ₀1, uIcc_of_le (by linarith)] at hs
    have hsim : |s.im| ≤ T := abs_le.mpr ⟨hs.2.1, hs.2.2⟩
    exact (differentiableAt_gK hreg hx0 (hregT s hsim hs.1.1) (by linarith [hs.1.1])).differentiableWithinAt
  have hrect := integral_boundary_rect_eq_zero_of_differentiableOn (gK x) ((σ₀ : ℂ) - T * I)
    ((1 : ℂ) + T * I) hdiff
  have r1 : ((σ₀ : ℂ) - T * I).re = σ₀ := by simp
  have r2 : ((σ₀ : ℂ) - T * I).im = -T := by simp
  have r3 : ((1 : ℂ) + T * I).re = 1 := by simp
  have r4 : ((1 : ℂ) + T * I).im = T := by simp
  rw [r1, r2, r3, r4] at hrect
  set Bot := ∫ u : ℝ in σ₀..1, gK x (u + ((-T : ℝ) : ℂ) * I) with hBot
  set Top := ∫ u : ℝ in σ₀..1, gK x (u + (T : ℂ) * I) with hTop
  set VR := ∫ y : ℝ in (-T)..T, gK x ((1 : ℂ) + y * I) with hVR
  set VL := ∫ y : ℝ in (-T)..T, gK x ((σ₀ : ℂ) + y * I) with hVL
  have hVReq : I • VR = I • VL - Bot + Top := by
    linear_combination hrect
  have hVRn : ‖VR‖ ≤ ‖VL‖ + ‖Bot‖ + ‖Top‖ := by
    have e : ‖VR‖ = ‖I • VR‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    rw [e, hVReq]
    have := norm_sub_le (I • VL) Bot
    have h2 := norm_add_le (I • VL - Bot) Top
    rw [norm_smul, Complex.norm_I, one_mul] at this
    linarith
  -- bounds for the three sides
  have hVL : ‖VL‖ ≤ x ^ σ₀ * (16 * C₀ * ℓ ^ 2) * ∫ y : ℝ, 1 / (1 + |y|) ^ 2 := by
    set b : ℝ → ℝ := fun y => x ^ σ₀ * (16 * C₀ * ℓ ^ 2) * (1 / (1 + |y|) ^ 2) with hb
    have hbint : Integrable b := (MeanSquare.integrable_div_sq 1).const_mul _
    have h1 : ‖VL‖ ≤ ∫ y in (-T)..T, b y := by
      refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
        (ae_of_all _ fun y hy => ?_) hbint.intervalIntegrable
      have hre : ((σ₀ : ℂ) + y * I).re = σ₀ := by simp
      have him : ((σ₀ : ℂ) + y * I).im = y := by simp
      have hyT : |y| ≤ T := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
      have := norm_gK_le hreg hC₀ hx0 (s := (σ₀ : ℂ) + y * I)
        (hregT _ (by rw [him]; exact hyT) (by rw [hre])) (by rw [hre]; linarith)
      rw [hre, him] at this
      refine this.trans ?_
      simp only [hb]
      have hl : Real.log (|y| + 2) ≤ ℓ := Real.log_le_log (by positivity) (by linarith)
      have hl0 : 0 ≤ Real.log (|y| + 2) := (log_pos_two y).le
      have : Real.log (|y| + 2) ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ hl0 hl 2
      have : 0 ≤ x ^ σ₀ := by positivity
      calc x ^ σ₀ * (16 * C₀ * Real.log (|y| + 2) ^ 2 / (1 + |y|) ^ 2)
          ≤ x ^ σ₀ * (16 * C₀ * ℓ ^ 2 / (1 + |y|) ^ 2) := by gcongr
        _ = _ := by ring
    have h2 : ∫ y in (-T)..T, b y ≤ ∫ y, b y := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact setIntegral_le_integral hbint (ae_of_all _ fun y => by simp only [hb]; positivity)
    have h3 : ∫ y, b y = x ^ σ₀ * (16 * C₀ * ℓ ^ 2) * ∫ y : ℝ, 1 / (1 + |y|) ^ 2 := by
      simp only [hb]; rw [integral_const_mul]
    linarith
  have hside : ∀ v : ℝ, |v| = T → ‖∫ u : ℝ in σ₀..1, gK x (u + (v : ℂ) * I)‖ ≤
      x * (16 * C₀ * ℓ ^ 2 / (1 + T) ^ 2) := by
    intro v hv
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := σ₀) (b := 1)
      (C := x * (16 * C₀ * ℓ ^ 2 / (1 + T) ^ 2)) (f := fun u : ℝ => gK x (u + (v : ℂ) * I))
      (fun u hu => by
        rw [uIoc_of_le hσ₀1] at hu
        have hre : ((u : ℂ) + v * I).re = u := by simp
        have him : ((u : ℂ) + v * I).im = v := by simp
        have := norm_gK_le hreg hC₀ hx0 (s := (u : ℂ) + v * I)
          (hregT _ (by rw [him, hv]) (by rw [hre]; exact hu.1.le)) (by rw [hre]; linarith [hu.1])
        rw [hre, him, hv] at this
        refine this.trans ?_
        have : x ^ u ≤ x := by
          calc x ^ u ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hu.2
            _ = x := Real.rpow_one x
        gcongr)
    refine h.trans ?_
    have : |1 - σ₀| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have : 0 ≤ x * (16 * C₀ * ℓ ^ 2 / (1 + T) ^ 2) := by positivity
    nlinarith
  have hBotb := hside (-T) (by rw [abs_neg, abs_of_pos hT])
  have hTopb := hside T (abs_of_pos hT)
  -- assemble
  have hVRS : VR = ∫ y in S, f1 y := by
    rw [hVR, intervalIntegral.integral_of_le (by linarith)]
    first | done | simp [hf1, hS]
  rw [← hsplit]
  have h := norm_add_le (∫ y in S, f1 y) (∫ y in Sᶜ, f1 y)
  have h2 : ‖∫ y in S, f1 y‖ ≤ ‖VL‖ + ‖Bot‖ + ‖Top‖ := by rw [← hVRS]; exact hVRn
  exact h.trans (by linarith)

end RamanujanTau.SelbergDelange
