/-
# The Poincaré unfolding: discharging `PoincareUnfolding`

For `f` a cusp form equal to `poincare` on `ℍ`, and `n ≥ 1`, `y = 1/n`:
1. `a_n(f) = ∫₀¹ e(-nw) P(w) du` (Mathlib `ModularFormClass.qExpansion_coeff_eq_intervalIntegral`);
2. `P(w) = e(w) + ∑_{(c,d)} T(c,d,w)`, absolutely and uniformly on `[0,1] + iy`, dominated by the
   weight-12 Eisenstein majorant (`EisensteinSeries.summand_bound_of_mem_verticalStrip`,
   `summable_one_div_norm_rpow`);
3. dominated convergence swaps `∫₀¹` and `∑_{(c,d)}`; `∫₀¹ e((1-n)w) du = [n=1]`;
4. each `c`-layer is `unfold_c`.
-/
import RamanujanTau.TauBound.UnfoldC
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

namespace RamanujanTau.TauBound

open Complex MeasureTheory ModularForm
open scoped Real MatrixGroups

lemma norm_ee_le_one {z : ℂ} (h : 0 ≤ z.im) : ‖ee z‖ ≤ 1 := by
  rw [norm_ee, Real.exp_le_one_iff]; nlinarith [Real.pi_pos]

lemma im_poincare_arg (c : ℕ) (hc : c ≠ 0) (d : ℤ) (a : ℝ) {w : ℂ} (hw : 0 < w.im) :
    0 ≤ ((a : ℂ) / c - 1 / ((c : ℂ) * ((c : ℂ) * w + d))).im := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc
  set v : ℂ := (c : ℂ) * ((c : ℂ) * w + d)
  have hv : v.im = (c : ℝ) ^ 2 * w.im := by simp [v]; ring
  have h1 : ((a : ℂ) / c).im = 0 := by
    rw [show ((a : ℂ) / c) = ((a / c : ℝ) : ℂ) by push_cast; rfl]; exact Complex.ofReal_im _
  rw [Complex.sub_im, h1, zero_sub, one_div, Complex.inv_im, neg_div, neg_neg]
  exact div_nonneg (by rw [hv]; positivity) (Complex.normSq_nonneg _)

lemma norm_poincareTerm_le (c : ℕ) (hc : c ≠ 0) (d : ℤ) {w : ℂ} (hw : 0 < w.im) :
    ‖poincareTerm c d w‖ ≤ ‖(c : ℂ) * w + d‖ ^ (-12 : ℝ) := by
  unfold poincareTerm
  split_ifs
  · rw [norm_mul, norm_zpow]
    have h := norm_ee_le_one (im_poincare_arg c hc d ((((d : ZMod c)⁻¹).val : ℝ)) hw)
    push_cast at h
    rw [show ‖(c : ℂ) * w + d‖ ^ (-12 : ℝ) = ‖(c : ℂ) * w + d‖ ^ (-12 : ℤ) by
      rw [← Real.rpow_intCast]; norm_num]
    calc ‖(c : ℂ) * w + d‖ ^ (-12 : ℤ) * _ ≤ ‖(c : ℂ) * w + d‖ ^ (-12 : ℤ) * 1 := by
          gcongr
      _ = _ := mul_one _
  · rw [norm_zero]; positivity

lemma continuous_coefIntegrand (n c : ℕ) (hc : c ≠ 0) {y : ℝ} (hy : 0 < y) (d : ℤ) :
    Continuous (fun u : ℝ => ee (-(n : ℂ) * ((u : ℂ) + y * I)) *
      poincareTerm c d ((u : ℂ) + y * I)) := by
  have hw : Continuous fun x : ℝ => (x : ℂ) + y * I := by fun_prop
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hne : ∀ x : ℝ, (c : ℂ) * ((x : ℂ) + y * I) + d ≠ 0 := by
    intro x h
    have := congrArg Complex.im h
    simp at this
    rcases this with h1 | h1
    · exact hc h1
    · linarith
  refine (continuous_ee.comp (continuous_const.mul hw)).mul ?_
  unfold poincareTerm
  split_ifs
  · refine Continuous.mul ?_ ?_
    · exact (continuous_const.mul hw |>.add continuous_const).zpow₀ _ (fun x => Or.inl (hne x))
    · refine continuous_ee.comp (continuous_const.sub (continuous_const.div
        (continuous_const.mul ((continuous_const.mul hw).add continuous_const)) fun x => ?_))
      exact mul_ne_zero hc' (hne x)
  · exact continuous_const

lemma inv_qParam_pow (n : ℕ) (z : ℂ) :
    1 / Function.Periodic.qParam 1 z ^ n = ee (-(n : ℂ) * z) := by
  rw [Function.Periodic.qParam, ee, ← Complex.exp_nat_mul, one_div, ← Complex.exp_neg]
  congr 1; push_cast; ring

lemma integral_ee_first (n : ℕ) (y : ℝ) :
    ∫ u in (0 : ℝ)..1, ee (-(n : ℂ) * ((u : ℂ) + y * I)) * ee ((u : ℂ) + y * I) =
      if n = 1 then 1 else 0 := by
  have hpt : ∀ u : ℝ, ee (-(n : ℂ) * ((u : ℂ) + y * I)) * ee ((u : ℂ) + y * I) =
      ee ((1 - n : ℂ) * (y * I)) * Complex.exp ((2 * π * I * (1 - n : ℂ)) * u) := by
    intro u; rw [← ee_add, ee, ee, ← Complex.exp_add]; congr 1; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]
  split_ifs with h
  · subst h; simp [ee]
  · have hne : (2 * π * I * (1 - n : ℂ)) ≠ 0 := by
      have : (1 - n : ℂ) ≠ 0 := by
        intro h0; apply h
        have : (n : ℂ) = 1 := by linear_combination -h0
        exact_mod_cast this
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
        I_ne_zero) this
    rw [integral_exp_mul_complex hne]
    have h1 : Complex.exp (2 * π * I * (1 - n : ℂ) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show 2 * π * I * (1 - n : ℂ) * ((1 : ℝ) : ℂ) = ((1 - n : ℤ) : ℂ) * (2 * π * I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [h1]; simp

/-- Eisenstein majorant on the segment `[0,1] + iy`. -/
lemma poincareTerm_bound {y : ℝ} (hy : 0 < y) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (c : ℕ) (d : ℤ) (u : ℝ), 0 ≤ u → u ≤ 1 →
      ‖poincareTerm (c + 1) d ((u : ℂ) + y * I)‖ ≤
        R * ‖(![((c + 1 : ℕ) : ℤ), d] : Fin 2 → ℤ)‖ ^ (-12 : ℝ) := by
  set z0 : UpperHalfPlane := ⟨⟨1, y⟩, hy⟩
  refine ⟨EisensteinSeries.r z0 ^ (-12 : ℝ),
    Real.rpow_nonneg (EisensteinSeries.r_pos z0).le _, fun c d u hu0 hu1 => ?_⟩
  have him : 0 < ((u : ℂ) + y * I).im := by simpa using hy
  set z : UpperHalfPlane := ⟨(u : ℂ) + y * I, him⟩
  have hz : z ∈ UpperHalfPlane.verticalStrip 1 y := by
    refine ⟨?_, ?_⟩
    · show |((u : ℂ) + y * I).re| ≤ 1
      simp [abs_of_nonneg hu0, hu1]
    · show y ≤ ((u : ℂ) + y * I).im
      simp
  have h := EisensteinSeries.summand_bound_of_mem_verticalStrip (z := z) (k := 12) (by norm_num)
    (![((c + 1 : ℕ) : ℤ), d] : Fin 2 → ℤ) hy hz
  refine (norm_poincareTerm_le (c + 1) (by omega) d him).trans (le_of_eq_of_le ?_ h)
  congr 2

lemma summable_majorant :
    Summable (fun p : ℕ × ℤ => ‖(![((p.1 + 1 : ℕ) : ℤ), p.2] : Fin 2 → ℤ)‖ ^ (-12 : ℝ)) := by
  have hinj : Function.Injective (fun p : ℕ × ℤ => (![((p.1 + 1 : ℕ) : ℤ), p.2] : Fin 2 → ℤ)) := by
    intro p q h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    exact Prod.ext (by omega) h1
  exact (EisensteinSeries.summable_one_div_norm_rpow (k := 12) (by norm_num)).comp_injective hinj

/-- **The Poincaré unfolding** (discharges `PoincareUnfolding`). -/
theorem poincareUnfolding : PoincareUnfolding := by
  intro f hf n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set y : ℝ := 1 / (n : ℝ) with hydef
  have hy : 0 < y := by positivity
  obtain ⟨R, hR0, hR⟩ := poincareTerm_bound hy
  set E : ℝ := Real.exp (2 * π * n * y)
  set M : ℕ × ℤ → ℝ := fun p => E * (R * ‖(![((p.1 + 1 : ℕ) : ℤ), p.2] : Fin 2 → ℤ)‖ ^ (-12 : ℝ))
  have hMsum : Summable M := (summable_majorant.mul_left R).mul_left E
  set w : ℝ → ℂ := fun u => (u : ℂ) + y * I
  set F : ℕ × ℤ → ℝ → ℂ := fun p u =>
    ee (-(n : ℂ) * ((u : ℂ) + y * I)) * poincareTerm (p.1 + 1) p.2 ((u : ℂ) + y * I)
  set second : ℝ → ℂ := fun u => ee (-(n : ℂ) * ((u : ℂ) + y * I)) *
    ∑' c : ℕ, ∑' d : ℤ, poincareTerm (c + 1) d ((u : ℂ) + y * I)
  have hEn : ∀ u : ℝ, ‖ee (-(n : ℂ) * ((u : ℂ) + y * I))‖ = E := by
    intro u; rw [norm_ee]; congr 1; simp; ring
  have hFb : ∀ p u, 0 ≤ u → u ≤ 1 → ‖F p u‖ ≤ M p := by
    intro p u h0 h1
    simp only [F, M, norm_mul, hEn]
    exact mul_le_mul_of_nonneg_left (hR p.1 p.2 u h0 h1) (Real.exp_pos _).le
  have hlim : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → HasSum (fun p => F p u) (second u) := by
    intro u h0 h1
    have hs : Summable (fun p : ℕ × ℤ => poincareTerm (p.1 + 1) p.2 ((u : ℂ) + y * I)) :=
      Summable.of_norm_bounded ((summable_majorant.mul_left R))
        (fun p => hR p.1 p.2 u h0 h1)
    have := hs.hasSum.mul_left (ee (-(n : ℂ) * ((u : ℂ) + y * I)))
    rw [hs.tsum_prod' (fun c => hs.prod_factor c)] at this
    exact this
  have hIoc : Set.uIoc (0 : ℝ) 1 = Set.Ioc 0 1 := Set.uIoc_of_le zero_le_one
  have hDCT : HasSum (fun p => ∫ u in (0 : ℝ)..1, F p u) (∫ u in (0 : ℝ)..1, second u) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun p _ => M p)
      (fun p => (continuous_coefIntegrand n (p.1 + 1) (by omega) hy p.2).aestronglyMeasurable)
      (fun p => Filter.Eventually.of_forall fun u hu => ?_)
      (Filter.Eventually.of_forall fun u _ => hMsum)
      intervalIntegrable_const
      (Filter.Eventually.of_forall fun u hu => ?_)
    · rw [hIoc] at hu; exact hFb p u hu.1.le hu.2
    · rw [hIoc] at hu; exact hlim u hu.1.le hu.2
  have hlayers := hDCT.prod_fiberwise (fun c => unfold_c n (c + 1) (by omega) hy)
  -- the coefficient integral
  have hcoef := ModularFormClass.qExpansion_coeff_eq_intervalIntegral f one_pos
    one_mem_strictPeriods_SL n hy
  set first : ℝ → ℂ := fun u => ee (-(n : ℂ) * ((u : ℂ) + y * I)) * ee ((u : ℂ) + y * I)
  have hfull : ∀ u : ℝ, 1 / Function.Periodic.qParam 1 ((u : ℂ) + y * I) ^ n *
      f ⟨(u : ℂ) + y * I, by simpa using hy⟩ = first u + second u := by
    intro u
    rw [inv_qParam_pow, hf]
    simp only [first, second, poincare]
    ring
  have hcontfull : Continuous (fun u : ℝ => 1 / Function.Periodic.qParam 1 ((u : ℂ) + y * I) ^ n *
      f ⟨(u : ℂ) + y * I, by simpa using hy⟩) := by
    simp_rw [inv_qParam_pow]
    refine (continuous_ee.comp (by fun_prop)).mul ?_
    exact (ModularFormClass.holo f).continuous.comp
      (Continuous.upperHalfPlaneMk (by fun_prop) (fun u => by simpa using hy))
  have hcontfirst : Continuous first :=
    (continuous_ee.comp (by fun_prop)).mul (continuous_ee.comp (by fun_prop))
  have hsecond_int : IntervalIntegrable second volume 0 1 := by
    have := (hcontfull.intervalIntegrable (μ := volume) 0 1).sub
      (hcontfirst.intervalIntegrable (μ := volume) 0 1)
    refine this.congr (fun u _ => ?_)
    show _ - first u = second u
    rw [hfull]; ring
  have hcoef' : (UpperHalfPlane.qExpansion 1 f).coeff n =
      (if n = 1 then 1 else 0) + ∫ u in (0 : ℝ)..1, second u := by
    rw [hcoef, Complex.ofReal_one, div_one, one_mul]
    simp_rw [hfull]
    rw [intervalIntegral.integral_add (hcontfirst.intervalIntegrable 0 1) hsecond_int]
    simp only [first]
    rw [integral_ee_first]
  rw [hcoef']
  convert hlayers using 1
  · ring

end RamanujanTau.TauBound
