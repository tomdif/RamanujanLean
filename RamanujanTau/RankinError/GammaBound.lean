/-
# Elementary bounds for `Γ` in vertical strips

* `norm_Gamma_le_Gamma_re`: `‖Γ(w)‖ ≤ Γ(Re w)` for `Re w > 0`;
* `norm_sin_le_exp`: `‖sin z‖ ≤ e^{|Im z|}`;
* `exists_norm_inv_Gamma_le`: for `A ≥ 1/2` there is `C` with
  `‖Γ(w)⁻¹‖ ≤ C e^{π |Im w|}` whenever `Re w ≥ −A` and `|Im w| ≥ 1`;
* `norm_Gamma_conj_add_le`, `norm_Gamma_add_ge`: `Γ(ū + p)` and `Γ(u + q)` against `Γ(u)`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Complex Real MeasureTheory Set Filter Topology

lemma norm_Gamma_le_Gamma_re {w : ℂ} (hw : 0 < w.re) : ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := by
  rw [Complex.Gamma_eq_integral hw, Real.Gamma_eq_integral hw, GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by rw [Complex.norm_exp]; simp
  have h2 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by rw [Complex.norm_exp]; simp
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
  have := norm_sub_le (Complex.exp (-z * I)) (Complex.exp (z * I))
  rw [h1, h2] at this
  have e1 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.2 (le_abs_self _)
  have e2 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.2 (neg_le_abs _)
  linarith

/-- `‖Γ(w)⁻¹‖ ≤ Γ(1 − Re w) e^{π|Im w|}/π` for `Re w ≤ 1/2`. -/
lemma norm_inv_Gamma_le_left {w : ℂ} (hw : w.re ≤ 1 / 2) :
    ‖(Complex.Gamma w)⁻¹‖ ≤ Real.Gamma (1 - w.re) * Real.exp (π * |w.im|) / π := by
  have h1w : 0 < (1 - w).re := by simp; linarith
  have hG1 := Complex.Gamma_ne_zero_of_re_pos h1w
  have hπ := Real.pi_pos
  by_cases hG : Complex.Gamma w = 0
  · rw [hG, inv_zero, norm_zero]; positivity
  have hrefl := Complex.Gamma_mul_Gamma_one_sub w
  have hsin : Complex.sin (π * w) ≠ 0 := by
    intro h; rw [h, div_zero] at hrefl; exact mul_ne_zero hG hG1 hrefl
  have hinv : (Complex.Gamma w)⁻¹ = Complex.Gamma (1 - w) * Complex.sin (π * w) / π := by
    have hπc : (π : ℂ) ≠ 0 := by exact_mod_cast hπ.ne'
    field_simp
    rw [mul_comm (Complex.Gamma w), hrefl] at *
    field_simp
  rw [hinv, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ]
  have hb1 : ‖Complex.Gamma (1 - w)‖ ≤ Real.Gamma (1 - w.re) := by
    have := norm_Gamma_le_Gamma_re h1w; simpa using this
  have hb2 : ‖Complex.sin (π * w)‖ ≤ Real.exp (π * |w.im|) := by
    have := norm_sin_le_exp (π * w)
    have e : |(↑π * w).im| = π * |w.im| := by
      simp [abs_mul, abs_of_pos hπ]
    rwa [e] at this
  apply div_le_div_of_nonneg_right _ hπ.le
  exact mul_le_mul hb1 hb2 (norm_nonneg _) (by
    have : 0 < 1 - w.re := by linarith
    exact (Real.Gamma_pos_of_pos this).le)

lemma exists_norm_inv_Gamma_le {A : ℝ} (hA : 1 / 2 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, -A ≤ w.re → 1 ≤ |w.im| →
      ‖(Complex.Gamma w)⁻¹‖ ≤ C * Real.exp (π * |w.im|) := by
  -- bound for `Γ` on `[1/2, 1 + A]`
  have hcont : ContinuousOn Real.Gamma (Icc (1 / 2 : ℝ) (1 + A)) := by
    intro u hu
    refine (Real.differentiableAt_Gamma (fun m => ?_)).continuousAt.continuousWithinAt
    intro h; have := hu.1; rw [h] at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith
  obtain ⟨G, hGb⟩ := (isCompact_Icc).exists_bound_of_continuousOn hcont
  have hπ := Real.pi_pos
  refine ⟨|G| / π, by positivity, ?_⟩
  -- the claim for `Re w ≤ 1/2 + n`, by induction on `n`
  have key : ∀ n : ℕ, ∀ w : ℂ, -A ≤ w.re → w.re ≤ 1 / 2 + n → 1 ≤ |w.im| →
      ‖(Complex.Gamma w)⁻¹‖ ≤ |G| / π * Real.exp (π * |w.im|) := by
    intro n
    induction n with
    | zero =>
      intro w h1 h2 _
      simp only [CharP.cast_eq_zero, add_zero] at h2
      refine (norm_inv_Gamma_le_left h2).trans ?_
      have hu : 1 - w.re ∈ Icc (1 / 2 : ℝ) (1 + A) := ⟨by linarith, by linarith⟩
      have := hGb _ hu
      rw [Real.norm_eq_abs] at this
      have hG0 : Real.Gamma (1 - w.re) ≤ |G| := (le_abs_self _).trans (this.trans (le_abs_self _))
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hπ.le
      exact mul_le_mul_of_nonneg_right hG0 (Real.exp_pos _).le
    | succ n ih =>
      intro w h1 h2 h3
      by_cases hn : w.re ≤ 1 / 2 + n
      · exact ih w h1 hn h3
      push Not at hn
      have hw1 : w - 1 ≠ 0 := by
        intro h; have := congrArg im h; simp at this; rw [this] at h3; norm_num at h3
      have hrec : Complex.Gamma w = (w - 1) * Complex.Gamma (w - 1) := by
        have := Complex.Gamma_add_one (w - 1) hw1
        rwa [sub_add_cancel] at this
      have hIH := ih (w - 1) (by simp; push_cast at hn; linarith) (by simp; push_cast at h2; linarith)
        (by simpa using h3)
      have hnorm : 1 ≤ ‖w - 1‖ := by
        have := Complex.abs_im_le_norm (w - 1); simp at this; linarith
      rw [hrec, mul_inv, norm_mul, norm_inv]
      have : ‖w - 1‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hnorm
      have h0 : 0 ≤ ‖(Complex.Gamma (w - 1))⁻¹‖ := norm_nonneg _
      simp only [sub_im, one_im, sub_zero] at hIH
      calc ‖w - 1‖⁻¹ * ‖(Complex.Gamma (w - 1))⁻¹‖ ≤ 1 * ‖(Complex.Gamma (w - 1))⁻¹‖ :=
            mul_le_mul_of_nonneg_right this h0
        _ ≤ _ := by rw [one_mul]; exact hIH
  intro w h1 h3
  obtain ⟨n, hn⟩ := exists_nat_ge w.re
  exact key n w h1 (by linarith) h3

/-- `Γ(u + p) = (∏_{j<p} (u + j)) Γ(u)` for `Re u > 0`. -/
lemma Gamma_add_nat {u : ℂ} (hu : 0 < u.re) (p : ℕ) :
    Complex.Gamma (u + p) = (∏ j ∈ Finset.range p, (u + j)) * Complex.Gamma u := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hne : u + p ≠ 0 := by
      intro h; have := congrArg re h; simp at this
      have : (0:ℝ) ≤ p := Nat.cast_nonneg p; linarith
    rw [Finset.prod_range_succ, show u + ((p + 1 : ℕ) : ℂ) = (u + p) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ hne, ih]
    ring

lemma norm_prod_le_pow {u : ℂ} (p : ℕ) :
    ‖∏ j ∈ Finset.range p, (u + j)‖ ≤ (‖u‖ + p) ^ p := by
  rw [norm_prod]
  have : (‖u‖ + p) ^ p = ∏ _j ∈ Finset.range p, (‖u‖ + p) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [this]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro j hj
  have hj' : (j : ℝ) ≤ p := by exact_mod_cast (Finset.mem_range.1 hj).le
  calc ‖u + j‖ ≤ ‖u‖ + ‖(j : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖u‖ + p := by rw [Complex.norm_natCast]; linarith

/-- `|Γ(ū)| = |Γ(u)|`. -/
lemma norm_Gamma_conj (u : ℂ) : ‖Complex.Gamma (starRingEnd ℂ u)‖ = ‖Complex.Gamma u‖ := by
  rw [Complex.Gamma_conj, Complex.norm_conj]

end RamanujanTau.RankinError
