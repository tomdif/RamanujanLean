/-
# A priori bounds for `G_h` (part 2)
-/
import RamanujanTau.SCSProof.Gbounds

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open Complex
open scoped Real

lemma summable_shift_sq (σ : ℝ) (hs : Summable (fun n : ℕ => (tau n : ℝ) ^ 2 * Real.exp (-n * σ)))
    (h : ℕ) : Summable (fun n : ℕ => (tau (n + h) : ℝ) ^ 2 * Real.exp (-(n + h : ℕ) * σ)) :=
  (summable_nat_add_iff h).2 hs

/-- `Σ |a_n| e^{−nσ} ≤ (1 + e^{hσ})/2 · C₀ σ^{−12}`. -/
theorem abs_laplace_le : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (h : ℕ) (σ : ℝ), 0 < σ →
    Summable (fun n : ℕ => aabs h n * Real.exp (-n * σ)) ∧
      ∑' n : ℕ, aabs h n * Real.exp (-n * σ) ≤
        (1 + Real.exp (h * σ)) / 2 * (C₀ * σ ^ (-(12 : ℝ))) := by
  obtain ⟨C₀, hC₀, hT⟩ := tau_sq_laplace
  refine ⟨C₀, hC₀, fun h σ hσ => ?_⟩
  obtain ⟨hs, hle⟩ := hT σ hσ
  have hs2 := summable_shift_sq σ hs h
  have e2 : ∀ n : ℕ, (tau (n + h) : ℝ) ^ 2 * Real.exp (-n * σ) =
      Real.exp (h * σ) * ((tau (n + h) : ℝ) ^ 2 * Real.exp (-(n + h : ℕ) * σ)) := by
    intro n
    rw [mul_left_comm, ← Real.exp_add]; congr 2; push_cast; ring
  have hs2' : Summable (fun n : ℕ => (tau (n + h) : ℝ) ^ 2 * Real.exp (-n * σ)) := by
    simp_rw [e2]; exact hs2.mul_left _
  have hmaj : Summable (fun n : ℕ => ((tau n : ℝ) ^ 2 * Real.exp (-n * σ) +
      (tau (n + h) : ℝ) ^ 2 * Real.exp (-n * σ)) / 2) := (hs.add hs2').div_const 2
  have hpt : ∀ n : ℕ, aabs h n * Real.exp (-n * σ) ≤ ((tau n : ℝ) ^ 2 * Real.exp (-n * σ) +
      (tau (n + h) : ℝ) ^ 2 * Real.exp (-n * σ)) / 2 := by
    intro n
    have := aabs_le h n
    have he := Real.exp_pos (-n * σ)
    calc aabs h n * Real.exp (-n * σ) ≤ ((tau n : ℝ) ^ 2 + (tau (n + h) : ℝ) ^ 2) / 2 *
          Real.exp (-n * σ) := by gcongr
      _ = _ := by ring
  have hsum : Summable (fun n : ℕ => aabs h n * Real.exp (-n * σ)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (aabs_nonneg h n) (Real.exp_pos _).le) hpt hmaj
  refine ⟨hsum, ?_⟩
  have hshift : ∑' n : ℕ, (tau (n + h) : ℝ) ^ 2 * Real.exp (-(n + h : ℕ) * σ) ≤
      ∑' n : ℕ, (tau n : ℝ) ^ 2 * Real.exp (-n * σ) := by
    rw [← hs.sum_add_tsum_nat_add h]
    have : 0 ≤ ∑ i ∈ Finset.range h, (tau i : ℝ) ^ 2 * Real.exp (-i * σ) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    linarith
  calc ∑' n : ℕ, aabs h n * Real.exp (-n * σ)
      ≤ ∑' n : ℕ, ((tau n : ℝ) ^ 2 * Real.exp (-n * σ) +
          (tau (n + h) : ℝ) ^ 2 * Real.exp (-n * σ)) / 2 := hsum.tsum_le_tsum hpt hmaj
    _ = (∑' n : ℕ, (tau n : ℝ) ^ 2 * Real.exp (-n * σ) +
          Real.exp (h * σ) * ∑' n : ℕ, (tau (n + h) : ℝ) ^ 2 * Real.exp (-(n + h : ℕ) * σ)) / 2 := by
        rw [tsum_div_const, hs.tsum_add hs2']
        simp_rw [e2]; rw [tsum_mul_left]
    _ ≤ (C₀ * σ ^ (-(12 : ℝ)) + Real.exp (h * σ) * (C₀ * σ ^ (-(12 : ℝ)))) / 2 := by
        exact div_le_div_of_nonneg_right (add_le_add hle (mul_le_mul_of_nonneg_left
          (hshift.trans hle) (Real.exp_pos _).le)) (by norm_num)
    _ = _ := by ring

lemma norm_term (h n : ℕ) (W : ℂ) :
    ‖((tau n * tau (n + h) : ℤ) : ℂ) * cexp (-(n : ℂ) * W)‖ = aabs h n * Real.exp (-n * W.re) := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_intCast]
  have : (-(n : ℂ) * W).re = -n * W.re := by simp
  rw [this]
  rfl

lemma summable_Gh_term (h : ℕ) {W : ℂ} (hW : 0 < W.re)
    (hs : Summable (fun n : ℕ => aabs h n * Real.exp (-n * W.re))) :
    Summable (fun n : ℕ => ((tau n * tau (n + h) : ℤ) : ℂ) * cexp (-(n : ℂ) * W)) := by
  refine Summable.of_norm ?_
  simp_rw [norm_term]; exact hs

lemma norm_Gh_le (h : ℕ) (W : ℂ) (hs : Summable (fun n : ℕ => aabs h n * Real.exp (-n * W.re))) :
    ‖Gh h W‖ ≤ ∑' n : ℕ, aabs h n * Real.exp (-n * W.re) := by
  unfold Gh
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · simp_rw [norm_term]; exact hs
  · simp_rw [norm_term]

/-- `n e^{−nσ} ≤ (2/σ) e^{−nσ/2}`. -/
lemma n_exp_le (n : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    (n : ℝ) * Real.exp (-n * σ) ≤ 2 / σ * Real.exp (-n * (σ / 2)) := by
  have h1 : (n : ℝ) * (σ / 2) ≤ Real.exp (n * (σ / 2)) := by
    have := Real.add_one_le_exp (n * (σ / 2)); linarith
  have e : Real.exp (-n * σ) = Real.exp (-n * (σ / 2)) * Real.exp (-n * (σ / 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hx : Real.exp (-n * (σ / 2)) * Real.exp (n * (σ / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (-n * (σ / 2))
  calc (n : ℝ) * (Real.exp (-n * (σ / 2)) * Real.exp (-n * (σ / 2)))
      = 2 / σ * ((n * (σ / 2)) * Real.exp (-n * (σ / 2))) * Real.exp (-n * (σ / 2)) := by
        field_simp
    _ ≤ 2 / σ * (Real.exp (n * (σ / 2)) * Real.exp (-n * (σ / 2))) * Real.exp (-n * (σ / 2)) := by
        gcongr
    _ = 2 / σ * Real.exp (-n * (σ / 2)) := by rw [mul_comm (Real.exp _), hx]; ring

lemma n_laplace (h : ℕ) {σ : ℝ} (hσ : 0 < σ)
    (hs : Summable (fun n : ℕ => aabs h n * Real.exp (-n * (σ / 2)))) :
    Summable (fun n : ℕ => n * aabs h n * Real.exp (-n * σ)) ∧
      ∑' n : ℕ, n * aabs h n * Real.exp (-n * σ) ≤
        2 / σ * ∑' n : ℕ, aabs h n * Real.exp (-n * (σ / 2)) := by
  have hpt : ∀ n : ℕ, n * aabs h n * Real.exp (-n * σ) ≤
      2 / σ * (aabs h n * Real.exp (-n * (σ / 2))) := by
    intro n
    have := n_exp_le n hσ
    have ha := aabs_nonneg h n
    calc (n : ℝ) * aabs h n * Real.exp (-n * σ) = aabs h n * ((n : ℝ) * Real.exp (-n * σ)) := by
          ring
      _ ≤ aabs h n * (2 / σ * Real.exp (-n * (σ / 2))) := by gcongr
      _ = _ := by ring
  have hnn : ∀ n : ℕ, 0 ≤ n * aabs h n * Real.exp (-n * σ) := fun n =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (aabs_nonneg h n)) (Real.exp_pos _).le
  have hsum := Summable.of_nonneg_of_le hnn hpt (hs.mul_left _)
  refine ⟨hsum, ?_⟩
  rw [← tsum_mul_left]
  exact hsum.tsum_le_tsum hpt (hs.mul_left _)

/-- **Lipschitz bound.** -/
theorem norm_Gh_sub_le (h : ℕ) {σ : ℝ} (hσ : 0 < σ) {W W' : ℂ} (hW : σ ≤ W.re) (hW' : σ ≤ W'.re)
    (hs : Summable (fun n : ℕ => n * aabs h n * Real.exp (-n * σ)))
    (hs0 : Summable (fun n : ℕ => aabs h n * Real.exp (-n * σ))) :
    ‖Gh h W - Gh h W'‖ ≤ ‖W - W'‖ * ∑' n : ℕ, n * aabs h n * Real.exp (-n * σ) := by
  have hmono : ∀ {V : ℂ}, σ ≤ V.re → ∀ n : ℕ, aabs h n * Real.exp (-n * V.re) ≤
      aabs h n * Real.exp (-n * σ) := by
    intro V hV n
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (aabs_nonneg h n)
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hsW : Summable (fun n : ℕ => aabs h n * Real.exp (-n * W.re)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (aabs_nonneg h n) (Real.exp_pos _).le)
      (hmono hW) hs0
  have hsW' : Summable (fun n : ℕ => aabs h n * Real.exp (-n * W'.re)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (aabs_nonneg h n) (Real.exp_pos _).le)
      (hmono hW') hs0
  unfold Gh
  rw [← (summable_Gh_term h (hσ.trans_le hW) hsW).tsum_sub (summable_Gh_term h
    (hσ.trans_le hW') hsW')]
  have hterm : ∀ n : ℕ, ‖((tau n * tau (n + h) : ℤ) : ℂ) * cexp (-(n : ℂ) * W) -
      ((tau n * tau (n + h) : ℤ) : ℂ) * cexp (-(n : ℂ) * W')‖ ≤
      ‖W - W'‖ * (n * aabs h n * Real.exp (-n * σ)) := by
    intro n
    rw [← mul_sub, norm_mul, Complex.norm_intCast]
    have hconv : Convex ℝ {c : ℂ | σ ≤ c.re} := convex_halfSpace_re_ge σ
    have hd : ∀ x ∈ {c : ℂ | σ ≤ c.re}, DifferentiableAt ℂ (fun w : ℂ => cexp (-(n : ℂ) * w)) x :=
      fun x _ => by fun_prop
    have hb : ∀ x ∈ {c : ℂ | σ ≤ c.re}, ‖deriv (fun w : ℂ => cexp (-(n : ℂ) * w)) x‖ ≤
        n * Real.exp (-n * σ) := by
      intro x hx
      have hder : deriv (fun w : ℂ => cexp (-(n : ℂ) * w)) x = -(n : ℂ) * cexp (-(n : ℂ) * x) := by
        have := ((hasDerivAt_id x).const_mul (-(n : ℂ))).cexp
        simp only [mul_one, id] at this
        rw [this.deriv]; ring
      rw [hder, norm_mul, norm_neg, Complex.norm_natCast, Complex.norm_exp]
      gcongr
      simp only [Complex.mul_re, Complex.neg_re, Complex.natCast_re, Complex.neg_im,
        Complex.natCast_im, neg_zero, zero_mul, sub_zero]
      have : σ ≤ x.re := hx
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have := hconv.norm_image_sub_le_of_norm_deriv_le hd hb (show W' ∈ {c : ℂ | σ ≤ c.re} from hW')
      (show W ∈ {c : ℂ | σ ≤ c.re} from hW)
    unfold aabs
    calc |((tau n * tau (n + h) : ℤ) : ℝ)| * ‖cexp (-(n : ℂ) * W) - cexp (-(n : ℂ) * W')‖
        ≤ |((tau n * tau (n + h) : ℤ) : ℝ)| * (n * Real.exp (-n * σ) * ‖W - W'‖) := by
          gcongr
      _ = _ := by ring
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hs.mul_left _)
  · rw [← tsum_mul_left]
    exact (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hs.mul_left _)).tsum_le_tsum
      hterm (hs.mul_left _)

end RamanujanTau.SCSProof
