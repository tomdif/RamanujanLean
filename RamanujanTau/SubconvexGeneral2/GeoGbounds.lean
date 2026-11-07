/-
# A priori bounds for `G^f_h` (weight-`k` copy of `SCSProof.Gbounds2` + `Point2.laplace_le_of`)

* `abs_laplace_leF`: `Σ |a_n| e^{−nσ} ≤ (1 + e^{hσ})/2 · C₀ σ^{−k}`;
* `norm_GhF_le`, `norm_GhF_sub_le` (Lipschitz), `n_laplaceF`;
* `laplace_le_ofF`: `T(s) ≤ 2 C₀ s^{−k}` once `hs ≤ 1`;
* `powk_sub_le`: `|u^k − v^k| ≤ k m^{k−1} |u − v|`.
-/
import RamanujanTau.SubconvexGeneral2.GeoQform

set_option autoImplicit false

namespace RamanujanTau.SubconvexGeneral2

open Complex
open RamanujanTau.SCSProof RamanujanTau.SubconvexGeneral RamanujanTau.HeckeConvexGeneral
open scoped MatrixGroups Real ComplexConjugate

variable {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ))

lemma aabsF_nonneg (h n : ℕ) : 0 ≤ aabsF f h n := norm_nonneg _

/-- `Σ |a_n| e^{−nσ} ≤ (1 + e^{hσ})/2 · C₀ σ^{−k}`. -/
theorem abs_laplace_leF : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (h : ℕ) (σ : ℝ), 0 < σ →
    Summable (fun n : ℕ => aabsF f h n * Real.exp (-n * σ)) ∧
      ∑' n : ℕ, aabsF f h n * Real.exp (-n * σ) ≤
        (1 + Real.exp (h * σ)) / 2 * (C₀ * σ ^ (-(k : ℝ))) := by
  obtain ⟨C₀, hC₀, hT⟩ := coef_sq_laplace f
  refine ⟨C₀, hC₀, fun h σ hσ => ?_⟩
  obtain ⟨hs, hle⟩ := hT σ hσ
  have hs2 : Summable (fun n : ℕ => ‖coef f (n + h)‖ ^ 2 * Real.exp (-(n + h : ℕ) * σ)) :=
    (summable_nat_add_iff h).2 hs
  have e2 : ∀ n : ℕ, ‖coef f (n + h)‖ ^ 2 * Real.exp (-n * σ) =
      Real.exp (h * σ) * (‖coef f (n + h)‖ ^ 2 * Real.exp (-(n + h : ℕ) * σ)) := by
    intro n
    rw [mul_left_comm, ← Real.exp_add]; congr 2; push_cast; ring
  have hs2' : Summable (fun n : ℕ => ‖coef f (n + h)‖ ^ 2 * Real.exp (-n * σ)) := by
    simp_rw [e2]; exact hs2.mul_left _
  have hmaj : Summable (fun n : ℕ => (‖coef f n‖ ^ 2 * Real.exp (-n * σ) +
      ‖coef f (n + h)‖ ^ 2 * Real.exp (-n * σ)) / 2) := (hs.add hs2').div_const 2
  have hpt : ∀ n : ℕ, aabsF f h n * Real.exp (-n * σ) ≤ (‖coef f n‖ ^ 2 * Real.exp (-n * σ) +
      ‖coef f (n + h)‖ ^ 2 * Real.exp (-n * σ)) / 2 := by
    intro n
    have := aabsF_le f h n
    have he := Real.exp_pos (-n * σ)
    calc aabsF f h n * Real.exp (-n * σ) ≤ (‖coef f n‖ ^ 2 + ‖coef f (n + h)‖ ^ 2) / 2 *
          Real.exp (-n * σ) := by gcongr
      _ = _ := by ring
  have hsum : Summable (fun n : ℕ => aabsF f h n * Real.exp (-n * σ)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (aabsF_nonneg f h n) (Real.exp_pos _).le)
      hpt hmaj
  refine ⟨hsum, ?_⟩
  have hshift : ∑' n : ℕ, ‖coef f (n + h)‖ ^ 2 * Real.exp (-(n + h : ℕ) * σ) ≤
      ∑' n : ℕ, ‖coef f n‖ ^ 2 * Real.exp (-n * σ) := by
    rw [← hs.sum_add_tsum_nat_add h]
    have : 0 ≤ ∑ i ∈ Finset.range h, ‖coef f i‖ ^ 2 * Real.exp (-i * σ) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    linarith
  calc ∑' n : ℕ, aabsF f h n * Real.exp (-n * σ)
      ≤ ∑' n : ℕ, (‖coef f n‖ ^ 2 * Real.exp (-n * σ) +
          ‖coef f (n + h)‖ ^ 2 * Real.exp (-n * σ)) / 2 := hsum.tsum_le_tsum hpt hmaj
    _ = (∑' n : ℕ, ‖coef f n‖ ^ 2 * Real.exp (-n * σ) +
          Real.exp (h * σ) * ∑' n : ℕ, ‖coef f (n + h)‖ ^ 2 * Real.exp (-(n + h : ℕ) * σ)) / 2 := by
        rw [tsum_div_const, hs.tsum_add hs2']
        simp_rw [e2]; rw [tsum_mul_left]
    _ ≤ (C₀ * σ ^ (-(k : ℝ)) + Real.exp (h * σ) * (C₀ * σ ^ (-(k : ℝ)))) / 2 := by
        exact div_le_div_of_nonneg_right (add_le_add hle (mul_le_mul_of_nonneg_left
          (hshift.trans hle) (Real.exp_pos _).le)) (by norm_num)
    _ = _ := by ring

lemma norm_termF (h n : ℕ) (W : ℂ) :
    ‖conj (coef f n) * coef f (n + h) * cexp (-(n : ℂ) * W)‖ =
      aabsF f h n * Real.exp (-n * W.re) := by
  rw [norm_mul, Complex.norm_exp]
  have : (-(n : ℂ) * W).re = -n * W.re := by simp
  rw [this]
  rfl

lemma summable_GhF_term (h : ℕ) {W : ℂ}
    (hs : Summable (fun n : ℕ => aabsF f h n * Real.exp (-n * W.re))) :
    Summable (fun n : ℕ => conj (coef f n) * coef f (n + h) * cexp (-(n : ℂ) * W)) := by
  refine Summable.of_norm ?_
  simp_rw [norm_termF]; exact hs

lemma norm_GhF_le (h : ℕ) (W : ℂ)
    (hs : Summable (fun n : ℕ => aabsF f h n * Real.exp (-n * W.re))) :
    ‖GhF f h W‖ ≤ ∑' n : ℕ, aabsF f h n * Real.exp (-n * W.re) := by
  unfold GhF
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · simp_rw [norm_termF]; exact hs
  · simp_rw [norm_termF]

lemma n_laplaceF (h : ℕ) {σ : ℝ} (hσ : 0 < σ)
    (hs : Summable (fun n : ℕ => aabsF f h n * Real.exp (-n * (σ / 2)))) :
    Summable (fun n : ℕ => n * aabsF f h n * Real.exp (-n * σ)) ∧
      ∑' n : ℕ, n * aabsF f h n * Real.exp (-n * σ) ≤
        2 / σ * ∑' n : ℕ, aabsF f h n * Real.exp (-n * (σ / 2)) := by
  have hpt : ∀ n : ℕ, n * aabsF f h n * Real.exp (-n * σ) ≤
      2 / σ * (aabsF f h n * Real.exp (-n * (σ / 2))) := by
    intro n
    have := n_exp_le n hσ
    have ha := aabsF_nonneg f h n
    calc (n : ℝ) * aabsF f h n * Real.exp (-n * σ) = aabsF f h n * ((n : ℝ) * Real.exp (-n * σ)) := by
          ring
      _ ≤ aabsF f h n * (2 / σ * Real.exp (-n * (σ / 2))) := by gcongr
      _ = _ := by ring
  have hnn : ∀ n : ℕ, 0 ≤ n * aabsF f h n * Real.exp (-n * σ) := fun n =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (aabsF_nonneg f h n)) (Real.exp_pos _).le
  have hsum := Summable.of_nonneg_of_le hnn hpt (hs.mul_left _)
  refine ⟨hsum, ?_⟩
  rw [← tsum_mul_left]
  exact hsum.tsum_le_tsum hpt (hs.mul_left _)

/-- **Lipschitz bound**, weight `k`. -/
theorem norm_GhF_sub_le (h : ℕ) {σ : ℝ} {W W' : ℂ} (hW : σ ≤ W.re) (hW' : σ ≤ W'.re)
    (hs : Summable (fun n : ℕ => n * aabsF f h n * Real.exp (-n * σ)))
    (hs0 : Summable (fun n : ℕ => aabsF f h n * Real.exp (-n * σ))) :
    ‖GhF f h W - GhF f h W'‖ ≤ ‖W - W'‖ * ∑' n : ℕ, n * aabsF f h n * Real.exp (-n * σ) := by
  have hmono : ∀ {V : ℂ}, σ ≤ V.re → ∀ n : ℕ, aabsF f h n * Real.exp (-n * V.re) ≤
      aabsF f h n * Real.exp (-n * σ) := by
    intro V hV n
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (aabsF_nonneg f h n)
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hsW : Summable (fun n : ℕ => aabsF f h n * Real.exp (-n * W.re)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (aabsF_nonneg f h n) (Real.exp_pos _).le)
      (hmono hW) hs0
  have hsW' : Summable (fun n : ℕ => aabsF f h n * Real.exp (-n * W'.re)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (aabsF_nonneg f h n) (Real.exp_pos _).le)
      (hmono hW') hs0
  unfold GhF
  rw [← (summable_GhF_term f h hsW).tsum_sub (summable_GhF_term f h hsW')]
  have hterm : ∀ n : ℕ, ‖conj (coef f n) * coef f (n + h) * cexp (-(n : ℂ) * W) -
      conj (coef f n) * coef f (n + h) * cexp (-(n : ℂ) * W')‖ ≤
      ‖W - W'‖ * (n * aabsF f h n * Real.exp (-n * σ)) := by
    intro n
    rw [← mul_sub, norm_mul]
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
    show aabsF f h n * _ ≤ _
    calc aabsF f h n * ‖cexp (-(n : ℂ) * W) - cexp (-(n : ℂ) * W')‖
        ≤ aabsF f h n * (n * Real.exp (-n * σ) * ‖W - W'‖) := by
          gcongr; exact aabsF_nonneg f h n
      _ = _ := by ring
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hs.mul_left _)
  · rw [← tsum_mul_left]
    exact (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hs.mul_left _)).tsum_le_tsum
      hterm (hs.mul_left _)

/-- `T(s) ≤ 2 C₀ s^{−k}` once `h s ≤ 1`. -/
lemma laplace_le_ofF {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (h : ℕ) {s : ℝ} (hs : 0 < s) (hhs : h * s ≤ 1)
    (hb : ∑' n : ℕ, aabsF f h n * Real.exp (-n * s) ≤
      (1 + Real.exp (h * s)) / 2 * (C₀ * s ^ (-(k : ℝ)))) :
    ∑' n : ℕ, aabsF f h n * Real.exp (-n * s) ≤ 2 * C₀ * (1 / s ^ k) := by
  refine hb.trans ?_
  have he : Real.exp (h * s) ≤ 3 := by
    calc Real.exp (h * s) ≤ Real.exp 1 := Real.exp_le_exp.2 hhs
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hr : s ^ (-(k : ℝ)) = 1 / s ^ k := by
    rw [Real.rpow_neg hs.le, Real.rpow_natCast, one_div]
  rw [hr]
  have : 0 ≤ C₀ * (1 / s ^ k) := by positivity
  nlinarith

lemma powk_sub_le (j : ℕ) (u v : ℂ) {m : ℝ} (hu : ‖u‖ ≤ m) (hv : ‖v‖ ≤ m) :
    ‖u ^ j - v ^ j‖ ≤ j * m ^ (j - 1) * ‖u - v‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  gcongr
  refine (norm_sum_le _ _).trans ?_
  have hm : 0 ≤ m := (norm_nonneg _).trans hu
  calc ∑ i ∈ Finset.range j, ‖u ^ i * v ^ (j - 1 - i)‖ ≤ ∑ i ∈ Finset.range j, m ^ (j - 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i < j := Finset.mem_range.1 hi
        rw [norm_mul, norm_pow, norm_pow]
        calc ‖u‖ ^ i * ‖v‖ ^ (j - 1 - i) ≤ m ^ i * m ^ (j - 1 - i) := by gcongr
          _ = m ^ (j - 1) := by rw [← pow_add]; congr 1; omega
    _ = j * m ^ (j - 1) := by simp

end RamanujanTau.SubconvexGeneral2
