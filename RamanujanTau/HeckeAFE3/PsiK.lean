/-
# Higher derivatives of the digamma function on the right half-plane

* `analyticOnNhd_digamma`: `ψ` is analytic on the slit plane;
* `disc_far`: for `Re z ≥ 5`, every `q` with `‖q − z‖ ≤ ‖z‖/4` and every real `r ≥ 0` has
  `‖q + r‖ ≥ ‖z‖/2` (the disc stays away from `(−∞, 0]`);
* `norm_digamma_sub_le_disc`: `‖ψ(w) − ψ(z)‖ ≤ 18` on that disc (shift `w ↦ w + N`, `N ≈ ‖z‖/4`,
  then `ψ = log + O(1)` on `Re ≥ 6`);
* **`norm_iteratedDeriv_digamma_le`**: `‖ψ^{(k)}(z)‖ ≤ 18 k! 4^k / ‖z‖^k` (`k ≥ 1`, `Re z ≥ 5`),
  by Cauchy's estimate on the disc of radius `‖z‖/4`;
* **`norm_iteratedDeriv_digamma_diff_le`**: on the critical line,
  `‖ψ^{(k)}(6+it+u) − ψ^{(k)}(6+it)‖ ≤ D_k (1+|y|)^{k+2} / (1+|t|)^{k+1}` (`u = x+iy`, `x ≥ −1`).
-/
import RamanujanTau.HeckeAFE2.Main

set_option autoImplicit false

namespace RamanujanTau.HeckeAFE3

open Complex Set Metric Filter Topology RamanujanTau.HeckeAFE RamanujanTau.HeckeAFE2
open scoped Real

lemma ne_neg_nat_of_slit {w : ℂ} (hw : w ∈ slitPlane) (m : ℕ) : w ≠ -m := by
  rintro rfl
  rw [mem_slitPlane_iff] at hw
  simp at hw
  linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]

lemma differentiableOn_Gamma_slit : DifferentiableOn ℂ Gamma slitPlane := fun w hw =>
  (differentiableAt_Gamma w (ne_neg_nat_of_slit hw)).differentiableWithinAt

lemma analyticOnNhd_Gamma_slit : AnalyticOnNhd ℂ Gamma slitPlane :=
  differentiableOn_Gamma_slit.analyticOnNhd isOpen_slitPlane

lemma Gamma_ne_zero_slit {w : ℂ} (hw : w ∈ slitPlane) : Gamma w ≠ 0 :=
  Gamma_ne_zero (ne_neg_nat_of_slit hw)

theorem analyticOnNhd_digamma : AnalyticOnNhd ℂ digamma slitPlane := by
  have h : digamma = fun w => deriv Gamma w / Gamma w := by
    funext w; rw [digamma_def, logDeriv_apply]
  rw [h]
  exact (analyticOnNhd_Gamma_slit.deriv).div analyticOnNhd_Gamma_slit
    (fun w hw => Gamma_ne_zero_slit hw)

lemma analyticOnNhd_iteratedDeriv_digamma (k : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv k digamma) slitPlane := by
  rw [iteratedDeriv_eq_iterate]; exact analyticOnNhd_digamma.iterated_deriv k

/-! ## The disc `‖w − z‖ ≤ ‖z‖/4` -/

theorem disc_far {z q : ℂ} (hz : 5 ≤ z.re) (hq : ‖q - z‖ ≤ ‖z‖ / 4) {r : ℝ} (hr : 0 ≤ r) :
    ‖z‖ / 2 ≤ ‖q + r‖ := by
  have hzn : 0 ≤ ‖z‖ := norm_nonneg z
  have hq1 : 3 * ‖z‖ / 4 ≤ ‖q‖ := by
    have := norm_sub_norm_le z q
    rw [norm_sub_rev] at hq
    linarith
  have hre : z.re - ‖z‖ / 4 ≤ q.re := by
    have := Complex.abs_re_le_norm (q - z)
    rw [sub_re] at this
    have := neg_abs_le (q.re - z.re)
    linarith
  have hzre : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have hsq : ‖q‖ ^ 2 = q.re ^ 2 + q.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hsq2 : ‖q + r‖ ^ 2 = (q.re + r) ^ 2 + q.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have h9 : (3 * ‖z‖ / 4) ^ 2 ≤ ‖q‖ ^ 2 := pow_le_pow_left₀ (by positivity) hq1 2
  have key : (‖z‖ / 2) ^ 2 ≤ ‖q + r‖ ^ 2 := by
    rw [hsq2]; rw [hsq] at h9
    rcases le_or_gt 0 q.re with h | h
    · nlinarith
    · have : q.re ^ 2 ≤ (‖z‖ / 4) ^ 2 := by nlinarith
      nlinarith [sq_nonneg (q.re + r)]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 key

lemma disc_slit {z q : ℂ} (hz : 5 ≤ z.re) (hq : ‖q - z‖ ≤ ‖z‖ / 4) : q ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  have hfar := disc_far hz hq (r := -q.re) (by linarith)
  have : q + ((-q.re : ℝ) : ℂ) = 0 := by apply Complex.ext <;> simp [h2]
  rw [this, norm_zero] at hfar
  have : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) ((Complex.re_le_norm z).trans' hz)
  linarith

lemma disc_add_ne {z q : ℂ} (hz : 5 ≤ z.re) (hq : ‖q - z‖ ≤ ‖z‖ / 4) (n m : ℕ) :
    q + n ≠ -m := by
  intro h
  have hfar := disc_far hz hq (r := (n : ℝ) + m) (by positivity)
  have : q + (((n : ℝ) + m : ℝ) : ℂ) = 0 := by push_cast; rw [← add_assoc, h]; ring
  rw [this, norm_zero] at hfar
  have : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) ((Complex.re_le_norm z).trans' hz)
  linarith

/-- `ψ(w+N) = ψ(w) + Σ_{n<N} 1/(w+n)`. -/
lemma digamma_add_nat {w : ℂ} (hw : ∀ n m : ℕ, w + n ≠ -m) (N : ℕ) :
    digamma (w + N) = digamma w + ∑ n ∈ Finset.range N, (w + n)⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    have := digamma_apply_add_one (w + N) (hw N)
    rw [show w + ((N + 1 : ℕ) : ℂ) = w + N + 1 by push_cast; ring, this]

lemma norm_digamma_sub_log_le_eight {a : ℂ} (ha : 6 ≤ a.re) : ‖digamma a - log a‖ ≤ 8 := by
  refine (norm_digamma_sub_log_le (by linarith)).trans ?_
  rw [div_le_iff₀ (by linarith [abs_nonneg a.im])]
  nlinarith [abs_nonneg a.im]

theorem norm_digamma_sub_le_disc {z w : ℂ} (hz : 5 ≤ z.re) (hw : ‖w - z‖ ≤ ‖z‖ / 4) :
    ‖digamma w - digamma z‖ ≤ 18 := by
  have hzpos : 5 ≤ ‖z‖ := (Complex.re_le_norm z).trans' hz
  set N : ℕ := ⌈‖z‖ / 4⌉₊ + 1 with hN
  have hN1 : ‖z‖ / 4 + 1 ≤ (N : ℝ) := by
    have := Nat.le_ceil (‖z‖ / 4); rw [hN]; push_cast; linarith
  have hN2 : (N : ℝ) ≤ ‖z‖ / 4 + 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ ‖z‖ / 4 by positivity); rw [hN]; push_cast; linarith
  have hzz : ‖z - z‖ ≤ ‖z‖ / 4 := by simp; positivity
  have hshw := digamma_add_nat (disc_add_ne hz hw) N
  have hshz := digamma_add_nat (disc_add_ne hz hzz) N
  have hwre : z.re - ‖z‖ / 4 ≤ w.re := by
    have := Complex.abs_re_le_norm (w - z); rw [sub_re] at this
    have := neg_abs_le (w.re - z.re); linarith
  have hreW : 6 ≤ (w + N).re := by simp; linarith
  have hreZ : 6 ≤ (z + N).re := by simp; linarith
  -- (i) log difference by the mean value inequality
  have hlog : ‖log (w + N) - log (z + N)‖ ≤ 1 / 2 := by
    have hseg : ∀ p ∈ segment ℝ (z + N) (w + N), ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
        p = (z + θ * (w - z)) + ((N : ℝ) : ℂ) := by
      intro p hp
      rw [segment_eq_image] at hp
      obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hp
      exact ⟨θ, h0, h1, by simp only [Complex.real_smul]; push_cast; ring⟩
    have hq : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ‖(z + θ * (w - z)) - z‖ ≤ ‖z‖ / 4 := by
      intro θ h0 h1
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
      nlinarith [norm_nonneg (w - z)]
    have hre : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → 0 < ((z + θ * (w - z)) + ((N : ℝ) : ℂ)).re := by
      intro θ h0 h1
      have : z.re - ‖z‖ / 4 ≤ (z + θ * (w - z)).re := by
        have := Complex.abs_re_le_norm ((z + θ * (w - z)) - z); rw [sub_re] at this
        have := neg_abs_le ((z + θ * (w - z)).re - z.re)
        linarith [hq θ h0 h1]
      simp only [add_re, ofReal_re] at this ⊢
      linarith
    have hd : ∀ p ∈ segment ℝ (z + N) (w + N), DifferentiableAt ℂ log p := by
      intro p hp
      obtain ⟨θ, h0, h1, rfl⟩ := hseg p hp
      exact (hasDerivAt_log (mem_slitPlane_iff.2 (Or.inl (hre θ h0 h1)))).differentiableAt
    have hb : ∀ p ∈ segment ℝ (z + N) (w + N), ‖deriv log p‖ ≤ 2 / ‖z‖ := by
      intro p hp
      obtain ⟨θ, h0, h1, rfl⟩ := hseg p hp
      rw [(hasDerivAt_log (mem_slitPlane_iff.2 (Or.inl (hre θ h0 h1)))).deriv, norm_inv]
      have := disc_far hz (hq θ h0 h1) (r := (N : ℝ)) (by positivity)
      rw [show (2 : ℝ) / ‖z‖ = (‖z‖ / 2)⁻¹ by field_simp]
      exact inv_anti₀ (by positivity) this
    have := (convex_segment (z + N) (w + N)).norm_image_sub_le_of_norm_deriv_le hd hb
      (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    rw [show w + (N : ℂ) - (z + N) = w - z by ring] at this
    calc _ ≤ 2 / ‖z‖ * ‖w - z‖ := this
      _ ≤ 2 / ‖z‖ * (‖z‖ / 4) := by gcongr
      _ = 1 / 2 := by field_simp; ring
  -- (ii) the finite sum
  have hsum : ‖∑ n ∈ Finset.range N, ((w + n)⁻¹ - (z + n)⁻¹)‖ ≤ 1 := by
    have hterm : ∀ n ∈ Finset.range N, ‖(w + n)⁻¹ - (z + n)⁻¹‖ ≤ 1 / ‖z‖ := by
      intro n _
      have h1 := disc_far hz hw (r := (n : ℝ)) (by positivity)
      have h2 := disc_far hz hzz (r := (n : ℝ)) (by positivity)
      push_cast at h1 h2
      have hw0 : w + n ≠ 0 := by
        intro h; rw [h, norm_zero] at h1; linarith
      have hz0 : z + n ≠ 0 := by
        intro h; rw [h, norm_zero] at h2; linarith
      rw [inv_sub_inv hw0 hz0, norm_div, norm_mul,
        show z + (n : ℂ) - (w + n) = -(w - z) by ring, norm_neg, div_le_iff₀ (by positivity)]
      calc ‖w - z‖ ≤ ‖z‖ / 4 := hw
        _ ≤ 1 / ‖z‖ * ((‖z‖ / 2) * (‖z‖ / 2)) := by
            rw [show 1 / ‖z‖ * ((‖z‖ / 2) * (‖z‖ / 2)) = ‖z‖ / 4 by field_simp; ring]
        _ ≤ 1 / ‖z‖ * (‖w + n‖ * ‖z + n‖) := by gcongr
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div, div_le_one (by linarith)]
    linarith
  -- assemble
  have e : digamma w - digamma z = (log (w + N) - log (z + N)) + (digamma (w + N) - log (w + N)) -
      (digamma (z + N) - log (z + N)) - ∑ n ∈ Finset.range N, ((w + n)⁻¹ - (z + n)⁻¹) := by
    rw [Finset.sum_sub_distrib, hshw, hshz]; ring
  rw [e]
  have h1 := norm_digamma_sub_log_le_eight hreW
  have h2 := norm_digamma_sub_log_le_eight hreZ
  have := norm_sub_le ((log (w + N) - log (z + N)) + (digamma (w + N) - log (w + N)) -
      (digamma (z + N) - log (z + N))) (∑ n ∈ Finset.range N, ((w + n)⁻¹ - (z + n)⁻¹))
  have := norm_sub_le ((log (w + N) - log (z + N)) + (digamma (w + N) - log (w + N)))
    (digamma (z + N) - log (z + N))
  have := norm_add_le (log (w + N) - log (z + N)) (digamma (w + N) - log (w + N))
  linarith

/-- **Cauchy estimate**: `‖ψ^{(k)}(z)‖ ≤ 18 k! 4^k / ‖z‖^k` for `k ≥ 1`, `Re z ≥ 5`. -/
theorem norm_iteratedDeriv_digamma_le {k : ℕ} (hk : 1 ≤ k) {z : ℂ} (hz : 5 ≤ z.re) :
    ‖iteratedDeriv k digamma z‖ ≤ 18 * k.factorial * 4 ^ k / ‖z‖ ^ k := by
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) ((Complex.re_le_norm z).trans' hz)
  set R : ℝ := ‖z‖ / 4
  have hR : 0 < R := by positivity
  set h : ℂ → ℂ := fun w => digamma w - digamma z
  have hsub : closedBall z R ⊆ slitPlane := fun q hq => disc_slit hz (by
    rw [mem_closedBall, dist_eq_norm] at hq; exact hq)
  have hdiff : DifferentiableOn ℂ h slitPlane :=
    (analyticOnNhd_digamma.differentiableOn).sub_const _
  have hC : ∀ w ∈ sphere z R, ‖h w‖ ≤ 18 := by
    intro w hw
    rw [mem_sphere, dist_eq_norm] at hw
    exact norm_digamma_sub_le_disc hz hw.le
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR
    (hdiff.diffContOnCl_ball hsub) hC
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have he : iteratedDeriv (j + 1) h = iteratedDeriv (j + 1) digamma := by
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    congr 1; funext w; exact deriv_sub_const _
  rw [he] at hc
  refine hc.trans (le_of_eq ?_)
  simp only [R]; rw [div_pow]; field_simp

/-- **Differences of `ψ^{(k)}` on the critical line**: for `x ≥ −1` and every `k`,
`‖ψ^{(k)}(6+it+u) − ψ^{(k)}(6+it)‖ ≤ D (1+|y|)^{k+2}/(1+|t|)^{k+1}`. -/
theorem norm_iteratedDeriv_digamma_diff_le {x : ℝ} (hx : -1 ≤ x) (k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t y : ℝ,
      ‖iteratedDeriv k digamma ((6 + t * I) + ((x : ℂ) + y * I)) -
          iteratedDeriv k digamma (6 + t * I)‖ ≤ D * (1 + |y|) ^ (k + 2) / (1 + |t|) ^ (k + 1) := by
  set C : ℝ := 18 * (k + 1).factorial * 4 ^ (k + 1)
  refine ⟨(1 + |x|) * C * 2 ^ (k + 1), by positivity, fun t y => ?_⟩
  set s : ℂ := 6 + t * I
  set u : ℂ := (x : ℂ) + y * I
  have h1t : 0 < 1 + |t| := by positivity
  have hseg : ∀ w ∈ segment ℝ s (s + u), ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      w = (6 + t * I) + (((θ * x : ℝ) : ℂ) + ((θ * y : ℝ) : ℂ) * I) := by
    intro w hw
    rw [segment_eq_image] at hw
    obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hw
    exact ⟨θ, h0, h1, by simp only [s, u, Complex.real_smul]; push_cast; ring⟩
  have hre5 : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      5 ≤ ((6 + t * I) + (((θ * x : ℝ) : ℂ) + ((θ * y : ℝ) : ℂ) * I)).re := by
    intro θ h0 h1; simp; nlinarith
  have hd : ∀ w ∈ segment ℝ s (s + u), DifferentiableAt ℂ (iteratedDeriv k digamma) w := by
    intro w hw
    obtain ⟨θ, h0, h1, rfl⟩ := hseg w hw
    exact (analyticOnNhd_iteratedDeriv_digamma k _
      (mem_slitPlane_iff.2 (Or.inl (by linarith [hre5 θ h0 h1])))).differentiableAt
  have hb : ∀ w ∈ segment ℝ s (s + u), ‖deriv (iteratedDeriv k digamma) w‖ ≤
      C * (2 * (1 + |y|) / (1 + |t|)) ^ (k + 1) := by
    intro w hw
    obtain ⟨θ, h0, h1, rfl⟩ := hseg w hw
    rw [← iteratedDeriv_succ]
    refine (norm_iteratedDeriv_digamma_le (by omega) (hre5 θ h0 h1)).trans ?_
    have hinv := norm_inv_shift_le t (θ * x) (θ * y) (by nlinarith)
    have hθy : |θ * y| ≤ |y| := by rw [abs_mul, abs_of_nonneg h0]; nlinarith [abs_nonneg y]
    set W : ℂ := (6 + t * I) + (((θ * x : ℝ) : ℂ) + ((θ * y : ℝ) : ℂ) * I)
    have hWpos : 0 < ‖W‖ := lt_of_lt_of_le (by norm_num) ((Complex.re_le_norm W).trans' (hre5 θ h0 h1))
    rw [norm_inv] at hinv
    have : ‖W‖⁻¹ ≤ 2 * (1 + |y|) / (1 + |t|) := hinv.trans (by gcongr)
    calc 18 * ((k + 1).factorial : ℝ) * 4 ^ (k + 1) / ‖W‖ ^ (k + 1)
        = C * (‖W‖⁻¹) ^ (k + 1) := by simp only [C]; rw [inv_pow]; ring
      _ ≤ C * (2 * (1 + |y|) / (1 + |t|)) ^ (k + 1) := by gcongr
  have hmv := (convex_segment s (s + u)).norm_image_sub_le_of_norm_deriv_le hd hb
    (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  rw [add_sub_cancel_left] at hmv
  have hu : ‖u‖ ≤ (1 + |x|) * (1 + |y|) := by
    have := Complex.norm_le_abs_re_add_abs_im u
    simp [u] at this; nlinarith [abs_nonneg x, abs_nonneg y]
  calc _ ≤ C * (2 * (1 + |y|) / (1 + |t|)) ^ (k + 1) * ‖u‖ := hmv
    _ ≤ C * (2 * (1 + |y|) / (1 + |t|)) ^ (k + 1) * ((1 + |x|) * (1 + |y|)) := by gcongr
    _ = _ := by rw [div_pow, mul_pow]; field_simp; ring

end RamanujanTau.HeckeAFE3
