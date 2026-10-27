/-
# The minor arc

For `0 < t ≤ 1/2` and `t ≤ |θ| ≤ π`: `‖F(e^{−(t+iθ)})‖ ≤ ‖F(e^{−t})‖ · e^{−1/(200t)}`.

* per factor: `‖1 − xe^{iφ}‖ ≥ (1−x)·e^{x(1−cos φ)/8}`;
* `Σ_k r^k(1 − cos kθ) = r/(1−r) − Re(q/(1−q)) ≥ r/(1−r)·2/25` (since `‖1−q‖ ≥ (25/23)(1−r)`).
-/
import RamanujanTau.HardyRamanujan.Coeff

set_option autoImplicit false

namespace HardyRamanujan
open Complex Metric Realize Filter
open scoped Real Topology

lemma normSq_one_sub (x φ : ℝ) :
    ‖1 - (x : ℂ) * cexp (φ * I)‖ ^ 2 = (1 - x) ^ 2 + 2 * x * (1 - Real.cos φ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, zero_mul,
    sub_zero, sub_im, one_im, mul_im, zero_sub]
  linear_combination x ^ 2 * Real.sin_sq_add_cos_sq φ

/-- **one factor**. -/
lemma factor_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (φ : ℝ) :
    (1 - x) * Real.exp (x * (1 - Real.cos φ) / 8) ≤ ‖1 - (x : ℂ) * cexp (φ * I)‖ := by
  set c := 1 - Real.cos φ with hc
  have hc0 : 0 ≤ c := by rw [hc]; linarith [Real.cos_le_one φ]
  have hc2 : c ≤ 2 := by rw [hc]; linarith [Real.neg_one_le_cos φ]
  have hy : x * c / 4 < 1 := by nlinarith
  have hexp : Real.exp (x * c / 4) ≤ 1 + 2 * x * c := by
    have h := Real.exp_bound_div_one_sub_of_interval (by positivity : 0 ≤ x * c / 4) hy
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have hs0 : 0 ≤ x * c := mul_nonneg hx0 hc0
    have hs2 : x * c ≤ 2 := by nlinarith
    nlinarith [mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ 7 / 4 - x * c / 2)]
  have hL : 0 ≤ (1 - x) * Real.exp (x * c / 8) := mul_nonneg (by linarith) (Real.exp_pos _).le
  refine (pow_le_pow_iff_left₀ hL (norm_nonneg _) (two_ne_zero)).mp ?_
  rw [normSq_one_sub, mul_pow, ← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (x * c / 8) = x * c / 4 by push_cast; ring]
  have h1 : (1 - x) ^ 2 ≤ 1 := by nlinarith
  calc (1 - x) ^ 2 * Real.exp (x * c / 4) ≤ (1 - x) ^ 2 * (1 + 2 * x * c) :=
        mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
    _ ≤ (1 - x) ^ 2 + 2 * x * c := by nlinarith [mul_nonneg hx0 hc0]

/-- `s_k = r^{k+1}(1 − cos((k+1)θ))/8`. -/
noncomputable def sk (r θ : ℝ) (k : ℕ) : ℝ := r ^ (k + 1) * (1 - Real.cos ((k + 1) * θ)) / 8

lemma summable_sk {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) : Summable (sk r θ) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    (((summable_geometric_of_lt_one hr0 hr1).mul_left (r / 4)))
  · unfold sk; have := Real.cos_le_one ((k + 1) * θ)
    exact div_nonneg (mul_nonneg (pow_nonneg hr0 _) (by linarith)) (by norm_num)
  · unfold sk
    have := Real.neg_one_le_cos ((k + 1) * θ)
    have hp : 0 ≤ r ^ (k + 1) := by positivity
    calc r ^ (k + 1) * (1 - Real.cos ((k + 1) * θ)) / 8 ≤ r ^ (k + 1) * 2 / 8 := by gcongr; linarith
      _ = r / 4 * r ^ k := by ring

lemma multipliable_Pq {q : ℂ} (hq : ‖q‖ < 1) : Multipliable fun n : ℕ => (1 - q ^ (n + 1)) := by
  have hs : Summable fun n : ℕ => -q ^ (n + 1) := by
    refine Summable.of_norm ?_
    simpa [norm_pow] using (summable_geometric_of_lt_one (norm_nonneg _) hq).comp_injective (add_left_injective 1)
  simpa [sub_eq_add_neg] using Complex.multipliable_one_add_of_summable hs

/-- **the product bound** `‖(r;r)_∞‖ e^{Σ s_k} ≤ ‖(q;q)_∞‖`, `q = re^{iθ}`. -/
lemma Pq_norm_lower {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    ‖Pq r‖ * Real.exp (∑' k, sk r θ k) ≤ ‖Pq ((r : ℂ) * cexp (θ * I))‖ := by
  have hq : ‖(r : ℂ) * cexp (θ * I)‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0, norm_exp_ofReal_mul_I, mul_one]; exact hr1
  have hr' : ‖(r : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hr0]; exact hr1
  have hA := ((multipliable_Pq hr').hasProd.tendsto_prod_nat).norm
  have hB := ((multipliable_Pq hq).hasProd.tendsto_prod_nat).norm
  rw [← Pq_eq] at hA hB
  have hS := (summable_sk hr0 hr1 θ).hasSum.tendsto_sum_nat
  have hlim := hA.mul ((Real.continuous_exp.tendsto _).comp hS)
  refine le_of_tendsto_of_tendsto' hlim hB fun N => ?_
  simp only [Function.comp, norm_prod]
  rw [Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun k _ => by positivity) fun k _ => ?_
  have hx1 : r ^ (k + 1) < 1 := pow_lt_one₀ hr0 hr1 (by omega)
  have e1 : ‖1 - (r : ℂ) ^ (k + 1)‖ = 1 - r ^ (k + 1) := by
    rw [← ofReal_pow, ← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have e2 : ((r : ℂ) * cexp (θ * I)) ^ (k + 1) = ((r ^ (k + 1) : ℝ) : ℂ) * cexp (((k + 1) * θ : ℝ) * I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]; push_cast; congr 2; ring
  rw [e1, e2, sk, show r ^ (k + 1) * (1 - Real.cos ((k + 1) * θ)) / 8 =
    r ^ (k + 1) * (1 - Real.cos (((k + 1 : ℕ) : ℝ) * θ)) / 8 by push_cast; ring]
  have := factor_bound (pow_nonneg hr0 (k + 1)) hx1 ((k + 1 : ℕ) * θ)
  push_cast at this ⊢
  exact this

/-- the sum `Σ s_k`. -/
lemma hasSum_sk {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    HasSum (sk r θ) ((r / (1 - r) - (((r : ℂ) * cexp (θ * I)) / (1 - (r : ℂ) * cexp (θ * I))).re) / 8) := by
  set q : ℂ := (r : ℂ) * cexp (θ * I) with hqdef
  have hq : ‖q‖ < 1 := by
    rw [hqdef, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0, norm_exp_ofReal_mul_I, mul_one]; exact hr1
  have h1 : HasSum (fun k : ℕ => r ^ (k + 1)) (r / (1 - r)) := by
    have := (hasSum_geometric_of_lt_one hr0 hr1).mul_left r
    convert this using 1
    funext k; ring
  have h2 : HasSum (fun k : ℕ => q ^ (k + 1)) (q / (1 - q)) := by
    have := (hasSum_geometric_of_norm_lt_one hq).mul_left q
    convert this using 1
    funext k; ring
  have h2r := (Complex.hasSum_re h2)
  have h2' : HasSum (fun k : ℕ => r ^ (k + 1) * Real.cos ((k + 1) * θ)) (q / (1 - q)).re := by
    convert h2r using 1
    funext k
    rw [hqdef, mul_pow, ← Complex.exp_nat_mul, ← ofReal_pow,
      show ((k + 1 : ℕ) : ℂ) * (θ * I) = (((k + 1 : ℕ) * θ : ℝ) : ℂ) * I by push_cast; ring,
      re_ofReal_mul, exp_ofReal_mul_I_re]
    push_cast; ring
  have := (h1.sub h2').div_const 8
  convert this using 1
  funext k; rw [sk]; ring

lemma one_sub_cos_ge {θ : ℝ} (h : |θ| ≤ π) : 2 * θ ^ 2 / π ^ 2 ≤ 1 - Real.cos θ := by
  have hπ := Real.pi_pos
  have hs : 2 / π * (|θ| / 2) ≤ Real.sin (|θ| / 2) := Real.mul_le_sin (by positivity) (by linarith)
  have hc : 1 - Real.cos θ = 2 * Real.sin (|θ| / 2) ^ 2 := by
    rw [← Real.cos_abs θ, show |θ| = 2 * (|θ| / 2) by ring, Real.cos_two_mul, Real.cos_sq']
    try ring_nf
  rw [hc]
  have h0 : 0 ≤ 2 / π * (|θ| / 2) := by positivity
  have := pow_le_pow_left₀ h0 hs 2
  have hθ : θ ^ 2 = |θ| ^ 2 := (sq_abs θ).symm
  rw [hθ]
  calc 2 * |θ| ^ 2 / π ^ 2 = 2 * (2 / π * (|θ| / 2)) ^ 2 := by field_simp; try ring
    _ ≤ _ := by linarith

/-- **the minor arc**. -/
theorem minor_bound {t θ : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2) (hθ1 : t ≤ |θ|) (hθ2 : |θ| ≤ π) :
    ‖F (cexp (-zt t θ))‖ ≤ ‖F (cexp (-(t : ℂ)))‖ * Real.exp (-(1 / (200 * t))) := by
  set r := Real.exp (-t) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  have hrh : 1 / 2 ≤ r := by
    rw [hr]
    have : Real.exp (t) ≤ 2 := by
      have := Real.exp_bound_div_one_sub_of_interval ht.le (by linarith : t < 1)
      refine this.trans ?_
      rw [div_le_iff₀ (by linarith)]; linarith
    rw [Real.exp_neg]
    rw [le_inv_comm₀ (by norm_num) (Real.exp_pos _)]; linarith
  have h1r : 1 - r ≤ t := by rw [hr]; linarith [Real.add_one_le_exp (-t)]
  have h1r0 : 0 < 1 - r := by linarith
  -- the point
  have hz : cexp (-zt t θ) = (r : ℂ) * cexp ((-θ : ℝ) * I) := by
    rw [hr, Complex.ofReal_exp, ← Complex.exp_add]; congr 1; simp [zt]; ring
  set q : ℂ := (r : ℂ) * cexp ((-θ : ℝ) * I) with hqdef
  -- `‖1 − q‖ ≥ (25/23)(1 − r)`
  have hn : (25 / 23 * (1 - r)) ^ 2 ≤ ‖1 - q‖ ^ 2 := by
    rw [hqdef, normSq_one_sub]
    have hc := one_sub_cos_ge (θ := -θ) (by rwa [abs_neg])
    have hθt : t ^ 2 ≤ (-θ) ^ 2 := by rw [neg_sq, ← sq_abs θ]; exact pow_le_pow_left₀ ht.le hθ1 2
    have hπ2 : π ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have hπ0 : 0 < π ^ 2 := by positivity
    have : 2 * r * (1 - Real.cos (-θ)) ≥ 2 * (1 / 2) * (2 * t ^ 2 / π ^ 2) := by
      have h0 : 0 ≤ 2 * t ^ 2 / π ^ 2 := by positivity
      have : 2 * t ^ 2 / π ^ 2 ≤ 2 * (-θ) ^ 2 / π ^ 2 := by gcongr
      nlinarith
    have h3 : 2 * t ^ 2 / π ^ 2 ≥ t ^ 2 / 5 := by
      rw [ge_iff_le, div_le_div_iff₀ (by norm_num) hπ0]; nlinarith
    nlinarith [sq_nonneg (1 - r), mul_le_mul h1r h1r h1r0.le ht.le]
  have hn' : 25 / 23 * (1 - r) ≤ ‖1 - q‖ :=
    (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp hn
  -- `Re(q/(1−q)) ≤ (23/25) r/(1−r)`
  have hre : (q / (1 - q)).re ≤ 23 / 25 * (r / (1 - r)) := by
    refine (Complex.re_le_norm _).trans ?_
    have hq : ‖q‖ = r := by
      rw [hqdef, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le, norm_exp_ofReal_mul_I, mul_one]
    rw [norm_div, hq, div_le_iff₀ (by linarith [hn', h1r0])]
    calc r = 23 / 25 * (r / (1 - r)) * (25 / 23 * (1 - r)) := by field_simp
      _ ≤ 23 / 25 * (r / (1 - r)) * ‖1 - q‖ := by gcongr
  -- the exponent
  have hS : 1 / (200 * t) ≤ ∑' k, sk r (-θ) k := by
    rw [(hasSum_sk hr0.le hr1 (-θ)).tsum_eq]
    have : r / (1 - r) ≥ (1 / 2) / t := by
      rw [ge_iff_le, div_le_div_iff₀ ht h1r0]; nlinarith
    have h' : 1 / (200 * t) = (2 / 25 * ((1 / 2) / t)) / 8 := by field_simp; ring
    rw [h']
    gcongr
    linarith
  -- assemble
  have hP := Pq_norm_lower hr0.le hr1 (-θ)
  have hPr : 0 < ‖Pq r‖ := norm_pos_iff.mpr (Pq_ne_zero (by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hr0.le]; exact hr1))
  have hrc : cexp (-(t : ℂ)) = (r : ℂ) := by rw [hr, Complex.ofReal_exp]; push_cast; ring_nf
  rw [hz, hrc, F, F, norm_inv, norm_inv]
  rw [← hqdef] at hP
  have hPq : 0 < ‖Pq q‖ := lt_of_lt_of_le (mul_pos hPr (Real.exp_pos _)) hP
  rw [Real.exp_neg, ← mul_inv]
  exact inv_anti₀ (by positivity) (le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hS) hPr.le) hP)

end HardyRamanujan
