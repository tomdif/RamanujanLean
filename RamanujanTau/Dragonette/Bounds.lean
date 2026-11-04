/-
# Bounds for `b(−e^{−z}) = Oz(e^{−z})·Jt z`

* near the cusp: `Fr z · Jt(π²/z) = 1 + O(e^{−Re(π²/z)})` and `Fr z = 1 + O(e^{−Re(π²/z)})`;
* away from it: `‖(−s;s²)_∞‖ ≤ (−r;r²)_∞ e^{−D/4}`, `D = r/(1−r²) − Re(s/(1−s²))`, and `D ≥ 1/(40t)` on the minor arc.
-/
import RamanujanTau.Dragonette.Phi

set_option autoImplicit false

namespace Dragonette
open Complex Finset Filter HardyRamanujan Metric
open scoped Real Topology

lemma mul_sub_one_le {a b : ℂ} {α β : ℝ} (ha : ‖a - 1‖ ≤ α) (hb : ‖b - 1‖ ≤ β) :
    ‖a * b - 1‖ ≤ α + β + α * β := by
  have hβ : 0 ≤ β := (norm_nonneg _).trans hb
  have hα : 0 ≤ α := (norm_nonneg _).trans ha
  have hb' : ‖b‖ ≤ 1 + β := by
    have := norm_add_le (b - 1) 1; simp at this; linarith
  calc ‖a * b - 1‖ = ‖(a - 1) * b + (b - 1)‖ := by ring_nf
    _ ≤ ‖a - 1‖ * ‖b‖ + ‖b - 1‖ := by rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ α * (1 + β) + β := by gcongr
    _ = _ := by ring

lemma Pq_sub_one {w : ℂ} {ε : ℝ} (hw : ‖w‖ ≤ ε) (hε : 2 * C0 * ε ≤ 1 / 2) (hε2 : ε ≤ 1 / 2) :
    ‖Pq w - 1‖ ≤ 4 * C0 * ε := by
  have hF := (F_sub_one (hw.trans hε2)).trans (by gcongr; linarith [C0_nonneg] : 2 * C0 * ‖w‖ ≤ 2 * C0 * ε)
  have hFn : 1 / 2 ≤ ‖F w‖ := by
    have := norm_sub_norm_le (1 : ℂ) (F w)
    rw [norm_one, norm_sub_rev] at this; linarith
  have hF0 : F w ≠ 0 := fun h => by rw [h, norm_zero] at hFn; linarith
  have e : Pq w - 1 = (1 - F w) / F w := by
    have : Pq w = 1 / F w := by rw [F, one_div, inv_inv]
    rw [this]; field_simp
  rw [e, norm_div, div_le_iff₀ (by linarith), norm_sub_rev]
  have h4 : 0 ≤ 4 * C0 * ε := by nlinarith [C0_nonneg, (norm_nonneg w).trans hw]
  nlinarith [mul_le_mul_of_nonneg_left hFn h4]

lemma norm_cexp_mul_le {z : ℂ} {c : ℝ} (hc : 1 ≤ c) (hz : 0 ≤ ((π : ℂ) ^ 2 / z).re) :
    ‖cexp (-((c : ℂ) * π ^ 2 / z))‖ ≤ Real.exp (-((π : ℂ) ^ 2 / z).re) := by
  rw [norm_exp, Real.exp_le_exp, show (c : ℂ) * π ^ 2 / z = (c : ℂ) * (π ^ 2 / z) by ring, neg_re, re_ofReal_mul]
  nlinarith

/-- **the cusp corrections**. -/
theorem Fr_near {z : ℂ} (hz : 0 < z.re) (h1 : 1 ≤ ((π : ℂ) ^ 2 / z).re)
    (hη : (4 * C0 + 4) * Real.exp (-((π : ℂ) ^ 2 / z).re) ≤ 1) :
    ‖Fr z - 1‖ ≤ 15 * ((4 * C0 + 4) * Real.exp (-((π : ℂ) ^ 2 / z).re)) ∧
    ‖Fr z * Jt (π ^ 2 / z) - 1‖ ≤ 31 * ((4 * C0 + 4) * Real.exp (-((π : ℂ) ^ 2 / z).re)) := by
  set ε := Real.exp (-((π : ℂ) ^ 2 / z).re)
  set η := (4 * C0 + 4) * ε
  have hC := C0_nonneg
  have hε0 : 0 ≤ ε := (Real.exp_pos _).le
  have hεη : ε ≤ η / 4 := by nlinarith
  have hε2 : ε ≤ 1 / 2 := by linarith
  have hCε : 2 * C0 * ε ≤ 1 / 2 := by nlinarith
  have h0 : 0 ≤ ((π : ℂ) ^ 2 / z).re := by linarith
  have w1 : ‖cexp (-(4 * π ^ 2 / z))‖ ≤ ε := by
    have := norm_cexp_mul_le (c := 4) (by norm_num) h0; push_cast at this; exact this
  have w2 : ‖cexp (-(π ^ 2 / z))‖ ≤ ε := by
    have := norm_cexp_mul_le (c := 1) le_rfl h0; push_cast at this; simpa using this
  have w3 : ‖cexp (-(2 * π ^ 2 / z))‖ ≤ ε := by
    have := norm_cexp_mul_le (c := 2) (by norm_num) h0; push_cast at this; exact this
  have a1 : ‖F (cexp (-(4 * π ^ 2 / z))) - 1‖ ≤ η :=
    (F_sub_one (w1.trans hε2)).trans (by nlinarith [norm_nonneg (cexp (-(4 * π ^ 2 / z)))])
  have a2 : ‖F (cexp (-(π ^ 2 / z))) - 1‖ ≤ η :=
    (F_sub_one (w2.trans hε2)).trans (by nlinarith [norm_nonneg (cexp (-(π ^ 2 / z)))])
  have a3 : ‖Pq (cexp (-(2 * π ^ 2 / z))) - 1‖ ≤ η := (Pq_sub_one w3 hCε hε2).trans (by nlinarith)
  have a4 : ‖Jt (π ^ 2 / z) - 1‖ ≤ η := (norm_Jt_sub_one_le h1).trans (by nlinarith)
  have hη0 : 0 ≤ η := by positivity
  have b12 := mul_sub_one_le a1 a2
  have b123 := mul_sub_one_le b12 a3
  have b1233 := mul_sub_one_le b123 a3
  have hFr : ‖Fr z - 1‖ ≤ 15 * η := by
    have e : Fr z = F (cexp (-(4 * π ^ 2 / z))) * F (cexp (-(π ^ 2 / z))) * Pq (cexp (-(2 * π ^ 2 / z))) *
        Pq (cexp (-(2 * π ^ 2 / z))) := by unfold Fr; ring
    rw [e]
    refine b1233.trans ?_
    nlinarith [mul_nonneg hη0 hη0, mul_nonneg (mul_nonneg hη0 hη0) hη0]
  refine ⟨hFr, (mul_sub_one_le hFr a4).trans ?_⟩
  nlinarith [mul_nonneg hη0 hη0]

/-- **one factor, from above**: `‖1 + u‖ ≤ (1 + ‖u‖) e^{−(‖u‖ − Re u)/4}` for `‖u‖ ≤ 1`. -/
lemma factor_upper {u : ℂ} (hu : ‖u‖ ≤ 1) : ‖1 + u‖ ≤ (1 + ‖u‖) * Real.exp (-(‖u‖ - u.re) / 4) := by
  set a := ‖u‖
  set c := u.re
  have hc : |c| ≤ a := Complex.abs_re_le_norm u
  have ha0 : 0 ≤ a := norm_nonneg u
  have hd : 0 ≤ a - c := by linarith [le_abs_self c]
  have hsq : ‖1 + u‖ ^ 2 = 1 + 2 * c + a ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, show a ^ 2 = ‖u‖ ^ 2 from rfl, Complex.sq_norm,
      Complex.normSq_apply]
    simp only [add_re, one_re, add_im, one_im, zero_add]; ring
  have he : 1 - (a - c) / 2 ≤ Real.exp (-(a - c) / 2) := by linarith [Real.add_one_le_exp (-(a - c) / 2)]
  have hR : 0 ≤ (1 + a) * Real.exp (-(a - c) / 4) := by positivity
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).mp ?_
  rw [hsq, mul_pow, ← Real.exp_nat_mul]
  have he' : Real.exp (((2 : ℕ) : ℝ) * (-(a - c) / 4)) = Real.exp (-(a - c) / 2) := by congr 1; push_cast; ring
  rw [he']
  have h4 : (1 + a) ^ 2 ≤ 4 := by nlinarith
  calc 1 + 2 * c + a ^ 2 = (1 + a) ^ 2 * 1 - 2 * (a - c) := by ring
    _ ≤ (1 + a) ^ 2 * (1 - (a - c) / 2) := by nlinarith
    _ ≤ _ := by gcongr

/-- **the product from above**. -/
theorem Oz_norm_upper {s : ℂ} (hs : ‖s‖ < 1) :
    ‖Oz s‖ ≤ ‖Oz (‖s‖ : ℂ)‖ * Real.exp (-(‖s‖ / (1 - ‖s‖ ^ 2) - (s / (1 - s ^ 2)).re) / 4) := by
  set r := ‖s‖ with hr
  have h0 : 0 ≤ r := norm_nonneg s
  have hr' : ‖(r : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg h0]; exact hs
  have hs2 : ‖s ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ h0 hs (by norm_num)
  have hr2 : r ^ 2 < 1 := pow_lt_one₀ h0 hs (by norm_num)
  have hA := ((mult_one_add_pow hr' (fun k => 2 * k + 1) (fun k => by dsimp only; omega)).hasProd.tendsto_prod_nat).norm
  have hB := ((mult_one_add_pow hs (fun k => 2 * k + 1) (fun k => by dsimp only; omega)).hasProd.tendsto_prod_nat).norm
  have g1 : HasSum (fun k : ℕ => r ^ (2 * k + 1)) (r / (1 - r ^ 2)) := by
    have := (hasSum_geometric_of_lt_one (by positivity) hr2).mul_left r
    convert this using 1
    funext k; ring
  have g2 : HasSum (fun k : ℕ => s ^ (2 * k + 1)) (s / (1 - s ^ 2)) := by
    have := (hasSum_geometric_of_norm_lt_one hs2).mul_left s
    convert this using 1
    funext k; ring
  have hS := ((g1.sub (Complex.hasSum_re g2)).neg.div_const 4).tendsto_sum_nat
  have hlim := hA.mul ((Real.continuous_exp.tendsto _).comp hS)
  refine le_of_tendsto_of_tendsto' hB hlim fun K => ?_
  simp only [Function.comp, norm_prod]
  rw [Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun k _ => norm_nonneg _) fun k _ => ?_
  have hu : ‖s ^ (2 * k + 1)‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ h0 hs.le
  have := factor_upper hu
  have e1 : ‖1 + (r : ℂ) ^ (2 * k + 1)‖ = 1 + ‖s ^ (2 * k + 1)‖ := by
    rw [← ofReal_pow, ← ofReal_one, ← ofReal_add, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      norm_pow]
  rw [e1, norm_pow] at *
  convert this using 2

/-- **the minor-arc decay** of `(−s;s²)_∞`: for `0 < t ≤ 1/20`, `t ≤ |θ| ≤ π`,
`‖Oz(e^{−t−iθ})‖ ≤ (−r;r²)_∞ e^{−1/(160t)}`. -/
theorem Oz_minor {t θ : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 20) (hθ1 : t ≤ |θ|) (hθ2 : |θ| ≤ π) :
    ‖Oz (cexp (-zt t θ))‖ ≤ ‖Oz ((Real.exp (-t) : ℝ) : ℂ)‖ * Real.exp (-(1 / (160 * t))) := by
  set r := Real.exp (-t) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  have h1r : 1 - r ≤ t := by rw [hr]; linarith [Real.add_one_le_exp (-t)]
  have hr19 : 19 / 20 ≤ r := by linarith
  have h1r0 : 0 < 1 - r := by linarith
  have hz : cexp (-zt t θ) = (r : ℂ) * cexp ((-θ : ℝ) * I) := by
    rw [hr, Complex.ofReal_exp, ← Complex.exp_add]; congr 1; simp [zt]; ring
  set q : ℂ := (r : ℂ) * cexp ((-θ : ℝ) * I) with hqdef
  have hq : ‖q‖ = r := by
    rw [hqdef, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le, norm_exp_ofReal_mul_I, mul_one]
  -- `‖1 − q‖ ≥ (25/23)(1 − r)` (as in `HardyRamanujan.minor_bound`)
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
  have h1q : 1 - q ≠ 0 := fun h => by rw [h, norm_zero] at hn'; nlinarith
  have h1q' : 1 + q ≠ 0 := fun h => by
    have : q = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hq; linarith
  -- `Re(q/(1−q²)) ≤ (1/2)·1/‖1−q‖`
  have hsplit : q / (1 - q ^ 2) = (1 / (1 - q) - 1 / (1 + q)) / 2 := by
    have : 1 - q ^ 2 = (1 - q) * (1 + q) := by ring
    rw [this]; field_simp; ring
  have hre1 : 0 ≤ (1 / (1 + q)).re := by
    rw [one_div, inv_re]
    refine div_nonneg ?_ (Complex.normSq_nonneg _)
    have := Complex.abs_re_le_norm q
    rw [hq] at this
    simp only [add_re, one_re]; linarith [neg_abs_le q.re]
  have hre2 : (1 / (1 - q)).re ≤ 23 / 25 / (1 - r) := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_div, norm_one, div_le_div_iff₀ (norm_pos_iff.mpr h1q) h1r0]
    linarith
  have hre : (q / (1 - q ^ 2)).re ≤ 23 / 50 / (1 - r) := by
    rw [hsplit, Complex.div_ofNat_re, sub_re]
    have : 23 / 50 / (1 - r) = (23 / 25 / (1 - r)) / 2 := by ring
    rw [this]; linarith
  -- `D ≥ 1/(40t)`
  have hD : 1 / (40 * t) ≤ r / (1 - r ^ 2) - (q / (1 - q ^ 2)).re := by
    have e : r / (1 - r ^ 2) = (r / (1 + r)) / (1 - r) := by
      rw [show 1 - r ^ 2 = (1 - r) * (1 + r) by ring]; field_simp
    have hrr : 19 / 39 ≤ r / (1 + r) := by rw [le_div_iff₀ (by linarith)]; linarith
    have : 1 / (40 * t) ≤ (r / (1 + r) - 23 / 50) / (1 - r) := by
      rw [div_le_div_iff₀ (by positivity) h1r0]; nlinarith
    calc 1 / (40 * t) ≤ (r / (1 + r) - 23 / 50) / (1 - r) := this
      _ = r / (1 - r ^ 2) - 23 / 50 / (1 - r) := by rw [e]; ring
      _ ≤ _ := by linarith
  have hU := Oz_norm_upper (s := q) (by rw [hq]; exact hr1)
  rw [hq] at hU
  rw [hz]
  refine hU.trans ?_
  gcongr
  have : 1 / (160 * t) = 1 / (40 * t) / 4 := by field_simp; ring
  rw [this, neg_div]
  gcongr

end Dragonette
