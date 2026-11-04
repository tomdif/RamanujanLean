/-
# The weight-`k` gamma factor `γₘ(s) = 2π^{−s}Γ(s)Γ(s+m)(4π)^{−s−m}`, `m = k − 1`

Generalizes `RankinError/Convexity.lean` and `RankinError/Landau.lean` (which have `m = 11`):

* `gamM`, `invGamM`, `RSDataM m a κ` (the Rankin–Selberg data for weight `m + 1`);
* `gammaM_ratio_le`: for `m ≥ 2`, on `Re s = −3/2`,
  `‖γₘ(1−s)/γₘ(s)‖ ≤ (m+1)⁴ (‖s+2‖+13)^{17}`.

The exponent `17` is independent of `m`: with `w = s + m` (`Re w = m − 3/2 > 0`),
`1 − s + m = w̄ + 4`, so `Γ(1−s+m)/Γ(s+m) = (∏_{j<4}(w̄+j))·Γ(w̄)/Γ(w)`, a polynomial of degree 4
times a unimodular factor.
-/
import RamanujanTau.RankinError.Landau

set_option autoImplicit false

namespace RamanujanTau.RankinErrorGeneral

open Complex Real MeasureTheory Set Filter Topology
open RamanujanTau.RankinError

/-- The gamma factor `γₘ(s) = 2 π^{−s} Γ(s) Γ(s+m) (4π)^{−s−m}`. -/
noncomputable def gamM (m : ℕ) (s : ℂ) : ℂ :=
  2 * (π : ℂ) ^ (-s) * Complex.Gamma s * Complex.Gamma (s + m) * ((4 * π : ℝ) : ℂ) ^ (-s - m)

/-- Its reciprocal, an entire function. -/
noncomputable def invGamM (m : ℕ) (s : ℂ) : ℂ :=
  (π : ℂ) ^ s * ((4 * π : ℝ) : ℂ) ^ (s + m) / 2 * (Complex.Gamma s)⁻¹ *
    (Complex.Gamma (s + m))⁻¹

/-- The Rankin–Selberg data in weight `m + 1`. -/
structure RSDataM (m : ℕ) (a : ℕ → ℝ) (κ : ℝ) where
  Λ₀ : ℂ → ℂ
  diff : Differentiable ℂ Λ₀
  L₀ : ℝ
  bdd : ∀ s : ℂ, -3 / 2 ≤ s.re → s.re ≤ 5 / 2 → ‖Λ₀ s‖ ≤ L₀
  fe : ∀ s : ℂ, Λ₀ (1 - s) = Λ₀ s
  unfold : ∀ s : ℂ, 2 < s.re →
    gamM m s * riemannZeta (2 * s) * LSeries (fun n => (a n : ℂ)) s =
      Λ₀ s + κ * (1 / (s - 1) - 1 / s)

/-- At `m = 11` the gamma factor is the one of `RankinError`. -/
lemma gamM_eleven : gamM 11 = gam := by
  funext s; unfold gamM gam; push_cast; rfl

lemma invGamM_eleven : invGamM 11 = invGam := by
  funext s; unfold invGamM invGam; push_cast; rfl

lemma differentiable_invGamM (m : ℕ) : Differentiable ℂ (invGamM m) := by
  intro s
  have h3 : DifferentiableAt ℂ (fun s => (Complex.Gamma s)⁻¹) s := by
    simpa using Complex.differentiable_one_div_Gamma s
  have h4 : DifferentiableAt ℂ (fun s => (Complex.Gamma (s + m))⁻¹) s := by
    have := (Complex.differentiable_one_div_Gamma (s + m)).comp s
      (differentiableAt_id.add_const (m : ℂ))
    simpa [Function.comp_def] using this
  unfold invGamM
  exact ((((differentiableAt_id.const_cpow (Or.inl pi_ne_zero')).mul
    ((differentiableAt_id.add_const _).const_cpow (Or.inl fourpi_ne_zero))).div_const 2).mul
    h3).mul h4

lemma gamM_mul_invGamM (m : ℕ) {s : ℂ} (hs : 0 < s.re) : gamM m s * invGamM m s = 1 := by
  have hG1 := Complex.Gamma_ne_zero_of_re_pos hs
  have hG2 := Complex.Gamma_ne_zero_of_re_pos (s := s + m)
    (by simp; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])
  unfold gamM invGamM
  have e1 : (π : ℂ) ^ (-s) * (π : ℂ) ^ s = 1 := by
    rw [cpow_neg, inv_mul_cancel₀ (cpow_ne_zero_iff.2 (Or.inl pi_ne_zero'))]
  have e2 : ((4 * π : ℝ) : ℂ) ^ (-s - m) * ((4 * π : ℝ) : ℂ) ^ (s + m) = 1 := by
    rw [show -s - m = -(s + m) by ring, cpow_neg,
      inv_mul_cancel₀ (cpow_ne_zero_iff.2 (Or.inl fourpi_ne_zero))]
  calc _ = ((π : ℂ) ^ (-s) * (π : ℂ) ^ s) *
        (((4 * π : ℝ) : ℂ) ^ (-s - m) * ((4 * π : ℝ) : ℂ) ^ (s + m)) *
        (Complex.Gamma s * (Complex.Gamma s)⁻¹) *
        (Complex.Gamma (s + m) * (Complex.Gamma (s + m))⁻¹) := by ring
    _ = 1 := by rw [e1, e2, mul_inv_cancel₀ hG1, mul_inv_cancel₀ hG2]; ring

/-- The `Γ`-ratio on the left edge `Re s = −3/2`, for `m ≥ 2`. -/
lemma gammaM_ratio_le {m : ℕ} (hm : 2 ≤ m) {s : ℂ} (hs : s.re = -3 / 2) :
    ‖gamM m (1 - s) * invGamM m s‖ ≤ ((m : ℝ) + 1) ^ 4 * (‖s + 2‖ + 13) ^ 17 := by
  set u : ℂ := s + 2 with hu
  have hure : u.re = 1 / 2 := by rw [hu]; simp [hs]; norm_num
  have hu0 : 0 < u.re := by rw [hure]; norm_num
  have hcu0 : 0 < (starRingEnd ℂ u).re := by simp [hure]
  have hw : 1 - s = starRingEnd ℂ u + 2 := by
    apply Complex.ext <;> simp [hu, hs] <;> norm_num
  have hs' : s = u - 2 := by rw [hu]; ring
  have hGu := Complex.Gamma_ne_zero_of_re_pos hu0
  have hu1 : u - 1 ≠ 0 := by intro h; have := congrArg re h; simp [hure] at this; norm_num at this
  have hu2 : u - 2 ≠ 0 := by intro h; have := congrArg re h; simp [hure] at this; norm_num at this
  have hGs : Complex.Gamma u = (u - 1) * (u - 2) * Complex.Gamma (u - 2) := by
    have e1 := Complex.Gamma_add_one (u - 1) hu1
    have e2 := Complex.Gamma_add_one (u - 2) hu2
    rw [sub_add_cancel] at e1
    rw [show u - 2 + 1 = u - 1 by ring] at e2
    rw [e1, e2]; ring
  have r1 : Complex.Gamma (1 - s) * (Complex.Gamma s)⁻¹ =
      (starRingEnd ℂ u) * (starRingEnd ℂ u + 1) * ((u - 1) * (u - 2)) *
        (Complex.Gamma (starRingEnd ℂ u) * (Complex.Gamma u)⁻¹) := by
    have h2 := Gamma_add_nat hcu0 2
    push_cast at h2
    rw [hw, hs', h2, hGs]
    simp [Finset.prod_range_succ]
    field_simp
  have hratio : ‖Complex.Gamma (starRingEnd ℂ u) * (Complex.Gamma u)⁻¹‖ = 1 := by
    rw [norm_mul, norm_inv, norm_Gamma_conj, mul_inv_cancel₀ (norm_ne_zero_iff.2 hGu)]
  -- the second ratio, with `w = s + m`
  set w : ℂ := s + m with hwdef
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hwre : w.re = m - 3 / 2 := by rw [hwdef]; simp [hs]; ring
  have hw0 : 0 < w.re := by rw [hwre]; linarith
  have hcw0 : 0 < (starRingEnd ℂ w).re := by simp; linarith
  have hGw := Complex.Gamma_ne_zero_of_re_pos hw0
  have r2 : Complex.Gamma (1 - s + m) * (Complex.Gamma (s + m))⁻¹ =
      (∏ j ∈ Finset.range 4, (starRingEnd ℂ w + j)) *
        (Complex.Gamma (starRingEnd ℂ w) * (Complex.Gamma w)⁻¹) := by
    have e1 : 1 - s + m = starRingEnd ℂ w + (4 : ℕ) := by
      apply Complex.ext <;> simp [hwdef, hs] <;> ring
    rw [e1, Gamma_add_nat hcw0 4, ← hwdef]
    ring
  have hratio2 : ‖Complex.Gamma (starRingEnd ℂ w) * (Complex.Gamma w)⁻¹‖ = 1 := by
    rw [norm_mul, norm_inv, norm_Gamma_conj, mul_inv_cancel₀ (norm_ne_zero_iff.2 hGw)]
  have hpi : ‖(π : ℂ) ^ (-(1 - s)) * (π : ℂ) ^ s‖ ≤ 1 := by
    rw [norm_mul, show (π : ℂ) = ((π : ℝ) : ℂ) from rfl, norm_cpow_pos π Real.pi_pos,
      norm_cpow_pos π Real.pi_pos, ← Real.rpow_add Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp [hs]; norm_num
  have h4pi : ‖((4 * π : ℝ) : ℂ) ^ (-(1 - s) - m) * ((4 * π : ℝ) : ℂ) ^ (s + m)‖ ≤ 1 := by
    rw [norm_mul, norm_cpow_pos _ (by positivity), norm_cpow_pos _ (by positivity),
      ← Real.rpow_add (by positivity)]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [Real.pi_gt_three])
    simp [hs]; norm_num
  have hsplit : gamM m (1 - s) * invGamM m s =
      ((π : ℂ) ^ (-(1 - s)) * (π : ℂ) ^ s) *
      (((4 * π : ℝ) : ℂ) ^ (-(1 - s) - m) * ((4 * π : ℝ) : ℂ) ^ (s + m)) *
      (Complex.Gamma (1 - s) * (Complex.Gamma s)⁻¹) *
      (Complex.Gamma (1 - s + m) * (Complex.Gamma (s + m))⁻¹) := by
    unfold gamM invGamM; ring
  rw [hsplit, r1, r2, norm_mul, norm_mul, norm_mul]
  have hn1 : ‖starRingEnd ℂ u * (starRingEnd ℂ u + 1) * ((u - 1) * (u - 2)) *
      (Complex.Gamma (starRingEnd ℂ u) * (Complex.Gamma u)⁻¹)‖ ≤ (‖u‖ + 13) ^ 4 := by
    rw [norm_mul, hratio, mul_one, norm_mul, norm_mul, norm_mul]
    have a1 : ‖starRingEnd ℂ u‖ ≤ ‖u‖ + 13 := by rw [Complex.norm_conj]; linarith
    have a2 : ‖starRingEnd ℂ u + 1‖ ≤ ‖u‖ + 13 := by
      have := norm_add_le (starRingEnd ℂ u) 1; rw [Complex.norm_conj, norm_one] at this; linarith
    have a3 : ‖u - 1‖ ≤ ‖u‖ + 13 := by
      have := norm_sub_le u 1; rw [norm_one] at this; linarith
    have a4 : ‖u - 2‖ ≤ ‖u‖ + 13 := by
      have := norm_sub_le u 2; rw [Complex.norm_two] at this; linarith
    calc ‖starRingEnd ℂ u‖ * ‖starRingEnd ℂ u + 1‖ * (‖u - 1‖ * ‖u - 2‖)
        ≤ (‖u‖ + 13) * (‖u‖ + 13) * ((‖u‖ + 13) * (‖u‖ + 13)) := by gcongr
      _ = (‖u‖ + 13) ^ 4 := by ring
  have hn2 : ‖(∏ j ∈ Finset.range 4, (starRingEnd ℂ w + j)) *
      (Complex.Gamma (starRingEnd ℂ w) * (Complex.Gamma w)⁻¹)‖ ≤
        ((m : ℝ) + 1) ^ 4 * (‖u‖ + 13) ^ 4 := by
    rw [norm_mul, hratio2, mul_one]
    have hp1 := norm_prod_le_pow (u := starRingEnd ℂ w) 4
    rw [Complex.norm_conj] at hp1
    have hwu : w = u + ((m : ℂ) - 2) := by rw [hwdef, hu]; ring
    have hwn : ‖w‖ ≤ ‖u‖ + ((m : ℝ) - 2) := by
      rw [hwu]
      refine (norm_add_le _ _).trans ?_
      have : ‖((m : ℂ) - 2)‖ = (m : ℝ) - 2 := by
        rw [show ((m : ℂ) - 2) = (((m : ℝ) - 2 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      rw [this]
    have hb : ‖w‖ + ((4 : ℕ) : ℝ) ≤ ((m : ℝ) + 1) * (‖u‖ + 13) := by
      push_cast; nlinarith [norm_nonneg u]
    calc ‖∏ j ∈ Finset.range 4, (starRingEnd ℂ w + j)‖ ≤ (‖w‖ + ((4 : ℕ) : ℝ)) ^ 4 := hp1
      _ ≤ (((m : ℝ) + 1) * (‖u‖ + 13)) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hb 4
      _ = _ := by rw [mul_pow]
  have hu13 : (1:ℝ) ≤ ‖u‖ + 13 := by linarith [norm_nonneg u]
  calc ‖(π : ℂ) ^ (-(1 - s)) * (π : ℂ) ^ s‖ *
        ‖((4 * π : ℝ) : ℂ) ^ (-(1 - s) - m) * ((4 * π : ℝ) : ℂ) ^ (s + m)‖ * _ * _
      ≤ 1 * 1 * (‖u‖ + 13) ^ 4 * (((m : ℝ) + 1) ^ 4 * (‖u‖ + 13) ^ 4) := by gcongr
    _ = ((m : ℝ) + 1) ^ 4 * ((‖u‖ + 13) ^ 8 * 1) := by ring
    _ ≤ ((m : ℝ) + 1) ^ 4 * ((‖u‖ + 13) ^ 8 * (‖u‖ + 13) ^ 9) := by
        gcongr; exact one_le_pow₀ hu13
    _ = ((m : ℝ) + 1) ^ 4 * (‖s + 2‖ + 13) ^ 17 := by rw [← pow_add]

end RamanujanTau.RankinErrorGeneral

#print axioms RamanujanTau.RankinErrorGeneral.gammaM_ratio_le
