/-
# Phragmén–Lindelöf for the Rankin–Selberg L-function, and the power-saving error term

See `Convexity.lean` for the statement of `RSData`. Main results:

* `gamma_ratio_le`: on `Re s = −3/2`, `‖γ(1−s)/γ(s)‖ ≤ 2⁹ (‖s+2‖ + 13)^{17}`;
* `fPL_bound`: `‖(s(s−1)Λ₀(s) + κ)/(γ(s)(s+3)¹⁹)‖ ≤ C` on `−3/2 ≤ Re s ≤ 5/2`;
* `power_saving_of_RSData`: `|∑_{n≤N} aₙ − c₀N| ≤ C N^{1−2^{−22}}`.
-/
import RamanujanTau.RankinError.Convexity

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Complex Real MeasureTheory Set Filter Topology

lemma norm_le_norm_of_sq {z w : ℂ} (h : Complex.normSq z ≤ Complex.normSq w) : ‖z‖ ≤ ‖w‖ := by
  have h1 : ‖z‖ ^ 2 ≤ ‖w‖ ^ 2 := by rw [Complex.sq_norm, Complex.sq_norm]; exact h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

lemma norm_le_norm_add_three {s : ℂ} (hs : -3 / 2 ≤ s.re) : ‖s‖ ≤ ‖s + 3‖ := by
  apply norm_le_norm_of_sq; simp [Complex.normSq_apply]; nlinarith

lemma norm_sub_one_le_norm_add_three {s : ℂ} (hs : -1 ≤ s.re) : ‖s - 1‖ ≤ ‖s + 3‖ := by
  apply norm_le_norm_of_sq; simp [Complex.normSq_apply]; nlinarith

lemma one_le_norm_add_three {s : ℂ} (hs : -2 ≤ s.re) : 1 ≤ ‖s + 3‖ := by
  have := Complex.abs_re_le_norm (s + 3)
  simp at this
  have : |s.re + 3| = s.re + 3 := abs_of_nonneg (by linarith)
  linarith

/-- The `Γ`-ratio on the left edge `Re s = −3/2`, with `u = s + 2` (so `Re u = 1/2`). -/
lemma gamma_ratio_le {s : ℂ} (hs : s.re = -3 / 2) :
    ‖gam (1 - s) * invGam s‖ ≤ 2 ^ 9 * (‖s + 2‖ + 13) ^ 17 := by
  set u : ℂ := s + 2 with hu
  have hure : u.re = 1 / 2 := by rw [hu]; simp [hs]; norm_num
  have hu0 : 0 < u.re := by rw [hure]; norm_num
  have hcu0 : 0 < (starRingEnd ℂ u).re := by simp [hure]
  have hw : 1 - s = starRingEnd ℂ u + 2 := by
    apply Complex.ext <;> simp [hu, hs] <;> norm_num
  have hs' : s = u - 2 := by rw [hu]; ring
  have hGu := Complex.Gamma_ne_zero_of_re_pos hu0
  -- `Γ(u) = (u-1)(u-2) Γ(u-2)`
  have hu1 : u - 1 ≠ 0 := by intro h; have := congrArg re h; simp [hure] at this; norm_num at this
  have hu2 : u - 2 ≠ 0 := by intro h; have := congrArg re h; simp [hure] at this; norm_num at this
  have hGs : Complex.Gamma u = (u - 1) * (u - 2) * Complex.Gamma (u - 2) := by
    have e1 := Complex.Gamma_add_one (u - 1) hu1
    have e2 := Complex.Gamma_add_one (u - 2) hu2
    rw [sub_add_cancel] at e1
    rw [show u - 2 + 1 = u - 1 by ring] at e2
    rw [e1, e2]; ring
  have hGs0 : Complex.Gamma (u - 2) ≠ 0 := by
    intro h; rw [h, mul_zero] at hGs; exact hGu hGs
  -- the two ratios
  have r1 : Complex.Gamma (1 - s) * (Complex.Gamma s)⁻¹ =
      (starRingEnd ℂ u) * (starRingEnd ℂ u + 1) * ((u - 1) * (u - 2)) *
        (Complex.Gamma (starRingEnd ℂ u) * (Complex.Gamma u)⁻¹) := by
    have h2 := Gamma_add_nat hcu0 2
    push_cast at h2
    rw [hw, hs', h2, hGs]
    simp [Finset.prod_range_succ]
    field_simp
  have r2 : Complex.Gamma (1 - s + 11) * (Complex.Gamma (s + 11))⁻¹ =
      (∏ j ∈ Finset.range 13, (starRingEnd ℂ u + j)) * (∏ j ∈ Finset.range 9, (u + j))⁻¹ *
        (Complex.Gamma (starRingEnd ℂ u) * (Complex.Gamma u)⁻¹) := by
    have e1 : 1 - s + 11 = starRingEnd ℂ u + (13 : ℕ) := by rw [hw]; push_cast; ring
    have e2 : s + 11 = u + (9 : ℕ) := by rw [hs']; push_cast; ring
    rw [e1, e2, Gamma_add_nat hcu0 13, Gamma_add_nat hu0 9]
    have hp : ∏ j ∈ Finset.range 9, (u + j) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]; intro j _ h; have := congrArg re h; simp [hure] at this
      have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith
    field_simp
  have hratio : ‖Complex.Gamma (starRingEnd ℂ u) * (Complex.Gamma u)⁻¹‖ = 1 := by
    rw [norm_mul, norm_inv, norm_Gamma_conj, mul_inv_cancel₀ (norm_ne_zero_iff.2 hGu)]
  -- the exponential factors
  have hpi : ‖(π : ℂ) ^ (-(1 - s)) * (π : ℂ) ^ s‖ ≤ 1 := by
    rw [norm_mul, show (π : ℂ) = ((π : ℝ) : ℂ) from rfl, norm_cpow_pos π Real.pi_pos,
      norm_cpow_pos π Real.pi_pos, ← Real.rpow_add Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp [hs]; norm_num
  have h4pi : ‖((4 * π : ℝ) : ℂ) ^ (-(1 - s) - 11) * ((4 * π : ℝ) : ℂ) ^ (s + 11)‖ ≤ 1 := by
    rw [norm_mul, norm_cpow_pos _ (by positivity), norm_cpow_pos _ (by positivity),
      ← Real.rpow_add (by positivity)]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [Real.pi_gt_three])
    simp [hs]; norm_num
  have hsplit : gam (1 - s) * invGam s =
      ((π : ℂ) ^ (-(1 - s)) * (π : ℂ) ^ s) *
      (((4 * π : ℝ) : ℂ) ^ (-(1 - s) - 11) * ((4 * π : ℝ) : ℂ) ^ (s + 11)) *
      (Complex.Gamma (1 - s) * (Complex.Gamma s)⁻¹) *
      (Complex.Gamma (1 - s + 11) * (Complex.Gamma (s + 11))⁻¹) := by
    unfold gam invGam; ring
  rw [hsplit, r1, r2, norm_mul, norm_mul, norm_mul]
  -- bound the polynomial pieces
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
  have hn2 : ‖(∏ j ∈ Finset.range 13, (starRingEnd ℂ u + j)) * (∏ j ∈ Finset.range 9, (u + j))⁻¹ *
      (Complex.Gamma (starRingEnd ℂ u) * (Complex.Gamma u)⁻¹)‖ ≤ 2 ^ 9 * (‖u‖ + 13) ^ 13 := by
    rw [norm_mul, hratio, mul_one, norm_mul, norm_inv]
    have hp1 := norm_prod_le_pow (u := starRingEnd ℂ u) 13
    rw [Complex.norm_conj] at hp1
    have hp2 : (1 / 2 : ℝ) ^ 9 ≤ ‖∏ j ∈ Finset.range 9, (u + j)‖ := by
      rw [norm_prod]
      have : (1 / 2 : ℝ) ^ 9 = ∏ _j ∈ Finset.range 9, (1 / 2 : ℝ) := by
        rw [Finset.prod_const, Finset.card_range]
      rw [this]
      apply Finset.prod_le_prod (fun _ _ => by norm_num)
      intro j _
      have := Complex.abs_re_le_norm (u + j)
      simp [hure] at this
      have : (0:ℝ) ≤ j := Nat.cast_nonneg j
      rw [abs_of_nonneg (by linarith)] at *; linarith
    have hp2' : ‖∏ j ∈ Finset.range 9, (u + j)‖⁻¹ ≤ 2 ^ 9 := by
      have h0 : (0:ℝ) < (1 / 2) ^ 9 := by norm_num
      calc ‖∏ j ∈ Finset.range 9, (u + j)‖⁻¹ ≤ ((1 / 2 : ℝ) ^ 9)⁻¹ := inv_anti₀ h0 hp2
        _ = 2 ^ 9 := by norm_num
    calc ‖∏ j ∈ Finset.range 13, (starRingEnd ℂ u + j)‖ * ‖∏ j ∈ Finset.range 9, (u + j)‖⁻¹
        ≤ (‖u‖ + 13) ^ 13 * 2 ^ 9 := by
          apply mul_le_mul _ hp2' (by positivity) (by positivity)
          exact hp1.trans (by push_cast; rfl)
      _ = 2 ^ 9 * (‖u‖ + 13) ^ 13 := by ring
  have hu13 : (1:ℝ) ≤ ‖u‖ + 13 := by linarith [norm_nonneg u]
  calc ‖(π : ℂ) ^ (-(1 - s)) * (π : ℂ) ^ s‖ *
        ‖((4 * π : ℝ) : ℂ) ^ (-(1 - s) - 11) * ((4 * π : ℝ) : ℂ) ^ (s + 11)‖ * _ * _
      ≤ 1 * 1 * (‖u‖ + 13) ^ 4 * (2 ^ 9 * (‖u‖ + 13) ^ 13) := by gcongr
    _ = 2 ^ 9 * (‖u‖ + 13) ^ 17 := by ring

end RamanujanTau.RankinError
