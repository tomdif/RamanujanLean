/-
# Second-order Stirling for the Δ Gamma-ratio

Degree 2 doubles the conductor (`t²`), so the first-order estimate `R_t τ^{−2z} = 1 + O(1/t)` is not
enough (it would cost `τ^{2c}/t ≥ 1`). The `1/t` terms cancel between `±t`:

* `norm_digamma_second`: `‖ψ(s) − log s + 1/(2s)‖ ≤ 6/(Re s + |Im s|)²` for `Re s ≥ 6`;
* `norm_EfD_le`: for `E_t(z) = Σ± [log Γ(6+z±it) − log Γ(6±it)] − 2z log t`,
  `‖E_t(c+iy)‖ ≤ 150 (1+|y|)³/t²` when `|y| ≤ t/4`, `t ≥ 16`.
-/
import RamanujanTau.GoodSecondTerm.AFE
import RamanujanTau.ZetaAFE.GammaBound
import RamanujanTau.CriticalMeanSquareAsymp.Gamma

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.HeckeL RamanujanTau.ZeroCountRvM

lemma norm_add_nat_ge {s : ℂ} (hs : 0 ≤ s.re) (j : ℕ) :
    (s.re + j + |s.im|) / 2 ≤ ‖s + j‖ ∧ s.re + j ≤ ‖s + j‖ := by
  have hn2 : ‖s + j‖ ^ 2 = (s.re + j) ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have h0 : 0 ≤ ‖s + j‖ := norm_nonneg _
  have hj := Nat.cast_nonneg (α := ℝ) j
  constructor
  · refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) h0 ?_
    rw [hn2]; nlinarith [sq_nonneg (s.re + j - |s.im|), sq_abs s.im, abs_nonneg s.im]
  · refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) h0 ?_
    rw [hn2]; nlinarith [sq_nonneg s.im]

lemma ne_zero_add_nat {s : ℂ} (hs : 0 < s.re) (j : ℕ) : s + j ≠ 0 := fun h => by
  have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) j]

lemma norm_succ_ge {s : ℂ} (hs : 0 ≤ s.re) (j : ℕ) : ‖s + j‖ ≤ ‖s + j + 1‖ := by
  have h1 : ‖s + j‖ ^ 2 = (s.re + j) ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have h2 : ‖s + j + 1‖ ^ 2 = (s.re + j + 1) ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (norm_nonneg _) ?_
  rw [h1, h2]; nlinarith [Nat.cast_nonneg (α := ℝ) j]

lemma summable_tele {s : ℂ} (hs : 0 < s.re) :
    Summable fun j : ℕ => 1 / ((s + j) * (s + j + 1)) := by
  refine Summable.of_norm_bounded (g := fun j : ℕ => 1 / (s.re + j) ^ 2)
    (summable_inv_sq_add hs) (fun j => ?_)
  have h1 := (norm_add_nat_ge hs.le j).2
  have h2 := h1.trans (norm_succ_ge hs.le j)
  have hp : 0 < s.re + j := by linarith [Nat.cast_nonneg (α := ℝ) j]
  rw [norm_div, norm_one, norm_mul, one_div_le_one_div (mul_pos (hp.trans_le h1) (hp.trans_le h2))
    (by positivity), sq]
  exact mul_le_mul h1 h2 hp.le (norm_nonneg _)

lemma hasSum_tele {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun j : ℕ => 1 / ((s + j) * (s + j + 1))) (1 / s) := by
  have hpart : ∀ N : ℕ, ∑ j ∈ Finset.range N, 1 / ((s + j) * (s + j + 1)) = 1 / s - 1 / (s + N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 := ne_zero_add_nat hs N
      have h2 : s + ((N : ℂ) + 1) ≠ 0 := by
        have := ne_zero_add_nat hs (N + 1); push_cast at this; exact this
      have h3 : s + (N : ℂ) + 1 ≠ 0 := by rwa [add_assoc]
      have h0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
      push_cast
      field_simp
      ring
  have h0 : Tendsto (fun N : ℕ => 1 / (s + N)) atTop (𝓝 0) := by
    have hb : Tendsto (fun N : ℕ => 1 / (s.re + N)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
    refine squeeze_zero_norm (fun N => ?_) hb
    have hp : 0 < s.re + N := by linarith [Nat.cast_nonneg (α := ℝ) N]
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hp (norm_add_nat_ge hs.le N).2
  have hlim : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, 1 / ((s + j) * (s + j + 1))) atTop
      (𝓝 (1 / s)) := by
    simp_rw [hpart]; simpa using h0.const_sub (1 / s)
  exact (summable_tele hs).hasSum_iff_tendsto_nat.mpr hlim

lemma logTaylor_three (w : ℂ) : logTaylor 3 w = w - w ^ 2 / 2 := by
  simp [logTaylor, Finset.sum_range_succ]; ring

/-- `‖ψ(s) − log s + 1/(2s)‖ ≤ 6/(Re s + |Im s|)²` for `Re s ≥ 6`. -/
theorem norm_digamma_second {s : ℂ} (hs : 6 ≤ s.re) :
    ‖digamma s - log s + 1 / (2 * s)‖ ≤ 10 / (s.re + |s.im|) ^ 2 := by
  have hs0 : 0 < s.re := by linarith
  set a : ℝ := s.re + |s.im| with ha
  have ha6 : 6 ≤ a := by have := abs_nonneg s.im; linarith
  have hsum1 := summable_et hs0
  have hsum2 := (summable_tele hs0).mul_left (1 / 2)
  have hrepr : digamma s - log s + 1 / (2 * s) =
      ∑' j : ℕ, (et s j + 1 / 2 * (1 / ((s + j) * (s + j + 1)))) := by
    rw [hsum1.tsum_add hsum2, tsum_mul_left, (hasSum_tele hs0).tsum_eq, digamma_eq_log_add hs0]
    have : s ≠ 0 := Complex.ne_zero_of_re_pos hs0
    field_simp; ring
  rw [hrepr]
  have hb : ∀ j : ℕ, ‖et s j + 1 / 2 * (1 / ((s + j) * (s + j + 1)))‖ ≤ 8 * (1 / (a + j) ^ 3) := by
    intro j
    have hne := ne_zero_add_nat hs0 j
    have hne1 : s + j + 1 ≠ 0 := by
      have := ne_zero_add_nat hs0 (j + 1); push_cast at this; rwa [← add_assoc] at this
    set w : ℂ := 1 / (s + j) with hw
    have hge := norm_add_nat_ge hs0.le j
    have hj := Nat.cast_nonneg (α := ℝ) j
    have hwn : ‖w‖ ≤ 1 / 6 := by
      rw [hw, norm_div, norm_one]; exact one_div_le_one_div_of_le (by norm_num) (by linarith [hge.2])
    have hwn2 : ‖w‖ ≤ 2 / (a + j) := by
      rw [hw, norm_div, norm_one, div_le_div_iff₀ (by
        exact lt_of_lt_of_le (by linarith) hge.2) (by linarith)]
      have := hge.1
      linarith [ha]
    have hr := Complex.norm_log_sub_logTaylor_le 2 (z := w) (by linarith)
    rw [logTaylor_three] at hr
    have hr' : ‖log (1 + w) - (w - w ^ 2 / 2)‖ ≤ ‖w‖ ^ 3 / 2 := by
      refine hr.trans ?_
      have h1 : (1 - ‖w‖)⁻¹ ≤ 6 / 5 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      push_cast
      calc ‖w‖ ^ (2 + 1) * (1 - ‖w‖)⁻¹ / (2 + 1) ≤ ‖w‖ ^ 3 * (6 / 5) / 3 := by
            norm_num; gcongr
        _ ≤ ‖w‖ ^ 3 / 2 := by have := pow_nonneg (norm_nonneg w) 3; nlinarith
    have hid : et s j + 1 / 2 * (1 / ((s + j) * (s + j + 1))) =
        (log (1 + w) - (w - w ^ 2 / 2)) - w ^ 2 / (2 * (s + j + 1)) := by
      unfold et; rw [hw]; field_simp; ring
    rw [hid]
    have h2 : ‖w ^ 2 / (2 * (s + j + 1))‖ ≤ ‖w‖ ^ 3 / 2 := by
      rw [norm_div, norm_mul, norm_pow, show ‖(2 : ℂ)‖ = 2 by simp]
      have hsj : ‖s + j‖ ≤ ‖s + j + 1‖ := norm_succ_ge hs0.le j
      have hpos : 0 < ‖s + j‖ := norm_pos_iff.mpr hne
      have hw' : ‖w‖ = 1 / ‖s + j‖ := by rw [hw, norm_div, norm_one]
      rw [div_le_div_iff₀ (by have := norm_pos_iff.mpr hne1; positivity) (by norm_num), hw']
      rw [one_div, inv_pow, inv_pow]
      have : (‖s + j‖ ^ 3)⁻¹ * (2 * ‖s + j + 1‖) ≥ (‖s + j‖ ^ 3)⁻¹ * (2 * ‖s + j‖) := by gcongr
      have e : (‖s + j‖ ^ 3)⁻¹ * (2 * ‖s + j‖) = (‖s + j‖ ^ 2)⁻¹ * 2 := by field_simp
      linarith
    have hw3 : ‖w‖ ^ 3 ≤ 8 / (a + j) ^ 3 := by
      calc ‖w‖ ^ 3 ≤ (2 / (a + j)) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hwn2 3
        _ = 8 / (a + j) ^ 3 := by rw [div_pow]; norm_num
    calc ‖(log (1 + w) - (w - w ^ 2 / 2)) - w ^ 2 / (2 * (s + j + 1))‖
        ≤ ‖w‖ ^ 3 / 2 + ‖w‖ ^ 3 / 2 := (norm_sub_le _ _).trans (add_le_add hr' h2)
      _ ≤ 8 / (a + j) ^ 3 := by linarith
      _ = 8 * (1 / (a + j) ^ 3) := by ring
  have ha1 : 1 < a := by linarith
  obtain ⟨hsq, hsqle⟩ := tsum_inv_sq_le ha1
  have hcmp : ∀ j : ℕ, 8 * (1 / (a + j) ^ 3) ≤ 8 / a * (1 / (a + j) ^ 2) := by
    intro j
    have hj := Nat.cast_nonneg (α := ℝ) j
    have hp : 0 < a + j := by linarith
    rw [show (a + j) ^ 3 = (a + j) * (a + j) ^ 2 by ring]
    rw [mul_one_div, mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a + j)]
  have hs3 : Summable fun j : ℕ => 8 * (1 / (a + j) ^ 3) :=
    Summable.of_nonneg_of_le (fun j => by have := Nat.cast_nonneg (α := ℝ) j; positivity) hcmp
      (hsq.summable.mul_left _)
  calc ‖∑' j : ℕ, (et s j + 1 / 2 * (1 / ((s + j) * (s + j + 1))))‖
      ≤ ∑' j : ℕ, 8 * (1 / (a + j) ^ 3) := tsum_of_norm_bounded hs3.hasSum hb
    _ ≤ ∑' j : ℕ, 8 / a * (1 / (a + j) ^ 2) := hs3.tsum_le_tsum hcmp (hsq.summable.mul_left _)
    _ = 8 / a * ∑' j : ℕ, 1 / (a + j) ^ 2 := tsum_mul_left
    _ ≤ 8 / a * (1 / (a - 1)) := by gcongr
    _ ≤ 10 / a ^ 2 := by
        rw [div_mul_div_comm, div_le_div_iff₀ (by nlinarith) (by positivity)]; nlinarith

end RamanujanTau.GoodSecondTerm
