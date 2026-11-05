/-
# Two analytic inputs for the lower bound

* `fe_lower`: for `(k−1)/2 ≤ σ ≤ k/2`, the functional equation and uniform Stirling give
  `‖L(f, σ+it)‖ ≥ c (1+|t|)^{k−2σ} ‖L(f, k−σ−it)‖` with `c > 0` independent of `σ, t`.
* `tail_small`: if `m` is the least index with `a_f(m) ≠ 0`, then on a far-right line
  `Re s = c`, `‖L(f,s) m^s − a_f(m)‖ ≤ |a_f(m)|/2` uniformly in `Im s`.
-/
import RamanujanTau.TauOmegaPartial.Fourier
import RamanujanTau.RankinLandau.GammaUnif

set_option autoImplicit false

namespace RamanujanTau.TauOmegaPartial

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.HeckeConvexGeneral
open scoped MatrixGroups Real

variable {k : ℕ}

/-- **Functional-equation lower bound**, uniform for `(k−1)/2 ≤ σ ≤ k/2`. -/
theorem fe_lower (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 3 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ σ t : ℝ, ((k : ℝ) - 1) / 2 ≤ σ → σ ≤ (k : ℝ) / 2 →
      c * (1 + |t|) ^ ((k : ℝ) - 2 * σ) * ‖fL f ((k : ℂ) - ((σ : ℂ) + t * I))‖ ≤
        ‖fL f ((σ : ℂ) + t * I)‖ := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨C, hC0, hC⟩ := RamanujanTau.RankinLandau.norm_Gamma_ratio_unif' (R := k) (by linarith)
  refine ⟨1 / (2 * π * C), by positivity, fun σ t h1 h2 => ?_⟩
  set s : ℂ := (σ : ℂ) + t * I with hs
  set w : ℂ := (k : ℂ) - s with hw
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hwre : w.re = k - σ := by simp [hw, hs]
  have hwim : w.im = -t := by simp [hw, hs]
  have hΓ := hC s w (by rw [hsre]; linarith) (by rw [hsre]; linarith) (by rw [hwre]; linarith)
    (by rw [hwre]; linarith) (by rw [hsim, hwim, abs_neg])
  rw [hsre, hwre, hwim, abs_neg] at hΓ
  have hs0 : ∀ n : ℕ, s ≠ -n := by
    intro n h; have := congrArg Complex.re h; rw [hsre] at this; simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hw0 : ∀ n : ℕ, (k : ℂ) - s ≠ -n := by
    intro n h; have := congrArg Complex.re h; rw [← hw, hwre] at this; simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hfe := fL_functional_equation f (by omega) hs0 hw0
  rw [← hw] at hfe
  have hn := congrArg norm hfe
  simp only [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, norm_two_pi_cpow'] at hn
  have e1 : (-w).re = -(k - σ) := by rw [Complex.neg_re, hwre]
  have e2 : (-s).re = -σ := by rw [Complex.neg_re, hsre]
  rw [e1, e2] at hn
  have hGw : 0 < ‖Complex.Gamma w‖ := norm_pos_iff.2 (Complex.Gamma_ne_zero_of_re_pos
    (by rw [hwre]; linarith))
  set P : ℝ := 1 + |t| with hP
  have hP1 : 1 ≤ P := by rw [hP]; linarith [abs_nonneg t]
  have hP0 : 0 < P := by linarith
  set e : ℝ := (k : ℝ) - 2 * σ with he
  have he0 : 0 ≤ e := by rw [he]; linarith
  have he1 : e ≤ 1 := by rw [he]; linarith
  have hpp : P ^ e * P ^ (σ - (k - σ)) = 1 := by
    rw [← Real.rpow_add hP0]; rw [show e + (σ - (k - σ)) = 0 by rw [he]; ring, Real.rpow_zero]
  have h2pi : (2 * π) ^ (-(k - σ)) = (2 * π) ^ (-σ) * (2 * π) ^ (-e) := by
    rw [← Real.rpow_add (by positivity)]; congr 1; rw [he]; ring
  have hpe : (2 * π) ^ e ≤ 2 * π := by
    calc (2 * π) ^ e ≤ (2 * π) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) he1
      _ = 2 * π := Real.rpow_one _
  have hpe0 : 0 < (2 * π) ^ e := by positivity
  have hpm : (2 * π) ^ (-e) * (2 * π) ^ e = 1 := by
    rw [← Real.rpow_add (by positivity)]; simp
  -- ‖L(w)‖ ‖Γ w‖ (2π)^{-σ}(2π)^{-e} = (2π)^{-σ} ‖Γ s‖ ‖L s‖ ≤ (2π)^{-σ} C P^{2σ-k} ‖Γ w‖ ‖L s‖
  have hLw : ‖fL f w‖ * (2 * π) ^ (-e) ≤ C * P ^ (σ - (k - σ)) * ‖fL f s‖ := by
    have hsig : 0 < (2 * π) ^ (-σ) := by positivity
    have key : (2 * π) ^ (-σ) * ‖Complex.Gamma w‖ * (‖fL f w‖ * (2 * π) ^ (-e)) ≤
        (2 * π) ^ (-σ) * ‖Complex.Gamma w‖ * (C * P ^ (σ - (k - σ)) * ‖fL f s‖) := by
      calc (2 * π) ^ (-σ) * ‖Complex.Gamma w‖ * (‖fL f w‖ * (2 * π) ^ (-e))
          = (2 * π) ^ (-(k - σ)) * ‖Complex.Gamma w‖ * ‖fL f w‖ := by rw [h2pi]; ring
        _ = (2 * π) ^ (-σ) * ‖Complex.Gamma s‖ * ‖fL f s‖ := hn
        _ ≤ (2 * π) ^ (-σ) * (C * P ^ (σ - (k - σ)) * ‖Complex.Gamma w‖) * ‖fL f s‖ := by
            gcongr
        _ = _ := by ring
    exact le_of_mul_le_mul_left key (by positivity)
  have hfin : 1 / (2 * π * C) * P ^ e * ‖fL f w‖ ≤ ‖fL f s‖ := by
    have h3 : ‖fL f w‖ ≤ (2 * π) ^ e * (C * P ^ (σ - (k - σ)) * ‖fL f s‖) := by
      have := mul_le_mul_of_nonneg_left hLw hpe0.le
      calc ‖fL f w‖ = (2 * π) ^ e * (‖fL f w‖ * (2 * π) ^ (-e)) := by
            rw [mul_comm ((2 * π) ^ e), mul_assoc, hpm, mul_one]
        _ ≤ _ := this
    have h4 : P ^ e * ‖fL f w‖ ≤ (2 * π) ^ e * C * ‖fL f s‖ := by
      calc P ^ e * ‖fL f w‖ ≤ P ^ e * ((2 * π) ^ e * (C * P ^ (σ - (k - σ)) * ‖fL f s‖)) := by
            gcongr
        _ = (2 * π) ^ e * C * ‖fL f s‖ * (P ^ e * P ^ (σ - (k - σ))) := by ring
        _ = _ := by rw [hpp, mul_one]
    have h5 : (2 * π) ^ e * C * ‖fL f s‖ ≤ 2 * π * C * ‖fL f s‖ := by gcongr
    rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (fL f s)]
  exact hfin

lemma rpow_aux (a : ℝ) {n m : ℝ} (hn : 0 < n) (hm : 0 < m) (c : ℝ) (N : ℕ) :
    a / n ^ (c + N) * m ^ (c + N) = a / n ^ c * m ^ c * (m / n) ^ N := by
  rw [Real.rpow_add hn, Real.rpow_add hm, Real.rpow_natCast, Real.rpow_natCast, div_pow]
  have h1 : 0 < n ^ c := Real.rpow_pos_of_pos hn c
  have h2 : 0 < n ^ N := pow_pos hn N
  field_simp

/-- **The leading coefficient dominates on a far-right line.** -/
theorem tail_small (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {m : ℕ} (hm : 1 ≤ m)
    (hlow : ∀ n < m, coef f n = 0) (hm0 : coef f m ≠ 0) :
    ∃ c : ℝ, ((k : ℝ) + 1) / 2 + 1 ≤ c ∧ ∀ y : ℝ,
      ‖fL f ((c : ℂ) + y * I) * (m : ℂ) ^ ((c : ℂ) + y * I) - coef f m‖ ≤ ‖coef f m‖ / 2 := by
  set c1 : ℝ := ((k : ℝ) + 1) / 2 + 1 with hc1
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hsum1 := summable_norm_coef_div_rpow f hk (σ := c1) (by rw [hc1]; linarith)
  set S1 : ℝ := ∑' n : ℕ, ‖coef f n‖ / (n : ℝ) ^ c1 with hS1
  have hS10 : 0 ≤ S1 := tsum_nonneg fun n => by positivity
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set q : ℝ := (m : ℝ) / (m + 1) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one (by linarith)]; linarith
  set M : ℝ := (m : ℝ) ^ c1 * S1 + 1 with hM
  have hM0 : 0 < M := by positivity
  have ham : 0 < ‖coef f m‖ := norm_pos_iff.2 hm0
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < ‖coef f m‖ / 2 / M by positivity) hq1
  refine ⟨c1 + N, by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)], fun y => ?_⟩
  set s : ℂ := ((c1 + N : ℝ) : ℂ) + y * I with hs
  have hsre : s.re = c1 + N := by simp [hs]
  have hLS : LSeriesSummable (coef f) s := LSeriesSummable_coef f hk (by rw [hsre]; linarith
    [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
  have hmpos : 0 < m := by omega
  have hnm : ‖(m : ℂ) ^ s‖ = (m : ℝ) ^ (c1 + N) := by
    rw [Complex.norm_natCast_cpow_of_pos hmpos, hsre]
  -- pointwise bound of the terms
  set T : ℕ → ℂ := fun n => LSeries.term (coef f) s n * (m : ℂ) ^ s with hT
  have hTsum : Summable T := hLS.mul_right _
  have hTm : T m = coef f m := by
    simp only [hT, LSeries.term, if_neg (show m ≠ 0 by omega)]
    have : (m : ℂ) ^ s ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h (by exact_mod_cast hmpos.ne')
    field_simp
  set B : ℕ → ℝ := fun n => q ^ N * (m : ℝ) ^ c1 * (‖coef f n‖ / (n : ℝ) ^ c1) with hB
  have hBsum : Summable B := hsum1.mul_left _
  have hpt : ∀ n, ‖(if n = m then 0 else T n)‖ ≤ B n := by
    intro n
    have hB0 : 0 ≤ B n := by positivity
    by_cases h : n = m
    · rw [if_pos h, norm_zero]; exact hB0
    rw [if_neg h]
    rcases Nat.lt_or_gt_of_ne h with hlt | hgt
    · rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp [hT, LSeries.term]; exact hB0
      · simp [hT, LSeries.term, hlow n hlt]; exact hB0
    · have hn0 : 0 < n := by omega
      have hnR : (m : ℝ) + 1 ≤ n := by exact_mod_cast hgt
      have hnpos : (0 : ℝ) < n := by linarith
      simp only [hT, LSeries.term, if_neg (show n ≠ 0 by omega), norm_mul, norm_div,
        Complex.norm_natCast_cpow_of_pos hn0, hsre, hnm]
      have hr : (m : ℝ) / n ≤ q := by
        rw [hq, div_le_div_iff₀ hnpos (by linarith)]; nlinarith
      have hmn0 : 0 ≤ (m : ℝ) / n := by positivity
      have e1 : ‖coef f n‖ / (n : ℝ) ^ (c1 + N) * (m : ℝ) ^ (c1 + N) =
          ‖coef f n‖ / (n : ℝ) ^ c1 * (m : ℝ) ^ c1 * ((m : ℝ) / n) ^ N := by
        exact rpow_aux _ hnpos (by linarith) c1 N
      rw [e1, hB]
      have : ((m : ℝ) / n) ^ N ≤ q ^ N := pow_le_pow_left₀ hmn0 hr N
      have h0 : 0 ≤ ‖coef f n‖ / (n : ℝ) ^ c1 * (m : ℝ) ^ c1 := by positivity
      calc ‖coef f n‖ / (n : ℝ) ^ c1 * (m : ℝ) ^ c1 * ((m : ℝ) / n) ^ N
          ≤ ‖coef f n‖ / (n : ℝ) ^ c1 * (m : ℝ) ^ c1 * q ^ N := by gcongr
        _ = _ := by ring
  have hite : Summable (fun n => ‖(if n = m then 0 else T n)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hBsum
  have hsplit : fL f s * (m : ℂ) ^ s - coef f m = ∑' n, (if n = m then 0 else T n) := by
    rw [fL_eq_LSeries f hk (by rw [hsre]; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]), LSeries,
      ← tsum_mul_right, hTsum.tsum_eq_add_tsum_ite m, hTm]
    ring
  have hs' : ((c1 + N : ℝ) : ℂ) + y * I = ((c1 + N : ℝ) : ℂ) + y * I := rfl
  have hcast : ((c1 + (N : ℝ) : ℝ) : ℂ) = ((c1 : ℂ) + (N : ℂ)) := by push_cast; ring
  show ‖fL f (((c1 + N : ℝ) : ℂ) + y * I) * (m : ℂ) ^ (((c1 + N : ℝ) : ℂ) + y * I) - coef f m‖ ≤ _
  rw [← hs, hsplit]
  calc ‖∑' n, (if n = m then 0 else T n)‖ ≤ ∑' n, ‖(if n = m then 0 else T n)‖ :=
        norm_tsum_le_tsum_norm hite
    _ ≤ ∑' n, B n := hite.tsum_le_tsum hpt hBsum
    _ = q ^ N * (m : ℝ) ^ c1 * S1 := by rw [hB, tsum_mul_left]
    _ ≤ q ^ N * M := by rw [hM]; nlinarith [pow_nonneg hq0 N]
    _ ≤ ‖coef f m‖ / 2 / M * M := by gcongr
    _ = ‖coef f m‖ / 2 := by field_simp

end RamanujanTau.TauOmegaPartial
