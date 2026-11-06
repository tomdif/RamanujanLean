/-
# The averaged off-diagonal pair term and its bounds

`zz T H p = coefD p · Ptil(Λ_p, λ_p, T, H)` for `p.1 ≠ p.2` (`Λ = log MN`, `λ = log(N/M)`), the average
over `u ∈ [T,T+H]` of `∫_{16}^u b_p`. `coefD p = λ(M)λ(N)e^{−Λ/2}` (`coefD_eq_lam`).

`norm_zz_le` (`M < N`, `h = N − M`, `D = min(1, e^{−2(Λ − 2 log((T+H)/2π))})`):

    ‖zz‖ ≤ |λ(M)λ(N)| e^{−Λ/2} [c₁₆ e^{−6Λ} N/h + (N/h)² (7Kφ e^{−Λ/2} D + 3 K_W D / H)].
-/
import RamanujanTau.GoodSecondTerm2.SCSAbel

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm2

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.SubconvexityCond

lemma lam_succ_eq (m : ℕ) : lam (m + 1) = ((tau (m + 1) : ℤ) : ℝ) * Real.exp (-(11 / 2 * lg m)) := by
  unfold lam lg
  rw [Real.rpow_def_of_pos (by positivity)]
  push_cast; ring_nf

lemma coefD_eq_lam (p : ℕ × ℕ) :
    coefD p = lam (p.1 + 1) * lam (p.2 + 1) * Real.exp (-((lg p.1 + lg p.2) / 2)) := by
  unfold coefD
  rw [lam_succ_eq, lam_succ_eq]
  have : Real.exp (-(6 * (lg p.1 + lg p.2))) =
      Real.exp (-(11 / 2 * lg p.1)) * Real.exp (-(11 / 2 * lg p.2)) * Real.exp (-((lg p.1 + lg p.2) / 2)) := by
    simp only [← Real.exp_add]; congr 1; ring
  rw [this]; ring

/-- The averaged pair term. -/
noncomputable def zz (T H : ℝ) (p : ℕ × ℕ) : ℂ :=
  if p.1 = p.2 then 0 else (coefD p : ℂ) * Ptil (lg p.1 + lg p.2) (lg p.2 - lg p.1) T H

/-- `D = min(1, e^{−2(Λ − 2 log(T'/2π))})`. -/
noncomputable def Dfac (Λ T' : ℝ) : ℝ := min 1 (Real.exp (-(2 * (Λ - 2 * ellT T'))))

lemma Dfac_nonneg (Λ T' : ℝ) : 0 ≤ Dfac Λ T' := le_min zero_le_one (Real.exp_pos _).le

noncomputable def KW : ℝ := max 2 (Real.exp (2 ^ 2) / (2 * Real.sqrt Real.pi))

lemma KW_pos : 0 < KW := lt_max_of_lt_left (by norm_num)

lemma WV_le_D (Λ T' : ℝ) : WV Λ T' ≤ KW * Dfac Λ T' := by
  unfold WV Dfac
  have h1 := V_le_two (Λ - 2 * ellT T')
  have h2 := V_le_exp_k (k := 2) (by norm_num) (Λ - 2 * ellT T')
  rcases le_total 1 (Real.exp (-(2 * (Λ - 2 * ellT T')))) with h | h
  · rw [min_eq_left h, mul_one]; exact h1.trans (le_max_left _ _)
  · rw [min_eq_right h]
    refine h2.trans ?_
    gcongr; exact le_max_right _ _

noncomputable def c16 : ℝ := Real.exp (6 ^ 2) / (6 * Real.sqrt Real.pi) * Real.exp (12 * ellT 16)

lemma c16_pos : 0 < c16 := by
  unfold c16; have := Real.sqrt_pos.mpr Real.pi_pos; positivity

lemma WV16_le (Λ : ℝ) : WV Λ 16 ≤ c16 * Real.exp (-(6 * Λ)) := by
  unfold WV c16
  refine (V_le_exp_k (k := 6) (by norm_num) _).trans (le_of_eq ?_)
  rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- **Pair bound.** -/
theorem norm_zz_le {T H : ℝ} (hT : 16 ≤ T) (hH : 0 < H) {m n : ℕ} (hmn : m < n) :
    ‖zz T H (m, n)‖ ≤ |lam (m + 1)| * |lam (n + 1)| * Real.exp (-((lg m + lg n) / 2)) *
      (c16 * Real.exp (-(6 * (lg m + lg n))) * (((n : ℝ) + 1) / ((n : ℝ) - m)) +
        (((n : ℝ) + 1) / ((n : ℝ) - m)) ^ 2 *
          (7 * Kphi * Real.exp (-((lg m + lg n) / 2)) * Dfac (lg m + lg n) (T + H) +
            3 * KW * Dfac (lg m + lg n) (T + H) / H)) := by
  have hne : m ≠ n := hmn.ne
  unfold zz
  simp only [hne, if_false]
  set Λ := lg m + lg n with hΛ
  set lam' := lg n - lg m with hlam
  have hlam0 : lam' ≠ 0 := by
    have : lg m < lg n := by
      unfold lg; exact Real.log_lt_log (by positivity) (by exact_mod_cast (by omega : m + 1 < n + 1))
    rw [hlam]; linarith
  have hinv := inv_abs_lg_sub_le hmn
  have hlpos : 0 < |lam'| := abs_pos.mpr hlam0
  have hΦ : ∀ t ∈ Icc 16 (T + H), phiD Λ t ≤ Kphi * Real.exp (-(Λ / 2)) * Dfac Λ (T + H) :=
    fun t ht => phiD_le_min Λ (by linarith [ht.1]) ht.2
  have hP := norm_Ptil_le (Λ := Λ) (lam := lam') hT hH hlam0 hΦ
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, coefD_eq_lam, abs_mul, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  simp only
  rw [← hΛ]
  have hq : 1 / |lam'| ≤ ((n : ℝ) + 1) / ((n : ℝ) - m) := hinv
  have hq0 : 0 ≤ ((n : ℝ) + 1) / ((n : ℝ) - m) := by
    have : (m : ℝ) < n := by exact_mod_cast hmn
    have : (0 : ℝ) < (n : ℝ) - m := by linarith
    positivity
  have hq2 : 1 / lam' ^ 2 ≤ (((n : ℝ) + 1) / ((n : ℝ) - m)) ^ 2 := by
    rw [← sq_abs, one_div, ← inv_pow, ← one_div]
    exact pow_le_pow_left₀ (by positivity) hq 2
  have hW16 := WV16_le Λ
  have hWT := WV_le_D Λ (T + H)
  have hW16' : 0 ≤ WV Λ 16 := V_nonneg _
  have hD := Dfac_nonneg Λ (T + H)
  have hK := Kphi_pos
  have hKW := KW_pos
  have hpos : 0 ≤ |lam (m + 1)| * |lam (n + 1)| * Real.exp (-(Λ / 2)) := by positivity
  rw [show -((lg m + lg n) / 2) = -(Λ / 2) by rw [hΛ]]
  refine mul_le_mul_of_nonneg_left (hP.trans ?_) hpos
  have e1 : WV Λ 16 / |lam'| = WV Λ 16 * (1 / |lam'|) := by ring
  have e2 : (7 * (Kphi * Real.exp (-(Λ / 2)) * Dfac Λ (T + H)) + 3 * WV Λ (T + H) / H) / lam' ^ 2 =
      (7 * (Kphi * Real.exp (-(Λ / 2)) * Dfac Λ (T + H)) + 3 * WV Λ (T + H) / H) * (1 / lam' ^ 2) := by ring
  rw [e1, e2]
  have hB : 7 * (Kphi * Real.exp (-(Λ / 2)) * Dfac Λ (T + H)) + 3 * WV Λ (T + H) / H ≤
      7 * Kphi * Real.exp (-(Λ / 2)) * Dfac Λ (T + H) + 3 * KW * Dfac Λ (T + H) / H := by
    have : 3 * WV Λ (T + H) / H ≤ 3 * (KW * Dfac Λ (T + H)) / H := by gcongr
    linarith [this, show 3 * (KW * Dfac Λ (T + H)) / H = 3 * KW * Dfac Λ (T + H) / H by ring]
  have hB0 : 0 ≤ 7 * (Kphi * Real.exp (-(Λ / 2)) * Dfac Λ (T + H)) + 3 * WV Λ (T + H) / H := by
    have := V_nonneg (Λ - 2 * ellT (T + H)); unfold WV; positivity
  have t1 : WV Λ 16 * (1 / |lam'|) ≤ c16 * Real.exp (-(6 * Λ)) * (((n : ℝ) + 1) / ((n : ℝ) - m)) :=
    mul_le_mul hW16 hq (by positivity) (by have := c16_pos; positivity)
  have t2 : (7 * (Kphi * Real.exp (-(Λ / 2)) * Dfac Λ (T + H)) + 3 * WV Λ (T + H) / H) * (1 / lam' ^ 2) ≤
      (((n : ℝ) + 1) / ((n : ℝ) - m)) ^ 2 *
        (7 * Kphi * Real.exp (-(Λ / 2)) * Dfac Λ (T + H) + 3 * KW * Dfac Λ (T + H) / H) := by
    rw [mul_comm ((((n : ℝ) + 1) / ((n : ℝ) - m)) ^ 2)]
    exact mul_le_mul hB hq2 (by positivity) (by positivity)
  linarith

end RamanujanTau.GoodSecondTerm2
