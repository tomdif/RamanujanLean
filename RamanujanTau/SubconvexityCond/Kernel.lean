/-
# Elementary facts for the off-diagonal: `ℓ_h(n) = log(1+h/n)`, the Gaussian factor, Abel summation
-/
import RamanujanTau.SubconvexityCond.Expand
import RamanujanTau.SubconvexityCond.Defs

set_option autoImplicit false

namespace RamanujanTau.SubconvexityCond

open Real Finset

/-- `ℓ_h(n) = log(n+h) − log n`. -/
noncomputable def ell (h n : ℕ) : ℝ := Real.log ((n : ℝ) + h) - Real.log n

/-- The Gaussian factor `E_h(n) = e^{−(H ℓ_h(n))²/4}`. -/
noncomputable def Ef (H : ℝ) (h n : ℕ) : ℝ := Real.exp (-(H * ell h n) ^ 2 / 4)

lemma kw_shift (H T : ℝ) (h n : ℕ) :
    kw H T (n + h) n = Ef H h n * Real.cos (ell h n * T) := by
  unfold kw Ef ell
  push_cast
  rw [show Real.log n - Real.log ((n : ℝ) + h) = -(Real.log ((n : ℝ) + h) - Real.log n) by ring,
    mul_neg, neg_sq, neg_mul, Real.cos_neg]

lemma ell_eq {h n : ℕ} (hn : 1 ≤ n) : ell h n = Real.log (1 + (h : ℝ) / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold ell
  rw [← Real.log_div (by positivity) hn0.ne']
  congr 1; field_simp

lemma ell_nonneg (h n : ℕ) (hn : 1 ≤ n) : 0 ≤ ell h n := by
  rw [ell_eq hn]
  exact Real.log_nonneg (by have : (0:ℝ) ≤ h / n := by positivity
                            linarith)

lemma ell_diff {h n : ℕ} (hn : 1 ≤ n) :
    ell h n - ell h (n + 1) =
      Real.log (((n : ℝ) + h) * (n + 1) / ((n : ℝ) * ((n : ℝ) + 1 + h))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold ell
  push_cast
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  ring_nf

lemma ell_succ_le {h n : ℕ} (hn : 1 ≤ n) : ell h (n + 1) ≤ ell h n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have := ell_diff (h := h) hn
  have h1 : 0 ≤ Real.log (((n : ℝ) + h) * (n + 1) / ((n : ℝ) * ((n : ℝ) + 1 + h))) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    nlinarith
  linarith

lemma ell_sub_succ_le {h n : ℕ} (hn : 1 ≤ n) : ell h n - ell h (n + 1) ≤ (h : ℝ) / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  rw [ell_diff hn]
  refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
  rw [div_sub_one (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hh0 hn0.le, mul_nonneg (mul_nonneg hh0 hn0.le) hh0]

lemma Ef_pos (H : ℝ) (h n : ℕ) : 0 < Ef H h n := Real.exp_pos _

lemma Ef_le_one (H : ℝ) (h n : ℕ) : Ef H h n ≤ 1 := by
  unfold Ef; rw [Real.exp_le_one_iff]
  have := sq_nonneg (H * ell h n); linarith

lemma Ef_mono {H : ℝ} (hH : 0 ≤ H) {h n : ℕ} (hn : 1 ≤ n) : Ef H h n ≤ Ef H h (n + 1) := by
  unfold Ef
  apply Real.exp_le_exp.2
  have h1 := ell_nonneg h (n + 1) (by omega)
  have h2 := ell_succ_le (h := h) hn
  have h3 : H * ell h (n + 1) ≤ H * ell h n := mul_le_mul_of_nonneg_left h2 hH
  have h4 : 0 ≤ H * ell h (n + 1) := mul_nonneg hH h1
  nlinarith

/-- Away from the diagonal band (`nρ < hH`), the Gaussian factor is `≤ e^{−ρ²/64}`. -/
lemma Ef_small {H ρ : ℝ} (hρ : 1 ≤ ρ) (hρH : ρ ≤ H) {h n : ℕ} (hh : 1 ≤ h) (hn : 1 ≤ n)
    (hnh : (n : ℝ) * ρ < h * H) : Ef H h (n + 1) ≤ Real.exp (-ρ ^ 2 / 64) := by
  have hH0 : 0 < H := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  set c : ℝ := ρ / (2 * H) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by rw [hc, div_le_one (by positivity)]; linarith
  have hy : c ≤ (h : ℝ) / ((n + 1 : ℕ) : ℝ) := by
    rw [hc]; push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : ρ ≤ h * H := by nlinarith
    nlinarith
  have hl : c / 2 ≤ ell h (n + 1) := by
    rw [ell_eq (by omega)]
    have h1 : Real.log (1 + c) ≤ Real.log (1 + (h : ℝ) / ((n + 1 : ℕ) : ℝ)) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 := Real.one_sub_inv_le_log_of_pos (x := 1 + c) (by linarith)
    have h3 : c / 2 ≤ 1 - (1 + c)⁻¹ := by
      rw [show 1 - (1 + c)⁻¹ = c / (1 + c) by field_simp; ring]
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
    linarith
  unfold Ef
  apply Real.exp_le_exp.2
  have h4 : ρ / 4 ≤ H * ell h (n + 1) := by
    have : H * (c / 2) = ρ / 4 := by rw [hc]; field_simp; ring
    rw [← this]; exact mul_le_mul_of_nonneg_left hl hH0.le
  have h5 : 0 ≤ ρ / 4 := by positivity
  nlinarith

lemma abs_cos_sub_cos_le (a b : ℝ) : |Real.cos a - Real.cos b| ≤ |a - b| := by
  rw [Real.cos_sub_cos, abs_mul, abs_mul]
  have h1 := Real.abs_sin_le_one ((a + b) / 2)
  have h2 := Real.abs_sin_le_abs (x := (a - b) / 2)
  rw [abs_div, abs_two] at h2
  have h3 : |(-2 : ℝ)| = 2 := by norm_num
  rw [h3]
  have : 0 ≤ |Real.sin ((a - b) / 2)| := abs_nonneg _
  nlinarith [abs_nonneg (Real.sin ((a + b) / 2))]

/-- **Abel summation** on `Icc 1 N`. -/
lemma abel_Icc (a G : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, a n * G n = (∑ k ∈ Icc 1 N, a k) * G (N + 1) +
      ∑ n ∈ Icc 1 N, (∑ k ∈ Icc 1 n, a k) * (G n - G (n + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih, sum_Icc_succ_top (show 1 ≤ N + 1 by omega) (fun n =>
      (∑ k ∈ Icc 1 n, a k) * (G n - G (n + 1))), sum_Icc_succ_top (show 1 ≤ N + 1 by omega)]
    ring

lemma sum_telescope (E : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (E (n + 1) - E n) = E (N + 1) - E 1 := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_Icc_succ_top (by omega), ih]; ring

end RamanujanTau.SubconvexityCond
