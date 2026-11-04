/-
# Linking the model to `p(n)`: `U(n+j) = √(U(n)² + a j)`, `Mmain = (K/2)e^{F(U)}`, and the relative error
-/
import RamanujanTau.JensenThreshold.Tail.Setup

set_option autoImplicit false

namespace JensenThreshold.Tail

open Real Rademacher

lemma uk1_sq {m : ℕ} (hm : 1 ≤ m) : uk 1 m ^ 2 = aC * ((m : ℝ) - 1 / 24) := by
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [uk, Nat.cast_one, div_one, mul_pow, Real.sq_sqrt (by nlinarith), aC]; ring

lemma uk1_pos {m : ℕ} (hm : 1 ≤ m) : 0 < uk 1 m := uk_pos one_pos hm

lemma Us_uk {n : ℕ} (hn : 1 ≤ n) (j : ℕ) (hU : 1 < uk 1 n) : Us (uk 1 n) j = uk 1 (n + j) := by
  unfold Us
  rw [uk1_sq hn, ← Real.sqrt_sq (uk1_pos (show 1 ≤ n + j by omega)).le, uk1_sq (by omega)]
  congr 1; push_cast; ring

lemma Mmain_eq_exp {m : ℕ} (hU : 1 < uk 1 m) : Mmain m = Kc / 2 * Real.exp (Fn (uk 1 m)) := by
  unfold Mmain Fn
  have h0 : 0 < uk 1 m := by linarith
  rw [Real.exp_sub, Real.exp_add, Real.exp_log (by linarith), show (3 : ℝ) * Real.log (uk 1 m) =
    Real.log (uk 1 m ^ 3) by rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
  field_simp

/-- relative error of the main term. -/
lemma rel_err {m : ℕ} (hm : 2 ≤ m) (hU : 1 < uk 1 m) :
    |(HardyRamanujan.p m : ℝ) / Mmain m - 1| ≤ 2 * uk 1 m ^ 3 / (uk 1 m - 1) * Real.exp (-(uk 1 m / 2)) := by
  have h := p_sub_main_le m hm
  have hMpos : 0 < Mmain m := by
    rw [Mmain_eq_exp hU]; have := Kc_pos; positivity
  have e : (HardyRamanujan.p m : ℝ) / Mmain m - 1 = ((HardyRamanujan.p m : ℝ) - Mmain m) / Mmain m := by
    field_simp
  rw [e, abs_div, abs_of_pos hMpos, div_le_iff₀ hMpos]
  refine le_trans h (le_of_eq ?_)
  unfold Mmain
  have h0 : 0 < uk 1 m := by linarith
  have h1 : uk 1 m - 1 ≠ 0 := by linarith
  have hx : Real.exp (uk 1 m / 2) = Real.exp (-(uk 1 m / 2)) * Real.exp (uk 1 m) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hx]; field_simp

lemma exp_neg_le_inv_sum {x : ℝ} (hx : 0 ≤ x) (N : ℕ) (hpos : 0 < ∑ i ∈ Finset.range N, x ^ i / (i.factorial : ℝ)) :
    Real.exp (-x) ≤ (∑ i ∈ Finset.range N, x ^ i / (i.factorial : ℝ))⁻¹ := by
  rw [Real.exp_neg]
  exact inv_anti₀ hpos (Real.sum_le_exp_of_nonneg hx N)

lemma exp_neg_le_pow {x : ℝ} (hx : 0 < x) (N : ℕ) :
    Real.exp (-x) ≤ (N.factorial : ℝ) * (x ^ N)⁻¹ := by
  have h := Real.sum_le_exp_of_nonneg hx.le (N + 1)
  have hterm : x ^ N / (N.factorial : ℝ) ≤ ∑ i ∈ Finset.range (N + 1), x ^ i / (i.factorial : ℝ) :=
    Finset.single_le_sum (f := fun i => x ^ i / (i.factorial : ℝ)) (fun i _ => by positivity)
      (Finset.mem_range.mpr (by omega))
  have hpos : 0 < x ^ N / (N.factorial : ℝ) := by positivity
  rw [Real.exp_neg]
  calc (Real.exp x)⁻¹ ≤ (x ^ N / (N.factorial : ℝ))⁻¹ := inv_anti₀ hpos (le_trans hterm h)
    _ = _ := by rw [inv_div]; ring

end JensenThreshold.Tail
