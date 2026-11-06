/-
# The two-sided Selberg lemma `Σ_{n≤N} α(n)²/n ≍ (log N)^{1/4}` (under Deligne)

`α` = coefficients of `L(Δ,s)^{−1/2}` (`SelbergCoeffs.alpha`).  Apply `logmean_upper` /
`logmean_lower` to `f = α²` with `κ = 1/4`: `α(p)² = λ(p)²/4`, and the RS Mertens theorems
(`mertens1_prime`, `mertens2_bound`, unconditional) give the prime sums; Deligne gives
`|α(p^k)| ≤ 1` (`abs_alpha_le_one`) and `α(p)² ≤ 1`.
-/
import RamanujanTau.SelbergCoeffs3.LogMean
import RamanujanTau.SelbergCoeffs3.MertensRate
import RamanujanTau.SelbergCoeffs.Main

set_option autoImplicit false

namespace RamanujanTau.SelbergCoeffs3

open Finset ArithmeticFunction
open RamanujanTau.EdgeNonvanishing (lam)
open RamanujanTau.SelbergCoeffs (alpha alpha_mult alpha_prime abs_alpha_le_one)

noncomputable section

/-- `α²` as a multiplicative function. -/
def alphaSq : ArithmeticFunction ℝ := alpha.pmul alpha

lemma alphaSq_apply (n : ℕ) : alphaSq n = alpha n ^ 2 := by simp [alphaSq, sq]

lemma alphaSq_mult : alphaSq.IsMultiplicative := alpha_mult.pmul alpha_mult

lemma alphaSq_prime {p : ℕ} (hp : p.Prime) : alphaSq p = lam p ^ 2 / 4 := by
  rw [alphaSq_apply, alpha_prime hp]; ring

lemma sum_alphaSq_prime (M : ℕ) :
    ∑ p ∈ PrimesTo M, alphaSq p / p = 1 / 4 * ∑ p ∈ PrimesTo M, lam p ^ 2 / p := by
  rw [mul_sum]
  exact sum_congr rfl fun p hp => by
    rw [alphaSq_prime (mem_filter.mp hp).2]; ring

lemma sum_alphaSq_prime_log (M : ℕ) :
    ∑ p ∈ PrimesTo M, alphaSq p * Real.log p / p =
      1 / 4 * ∑ p ∈ PrimesTo M, lam p ^ 2 * Real.log p / p := by
  rw [mul_sum]
  exact sum_congr rfl fun p hp => by
    rw [alphaSq_prime (mem_filter.mp hp).2]; ring

/-- **Two-sided Selberg lemma** (under Deligne):
`c (log N)^{1/4} ≤ Σ_{n≤N} α(n)²/n ≤ C (log N)^{1/4}` for all `N ≥ 2`. -/
theorem selberg_two_sided [DeligneBound] : ∃ c C : ℝ, 0 < c ∧ ∀ N : ℕ, 2 ≤ N →
    c * Real.log N ^ (1 / 4 : ℝ) ≤ ∑ n ∈ Ioc 0 N, alpha n ^ 2 / n ∧
      ∑ n ∈ Ioc 0 N, alpha n ^ 2 / n ≤ C * Real.log N ^ (1 / 4 : ℝ) := by
  obtain ⟨C2, hC2⟩ := SelbergCoeffs2.mertens2_bound
  obtain ⟨E, hE⟩ := SelbergCoeffs2.mertens1_prime
  have h0 : ∀ n, 0 ≤ alphaSq n := fun n => by rw [alphaSq_apply]; positivity
  have hle1 : ∀ n, alphaSq n ≤ 1 := fun n => by
    rw [alphaSq_apply, ← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (abs_alpha_le_one n)
  -- upper
  have hU := logmean_upper alphaSq alphaSq_mult h0 (B := 1) (κ := 1 / 4) (C := C2 / 4)
    (fun p k _ _ => hle1 _) (fun M hM => by
      rw [sum_alphaSq_prime]; simp only [PrimesTo]
      have := (abs_le.mp (hC2 M)).2
      linarith)
  -- lower
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨c, hc, hL⟩ := logmean_lower alphaSq alphaSq_mult h0 (A := 1 / 4 * (1 + |E| / Real.log 2))
    (κ := 1 / 4) (C := C2 / 4) (by norm_num) (fun p _ => (hle1 p).trans (by norm_num))
    (fun M hM => by
      rw [sum_alphaSq_prime_log]; simp only [PrimesTo]
      have h1 := (abs_le.mp (hE M (by omega))).2
      have hLM : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) (by exact_mod_cast hM)
      have hE' : E ≤ |E| / Real.log 2 * Real.log M := by
        have : |E| ≤ |E| / Real.log 2 * Real.log M := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
          exact mul_le_mul_of_nonneg_left hLM (abs_nonneg _)
        linarith [le_abs_self E]
      nlinarith)
    (fun M hM => by
      rw [sum_alphaSq_prime]; simp only [PrimesTo]
      have := (abs_le.mp (hC2 M)).1
      linarith)
  refine ⟨c, Real.exp (C2 / 4 + 2 * 1), hc, fun N hN => ⟨?_, ?_⟩⟩
  · have := hL N hN
    simpa [alphaSq_apply] using this
  · have := hU N hN
    simpa [alphaSq_apply] using this

end

end RamanujanTau.SelbergCoeffs3
