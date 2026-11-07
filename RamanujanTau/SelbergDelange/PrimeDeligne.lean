/-
# The prime form `Σ_{p≤x} λ(p)² log p = x + O(x e^{−b√log x})` (`[DeligneBound]`)

`ψ_R(x) = Σ_{p≤x} λ(p)² log p + Σ_{p^k≤x, k≥2} A_k(p)² log p`.  Under Deligne `|A_k(p)| ≤ 2`, so
`vR ≤ 4Λ` and the prime powers contribute `≤ 4(ψ(x) − θ(x)) ≤ 8√x log x`
(Mathlib's `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`).

Deligne is used only here (the prime-power terms).  `psiR_error` itself is unconditional.
-/
import RamanujanTau.SelbergDelange.Unsmooth
import RamanujanTau.TauPNTError.Uncond
import RamanujanTau.TauPNT.Signs

set_option autoImplicit false

namespace RamanujanTau.SelbergDelange

open Filter Topology
open RamanujanTau.EdgeNonvanishing RamanujanTau.TauPNTUncond RamanujanTau.TauPNT

section Deligne

variable [DeligneBound]

lemma vR_le_vonMangoldt (n : ℕ) : vR n ≤ 4 * ArithmeticFunction.vonMangoldt n := by
  by_cases h : IsPrimePow n
  · have hp : n.minFac.Prime := Nat.minFac_prime h.ne_one
    rw [vR, if_pos h, ArithmeticFunction.vonMangoldt_apply, if_pos h]
    have hA := abs_AA_le_two hp (n.factorization n.minFac)
    have hl : 0 ≤ Real.log n.minFac := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    have h4 : AA n.minFac (n.factorization n.minFac) ^ 2 ≤ 4 := by
      have := sq_abs (AA n.minFac (n.factorization n.minFac))
      have h0 := abs_nonneg (AA n.minFac (n.factorization n.minFac))
      nlinarith
    nlinarith
  · rw [vR, if_neg h, ArithmeticFunction.vonMangoldt_apply, if_neg h]; simp

lemma sqrt_log_le {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x * Real.log x ≤ 10 * x ^ (9 / 10 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hl := Real.log_le_rpow_div hx0.le (ε := 1 / 10) (by norm_num)
  have hs : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
  have hsn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  calc Real.sqrt x * Real.log x ≤ x ^ (1 / 2 : ℝ) * (x ^ (1 / 10 : ℝ) / (1 / 10)) := by
        rw [← hs]; gcongr
    _ = 10 * x ^ (3 / 5 : ℝ) := by
        have : x ^ (1 / 2 : ℝ) * x ^ (1 / 10 : ℝ) = x ^ (3 / 5 : ℝ) := by
          rw [← Real.rpow_add hx0]; norm_num
        rw [← this]; ring
    _ ≤ 10 * x ^ (9 / 10 : ℝ) := by
        have : x ^ (3 / 5 : ℝ) ≤ x ^ (9 / 10 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
        linarith

/-- **`Σ_{p≤x} λ(p)² log p = x + O(x exp(−b√log x))`** (`[DeligneBound]` for prime powers only). -/
theorem rs_prime_PNT_error : ∃ b : ℝ, 0 < b ∧ ∃ K X₀ : ℝ, 0 ≤ K ∧ ∀ x : ℝ, X₀ ≤ x →
    |∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, lam p ^ 2 * Real.log p - x| ≤
      K * x * Real.exp (-b * Real.sqrt (Real.log x)) := by
  obtain ⟨b, hb, K, X₀, hK, h⟩ := psiR_error
  set b' := min b (1 / 10) with hb'
  refine ⟨b', lt_min hb (by norm_num), K + 80, max X₀ 3, by positivity, fun x hx => ?_⟩
  have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hpsi := h x (le_trans (le_max_left _ _) hx)
  set P := ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, lam p ^ 2 * Real.log p with hP
  set Q := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with ¬ n.Prime, vR n with hQ
  have hsplit : psiR x = P + Q := by
    rw [psiR, ← Finset.sum_filter_add_sum_filter_not _ (fun n => n.Prime)]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    exact vR_prime (Finset.mem_filter.1 hp).2
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun n _ => vR_nonneg n
  have hQ1 : Q ≤ 8 * (Real.sqrt x * Real.log x) := by
    have h1 : Q ≤ 4 * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with ¬ n.Prime, ArithmeticFunction.vonMangoldt n := by
      rw [hQ, Finset.mul_sum, TauPartialSums.Icc_one_eq_Ioc]
      exact Finset.sum_le_sum fun n _ => vR_le_vonMangoldt n
    have h2 := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := x) (by linarith)
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime] at h2
    have h3 := le_abs_self (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with ¬ n.Prime, ArithmeticFunction.vonMangoldt n)
    linarith
  have hE : Real.exp (-b * Real.sqrt (Real.log x)) ≤ Real.exp (-b' * Real.sqrt (Real.log x)) := by
    apply Real.exp_le_exp.mpr
    have := Real.sqrt_nonneg (Real.log x)
    have : b' ≤ b := min_le_left _ _
    nlinarith
  have h910 := TauPNTError.pow_910_le (b := b') (min_le_right _ _) hx3
  have hsl := sqrt_log_le (x := x) (by linarith)
  have hQ2 : Q ≤ 80 * (x * Real.exp (-b' * Real.sqrt (Real.log x))) := by nlinarith
  rw [hsplit] at hpsi
  have hKE : K * x * Real.exp (-b * Real.sqrt (Real.log x)) ≤
      K * x * Real.exp (-b' * Real.sqrt (Real.log x)) := by gcongr
  rw [abs_le] at hpsi ⊢
  constructor <;> nlinarith

end Deligne

end RamanujanTau.SelbergDelange
