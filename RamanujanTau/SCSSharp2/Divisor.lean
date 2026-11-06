/-
# The divisor bound `τ(n) ≤ C_β n^β`

`card_divisors_le_rpow`: for every `β > 0` there is `C` with `#n.divisors ≤ C n^β` for `n ≥ 1`.

Proof prime by prime from `#n.divisors = ∏_{p | n} (e_p + 1)` (`Nat.card_divisors`):
* if `p ≥ 2^{1/β}` then `(p^e)^β ≥ 2^e ≥ e + 1`;
* always `(p^e)^β ≥ 2^{eβ} ≥ 1 + eβ log 2`, so `e + 1 ≤ C₁ (p^e)^β` with `C₁ = 1 + 1/(β log 2)`;
and there are fewer than `P₀ = ⌈2^{1/β}⌉` primes of the second kind.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.SCSSharp2

open Finset

lemma succ_le_C1_rpow (β : ℝ) (hβ : 0 < β) (p e : ℕ) (hp : 2 ≤ p) :
    ((e : ℝ) + 1) ≤ (1 + 1 / (β * Real.log 2)) * (((p : ℝ) ^ e) ^ β) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : ((2 : ℝ) ^ e) ^ β ≤ ((p : ℝ) ^ e) ^ β := by gcongr
  have h2 : ((2 : ℝ) ^ e) ^ β = Real.exp (e * β * Real.log 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.rpow_def_of_pos (by norm_num)]
    ring_nf
  have h3 : 1 + e * β * Real.log 2 ≤ Real.exp (e * β * Real.log 2) := by
    have := Real.add_one_le_exp (e * β * Real.log 2); linarith
  have hbl : 0 < β * Real.log 2 := by positivity
  have h4 : ((e : ℝ) + 1) ≤ (1 + 1 / (β * Real.log 2)) * (1 + e * β * Real.log 2) := by
    have e1 : (1 + 1 / (β * Real.log 2)) * (1 + e * β * Real.log 2) =
        1 + e * (β * Real.log 2) + 1 / (β * Real.log 2) + e := by
      field_simp; ring
    rw [e1]
    have : 0 ≤ (e : ℝ) * (β * Real.log 2) := by positivity
    have : 0 ≤ 1 / (β * Real.log 2) := by positivity
    linarith
  calc ((e : ℝ) + 1) ≤ (1 + 1 / (β * Real.log 2)) * (1 + e * β * Real.log 2) := h4
    _ ≤ (1 + 1 / (β * Real.log 2)) * (((p : ℝ) ^ e) ^ β) := by
        gcongr; rw [← h2] at h3; linarith

lemma succ_le_rpow_of_large (β : ℝ) (hβ : 0 < β) (p e : ℕ) (hp : (2 : ℝ) ^ (1 / β) ≤ p) :
    ((e : ℝ) + 1) ≤ ((p : ℝ) ^ e) ^ β := by
  have hp0 : (0 : ℝ) ≤ p := le_trans (by positivity) hp
  have h2 : (2 : ℝ) ≤ (p : ℝ) ^ β := by
    have := Real.rpow_le_rpow (by positivity) hp hβ.le
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hβ.ne', Real.rpow_one] at this
  have h3 : ((p : ℝ) ^ e) ^ β = ((p : ℝ) ^ β) ^ e := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0, ← Real.rpow_natCast, ← Real.rpow_mul hp0, mul_comm]
  rw [h3]
  have h4 : ((e : ℝ) + 1) ≤ 2 ^ e := by
    have : e + 1 ≤ 2 ^ e := Nat.lt_two_pow_self
    exact_mod_cast this
  exact h4.trans (pow_le_pow_left₀ (by norm_num) h2 e)

/-- **Divisor bound** `τ(n) ≤ C_β n^β`. -/
theorem card_divisors_le_rpow (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → (#n.divisors : ℝ) ≤ C * (n : ℝ) ^ β := by
  classical
  set C₁ : ℝ := 1 + 1 / (β * Real.log 2) with hC₁
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC₁1 : 1 ≤ C₁ := by
    have : 0 ≤ 1 / (β * Real.log 2) := by positivity
    rw [hC₁]; linarith
  set P0 : ℕ := ⌈(2 : ℝ) ^ (1 / β)⌉₊
  refine ⟨C₁ ^ P0, one_le_pow₀ hC₁1, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hpt : ∀ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ≤
      (if p < P0 then C₁ else 1) * (((p : ℝ) ^ n.factorization p) ^ β) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    split_ifs with h
    · exact succ_le_C1_rpow β hβ p _ hp2
    · push Not at h
      rw [one_mul]
      exact succ_le_rpow_of_large β hβ p _ ((Nat.le_ceil _).trans (by exact_mod_cast h))
  have hcard : (#n.divisors : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hn0]; push_cast; rfl
  have h1 : (#n.divisors : ℝ) ≤
      ∏ p ∈ n.primeFactors, ((if p < P0 then C₁ else 1) * (((p : ℝ) ^ n.factorization p) ^ β)) := by
    rw [hcard]
    exact Finset.prod_le_prod (fun _ _ => by positivity) hpt
  rw [Finset.prod_mul_distrib] at h1
  have h2 : ∏ p ∈ n.primeFactors, (if p < P0 then C₁ else 1) ≤ C₁ ^ P0 := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    refine pow_le_pow_right₀ hC₁1 ?_
    calc (n.primeFactors.filter (fun p => p < P0)).card
        ≤ (Finset.range P0).card := Finset.card_le_card (fun p hp => by
          simp only [Finset.mem_filter] at hp; simpa using hp.2)
      _ = P0 := Finset.card_range _
  have h3 : ∏ p ∈ n.primeFactors, (((p : ℝ) ^ n.factorization p) ^ β) = (n : ℝ) ^ β := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
    congr 1
    have := Nat.prod_factorization_pow_eq_self hn0
    rw [Finsupp.prod, Nat.support_factorization] at this
    conv_rhs => rw [← this]
    push_cast; rfl
  rw [h3] at h1
  calc (#n.divisors : ℝ) ≤ (∏ p ∈ n.primeFactors, (if p < P0 then C₁ else 1)) * (n : ℝ) ^ β := h1
    _ ≤ C₁ ^ P0 * (n : ℝ) ^ β := by gcongr

end RamanujanTau.SCSSharp2
