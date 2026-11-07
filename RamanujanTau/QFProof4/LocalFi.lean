/-
# Local values and bounds of `Fi = recF(ΛR/2)/n`

* `gRm_ppow`: `gRm` is supported on prime powers (unconditional);
* `Fi_eq_prod`: `Fi n = Π_{p|n} Fi(p^{v_p n})` (unconditional);
* `recF_gRm_prime`: `recF gRm p = λ(p)²/2` (unconditional);
* `abs_gRm_le [DeligneBound]`: `|gRm n| ≤ 3Λ(n)`;
* `abs_recF_gRm_ppow [DeligneBound]`: `|recF gRm (p^k)| ≤ (k+1)(k+2)/2`.
-/
import RamanujanTau.QFProof4.RecFMult
import RamanujanTau.SelbergDelange.PrimeDeligne

set_option autoImplicit false

namespace RamanujanTau.QFProof4

open Finset ArithmeticFunction RamanujanTau.QFProof3
open scoped ArithmeticFunction.vonMangoldt
open RamanujanTau.SelbergDelange3 (recF recF_eq recF_zero recF_one gR gR_zero gR_one)
open RamanujanTau.SelbergCoeffs2 (LamR sqL sqL_nonneg LamR_prime)
open RamanujanTau.TauPNTUncond (vR vR_nonneg vR_of_not)

lemma gRm_eq (n : ℕ) : gRm n = LamR n / 2 := by simp [gRm, gR]; ring

lemma sqL_le_vonMangoldt (n : ℕ) : sqL n ≤ ArithmeticFunction.vonMangoldt n := by
  unfold sqL
  split_ifs with h
  · conv_rhs => rw [← h]
    rw [vonMangoldt_apply_pow (by norm_num)]
  · exact vonMangoldt_nonneg

lemma gRm_ppow (n : ℕ) (hn : ¬ IsPrimePow n) : gRm n = 0 := by
  rw [gRm_eq, LamR, vR_of_not hn]
  have h1 := sqL_le_vonMangoldt n
  have h2 := sqL_nonneg n
  rw [vonMangoldt_apply, if_neg hn] at h1
  have : sqL n = 0 := le_antisymm h1 h2
  rw [this]; ring

lemma gRm_zero : gRm 0 = 0 := by simp [gRm, gR_zero]
lemma gRm_one : gRm 1 = 0 := by simp [gRm, gR_one]

lemma recF_gRm_eq_prod (n : ℕ) (hn : n ≠ 0) :
    recF gRm n = ∏ p ∈ n.primeFactors, recF gRm (p ^ n.factorization p) :=
  recF_eq_prod gRm gRm_zero gRm_one gRm_ppow n hn

lemma Fi_apply (n : ℕ) : Fi n = recF gRm n / n := rfl

lemma Fi_eq_prod (n : ℕ) (hn : n ≠ 0) :
    Fi n = ∏ p ∈ n.primeFactors, Fi (p ^ n.factorization p) := by
  rw [Fi_apply, recF_gRm_eq_prod n hn]
  conv_lhs => rw [show (n : ℝ) = ((n.factorization.prod (· ^ ·) : ℕ) : ℝ) by
    rw [Nat.prod_factorization_pow_eq_self hn]]
  rw [Finsupp.prod, Nat.support_factorization, Nat.cast_prod, ← prod_div_distrib]
  refine prod_congr rfl fun p _ => ?_
  rw [Fi_apply]

lemma recF_gRm_prime {p : ℕ} (hp : p.Prime) :
    recF gRm p = RamanujanTau.EdgeNonvanishing.lam p ^ 2 / 2 := by
  have h := recF_ppow_rec gRm gRm_zero gRm_one hp 1
  have hI : Icc 0 1 = {0, 1} := by ext; simp; omega
  rw [hI, sum_pair (by norm_num)] at h
  simp only [pow_zero, gRm_one, zero_mul, zero_add, pow_one, Nat.sub_self, recF_one, mul_one,
    Nat.cast_one, one_mul] at h
  rw [gRm_eq, LamR_prime hp] at h
  have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have : Real.log p * recF gRm p = Real.log p * (RamanujanTau.EdgeNonvanishing.lam p ^ 2 / 2) := by
    rw [h]; ring
  exact mul_left_cancel₀ hl.ne' this

section Deligne

variable [DeligneBound]

lemma abs_LamR_le (n : ℕ) : |LamR n| ≤ 6 * ArithmeticFunction.vonMangoldt n := by
  have h1 := RamanujanTau.SelbergDelange.vR_le_vonMangoldt n
  have h2 := sqL_le_vonMangoldt n
  have h3 := vR_nonneg n
  have h4 := sqL_nonneg n
  rw [LamR, abs_le]; constructor <;> linarith

lemma abs_gRm_le (n : ℕ) : |gRm n| ≤ 3 * ArithmeticFunction.vonMangoldt n := by
  rw [gRm_eq, abs_div, abs_two]; linarith [abs_LamR_le n]

omit [DeligneBound] in
lemma sum_tri (k : ℕ) :
    ∑ i ∈ range k, ((i : ℝ) + 1) * ((i : ℝ) + 2) / 2 = (k : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) + 2) / 6 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

lemma abs_recF_gRm_ppow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    |recF gRm (p ^ k)| ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 := by
  have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [recF_one]
    have h := recF_ppow_rec gRm gRm_zero gRm_one hp k
    have hI : Icc 0 k = range (k + 1) := by ext; simp only [mem_Icc, mem_range]; omega
    rw [hI, sum_range_succ', pow_zero, gRm_one, zero_mul, add_zero] at h
    have hb : |∑ e ∈ range k, gRm (p ^ (e + 1)) * recF gRm (p ^ (k - (e + 1)))| ≤
        3 * Real.log p * ∑ e ∈ range k, ((e : ℝ) + 1) * ((e : ℝ) + 2) / 2 := by
      rw [← sum_range_reflect, mul_sum]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun e he => ?_)
      have hek : e < k := mem_range.1 he
      rw [show k - 1 - e + 1 = k - e by omega, abs_mul]
      have hg : |gRm (p ^ (k - e))| ≤ 3 * Real.log p := by
        have := abs_gRm_le (p ^ (k - e))
        rwa [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp] at this
      have hr := ih (k - (k - e)) (by omega)
      rw [show k - (k - e) = e by omega] at hr ⊢
      calc |gRm (p ^ (k - e))| * |recF gRm (p ^ e)| ≤ (3 * Real.log p) * (((e : ℝ) + 1) * ((e : ℝ) + 2) / 2) :=
            mul_le_mul hg hr (abs_nonneg _) (by positivity)
        _ = _ := by ring
    rw [sum_tri] at hb
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have : (k : ℝ) * Real.log p * |recF gRm (p ^ k)| ≤
        (k : ℝ) * Real.log p * (((k : ℝ) + 1) * ((k : ℝ) + 2) / 2) := by
      rw [← abs_of_pos (mul_pos hk0 hl), ← abs_mul, h]
      calc _ ≤ 3 * Real.log p * ((k : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) + 2) / 6) := hb
        _ = _ := by rw [abs_of_pos (mul_pos hk0 hl)]; ring
    exact le_of_mul_le_mul_left this (mul_pos hk0 hl)

end Deligne

end RamanujanTau.QFProof4
