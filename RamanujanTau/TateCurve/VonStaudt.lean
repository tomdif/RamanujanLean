import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.FieldTheory.Finite.Basic

/-!
# The `p`-part of von Staudt–Clausen

For an odd prime `p`: `p · B_m` is `p`-integral for every `m`, `p · B_m ≡ Σ_{k<p} kᵐ (mod p)`, and hence
`p · B_{p−1} ≡ −1 (mod p)` (stated with `padicNorm`).
-/

set_option autoImplicit false

namespace TateCurve
open Finset

variable {p : ℕ} [hp : Fact p.Prime]

lemma padicNorm_pow (x : ℚ) (n : ℕ) : padicNorm p (x ^ n) = padicNorm p x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, padicNorm.mul, ih, pow_succ]

lemma padicNorm_natCast_le (n : ℕ) : padicNorm p (n : ℚ) ≤ 1 := by
  exact_mod_cast padicNorm.of_int (p := p) (n : ℤ)

lemma padicNorm_sum_pow_le_one (m : ℕ) : padicNorm p (∑ k ∈ range p, (k : ℚ) ^ m) ≤ 1 := by
  refine padicNorm.sum_le' (fun k _ => ?_) zero_le_one
  rw [padicNorm_pow]
  exact pow_le_one₀ (padicNorm.nonneg _) (padicNorm_natCast_le k)

lemma lt_three_pow (e : ℕ) (he : 1 ≤ e) : e + 1 < 3 ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ n _ ih => rw [pow_succ]; omega

/-- `|pᵉ/(e+1)|_p ≤ p⁻¹` for `e ≥ 1`, `p ≥ 3`. -/
lemma padicNorm_pow_div_succ (hp3 : 3 ≤ p) (e : ℕ) (he : 1 ≤ e) :
    padicNorm p ((p : ℚ) ^ e / ((e : ℚ) + 1)) ≤ (p : ℚ)⁻¹ := by
  have hp1 : p ≠ 1 := hp.out.ne_one
  obtain ⟨v, u, hu, hvu'⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.succ_ne_zero e) p hp1
  have hvu : e + 1 = p ^ v * u := hvu'
  have hu0 : u ≠ 0 := by rintro rfl; simp at hvu
  have hvlt : v < e := by
    have h1 : p ^ v ≤ e + 1 := by
      rw [hvu]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hu0)
    have h2 : e + 1 < p ^ e := lt_of_lt_of_le (lt_three_pow e he) (Nat.pow_le_pow_left hp3 e)
    exact (Nat.pow_lt_pow_iff_right (by omega)).mp (lt_of_le_of_lt h1 h2)
  have hcast : ((e : ℚ) + 1) = (p : ℚ) ^ v * (u : ℚ) := by exact_mod_cast hvu
  have hnu : padicNorm p (u : ℚ) = 1 := (padicNorm.nat_eq_one_iff u).mpr hu
  have hpn : padicNorm p (p : ℚ) = (p : ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime
  have hp0 : ((p : ℚ)⁻¹) ≠ 0 := by
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    exact inv_ne_zero this
  rw [hcast, padicNorm.div, padicNorm.mul, hnu, mul_one, padicNorm_pow, padicNorm_pow, hpn]
  rw [div_eq_mul_inv, ← pow_sub₀ _ hp0 hvlt.le]
  have hle : (p : ℚ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_lt.le)
  exact pow_le_of_le_one (by positivity) hle (by omega)

/-- `p · B_m − Σ_{k<p} kᵐ` lies in `p ℤ_(p)`, for every `m` (odd prime `p`). -/
theorem padicNorm_p_mul_bernoulli_sub (hp3 : 3 ≤ p) (m : ℕ) :
    padicNorm p ((p : ℚ) * bernoulli m - ∑ k ∈ range p, (k : ℚ) ^ m) ≤ (p : ℚ)⁻¹ := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  have hpos : (0 : ℚ) ≤ (p : ℚ)⁻¹ := by positivity
  -- integrality of `p B_i` for `i < m`
  have hint : ∀ i < m, padicNorm p ((p : ℚ) * bernoulli i) ≤ 1 := by
    intro i hi
    have h1 := ih i hi
    have h2 := padicNorm_sum_pow_le_one (p := p) i
    have hle : (p : ℚ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_lt.le)
    calc padicNorm p ((p : ℚ) * bernoulli i)
        = padicNorm p (((p : ℚ) * bernoulli i - ∑ k ∈ range p, (k : ℚ) ^ i) + ∑ k ∈ range p, (k : ℚ) ^ i) := by
          ring_nf
      _ ≤ max _ _ := padicNorm.nonarchimedean
      _ ≤ 1 := max_le (h1.trans hle) h2
  rw [sum_range_pow, sum_range_succ]
  have hlast : bernoulli m * ((m + 1).choose m : ℚ) * (p : ℚ) ^ (m + 1 - m) / (m + 1) =
      (p : ℚ) * bernoulli m := by
    rw [Nat.choose_succ_self_right, show m + 1 - m = 1 by omega]
    push_cast
    field_simp
  rw [hlast, sub_add_cancel_right, padicNorm.neg]
  refine padicNorm.sum_le' (fun i hi => ?_) hpos
  have him : i < m := mem_range.mp hi
  have hch : ((m + 1).choose i : ℚ) * (((m - i : ℕ) : ℚ) + 1) = (m.choose i : ℚ) * ((m : ℚ) + 1) := by
    have := Nat.choose_mul_succ_eq m i
    rw [show m + 1 - i = (m - i) + 1 by omega] at this
    exact_mod_cast this.symm
  have hpow : (p : ℚ) ^ (m + 1 - i) = (p : ℚ) * (p : ℚ) ^ (m - i) := by
    rw [show m + 1 - i = (m - i) + 1 by omega, pow_succ, mul_comm]
  have hterm : bernoulli i * ((m + 1).choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / (m + 1) =
      ((p : ℚ) * bernoulli i) * (m.choose i : ℚ) * ((p : ℚ) ^ (m - i) / (((m - i : ℕ) : ℚ) + 1)) := by
    rw [hpow]
    have h1 : ((m : ℚ) + 1) ≠ 0 := by positivity
    have h2 : (((m - i : ℕ) : ℚ) + 1) ≠ 0 := by positivity
    rw [← mul_div_assoc, div_eq_div_iff h1 h2]
    linear_combination (bernoulli i * (p : ℚ) * (p : ℚ) ^ (m - i)) * hch
  rw [hterm, padicNorm.mul, padicNorm.mul]
  have hA := hint i him
  have hB := padicNorm_natCast_le (p := p) (m.choose i)
  have hC := padicNorm_pow_div_succ hp3 (m - i) (by omega)
  calc padicNorm p ((p : ℚ) * bernoulli i) * padicNorm p (m.choose i : ℚ) *
        padicNorm p ((p : ℚ) ^ (m - i) / (((m - i : ℕ) : ℚ) + 1))
      ≤ 1 * 1 * (p : ℚ)⁻¹ := by
        gcongr <;> exact padicNorm.nonneg _
    _ = (p : ℚ)⁻¹ := by ring

/-- `p · B_m` is `p`-integral. -/
theorem padicNorm_p_mul_bernoulli_le_one (hp3 : 3 ≤ p) (m : ℕ) :
    padicNorm p ((p : ℚ) * bernoulli m) ≤ 1 := by
  have h1 := padicNorm_p_mul_bernoulli_sub hp3 m
  have h2 := padicNorm_sum_pow_le_one (p := p) m
  have hle : (p : ℚ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_lt.le)
  calc padicNorm p ((p : ℚ) * bernoulli m)
      = padicNorm p (((p : ℚ) * bernoulli m - ∑ k ∈ range p, (k : ℚ) ^ m) + ∑ k ∈ range p, (k : ℚ) ^ m) := by
        ring_nf
    _ ≤ max _ _ := padicNorm.nonarchimedean
    _ ≤ 1 := max_le (h1.trans hle) h2

/-- Fermat: `Σ_{k<p} k^{p−1} ≡ −1 (mod p)`. -/
lemma dvd_sum_pow_sub_one_add_one : (p : ℤ) ∣ (∑ k ∈ range p, (k : ℤ) ^ (p - 1)) + 1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have hterm : ∀ k ∈ range p, ((k : ZMod p)) ^ (p - 1) = if k = 0 then 0 else 1 := by
    intro k hk
    split_ifs with h
    · subst h; simp [zero_pow (show p - 1 ≠ 0 by have := hp.out.two_le; omega)]
    · apply ZMod.pow_card_sub_one_eq_one
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      intro hd
      exact h (Nat.eq_zero_of_dvd_of_lt hd (mem_range.mp hk))
  rw [sum_congr rfl hterm, sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul, mul_one]
  have hcard : (filter (fun k => ¬k = 0) (range p)).card = p - 1 := by
    rw [filter_ne', card_erase_of_mem (mem_range.mpr hp.out.pos), card_range]
  rw [hcard, Nat.cast_sub hp.out.one_le, ZMod.natCast_self]
  ring

/-- **von Staudt–Clausen at `p`**: `p · B_{p−1} ≡ −1 (mod p)`, i.e. `|p B_{p−1} + 1|_p ≤ p⁻¹`. -/
theorem padicNorm_p_mul_bernoulli_add_one (hp3 : 3 ≤ p) :
    padicNorm p ((p : ℚ) * bernoulli (p - 1) + 1) ≤ (p : ℚ)⁻¹ := by
  have h1 := padicNorm_p_mul_bernoulli_sub hp3 (p - 1)
  obtain ⟨t, ht⟩ := dvd_sum_pow_sub_one_add_one (p := p)
  have h2 : padicNorm p ((∑ k ∈ range p, (k : ℚ) ^ (p - 1)) + 1) ≤ (p : ℚ)⁻¹ := by
    have : (∑ k ∈ range p, (k : ℚ) ^ (p - 1)) + 1 = (p : ℚ) * (t : ℚ) := by exact_mod_cast ht
    rw [this, padicNorm.mul, padicNorm.padicNorm_p_of_prime]
    exact mul_le_of_le_one_right (by positivity) (padicNorm.of_int t)
  calc padicNorm p ((p : ℚ) * bernoulli (p - 1) + 1)
      = padicNorm p (((p : ℚ) * bernoulli (p - 1) - ∑ k ∈ range p, (k : ℚ) ^ (p - 1)) +
          ((∑ k ∈ range p, (k : ℚ) ^ (p - 1)) + 1)) := by ring_nf
    _ ≤ max _ _ := padicNorm.nonarchimedean
    _ ≤ (p : ℚ)⁻¹ := max_le h1 h2

/-- `p · B_{p−1}` is a `p`-adic unit. -/
theorem padicNorm_p_mul_bernoulli_eq_one (hp3 : 3 ≤ p) :
    padicNorm p ((p : ℚ) * bernoulli (p - 1)) = 1 := by
  have h := padicNorm_p_mul_bernoulli_add_one hp3
  have hlt : (p : ℚ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  have hne : padicNorm p ((p : ℚ) * bernoulli (p - 1) + 1) ≠ padicNorm p (-1 : ℚ) := by
    rw [padicNorm.neg, padicNorm.one]; exact (lt_of_le_of_lt h hlt).ne
  have := padicNorm.add_eq_max_of_ne hne
  rw [show (p : ℚ) * bernoulli (p - 1) + 1 + -1 = (p : ℚ) * bernoulli (p - 1) by ring,
    padicNorm.neg, padicNorm.one] at this
  rw [this]
  exact max_eq_right (h.trans hlt.le)

theorem bernoulli_sub_one_ne_zero (hp3 : 3 ≤ p) : bernoulli (p - 1) ≠ 0 := by
  intro h
  have := padicNorm_p_mul_bernoulli_eq_one (p := p) hp3
  rw [h, mul_zero, padicNorm.zero] at this
  exact zero_ne_one this

end TateCurve
