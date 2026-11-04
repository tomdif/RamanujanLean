import RamanujanTau.KolbergTau.Parity
import RamanujanTau.Congruences.Mod2

/-! # Kolberg's congruence `τ(n) ≡ σ₁₁(n) (mod 2¹¹)` for `n ≡ 1 (mod 8)`

From `linA` at `n` (`LehmerSmall.linA_coeff`):
`27648(τ(n) − σ₁₁(n)) = 2520·47775744·c(n) − Σ_{d∣n} g(d)`, with `c(n) = [qⁿ]S₁²(θS₁)²`,
`g(d) = P_A(n,d) + 27648d¹¹`, and `2520·47775744 = 2¹⁹·229635`, `27648 = 2¹⁰·27`.

* `c(n) ≡ 0 (mod 4)` for `n ≡ 1 (mod 8)` (`coeff_A_mod4`, parity supports mod 8).
* `Σ g ≡ 0 (mod 2²¹)` for `n ≡ 1 (mod 8)`: the divisors pair as `d ↔ e = n/d`, `d ≡ e (mod 8)`, and
  `g(d) + g(e) = 27648(d−e)²(d+e)k(d,e)`. Writing `e = d + 8m`,
  `(d−e)²(d+e)k(d,e) = 128·m²(d+4m)k(d,d+8m)` and `16 ∣ m²(d+4m)k(d,d+8m)` for odd `d` (check over `ZMod 16`).

So `2²¹ ∣ 2¹⁰·27(τ − σ₁₁)`, i.e. `2¹¹ ∣ τ(n) − σ₁₁(n)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace RamanujanTau.KolbergTau
open RamanujanTau PowerSeries Igusa RamanujanTau.LehmerSmall
open scoped ArithmeticFunction.sigma

/-- The pairing polynomial `k(x, y)` of `tau_mod256_odd`. -/
def kk (x y : ℤ) : ℤ :=
  x ^ 8 + x ^ 7 * y + 352 * x ^ 6 * y ^ 2 - 2483 * x ^ 5 * y ^ 3 + 4888 * x ^ 4 * y ^ 4 +
    1260 * x ^ 4 * y ^ 2 - 2483 * x ^ 3 * y ^ 5 - 3780 * x ^ 3 * y ^ 3 + 352 * x ^ 2 * y ^ 6 +
    1260 * x ^ 2 * y ^ 4 + 630 * x ^ 2 * y ^ 2 + x * y ^ 7 + y ^ 8

lemma pair_identity (d e : ℤ) :
    PA (d * e) d + 27648 * d ^ 11 + (PA (d * e) e + 27648 * e ^ 11) =
      27648 * ((d - e) ^ 2 * (d + e) * kk d e) := by
  simp only [PA, kk]; ring

lemma z16 : ∀ j y : ZMod 16, ∀ x : ZMod 16, x = 2 * j + 1 →
    y ^ 2 * (x + 4 * y) * (x ^ 8 + x ^ 7 * (x + 8 * y) + 352 * x ^ 6 * (x + 8 * y) ^ 2 -
      2483 * x ^ 5 * (x + 8 * y) ^ 3 + 4888 * x ^ 4 * (x + 8 * y) ^ 4 + 1260 * x ^ 4 * (x + 8 * y) ^ 2 -
      2483 * x ^ 3 * (x + 8 * y) ^ 5 - 3780 * x ^ 3 * (x + 8 * y) ^ 3 + 352 * x ^ 2 * (x + 8 * y) ^ 6 +
      1260 * x ^ 2 * (x + 8 * y) ^ 4 + 630 * x ^ 2 * (x + 8 * y) ^ 2 + x * (x + 8 * y) ^ 7 +
      (x + 8 * y) ^ 8) = 0 := by
  intro j y x hx; subst hx; revert j y; decide

/-- **Milestone K2 (pair lemma).** For odd `d ≡ e (mod 8)`, `2¹¹ ∣ (d−e)²(d+e)k(d,e)`. -/
theorem pair_dvd {d e : ℤ} (hd : d % 2 = 1) (hde : (8 : ℤ) ∣ e - d) :
    (2048 : ℤ) ∣ (d - e) ^ 2 * (d + e) * kk d e := by
  obtain ⟨m, hm⟩ := hde
  have he : e = d + 8 * m := by linarith
  have h16 : (16 : ℤ) ∣ m ^ 2 * (d + 4 * m) * kk d (d + 8 * m) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 16).mp
    have hj : d = 2 * (d / 2) + 1 := by omega
    have hx : (d : ZMod 16) = 2 * ((d / 2 : ℤ) : ZMod 16) + 1 := by
      conv_lhs => rw [hj]
      push_cast; ring
    have := z16 ((d / 2 : ℤ) : ZMod 16) (m : ZMod 16) (d : ZMod 16) hx
    simp only [kk]; push_cast; exact this
  obtain ⟨t, ht⟩ := h16
  exact ⟨t, by rw [he]; linear_combination 128 * ht⟩

lemma mod8_eq_of_mul {d e : ℕ} (h : (d * e) % 8 = 1) : d % 8 = e % 8 := by
  have h' : (d % 8) * (e % 8) % 8 = 1 := by rw [← Nat.mul_mod]; exact h
  have hd : d % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have he : e % 8 < 8 := Nat.mod_lt _ (by norm_num)
  generalize d % 8 = a at *
  generalize e % 8 = b at *
  interval_cases a <;> interval_cases b <;> simp_all

/-- **Milestone K3.** `Σ_{d∣n} (P_A(n,d) + 27648d¹¹) ≡ 0 (mod 2²¹)` for `n ≡ 1 (mod 8)`. -/
theorem sum_g_dvd {n : ℕ} (hn : n ≠ 0) (h8 : n % 8 = 1) :
    (2097152 : ℤ) ∣ ∑ d ∈ n.divisors, (PA n d + 27648 * (d : ℤ) ^ 11) := by
  set g : ℕ → ℤ := fun d => PA n d + 27648 * (d : ℤ) ^ 11 with hg
  have hodd : n % 2 = 1 := by omega
  have hpair : ∀ d ∈ n.divisors, (2097152 : ℤ) ∣ g d + g (n / d) := by
    intro d hd
    have hdn := Nat.dvd_of_mem_divisors hd
    obtain ⟨e, he⟩ := hdn
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hq : n / d = e := by rw [he]; exact Nat.mul_div_cancel_left e hd0
    have hdo : d % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one d with h | h
      · exfalso; rw [he, Nat.mul_mod, h, zero_mul, Nat.zero_mod] at hodd; omega
      · exact h
    have hde : d % 8 = e % 8 := mod8_eq_of_mul (by rw [← he]; exact h8)
    have h2 := pair_dvd (d := (d : ℤ)) (e := (e : ℤ)) (by omega) (by omega)
    obtain ⟨t, ht⟩ := h2
    refine ⟨27 * t, ?_⟩
    have hne : (n : ℤ) = d * e := by exact_mod_cast he
    rw [hq, hg]
    simp only
    rw [hne, pair_identity]
    linear_combination 27648 * ht
  have hdiag : ∀ d ∈ n.divisors, n / d = d → g d = 0 := by
    intro d hd h
    have hne : (n : ℤ) = d * d := by
      have := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd); rw [h] at this; exact_mod_cast this.symm
    rw [hg]; simp only; rw [hne, PA]; ring
  have hz : ((∑ d ∈ n.divisors, g d : ℤ) : ZMod 2097152) = 0 := by
    rw [Int.cast_sum]
    refine Finset.sum_involution (fun d _ => n / d) ?_ ?_ ?_ ?_
    · intro d hd
      rw [← Int.cast_add, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hpair d hd
    · intro d hd hne heq
      exact hne (by rw [hdiag d hd heq, Int.cast_zero])
    · intro d hd
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hn⟩
    · intro d hd
      exact Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hn
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2097152).mp hz

/-- **Kolberg (1962): `τ(n) ≡ σ₁₁(n) (mod 2¹¹)` for `n ≡ 1 (mod 8)`.** -/
theorem tau_mod2048_one_mod8 {n : ℕ} (hn : n ≠ 0) (h8 : n % 8 = 1) :
    (2048 : ℤ) ∣ TauCong.tauPS n - (σ 11 n : ℤ) := by
  have hk := linA_coeff hn
  have hsum : ∑ d ∈ n.divisors, (PA n d + 27648 * (d : ℤ) ^ 11) =
      ∑ d ∈ n.divisors, PA n d + 27648 * (σ 11 n : ℤ) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sigma_int_sum]
  obtain ⟨t, ht⟩ := sum_g_dvd hn h8
  obtain ⟨u, hu⟩ := coeff_A_mod4 h8
  have key : (27648 : ℤ) * (TauCong.tauPS n - (σ 11 n : ℤ)) = 2097152 * (229635 * u - t) := by
    linear_combination -hk - ht + hsum + 2520 * 47775744 * hu
  generalize TauCong.tauPS n - (σ 11 n : ℤ) = X at key ⊢
  generalize 229635 * u - t = Y at key
  omega

/-- The repo's hypothesis class `TauMod2_11` (Kolberg 1962), now a theorem. -/
instance instTauMod2_11 : TauMod2_11 where
  congruence := by
    intro n hn h8
    rw [tau_eq_tauPS, sigma11_eq, Int.modEq_iff_dvd, ← neg_sub, dvd_neg]
    exact tau_mod2048_one_mod8 (by omega) h8

/-- Unconditional restatement in the class's own terms. -/
theorem tauMod2_11_holds {n : ℕ} (hn : n ≥ 1) (h8 : n % 8 = 1) :
    τ n ≡ sigma11 n [ZMOD 2048] :=
  TauMod2_11.congruence hn h8

end RamanujanTau.KolbergTau

#print axioms RamanujanTau.KolbergTau.pair_dvd
#print axioms RamanujanTau.KolbergTau.sum_g_dvd
#print axioms RamanujanTau.KolbergTau.tau_mod2048_one_mod8
#print axioms RamanujanTau.KolbergTau.instTauMod2_11
#print axioms RamanujanTau.KolbergTau.tauMod2_11_holds
