import RamanujanTau.LehmerSmall.QuasiLin
import RamanujanTau.Congruences.Mod3
import RamanujanTau.Congruences.Mod2

/-! # `τ ≡ n²σ₇ (mod 27)` for `3 ∤ n` and `τ ≡ σ₁₁ (mod 2⁸)` for odd `n`

Both come from the single quasimodular identity `linA` (`QuasiLin.lean`). At any `n ≥ 1` it reads
`2520·24²·288²·[qⁿ]S₁²(θS₁)² = Σ_{d ∣ n} P(n, d) + 27648·τ(n)` for an explicit integer polynomial `P`.

* **mod 27.** For `n = de` with `3 ∤ d, e`:
  `P(de, d) + 27648(de)²d⁷ = 2¹⁰3⁵·d⁴e²·(d − e)·h(d, e)`, and `(d − e)h(d, e) ≡ 0 (mod 3)` (a check over
  `ZMod 3`). So `27648(τ − n²σ₇) ≡ 0 (mod 3⁶)`.
* **mod 2⁸.** Write `g(d) = P(n, d) + 27648d¹¹`. For `n = de` odd, `g(d) + g(e) = 27648(d − e)²(d + e)k(d, e)`
  and `2⁸ ∣ (d − e)²(d + e)k(d, e)` (a check over `ZMod 256`). Also `g(d) = 0` when `d = e`. The involution
  `d ↦ n/d` on the divisors therefore gives `Σ g ≡ 0 (mod 2¹⁸)`, i.e. `27648(τ − σ₁₁) ≡ 0 (mod 2¹⁸)`.

These supply the repo's hypothesis classes `TauMod27` (`Congruences/Mod3.lean`) and `TauMod2_8`
(`Congruences/Mod2.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace RamanujanTau.LehmerSmall
open RamanujanTau PowerSeries ModP Igusa
open scoped ArithmeticFunction.sigma

/-- The divisor-sum kernel of `linA`. -/
def PA (n d : ℤ) : ℤ :=
  -17418240 * n ^ 3 * d ^ 1 + 104509440 * n ^ 4 * d ^ 1 - 125411328 * n ^ 5 * d ^ 1 +
    17418240 * n ^ 2 * d ^ 3 - 139345920 * n ^ 3 * d ^ 3 + 194088960 * n ^ 4 * d ^ 3 +
    34836480 * n ^ 2 * d ^ 5 - 78382080 * n ^ 3 * d ^ 5 + 9676800 * n ^ 2 * d ^ 7

lemma sigma_int_sum (k n : ℕ) : (σ k n : ℤ) = ∑ d ∈ n.divisors, (d : ℤ) ^ k := by
  rw [ArithmeticFunction.sigma_apply]; push_cast; rfl

/-- `linA` at an arbitrary `n ≥ 1`. -/
lemma linA_coeff {n : ℕ} (hn : n ≠ 0) :
    2520 * (47775744 * coeff n (Sk 1 ^ 2 * theta (Sk 1) ^ 2)) =
      ∑ d ∈ n.divisors, PA n d + 27648 * TauCong.tauPS n := by
  have hk := congrArg (coeff n) linA
  rw [TA_eq] at hk
  simp only [map_add, map_sub, map_neg, neg_mul, coeff_ofNat_mul', coeff_iter, cE2 hn, cE4 hn, cE6 hn,
    cF8 hn, cF10 hn, cE6sq] at hk
  have hs : ∑ d ∈ n.divisors, PA n d =
      -17418240 * (n : ℤ) ^ 3 * (σ 1 n : ℤ) + 104509440 * (n : ℤ) ^ 4 * (σ 1 n : ℤ) -
        125411328 * (n : ℤ) ^ 5 * (σ 1 n : ℤ) + 17418240 * (n : ℤ) ^ 2 * (σ 3 n : ℤ) -
        139345920 * (n : ℤ) ^ 3 * (σ 3 n : ℤ) + 194088960 * (n : ℤ) ^ 4 * (σ 3 n : ℤ) +
        34836480 * (n : ℤ) ^ 2 * (σ 5 n : ℤ) - 78382080 * (n : ℤ) ^ 3 * (σ 5 n : ℤ) +
        9676800 * (n : ℤ) ^ 2 * (σ 7 n : ℤ) := by
    simp only [PA, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sigma_int_sum]
    try simp only [pow_one]
  rw [hs]
  linear_combination hk

lemma d3h : ∀ x y : ZMod 3, x ≠ 0 → y ≠ 0 →
    (x - y) * (39 * x ^ 4 - 276 * x ^ 3 * y + 504 * x ^ 2 * y ^ 2 + 140 * x ^ 2 - 420 * x * y + 70) = 0 := by
  decide

lemma not_dvd_three_of_coprime {n d : ℕ} (h3 : Nat.Coprime n 3) (hd : d ∣ n) : ((d : ℤ) : ZMod 3) ≠ 0 := by
  intro h
  rw [Int.cast_natCast, ZMod.natCast_eq_zero_iff] at h
  have : 3 ∣ Nat.gcd n 3 := Nat.dvd_gcd (dvd_trans h hd) dvd_rfl
  rw [h3] at this; norm_num at this

/-- **`τ(n) ≡ n²σ₇(n) (mod 27)`** for `3 ∤ n`. -/
theorem tau_mod27_coprime {n : ℕ} (hn : n ≠ 0) (h3 : Nat.Coprime n 3) :
    (27 : ℤ) ∣ TauCong.tauPS n - (n : ℤ) ^ 2 * (σ 7 n : ℤ) := by
  have hk := linA_coeff hn
  have hsum : ∑ d ∈ n.divisors, (PA n d + 27648 * (n : ℤ) ^ 2 * (d : ℤ) ^ 7) =
      ∑ d ∈ n.divisors, PA n d + 27648 * (n : ℤ) ^ 2 * (σ 7 n : ℤ) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sigma_int_sum]
  have hdiv : (729 : ℤ) ∣ ∑ d ∈ n.divisors, (PA n d + 27648 * (n : ℤ) ^ 2 * (d : ℤ) ^ 7) := by
    refine Finset.dvd_sum fun d hd => ?_
    have hdn := Nat.dvd_of_mem_divisors hd
    obtain ⟨e, he⟩ := Nat.dvd_of_mem_divisors hd
    have hen : e ∣ n := ⟨d, by rw [he, mul_comm]⟩
    have hx := not_dvd_three_of_coprime h3 hdn
    have hy := not_dvd_three_of_coprime h3 hen
    have h3d : (3 : ℤ) ∣ ((d : ℤ) - e) * (39 * (d : ℤ) ^ 4 - 276 * (d : ℤ) ^ 3 * e + 504 * (d : ℤ) ^ 2 * (e : ℤ) ^ 2 +
        140 * (d : ℤ) ^ 2 - 420 * d * e + 70) := by
      have hz := d3h _ _ hx hy
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (((d : ℤ) - e) * (39 * (d : ℤ) ^ 4 - 276 * (d : ℤ) ^ 3 * e +
        504 * (d : ℤ) ^ 2 * (e : ℤ) ^ 2 + 140 * (d : ℤ) ^ 2 - 420 * d * e + 70)) 3).mp (by push_cast at hz ⊢; exact hz)
      exact_mod_cast this
    obtain ⟨t, ht⟩ := h3d
    refine ⟨1024 * (d : ℤ) ^ 4 * (e : ℤ) ^ 2 * t, ?_⟩
    have hne : (n : ℤ) = d * e := by exact_mod_cast he
    rw [hne, PA]
    linear_combination 248832 * (d : ℤ) ^ 4 * (e : ℤ) ^ 2 * ht
  obtain ⟨t, ht⟩ := hdiv
  have key : (27648 : ℤ) * (TauCong.tauPS n - (n : ℤ) ^ 2 * (σ 7 n : ℤ)) =
      729 * (165150720 * coeff n (Sk 1 ^ 2 * theta (Sk 1) ^ 2) - t) := by
    linear_combination -hk - ht + hsum
  generalize TauCong.tauPS n - (n : ℤ) ^ 2 * (σ 7 n : ℤ) = X at key ⊢
  generalize 165150720 * coeff n (Sk 1 ^ 2 * theta (Sk 1) ^ 2) - t = Y at key
  omega

lemma d256k : ∀ x y : ZMod 256, x.val % 2 = 1 → y.val % 2 = 1 →
    (x - y) ^ 2 * (x + y) * (x ^ 8 + x ^ 7 * y + 352 * x ^ 6 * y ^ 2 - 2483 * x ^ 5 * y ^ 3 + 4888 * x ^ 4 * y ^ 4 +
      1260 * x ^ 4 * y ^ 2 - 2483 * x ^ 3 * y ^ 5 - 3780 * x ^ 3 * y ^ 3 + 352 * x ^ 2 * y ^ 6 +
      1260 * x ^ 2 * y ^ 4 + 630 * x ^ 2 * y ^ 2 + x * y ^ 7 + y ^ 8) = 0 := by
  decide +kernel

lemma odd_of_dvd_odd {n d : ℕ} (hn : n % 2 = 1) (hd : d ∣ n) : ((d : ℤ) : ZMod 256).val % 2 = 1 := by
  rw [Int.cast_natCast, ZMod.val_natCast]
  have : d % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one d with h | h
    · exfalso; obtain ⟨e, rfl⟩ := hd; rw [Nat.mul_mod, h, zero_mul, Nat.zero_mod] at hn; omega
    · exact h
  omega

/-- **`τ(n) ≡ σ₁₁(n) (mod 2⁸)`** for odd `n`. -/
theorem tau_mod256_odd {n : ℕ} (hn : n ≠ 0) (hodd : n % 2 = 1) :
    (256 : ℤ) ∣ TauCong.tauPS n - (σ 11 n : ℤ) := by
  have hk := linA_coeff hn
  set g : ℕ → ℤ := fun d => PA n d + 27648 * (d : ℤ) ^ 11 with hg
  have hsum : ∑ d ∈ n.divisors, g d = ∑ d ∈ n.divisors, PA n d + 27648 * (σ 11 n : ℤ) := by
    rw [hg, Finset.sum_add_distrib, ← Finset.mul_sum, sigma_int_sum]
  have hpair : ∀ d ∈ n.divisors, (262144 : ℤ) ∣ g d + g (n / d) := by
    intro d hd
    have hdn := Nat.dvd_of_mem_divisors hd
    obtain ⟨e, he⟩ := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hq : n / d = e := by rw [he]; exact Nat.mul_div_cancel_left e hd0
    have hen : e ∣ n := ⟨d, by rw [he, mul_comm]⟩
    have h2 : (256 : ℤ) ∣ ((d : ℤ) - e) ^ 2 * ((d : ℤ) + e) * ((d : ℤ) ^ 8 + (d : ℤ) ^ 7 * e +
        352 * (d : ℤ) ^ 6 * (e : ℤ) ^ 2 - 2483 * (d : ℤ) ^ 5 * (e : ℤ) ^ 3 + 4888 * (d : ℤ) ^ 4 * (e : ℤ) ^ 4 +
        1260 * (d : ℤ) ^ 4 * (e : ℤ) ^ 2 - 2483 * (d : ℤ) ^ 3 * (e : ℤ) ^ 5 - 3780 * (d : ℤ) ^ 3 * (e : ℤ) ^ 3 +
        352 * (d : ℤ) ^ 2 * (e : ℤ) ^ 6 + 1260 * (d : ℤ) ^ 2 * (e : ℤ) ^ 4 + 630 * (d : ℤ) ^ 2 * (e : ℤ) ^ 2 +
        d * (e : ℤ) ^ 7 + (e : ℤ) ^ 8) := by
      have hz := d256k _ _ (odd_of_dvd_odd hodd hdn) (odd_of_dvd_odd hodd hen)
      suffices h : ((256 : ℕ) : ℤ) ∣ ((d : ℤ) - e) ^ 2 * ((d : ℤ) + e) * ((d : ℤ) ^ 8 + (d : ℤ) ^ 7 * e +
        352 * (d : ℤ) ^ 6 * (e : ℤ) ^ 2 - 2483 * (d : ℤ) ^ 5 * (e : ℤ) ^ 3 + 4888 * (d : ℤ) ^ 4 * (e : ℤ) ^ 4 +
        1260 * (d : ℤ) ^ 4 * (e : ℤ) ^ 2 - 2483 * (d : ℤ) ^ 3 * (e : ℤ) ^ 5 - 3780 * (d : ℤ) ^ 3 * (e : ℤ) ^ 3 +
        352 * (d : ℤ) ^ 2 * (e : ℤ) ^ 6 + 1260 * (d : ℤ) ^ 2 * (e : ℤ) ^ 4 + 630 * (d : ℤ) ^ 2 * (e : ℤ) ^ 2 +
        d * (e : ℤ) ^ 7 + (e : ℤ) ^ 8) by exact_mod_cast h
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 256).mp
      push_cast; exact hz
    obtain ⟨t, ht⟩ := h2
    refine ⟨27 * t, ?_⟩
    have hne : (n : ℤ) = d * e := by exact_mod_cast he
    rw [hq, hg]
    simp only
    rw [hne, PA, PA]
    linear_combination 27648 * ht
  have hdiag : ∀ d ∈ n.divisors, n / d = d → g d = 0 := by
    intro d hd h
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hne : (n : ℤ) = d * d := by
      have := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd); rw [h] at this; exact_mod_cast this.symm
    rw [hg]; simp only; rw [hne, PA]; ring
  have hdiv : (262144 : ℤ) ∣ ∑ d ∈ n.divisors, g d := by
    have hz : ((∑ d ∈ n.divisors, g d : ℤ) : ZMod 262144) = 0 := by
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
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 262144).mp hz
  obtain ⟨t, ht⟩ := hdiv
  have key : (27648 : ℤ) * (TauCong.tauPS n - (σ 11 n : ℤ)) =
      262144 * (459270 * coeff n (Sk 1 ^ 2 * theta (Sk 1) ^ 2) - t) := by
    linear_combination -hk - ht + hsum
  generalize TauCong.tauPS n - (σ 11 n : ℤ) = X at key ⊢
  generalize 459270 * coeff n (Sk 1 ^ 2 * theta (Sk 1) ^ 2) - t = Y at key
  omega

lemma sigma7_eq (n : ℕ) : sigma7 n = (σ 7 n : ℤ) := by rw [sigma_int_sum]; rfl
lemma sigma11_eq (n : ℕ) : sigma11 n = (σ 11 n : ℤ) := by rw [sigma_int_sum]; rfl

/-- The repo's hypothesis class `TauMod27`, now a theorem. -/
instance instTauMod27 : TauMod27 where
  congruence := by
    intro n hn h3
    rw [tau_eq_tauPS, sigma7_eq, Int.modEq_iff_dvd, ← neg_sub, dvd_neg]
    exact tau_mod27_coprime (by omega) h3

/-- The repo's hypothesis class `TauMod2_8`, now a theorem. -/
instance instTauMod2_8 : TauMod2_8 where
  congruence := by
    intro n hn hodd
    rw [tau_eq_tauPS, sigma11_eq, Int.modEq_iff_dvd, ← neg_sub, dvd_neg]
    exact tau_mod256_odd (by omega) (Nat.odd_iff.mp hodd)

end RamanujanTau.LehmerSmall

#print axioms RamanujanTau.LehmerSmall.tau_mod27_coprime
#print axioms RamanujanTau.LehmerSmall.tau_mod256_odd
#print axioms RamanujanTau.LehmerSmall.instTauMod27
#print axioms RamanujanTau.LehmerSmall.instTauMod2_8
