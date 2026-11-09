/-
# `G(−q)`, `H(−q)` as products

`Ng_mul_odd`: `(−q^c;q^M)_∞ (q^c;q^M)_∞ = (q^{2c};q^{2M})_∞` for `c` odd and `M` even.
`NgG_prod`: `G(−q) (q²;q²⁰)(q⁶;q¹⁰)(q⁴;q¹⁰)(q¹⁸;q²⁰) = (q;q¹⁰)(q⁹;q¹⁰)`.
`NgH_prod`: `H(−q) (q²;q¹⁰)(q⁸;q¹⁰)(q¹⁴;q²⁰)(q⁶;q²⁰) = (q⁷;q¹⁰)(q³;q¹⁰)`.
-/
import RamanujanTau.Forty.NgTools

set_option autoImplicit false

namespace Forty
open PowerSeries Finset
open RankProof (Pinf Pfin Pinf_ext X_pow_dvd_Pinf_sub isUnit_Pinf)

lemma Ng_Pfin_mul_odd (c M : ℕ) (hc : Odd c) (hM : Even M) (K : ℕ) :
    Ng (Pfin c M K) * Pfin c M K = Pfin (2 * c) (2 * M) K := by
  simp only [Pfin, map_prod, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  have hodd : Odd (c + M * i) := hc.add_even (hM.mul_right i)
  rw [map_sub, map_one, map_pow, Ng, rescale_X, mul_pow, ← map_pow, hodd.neg_one_pow]
  simp only [map_neg, map_one, neg_one_mul]
  rw [show 2 * c + 2 * M * i = 2 * (c + M * i) by ring, pow_mul]
  ring

/-- `(−q^c;q^M)(q^c;q^M) = (q^{2c};q^{2M})` for `c` odd, `M` even. -/
theorem Ng_mul_odd (c M : ℕ) (hc : Odd c) (hM : Even M) (hM1 : 1 ≤ M) :
    Ng (Pinf c M) * Pinf c M = Pinf (2 * c) (2 * M) := by
  have hc1 : 1 ≤ c := hc.pos
  refine Pinf_ext (by omega) (by omega) fun N => ?_
  have h1 := X_pow_dvd_Pinf_sub c M hc1 hM1 N
  rw [← Ng_Pfin_mul_odd c M hc hM N,
    show Ng (Pinf c M) * Pinf c M - Ng (Pfin c M N) * Pfin c M N
      = Ng (Pinf c M) * (Pinf c M - Pfin c M N) + Ng (Pinf c M - Pfin c M N) * Pfin c M N by
        rw [map_sub]; ring]
  exact dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_left (Ng_X_pow_dvd h1) _)

lemma Pinf_split' (b a : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a) {a2 b2 : ℕ} (h1 : a2 = 2 * a) (h2 : b2 = b + a) :
    Pinf b a = Pinf b a2 * Pinf b2 a2 := by
  subst h1 h2; exact RankProof.Pinf_split b a hb ha

private lemma ev (b a : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a) {b' a' : ℕ} (h1 : b' = 2 * b) (h2 : a' = 2 * a) :
    Ng (Pinf b' a') = Pinf b' a' := by subst h1 h2; exact Ng_Pinf_even b a hb ha

private lemma od (c M : ℕ) (hc : Odd c) (hM : Even M) (hM1 : 1 ≤ M) {c' M' : ℕ} (h1 : c' = 2 * c) (h2 : M' = 2 * M) :
    Ng (Pinf c M) * Pinf c M = Pinf c' M' := by subst h1 h2; exact Ng_mul_odd c M hc hM hM1

/-- `G(−q)` as a product quotient. -/
theorem NgG_prod : Ng G * (Pinf 2 20 * Pinf 6 10 * Pinf 4 10 * Pinf 18 20) = Pinf 1 10 * Pinf 9 10 := by
  have hG := congrArg Ng G_mul_uu
  rw [map_mul, map_one, uu, map_mul, Pinf_split' 1 5 le_rfl (by norm_num) (rfl : 10 = 2 * 5) rfl,
    Pinf_split' 4 5 (by norm_num) (by norm_num) (rfl : 10 = 2 * 5) rfl, map_mul, map_mul,
    ev 3 5 (by norm_num) (by norm_num) (rfl : 6 = 2 * 3) rfl, ev 2 5 (by norm_num) (by norm_num) (rfl : 4 = 2 * 2) rfl] at hG
  norm_num at hG
  have o1 := od 1 10 (by decide) (by decide) (by norm_num) (rfl : 2 = 2 * 1) (rfl : 20 = 2 * 10)
  have o9 := od 9 10 (by decide) (by decide) (by norm_num) (rfl : 18 = 2 * 9) (rfl : 20 = 2 * 10)
  linear_combination (Pinf 1 10 * Pinf 9 10) * hG - (Ng G * Pinf 6 10 * Pinf 4 10 * Ng (Pinf 1 10) * Pinf 1 10) * o9
    - (Ng G * Pinf 6 10 * Pinf 4 10 * Pinf 18 20) * o1

/-- `H(−q)` as a product quotient. -/
theorem NgH_prod : Ng H * (Pinf 2 10 * Pinf 8 10 * Pinf 14 20 * Pinf 6 20) = Pinf 7 10 * Pinf 3 10 := by
  have hH := congrArg Ng H_mul_vv
  rw [map_mul, map_one, vv, map_mul, Pinf_split' 2 5 (by norm_num) (by norm_num) (rfl : 10 = 2 * 5) rfl,
    Pinf_split' 3 5 (by norm_num) (by norm_num) (rfl : 10 = 2 * 5) rfl, map_mul, map_mul,
    ev 1 5 le_rfl (by norm_num) (rfl : 2 = 2 * 1) rfl, ev 4 5 (by norm_num) (by norm_num) (rfl : 8 = 2 * 4) rfl] at hH
  norm_num at hH
  have o7 := od 7 10 (by decide) (by decide) (by norm_num) (rfl : 14 = 2 * 7) (rfl : 20 = 2 * 10)
  have o3 := od 3 10 (by decide) (by decide) (by norm_num) (rfl : 6 = 2 * 3) (rfl : 20 = 2 * 10)
  linear_combination (Pinf 7 10 * Pinf 3 10) * hH - (Ng H * Pinf 2 10 * Pinf 8 10 * Ng (Pinf 7 10) * Pinf 7 10) * o3
    - (Ng H * Pinf 2 10 * Pinf 8 10 * Pinf 6 20) * o7

end Forty
