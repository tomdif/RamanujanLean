/-
# Entry 3.15(i): `G(q³)G(q⁷) + q²H(q³)H(q⁷) = G(q²¹)H(q) − q⁴G(q)H(q²¹)`

Berndt et al. prove this entry only with modular forms (Biagioli). Here it follows from Entries 3.7–3.10 by two
`2 × 2` eliminations and one functional-equation argument.

Write `L₁(q) = G(q³)G(q⁷) + q²H(q³)H(q⁷)` and `L₂(q) = G(q²¹)H(q) − q⁴G(q)H(q²¹)`.
* Entry 3.7 at `q⁷` and Entry 3.9 at `q³` are two linear equations in `G(q²¹)`, `H(q²¹)`. Their determinant is
  `−q³L₁(q²)`, so Cramer's rule gives `L₂(q)L₁(q²)` as a combination of Entry 3.8 and Entry 3.10 (`elim15a`).
* Entry 3.7 at `q` and Entry 3.10 at `q³` are two linear equations in `G(q³)`, `H(q³)`. Their determinant is
  `−qL₂(q²)`, so `L₁(q)L₂(q²)` is a combination of Entry 3.8 at `q⁷` and Entry 3.9 (`elim15b`).
* Both products equal `u + q/u` with `u = χ(−q)χ(−q²¹)/(χ(−q³)χ(−q⁷))` (`prod15a`, `prod15b`). So
  `L₂(q)L₁(q²) = L₁(q)L₂(q²)`.
* With `D = L₁ − L₂` this reads `D(q)L₂(q²) = L₂(q)D(q²)`. Since `D(0) = 0`, comparing lowest coefficients gives
  `D = 0` (`eq_zero_of_S2`).
-/
import RamanujanTau.Forty.E07
import RamanujanTau.Forty.E08
import RamanujanTau.Forty.E09
import RamanujanTau.Forty.E10
import RamanujanTau.Forty.R11
import RamanujanTau.Forty.E20

set_option autoImplicit false

namespace Forty
open PowerSeries
open RankProof (Pinf isUnit_Pinf)

private lemma SX15 (a : ℕ) [NeZero a] : S a X = X ^ a := RankProof.Ea_X a _

private lemma clr {a b c : PowerSeries ℤ} (h : a = b * Ring.inverse c) (hc : IsUnit c) : a * c = b := by
  rw [h, mul_assoc, Ring.inverse_mul_cancel _ hc, mul_one]

/-- a power series `D` with `D(0) = 0` and `D(q)V(q) = U(q)D(q²)`, `V(0) = 1`, vanishes. -/
lemma eq_zero_of_S2 {D U V : PowerSeries ℤ} (h0 : constantCoeff D = 0) (hV : constantCoeff V = 1)
    (h : D * V = U * S 2 D) : D = 0 := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [map_zero]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [coeff_zero_eq_constantCoeff_apply]; exact h0
    have h1 := congrArg (coeff n) h
    rw [coeff_mul, coeff_mul] at h1
    have hL : ∑ p ∈ Finset.antidiagonal n, coeff p.1 D * coeff p.2 V = coeff n D := by
      rw [Finset.sum_eq_single_of_mem (n, 0) (Finset.mem_antidiagonal.mpr (by simp))]
      · rw [coeff_zero_eq_constantCoeff_apply, hV, mul_one]
      · intro p hp hne
        have hp' := Finset.mem_antidiagonal.mp hp
        have hlt : p.1 < n := by
          rcases p with ⟨a, b⟩
          simp only [ne_eq, Prod.mk.injEq] at hne hp' ⊢
          omega
        rw [ih p.1 hlt, map_zero, zero_mul]
    have hR : ∑ p ∈ Finset.antidiagonal n, coeff p.1 U * coeff p.2 (S 2 D) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hp' := Finset.mem_antidiagonal.mp hp
      rw [coeff_S]
      split_ifs with hd
      · rw [ih (p.2 / 2) (by omega), map_zero, mul_zero]
      · rw [mul_zero]
    rw [hL, hR] at h1
    exact h1

private lemma P_ne (b a : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a) : Pinf b a ≠ 0 := Pinf_ne b a hb ha

/-- Cramer's rule for `G(q²¹)`, `H(q²¹)` (Entries 3.7 at `q⁷`, 3.9 at `q³`, 3.8, 3.10):
`L₂(q)L₁(q²) χ(−q)χ(−q³)χ(−q⁷)χ(−q²¹) = χ²(−q)χ²(−q²¹) + qχ²(−q³)χ²(−q⁷)`. -/
theorem prod15a : (S 21 G * H - X ^ 4 * G * S 21 H) * (S 6 G * S 14 G + X ^ 4 * S 6 H * S 14 H) *
    (Pinf 1 2 * Pinf 3 6 * Pinf 7 14 * Pinf 21 42) =
      Pinf 1 2 ^ 2 * Pinf 21 42 ^ 2 + X * Pinf 3 6 ^ 2 * Pinf 7 14 ^ 2 := by
  -- Entry 3.7 at `q⁷`
  have E1 : (S 14 G * S 21 G + X ^ 7 * S 14 H * S 21 H) * Pinf 7 14 = Pinf 21 42 := by
    have h := congrArg (S 7) (clr entry_3_7 (isUnit_Pinf 1 2 le_rfl (by norm_num)))
    simp only [map_mul, map_add, map_pow, SX15, S_S 7 2 14 rfl, S_S 7 3 21 rfl, chim, Nat.reduceMul,
      S_P' 7 1 2 le_rfl (by norm_num) (rfl : 7 = 7 * 1) (rfl : 14 = 7 * 2),
      S_P' 7 3 6 (by norm_num) (by norm_num) (rfl : 21 = 7 * 3) (rfl : 42 = 7 * 6)] at h
    exact h
  -- Entry 3.8
  have E2 : (S 6 G * H - X * G * S 6 H) * Pinf 3 6 = Pinf 1 2 := by
    have h := clr entry_3_8 (isUnit_Pinf 3 6 (by norm_num) (by norm_num))
    simp only [chim, Nat.reduceMul] at h; exact h
  -- Entry 3.9 at `q³`
  have E3 : (S 21 G * S 6 H - X ^ 3 * S 6 G * S 21 H) * Pinf 21 42 = Pinf 3 6 := by
    have h := congrArg (S 3) (clr entry_3_9 (isUnit_Pinf 7 14 (by norm_num) (by norm_num)))
    simp only [map_mul, map_sub, map_pow, SX15, S_S 3 7 21 rfl, S_S 3 2 6 rfl, chim, Nat.reduceMul,
      S_P' 3 1 2 le_rfl (by norm_num) (rfl : 3 = 3 * 1) (rfl : 6 = 3 * 2),
      S_P' 3 7 14 (by norm_num) (by norm_num) (rfl : 21 = 3 * 7) (rfl : 42 = 3 * 14)] at h
    linear_combination h
  -- Entry 3.10
  have E4 : (G * S 14 G + X ^ 3 * H * S 14 H) * Pinf 1 2 = Pinf 7 14 := by
    have h := clr entry_3_10 (isUnit_Pinf 1 2 le_rfl (by norm_num))
    simp only [chim, Nat.reduceMul] at h; exact h
  linear_combination
    ((S 6 G * H - X * G * S 6 H) * Pinf 3 6 * Pinf 1 2 * Pinf 21 42) * E1
    + (Pinf 21 42 * Pinf 1 2 * Pinf 21 42) * E2
    + X * ((G * S 14 G + X ^ 3 * H * S 14 H) * Pinf 1 2 * Pinf 3 6 * Pinf 7 14) * E3
    + X * (Pinf 3 6 * Pinf 3 6 * Pinf 7 14) * E4

/-- Cramer's rule for `G(q³)`, `H(q³)` (Entries 3.7, 3.10 at `q³`, 3.8 at `q⁷`, 3.9):
`L₁(q)L₂(q²) χ(−q)χ(−q³)χ(−q⁷)χ(−q²¹) = χ²(−q)χ²(−q²¹) + qχ²(−q³)χ²(−q⁷)`. -/
theorem prod15b : (S 3 G * S 7 G + X ^ 2 * S 3 H * S 7 H) * (S 42 G * S 2 H - X ^ 8 * S 2 G * S 42 H) *
    (Pinf 1 2 * Pinf 3 6 * Pinf 7 14 * Pinf 21 42) =
      Pinf 1 2 ^ 2 * Pinf 21 42 ^ 2 + X * Pinf 3 6 ^ 2 * Pinf 7 14 ^ 2 := by
  -- Entry 3.7
  have E5 : (S 2 G * S 3 G + X * S 2 H * S 3 H) * Pinf 1 2 = Pinf 3 6 := by
    have h := clr entry_3_7 (isUnit_Pinf 1 2 le_rfl (by norm_num))
    simp only [chim, Nat.reduceMul] at h; exact h
  -- Entry 3.8 at `q⁷`
  have E6 : (S 42 G * S 7 H - X ^ 7 * S 7 G * S 42 H) * Pinf 21 42 = Pinf 7 14 := by
    have h := congrArg (S 7) (clr entry_3_8 (isUnit_Pinf 3 6 (by norm_num) (by norm_num)))
    simp only [map_mul, map_sub, map_pow, SX15, S_S 7 6 42 rfl, chim, Nat.reduceMul,
      S_P' 7 1 2 le_rfl (by norm_num) (rfl : 7 = 7 * 1) (rfl : 14 = 7 * 2),
      S_P' 7 3 6 (by norm_num) (by norm_num) (rfl : 21 = 7 * 3) (rfl : 42 = 7 * 6)] at h
    linear_combination h
  -- Entry 3.10 at `q³`
  have E7 : (S 3 G * S 42 G + X ^ 9 * S 3 H * S 42 H) * Pinf 3 6 = Pinf 21 42 := by
    have h := congrArg (S 3) (clr entry_3_10 (isUnit_Pinf 1 2 le_rfl (by norm_num)))
    simp only [map_mul, map_add, map_pow, SX15, S_S 3 14 42 rfl, chim, Nat.reduceMul,
      S_P' 3 1 2 le_rfl (by norm_num) (rfl : 3 = 3 * 1) (rfl : 6 = 3 * 2),
      S_P' 3 7 14 (by norm_num) (by norm_num) (rfl : 21 = 3 * 7) (rfl : 42 = 3 * 14)] at h
    linear_combination h
  -- Entry 3.9
  have E8 : (S 7 G * S 2 H - X * S 2 G * S 7 H) * Pinf 7 14 = Pinf 1 2 := by
    have h := clr entry_3_9 (isUnit_Pinf 7 14 (by norm_num) (by norm_num))
    simp only [chim, Nat.reduceMul] at h; exact h
  linear_combination
    X * ((S 42 G * S 7 H - X ^ 7 * S 7 G * S 42 H) * Pinf 21 42 * Pinf 3 6 * Pinf 7 14) * E5
    + X * (Pinf 3 6 * Pinf 3 6 * Pinf 7 14) * E6
    + ((S 7 G * S 2 H - X * S 2 G * S 7 H) * Pinf 7 14 * Pinf 1 2 * Pinf 21 42) * E7
    + (Pinf 21 42 * Pinf 1 2 * Pinf 21 42) * E8

private lemma cc_H15 : constantCoeff H = 1 := cc_H

/-- **Entry 3.15(i)** (Ramanujan; Biagioli): `G(q³)G(q⁷) + q²H(q³)H(q⁷) = G(q²¹)H(q) − q⁴G(q)H(q²¹)`. -/
theorem entry_3_15_i : S 3 G * S 7 G + X ^ 2 * S 3 H * S 7 H = S 21 G * H - X ^ 4 * G * S 21 H := by
  set L1 := S 3 G * S 7 G + X ^ 2 * S 3 H * S 7 H with hL1
  set L2 := S 21 G * H - X ^ 4 * G * S 21 H with hL2
  have hS1 : S 2 L1 = S 6 G * S 14 G + X ^ 4 * S 6 H * S 14 H := by
    simp only [hL1, map_add, map_mul, map_pow, SX15, S_S 2 3 6 rfl, S_S 2 7 14 rfl]; ring
  have hS2 : S 2 L2 = S 42 G * S 2 H - X ^ 8 * S 2 G * S 42 H := by
    simp only [hL2, map_sub, map_mul, map_pow, SX15, S_S 2 21 42 rfl]; ring
  have a := prod15a
  have b := prod15b
  rw [← hL2, ← hS1] at a
  rw [← hL1, ← hS2] at b
  clear_value L1 L2
  have hPi : Pinf 1 2 * Pinf 3 6 * Pinf 7 14 * Pinf 21 42 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (P_ne 1 2 le_rfl (by norm_num)) (P_ne 3 6 (by norm_num) (by norm_num)))
      (P_ne 7 14 (by norm_num) (by norm_num))) (P_ne 21 42 (by norm_num) (by norm_num))
  have key : L2 * S 2 L1 = L1 * S 2 L2 := by
    apply mul_right_cancel₀ hPi
    linear_combination a - b
  have hD : (L1 - L2) * S 2 L2 = L2 * S 2 (L1 - L2) := by
    rw [map_sub]; linear_combination -key
  have c1 : constantCoeff L1 = 1 := by
    simp [hL1, map_add, map_mul, cc_S, cc_G, cc_H15]
  have c2 : constantCoeff L2 = 1 := by
    simp [hL2, map_sub, map_mul, cc_S, cc_G, cc_H15]
  have h0 : constantCoeff (L1 - L2) = 0 := by rw [map_sub, c1, c2, sub_self]
  have hV : constantCoeff (S 2 L2) = 1 := by rw [cc_S, c2]
  have := eq_zero_of_S2 h0 hV hD
  exact sub_eq_zero.mp this

end Forty
