/-
# Entry 3.31: `{G(q²)G(q³³) + q⁷H(q²)H(q³³)} / {G(q⁶⁶)H(q) − q¹³H(q⁶⁶)G(q)} = χ(−q³)/χ(−q¹¹)`

Berndt et al., Mem. AMS 188 (2007), §31: with `M, N` the numerator and denominator here and `T, U` those of Entry 3.32,
two `3 × 3` eliminations give (31.8) `N U = 1 − qW` (Entries 3.4 at `q, q⁶` and 3.8 at `q, q¹¹`) and (31.11)
`M T = −q + 1/W` (Entries 3.4 at `q², q³` and 3.7 at `q, q¹¹`), `W = χ(−q)χ(−q¹¹)/(χ(−q³)χ(−q³³))`. Each elimination
is a polynomial identity (`ring`). With Entry 3.32 (`entry_3_32`) this gives Entry 3.31.
-/
import RamanujanTau.Forty.E32
import RamanujanTau.Forty.E04
import RamanujanTau.Forty.E07
import RamanujanTau.Forty.E08

set_option autoImplicit false

namespace Forty
open PowerSeries
open RankProof (Pinf isUnit_Pinf)

private lemma ccH31 : constantCoeff H = 1 := by
  have h := congrArg constantCoeff H_mul_vv
  rw [map_mul, vv, map_mul, cc_Pinf 2 5 (by norm_num) (by norm_num), cc_Pinf 3 5 (by norm_num) (by norm_num), map_one] at h
  simpa using h

private lemma clear {a b c : PowerSeries ℤ} (hc : IsUnit c) (h : a = b * Ring.inverse c) : a * c = b := by
  rw [h, mul_assoc, Ring.inverse_mul_cancel _ hc, mul_one]

/-- (31.8), cleared: `N U χ(−q³)χ(−q³³) = χ(−q³)χ(−q³³) − q χ(−q)χ(−q¹¹)`. -/
theorem NU31 : (S 66 G * H - X ^ 13 * S 66 H * G) * (S 11 G * S 6 H - X * S 11 H * S 6 G) * (Pinf 3 6 * Pinf 33 66) =
    Pinf 3 6 * Pinf 33 66 - X * Pinf 11 22 * Pinf 1 2 := by
  have e4 := entry_3_4
  have e4s := congrArg (S 6) entry_3_4
  have e8 := clear (isUnit_Pinf 3 6 (by norm_num) (by norm_num)) entry_3_8
  have e8s := congrArg (S 11) e8
  simp only [chim, Nat.reduceMul] at e8 e8s
  simp only [map_mul, map_sub, map_pow, map_one, S_comp 6 11 66 (by norm_num), S_comp 11 6 66 (by norm_num),
    S_P' 11 3 6 (by norm_num) (by norm_num) (rfl : 33 = 11 * 3) (rfl : 66 = 11 * 6),
    S_P' 11 1 2 le_rfl (by norm_num) (rfl : 11 = 11 * 1) (rfl : 22 = 11 * 2),
    show S 6 X = X ^ 6 from RankProof.Ea_X 6 _, show S 11 X = X ^ 11 from RankProof.Ea_X 11 _] at e4s e8s
  have key : (S 66 G * H - X ^ 13 * S 66 H * G) * (S 11 G * S 6 H - X * S 11 H * S 6 G) =
      (S 66 G * S 6 H - (X ^ 6) ^ 2 * S 6 G * S 66 H) * (S 11 G * H - X ^ 2 * G * S 11 H)
        - X * (S 66 G * S 11 H - X ^ 11 * G * 0 - X ^ 11 * S 11 G * S 66 H) * (S 6 G * H - X * G * S 6 H) := by
    ring
  rw [e4, e4s] at key
  rw [key]
  linear_combination (-(X * (S 6 G * H - X * G * S 6 H) * Pinf 3 6)) * e8s - (X * Pinf 11 22) * e8

/-- (31.11), cleared: `M T χ(−q)χ(−q¹¹) = χ(−q³)χ(−q³³) − q χ(−q)χ(−q¹¹)`. -/
theorem MT31 : (S 2 G * S 33 G + X ^ 7 * S 2 H * S 33 H) * (S 3 G * S 22 G + X ^ 5 * S 3 H * S 22 H) *
      (Pinf 11 22 * Pinf 1 2) = Pinf 3 6 * Pinf 33 66 - X * Pinf 11 22 * Pinf 1 2 := by
  have e2 := congrArg (S 2) entry_3_4
  have e3 := congrArg (S 3) entry_3_4
  have e7 := clear (isUnit_Pinf 1 2 le_rfl (by norm_num)) entry_3_7
  have e7s := congrArg (S 11) e7
  simp only [chim, Nat.reduceMul] at e7 e7s
  simp only [map_mul, map_sub, map_add, map_pow, map_one, S_comp 2 11 22 (by norm_num), S_comp 3 11 33 (by norm_num),
    S_comp 11 2 22 (by norm_num), S_comp 11 3 33 (by norm_num),
    S_P' 11 3 6 (by norm_num) (by norm_num) (rfl : 33 = 11 * 3) (rfl : 66 = 11 * 6),
    S_P' 11 1 2 le_rfl (by norm_num) (rfl : 11 = 11 * 1) (rfl : 22 = 11 * 2),
    show S 2 X = X ^ 2 from RankProof.Ea_X 2 _, show S 3 X = X ^ 3 from RankProof.Ea_X 3 _,
    show S 11 X = X ^ 11 from RankProof.Ea_X 11 _] at e2 e3 e7s
  have key : (S 2 G * S 33 G + X ^ 7 * S 2 H * S 33 H) * (S 3 G * S 22 G + X ^ 5 * S 3 H * S 22 H) =
      (S 22 G * S 33 G + X ^ 11 * S 22 H * S 33 H) * (S 2 G * S 3 G + X * S 2 H * S 3 H)
        - X * (S 33 G * S 3 H - (X ^ 3) ^ 2 * S 3 G * S 33 H) * (S 22 G * S 2 H - (X ^ 2) ^ 2 * S 2 G * S 22 H) := by
    ring
  rw [e2, e3] at key
  rw [key]
  linear_combination ((S 2 G * S 3 G + X * S 2 H * S 3 H) * Pinf 1 2) * e7s + (Pinf 33 66) * e7

/-- **Entry 3.31** (Biagioli; here from Entry 3.32 and Berndt et al. §31):
`G(q²)G(q³³) + q⁷H(q²)H(q³³) = {G(q⁶⁶)H(q) − q¹³H(q⁶⁶)G(q)} χ(−q³)/χ(−q¹¹)`. -/
theorem entry_3_31 : S 2 G * S 33 G + X ^ 7 * S 2 H * S 33 H =
    (S 66 G * H - X ^ 13 * S 66 H * G) * chim 3 * Ring.inverse (chim 11) := by
  apply eq_mul_inv_of (isUnit_Pinf 11 22 (by norm_num) (by norm_num))
  simp only [chim, Nat.reduceMul]
  have h32 := clear (isUnit_Pinf 1 2 le_rfl (by norm_num)) entry_3_32
  simp only [chim, Nat.reduceMul] at h32
  have hNU := NU31
  have hMT := MT31
  set M := S 2 G * S 33 G + X ^ 7 * S 2 H * S 33 H
  set N := S 66 G * H - X ^ 13 * S 66 H * G
  set T := S 3 G * S 22 G + X ^ 5 * S 3 H * S 22 H
  set U := S 11 G * S 6 H - X * S 11 H * S 6 G
  have hU : U ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    simp only [U, map_sub, map_mul, cc_S, cc_G, ccH31, constantCoeff_X, map_zero] at this
    norm_num at this
  have hTU : T * Pinf 1 2 = U * Pinf 33 66 := by
    rw [h32]; ring
  have hz : U * Pinf 33 66 * (M * Pinf 11 22 - N * Pinf 3 6) = 0 := by
    linear_combination (-M) * (Pinf 11 22) * hTU + hMT - hNU
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd h (mul_ne_zero hU (Pinf_ne 33 66 (by norm_num) (by norm_num)))
  · linear_combination h

end Forty
