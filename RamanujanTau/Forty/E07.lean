/-
# Entry 3.7 (Type I: one product of two thetas split by one matrix exact cover; Cao, arXiv:2503.11445)
-/
import RamanujanTau.Forty.Tools

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

/-- the ECS `B = (2 3; −1 1)`, `I = {−2,…,2}`. -/
def B7 : ECS where
  b11 := 2
  b12 := 3
  b21 := -1
  b22 := 1
  r1 := 1
  r2 := 0
  I := {-2, -1, 0, 1, 2}
  det_ne := by norm_num
  cover := fun m n => ⟨(m + 2 * n + 2) % 5 - 2, by simp only [mem_insert, mem_singleton]; omega,
    (m + 2 * n - ((m + 2 * n + 2) % 5 - 2)) / 5 - n, (m + 2 * n - ((m + 2 * n + 2) % 5 - 2)) / 5, by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

lemma h6 : 1 ≤ 6 := by norm_num
lemma h10 : 1 ≤ 10 := by norm_num
lemma h15 : 1 ≤ 15 := by norm_num

/-! ## Entry 3.7 -/

/-- Cao's form of Entry 3.7: `f(1,q) f(−q³,−q³) = 2 f(−q⁴,−q⁶)f(−q⁶,−q⁹) + 2q f(−q²,−q⁸)f(−q³,−q¹²)`. -/
theorem L7 : θ one_le_one' 0 (-1) * θ h6 3 1 = 2 * (θ h10 4 1 * θ h15 6 1) + 2 * (mono 1 1 * (θ h10 2 1 * θ h15 3 1)) := by
  rw [θθ_lattice one_le_one' h6 h10 h15 0 3 (by norm_num) one_ne_zero B7 rfl rfl (by norm_num [B7]) (by norm_num [B7])
    (by norm_num [B7])]
  simp only [B7]
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
  norm_num [c2]
  rw [θ_zero_pt h10, θ_refl1 h10 4 6 (by norm_num), θ_refl1 h15 6 9 (by norm_num), θ_refl1 h10 2 8 (by norm_num),
    θ_refl1 h15 3 12 (by norm_num)]
  ring

/-- `Θ₇`: the product form of `L7` in `ℤ⟦q⟧`. -/
theorem P7 : (2 * (J 4 10 * J 6 15) + 2 * (PowerSeries.X * (J 2 10 * J 3 15))) * Pinf 1 2 = 2 * Pinf 2 2 * J 3 6 := by
  apply ι_inj
  have h := congrArg (· * ι (Pinf 1 2)) L7
  simp only at h
  have hb := θ_bar0 (N := 1) one_le_one'
  norm_num at hb
  rw [θu' h10 4 (by norm_num) (by norm_num) (by norm_num), θu' h15 6 (by norm_num) (by norm_num) (by norm_num),
    θu' h10 2 (by norm_num) (by norm_num) (by norm_num), θu' h15 3 (by norm_num) (by norm_num) (by norm_num),
    θu' h6 3 (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [map_mul, map_add, map_ofNat, ι_X]
  linear_combination -h + ι (J 3 6) * hb

/-- **Entry 3.7** (Rogers 1921): `G(q²)G(q³) + qH(q²)H(q³) = χ(−q³)/χ(−q)`. -/
theorem entry_3_7 : S 2 G * S 3 G + PowerSeries.X * S 2 H * S 3 H = chim 3 * Ring.inverse (chim 1) := by
  have hu : IsUnit (chim 1) := isUnit_Pinf 1 2 le_rfl (by norm_num)
  apply eq_mul_inv_of hu
  refine two_term (SG_mul 2) (SG_mul 3) (SH_mul 2) (SH_mul 3) ?_
  have hE : (2 * Pinf 10 10 * Pinf 15 15 : PowerSeries ℤ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne (isUnit_Pinf 10 10 (by norm_num) (by norm_num)).ne_zero)
      (isUnit_Pinf 15 15 (by norm_num) (by norm_num)).ne_zero
  apply mul_left_cancel₀ hE
  have P := P7
  simp only [J, chim] at P ⊢
  simp only [Nat.reduceMul, Nat.reduceSub] at P ⊢
  simp (disch := norm_num) only [atom _ _ 30] at P ⊢
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd,
    Nat.reduceDiv, mul_zero, add_zero, mul_one] at P ⊢
  linear_combination P

end Forty
