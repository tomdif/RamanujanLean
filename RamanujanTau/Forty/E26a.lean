/-
# The degree-11 modular equation behind Entries 3.26 and 3.27(i)

`φ(q)φ(q¹¹) − φ(−q)φ(−q¹¹) − 4q³ψ(q²)ψ(q²²) = 4q f(−q²)f(−q²²)`, i.e.
`χ²(q)χ²(q¹¹) − χ²(−q)χ²(−q¹¹) − 4q³/(χ²(−q²)χ²(−q²²)) = 4q` (`M26chi`).

This is the level-11 member of the family of Entries 3.17 and 3.18. It replaces Schröter's degree-11 modular
equation in Watson's proof of Entry 3.26 (Berndt et al. §29). The proof is the one of 3.17: the form of Entry 3.4,
`3x² + 2xy + 4y² + x + 4y` with sign `(−1)^x`, has an exact cover of determinant 3 (giving `2f(−q²)f(−q²²)`) and one
of determinant 4, `B = (0 −4; 1 1)`, whose cosets give `2ψ(q⁸)φ(q⁴⁴) − 2q²ψ(q²)ψ(q²²) + 2q¹⁰φ(q⁴)ψ(q⁸⁸)`
(`L3_26`, in `ℂ((t))` with `t = q`). The 2-dissection `φ(q) = φ(q⁴) + 2qψ(q⁸)` (`dis2`) finishes (`M3_26`).
-/
import RamanujanTau.Forty.E17
import RamanujanTau.Forty.E27

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm2 : 1 ≤ 2 := by norm_num
private lemma hm6 : 1 ≤ 6 := by norm_num
private lemma hm8 : 1 ≤ 8 := by norm_num
private lemma hm22 : 1 ≤ 22 := by norm_num
private lemma hm66 : 1 ≤ 66 := by norm_num
private lemma hm88 : 1 ≤ 88 := by norm_num

/-- Entry 3.26, side a: `B = (-1 1; 0 -3)`, shifts `i (0, 1)`, `i ∈ {(-2), (-1), 0}`. -/
def B3_26a : ECS where
  b11 := (-1)
  b12 := 1
  b21 := 0
  b22 := (-3)
  r1 := 0
  r2 := 1
  I := {(-2), (-1), 0}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-2)) % 3 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    (((-3) * (m - 0 * ((0 * m + 1 * n - (-2)) % 3 + (-2))) - 1 * (n - 1 * ((0 * m + 1 * n - (-2)) % 3 + (-2)))) / 3), (((-1) * (n - 1 * ((0 * m + 1 * n - (-2)) % 3 + (-2))) - 0 * (m - 0 * ((0 * m + 1 * n - (-2)) % 3 + (-2)))) / 3), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- Entry 3.26, side b: `B = (0 -4; 1 1)`, shifts `i (1, 0)`, `i ∈ {(-1), 0, 1, 2}`. -/
def B3_26b : ECS where
  b11 := 0
  b12 := (-4)
  b21 := 1
  b22 := 1
  r1 := 1
  r2 := 0
  I := {(-1), 0, 1, 2}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - (-1)) % 4 + (-1)), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 0 * n - (-1)) % 4 + (-1))) - (-4) * (n - 0 * ((1 * m + 0 * n - (-1)) % 4 + (-1)))) / 4), ((0 * (n - 0 * ((1 * m + 0 * n - (-1)) % 4 + (-1))) - 1 * (m - 1 * ((1 * m + 0 * n - (-1)) % 4 + (-1)))) / 4), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- Type II on `3x²+2xy+4y²+x+4y`, sign `(−1)^x`: covers of determinants 3 and 4. -/
theorem L3_26 : 2 * (θ hm6 2 1 * θ hm66 22 1) = (θ hm8 0 (-1) * θ hm88 44 (-1)) - 2 * (mono 2 1 * (θ hm8 2 (-1) * θ hm88 22 (-1))) + (mono 10 1 * (θ hm8 4 (-1) * θ hm88 0 (-1))) := by
  have h := qf_two 3 1 4 1 4 1 0 B3_26a B3_26b
    hm6 hm66 hm8 hm88 (by norm_num [B3_26a]) (by norm_num [B3_26a]) (by norm_num [B3_26a])
    (by norm_num [B3_26b]) (by norm_num [B3_26b]) (by norm_num [B3_26b])
  simp only [B3_26a, B3_26b] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm6 2 0 0 1 (e := 4) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm66 22 0 0 1 (e := 44) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm8 2 0 0 1 (e := 6) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm88 22 0 0 1 (e := 66) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm8 0 1 (by norm_num : (-1 : ℂ) ≠ 0) 0 1 (e := 8) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm8 2 1 (by norm_num : (-1 : ℂ) ≠ 0) (-2) 1 (e := 10) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm8 4 1 (by norm_num : (-1 : ℂ) ≠ 0) (-4) 1 (e := 12) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm6 1 (e := 6) (by norm_num), θz' hm66 1 (e := 66) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- `φ(q)φ(q¹¹) − φ(−q)φ(−q¹¹) − 4q³ψ(q²)ψ(q²²) = 4q f(−q²)f(−q²²)`, in `ℂ((t))`. -/
theorem M3_26 : θ hm2 1 (-1) * θ hm22 11 (-1) - θ hm2 1 1 * θ hm22 11 1
    - 4 * mono 3 1 * (θ hm8 2 (-1) * θ hm88 22 (-1)) = 4 * mono 1 1 * (θ hm6 2 1 * θ hm66 22 1) := by
  have hLat := L3_26
  have d1 := dis2 hm2 hm8 rfl 1 (by norm_num : (-1 : ℂ) ≠ 0) 4 0 1 (-1) 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have d2 := dis2 hm2 hm8 rfl 1 one_ne_zero 4 0 1 (-1) (-1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have d3 := dis2 hm22 hm88 rfl 11 (by norm_num : (-1 : ℂ) ≠ 0) 44 0 11 (-1) 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have d4 := dis2 hm22 hm88 rfl 11 one_ne_zero 44 0 11 (-1) (-1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [d1, d2, d3, d4, mono_neg1, mono_neg1]
  have m1 : (mono 1 1 : L) * mono 10 1 = mono 11 1 := by rw [mono_mul]; norm_num
  have m2 : (mono 1 1 : L) * mono 2 1 = mono 3 1 := by rw [mono_mul]; norm_num
  linear_combination (-2 * mono 1 1) * hLat
    - (2 * θ hm8 4 (-1) * θ hm88 0 (-1)) * m1 + (4 * θ hm8 2 (-1) * θ hm88 22 (-1)) * m2

private lemma J_ne26 (e N : ℕ) (h1 : 1 ≤ e) (h2 : e < N) : J e N ≠ 0 :=
  mul_ne_zero (mul_ne_zero (Pinf_ne e N h1 (by omega)) (Pinf_ne (N - e) N (by omega) (by omega)))
    (Pinf_ne N N (by omega) (by omega))

private lemma ι_ne26 {f : PowerSeries ℤ} (h : f ≠ 0) : ι f ≠ 0 := fun h0 => h (ι_inj (h0.trans (map_zero ι).symm))

local notation "φ" => RamanujanTau.Septic.phi

/-- the product form of `M3_26`. -/
theorem P3_26 : (φ * S 11 φ - J 1 2 * J 11 22) * (J 2 8 * J 22 88)
      - 4 * PowerSeries.X ^ 3 * ((J 4 16 * J 8 16) * (J 44 176 * J 88 176)) =
    4 * PowerSeries.X * (J 2 6 * J 22 66) * (J 2 8 * J 22 88) := by
  apply ι_inj
  have h := M3_26
  have hA := θ_bar hm2 1 le_rfl (by norm_num)
  have hB := θ_bar hm22 11 (by norm_num) (by norm_num)
  have hC := θ_bar hm8 2 (by norm_num) (by norm_num)
  have hD := θ_bar hm88 22 (by norm_num) (by norm_num)
  norm_num at hA hB hC hD
  have pA := congrArg ι phi_J
  have pB0 := congrArg (S 11) phi_J
  rw [map_mul, map_mul, S_J' 11 1 2 le_rfl (by norm_num) (rfl : 11 = 11 * 1) (rfl : 22 = 11 * 2),
    S_J' 11 2 4 (by norm_num) (by norm_num) (rfl : 22 = 11 * 2) (rfl : 44 = 11 * 4)] at pB0
  have pB := congrArg ι pB0
  simp only [map_mul] at hA hB hC hD pA pB
  have iA : θ hm2 1 (-1) = ι φ := by
    apply mul_right_cancel₀ (ι_ne26 (J_ne26 1 2 le_rfl (by norm_num)))
    rw [hA, pA]
  have iB : θ hm22 11 (-1) = ι (S 11 φ) := by
    apply mul_right_cancel₀ (ι_ne26 (J_ne26 11 22 (by norm_num) (by norm_num)))
    rw [hB, pB]
  rw [iA, iB, θu' hm2 1 (e' := 1) (by norm_num) le_rfl (by norm_num),
    θu' hm22 11 (e' := 11) (by norm_num) (by norm_num) (by norm_num),
    θu' hm6 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm66 22 (e' := 22) (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [map_mul, map_sub, map_add, map_pow, map_ofNat, ι_X, ι_Xpow] at h ⊢
  push_cast at h ⊢
  have m3 : (mono 1 1 : L) ^ 3 = mono 3 1 := by rw [mono, single_pow]; norm_num
  linear_combination (ι (J 2 8) * ι (J 22 88)) * h
    + 4 * mono 3 1 * (θ hm88 22 (-1) * ι (J 22 88)) * hC
    + 4 * mono 3 1 * (ι (J 4 16) * ι (J 8 16)) * hD
    - 4 * (ι (J 4 16) * ι (J 8 16) * ι (J 44 176) * ι (J 88 176)) * m3

/-- **The degree-11 modular equation** (`χ` form):
`(χ²(q)χ²(q¹¹) − χ²(−q)χ²(−q¹¹) − 4q) χ²(−q²)χ²(−q²²) = 4q³`. -/
theorem M26chi : (chip 1 ^ 2 * chip 11 ^ 2 - chim 1 ^ 2 * chim 11 ^ 2 - 4 * PowerSeries.X) * (chim 2 ^ 2 * chim 22 ^ 2) =
    4 * PowerSeries.X ^ 3 := by
  have hφ := phi_chip
  have hφ11 := congrArg (S 11) phi_chip
  rw [map_mul, map_pow, S11_chip1, S_P' 11 2 2 (by norm_num) (by norm_num) (rfl : 22 = 11 * 2) (rfl : 22 = 11 * 2)] at hφ11
  have hJ1 : J 1 2 = chim 1 ^ 2 * Pinf 2 2 := by simp only [J, chim, Nat.reduceMul, Nat.reduceSub]; ring
  have hJ11 : J 11 22 = chim 11 ^ 2 * Pinf 22 22 := by simp only [J, chim, Nat.reduceMul, Nat.reduceSub]; ring
  have k1 : J 4 16 * J 8 16 * Pinf 2 4 = Pinf 4 4 * J 2 8 := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 16]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  have k2 := congrArg (S 11) k1
  simp only [map_mul, S_J' 11 4 16 (by norm_num) (by norm_num) (rfl : 44 = 11 * 4) (rfl : 176 = 11 * 16),
    S_J' 11 8 16 (by norm_num) (by norm_num) (rfl : 88 = 11 * 8) (rfl : 176 = 11 * 16),
    S_J' 11 2 8 (by norm_num) (by norm_num) (rfl : 22 = 11 * 2) (rfl : 88 = 11 * 8),
    S_P' 11 2 4 (by norm_num) (by norm_num) (rfl : 22 = 11 * 2) (rfl : 44 = 11 * 4),
    S_P' 11 4 4 (by norm_num) (by norm_num) (rfl : 44 = 11 * 4) (rfl : 44 = 11 * 4)] at k2
  have a2 := atom 2 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have a22 := atom 22 22 44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [prod_range_succ, prod_range_zero, one_mul] at a2 a22
  norm_num at a2 a22
  have j6 : J 2 6 = Pinf 2 2 := by
    have a := atom 2 2 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simp only [prod_range_succ, prod_range_zero, one_mul] at a
    norm_num at a
    simp only [J, Nat.reduceSub]; rw [a]
  have j66 : J 22 66 = Pinf 22 22 := by
    have a := atom 22 22 66 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simp only [prod_range_succ, prod_range_zero, one_mul] at a
    norm_num at a
    simp only [J, Nat.reduceSub]; rw [a]
  have P := P3_26
  rw [hφ11, hφ, hJ1, hJ11, j6, j66] at P
  have hK : Pinf 2 2 * Pinf 22 22 * (J 2 8 * J 22 88) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Pinf_ne 2 2 (by norm_num) (by norm_num)) (Pinf_ne 22 22 (by norm_num) (by norm_num)))
      (mul_ne_zero (J_ne26 2 8 (by norm_num) (by norm_num)) (J_ne26 22 88 (by norm_num) (by norm_num)))
  apply mul_left_cancel₀ hK
  simp only [chim, Nat.reduceMul] at P ⊢
  rw [a2, a22] at P ⊢
  linear_combination (Pinf 2 4 ^ 2 * Pinf 22 44 ^ 2) * P
    + 4 * PowerSeries.X ^ 3 * (Pinf 2 4 * Pinf 22 44 * (J 44 176 * J 88 176 * Pinf 22 44)) * k1
    + 4 * PowerSeries.X ^ 3 * (Pinf 2 4 * Pinf 22 44 * Pinf 4 4 * J 2 8) * k2

/-- the degree-11 modular equation at `q²`:
`(χ²(q²)χ²(q²²) − χ²(−q²)χ²(−q²²) − 4q²) χ²(−q⁴)χ²(−q⁴⁴) = 4q⁶`. -/
theorem M26chi2 : (chip 2 ^ 2 * chip 22 ^ 2 - chim 2 ^ 2 * chim 22 ^ 2 - 4 * PowerSeries.X ^ 2) *
    (chim 4 ^ 2 * chim 44 ^ 2) = 4 * PowerSeries.X ^ 6 := by
  have h := congrArg (S 2) M26chi
  have c1 : S 2 (chip 1) = chip 2 := by rw [chip, chip, S_one]
  have c11 : S 2 (chip 11) = chip 22 := by rw [chip, chip, S_S 2 11 22 rfl]
  simp only [map_mul, map_sub, map_pow, map_ofNat, c1, c11, chim,
    show (S 2) PowerSeries.X = PowerSeries.X ^ 2 from RankProof.Ea_X 2 _,
    S_P' 2 1 2 le_rfl (by norm_num) (rfl : 2 = 2 * 1) (rfl : 4 = 2 * 2),
    S_P' 2 11 22 (by norm_num) (by norm_num) (rfl : 22 = 2 * 11) (rfl : 44 = 2 * 22),
    S_P' 2 2 4 (by norm_num) (by norm_num) (rfl : 4 = 2 * 2) (rfl : 8 = 2 * 4),
    S_P' 2 22 44 (by norm_num) (by norm_num) (rfl : 44 = 2 * 22) (rfl : 88 = 2 * 44)] at h
  simp only [chim, Nat.reduceMul]
  linear_combination h

end Forty
