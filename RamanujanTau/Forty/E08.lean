/-
# Entry 3.8 (Type I: one product of two thetas split by one matrix exact cover; Cao, arXiv:2503.11445)
-/
import RamanujanTau.Forty.Tools

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm2 : 1 ≤ 2 := by norm_num
private lemma hm3 : 1 ≤ 3 := by norm_num
private lemma hm5 : 1 ≤ 5 := by norm_num
private lemma hm30 : 1 ≤ 30 := by norm_num

/-- Entry 3.8: `B = (1 3; -1 2)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B3_8 : ECS where
  b11 := 1
  b12 := 3
  b21 := (-1)
  b22 := 2
  r1 := 1
  r2 := 0
  I := {(-2), (-1), 0, 1, 2}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 1 * n - (-2)) % 5 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    ((2 * (m - 1 * ((1 * m + 1 * n - (-2)) % 5 + (-2))) - 3 * (n - 0 * ((1 * m + 1 * n - (-2)) % 5 + (-2)))) / 5), ((1 * (n - 0 * ((1 * m + 1 * n - (-2)) % 5 + (-2))) - (-1) * (m - 1 * ((1 * m + 1 * n - (-2)) % 5 + (-2)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L3_8 : θ hm2 1 1 * θ hm3 0 (-1) = 2 * (θ hm5 1 1 * θ hm30 12 1) - 2 * (mono 1 1 * (θ hm5 2 1 * θ hm30 6 1)) := by
  have h := θθ_lattice hm2 hm3 hm5 hm30 1 0 one_ne_zero (by norm_num : (-1 : ℂ) ≠ 0) B3_8 rfl rfl
    (by norm_num [B3_8]) (by norm_num [B3_8]) (by norm_num [B3_8])
  simp only [B3_8] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [c2] at h
  simp only [θ_nfr1 hm30 12 0 0 1 (e := 18) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm30 6 0 0 1 (e := 24) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm5 1 0 0 1 (e := 4) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm5 2 1 (-3) (-1) (e := 8) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm5 1 1 one_ne_zero (-1) (-1) (e := 6) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm30 0 (e := 0) (by norm_num), θz' hm5 0 (e := 0) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- the product form of `L3_8`: `(f(−q,−q⁴)f(−q¹²,−q¹⁸) − q f(−q²,−q³)f(−q⁶,−q²⁴)) (q³;q⁶) = f(−q,−q) (q⁶;q⁶)`. -/
theorem P3_8 : (J 1 5 * J 12 30 - PowerSeries.X * (J 2 5 * J 6 30)) * Pinf 3 6 = J 1 2 * Pinf 6 6 := by
  apply mul_left_cancel₀ two_ne
  apply ι_inj
  have h := congrArg (· * ι (Pinf 3 6)) L3_8
  simp only at h
  have hb := θ_bar0 (N := 3) hm3
  norm_num at hb
  rw [θu' hm5 1 (e' := 1) (by norm_num) (by norm_num) (by norm_num), θu' hm30 12 (e' := 12) (by norm_num) (by norm_num) (by norm_num),
    θu' hm5 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num), θu' hm30 6 (e' := 6) (by norm_num) (by norm_num) (by norm_num),
    θu' hm2 1 (e' := 1) (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [map_mul, map_sub, map_ofNat, ι_X]
  linear_combination -h + ι (J 1 2) * hb

/-- **Entry 3.8** (Rogers 1921): `G(q⁶)H(q) − qG(q)H(q⁶) = χ(−q)/χ(−q³)`. -/
theorem entry_3_8 : S 6 G * H - PowerSeries.X * G * S 6 H = chim 1 * Ring.inverse (chim 3) := by
  apply eq_mul_inv_of (isUnit_Pinf 3 6 (by norm_num) (by norm_num))
  have e1 := SG_E 6
  have e2 := SH_E 6
  norm_num at e1 e2
  have e3 := G_E
  have e4 := H_E
  have k : J 1 2 * Pinf 6 6 = Pinf 6 6 * Pinf 1 1 * Pinf 1 2 := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 2]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  apply mul_left_cancel₀ (mul_ne_zero (Pinf_ne 6 6 (by norm_num) (by norm_num)) (Pinf_ne 1 1 le_rfl le_rfl))
  simp only [chim, Nat.reduceMul]
  linear_combination Pinf 3 6 * ((H * Pinf 1 1) * e1 + J 12 30 * e4 - PowerSeries.X * (S 6 H * Pinf 6 6) * e3
      - PowerSeries.X * J 2 5 * e2) + P3_8 + k

end Forty
