/-
# Entry 3.2 (Type I: one product of two thetas split by one matrix exact cover; Cao, arXiv:2503.11445)
-/
import RamanujanTau.Forty.Tools

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm1 : 1 ≤ 1 := by norm_num
private lemma hm4 : 1 ≤ 4 := by norm_num
private lemma hm5 : 1 ≤ 5 := by norm_num
private lemma hm20 : 1 ≤ 20 := by norm_num

/-- Entry 3.2: `B = (1 4; -1 1)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B3_2 : ECS where
  b11 := 1
  b12 := 4
  b21 := (-1)
  b22 := 1
  r1 := 1
  r2 := 0
  I := {(-2), (-1), 0, 1, 2}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 1 * n - (-2)) % 5 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 1 * n - (-2)) % 5 + (-2))) - 4 * (n - 0 * ((1 * m + 1 * n - (-2)) % 5 + (-2)))) / 5), ((1 * (n - 0 * ((1 * m + 1 * n - (-2)) % 5 + (-2))) - (-1) * (m - 1 * ((1 * m + 1 * n - (-2)) % 5 + (-2)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L3_2 : θ hm1 0 (-1) * θ hm4 2 1 = 2 * (θ hm5 2 1 * θ hm20 8 1) + 2 * (mono 1 1 * (θ hm5 1 1 * θ hm20 4 1)) := by
  have h := θθ_lattice hm1 hm4 hm5 hm20 0 2 (by norm_num : (-1 : ℂ) ≠ 0) one_ne_zero B3_2 rfl rfl
    (by norm_num [B3_2]) (by norm_num [B3_2]) (by norm_num [B3_2])
  simp only [B3_2] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [c2] at h
  simp only [θ_nfr1 hm20 4 0 0 1 (e := 16) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 8 0 0 1 (e := 12) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm5 1 0 0 1 (e := 4) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm5 2 0 0 1 (e := 3) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm20 0 (e := 0) (by norm_num), θz' hm5 0 (e := 0) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- the product form of `L3_2`: `(f(−q²,−q³)f(−q⁸,−q¹²) + q f(−q,−q⁴)f(−q⁴,−q¹⁶)) (q;q²) = (q²;q²) f(−q²,−q²)`. -/
theorem P3_2 : (J 2 5 * J 8 20 + PowerSeries.X * (J 1 5 * J 4 20)) * Pinf 1 2 = Pinf 2 2 * J 2 4 := by
  apply mul_left_cancel₀ two_ne
  apply ι_inj
  have h := congrArg (· * ι (Pinf 1 2)) L3_2
  simp only at h
  have hb := θ_bar0 (N := 1) hm1
  norm_num at hb
  rw [θu' hm5 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num), θu' hm20 8 (e' := 8) (by norm_num) (by norm_num) (by norm_num),
    θu' hm5 1 (e' := 1) (by norm_num) (by norm_num) (by norm_num), θu' hm20 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm4 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [map_mul, map_add, map_ofNat, ι_X]
  linear_combination -h + ι (J 2 4) * hb

/-- **Entry 3.2** (Rogers 1921, Watson 1933): `G(q)G(q⁴) + qH(q)H(q⁴) = χ(q)²`. -/
theorem entry_3_2 : G * S 4 G + PowerSeries.X * H * S 4 H = chip 1 ^ 2 := by
  have hc := chip_mul 1
  norm_num at hc
  have e1 := SG_E 4
  have e2 := SH_E 4
  norm_num at e1 e2
  have e3 := G_E
  have e4 := H_E
  have k : Pinf 2 2 * J 2 4 * Pinf 1 2 = Pinf 2 4 ^ 2 * (Pinf 1 1 * Pinf 4 4) := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 4]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  have P := P3_2
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (Pinf_ne 1 1 le_rfl le_rfl) (Pinf_ne 4 4 (by norm_num) (by norm_num)))
    (pow_ne_zero 2 (Pinf_ne 1 2 le_rfl (by norm_num))))
  linear_combination Pinf 1 2 ^ 2 * ((S 4 G * Pinf 4 4) * e3 + J 2 5 * e1 + PowerSeries.X * (S 4 H * Pinf 4 4) * e4
      + PowerSeries.X * J 1 5 * e2) + Pinf 1 2 * P + k
    - Pinf 1 1 * Pinf 4 4 * (chip 1 * Pinf 1 2 + Pinf 2 4) * hc

end Forty
