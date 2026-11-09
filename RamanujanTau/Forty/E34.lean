/-
# Entry 3.34 (Bressoud; Berndt et al. §33)

`{G(q)G(−q¹⁹) − q⁴H(q)H(−q¹⁹)}{G(−q)G(q¹⁹) − q⁴H(−q)H(q¹⁹)} = G(q²)G(q³⁸) + q⁸H(q²)H(q³⁸)`.

Route (Berndt et al. §33, a modification of Bressoud's proof):
* (33.1) `G(q)G(−q) f(−q²) = f(q⁴,q⁶)`, `H(q)H(−q) f(−q²) = f(q²,q⁸)` (`F1_J`, `F2_J`, product manipulations with
  `NgG_prod`, `NgH_prod`);
* (33.2) `G(q)H(−q) f(−q²) = ψ(q²) + qψ(q¹⁰)`, `G(−q)H(q) f(−q²) = ψ(q²) − qψ(q¹⁰)` (Entries 3.20 + 3.21, `K1_eq`,
  `K2_eq`);
* this reduces 3.34 to the four-product theta identity (33.6), proved in `ℂ((t))` (`L33_6`) from
  - (33.7) = `M3_17` (Entry 3.17 at `q²`, Cao's Type II proof);
  - (20.5): the 20-coset Type I cover `B = (1 −19; 1 1)` of `φ(q)φ(q¹⁹)` and of `φ(−q)φ(−q¹⁹)` (`L34a`, `L34b`);
  - (20.6) at `−q²`: `ψ(q²)ψ(q³⁸)` as five products. The memoir uses its Theorem 4.14; here it is a Type II
    identity for the form `4x² + 4xy + 20y² + 2x − 18y` with covers `(1 1; 0 −2)` (det 2) and `(0 10; 1 −1)`
    (det 10) (`L34d`);
  - the 2-dissections (33.10) (`dis2`).
-/
import RamanujanTau.Forty.E17
import RamanujanTau.Forty.E20
import RamanujanTau.Forty.NgOdd

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm2 : 1 ≤ 2 := by norm_num
private lemma hm8 : 1 ≤ 8 := by norm_num
private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm38 : 1 ≤ 38 := by norm_num
private lemma hm40 : 1 ≤ 40 := by norm_num
private lemma hm152 : 1 ≤ 152 := by norm_num
private lemma hm190 : 1 ≤ 190 := by norm_num
private lemma hm760 : 1 ≤ 760 := by norm_num

/-- Entry 34a: `B = (1 -19; 1 1)`, shifts `i (1, 0)`, `i ∈ {(-9), (-8), (-7), (-6), (-5), (-4), (-3), (-2), (-1), 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}`. -/
def B34a : ECS where
  b11 := 1
  b12 := (-19)
  b21 := 1
  b22 := 1
  r1 := 1
  r2 := 0
  I := {(-9), (-8), (-7), (-6), (-5), (-4), (-3), (-2), (-1), 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 19 * n - (-9)) % 20 + (-9)), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 19 * n - (-9)) % 20 + (-9))) - (-19) * (n - 0 * ((1 * m + 19 * n - (-9)) % 20 + (-9)))) / 20), ((1 * (n - 0 * ((1 * m + 19 * n - (-9)) % 20 + (-9))) - 1 * (m - 1 * ((1 * m + 19 * n - (-9)) % 20 + (-9)))) / 20), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L34a : θ hm2 1 (-1) * θ hm38 19 (-1) = (θ hm40 20 (-1) * θ hm760 380 (-1)) + 2 * (mono 1 1 * (θ hm40 18 (-1) * θ hm760 342 (-1))) + 2 * (mono 4 1 * (θ hm40 16 (-1) * θ hm760 304 (-1))) + 2 * (mono 9 1 * (θ hm40 14 (-1) * θ hm760 266 (-1))) + 2 * (mono 16 1 * (θ hm40 12 (-1) * θ hm760 228 (-1))) + 2 * (mono 25 1 * (θ hm40 10 (-1) * θ hm760 190 (-1))) + 2 * (mono 36 1 * (θ hm40 8 (-1) * θ hm760 152 (-1))) + 2 * (mono 49 1 * (θ hm40 6 (-1) * θ hm760 114 (-1))) + 2 * (mono 64 1 * (θ hm40 4 (-1) * θ hm760 76 (-1))) + 2 * (mono 81 1 * (θ hm40 2 (-1) * θ hm760 38 (-1))) + (mono 100 1 * (θ hm40 0 (-1) * θ hm760 0 (-1))) := by
  have h := θθ_lattice hm2 hm38 hm40 hm760 1 19 (by norm_num : (-1 : ℂ) ≠ 0) (by norm_num : (-1 : ℂ) ≠ 0) B34a rfl rfl
    (by norm_num [B34a]) (by norm_num [B34a]) (by norm_num [B34a])
  simp only [B34a] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [c2] at h
  simp only [θ_nfrm hm40 10 0 0 1 (e := 30) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 12 0 0 1 (e := 28) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 14 0 0 1 (e := 26) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 16 0 0 1 (e := 24) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 18 0 0 1 (e := 22) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 2 0 0 1 (e := 38) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 4 0 0 1 (e := 36) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 6 0 0 1 (e := 34) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 8 0 0 1 (e := 32) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 114 0 0 1 (e := 646) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 152 0 0 1 (e := 608) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 190 0 0 1 (e := 570) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 228 0 0 1 (e := 532) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 266 0 0 1 (e := 494) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 304 0 0 1 (e := 456) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 342 0 0 1 (e := 418) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 38 0 0 1 (e := 722) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 76 0 0 1 (e := 684) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm40 0 1 (by norm_num : (-1 : ℂ) ≠ 0) 0 1 (e := 40) (by norm_num) (by norm_num [c2]) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- Entry 34b: `B = (1 -19; 1 1)`, shifts `i (1, 0)`, `i ∈ {(-9), (-8), (-7), (-6), (-5), (-4), (-3), (-2), (-1), 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}`. -/
def B34b : ECS where
  b11 := 1
  b12 := (-19)
  b21 := 1
  b22 := 1
  r1 := 1
  r2 := 0
  I := {(-9), (-8), (-7), (-6), (-5), (-4), (-3), (-2), (-1), 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 19 * n - (-9)) % 20 + (-9)), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 19 * n - (-9)) % 20 + (-9))) - (-19) * (n - 0 * ((1 * m + 19 * n - (-9)) % 20 + (-9)))) / 20), ((1 * (n - 0 * ((1 * m + 19 * n - (-9)) % 20 + (-9))) - 1 * (m - 1 * ((1 * m + 19 * n - (-9)) % 20 + (-9)))) / 20), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L34b : θ hm2 1 1 * θ hm38 19 1 = (θ hm40 20 (-1) * θ hm760 380 (-1)) - 2 * (mono 1 1 * (θ hm40 18 (-1) * θ hm760 342 (-1))) + 2 * (mono 4 1 * (θ hm40 16 (-1) * θ hm760 304 (-1))) - 2 * (mono 9 1 * (θ hm40 14 (-1) * θ hm760 266 (-1))) + 2 * (mono 16 1 * (θ hm40 12 (-1) * θ hm760 228 (-1))) - 2 * (mono 25 1 * (θ hm40 10 (-1) * θ hm760 190 (-1))) + 2 * (mono 36 1 * (θ hm40 8 (-1) * θ hm760 152 (-1))) - 2 * (mono 49 1 * (θ hm40 6 (-1) * θ hm760 114 (-1))) + 2 * (mono 64 1 * (θ hm40 4 (-1) * θ hm760 76 (-1))) - 2 * (mono 81 1 * (θ hm40 2 (-1) * θ hm760 38 (-1))) + (mono 100 1 * (θ hm40 0 (-1) * θ hm760 0 (-1))) := by
  have h := θθ_lattice hm2 hm38 hm40 hm760 1 19 one_ne_zero one_ne_zero B34b rfl rfl
    (by norm_num [B34b]) (by norm_num [B34b]) (by norm_num [B34b])
  simp only [B34b] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [c2] at h
  simp only [θ_nfrm hm40 10 0 0 1 (e := 30) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 12 0 0 1 (e := 28) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 14 0 0 1 (e := 26) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 16 0 0 1 (e := 24) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 18 0 0 1 (e := 22) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 2 0 0 1 (e := 38) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 4 0 0 1 (e := 36) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 6 0 0 1 (e := 34) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 8 0 0 1 (e := 32) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 114 0 0 1 (e := 646) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 152 0 0 1 (e := 608) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 190 0 0 1 (e := 570) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 228 0 0 1 (e := 532) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 266 0 0 1 (e := 494) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 304 0 0 1 (e := 456) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 342 0 0 1 (e := 418) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 38 0 0 1 (e := 722) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 76 0 0 1 (e := 684) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm40 0 1 (by norm_num : (-1 : ℂ) ≠ 0) 0 1 (e := 40) (by norm_num) (by norm_num [c2]) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- Entry 34d, side a: `B = (1 1; 0 -2)`, shifts `i (0, 1)`, `i ∈ {0, 1}`. -/
def B34da : ECS where
  b11 := 1
  b12 := 1
  b21 := 0
  b22 := (-2)
  r1 := 0
  r2 := 1
  I := {0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - 0) % 2 + 0), by simp only [mem_insert, mem_singleton]; omega,
    (((-2) * (m - 0 * ((0 * m + 1 * n - 0) % 2 + 0)) - 1 * (n - 1 * ((0 * m + 1 * n - 0) % 2 + 0))) / (-2)), ((1 * (n - 1 * ((0 * m + 1 * n - 0) % 2 + 0)) - 0 * (m - 0 * ((0 * m + 1 * n - 0) % 2 + 0))) / (-2)), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- Entry 34d, side b: `B = (0 10; 1 -1)`, shifts `i (1, 0)`, `i ∈ {(-4), (-3), (-2), (-1), 0, 1, 2, 3, 4, 5}`. -/
def B34db : ECS where
  b11 := 0
  b12 := 10
  b21 := 1
  b22 := (-1)
  r1 := 1
  r2 := 0
  I := {(-4), (-3), (-2), (-1), 0, 1, 2, 3, 4, 5}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - (-4)) % 10 + (-4)), by simp only [mem_insert, mem_singleton]; omega,
    (((-1) * (m - 1 * ((1 * m + 0 * n - (-4)) % 10 + (-4))) - 10 * (n - 0 * ((1 * m + 0 * n - (-4)) % 10 + (-4)))) / (-10)), ((0 * (n - 0 * ((1 * m + 0 * n - (-4)) % 10 + (-4))) - 1 * (m - 1 * ((1 * m + 0 * n - (-4)) % 10 + (-4)))) / (-10)), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L34d : 2 * (θ hm8 2 (-1) * θ hm152 38 (-1)) = 2 * (θ hm40 2 (-1) * θ hm760 342 (-1)) + 2 * (mono 6 1 * (θ hm40 6 (-1) * θ hm760 266 (-1))) + 2 * (mono 20 1 * (θ hm40 10 (-1) * θ hm760 190 (-1))) + 2 * (mono 42 1 * (θ hm40 14 (-1) * θ hm760 114 (-1))) + 2 * (mono 72 1 * (θ hm40 18 (-1) * θ hm760 38 (-1))) := by
  have h := qf_two 4 2 20 2 (-18) 0 0 B34da B34db
    hm8 hm152 hm40 hm760 (by norm_num [B34da]) (by norm_num [B34da]) (by norm_num [B34da])
    (by norm_num [B34db]) (by norm_num [B34db]) (by norm_num [B34db])
  simp only [B34da, B34db] at h
  rw [sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfrm hm152 38 0 0 1 (e := 114) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 10 (-1) (-10) 1 (e := (-10)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 14 (-1) (-14) 1 (e := (-14)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 18 0 0 1 (e := 22) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 2 (-1) (-2) 1 (e := (-2)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm40 6 (-1) (-6) 1 (e := (-6)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 114 0 0 1 (e := 646) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 190 0 0 1 (e := 570) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 266 0 0 1 (e := 494) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 342 0 0 1 (e := 418) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm760 38 0 0 1 (e := 722) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm8 2 0 0 1 (e := 6) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm760 38 1 (by norm_num : (-1 : ℂ) ≠ 0) (-38) 1 (e := 798) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm8 2 1 (by norm_num : (-1 : ℂ) ≠ 0) (-2) 1 (e := 10) (by norm_num) (by norm_num [c2]) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h



/-! ## the 2-dissections (33.10), (2.19) -/

lemma d34_1 : θ hm10 4 (-1) = θ hm40 18 (-1) + mono 4 1 * θ hm40 2 (-1) := by
  rw [dis2 hm10 hm40 rfl 4 (by norm_num : (-1 : ℂ) ≠ 0) 18 (-2) 6 (-1) 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num),
    θ_nfrm hm40 2 (-1) (-2) 1 (e := (-2)) (by norm_num) (by norm_num [c2]) (by norm_num), ← mul_assoc, mono_mul]
  norm_num

lemma d34_2 : θ hm10 2 (-1) = θ hm40 14 (-1) + mono 2 1 * θ hm40 6 (-1) := by
  rw [dis2 hm10 hm40 rfl 2 (by norm_num : (-1 : ℂ) ≠ 0) 14 (-6) 8 (-1) 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num),
    θ_nfrm hm40 6 (-1) (-6) 1 (e := (-6)) (by norm_num) (by norm_num [c2]) (by norm_num), ← mul_assoc, mono_mul]
  norm_num

lemma d34_3 : θ hm10 0 (-1) = 2 * θ hm40 10 (-1) := by
  rw [dis2 hm10 hm40 rfl 0 (by norm_num : (-1 : ℂ) ≠ 0) 10 (-10) 10 (-1) 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num),
    θ_nfrm hm40 10 (-1) (-10) 1 (e := (-10)) (by norm_num) (by norm_num [c2]) (by norm_num), ← mul_assoc, mono_mul]
  norm_num
  ring

lemma d34_4 : θ hm190 76 (-1) = θ hm760 342 (-1) + mono 76 1 * θ hm760 38 (-1) := by
  rw [dis2 hm190 hm760 rfl 76 (by norm_num : (-1 : ℂ) ≠ 0) 342 (-38) 114 (-1) 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num),
    θ_nfrm hm760 38 (-1) (-38) 1 (e := (-38)) (by norm_num) (by norm_num [c2]) (by norm_num), ← mul_assoc, mono_mul]
  norm_num

lemma d34_5 : θ hm190 38 (-1) = θ hm760 266 (-1) + mono 38 1 * θ hm760 114 (-1) := by
  rw [dis2 hm190 hm760 rfl 38 (by norm_num : (-1 : ℂ) ≠ 0) 266 (-114) 152 (-1) 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num),
    θ_nfrm hm760 114 (-1) (-114) 1 (e := (-114)) (by norm_num) (by norm_num [c2]) (by norm_num), ← mul_assoc,
    mono_mul]
  norm_num

lemma d34_6 : θ hm190 0 (-1) = 2 * θ hm760 190 (-1) := by
  rw [dis2 hm190 hm760 rfl 0 (by norm_num : (-1 : ℂ) ≠ 0) 190 (-190) 190 (-1) 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num),
    θ_nfrm hm760 190 (-1) (-190) 1 (e := (-190)) (by norm_num) (by norm_num [c2]) (by norm_num), ← mul_assoc,
    mono_mul]
  norm_num
  ring

lemma d34_7 : θ hm2 0 (-1) = 2 * θ hm8 2 (-1) := by
  rw [dis2 hm2 hm8 rfl 0 (by norm_num : (-1 : ℂ) ≠ 0) 2 (-2) 2 (-1) 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num),
    θ_nfrm hm8 2 (-1) (-2) 1 (e := (-2)) (by norm_num) (by norm_num [c2]) (by norm_num), ← mul_assoc, mono_mul]
  norm_num
  ring

lemma d34_8 : θ hm38 0 (-1) = 2 * θ hm152 38 (-1) := by
  rw [dis2 hm38 hm152 rfl 0 (by norm_num : (-1 : ℂ) ≠ 0) 38 (-38) 38 (-1) 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num),
    θ_nfrm hm152 38 (-1) (-38) 1 (e := (-38)) (by norm_num) (by norm_num [c2]) (by norm_num), ← mul_assoc,
    mono_mul]
  norm_num
  ring

lemma monoT (k : ℕ) : (mono (k : ℤ) 1 : L) = mono 1 1 ^ k := by
  rw [mono, single_pow]; simp

/-- Berndt et al. (33.6) multiplied by `4q`, in `ℂ((t))`: with `θ₁₀(e,±1)`, `θ₁₉₀(e,±1)` the theta functions
`f(∓q^e, ∓q^{N−e})` and `θ_N(0,−1) = 2ψ(q^N)`. -/
theorem L33_6 : 4 * mono 1 1 * (θ hm10 4 1 * θ hm190 76 1 + mono 8 1 * (θ hm10 2 1 * θ hm190 38 1)) =
    4 * mono 1 1 * (θ hm10 4 (-1) * θ hm190 76 (-1) + mono 8 1 * (θ hm10 2 (-1) * θ hm190 38 (-1)))
      + 2 * mono 25 1 * (θ hm10 0 (-1) * θ hm190 0 (-1)) - 2 * mono 5 1 * (θ hm2 0 (-1) * θ hm38 0 (-1)) := by
  have hM := M3_17
  have ha := L34a
  have hb := L34b
  have hd := L34d
  rw [d34_1, d34_2, d34_3, d34_4, d34_5, d34_6, d34_7, d34_8]
  simp only [show (mono 2 1 : L) = mono 1 1 ^ 2 from monoT 2, show (mono 4 1 : L) = mono 1 1 ^ 4 from monoT 4, show (mono 5 1 : L) = mono 1 1 ^ 5 from monoT 5, show (mono 6 1 : L) = mono 1 1 ^ 6 from monoT 6, show (mono 8 1 : L) = mono 1 1 ^ 8 from monoT 8, show (mono 9 1 : L) = mono 1 1 ^ 9 from monoT 9, show (mono 16 1 : L) = mono 1 1 ^ 16 from monoT 16, show (mono 20 1 : L) = mono 1 1 ^ 20 from monoT 20, show (mono 25 1 : L) = mono 1 1 ^ 25 from monoT 25, show (mono 36 1 : L) = mono 1 1 ^ 36 from monoT 36, show (mono 38 1 : L) = mono 1 1 ^ 38 from monoT 38, show (mono 42 1 : L) = mono 1 1 ^ 42 from monoT 42, show (mono 49 1 : L) = mono 1 1 ^ 49 from monoT 49, show (mono 64 1 : L) = mono 1 1 ^ 64 from monoT 64, show (mono 72 1 : L) = mono 1 1 ^ 72 from monoT 72, show (mono 76 1 : L) = mono 1 1 ^ 76 from monoT 76, show (mono 81 1 : L) = mono 1 1 ^ 81 from monoT 81, show (mono 100 1 : L) = mono 1 1 ^ 100 from monoT 100] at hM ha hb hd ⊢
  linear_combination hM + ha - hb + 2 * mono 1 1 ^ 5 * hd

/-! ## bridge to products -/

local notation "φ" => RamanujanTau.Septic.phi
local notation "ψ" => RamanujanTau.Septic.ramF 1 3

private lemma ι_ne' {f : PowerSeries ℤ} (h : f ≠ 0) : ι f ≠ 0 := fun h0 => h (ι_inj (h0.trans (map_zero ι).symm))

private lemma J_ne' (e N : ℕ) (h1 : 1 ≤ e) (h2 : e < N) : J e N ≠ 0 :=
  mul_ne_zero (mul_ne_zero (Pinf_ne e N h1 (by omega)) (Pinf_ne (N - e) N (by omega) (by omega)))
    (Pinf_ne N N (by omega) (by omega))

/-- `f(1, q^N) = 2x` once `x (q^N;q^{2N}) = (q^{2N};q^{2N})` (i.e. `x = ψ(q^N)`). -/
lemma θ0_eq {N : ℕ} [NeZero N] (h : 1 ≤ N) (x : PowerSeries ℤ) (hx : x * Pinf N (2 * N) = Pinf (2 * N) (2 * N)) :
    θ h 0 (-1) = 2 * ι x := by
  have hb := θ_bar0 (N := N) h
  apply mul_right_cancel₀ (ι_ne' (Pinf_ne N (2 * N) h (by omega)))
  rw [hb, mul_assoc, ← map_mul, hx]

/-- `f(q^e, q^{N−e}) = x` once `x J_{e,N} = J_{2e,2N} J_{N,2N}`. -/
lemma θm_eq {N : ℕ} (h : 1 ≤ N) (e : ℕ) {e' : ℤ} (he' : e' = e) (he : 1 ≤ e) (heN : e < N) (x : PowerSeries ℤ)
    (hx : x * J e N = J (2 * e) (2 * N) * J N (2 * N)) : θ h e' (-1) = ι x := by
  have hb := θ_bar h e he heN
  rw [he']
  apply mul_right_cancel₀ (ι_ne' (J_ne' e N he heN))
  rw [hb, ← map_mul, hx]

/-- (33.1): `G(q)G(−q) f(−q²) = f(q⁴,q⁶)`, i.e. `· J_{4,10} = J_{8,20} J_{10,20}`. -/
lemma F1_J : G * Ng G * Pinf 2 2 * J 4 10 = J 8 20 * J 10 20 := by
  have hG := G_mul_uu
  have hN := NgG_prod
  have key : Pinf 1 10 * Pinf 9 10 * Pinf 2 2 * J 4 10 =
      J 8 20 * J 10 20 * uu * (Pinf 2 20 * Pinf 6 10 * Pinf 4 10 * Pinf 18 20) := by
    simp only [J, uu, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 20]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  have hD : (Pinf 2 20 * Pinf 6 10 * Pinf 4 10 * Pinf 18 20 : PowerSeries ℤ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (Pinf_ne 2 20 (by norm_num) (by norm_num))
      (Pinf_ne 6 10 (by norm_num) (by norm_num))) (Pinf_ne 4 10 (by norm_num) (by norm_num)))
      (Pinf_ne 18 20 (by norm_num) (by norm_num))
  have k2 : Ng G * Pinf 2 2 * J 4 10 = J 8 20 * J 10 20 * uu := by
    apply mul_left_cancel₀ hD
    linear_combination key + (Pinf 2 2 * J 4 10) * hN
  linear_combination G * k2 + (J 8 20 * J 10 20) * hG

/-- (33.1): `H(q)H(−q) f(−q²) = f(q²,q⁸)`, i.e. `· J_{2,10} = J_{4,20} J_{10,20}`. -/
lemma F2_J : H * Ng H * Pinf 2 2 * J 2 10 = J 4 20 * J 10 20 := by
  have hH := H_mul_vv
  have hN := NgH_prod
  have key : Pinf 7 10 * Pinf 3 10 * Pinf 2 2 * J 2 10 =
      J 4 20 * J 10 20 * vv * (Pinf 2 10 * Pinf 8 10 * Pinf 14 20 * Pinf 6 20) := by
    simp only [J, vv, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 20]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  have hD : (Pinf 2 10 * Pinf 8 10 * Pinf 14 20 * Pinf 6 20 : PowerSeries ℤ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (Pinf_ne 2 10 (by norm_num) (by norm_num))
      (Pinf_ne 8 10 (by norm_num) (by norm_num))) (Pinf_ne 14 20 (by norm_num) (by norm_num)))
      (Pinf_ne 6 20 (by norm_num) (by norm_num))
  have k2 : Ng H * Pinf 2 2 * J 2 10 = J 4 20 * J 10 20 * vv := by
    apply mul_left_cancel₀ hD
    linear_combination key + (Pinf 2 2 * J 2 10) * hN
  linear_combination H * k2 + (J 4 20 * J 10 20) * hH

lemma S2ψ_mul : S 2 ψ * Pinf 2 4 = Pinf 4 4 := by
  have h := congrArg (S 2) psi_mul
  rw [map_mul, S_Pinf 2 1 2 le_rfl (by norm_num), S_Pinf 2 2 2 (by norm_num) (by norm_num)] at h
  exact h

lemma S10ψ_mul : S 10 ψ * Pinf 10 20 = Pinf 20 20 := by
  have h := congrArg (S 10) psi_mul
  rw [map_mul, S_Pinf 10 1 2 le_rfl (by norm_num), S_Pinf 10 2 2 (by norm_num) (by norm_num)] at h
  exact h

/-- (33.2), from Entries 3.20 and 3.21: `G(q)H(−q) f(−q²) = ψ(q²) + qψ(q¹⁰)`. -/
lemma K1_eq : G * Ng H * Pinf 2 2 = S 2 ψ + PowerSeries.X * S 10 ψ := by
  have e20 := entry_3_20
  have e21 := entry_3_21
  have hc : IsUnit (chim 2 ^ 2) := (isUnit_Pinf 2 4 (by norm_num) (by norm_num)).pow 2
  have hf : IsUnit (fm 2) := isUnit_Pinf 2 2 (by norm_num) (by norm_num)
  have ic := Ring.mul_inverse_cancel _ hc
  have iF := Ring.mul_inverse_cancel _ hf
  have hs := S2ψ_mul
  have a2 := atom 2 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [prod_range_succ, prod_range_zero, one_mul] at a2
  norm_num at a2
  simp only [chim, fm, Nat.reduceMul] at ic iF e20 e21
  apply mul_left_cancel₀ two_ne
  linear_combination Pinf 2 2 * e20 + Pinf 2 2 * e21 + 2 * PowerSeries.X * S 10 ψ * iF
    + 2 * Ring.inverse (Pinf 2 4 ^ 2) * a2 - 2 * Ring.inverse (Pinf 2 4 ^ 2) * Pinf 2 4 * hs + 2 * S 2 ψ * ic

/-- (33.2), from Entries 3.20 and 3.21: `G(−q)H(q) f(−q²) = ψ(q²) − qψ(q¹⁰)`. -/
lemma K2_eq : Ng G * H * Pinf 2 2 = S 2 ψ - PowerSeries.X * S 10 ψ := by
  have e20 := entry_3_20
  have e21 := entry_3_21
  have hc : IsUnit (chim 2 ^ 2) := (isUnit_Pinf 2 4 (by norm_num) (by norm_num)).pow 2
  have hf : IsUnit (fm 2) := isUnit_Pinf 2 2 (by norm_num) (by norm_num)
  have ic := Ring.mul_inverse_cancel _ hc
  have iF := Ring.mul_inverse_cancel _ hf
  have hs := S2ψ_mul
  have a2 := atom 2 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [prod_range_succ, prod_range_zero, one_mul] at a2
  norm_num at a2
  simp only [chim, fm, Nat.reduceMul] at ic iF e20 e21
  apply mul_left_cancel₀ two_ne
  linear_combination Pinf 2 2 * e20 - Pinf 2 2 * e21 - 2 * PowerSeries.X * S 10 ψ * iF
    + 2 * Ring.inverse (Pinf 2 4 ^ 2) * a2 - 2 * Ring.inverse (Pinf 2 4 ^ 2) * Pinf 2 4 * hs + 2 * S 2 ψ * ic

/-- **(33.6)** of Berndt et al. in product form, for any series with the product forms of
`f(q⁴,q⁶), f(q⁷⁶,q¹¹⁴), f(q²,q⁸), f(q³⁸,q¹⁵²), ψ(q²), ψ(q³⁸), ψ(q¹⁰), ψ(q¹⁹⁰)`:
`f(−q⁴,−q⁶)f(−q⁷⁶,−q¹¹⁴) + q⁸f(−q²,−q⁸)f(−q³⁸,−q¹⁵²)
  = f(q⁴,q⁶)f(q⁷⁶,q¹¹⁴) + q⁸f(q²,q⁸)f(q³⁸,q¹⁵²) + 2q²⁴ψ(q¹⁰)ψ(q¹⁹⁰) − 2q⁴ψ(q²)ψ(q³⁸)`. -/
theorem P33_6 (a b c d s2 s38 s10 s190 : PowerSeries ℤ)
    (ha : a * J 4 10 = J 8 20 * J 10 20) (hb : b * J 76 190 = J 152 380 * J 190 380)
    (hc : c * J 2 10 = J 4 20 * J 10 20) (hd : d * J 38 190 = J 76 380 * J 190 380)
    (h2 : s2 * Pinf 2 4 = Pinf 4 4) (h38 : s38 * Pinf 38 76 = Pinf 76 76)
    (h10 : s10 * Pinf 10 20 = Pinf 20 20) (h190 : s190 * Pinf 190 380 = Pinf 380 380) :
    J 4 10 * J 76 190 + PowerSeries.X ^ 8 * (J 2 10 * J 38 190) =
      a * b + PowerSeries.X ^ 8 * (c * d) + 2 * PowerSeries.X ^ 24 * (s10 * s190)
        - 2 * PowerSeries.X ^ 4 * (s2 * s38) := by
  have hX : (4 * PowerSeries.X : PowerSeries ℤ) ≠ 0 :=
    mul_ne_zero (by
      intro h; have := congrArg PowerSeries.constantCoeff h; rw [map_ofNat, map_zero] at this; norm_num at this)
      PowerSeries.X_ne_zero
  apply mul_left_cancel₀ hX
  apply ι_inj
  have h := L33_6
  rw [θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm190 76 (e' := 76) (by norm_num) (by norm_num) (by norm_num),
    θu' hm190 38 (e' := 38) (by norm_num) (by norm_num) (by norm_num),
    θm_eq hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num) a ha,
    θm_eq hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num) c hc,
    θm_eq hm190 76 (e' := 76) (by norm_num) (by norm_num) (by norm_num) b hb,
    θm_eq hm190 38 (e' := 38) (by norm_num) (by norm_num) (by norm_num) d hd,
    θ0_eq (N := 2) hm2 s2 h2, θ0_eq (N := 38) hm38 s38 h38, θ0_eq (N := 10) hm10 s10 h10,
    θ0_eq (N := 190) hm190 s190 h190] at h
  simp only [show (mono 5 1 : L) = mono 1 1 ^ 5 from monoT 5, show (mono 8 1 : L) = mono 1 1 ^ 8 from monoT 8,
    show (mono 25 1 : L) = mono 1 1 ^ 25 from monoT 25] at h
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, ι_X]
  linear_combination h

/-- **Entry 3.34** (Watson, corrected by Bressoud; Berndt et al. §33):
`{G(q)G(−q¹⁹) − q⁴H(q)H(−q¹⁹)}{G(−q)G(q¹⁹) − q⁴H(−q)H(q¹⁹)} = G(q²)G(q³⁸) + q⁸H(q²)H(q³⁸)`. -/
theorem entry_3_34 :
    (G * S 19 (Ng G) - PowerSeries.X ^ 4 * H * S 19 (Ng H)) * (Ng G * S 19 G - PowerSeries.X ^ 4 * Ng H * S 19 H) =
      S 2 G * S 38 G + PowerSeries.X ^ 8 * S 2 H * S 38 H := by
  have X19 : S 19 PowerSeries.X = PowerSeries.X ^ 19 := RankProof.Ea_X 19 _
  have F1 := F1_J
  have F2 := F2_J
  have hb : S 19 G * S 19 (Ng G) * Pinf 38 38 * J 76 190 = J 152 380 * J 190 380 := by
    have h := congrArg (S 19) F1_J
    simp only [map_mul, S_P' 19 2 2 (by norm_num) (by norm_num) (rfl : 38 = 19 * 2) (rfl : 38 = 19 * 2),
      S_J' 19 4 10 (by norm_num) (by norm_num) (rfl : 76 = 19 * 4) (rfl : 190 = 19 * 10),
      S_J' 19 8 20 (by norm_num) (by norm_num) (rfl : 152 = 19 * 8) (rfl : 380 = 19 * 20),
      S_J' 19 10 20 (by norm_num) (by norm_num) (rfl : 190 = 19 * 10) (rfl : 380 = 19 * 20)] at h
    exact h
  have hd : S 19 H * S 19 (Ng H) * Pinf 38 38 * J 38 190 = J 76 380 * J 190 380 := by
    have h := congrArg (S 19) F2_J
    simp only [map_mul, S_P' 19 2 2 (by norm_num) (by norm_num) (rfl : 38 = 19 * 2) (rfl : 38 = 19 * 2),
      S_J' 19 2 10 (by norm_num) (by norm_num) (rfl : 38 = 19 * 2) (rfl : 190 = 19 * 10),
      S_J' 19 4 20 (by norm_num) (by norm_num) (rfl : 76 = 19 * 4) (rfl : 380 = 19 * 20),
      S_J' 19 10 20 (by norm_num) (by norm_num) (rfl : 190 = 19 * 10) (rfl : 380 = 19 * 20)] at h
    exact h
  have h38 : S 19 (S 2 ψ) * Pinf 38 76 = Pinf 76 76 := by
    have h := congrArg (S 19) S2ψ_mul
    rw [map_mul, S_P' 19 2 4 (by norm_num) (by norm_num) (rfl : 38 = 19 * 2) (rfl : 76 = 19 * 4),
      S_P' 19 4 4 (by norm_num) (by norm_num) (rfl : 76 = 19 * 4) (rfl : 76 = 19 * 4)] at h
    exact h
  have h190 : S 19 (S 10 ψ) * Pinf 190 380 = Pinf 380 380 := by
    have h := congrArg (S 19) S10ψ_mul
    rw [map_mul, S_P' 19 10 20 (by norm_num) (by norm_num) (rfl : 190 = 19 * 10) (rfl : 380 = 19 * 20),
      S_P' 19 20 20 (by norm_num) (by norm_num) (rfl : 380 = 19 * 20) (rfl : 380 = 19 * 20)] at h
    exact h
  have P := P33_6 _ _ _ _ _ _ _ _ F1 hb F2 hd S2ψ_mul h38 S10ψ_mul h190
  have K1 := K1_eq
  have K2 := K2_eq
  have K1' : S 19 G * S 19 (Ng H) * Pinf 38 38 = S 19 (S 2 ψ) + PowerSeries.X ^ 19 * S 19 (S 10 ψ) := by
    have h := congrArg (S 19) K1_eq
    simp only [map_mul, map_add, X19, S_P' 19 2 2 (by norm_num) (by norm_num) (rfl : 38 = 19 * 2)
      (rfl : 38 = 19 * 2)] at h
    exact h
  have K2' : S 19 (Ng G) * S 19 H * Pinf 38 38 = S 19 (S 2 ψ) - PowerSeries.X ^ 19 * S 19 (S 10 ψ) := by
    have h := congrArg (S 19) K2_eq
    simp only [map_mul, map_sub, X19, S_P' 19 2 2 (by norm_num) (by norm_num) (rfl : 38 = 19 * 2)
      (rfl : 38 = 19 * 2)] at h
    exact h
  have e1 := SG_E 2
  have e2 := SH_E 2
  have e3 := SG_E 38
  have e4 := SH_E 38
  norm_num at e1 e2 e3 e4
  have hL : (S 2 G * S 38 G + PowerSeries.X ^ 8 * S 2 H * S 38 H) * (Pinf 2 2 * Pinf 38 38) =
      J 4 10 * J 76 190 + PowerSeries.X ^ 8 * (J 2 10 * J 38 190) := by
    linear_combination (S 38 G * Pinf 38 38) * e1 + J 4 10 * e3 + PowerSeries.X ^ 8 * (S 38 H * Pinf 38 38) * e2
      + PowerSeries.X ^ 8 * J 2 10 * e4
  have hW : (Pinf 2 2 * Pinf 38 38 : PowerSeries ℤ) ≠ 0 :=
    mul_ne_zero (Pinf_ne 2 2 (by norm_num) (by norm_num)) (Pinf_ne 38 38 (by norm_num) (by norm_num))
  apply mul_left_cancel₀ hW
  linear_combination -P - hL
    - PowerSeries.X ^ 4 * (S 19 (Ng G) * S 19 H * Pinf 38 38) * K1
    - PowerSeries.X ^ 4 * (S 2 ψ + PowerSeries.X * S 10 ψ) * K2'
    - PowerSeries.X ^ 4 * (S 19 G * S 19 (Ng H) * Pinf 38 38) * K2
    - PowerSeries.X ^ 4 * (S 2 ψ - PowerSeries.X * S 10 ψ) * K1'

end Forty

