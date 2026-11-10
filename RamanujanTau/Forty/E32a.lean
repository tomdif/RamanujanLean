/-
# Entries 3.31 and 3.32, part A: the two binary-form identities

Yesilyurt, *A generalization of a modular identity of Rogers*, J. Number Theory 129 (2009), §5, proves 3.31 and 3.32
(whose only earlier proofs, by Biagioli, use modular forms) from his generalised Rogers identity. Here the two
needed instances are written as Type II identities (`qf_two`), found with `scripts/forty/ecs.py`; both forms have
determinant 396 and are read at `t = q` (so every theta below is at `q ↦ q²` of the identity in the text):

* `L32U`: `18x²−12xy+24y²+16x+2y`, sign `(−1)^x`, covers `(−1 3; −1 −2)` (det 5, moduli 60, 660) and
  `(0 −4; 1 −1)` (det 4, moduli 48, 528, barred thetas);
* `L32T`: `8x²−4xy+50y²+2x+16y`, sign `(−1)^y`, covers `(−2 −3; 1 −1)` (det 5, moduli 180, 220) and
  `(−1 −1; 0 −4)` (det 4, moduli 16, 1584, barred thetas).

See `E32.lean` for the quintuple collapses and the rest of the argument.
-/
import RamanujanTau.Forty.E13

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm16 : 1 ≤ 16 := by norm_num
private lemma hm48 : 1 ≤ 48 := by norm_num
private lemma hm60 : 1 ≤ 60 := by norm_num
private lemma hm180 : 1 ≤ 180 := by norm_num
private lemma hm220 : 1 ≤ 220 := by norm_num
private lemma hm528 : 1 ≤ 528 := by norm_num
private lemma hm660 : 1 ≤ 660 := by norm_num
private lemma hm1584 : 1 ≤ 1584 := by norm_num


/-- Entry 32U, side a: `B = (-1 3; -1 -2)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B32Ua : ECS where
  b11 := (-1)
  b12 := 3
  b21 := (-1)
  b22 := (-2)
  r1 := 1
  r2 := 0
  I := {(-2), (-1), 0, 1, 2}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 4 * n - (-2)) % 5 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    (((-2) * (m - 1 * ((1 * m + 4 * n - (-2)) % 5 + (-2))) - 3 * (n - 0 * ((1 * m + 4 * n - (-2)) % 5 + (-2)))) / 5), (((-1) * (n - 0 * ((1 * m + 4 * n - (-2)) % 5 + (-2))) - (-1) * (m - 1 * ((1 * m + 4 * n - (-2)) % 5 + (-2)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- Entry 32U, side b: `B = (0 -4; 1 -1)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1), 0, 1}`. -/
def B32Ub : ECS where
  b11 := 0
  b12 := (-4)
  b21 := 1
  b22 := (-1)
  r1 := 1
  r2 := 0
  I := {(-2), (-1), 0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - (-2)) % 4 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    (((-1) * (m - 1 * ((1 * m + 0 * n - (-2)) % 4 + (-2))) - (-4) * (n - 0 * ((1 * m + 0 * n - (-2)) % 4 + (-2)))) / 4), ((0 * (n - 0 * ((1 * m + 0 * n - (-2)) % 4 + (-2))) - 1 * (m - 1 * ((1 * m + 0 * n - (-2)) % 4 + (-2)))) / 4), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L32U : (θ hm60 12 1 * θ hm660 286 1) - (mono 2 1 * (θ hm60 24 1 * θ hm660 242 1)) + (mono 22 1 * (θ hm60 12 1 * θ hm660 154 1)) - (mono 68 1 * (θ hm60 24 1 * θ hm660 22 1)) = (θ hm48 22 (-1) * θ hm528 198 (-1)) - (mono 2 1 * (θ hm48 10 (-1) * θ hm528 198 (-1))) - (mono 34 1 * (θ hm48 14 (-1) * θ hm528 66 (-1))) + (mono 38 1 * (θ hm48 2 (-1) * θ hm528 66 (-1))) := by
  have h := qf_two 18 (-6) 24 16 2 1 0 B32Ua B32Ub
    hm60 hm660 hm48 hm528 (by norm_num [B32Ua]) (by norm_num [B32Ua]) (by norm_num [B32Ua])
    (by norm_num [B32Ub]) (by norm_num [B32Ub]) (by norm_num [B32Ub])
  simp only [B32Ua, B32Ub] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm60 12 (-1) (-12) (-1) (e := (-12)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm60 24 0 0 1 (e := 36) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm660 154 0 0 1 (e := 506) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm660 22 0 0 1 (e := 638) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm660 286 0 0 1 (e := 374) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm48 10 0 0 1 (e := 38) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm48 22 0 0 1 (e := 26) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm528 198 0 0 1 (e := 330) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm528 66 0 0 1 (e := 462) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm48 2 1 (by norm_num : (-1 : ℂ) ≠ 0) (-2) 1 (e := 50) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm60 24 (-1) one_ne_zero (-36) (-1) (e := (-36)) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm60 1 (e := 60) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- Entry 32T, side a: `B = (-2 -3; 1 -1)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B32Ta : ECS where
  b11 := (-2)
  b12 := (-3)
  b21 := 1
  b22 := (-1)
  r1 := 1
  r2 := 0
  I := {(-2), (-1), 0, 1, 2}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 2 * n - (-2)) % 5 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    (((-1) * (m - 1 * ((1 * m + 2 * n - (-2)) % 5 + (-2))) - (-3) * (n - 0 * ((1 * m + 2 * n - (-2)) % 5 + (-2)))) / 5), (((-2) * (n - 0 * ((1 * m + 2 * n - (-2)) % 5 + (-2))) - 1 * (m - 1 * ((1 * m + 2 * n - (-2)) % 5 + (-2)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- Entry 32T, side b: `B = (-1 -1; 0 -4)`, shifts `i (0, 1)`, `i ∈ {(-2), (-1), 0, 1}`. -/
def B32Tb : ECS where
  b11 := (-1)
  b12 := (-1)
  b21 := 0
  b22 := (-4)
  r1 := 0
  r2 := 1
  I := {(-2), (-1), 0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-2)) % 4 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    (((-4) * (m - 0 * ((0 * m + 1 * n - (-2)) % 4 + (-2))) - (-1) * (n - 1 * ((0 * m + 1 * n - (-2)) % 4 + (-2)))) / 4), (((-1) * (n - 1 * ((0 * m + 1 * n - (-2)) % 4 + (-2))) - 0 * (m - 0 * ((0 * m + 1 * n - (-2)) % 4 + (-2)))) / 4), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L32T : (θ hm180 78 1 * θ hm220 88 1) + (mono 6 1 * (θ hm180 42 1 * θ hm220 88 1)) + (mono 10 1 * (θ hm180 66 1 * θ hm220 44 1)) + (mono 28 1 * (θ hm180 6 1 * θ hm220 44 1)) = (θ hm16 6 (-1) * θ hm1584 726 (-1)) - (mono 34 1 * (θ hm16 2 (-1) * θ hm1584 462 (-1))) - (mono 66 1 * (θ hm16 6 (-1) * θ hm1584 330 (-1))) + (mono 166 1 * (θ hm16 2 (-1) * θ hm1584 66 (-1))) := by
  have h := qf_two 8 (-2) 50 2 16 0 1 B32Ta B32Tb
    hm180 hm220 hm16 hm1584 (by norm_num [B32Ta]) (by norm_num [B32Ta]) (by norm_num [B32Ta])
    (by norm_num [B32Tb]) (by norm_num [B32Tb]) (by norm_num [B32Tb])
  simp only [B32Ta, B32Tb] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm180 42 0 0 1 (e := 138) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm180 6 0 0 1 (e := 174) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm180 78 0 0 1 (e := 102) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm220 44 0 0 1 (e := 176) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm220 88 0 0 1 (e := 132) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm1584 462 0 0 1 (e := 1122) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm1584 66 0 0 1 (e := 1518) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm16 2 (-1) (-2) 1 (e := (-2)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm16 6 0 0 1 (e := 10) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm220 0 (e := 0) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


end Forty
