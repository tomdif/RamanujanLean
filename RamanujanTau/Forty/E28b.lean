/-
# Entry 3.28(ii): the two lattice identities (Yesilyurt, JMAA 388 (2012) §3, in Cao's language)

With `Q = q¹⁷`, `V(q) = G(q)G(Q²) + q⁷H(q)H(Q²)`. Yesilyurt's `R₁(1,1,1,0,0,17,3,1,4) = R₁(1,1,1,7,−2,1,51,17,5)`
(his (3.9)) and `R₁(1,0,1,0,0,17,3,1,4) = R₁(1,1,0,7,−2,1,51,17,5)` (his (3.17)) are the Type II identities of the
form `5x² + 34xy + 68y² + x` with signs `(−1)^{x+y}` (`L28p`) and `(−1)^y` (`L28m`), split by the covers
`(0 −4; 1 1)` (determinant 4) and `(1 17; 0 −5)` (determinant 5). One quintuple collapse at nome `q⁸` (`A4p_c`,
`A4m_c`) and two at nome `Q¹⁰` (`B5p_c`, `B5m_c`) evaluate the four sides. Here `t = q`.
-/
import RamanujanTau.Forty.E29d

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm8 : 1 ≤ 8 := by norm_num
private lemma hm170 : 1 ≤ 170 := by norm_num
private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm24 : 1 ≤ 24 := by norm_num
private lemma hm136 : 1 ≤ 136 := by norm_num
private lemma hm510 : 1 ≤ 510 := by norm_num

/-- E28p, side a: `B = (0 -4; 1 1)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1), 0, 1}`. -/
def B28pa : ECS where
  b11 := 0
  b12 := (-4)
  b21 := 1
  b22 := 1
  r1 := 1
  r2 := 0
  I := {(-2), (-1), 0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - (-2)) % 4 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 0 * n - (-2)) % 4 + (-2))) - (-4) * (n - 0 * ((1 * m + 0 * n - (-2)) % 4 + (-2)))) / 4), ((0 * (n - 0 * ((1 * m + 0 * n - (-2)) % 4 + (-2))) - 1 * (m - 1 * ((1 * m + 0 * n - (-2)) % 4 + (-2)))) / 4), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- E28p, side b: `B = (1 17; 0 -5)`, shifts `i (0, 1)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B28pb : ECS where
  b11 := 1
  b12 := 17
  b21 := 0
  b22 := (-5)
  r1 := 0
  r2 := 1
  I := {(-2), (-1), 0, 1, 2}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-2)) % 5 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    (((-5) * (m - 0 * ((0 * m + 1 * n - (-2)) % 5 + (-2))) - 17 * (n - 1 * ((0 * m + 1 * n - (-2)) % 5 + (-2)))) / (-5)), ((1 * (n - 1 * ((0 * m + 1 * n - (-2)) % 5 + (-2))) - 0 * (m - 0 * ((0 * m + 1 * n - (-2)) % 5 + (-2)))) / (-5)), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L28p : (θ hm136 68 1 * θ hm24 8 1) - (mono 4 1 * (θ hm136 34 1 * θ hm24 10 1)) - (mono 6 1 * (θ hm136 34 1 * θ hm24 2 1)) = (θ hm10 4 1 * θ hm510 238 (-1)) + (mono 14 1 * (θ hm10 2 1 * θ hm510 136 (-1))) - (mono 34 1 * (θ hm10 4 1 * θ hm510 68 (-1))) - (mono 48 1 * (θ hm10 2 1 * θ hm510 34 (-1))) := by
  have h := qf_two 5 17 68 1 0 1 1 B28pa B28pb
    hm136 hm24 hm10 hm510 (by norm_num [B28pa]) (by norm_num [B28pa]) (by norm_num [B28pa])
    (by norm_num [B28pb]) (by norm_num [B28pb]) (by norm_num [B28pb])
  simp only [B28pa, B28pb] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm10 2 (-7) (-224) (-1) (e := (-62)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm10 4 0 0 1 (e := 6) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm136 34 0 0 1 (e := 102) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm24 10 0 0 1 (e := 14) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm24 4 0 0 1 (e := 20) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm510 136 0 0 1 (e := 374) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm510 238 0 0 1 (e := 272) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm510 34 0 0 1 (e := 476) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm10 2 (-3) one_ne_zero (-54) (-1) (e := (-28)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm10 4 7 one_ne_zero (-238) (-1) (e := 74) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm10 4 (e := 40) (by norm_num), θz' hm136 0 (e := 0) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- Entry 28m, side a: `B = (0 -4; 1 1)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1), 0, 1}`. -/
def B28ma : ECS where
  b11 := 0
  b12 := (-4)
  b21 := 1
  b22 := 1
  r1 := 1
  r2 := 0
  I := {(-2), (-1), 0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - (-2)) % 4 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 0 * n - (-2)) % 4 + (-2))) - (-4) * (n - 0 * ((1 * m + 0 * n - (-2)) % 4 + (-2)))) / 4), ((0 * (n - 0 * ((1 * m + 0 * n - (-2)) % 4 + (-2))) - 1 * (m - 1 * ((1 * m + 0 * n - (-2)) % 4 + (-2)))) / 4), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- Entry 28m, side b: `B = (1 17; 0 -5)`, shifts `i (0, 1)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B28mb : ECS where
  b11 := 1
  b12 := 17
  b21 := 0
  b22 := (-5)
  r1 := 0
  r2 := 1
  I := {(-2), (-1), 0, 1, 2}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-2)) % 5 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    (((-5) * (m - 0 * ((0 * m + 1 * n - (-2)) % 5 + (-2))) - 17 * (n - 1 * ((0 * m + 1 * n - (-2)) % 5 + (-2)))) / (-5)), ((1 * (n - 1 * ((0 * m + 1 * n - (-2)) % 5 + (-2))) - 0 * (m - 0 * ((0 * m + 1 * n - (-2)) % 5 + (-2)))) / (-5)), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L28m : (θ hm136 68 1 * θ hm24 8 1) + (mono 4 1 * (θ hm136 34 1 * θ hm24 10 1)) + (mono 6 1 * (θ hm136 34 1 * θ hm24 2 1)) = (θ hm10 4 (-1) * θ hm510 238 1) - (mono 8 1 * (θ hm10 0 (-1) * θ hm510 170 1)) - (mono 14 1 * (θ hm10 2 (-1) * θ hm510 136 1)) + (mono 34 1 * (θ hm10 4 (-1) * θ hm510 68 1)) + (mono 48 1 * (θ hm10 2 (-1) * θ hm510 34 1)) := by
  have h := qf_two 5 17 68 1 0 0 1 B28ma B28mb
    hm136 hm24 hm10 hm510 (by norm_num [B28ma]) (by norm_num [B28ma]) (by norm_num [B28ma])
    (by norm_num [B28mb]) (by norm_num [B28mb]) (by norm_num [B28mb])
  simp only [B28ma, B28mb] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm136 34 0 0 1 (e := 102) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm24 10 0 0 1 (e := 14) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm24 4 0 0 1 (e := 20) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm510 136 0 0 1 (e := 374) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm510 238 0 0 1 (e := 272) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm510 34 0 0 1 (e := 476) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm10 2 (-7) (-224) 1 (e := (-62)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm10 4 0 0 1 (e := 6) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm10 0 4 (by norm_num : (-1 : ℂ) ≠ 0) (-60) 1 (e := 40) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm10 2 (-3) (by norm_num : (-1 : ℂ) ≠ 0) (-54) 1 (e := (-28)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm10 4 7 (by norm_num : (-1 : ℂ) ≠ 0) (-238) 1 (e := 74) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm136 0 (e := 0) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- the determinant-4 side of `L28p`. -/
noncomputable def A4p : L := (θ hm136 68 1 * θ hm24 8 1) - (mono 4 1 * (θ hm136 34 1 * θ hm24 10 1))
  - (mono 6 1 * (θ hm136 34 1 * θ hm24 2 1))
/-- the determinant-4 side of `L28m`. -/
noncomputable def A4m : L := (θ hm136 68 1 * θ hm24 8 1) + (mono 4 1 * (θ hm136 34 1 * θ hm24 10 1))
  + (mono 6 1 * (θ hm136 34 1 * θ hm24 2 1))
/-- the determinant-5 side of `L28p`. -/
noncomputable def B5p : L := (θ hm10 4 1 * θ hm510 238 (-1)) + (mono 14 1 * (θ hm10 2 1 * θ hm510 136 (-1)))
  - (mono 34 1 * (θ hm10 4 1 * θ hm510 68 (-1))) - (mono 48 1 * (θ hm10 2 1 * θ hm510 34 (-1)))
/-- the determinant-5 side of `L28m`. -/
noncomputable def B5m : L := (θ hm10 4 (-1) * θ hm510 238 1) - (mono 8 1 * (θ hm10 0 (-1) * θ hm510 170 1))
  - (mono 14 1 * (θ hm10 2 (-1) * θ hm510 136 1)) + (mono 34 1 * (θ hm10 4 (-1) * θ hm510 68 1))
  + (mono 48 1 * (θ hm10 2 (-1) * θ hm510 34 1))

theorem A4p_eq : A4p = B5p := by rw [A4p, B5p, L28p]
theorem A4m_eq : A4m = B5m := by rw [A4m, B5m, L28m]

private lemma mm (a b c : ℤ) (h : a + b = c) : (mono a 1 : L) * mono b 1 = mono c 1 := by
  rw [mono_mul, h]; norm_num

theorem A4p_c : A4p * θ hm8 2 1 = θ hm24 8 1 * (θ hm136 68 1 * θ hm8 2 1 - mono 4 1 * (θ hm136 34 1 * θ hm8 4 1)) := by
  have Q1 := quint1 hm8 hm24 rfl 2 14 22 8 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_refl1 hm24 10 14 (by norm_num), θ_refl1 hm24 2 22 (by norm_num)] at Q1
  rw [A4p]
  linear_combination (-(mono 4 1 * θ hm136 34 1)) * Q1
    + (θ hm136 34 1 * θ hm24 2 1 * θ hm8 2 1) * mm 4 2 6 (by norm_num)

theorem A4m_c : A4m * θ hm8 2 1 = θ hm24 8 1 * (θ hm136 68 1 * θ hm8 2 1 + mono 4 1 * (θ hm136 34 1 * θ hm8 4 1)) := by
  have Q1 := quint1 hm8 hm24 rfl 2 14 22 8 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_refl1 hm24 10 14 (by norm_num), θ_refl1 hm24 2 22 (by norm_num)] at Q1
  rw [A4m]
  linear_combination (mono 4 1 * θ hm136 34 1) * Q1
    - (θ hm136 34 1 * θ hm24 2 1 * θ hm8 2 1) * mm 4 2 6 (by norm_num)

theorem B5p_c : B5p * (θ hm170 34 (-1) * θ hm170 68 (-1)) = θ hm510 170 1 *
    (θ hm10 4 1 * θ hm170 68 1 * θ hm170 68 (-1) + mono 14 1 * (θ hm10 2 1 * θ hm170 136 1 * θ hm170 34 (-1))) := by
  have Q1 := quintm hm170 hm510 rfl 34 272 442 170 68 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q2 := quintm hm170 hm510 rfl 68 374 544 170 136 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_reflm hm510 238 272 (by norm_num), θ_reflm hm510 68 442 (by norm_num)] at Q1
  rw [θ_reflm hm510 136 374 (by norm_num),
    θ_sh hm510 34 1 (by norm_num : (-1 : ℂ) ≠ 0) (-34) 1 (e := 544) (by norm_num) (by norm_num [c2]) (by norm_num)] at Q2
  rw [B5p]
  linear_combination (θ hm10 4 1 * θ hm170 68 (-1)) * Q1 + (mono 14 1 * θ hm10 2 1 * θ hm170 34 (-1)) * Q2
    + (mono 14 1 * θ hm10 2 1 * θ hm510 34 (-1) * θ hm170 34 (-1) * θ hm170 68 (-1)) * mm 68 (-34) 34 (by norm_num)
    + (θ hm10 2 1 * θ hm510 34 (-1) * θ hm170 34 (-1) * θ hm170 68 (-1)) * mm 14 34 48 (by norm_num)

theorem B5m_c : B5m * (θ hm170 34 1 * θ hm170 68 1) = θ hm510 170 1 *
    (θ hm10 4 (-1) * θ hm170 68 1 * θ hm170 68 1 - mono 14 1 * (θ hm10 2 (-1) * θ hm170 136 1 * θ hm170 34 1)
      - mono 8 1 * (θ hm10 0 (-1) * θ hm170 34 1 * θ hm170 68 1)) := by
  have Q1 := quint1 hm170 hm510 rfl 34 272 442 170 68 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q2 := quint1 hm170 hm510 rfl 68 374 544 170 136 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_refl1 hm510 238 272 (by norm_num), θ_refl1 hm510 68 442 (by norm_num)] at Q1
  rw [θ_refl1 hm510 136 374 (by norm_num),
    θ_sh hm510 34 1 one_ne_zero (-34) (-1) (e := 544) (by norm_num) (by norm_num [c2]) (by norm_num), mono_neg1] at Q2
  rw [B5m]
  linear_combination (θ hm10 4 (-1) * θ hm170 68 1) * Q1 - (mono 14 1 * θ hm10 2 (-1) * θ hm170 34 1) * Q2
    - (mono 14 1 * θ hm10 2 (-1) * θ hm510 34 1 * θ hm170 34 1 * θ hm170 68 1) * mm 68 (-34) 34 (by norm_num)
    - (θ hm10 2 (-1) * θ hm510 34 1 * θ hm170 34 1 * θ hm170 68 1) * mm 14 34 48 (by norm_num)

end Forty
