/-
# Entry 3.35: the two lattice identities (Yesilyurt, JMAA 388 (2012) §5, in Cao's language)

With `Q = q⁴⁷`, Yesilyurt's `A(q) = H(q²)G(Q) − q⁹G(q²)H(Q)` and `B(q) = G(q)G(Q²) + q¹⁹H(q)H(Q²)`.
His `R₂(1,0,1,1,3,47,1,5) = R₁(−1,0,1,0,4,1,141,3,10)` ((5.1)) is the Type II identity of the form
`10x² + 6xy + 15y² + 12x + 13y` with sign `(−1)^x` (`L47p`), split by the covers `(−5 0; 1 −1)` (determinant 5) and
`(−1 3; 0 −10)` (determinant 10); with sign `(−1)^{x+y}` (cover `(5 0; −1 1)`) it is `L47m`. The determinant-10 sides
are `Ye47 ± Yo47`. Collapses: quintuple product at nome `t⁹⁴⁰ = Q²⁰` (`Yo47_c`, `Ye47_c`) and at `t¹⁰` (`D5p47_c`,
`D5m47_c`); `t = q`.
-/
import RamanujanTau.Forty.E29d

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm940 : 1 ≤ 940 := by norm_num
private lemma hm20 : 1 ≤ 20 := by norm_num
private lemma hm30 : 1 ≤ 30 := by norm_num
private lemma hm470 : 1 ≤ 470 := by norm_num
private lemma hm2820 : 1 ≤ 2820 := by norm_num

/-- E47p, side a: `B = (-5 0; 1 -1)`, shifts `i (1, 0)`, `i ∈ {(-4), (-3), (-2), (-1), 0}`. -/
def B47pa : ECS where
  b11 := (-5)
  b12 := 0
  b21 := 1
  b22 := (-1)
  r1 := 1
  r2 := 0
  I := {(-4), (-3), (-2), (-1), 0}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - (-4)) % 5 + (-4)), by simp only [mem_insert, mem_singleton]; omega,
    (((-1) * (m - 1 * ((1 * m + 0 * n - (-4)) % 5 + (-4))) - 0 * (n - 0 * ((1 * m + 0 * n - (-4)) % 5 + (-4)))) / 5), (((-5) * (n - 0 * ((1 * m + 0 * n - (-4)) % 5 + (-4))) - 1 * (m - 1 * ((1 * m + 0 * n - (-4)) % 5 + (-4)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- E47p, side b: `B = (-1 3; 0 -10)`, shifts `i (0, 1)`, `i ∈ {(-5), (-4), (-3), (-2), (-1), 0, 1, 2, 3, 4}`. -/
def B47pb : ECS where
  b11 := (-1)
  b12 := 3
  b21 := 0
  b22 := (-10)
  r1 := 0
  r2 := 1
  I := {(-5), (-4), (-3), (-2), (-1), 0, 1, 2, 3, 4}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-5)) % 10 + (-5)), by simp only [mem_insert, mem_singleton]; omega,
    (((-10) * (m - 0 * ((0 * m + 1 * n - (-5)) % 10 + (-5))) - 3 * (n - 1 * ((0 * m + 1 * n - (-5)) % 10 + (-5)))) / 10), (((-1) * (n - 1 * ((0 * m + 1 * n - (-5)) % 10 + (-5))) - 0 * (m - 0 * ((0 * m + 1 * n - (-5)) % 10 + (-5)))) / 10), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L47p : -((mono (-2) 1 * (θ hm470 188 1 * θ hm30 8 (-1)))) + (θ hm470 188 1 * θ hm30 2 (-1)) + (mono 16 1 * (θ hm470 94 1 * θ hm30 14 (-1))) - (mono 18 1 * (θ hm470 94 1 * θ hm30 4 (-1))) = -((mono (-2) 1 * (θ hm20 2 1 * θ hm2820 1316 1))) + (mono 2 1 * (θ hm20 4 1 * θ hm2820 1222 1)) - (mono 20 1 * (θ hm20 8 1 * θ hm2820 1034 1)) + (mono 34 1 * (θ hm20 10 1 * θ hm2820 940 1)) - (mono 72 1 * (θ hm20 6 1 * θ hm2820 752 1)) + (mono 96 1 * (θ hm20 4 1 * θ hm2820 658 1)) - (mono 186 1 * (θ hm20 2 1 * θ hm2820 376 1)) + (mono 260 1 * (θ hm20 6 1 * θ hm2820 188 1)) - (mono 302 1 * (θ hm20 8 1 * θ hm2820 94 1)) := by
  have h := qf_two 10 3 15 12 13 1 0 B47pa B47pb
    hm470 hm30 hm20 hm2820 (by norm_num [B47pa]) (by norm_num [B47pa]) (by norm_num [B47pa])
    (by norm_num [B47pb]) (by norm_num [B47pb]) (by norm_num [B47pb])
  simp only [B47pa, B47pb] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm20 2 (-1) (-2) (-1) (e := (-2)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 4 0 0 1 (e := 16) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 6 (-2) (-32) 1 (e := (-26)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 8 (-1) (-8) (-1) (e := (-8)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm2820 1222 0 0 1 (e := 1598) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm2820 376 0 0 1 (e := 2444) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm2820 658 0 0 1 (e := 2162) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm2820 94 0 0 1 (e := 2726) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm2820 940 0 0 1 (e := 1880) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm470 188 0 0 1 (e := 282) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm470 94 0 0 1 (e := 376) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm30 10 0 0 1 (e := 20) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm30 4 0 0 1 (e := 26) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm20 2 1 one_ne_zero (-2) (-1) (e := 22) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm20 6 (-1) one_ne_zero (-14) (-1) (e := (-14)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm20 8 1 one_ne_zero (-8) (-1) (e := 28) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm470 94 1 one_ne_zero (-94) (-1) (e := 564) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm20 (-1) (e := (-20)) (by norm_num), θz' hm470 1 (e := 470) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- Entry 47m, side a: `B = (5 0; -1 1)`, shifts `i (1, 0)`, `i ∈ {(-4), (-3), (-2), (-1), 0}`. -/
def B47ma : ECS where
  b11 := 5
  b12 := 0
  b21 := (-1)
  b22 := 1
  r1 := 1
  r2 := 0
  I := {(-4), (-3), (-2), (-1), 0}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - (-4)) % 5 + (-4)), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 0 * n - (-4)) % 5 + (-4))) - 0 * (n - 0 * ((1 * m + 0 * n - (-4)) % 5 + (-4)))) / 5), ((5 * (n - 0 * ((1 * m + 0 * n - (-4)) % 5 + (-4))) - (-1) * (m - 1 * ((1 * m + 0 * n - (-4)) % 5 + (-4)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- Entry 47m, side b: `B = (-1 3; 0 -10)`, shifts `i (0, 1)`, `i ∈ {(-5), (-4), (-3), (-2), (-1), 0, 1, 2, 3, 4}`. -/
def B47mb : ECS where
  b11 := (-1)
  b12 := 3
  b21 := 0
  b22 := (-10)
  r1 := 0
  r2 := 1
  I := {(-5), (-4), (-3), (-2), (-1), 0, 1, 2, 3, 4}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-5)) % 10 + (-5)), by simp only [mem_insert, mem_singleton]; omega,
    (((-10) * (m - 0 * ((0 * m + 1 * n - (-5)) % 10 + (-5))) - 3 * (n - 1 * ((0 * m + 1 * n - (-5)) % 10 + (-5)))) / 10), (((-1) * (n - 1 * ((0 * m + 1 * n - (-5)) % 10 + (-5))) - 0 * (m - 0 * ((0 * m + 1 * n - (-5)) % 10 + (-5)))) / 10), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L47m : -((mono (-2) 1 * (θ hm470 188 (-1) * θ hm30 8 1))) + (θ hm470 188 (-1) * θ hm30 2 1) + (mono 16 1 * (θ hm470 94 (-1) * θ hm30 14 1)) + (mono 18 1 * (θ hm470 94 (-1) * θ hm30 4 1)) - (mono 54 1 * (θ hm470 0 (-1) * θ hm30 10 1)) = -((mono (-2) 1 * (θ hm20 2 1 * θ hm2820 1316 1))) - (mono 2 1 * (θ hm20 4 1 * θ hm2820 1222 1)) + (mono 20 1 * (θ hm20 8 1 * θ hm2820 1034 1)) + (mono 34 1 * (θ hm20 10 1 * θ hm2820 940 1)) - (mono 72 1 * (θ hm20 6 1 * θ hm2820 752 1)) - (mono 96 1 * (θ hm20 4 1 * θ hm2820 658 1)) - (mono 186 1 * (θ hm20 2 1 * θ hm2820 376 1)) + (mono 260 1 * (θ hm20 6 1 * θ hm2820 188 1)) + (mono 302 1 * (θ hm20 8 1 * θ hm2820 94 1)) := by
  have h := qf_two 10 3 15 12 13 1 1 B47ma B47mb
    hm470 hm30 hm20 hm2820 (by norm_num [B47ma]) (by norm_num [B47ma]) (by norm_num [B47ma])
    (by norm_num [B47mb]) (by norm_num [B47mb]) (by norm_num [B47mb])
  simp only [B47ma, B47mb] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm20 2 (-1) (-2) (-1) (e := (-2)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 4 0 0 1 (e := 16) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 6 (-2) (-32) 1 (e := (-26)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 8 (-1) (-8) (-1) (e := (-8)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm2820 1222 0 0 1 (e := 1598) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm2820 376 0 0 1 (e := 2444) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm2820 658 0 0 1 (e := 2162) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm2820 94 0 0 1 (e := 2726) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm2820 940 0 0 1 (e := 1880) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm30 14 0 0 1 (e := 16) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm30 2 0 0 1 (e := 28) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm30 8 0 0 1 (e := 22) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm470 188 0 0 1 (e := 282) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm470 94 (-1) (-94) 1 (e := (-94)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm20 2 1 one_ne_zero (-2) (-1) (e := 22) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm20 6 (-1) one_ne_zero (-14) (-1) (e := (-14)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm20 8 1 one_ne_zero (-8) (-1) (e := 28) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm20 (-1) (e := (-20)) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


noncomputable def Yo47 : L := mono 2 1 * (θ hm20 4 1 * θ hm2820 1222 1) - mono 20 1 * (θ hm20 8 1 * θ hm2820 1034 1)
  + mono 96 1 * (θ hm20 4 1 * θ hm2820 658 1) - mono 302 1 * (θ hm20 8 1 * θ hm2820 94 1)

noncomputable def Ye47 : L := -(mono (-2) 1 * (θ hm20 2 1 * θ hm2820 1316 1)) + mono 34 1 * (θ hm20 10 1 * θ hm2820 940 1)
  - mono 72 1 * (θ hm20 6 1 * θ hm2820 752 1) - mono 186 1 * (θ hm20 2 1 * θ hm2820 376 1)
  + mono 260 1 * (θ hm20 6 1 * θ hm2820 188 1)

noncomputable def D5p47 : L := -((mono (-2) 1 * (θ hm470 188 1 * θ hm30 8 (-1)))) + (θ hm470 188 1 * θ hm30 2 (-1))
  + (mono 16 1 * (θ hm470 94 1 * θ hm30 14 (-1))) - (mono 18 1 * (θ hm470 94 1 * θ hm30 4 (-1)))

noncomputable def D5m47 : L := -((mono (-2) 1 * (θ hm470 188 (-1) * θ hm30 8 1))) + (θ hm470 188 (-1) * θ hm30 2 1)
  + (mono 16 1 * (θ hm470 94 (-1) * θ hm30 14 1)) + (mono 18 1 * (θ hm470 94 (-1) * θ hm30 4 1))
  - (mono 54 1 * (θ hm470 0 (-1) * θ hm30 10 1))

theorem D5p47_eq : D5p47 = Ye47 + Yo47 := by rw [D5p47, Ye47, Yo47, L47p]; ring
theorem D5m47_eq : D5m47 = Ye47 - Yo47 := by rw [D5m47, Ye47, Yo47, L47m]; ring

private lemma mm (a b c : ℤ) (h : a + b = c) : (mono a 1 : L) * mono b 1 = mono c 1 := by
  rw [mono_mul, h]; norm_num

private lemma m0 : (mono 0 1 : L) = 1 := rfl

theorem Yo47_c : Yo47 * (θ hm940 94 1 * θ hm940 282 1) = θ hm2820 940 1 *
    (mono 2 1 * (θ hm20 4 1 * θ hm940 188 1 * θ hm940 282 1) - mono 20 1 * (θ hm20 8 1 * θ hm940 376 1 * θ hm940 94 1)) := by
  have Q1 := quint1 hm940 hm2820 rfl 94 1222 2162 940 188 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q2 := quint1 hm940 hm2820 rfl 282 1786 2726 940 564 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_refl1 hm2820 658 2162 (by norm_num)] at Q1
  rw [θ_refl1 hm2820 1034 1786 (by norm_num), θ_refl1 hm2820 94 2726 (by norm_num),
    θ_refl1 hm940 376 564 (by norm_num)] at Q2
  rw [Yo47]
  linear_combination (mono 2 1 * θ hm20 4 1 * θ hm940 282 1) * Q1 - (mono 20 1 * θ hm20 8 1 * θ hm940 94 1) * Q2
    - (θ hm20 4 1 * θ hm2820 658 1 * θ hm940 94 1 * θ hm940 282 1) * mm 2 94 96 (by norm_num)
    + (θ hm20 8 1 * θ hm2820 94 1 * θ hm940 94 1 * θ hm940 282 1) * mm 20 282 302 (by norm_num)

theorem Ye47_c : Ye47 * (θ hm940 188 1 * θ hm940 376 1) = θ hm2820 940 1 *
    (-(mono (-2) 1 * (θ hm20 2 1 * θ hm940 376 1 * θ hm940 376 1)) - mono 72 1 * (θ hm20 6 1 * θ hm940 188 1 * θ hm940 188 1)
      + mono 34 1 * (θ hm20 10 1 * θ hm940 188 1 * θ hm940 376 1)) := by
  have Q3 := quint1 hm940 hm2820 rfl 188 1504 2444 940 376 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q4 := quint1 hm940 hm2820 rfl 376 2068 3008 940 752 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_refl1 hm2820 1316 1504 (by norm_num), θ_refl1 hm2820 376 2444 (by norm_num)] at Q3
  rw [θ_refl1 hm2820 752 2068 (by norm_num), θ_refl1 hm940 188 752 (by norm_num),
    θ_sh hm2820 188 1 one_ne_zero (-188) (-1) (e := 3008) (by norm_num) (by norm_num [c2]) (by norm_num), mono_neg1] at Q4
  rw [Ye47]
  linear_combination (-(mono (-2) 1 * θ hm20 2 1 * θ hm940 376 1)) * Q3 - (mono 72 1 * θ hm20 6 1 * θ hm940 188 1) * Q4
    + (θ hm20 2 1 * θ hm2820 376 1 * θ hm940 188 1 * θ hm940 376 1) * mm (-2) 188 186 (by norm_num)
    - (mono 72 1 * θ hm20 6 1 * θ hm2820 188 1 * θ hm940 188 1 * θ hm940 376 1) * mm 376 (-188) 188 (by norm_num)
    - (θ hm20 6 1 * θ hm2820 188 1 * θ hm940 188 1 * θ hm940 376 1) * mm 72 188 260 (by norm_num)

theorem D5p47_c : D5p47 * (θ hm10 4 (-1) * θ hm10 2 (-1)) = θ hm30 10 1 *
    (-(mono (-2) 1 * (θ hm470 188 1 * θ hm10 8 1 * θ hm10 2 (-1))) + mono 16 1 * (θ hm470 94 1 * θ hm10 4 1 * θ hm10 4 (-1))) := by
  have Q5 := quintm hm10 hm30 rfl 4 22 32 10 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q6 := quintm hm10 hm30 rfl 2 16 26 10 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_reflm hm30 8 22 (by norm_num),
    θ_sh hm30 2 1 (by norm_num : (-1 : ℂ) ≠ 0) (-2) 1 (e := 32) (by norm_num) (by norm_num [c2]) (by norm_num)] at Q5
  rw [θ_reflm hm30 14 16 (by norm_num), θ_reflm hm30 4 26 (by norm_num)] at Q6
  rw [D5p47]
  linear_combination (-(mono (-2) 1 * θ hm470 188 1 * θ hm10 2 (-1))) * Q5 + (mono 16 1 * θ hm470 94 1 * θ hm10 4 (-1)) * Q6
    - (mono (-2) 1 * θ hm470 188 1 * θ hm30 2 (-1) * θ hm10 4 (-1) * θ hm10 2 (-1)) * mm 4 (-2) 2 (by norm_num)
    - (θ hm470 188 1 * θ hm30 2 (-1) * θ hm10 4 (-1) * θ hm10 2 (-1)) * mm (-2) 2 0 (by norm_num)
    - (θ hm470 188 1 * θ hm30 2 (-1) * θ hm10 4 (-1) * θ hm10 2 (-1)) * m0
    + (θ hm470 94 1 * θ hm30 4 (-1) * θ hm10 4 (-1) * θ hm10 2 (-1)) * mm 16 2 18 (by norm_num)

theorem D5m47_c : D5m47 * (θ hm10 4 1 * θ hm10 2 1) = θ hm30 10 1 *
    (-(mono (-2) 1 * (θ hm470 188 (-1) * θ hm10 8 1 * θ hm10 2 1)) + mono 16 1 * (θ hm470 94 (-1) * θ hm10 4 1 * θ hm10 4 1)
      - mono 54 1 * (θ hm470 0 (-1) * θ hm10 2 1 * θ hm10 4 1)) := by
  have Q5 := quint1 hm10 hm30 rfl 4 22 32 10 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q6 := quint1 hm10 hm30 rfl 2 16 26 10 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_refl1 hm30 8 22 (by norm_num),
    θ_sh hm30 2 1 one_ne_zero (-2) (-1) (e := 32) (by norm_num) (by norm_num [c2]) (by norm_num), mono_neg1] at Q5
  rw [θ_refl1 hm30 14 16 (by norm_num), θ_refl1 hm30 4 26 (by norm_num)] at Q6
  rw [D5m47]
  linear_combination (-(mono (-2) 1 * θ hm470 188 (-1) * θ hm10 2 1)) * Q5 + (mono 16 1 * θ hm470 94 (-1) * θ hm10 4 1) * Q6
    - (mono (-2) 1 * θ hm470 188 (-1) * θ hm30 2 1 * θ hm10 4 1 * θ hm10 2 1) * mm 4 (-2) 2 (by norm_num)
    - (θ hm470 188 (-1) * θ hm30 2 1 * θ hm10 4 1 * θ hm10 2 1) * mm (-2) 2 0 (by norm_num)
    - (θ hm470 188 (-1) * θ hm30 2 1 * θ hm10 4 1 * θ hm10 2 1) * m0
    - (θ hm470 94 (-1) * θ hm30 4 1 * θ hm10 4 1 * θ hm10 2 1) * mm 16 2 18 (by norm_num)

end Forty
