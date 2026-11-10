/-
# Entry 3.29: the two lattice identities (Yesilyurt, JMAA 388 (2012) §4, in Cao's language)

With `Q = q²³`, `A(q) = G(q²)G(Q) + q⁵H(q²)H(Q)` and `B(q) = H(q)G(Q²) − q⁹G(q)H(Q²)`.

Yesilyurt's `R₂(1,0,0,1,3,23,2,5) = R₂(1,−9,0,4,69,1,1,10)` (his (4.1)) is a Type II identity: his sums `R` are
sums of the binary form `λM² + 2αm MJ + αp J² + …` (`scripts/forty/round8/rsum.py`), here
`7x² + 12xy + 15y² + 5x + y`, split by the orthogonal covers `(−5 0; 2 −1)` (determinant 5) and `(−1 −9; 1 −1)`
(determinant 10). With sign `(−1)^x` this is `L29p`; with sign `(−1)^y` (his `R₂(0,1,0,1,…)`, the sum behind his
closing remark) it is `L29m`. The determinant-10 sides are `Ye ∓ Yo` with the same two groups of terms.

Four quintuple collapses at nome `t⁴⁶⁰ = Q²⁰` evaluate the groups (`Yo_c`, `Ye_c`); two at nome `t¹⁰` evaluate the
determinant-5 sides (`D5p_c`, `D5m_c`). Here `t = q`.
-/
import RamanujanTau.Forty.E29a
import RamanujanTau.Forty.E30
import RamanujanTau.Forty.E16
import RamanujanTau.Forty.E13

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm460 : 1 ≤ 460 := by norm_num
private lemma hm20 : 1 ≤ 20 := by norm_num
private lemma hm30 : 1 ≤ 30 := by norm_num
private lemma hm230 : 1 ≤ 230 := by norm_num
private lemma hm1380 : 1 ≤ 1380 := by norm_num

/-- Entry 29p, side a: `B = (-5 0; 2 -1)`, shifts `i (1, 0)`, `i ∈ {(-3), (-2), (-1), 0, 1}`. -/
def B29pa : ECS where
  b11 := (-5)
  b12 := 0
  b21 := 2
  b22 := (-1)
  r1 := 1
  r2 := 0
  I := {(-3), (-2), (-1), 0, 1}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - (-3)) % 5 + (-3)), by simp only [mem_insert, mem_singleton]; omega,
    (((-1) * (m - 1 * ((1 * m + 0 * n - (-3)) % 5 + (-3))) - 0 * (n - 0 * ((1 * m + 0 * n - (-3)) % 5 + (-3)))) / 5), (((-5) * (n - 0 * ((1 * m + 0 * n - (-3)) % 5 + (-3))) - 2 * (m - 1 * ((1 * m + 0 * n - (-3)) % 5 + (-3)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- Entry 29p, side b: `B = (-1 -9; 1 -1)`, shifts `i (1, 0)`, `i ∈ {(-6), (-5), (-4), (-3), (-2), (-1), 0, 1, 2, 3}`. -/
def B29pb : ECS where
  b11 := (-1)
  b12 := (-9)
  b21 := 1
  b22 := (-1)
  r1 := 1
  r2 := 0
  I := {(-6), (-5), (-4), (-3), (-2), (-1), 0, 1, 2, 3}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 1 * n - (-6)) % 10 + (-6)), by simp only [mem_insert, mem_singleton]; omega,
    (((-1) * (m - 1 * ((1 * m + 1 * n - (-6)) % 10 + (-6))) - (-9) * (n - 0 * ((1 * m + 1 * n - (-6)) % 10 + (-6)))) / 10), (((-1) * (n - 0 * ((1 * m + 1 * n - (-6)) % 10 + (-6))) - 1 * (m - 1 * ((1 * m + 1 * n - (-6)) % 10 + (-6)))) / 10), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L29p : (θ hm230 92 1 * θ hm30 14 (-1)) - (mono 2 1 * (θ hm230 92 1 * θ hm30 4 (-1))) + (mono 10 1 * (θ hm230 46 1 * θ hm30 8 (-1))) - (mono 12 1 * (θ hm230 46 1 * θ hm30 2 (-1))) = (θ hm20 6 1 * θ hm1380 644 1) - (mono 2 1 * (θ hm20 8 1 * θ hm1380 598 1)) - (mono 12 1 * (θ hm20 4 1 * θ hm1380 506 1)) + (mono 18 1 * (θ hm20 10 1 * θ hm1380 460 1)) + (mono 38 1 * (θ hm20 2 1 * θ hm1380 368 1)) - (mono 48 1 * (θ hm20 8 1 * θ hm1380 322 1)) + (mono 92 1 * (θ hm20 6 1 * θ hm1380 184 1)) - (mono 130 1 * (θ hm20 2 1 * θ hm1380 92 1)) - (mono 150 1 * (θ hm20 4 1 * θ hm1380 46 1)) := by
  have h := qf_two 7 6 15 5 1 1 0 B29pa B29pb
    hm230 hm30 hm20 hm1380 (by norm_num [B29pa]) (by norm_num [B29pa]) (by norm_num [B29pa])
    (by norm_num [B29pb]) (by norm_num [B29pb]) (by norm_num [B29pb])
  simp only [B29pa, B29pb] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm1380 184 0 0 1 (e := 1196) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm1380 322 0 0 1 (e := 1058) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm1380 46 0 0 1 (e := 1334) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm1380 460 0 0 1 (e := 920) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm1380 598 0 0 1 (e := 782) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 2 0 0 1 (e := 18) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 4 0 0 1 (e := 16) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 6 0 0 1 (e := 14) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 8 0 0 1 (e := 12) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm230 46 0 0 1 (e := 184) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm230 92 0 0 1 (e := 138) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm30 10 1 (-20) 1 (e := 50) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm30 4 0 0 1 (e := 26) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm1380 92 1 one_ne_zero (-92) (-1) (e := 1472) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm30 8 1 (by norm_num : (-1 : ℂ) ≠ 0) (-8) 1 (e := 38) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm20 0 (e := 0) (by norm_num), θz' hm230 1 (e := 230) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h

/-- Entry 29m, side a: `B = (-5 0; 2 -1)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B29ma : ECS where
  b11 := (-5)
  b12 := 0
  b21 := 2
  b22 := (-1)
  r1 := 1
  r2 := 0
  I := {(-2), (-1), 0, 1, 2}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - (-2)) % 5 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    (((-1) * (m - 1 * ((1 * m + 0 * n - (-2)) % 5 + (-2))) - 0 * (n - 0 * ((1 * m + 0 * n - (-2)) % 5 + (-2)))) / 5), (((-5) * (n - 0 * ((1 * m + 0 * n - (-2)) % 5 + (-2))) - 2 * (m - 1 * ((1 * m + 0 * n - (-2)) % 5 + (-2)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- Entry 29m, side b: `B = (-1 -9; 1 -1)`, shifts `i (1, 0)`, `i ∈ {(-6), (-5), (-4), (-3), (-2), (-1), 0, 1, 2, 3}`. -/
def B29mb : ECS where
  b11 := (-1)
  b12 := (-9)
  b21 := 1
  b22 := (-1)
  r1 := 1
  r2 := 0
  I := {(-6), (-5), (-4), (-3), (-2), (-1), 0, 1, 2, 3}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 1 * n - (-6)) % 10 + (-6)), by simp only [mem_insert, mem_singleton]; omega,
    (((-1) * (m - 1 * ((1 * m + 1 * n - (-6)) % 10 + (-6))) - (-9) * (n - 0 * ((1 * m + 1 * n - (-6)) % 10 + (-6)))) / 10), (((-1) * (n - 0 * ((1 * m + 1 * n - (-6)) % 10 + (-6))) - 1 * (m - 1 * ((1 * m + 1 * n - (-6)) % 10 + (-6)))) / 10), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L29m : (θ hm230 92 (-1) * θ hm30 14 1) + (mono 2 1 * (θ hm230 92 (-1) * θ hm30 4 1)) - (mono 10 1 * (θ hm230 46 (-1) * θ hm30 8 1)) + (mono 12 1 * (θ hm230 46 (-1) * θ hm30 2 1)) - (mono 28 1 * (θ hm230 0 (-1) * θ hm30 10 1)) = (θ hm20 6 1 * θ hm1380 644 1) + (mono 2 1 * (θ hm20 8 1 * θ hm1380 598 1)) + (mono 12 1 * (θ hm20 4 1 * θ hm1380 506 1)) + (mono 18 1 * (θ hm20 10 1 * θ hm1380 460 1)) + (mono 38 1 * (θ hm20 2 1 * θ hm1380 368 1)) + (mono 48 1 * (θ hm20 8 1 * θ hm1380 322 1)) + (mono 92 1 * (θ hm20 6 1 * θ hm1380 184 1)) - (mono 130 1 * (θ hm20 2 1 * θ hm1380 92 1)) + (mono 150 1 * (θ hm20 4 1 * θ hm1380 46 1)) := by
  have h := qf_two 7 6 15 5 1 0 1 B29ma B29mb
    hm230 hm30 hm20 hm1380 (by norm_num [B29ma]) (by norm_num [B29ma]) (by norm_num [B29ma])
    (by norm_num [B29mb]) (by norm_num [B29mb]) (by norm_num [B29mb])
  simp only [B29ma, B29mb] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm1380 184 0 0 1 (e := 1196) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm1380 322 0 0 1 (e := 1058) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm1380 46 0 0 1 (e := 1334) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm1380 460 0 0 1 (e := 920) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm1380 598 0 0 1 (e := 782) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 2 0 0 1 (e := 18) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 4 0 0 1 (e := 16) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 6 0 0 1 (e := 14) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm20 8 0 0 1 (e := 12) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm30 10 (-1) (-10) (-1) (e := (-10)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm30 4 0 0 1 (e := 26) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm230 46 0 0 1 (e := 184) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm230 92 0 0 1 (e := 138) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm1380 92 1 one_ne_zero (-92) (-1) (e := 1472) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm30 8 1 one_ne_zero (-8) (-1) (e := 38) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm20 0 (e := 0) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- the odd group of the determinant-10 side. -/
noncomputable def Yo : L := mono 2 1 * (θ hm20 8 1 * θ hm1380 598 1) + mono 12 1 * (θ hm20 4 1 * θ hm1380 506 1)
  + mono 48 1 * (θ hm20 8 1 * θ hm1380 322 1) + mono 150 1 * (θ hm20 4 1 * θ hm1380 46 1)

/-- the even group of the determinant-10 side. -/
noncomputable def Ye : L := θ hm20 6 1 * θ hm1380 644 1 + mono 18 1 * (θ hm20 10 1 * θ hm1380 460 1)
  + mono 38 1 * (θ hm20 2 1 * θ hm1380 368 1) + mono 92 1 * (θ hm20 6 1 * θ hm1380 184 1)
  - mono 130 1 * (θ hm20 2 1 * θ hm1380 92 1)

/-- the determinant-5 side of `L29p`. -/
noncomputable def D5p : L := (θ hm230 92 1 * θ hm30 14 (-1)) - (mono 2 1 * (θ hm230 92 1 * θ hm30 4 (-1)))
  + (mono 10 1 * (θ hm230 46 1 * θ hm30 8 (-1))) - (mono 12 1 * (θ hm230 46 1 * θ hm30 2 (-1)))

/-- the determinant-5 side of `L29m`. -/
noncomputable def D5m : L := (θ hm230 92 (-1) * θ hm30 14 1) + (mono 2 1 * (θ hm230 92 (-1) * θ hm30 4 1))
  - (mono 10 1 * (θ hm230 46 (-1) * θ hm30 8 1)) + (mono 12 1 * (θ hm230 46 (-1) * θ hm30 2 1))
  - (mono 28 1 * (θ hm230 0 (-1) * θ hm30 10 1))

theorem D5p_eq : D5p = Ye - Yo := by rw [D5p, Ye, Yo, L29p]; ring

theorem D5m_eq : D5m = Ye + Yo := by rw [D5m, Ye, Yo, L29m]; ring

private lemma mm (a b c : ℤ) (h : a + b = c) : (mono a 1 : L) * mono b 1 = mono c 1 := by
  rw [mono_mul, h]; norm_num

/-- the odd group collapsed (quintuple product at `c = 1`, `N = 460`, `e = 46, 138`). -/
theorem Yo_c : Yo * (θ hm460 46 1 * θ hm460 138 1) = θ hm1380 460 1 *
    (mono 2 1 * (θ hm20 8 1 * θ hm460 92 1 * θ hm460 138 1) + mono 12 1 * (θ hm20 4 1 * θ hm460 184 1 * θ hm460 46 1)) := by
  have Q1 := quint1 hm460 hm1380 rfl 46 598 1058 460 92 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q2 := quint1 hm460 hm1380 rfl 138 874 1334 460 276 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_refl1 hm1380 322 1058 (by norm_num)] at Q1
  rw [θ_refl1 hm1380 506 874 (by norm_num), θ_refl1 hm1380 46 1334 (by norm_num),
    θ_refl1 hm460 184 276 (by norm_num)] at Q2
  rw [Yo]
  linear_combination (mono 2 1 * θ hm20 8 1 * θ hm460 138 1) * Q1 + (mono 12 1 * θ hm20 4 1 * θ hm460 46 1) * Q2
    - (θ hm20 8 1 * θ hm1380 322 1 * θ hm460 46 1 * θ hm460 138 1) * mm 2 46 48 (by norm_num)
    - (θ hm20 4 1 * θ hm1380 46 1 * θ hm460 46 1 * θ hm460 138 1) * mm 12 138 150 (by norm_num)

/-- the even group collapsed (`e = 92, 184`). -/
theorem Ye_c : Ye * (θ hm460 92 1 * θ hm460 184 1) = θ hm1380 460 1 *
    (θ hm20 6 1 * θ hm460 184 1 * θ hm460 184 1 + mono 38 1 * (θ hm20 2 1 * θ hm460 92 1 * θ hm460 92 1)
      + mono 18 1 * (θ hm20 10 1 * θ hm460 92 1 * θ hm460 184 1)) := by
  have Q1 := quint1 hm460 hm1380 rfl 92 736 1196 460 184 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q2 := quint1 hm460 hm1380 rfl 184 1012 1472 460 368 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_refl1 hm1380 644 736 (by norm_num), θ_refl1 hm1380 184 1196 (by norm_num)] at Q1
  rw [θ_refl1 hm1380 368 1012 (by norm_num), θ_refl1 hm460 92 368 (by norm_num),
    θ_sh hm1380 92 1 one_ne_zero (-92) (-1) (e := 1472) (by norm_num) (by norm_num [c2]) (by norm_num), mono_neg1] at Q2
  rw [Ye]
  have m3 : (mono 184 1 : L) * mono (-92) 1 = mono 92 1 := mm 184 (-92) 92 (by norm_num)
  linear_combination (θ hm20 6 1 * θ hm460 184 1) * Q1 + (mono 38 1 * θ hm20 2 1 * θ hm460 92 1) * Q2
    + (mono 38 1 * θ hm20 2 1 * θ hm1380 92 1 * θ hm460 92 1 * θ hm460 184 1) * m3
    + (θ hm20 2 1 * θ hm1380 92 1 * θ hm460 92 1 * θ hm460 184 1) * mm 38 92 130 (by norm_num)

/-- the determinant-5 side of `L29p` collapsed (`c = −1`, `N = 10`, `e = 2, 4`). -/
theorem D5p_c : D5p * (θ hm10 2 (-1) * θ hm10 4 (-1)) = θ hm30 10 1 *
    (θ hm230 92 1 * θ hm10 4 1 * θ hm10 4 (-1) + mono 10 1 * (θ hm230 46 1 * θ hm10 8 1 * θ hm10 2 (-1))) := by
  have Q1 := quintm hm10 hm30 rfl 2 16 26 10 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q2 := quintm hm10 hm30 rfl 4 22 32 10 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_reflm hm30 14 16 (by norm_num), θ_reflm hm30 4 26 (by norm_num)] at Q1
  rw [θ_reflm hm30 8 22 (by norm_num),
    θ_sh hm30 2 1 (by norm_num : (-1 : ℂ) ≠ 0) (-2) 1 (e := 32) (by norm_num) (by norm_num [c2]) (by norm_num)] at Q2
  rw [D5p]
  linear_combination (θ hm230 92 1 * θ hm10 4 (-1)) * Q1 + (mono 10 1 * θ hm230 46 1 * θ hm10 2 (-1)) * Q2
    + (mono 10 1 * θ hm230 46 1 * θ hm30 2 (-1) * θ hm10 2 (-1) * θ hm10 4 (-1)) * mm 4 (-2) 2 (by norm_num)
    + (θ hm230 46 1 * θ hm30 2 (-1) * θ hm10 2 (-1) * θ hm10 4 (-1)) * mm 10 2 12 (by norm_num)

/-- the determinant-5 side of `L29m` collapsed (`c = 1`, `N = 10`, `e = 2, 4`). -/
theorem D5m_c : D5m * (θ hm10 2 1 * θ hm10 4 1) = θ hm30 10 1 *
    (θ hm230 92 (-1) * θ hm10 4 1 * θ hm10 4 1 - mono 10 1 * (θ hm230 46 (-1) * θ hm10 8 1 * θ hm10 2 1)
      - mono 28 1 * (θ hm230 0 (-1) * θ hm10 2 1 * θ hm10 4 1)) := by
  have Q1 := quint1 hm10 hm30 rfl 2 16 26 10 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q2 := quint1 hm10 hm30 rfl 4 22 32 10 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_refl1 hm30 14 16 (by norm_num), θ_refl1 hm30 4 26 (by norm_num)] at Q1
  rw [θ_refl1 hm30 8 22 (by norm_num),
    θ_sh hm30 2 1 one_ne_zero (-2) (-1) (e := 32) (by norm_num) (by norm_num [c2]) (by norm_num), mono_neg1] at Q2
  rw [D5m]
  linear_combination (θ hm230 92 (-1) * θ hm10 4 1) * Q1 - (mono 10 1 * θ hm230 46 (-1) * θ hm10 2 1) * Q2
    - (mono 10 1 * θ hm230 46 (-1) * θ hm30 2 1 * θ hm10 2 1 * θ hm10 4 1) * mm 4 (-2) 2 (by norm_num)
    - (θ hm230 46 (-1) * θ hm30 2 1 * θ hm10 2 1 * θ hm10 4 1) * mm 10 2 12 (by norm_num)

end Forty
