/-
# Entry 3.16 (second equality), part A: the two lattice identities

See `E16ii.lean` for the argument.

# Entry 3.16 (second equality): `G(q²)G(q¹³) + q³H(q²)H(q¹³) = √(χ(−q¹³)/χ(−q) − qχ(−q)/χ(−q¹³))`

Berndt et al., Mem. AMS 188 (2007), §19, rewritten without the operator `L` (integral part of a `q^{1/5}`-series).
Write `a₁ = f(−q⁴,−q⁶)`, `a₂ = f(−q²,−q⁸)`, `b₁ = f(−q²⁶,−q³⁹)`, `b₂ = f(−q¹³,−q⁵²)` and
`A = a₁b₁ + q³a₂b₂ = {G(q²)G(q¹³) + q³H(q²)H(q¹³)} f(−q²)f(−q¹³)`.

* The memoir's Lemma 5.1 is used only through its components, which are four instances of the quintuple product
  (`quint1`): `a₂E₀ = f(−q¹⁰)a₁`, `a₁E₄ = f(−q¹⁰)a₂` with `E₀ = f(−q¹⁴,−q¹⁶) + q²f(−q⁴,−q²⁶)`,
  `E₄ = f(−q⁸,−q²²) − q²f(−q²,−q²⁸)`, and the same at `q¹³` (`G₀`, `G₄`). Hence (`core16`)
  `A² = f(−q²)f(−q¹³){E₀G₀ + 2q³f(−q¹⁰)f(−q⁶⁵) + q⁶E₄G₄}`, which is (19.10) without `L`.
* (19.11)/(19.17): Type I, `B = (2 −13; 1 1)` on `f(1,q)φ(−q¹³)` (`L16_1`, `P16_1`).
* (19.13)/(19.19)–(19.24): Type II on `3x²+10xy+17y²−x+7y` (at `t² = q`), covers `(−5 −1; 3 0)` (det 3, one
  coset vanishes) and `(−1 11; −1 −4)` (det 15) (`L16_2`, `P16_2`).
* Adding them: the bracket equals `ψ(q)φ(−q¹³) − qf(−q)f(−q²⁶)` (`brk16`), and the products give (19.25).

The square root is fixed by the constant term: `entry_3_16_ii_unique`.
-/
import RamanujanTau.Forty.E16

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm1 : 1 ≤ 1 := by norm_num
private lemma hm6 : 1 ≤ 6 := by norm_num
private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm26 : 1 ≤ 26 := by norm_num
private lemma hm30 : 1 ≤ 30 := by norm_num
private lemma hm60 : 1 ≤ 60 := by norm_num
private lemma hm65 : 1 ≤ 65 := by norm_num
private lemma hm156 : 1 ≤ 156 := by norm_num
private lemma hm195 : 1 ≤ 195 := by norm_num
private lemma hm390 : 1 ≤ 390 := by norm_num


/-- Entry 16.2, side a: `B = (-5 -1; 3 0)`, shifts `i (0, 1)`, `i ∈ {(-2), (-1), 0}`. -/
def B16_2a : ECS where
  b11 := (-5)
  b12 := (-1)
  b21 := 3
  b22 := 0
  r1 := 0
  r2 := 1
  I := {(-2), (-1), 0}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-2)) % 3 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    ((0 * (m - 0 * ((0 * m + 1 * n - (-2)) % 3 + (-2))) - (-1) * (n - 1 * ((0 * m + 1 * n - (-2)) % 3 + (-2)))) / 3), (((-5) * (n - 1 * ((0 * m + 1 * n - (-2)) % 3 + (-2))) - 3 * (m - 0 * ((0 * m + 1 * n - (-2)) % 3 + (-2)))) / 3), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- Entry 16.2, side b: `B = (-1 11; -1 -4)`, shifts `i (1, 0)`, `i ∈ {(-6), (-5), (-4), (-3), (-2), (-1), 0, 1, 2, 3, 4, 5, 6, 7, 8}`. -/
def B16_2b : ECS where
  b11 := (-1)
  b12 := 11
  b21 := (-1)
  b22 := (-4)
  r1 := 1
  r2 := 0
  I := {(-6), (-5), (-4), (-3), (-2), (-1), 0, 1, 2, 3, 4, 5, 6, 7, 8}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 14 * n - (-6)) % 15 + (-6)), by simp only [mem_insert, mem_singleton]; omega,
    (((-4) * (m - 1 * ((1 * m + 14 * n - (-6)) % 15 + (-6))) - 11 * (n - 0 * ((1 * m + 14 * n - (-6)) % 15 + (-6)))) / 15), (((-1) * (n - 0 * ((1 * m + 14 * n - (-6)) % 15 + (-6))) - (-1) * (m - 1 * ((1 * m + 14 * n - (-6)) % 15 + (-6)))) / 15), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L16_2 : 2 * (θ hm156 52 1 * θ hm6 2 1) = 2 * (θ hm60 24 1 * θ hm390 156 1) - 2 * (mono 2 1 * (θ hm60 8 1 * θ hm390 182 1)) - 2 * (mono 4 1 * (θ hm60 20 1 * θ hm390 130 1)) + 2 * (mono 14 1 * (θ hm60 4 1 * θ hm390 104 1)) + 2 * (mono 18 1 * (θ hm60 12 1 * θ hm390 78 1)) - 2 * (mono 24 1 * (θ hm60 28 1 * θ hm390 52 1)) + 2 * (mono 36 1 * (θ hm60 16 1 * θ hm390 26 1)) := by
  have h := qf_two 3 5 17 (-1) 7 1 0 B16_2a B16_2b
    hm156 hm6 hm60 hm390 (by norm_num [B16_2a]) (by norm_num [B16_2a]) (by norm_num [B16_2a])
    (by norm_num [B16_2b]) (by norm_num [B16_2b]) (by norm_num [B16_2b])
  simp only [B16_2a, B16_2b] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm156 52 0 0 1 (e := 104) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm390 104 0 0 1 (e := 286) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm390 130 0 0 1 (e := 260) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm390 156 0 0 1 (e := 234) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm390 182 0 0 1 (e := 208) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm390 26 0 0 1 (e := 364) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm390 52 0 0 1 (e := 338) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm390 78 0 0 1 (e := 312) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm6 2 0 0 1 (e := 4) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm60 12 (-2) (-84) 1 (e := (-72)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm60 16 1 (-44) (-1) (e := 104) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm60 20 0 0 1 (e := 40) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm60 24 (-1) (-24) (-1) (e := (-24)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm60 28 (-2) (-116) 1 (e := (-88)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm60 4 0 0 1 (e := 56) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm60 8 (-1) (-8) (-1) (e := (-8)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm6 2 2 one_ne_zero (-10) 1 (e := 14) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm60 12 1 one_ne_zero (-12) (-1) (e := 72) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm60 16 (-2) one_ne_zero (-148) 1 (e := (-104)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm60 20 (-1) one_ne_zero (-40) (-1) (e := (-40)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm60 28 1 one_ne_zero (-28) (-1) (e := 88) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm60 4 (-1) one_ne_zero (-56) (-1) (e := (-56)) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm156 0 (e := 0) (by norm_num), θz' hm390 0 (e := 0) (by norm_num), θz' hm6 4 (e := 24) (by norm_num), θz' hm60 2 (e := 120) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- the product form of `L16_2` in `ℤ⟦q⟧`. -/
theorem P16_2 : (J 26 78 * J 1 3) = (J 12 30 * J 78 195) - (PowerSeries.X ^ 1 * (J 4 30 * J 91 195)) - (PowerSeries.X ^ 2 * (J 10 30 * J 65 195)) + (PowerSeries.X ^ 7 * (J 2 30 * J 52 195)) + (PowerSeries.X ^ 9 * (J 6 30 * J 39 195)) - (PowerSeries.X ^ 12 * (J 14 30 * J 26 195)) + (PowerSeries.X ^ 18 * (J 8 30 * J 13 195)) := by
  apply S_inj 2
  have h := L16_2
  rw [θu' hm6 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num), θu' hm60 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num), θu' hm60 8 (e' := 8) (by norm_num) (by norm_num) (by norm_num), θu' hm60 12 (e' := 12) (by norm_num) (by norm_num) (by norm_num), θu' hm60 16 (e' := 16) (by norm_num) (by norm_num) (by norm_num), θu' hm60 20 (e' := 20) (by norm_num) (by norm_num) (by norm_num), θu' hm60 24 (e' := 24) (by norm_num) (by norm_num) (by norm_num), θu' hm60 28 (e' := 28) (by norm_num) (by norm_num) (by norm_num), θu' hm156 52 (e' := 52) (by norm_num) (by norm_num) (by norm_num), θu' hm390 26 (e' := 26) (by norm_num) (by norm_num) (by norm_num), θu' hm390 52 (e' := 52) (by norm_num) (by norm_num) (by norm_num), θu' hm390 78 (e' := 78) (by norm_num) (by norm_num) (by norm_num), θu' hm390 104 (e' := 104) (by norm_num) (by norm_num) (by norm_num), θu' hm390 130 (e' := 130) (by norm_num) (by norm_num) (by norm_num), θu' hm390 156 (e' := 156) (by norm_num) (by norm_num) (by norm_num), θu' hm390 182 (e' := 182) (by norm_num) (by norm_num) (by norm_num)] at h
  have h' : ι (2 * ((J 52 156 * J 2 6))) = ι (2 * ((J 24 60 * J 156 390) - (PowerSeries.X ^ 2 * (J 8 60 * J 182 390)) - (PowerSeries.X ^ 4 * (J 20 60 * J 130 390)) + (PowerSeries.X ^ 14 * (J 4 60 * J 104 390)) + (PowerSeries.X ^ 18 * (J 12 60 * J 78 390)) - (PowerSeries.X ^ 24 * (J 28 60 * J 52 390)) + (PowerSeries.X ^ 36 * (J 16 60 * J 26 390)))) := by
    simp only [map_mul, map_sub, map_add, map_neg, map_ofNat, ι_Xpow]
    push_cast
    linear_combination h
  have h2 := mul_left_cancel₀ two_ne (ι_inj h')
  simp only [map_sub, map_add, map_neg, map_mul, map_pow, map_ofNat, S_J 2 1 3 (by norm_num) (by norm_num), S_J 2 2 30 (by norm_num) (by norm_num), S_J 2 4 30 (by norm_num) (by norm_num), S_J 2 6 30 (by norm_num) (by norm_num), S_J 2 8 30 (by norm_num) (by norm_num), S_J 2 10 30 (by norm_num) (by norm_num), S_J 2 12 30 (by norm_num) (by norm_num), S_J 2 13 195 (by norm_num) (by norm_num), S_J 2 14 30 (by norm_num) (by norm_num), S_J 2 26 78 (by norm_num) (by norm_num), S_J 2 26 195 (by norm_num) (by norm_num), S_J 2 39 195 (by norm_num) (by norm_num), S_J 2 52 195 (by norm_num) (by norm_num), S_J 2 65 195 (by norm_num) (by norm_num), S_J 2 78 195 (by norm_num) (by norm_num), S_J 2 91 195 (by norm_num) (by norm_num),
    show (S 2) PowerSeries.X = PowerSeries.X ^ 2 from RankProof.Ea_X 2 _]
  simp only [Nat.reduceMul]
  linear_combination h2


/-- Entry 16.1: `B = (2 -13; 1 1)`, shifts `i (1, 0)`, `i ∈ {(-15), (-14), (-13), (-12), (-11), (-10), (-9), (-8), (-7), (-6), (-5), (-4), (-3), (-2), (-1)}`. -/
def B16_1 : ECS where
  b11 := 2
  b12 := (-13)
  b21 := 1
  b22 := 1
  r1 := 1
  r2 := 0
  I := {(-15), (-14), (-13), (-12), (-11), (-10), (-9), (-8), (-7), (-6), (-5), (-4), (-3), (-2), (-1)}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 13 * n - (-15)) % 15 + (-15)), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 13 * n - (-15)) % 15 + (-15))) - (-13) * (n - 0 * ((1 * m + 13 * n - (-15)) % 15 + (-15)))) / 15), ((2 * (n - 0 * ((1 * m + 13 * n - (-15)) % 15 + (-15))) - 1 * (m - 1 * ((1 * m + 13 * n - (-15)) % 15 + (-15)))) / 15), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L16_1 : θ hm1 0 (-1) * θ hm26 13 1 = 2 * (θ hm30 14 1 * θ hm195 91 1) + 2 * (mono 1 1 * (θ hm30 12 1 * θ hm195 78 1)) + 2 * (mono 3 1 * (θ hm30 10 1 * θ hm195 65 1)) + 2 * (mono 6 1 * (θ hm30 8 1 * θ hm195 52 1)) + 2 * (mono 10 1 * (θ hm30 6 1 * θ hm195 39 1)) + 2 * (mono 15 1 * (θ hm30 4 1 * θ hm195 26 1)) + 2 * (mono 21 1 * (θ hm30 2 1 * θ hm195 13 1)) := by
  have h := θθ_lattice hm1 hm26 hm30 hm195 0 13 (by norm_num : (-1 : ℂ) ≠ 0) one_ne_zero B16_1 rfl rfl
    (by norm_num [B16_1]) (by norm_num [B16_1]) (by norm_num [B16_1])
  simp only [B16_1] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [c2] at h
  simp only [θ_nfr1 hm195 13 0 0 1 (e := 182) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm195 26 0 0 1 (e := 169) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm195 39 0 0 1 (e := 156) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm195 52 0 0 1 (e := 143) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm195 65 0 0 1 (e := 130) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm195 78 0 0 1 (e := 117) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm195 91 1 (-104) (-1) (e := 299) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm30 10 (-1) (-10) (-1) (e := (-10)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm30 12 (-1) (-12) (-1) (e := (-12)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm30 14 (-1) (-14) (-1) (e := (-14)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm30 2 (-1) (-2) (-1) (e := (-2)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm30 4 (-1) (-4) (-1) (e := (-4)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm30 6 (-1) (-6) (-1) (e := (-6)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm30 8 (-1) (-8) (-1) (e := (-8)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm195 13 1 one_ne_zero (-13) (-1) (e := 208) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm195 26 1 one_ne_zero (-26) (-1) (e := 221) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm195 39 1 one_ne_zero (-39) (-1) (e := 234) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm195 52 1 one_ne_zero (-52) (-1) (e := 247) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm195 65 1 one_ne_zero (-65) (-1) (e := 260) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm195 78 1 one_ne_zero (-78) (-1) (e := 273) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm195 91 1 one_ne_zero (-91) (-1) (e := 286) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm30 14 (-1) one_ne_zero (-16) (-1) (e := (-16)) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm195 1 (e := 195) (by norm_num), θz' hm30 0 (e := 0) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h



end Forty
