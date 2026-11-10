/-
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
import RamanujanTau.Forty.E16iiA
import RamanujanTau.Forty.E03

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

/-- the product form of `L16_1`: `ψ(q)φ(−q¹³)` as seven products of moduli 30 and 195 (Berndt et al. (19.11)). -/
theorem P16_1 : Pinf 2 2 * J 13 26 = Pinf 1 2 * (J 14 30 * J 91 195 + PowerSeries.X * (J 12 30 * J 78 195)
    + PowerSeries.X ^ 3 * (J 10 30 * J 65 195) + PowerSeries.X ^ 6 * (J 8 30 * J 52 195)
    + PowerSeries.X ^ 10 * (J 6 30 * J 39 195) + PowerSeries.X ^ 15 * (J 4 30 * J 26 195)
    + PowerSeries.X ^ 21 * (J 2 30 * J 13 195)) := by
  apply ι_inj
  have h := L16_1
  rw [θu' hm26 13 (e' := 13) (by norm_num) (by norm_num) (by norm_num),
    θu' hm30 14 (e' := 14) (by norm_num) (by norm_num) (by norm_num),
    θu' hm30 12 (e' := 12) (by norm_num) (by norm_num) (by norm_num),
    θu' hm30 10 (e' := 10) (by norm_num) (by norm_num) (by norm_num),
    θu' hm30 8 (e' := 8) (by norm_num) (by norm_num) (by norm_num),
    θu' hm30 6 (e' := 6) (by norm_num) (by norm_num) (by norm_num),
    θu' hm30 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm30 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm195 91 (e' := 91) (by norm_num) (by norm_num) (by norm_num),
    θu' hm195 78 (e' := 78) (by norm_num) (by norm_num) (by norm_num),
    θu' hm195 65 (e' := 65) (by norm_num) (by norm_num) (by norm_num),
    θu' hm195 52 (e' := 52) (by norm_num) (by norm_num) (by norm_num),
    θu' hm195 39 (e' := 39) (by norm_num) (by norm_num) (by norm_num),
    θu' hm195 26 (e' := 26) (by norm_num) (by norm_num) (by norm_num),
    θu' hm195 13 (e' := 13) (by norm_num) (by norm_num) (by norm_num)] at h
  have hb := θ_bar0 hm1
  simp only [mul_one] at hb
  simp only [map_mul, map_add, ι_Xpow, ι_X]
  have h2 : (2 : L) * (ι (Pinf 2 2) * ι (J 13 26)) = 2 * (ι (Pinf 1 2) * (ι (J 14 30) * ι (J 91 195)
      + mono 1 1 * (ι (J 12 30) * ι (J 78 195)) + mono (3 : ℕ) 1 * (ι (J 10 30) * ι (J 65 195))
      + mono (6 : ℕ) 1 * (ι (J 8 30) * ι (J 52 195)) + mono (10 : ℕ) 1 * (ι (J 6 30) * ι (J 39 195))
      + mono (15 : ℕ) 1 * (ι (J 4 30) * ι (J 26 195)) + mono (21 : ℕ) 1 * (ι (J 2 30) * ι (J 13 195)))) := by
    push_cast
    linear_combination (-ι (J 13 26)) * hb + ι (Pinf 1 2) * h
  have h2ne : (2 : L) ≠ 0 := fun h0 => two_ne (ι_inj (by rw [map_ofNat, map_zero]; exact h0))
  exact mul_left_cancel₀ h2ne h2

lemma Jsym (e N : ℕ) (h : e ≤ N) : J (N - e) N = J e N := by
  simp only [J, Nat.sub_sub_self h]; ring

/-- the four quintuple-product components of Lemma 5.1, at `q²` and `q¹³` (product form). -/
lemma Q16 : ((J 14 30 + PowerSeries.X ^ 2 * J 4 30) * J 2 10 = J 10 30 * J 4 10) ∧
    ((J 8 30 - PowerSeries.X ^ 2 * J 2 30) * J 4 10 = J 10 30 * J 2 10) ∧
    ((J 91 195 + PowerSeries.X ^ 13 * J 26 195) * J 13 65 = J 65 195 * J 26 65) ∧
    ((J 52 195 - PowerSeries.X ^ 13 * J 13 195) * J 26 65 = J 65 195 * J 13 65) := by
  have Q1 := quint1 hm10 hm30 rfl 2 16 26 10 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q2 := quint1 hm10 hm30 rfl 4 22 32 10 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q3 := quint1 hm65 hm195 rfl 13 104 169 65 26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Q4 := quint1 hm65 hm195 rfl 26 143 208 65 52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_sh hm30 2 1 one_ne_zero (-2) (-1) (e := 32) (by norm_num) (by norm_num [c2]) (by norm_num),
    θ_refl1 hm10 2 8 (by norm_num)] at Q2
  rw [θ_sh hm195 13 1 one_ne_zero (-13) (-1) (e := 208) (by norm_num) (by norm_num [c2]) (by norm_num),
    θ_refl1 hm65 13 52 (by norm_num)] at Q4
  rw [θ_refl1 hm30 14 16 (by norm_num), θ_refl1 hm30 4 26 (by norm_num)] at Q1
  rw [θ_refl1 hm30 8 22 (by norm_num)] at Q2
  rw [θ_refl1 hm195 91 104 (by norm_num), θ_refl1 hm195 26 169 (by norm_num)] at Q3
  rw [θ_refl1 hm195 52 143 (by norm_num)] at Q4
  simp only [θu' hm30 14 (e' := 14) (by norm_num) (by norm_num) (by norm_num),
    θu' hm30 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm30 8 (e' := 8) (by norm_num) (by norm_num) (by norm_num),
    θu' hm30 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm30 10 (e' := 10) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm195 91 (e' := 91) (by norm_num) (by norm_num) (by norm_num),
    θu' hm195 26 (e' := 26) (by norm_num) (by norm_num) (by norm_num),
    θu' hm195 52 (e' := 52) (by norm_num) (by norm_num) (by norm_num),
    θu' hm195 13 (e' := 13) (by norm_num) (by norm_num) (by norm_num),
    θu' hm195 65 (e' := 65) (by norm_num) (by norm_num) (by norm_num),
    θu' hm65 13 (e' := 13) (by norm_num) (by norm_num) (by norm_num),
    θu' hm65 26 (e' := 26) (by norm_num) (by norm_num) (by norm_num)] at Q1 Q2 Q3 Q4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply ι_inj <;> simp only [map_mul, map_add, map_sub, ι_Xpow] <;> push_cast
  · linear_combination Q1
  · rw [mono_mono, show (4 : ℤ) + -2 = 2 by norm_num, show (1 : ℂ) * -1 = -1 by norm_num, mono_neg1] at Q2
    linear_combination Q2
  · linear_combination Q3
  · rw [mono_mono, show (26 : ℤ) + -13 = 13 by norm_num, show (1 : ℂ) * -1 = -1 by norm_num, mono_neg1] at Q4
    linear_combination Q4

lemma J16a : J 4 10 * J 2 10 = Pinf 2 2 * Pinf 10 10 := by
  simp only [J, Nat.reduceSub]
  simp (disch := norm_num) only [atom _ _ 10]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
    add_zero, mul_one]
  ring

lemma J16b : J 26 65 * J 13 65 = Pinf 13 13 * Pinf 65 65 := by
  simp only [J, Nat.reduceSub]
  simp (disch := norm_num) only [atom _ _ 65]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
    add_zero, mul_one]
  ring

lemma J16c : J 10 30 = Pinf 10 10 := by
  simp only [J, Nat.reduceSub]
  simp (disch := norm_num) only [atom _ _ 30]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
    add_zero, mul_one]

lemma J16d : J 65 195 = Pinf 65 65 := by
  simp only [J, Nat.reduceSub]
  simp (disch := norm_num) only [atom _ _ 195]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
    add_zero, mul_one]

lemma J16e : J 1 3 = Pinf 1 1 := by
  simp only [J, Nat.reduceSub]
  simp (disch := norm_num) only [atom _ _ 3]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
    add_zero, mul_one]

lemma J16f : J 26 78 = Pinf 26 26 := by
  simp only [J, Nat.reduceSub]
  simp (disch := norm_num) only [atom _ _ 78]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
    add_zero, mul_one]

/-- the bracket of (19.10) without `L`. -/
noncomputable def Bk16 : PowerSeries ℤ :=
  (J 14 30 + PowerSeries.X ^ 2 * J 4 30) * (J 91 195 + PowerSeries.X ^ 13 * J 26 195)
    + 2 * PowerSeries.X ^ 3 * (Pinf 10 10 * Pinf 65 65)
    + PowerSeries.X ^ 6 * ((J 8 30 - PowerSeries.X ^ 2 * J 2 30) * (J 52 195 - PowerSeries.X ^ 13 * J 13 195))

/-- (19.10) without the operator `L`: `A² = f(−q²)f(−q¹³)·Bk16`. -/
theorem core16 : (J 4 10 * J 26 65 + PowerSeries.X ^ 3 * (J 2 10 * J 13 65)) ^ 2 = Pinf 2 2 * Pinf 13 13 * Bk16 := by
  obtain ⟨Q0, Q4, R0, R4⟩ := Q16
  rw [J16c] at Q0 Q4
  rw [J16d] at R0 R4
  have Pa := J16a
  have Pb := J16b
  have hFK : Pinf 10 10 * Pinf 65 65 ≠ 0 := mul_ne_zero (Pinf_ne _ _ (by norm_num) (by norm_num)) (Pinf_ne _ _ (by norm_num) (by norm_num))
  apply mul_right_cancel₀ hFK
  unfold Bk16
  linear_combination
    (-(J 4 10 * J 26 65 * J 26 65 * Pinf 65 65)) * Q0
    + (-(J 4 10 * J 26 65 * (J 14 30 + PowerSeries.X ^ 2 * J 4 30) * J 2 10)) * R0
    + ((J 14 30 + PowerSeries.X ^ 2 * J 4 30) * (J 91 195 + PowerSeries.X ^ 13 * J 26 195) * J 26 65 * J 13 65
      + 2 * PowerSeries.X ^ 3 * Pinf 10 10 * Pinf 65 65 * J 26 65 * J 13 65
      + PowerSeries.X ^ 6 * (J 8 30 - PowerSeries.X ^ 2 * J 2 30) * (J 52 195 - PowerSeries.X ^ 13 * J 13 195) * J 26 65 * J 13 65) * Pa
    + ((J 14 30 + PowerSeries.X ^ 2 * J 4 30) * (J 91 195 + PowerSeries.X ^ 13 * J 26 195) * Pinf 2 2 * Pinf 10 10
      + 2 * PowerSeries.X ^ 3 * Pinf 10 10 * Pinf 65 65 * Pinf 2 2 * Pinf 10 10
      + PowerSeries.X ^ 6 * (J 8 30 - PowerSeries.X ^ 2 * J 2 30) * (J 52 195 - PowerSeries.X ^ 13 * J 13 195) * Pinf 2 2 * Pinf 10 10) * Pb
    + (-(PowerSeries.X ^ 6 * J 2 10 * J 13 65 * J 13 65 * Pinf 65 65)) * Q4
    + (-(PowerSeries.X ^ 6 * J 2 10 * J 13 65 * (J 8 30 - PowerSeries.X ^ 2 * J 2 30) * J 4 10)) * R4

/-- (19.17) + (19.24): `Bk16 = ψ(q)φ(−q¹³) − q f(−q)f(−q²⁶)`, cleared of `(q;q²)_∞`. -/
theorem brk16 : Bk16 * Pinf 1 2 = Pinf 2 2 * J 13 26 - PowerSeries.X * Pinf 1 2 * (Pinf 1 1 * Pinf 26 26) := by
  have h1 := P16_1
  have h2 := P16_2
  rw [J16e, J16f, J16c, J16d] at h2
  rw [J16c, J16d] at h1
  unfold Bk16
  linear_combination -h1 + PowerSeries.X * Pinf 1 2 * h2

/-- **Entry 3.16 (second equality), squared** (Berndt et al. §19):
`(G(q²)G(q¹³) + q³H(q²)H(q¹³))² = χ(−q¹³)/χ(−q) − qχ(−q)/χ(−q¹³)`. -/
theorem entry_3_16_ii : (S 2 G * S 13 G + PowerSeries.X ^ 3 * S 2 H * S 13 H) ^ 2 =
    chim 13 * Ring.inverse (chim 1) - PowerSeries.X * chim 1 * Ring.inverse (chim 13) := by
  have e1 := SG_E 2
  have e2 := SH_E 2
  have e3 := SG_E 13
  have e4 := SH_E 13
  norm_num at e1 e2 e3 e4
  have hL : (S 2 G * S 13 G + PowerSeries.X ^ 3 * S 2 H * S 13 H) * (Pinf 2 2 * Pinf 13 13) =
      (J 4 10 * J 26 65 + PowerSeries.X ^ 3 * (J 2 10 * J 13 65)) := by
    linear_combination (S 13 G * Pinf 13 13) * e1 + J 4 10 * e3 + PowerSeries.X ^ 3 * (S 13 H * Pinf 13 13) * e2
      + PowerSeries.X ^ 3 * J 2 10 * e4
  have c := core16
  have b := brk16
  have s1 := E1_split
  have s13 := congrArg (S 13) E1_split
  rw [map_mul, S_P' 13 1 1 le_rfl le_rfl (rfl : 13 = 13 * 1) (rfl : 13 = 13 * 1),
    S_P' 13 1 2 le_rfl (by norm_num) (rfl : 13 = 13 * 1) (rfl : 26 = 13 * 2),
    S_P' 13 2 2 (by norm_num) (by norm_num) (rfl : 26 = 13 * 2) (rfl : 26 = 13 * 2)] at s13
  have j13 : J 13 26 = Pinf 13 26 * Pinf 13 26 * Pinf 26 26 := by simp only [J, Nat.reduceSub]
  set Y := S 2 G * S 13 G + PowerSeries.X ^ 3 * S 2 H * S 13 H with hY
  -- `Y² f(−q²) f(−q¹³) = Bk16`
  have k1 : Y ^ 2 * (Pinf 2 2 * Pinf 13 13) = Bk16 := by
    apply mul_left_cancel₀ (mul_ne_zero (Pinf_ne 2 2 (by norm_num) (by norm_num)) (Pinf_ne 13 13 (by norm_num) (by norm_num)))
    linear_combination (Y * (Pinf 2 2 * Pinf 13 13) + (J 4 10 * J 26 65 + PowerSeries.X ^ 3 * (J 2 10 * J 13 65))) * hL + c
  have hu1 := isUnit_Pinf 1 2 le_rfl (by norm_num)
  have hu13 := isUnit_Pinf 13 26 (by norm_num) (by norm_num)
  have k2 : Y ^ 2 * (Pinf 1 2 * Pinf 13 26) = Pinf 13 26 ^ 2 - PowerSeries.X * Pinf 1 2 ^ 2 := by
    apply mul_left_cancel₀ (mul_ne_zero (Pinf_ne 2 2 (by norm_num) (by norm_num)) (Pinf_ne 26 26 (by norm_num) (by norm_num)))
    linear_combination (Pinf 1 2) * k1 + b - (Y ^ 2 * Pinf 2 2 * Pinf 1 2) * s13
      - (PowerSeries.X * Pinf 1 2 * Pinf 26 26) * s1 + (Pinf 2 2) * j13
  simp only [chim, show 2 * 13 = 26 by norm_num, mul_one]
  have i1 : Pinf 1 2 * Ring.inverse (Pinf 1 2) = 1 := Ring.mul_inverse_cancel _ hu1
  have i13 : Pinf 13 26 * Ring.inverse (Pinf 13 26) = 1 := Ring.mul_inverse_cancel _ hu13
  linear_combination (Ring.inverse (Pinf 1 2) * Ring.inverse (Pinf 13 26)) * k2
    + (-Y ^ 2 - PowerSeries.X * Pinf 1 2 * Ring.inverse (Pinf 13 26)) * i1
    + (-Y ^ 2 * Pinf 1 2 * Ring.inverse (Pinf 1 2) + Pinf 13 26 * Ring.inverse (Pinf 1 2)) * i13

/-- the same for the other side of Entry 3.16: `(G(q²⁶)H(q) − q⁵G(q)H(q²⁶))² = χ(−q¹³)/χ(−q) − qχ(−q)/χ(−q¹³)`. -/
theorem entry_3_16_ii' : (S 26 G * H - PowerSeries.X ^ 5 * G * S 26 H) ^ 2 =
    chim 13 * Ring.inverse (chim 1) - PowerSeries.X * chim 1 * Ring.inverse (chim 13) := by
  rw [← entry_3_16_i]; exact entry_3_16_ii

lemma cc_H16 : PowerSeries.constantCoeff H = 1 := by
  have h := congrArg PowerSeries.constantCoeff H_mul_vv
  rw [map_mul, vv, map_mul, cc_Pinf 2 5 (by norm_num) (by norm_num), cc_Pinf 3 5 (by norm_num) (by norm_num), map_one] at h
  simpa using h

/-- **Entry 3.16(ii)** with the branch of the square root: `G(q²)G(q¹³) + q³H(q²)H(q¹³)` is the unique power series
with constant term `1` whose square is `χ(−q¹³)/χ(−q) − qχ(−q)/χ(−q¹³)`. -/
theorem entry_3_16_ii_unique (Y : PowerSeries ℤ) (hY : Y ^ 2 =
    chim 13 * Ring.inverse (chim 1) - PowerSeries.X * chim 1 * Ring.inverse (chim 13))
    (h1 : PowerSeries.constantCoeff Y = 1) : Y = S 2 G * S 13 G + PowerSeries.X ^ 3 * S 2 H * S 13 H := by
  have h := entry_3_16_ii
  have hf : (Y - (S 2 G * S 13 G + PowerSeries.X ^ 3 * S 2 H * S 13 H)) *
      (Y + (S 2 G * S 13 G + PowerSeries.X ^ 3 * S 2 H * S 13 H)) = 0 := by
    linear_combination hY - h
  rcases mul_eq_zero.mp hf with h0 | h0
  · exact sub_eq_zero.mp h0
  · exfalso
    have := congrArg PowerSeries.constantCoeff h0
    simp only [map_add, map_mul, map_pow, cc_S, cc_G, cc_H16, h1, PowerSeries.constantCoeff_X, map_zero] at this
    norm_num at this

/-- the constant term of `G(q²)G(q¹³) + q³H(q²)H(q¹³)` is `1` (so it is the principal square root). -/
lemma cc_3_16 : PowerSeries.constantCoeff (S 2 G * S 13 G + PowerSeries.X ^ 3 * S 2 H * S 13 H) = 1 := by
  simp only [map_add, map_mul, map_pow, cc_S, cc_G, cc_H16, PowerSeries.constantCoeff_X]
  norm_num

end Forty
