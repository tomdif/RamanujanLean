/-
# The two Weierstrass identities of the MTC₁ endgame (base `Q³⁰`)

* `WA1` (`x = Q⁶`, `y = −Q²`, `u = Q⁴`, `v = Q¹⁰`): `(j̄₈j̄₄j₆ − Q²j₄j̄₆j̄₂) j₁₄ = j̄₁₂j̄₈j₁₀j₂`, hence `LemA1`:
  `Q⁻¹ j̄₋₂j̄₄/(j₂j₄j̄₂) − Q j̄₋₂j̄₂₄/(j₂j₂₄j̄₂₂) = Q⁻³ j̄₁₂j₁₀/(j₄j₆j₁₄)`;
* `WB1` (`x = Q`, `y = Q³`, `u = Q⁷`, `v = Q¹³`): `j₄j₁₂j₁₄ + Q⁴j₂j₄j₆ = j₆j₈j₁₄`, hence `LemB1`
  (the theta part of `(1 + ψ(Q²))(Q¹⁰;Q¹⁰)_∞` relative to `z₀ = Q²` vanishes).
-/
import RamanujanTau.MTC.ThetaLem

set_option autoImplicit false

namespace MTC
open ALz HahnSeries

lemma jc (a : ℤ) (e : ℤ) (he : e = 168 * a) : θ (h120 hqT) e 1 = j30 a := by rw [he]; rfl
lemma jbc (a : ℤ) (e : ℤ) (he : e = 168 * a) : θ (h120 hqT) e (-1) = jb30 a := by rw [he]; rfl

theorem WA1 : (jb30 8 * jb30 4 * j30 6 - Qm ^ 2 * j30 4 * jb30 6 * jb30 2) * j30 14 =
    jb30 12 * jb30 8 * j30 10 * j30 2 := by
  have hw := weierstrass (h120 hqT) (by' := 336) (bu := 672) (bv := 1680) (bx := 1008) (cy := -1) (cu := 1) (cv := 1)
    (cx := 1) (by norm_num) one_ne_zero one_ne_zero one_ne_zero (by norm_num) (by norm_num) (by norm_num)
  simp only [mul_one, inv_one] at hw
  norm_num at hw
  rw [jbc 8 1344 (by norm_num), jbc 4 672 (by norm_num), jc 14 2352 (by norm_num),
    jc (-6) (-1008) (by norm_num), jc 16 2688 (by norm_num), jc (-4) (-672) (by norm_num), jbc 6 1008 (by norm_num),
    jbc 2 336 (by norm_num), jbc 12 2016 (by norm_num), jbc (-8) (-1344) (by norm_num), jc 10 1680 (by norm_num),
    jc 2 336 (by norm_num), show (single (336 : ℤ) (1 : ℂ) : L) = Qm ^ 2 from m336,
    show (-6 : ℤ) = -((6 : ℕ) : ℤ) by norm_num, j30_neg, show (-4 : ℤ) = -((4 : ℕ) : ℤ) by norm_num, j30_neg,
    show (-8 : ℤ) = -((8 : ℕ) : ℤ) by norm_num, jb30_neg, j30_refl 16 14 (by norm_num)] at hw
  norm_num at hw
  have hQ := Qm_ne
  have key : (jb30 8 * jb30 4 * j30 6 - Qm ^ 2 * j30 4 * jb30 6 * jb30 2) * j30 14 - jb30 12 * jb30 8 * j30 10 * j30 2 =
      -(Qm ^ 6 * (jb30 8 * jb30 4 * j30 14 * (-(Qm ^ 6)⁻¹ * j30 6) - j30 14 * (-(Qm ^ 4)⁻¹ * j30 4) * jb30 6 * jb30 2 -
        -Qm ^ 2 * jb30 12 * ((Qm ^ 8)⁻¹ * jb30 8) * j30 10 * j30 2)) := by
    field_simp
    ring
  rw [sub_eq_zero.mpr hw, mul_zero, neg_zero] at key
  exact sub_eq_zero.mp key

theorem WB1 : j30 4 * j30 12 * j30 14 + Qm ^ 4 * j30 2 * j30 4 * j30 6 = j30 6 * j30 8 * j30 14 := by
  have hw := weierstrass (h120 hqT) (by' := 504) (bu := 1176) (bv := 2184) (bx := 168) (cy := 1) (cu := 1) (cv := 1)
    (cx := 1) one_ne_zero one_ne_zero one_ne_zero one_ne_zero (by norm_num) (by norm_num) (by norm_num)
  simp only [mul_one, inv_one] at hw
  norm_num at hw
  rw [jc 4 672 (by norm_num), jc (-2) (-336) (by norm_num), jc 20 3360 (by norm_num), jc (-6) (-1008) (by norm_num),
    jc 14 2352 (by norm_num), jc (-12) (-2016) (by norm_num), jc 10 1680 (by norm_num), jc 16 2688 (by norm_num),
    jc (-10) (-1680) (by norm_num), jc 8 1344 (by norm_num), mQ 4 672 (by norm_num),
    show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, j30_neg, show (-6 : ℤ) = -((6 : ℕ) : ℤ) by norm_num, j30_neg,
    show (-12 : ℤ) = -((12 : ℕ) : ℤ) by norm_num, j30_neg, show (-10 : ℤ) = -((10 : ℕ) : ℤ) by norm_num, j30_neg,
    j30_refl 20 10 (by norm_num), j30_refl 16 14 (by norm_num)] at hw
  norm_num at hw
  have hQ := Qm_ne
  have h10 := j30_ne 10 (by norm_num)
  have key : j30 4 * j30 12 * j30 14 + Qm ^ 4 * j30 2 * j30 4 * j30 6 - j30 6 * j30 8 * j30 14 =
      Qm ^ 12 / j30 10 * (j30 4 * (-(Qm ^ 2)⁻¹ * j30 2) * j30 10 * (-(Qm ^ 6)⁻¹ * j30 6) -
        j30 14 * (-(Qm ^ 12)⁻¹ * j30 12) * j30 10 * j30 4 -
        Qm ^ 4 * j30 14 * (-(Qm ^ 10)⁻¹ * j30 10) * j30 8 * (-(Qm ^ 6)⁻¹ * j30 6)) := by
    field_simp
    ring
  have h0 := sub_eq_zero.mpr hw
  first
    | (apply sub_eq_zero.mp; rw [key, h0, mul_zero])
    | (apply sub_eq_zero.mp; rw [key]; linear_combination (Qm ^ 12 / j30 10) * hw)

theorem LemA1 :
    Qm⁻¹ * jb30 (-2) * jb30 4 / (j30 2 * j30 4 * jb30 2) - Qm * jb30 (-2) * jb30 24 / (j30 2 * j30 24 * jb30 22) =
      (Qm ^ 3)⁻¹ * jb30 12 * j30 10 / (j30 4 * j30 6 * j30 14) := by
  have hW := WA1
  have hQ := Qm_ne
  have h2 := j30_ne 2 (by norm_num); have h4 := j30_ne 4 (by norm_num); have h6 := j30_ne 6 (by norm_num)
  have h14 := j30_ne 14 (by norm_num)
  have hb2 := jb30_ne 2; have hb8 := jb30_ne 8
  rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, jb30_neg, show (((2 : ℕ) : ℤ)) = 2 by norm_num,
    jb30_refl 24 6 (by norm_num), j30_refl 24 6 (by norm_num), jb30_refl 22 8 (by norm_num)]
  have key : Qm⁻¹ * ((Qm ^ 2)⁻¹ * jb30 2) * jb30 4 / (j30 2 * j30 4 * jb30 2) -
      Qm * ((Qm ^ 2)⁻¹ * jb30 2) * jb30 6 / (j30 2 * j30 6 * jb30 8) -
      (Qm ^ 3)⁻¹ * jb30 12 * j30 10 / (j30 4 * j30 6 * j30 14) =
      (Qm ^ 3)⁻¹ * ((jb30 8 * jb30 4 * j30 6 - Qm ^ 2 * j30 4 * jb30 6 * jb30 2) * j30 14 -
        jb30 12 * jb30 8 * j30 10 * j30 2) / (j30 2 * j30 4 * j30 6 * jb30 8 * j30 14) := by
    field_simp
    first | done | ring
  rw [sub_eq_zero.mpr hW, mul_zero, zero_div] at key
  exact sub_eq_zero.mp key

theorem LemB1 :
    -(Qm ^ 12 * j30 (-12) * j30 14 / (j30 2 * j30 24 * j30 12)) + Qm ^ 4 / j30 12 -
      j30 8 * j30 14 / (j30 2 * j30 4 * j30 12) = 0 := by
  have hW := WB1
  have hQ := Qm_ne
  have h2 := j30_ne 2 (by norm_num); have h4 := j30_ne 4 (by norm_num); have h6 := j30_ne 6 (by norm_num)
  have h12 := j30_ne 12 (by norm_num)
  rw [show (-12 : ℤ) = -((12 : ℕ) : ℤ) by norm_num, j30_neg, show (((12 : ℕ) : ℤ)) = 12 by norm_num,
    j30_refl 24 6 (by norm_num)]
  have key : -(Qm ^ 12 * (-(Qm ^ 12)⁻¹ * j30 12) * j30 14 / (j30 2 * j30 6 * j30 12)) + Qm ^ 4 / j30 12 -
      j30 8 * j30 14 / (j30 2 * j30 4 * j30 12) =
      (j30 4 * j30 12 * j30 14 + Qm ^ 4 * j30 2 * j30 4 * j30 6 - j30 6 * j30 8 * j30 14) /
        (j30 2 * j30 4 * j30 6 * j30 12) := by
    field_simp
    first | done | ring
  rw [key, sub_eq_zero.mpr hW, zero_div]

end MTC
