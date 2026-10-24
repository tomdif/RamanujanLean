/-
# The two theta identities of the endgame (base `Q³⁰`)

* `LemA` (HM Prop. 1.1, from `P11W`): the sum of the change-of-`z` quotients from `z₀ = Q⁴` to `z₁ = −1` at
  `x = Q¹⁴` and `x = Q⁴`:
  `Q⁴ j̄₋₄ (j̄₁₈/(j₄j₁₈j̄₁₄) + Q⁻² j̄₈/(j₄j₈j̄₄)) = Q⁻² j̄₆ j₁₀/(j₂j₁₂j₈)`;
* `LemB` (HM Prop. 3.2, from `F1prime`): the theta part of `(1 + φ(Q²))(Q¹⁰;Q¹⁰)_∞` relative to `z₀ = Q⁴` vanishes:
  `Q²⁴ j₋₂₄j₋₂/(j₄j₁₈j₋₆) + Q²/j₆ + Q¹² j₋₁₄j₋₂/(j₄j₈j₋₆) = 0`.
-/
import RamanujanTau.MTC.P11

set_option autoImplicit false

namespace MTC
open ALz HahnSeries

lemma jb30_ne (a : ℤ) : jb30 a ≠ 0 := by
  unfold jb30
  exact θ_ne_zero (h120 hqT) (by norm_num) fun _ _ => by norm_num

lemma mQ (k : ℕ) (e : ℤ) (h : e = 168 * k) : (mono e 1 : L) = Qm ^ k := by rw [h]; exact Qm_pow k

lemma mQn (k : ℕ) (e : ℤ) (h : e = -(168 * k)) : (mono e 1 : L) = (Qm ^ k)⁻¹ := by rw [h]; exact mneg k

/-- `j(Q^{−a}) = −Q^{−a} j(Q^a)`. -/
lemma j30_neg (k : ℕ) : j30 (-(k : ℤ)) = -(Qm ^ k)⁻¹ * j30 k := by
  unfold j30
  rw [show (168 : ℤ) * -(k : ℤ) = -(168 * k) by ring, tinv1, mneg]

/-- `j(−Q^{−a}) = Q^{−a} j(−Q^a)`. -/
lemma jb30_neg (k : ℕ) : jb30 (-(k : ℤ)) = (Qm ^ k)⁻¹ * jb30 k := by
  unfold jb30
  rw [show (168 : ℤ) * -(k : ℤ) = -(168 * k) by ring, inv_m, show -(mono (-(168 * (k : ℤ))) (-1) : L) =
    mono (-(168 * (k : ℤ))) 1 by simp [mono], mneg]

lemma j30_refl (a b : ℤ) (h : a + b = 30) : j30 a = j30 b := by
  unfold j30
  rw [show (168 : ℤ) * a = ((120 * 42 : ℕ) : ℤ) - 168 * b by push_cast; linarith, trefl1]

lemma jb30_refl (a b : ℤ) (h : a + b = 30) : jb30 a = jb30 b := by
  unfold jb30
  rw [show (168 : ℤ) * a = ((120 * 42 : ℕ) : ℤ) - 168 * b by push_cast; linarith, refl_m]

theorem LemA :
    Qm ^ 4 * jb30 (-4) * (jb30 18 / (j30 4 * j30 18 * jb30 14) + (Qm ^ 2)⁻¹ * jb30 8 / (j30 4 * j30 8 * jb30 4)) =
      (Qm ^ 2)⁻¹ * jb30 6 * j30 10 / (j30 2 * j30 12 * j30 8) := by
  have hP := P11W
  rw [mneg336, jb30_refl 16 14 (by norm_num)] at hP
  have hQ := Qm_ne
  have h2 := j30_ne 2 (by norm_num); have h4 := j30_ne 4 (by norm_num); have h8 := j30_ne 8 (by norm_num)
  have h12 := j30_ne 12 (by norm_num)
  have hb4 := jb30_ne 4; have hb14 := jb30_ne 14
  have key : Qm ^ 4 * jb30 (-4) * (jb30 18 / (j30 4 * j30 18 * jb30 14) + (Qm ^ 2)⁻¹ * jb30 8 /
      (j30 4 * j30 8 * jb30 4)) - (Qm ^ 2)⁻¹ * jb30 6 * j30 10 / (j30 2 * j30 12 * j30 8) =
      ((jb30 18 * j30 8 * jb30 4 * j30 2 + (Qm ^ 2)⁻¹ * (jb30 8 * j30 12 * jb30 14 * j30 2)) -
        (Qm ^ 2)⁻¹ * (jb30 14 * jb30 6 * j30 10 * j30 4)) / (j30 2 * j30 4 * j30 8 * j30 12 * jb30 14) := by
    rw [show (-4 : ℤ) = -((4 : ℕ) : ℤ) by norm_num, jb30_neg, show (((4 : ℕ) : ℤ)) = 4 by norm_num,
      j30_refl 18 12 (by norm_num)]
    field_simp
    first | done | ring
  rw [sub_eq_zero.mpr hP, zero_div] at key
  exact sub_eq_zero.mp key

theorem LemB :
    Qm ^ 24 * j30 (-24) * j30 (-2) / (j30 4 * j30 18 * j30 (-6)) + Qm ^ 2 / j30 6 +
      Qm ^ 12 * j30 (-14) * j30 (-2) / (j30 4 * j30 8 * j30 (-6)) = 0 := by
  have hF := F1prime
  rw [m336] at hF
  have hQ := Qm_ne
  have h2 := j30_ne 2 (by norm_num); have h4 := j30_ne 4 (by norm_num); have h6 := j30_ne 6 (by norm_num)
  have h8 := j30_ne 8 (by norm_num); have h12 := j30_ne 12 (by norm_num)
  have key : Qm ^ 24 * j30 (-24) * j30 (-2) / (j30 4 * j30 18 * j30 (-6)) + Qm ^ 2 / j30 6 +
      Qm ^ 12 * j30 (-14) * j30 (-2) / (j30 4 * j30 8 * j30 (-6)) =
      Qm ^ 2 * (j30 4 * j30 8 * j30 12 - (j30 2 * j30 12 * j30 14 + Qm ^ 2 * (j30 2 * j30 6 * j30 8))) /
        (j30 4 * j30 6 * j30 8 * j30 12) := by
    rw [show (-24 : ℤ) = -((24 : ℕ) : ℤ) by norm_num, j30_neg, show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, j30_neg,
      show (-6 : ℤ) = -((6 : ℕ) : ℤ) by norm_num, j30_neg, show (-14 : ℤ) = -((14 : ℕ) : ℤ) by norm_num, j30_neg]
    rw [show (((24 : ℕ) : ℤ)) = 24 by norm_num, j30_refl 24 6 (by norm_num), show (((2 : ℕ) : ℤ)) = 2 by norm_num,
      show (((6 : ℕ) : ℤ)) = 6 by norm_num, show (((14 : ℕ) : ℤ)) = 14 by norm_num, j30_refl 18 12 (by norm_num)]
    field_simp
    ring
  rw [key, sub_eq_zero.mpr hF, mul_zero, zero_div]

end MTC
