/-
# The `g`-side at the MTC₁ point

At `x₁ = Z²¹ t^{189}`, `y₁ = −x₁`: `X_t = Y_t = Q^{12−10t}`, and the brackets evaluate (HM (1.2f)) to
`t = 0 ↦ 0`, `t = 1 ↦ 2Q⁻³J₁`, `t = 2 ↦ 2Q⁻⁹J₁`:

`gNum_x1`: `J̄ g(x₁, y₁) = 2 j(Q²;Q³)(Q⁻³ A(Q²) + Q⁻⁹ A(Q⁻⁸))`.
-/
import RamanujanTau.MTC.GX373

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset

lemma θ504_504 : θ h504 504 1 = 0 := by
  rw [show (504 : ℤ) = ((504 : ℕ) : ℤ) * 1 by norm_num]; exact θ_qpow h504 1

/-- `j(Q⁵; Q³) = −Q⁻² j(Q²; Q³)`. -/
lemma θ504_840 : θ h504 840 1 = mono (-336) (-1) * θ h504 336 1 := by
  have h := θ_qshift h504 336 one_ne_zero 1
  rw [show (336 : ℤ) + ((504 : ℕ) : ℤ) * 1 = 840 by norm_num] at h
  rw [h]
  congr 1
  exact mono_ext (by norm_num [c2]) (by norm_num)

/-- `j(Q¹⁰; Q³) = −Q⁻¹² j(Q²; Q³)`. -/
lemma θ504_1680 : θ h504 1680 1 = mono (-2016) (-1) * θ h504 336 1 := by
  have h := θ_qshift h504 168 one_ne_zero 3
  rw [show (168 : ℤ) + ((504 : ℕ) : ℤ) * 3 = 1680 by norm_num] at h
  have hr : θ h504 (((504 : ℕ) : ℤ) - 336) 1 = θ h504 336 1 := by
    have := θ_reflect h504 336 one_ne_zero; rwa [inv_one] at this
  rw [h, show (168 : ℤ) = ((504 : ℕ) : ℤ) - 336 by norm_num, hr]
  congr 1
  exact mono_ext (by norm_num [c2]) (by norm_num)

lemma brk0₁ :
    mono (3 * (42 : ℕ) * c2 0 + 189 * 0) ((-Z84 ^ (63 : ℤ)) ^ (0 : ℤ)) * θ (h3qe hqG) (7 * (42 : ℕ) * 0 + 189) (Z84 ^ (21 : ℤ)) +
      mono (3 * (42 : ℕ) * c2 0 + 189 * 0) ((-Z84 ^ (21 : ℤ)) ^ (0 : ℤ)) * θ (h3qe hqG) (7 * (42 : ℕ) * 0 + 189) (Z84 ^ (63 : ℤ)) =
      0 := by
  have hp := pair_plus (h3qe hqG) (7 * (42 : ℕ) * 0 + 189) c21_ne
  rw [negsq21, θ504, show (((3 * 42 : ℕ) : ℤ) + 2 * (7 * ((42 : ℕ) : ℤ) * 0 + 189)) = 504 by norm_num,
    θ504_504] at hp
  have m1 : (mono (3 * (42 : ℕ) * c2 0 + 189 * 0) ((-Z84 ^ (63 : ℤ)) ^ (0 : ℤ)) : L) = 1 :=
    mono_ext (by norm_num [c2]) (by rw [zpow_zero])
  have m2 : (mono (3 * (42 : ℕ) * c2 0 + 189 * 0) ((-Z84 ^ (21 : ℤ)) ^ (0 : ℤ)) : L) = 1 :=
    mono_ext (by norm_num [c2]) (by rw [zpow_zero])
  rw [m1, m2, one_mul, one_mul, Z63_eq]
  linear_combination hp

lemma brk1₁ :
    mono (3 * (42 : ℕ) * c2 1 + 189 * 1) ((-Z84 ^ (63 : ℤ)) ^ (1 : ℤ)) * θ (h3qe hqG) (7 * (42 : ℕ) * 1 + 189) (Z84 ^ (21 : ℤ)) +
      mono (3 * (42 : ℕ) * c2 1 + 189 * 1) ((-Z84 ^ (21 : ℤ)) ^ (1 : ℤ)) * θ (h3qe hqG) (7 * (42 : ℕ) * 1 + 189) (Z84 ^ (63 : ℤ)) =
      2 * mono (-504) 1 * θ h504 336 1 := by
  have hp := pair_minus (h3qe hqG) (7 * (42 : ℕ) * 1 + 189) c21_ne
  rw [negsq21, θ504, show 2 * (7 * ((42 : ℕ) : ℤ) * 1 + 189) - ((3 * 42 : ℕ) : ℤ) = 840 by norm_num,
    θ504_840] at hp
  have m1 : (mono (3 * (42 : ℕ) * c2 1 + 189 * 1) ((-Z84 ^ (63 : ℤ)) ^ (1 : ℤ)) : L) = mono 189 (Z84 ^ (21 : ℤ)) :=
    mono_ext (by norm_num [c2]) (by rw [Z63_eq, neg_neg, zpow_one])
  have m2 : (mono (3 * (42 : ℕ) * c2 1 + 189 * 1) ((-Z84 ^ (21 : ℤ)) ^ (1 : ℤ)) : L) = -mono 189 (Z84 ^ (21 : ℤ)) := by
    rw [neg_mono_g]; exact mono_ext (by norm_num [c2]) (by rw [zpow_one])
  have hkey : (mono 189 (Z84 ^ (21 : ℤ)) : L) * mono (((3 * 42 : ℕ) : ℤ) - (7 * ((42 : ℕ) : ℤ) * 1 + 189))
      (-(Z84 ^ (21 : ℤ))⁻¹) * mono (-336) (-1) = mono (-504) 1 := by
    rw [mono_mul, mono_mul]
    exact mono_ext (by norm_num) (by field_simp [c21_ne, Z_ne])
  rw [m1, m2, Z63_eq]
  linear_combination (mono 189 (Z84 ^ (21 : ℤ)) : L) * hp + 2 * θ h504 336 1 * hkey

lemma brk2₁ :
    mono (3 * (42 : ℕ) * c2 2 + 189 * 2) ((-Z84 ^ (63 : ℤ)) ^ (2 : ℤ)) * θ (h3qe hqG) (7 * (42 : ℕ) * 2 + 189) (Z84 ^ (21 : ℤ)) +
      mono (3 * (42 : ℕ) * c2 2 + 189 * 2) ((-Z84 ^ (21 : ℤ)) ^ (2 : ℤ)) * θ (h3qe hqG) (7 * (42 : ℕ) * 2 + 189) (Z84 ^ (63 : ℤ)) =
      2 * mono (-1512) 1 * θ h504 336 1 := by
  have hp := pair_plus (h3qe hqG) (7 * (42 : ℕ) * 2 + 189) c21_ne
  rw [negsq21, θ504, show (((3 * 42 : ℕ) : ℤ) + 2 * (7 * ((42 : ℕ) : ℤ) * 2 + 189)) = 1680 by norm_num,
    θ504_1680] at hp
  have m1 : (mono (3 * (42 : ℕ) * c2 2 + 189 * 2) ((-Z84 ^ (63 : ℤ)) ^ (2 : ℤ)) : L) =
      mono (3 * (42 : ℕ) * c2 2 + 189 * 2) ((-Z84 ^ (21 : ℤ)) ^ (2 : ℤ)) :=
    mono_ext rfl (by rw [Z63_eq, neg_neg]; simp only [zpow_two]; ring)
  have hkey : (mono (3 * (42 : ℕ) * c2 2 + 189 * 2) ((-Z84 ^ (21 : ℤ)) ^ (2 : ℤ)) : L) * mono (-2016) (-1) =
      mono (-1512) 1 := by
    rw [mono_mul]
    refine mono_ext (by norm_num [c2]) ?_
    rw [show ((-Z84 ^ (21 : ℤ)) ^ (2 : ℤ)) = -(-(Z84 ^ (21 : ℤ)) ^ 2) by rw [zpow_two, sq]; ring, negsq21]
    norm_num
  rw [m1, Z63_eq]
  linear_combination (mono (3 * (42 : ℕ) * c2 2 + 189 * 2) ((-Z84 ^ (21 : ℤ)) ^ (2 : ℤ)) : L) * hp +
    2 * θ h504 336 1 * hkey

/-- **the `g`-side at `(x₁, y₁)`**: `J̄ g = 2 j(Q²;Q³)(Q⁻³A(Q²) + Q⁻⁹A(Q⁻⁸))`. -/
theorem gNum_x1 :
    gNum hqG 189 (Z84 ^ (63 : ℤ)) 189 (Z84 ^ (21 : ℤ)) =
      2 * θ h504 336 1 * (mono (-504) 1 * Av (h120 hqG) 336 1 0 (-1) +
        mono (-1512) 1 * Av (h120 hqG) (-1344) 1 0 (-1)) := by
  have ex0 : eX (qe := 42) 189 0 189 = 2016 := by norm_num [eX]
  have ex1 : eX (qe := 42) 189 1 189 = 336 := by norm_num [eX]
  have ex2 : eX (qe := 42) 189 2 189 = -1344 := by norm_num [eX]
  have ey0 : eY (qe := 42) 189 0 189 = 2016 := by norm_num [eY]
  have ey1 : eY (qe := 42) 189 1 189 = 336 := by norm_num [eY]
  have ey2 : eY (qe := 42) 189 2 189 = -1344 := by norm_num [eY]
  have cx1 : cX (Z84 ^ (63 : ℤ)) (Z84 ^ (21 : ℤ)) = 1 := by
    unfold cX; simp only [Z_neg']; zsimp; exact Z_eq_one (by norm_num)
  have cy1 : cY (Z84 ^ (63 : ℤ)) (Z84 ^ (21 : ℤ)) = 1 := by
    unfold cY; simp only [Z_neg']; zsimp; exact Z_eq_one (by norm_num)
  unfold gNum g1 g2
  rw [ex0, ex1, ex2, ey0, ey1, ey2, cx1, cy1]
  linear_combination Av (h120 hqG) 2016 1 0 (-1) * brk0₁ + Av (h120 hqG) 336 1 0 (-1) * brk1₁ +
    Av (h120 hqG) (-1344) 1 0 (-1) * brk2₁

end MTC
