/-
# The Weierstrass relation behind HM Prop. 1.1 at the MTC₀ point

With `j_a = j(Q^a; Q³⁰)`, `j̄_a = j(−Q^a; Q³⁰)` (`Q = t^{168}`):

  `j̄₁₈ j₈ j̄₄ j₂ + Q⁻² j̄₈ j₁₂ j̄₁₄ j₂ = Q⁻² j̄₁₆ j̄₆ j₁₀ j₄`   (`P11W`),

Weierstrass' three-term relation at `x = −Q¹¹`, `y = Q⁵`, `u = Q³`, `v = Q⁷`. It sums the two change-of-`z`
quotients `R₁₄ + Q⁻² R₄` of HM Prop. 1.1.
-/
import RamanujanTau.MTC.F1Prime

set_option autoImplicit false

namespace MTC
open ALz HahnSeries

/-- `j(−Q^a; Q³⁰)`. -/
noncomputable def jb30 (a : ℤ) : L := θ (h120 hqT) (168 * a) (-1)

/-- **the Weierstrass instance**. -/
theorem P11W :
    jb30 18 * j30 8 * jb30 4 * j30 2 + mono (-336) 1 * (jb30 8 * j30 12 * jb30 14 * j30 2) =
      mono (-336) 1 * (jb30 16 * jb30 6 * j30 10 * j30 4) := by
  have hw := weierstrass (h120 hqT) (by' := 840) (bu := 504) (bv := 1176) (bx := 1848) (cy := 1) (cu := 1) (cv := 1)
    (cx := -1) one_ne_zero one_ne_zero one_ne_zero (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [mul_one, inv_one, one_mul] at hw
  norm_num at hw
  rw [show (-672 : ℤ) = -(672) by norm_num, tinv1, show (-336 : ℤ) = -(336) by norm_num, tinv1] at hw
  unfold jb30 j30
  norm_num
  have eb : (mono (-672) 1 : L) = mono (-336) 1 * mono (-336) 1 := by
    rw [mono_mul]; exact mono_ext (by norm_num) (by norm_num)
  have eu : (mono 336 1 : L) * mono (-336) 1 = 1 := by
    rw [mono_mul, show (1 : L) = mono 0 1 from rfl]; exact mono_ext (by norm_num) (by norm_num)
  linear_combination (mono 336 1 : L) * hw + ((mono 336 1 : L) * (θ (h120 hqT) 2688 (-1) * θ (h120 hqT) 1008 (-1) * θ (h120 hqT) 1680 1 * θ (h120 hqT) 672 1)) * eb +
    (-((θ (h120 hqT) 3024 (-1) * θ (h120 hqT) 672 (-1) * θ (h120 hqT) 1344 1 * θ (h120 hqT) 336 1) + (mono (-336) 1 : L) * (θ (h120 hqT) 2016 1 * θ (h120 hqT) 336 1 * θ (h120 hqT) 2352 (-1) * θ (h120 hqT) 1344 (-1)) - (mono (-336) 1 : L) * (θ (h120 hqT) 2688 (-1) * θ (h120 hqT) 1008 (-1) * θ (h120 hqT) 1680 1 * θ (h120 hqT) 672 1))) * eu

end MTC
