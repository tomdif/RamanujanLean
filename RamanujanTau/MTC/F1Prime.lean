/-
# `J_{4,30} J_{8,30} J_{12,30} = J_{2,30} J_{12,30} J_{14,30} + Q² J_{2,30} J_{6,30} J_{8,30}`

This is the identity behind the equivalence of the rank form of `Φ(Q²)` with HM Prop. 3.2. It is Weierstrass'
three-term relation (`ALz.weierstrass`) at `y = Q⁻¹⁴`, `u = Q²`, `v = Q⁴`, `x = Q⁶` (base `Q³⁰`, `Q = t^{168}`), divided by
the common factor `J_{10,30}`.
-/
import RamanujanTau.MTC.ThetaY373

set_option autoImplicit false

namespace MTC
open ALz HahnSeries

/-- `j(Q^a; Q³⁰)`. -/
noncomputable def j30 (a : ℤ) : L := θ (h120 hqT) (168 * a) 1

lemma tinv1 {N : ℕ} (hN : 1 ≤ N) (e : ℤ) : θ hN (-e) 1 = -mono (-e) 1 * θ hN e 1 := by
  have h := θ_inv hN e one_ne_zero
  rwa [inv_one] at h

lemma trefl1 {N : ℕ} (hN : 1 ≤ N) (e : ℤ) : θ hN (N - e) 1 = θ hN e 1 := by
  have h := θ_reflect hN e one_ne_zero
  rwa [inv_one] at h

lemma j30_ne (a : ℤ) (h : ¬ (30 : ℤ) ∣ a) : j30 a ≠ 0 := by
  unfold j30
  refine θ_ne_zero (h120 hqT) one_ne_zero fun m hm => ?_
  exfalso; apply h
  refine ⟨m, ?_⟩
  have : (168 : ℤ) * a = 168 * (30 * m) := by rw [hm]; push_cast; ring
  omega

/-- the Weierstrass instance, normalized. -/
lemma weier_F1 :
    mono (-1680) 1 * (j30 2 * j30 6 * j30 8 * j30 10) + mono (-2016) 1 * (j30 2 * j30 10 * j30 12 * j30 14) =
      mono (-2016) 1 * (j30 4 * j30 8 * j30 10 * j30 12) := by
  have hw := weierstrass (h120 hqT) (by' := -2352) (bu := 336) (bv := 672) (bx := 1008) (cy := 1) (cu := 1) (cv := 1)
    (cx := 1) one_ne_zero one_ne_zero one_ne_zero one_ne_zero (by norm_num) (by norm_num) (by norm_num)
  simp only [mul_one, inv_one] at hw
  norm_num at hw
  rw [show (-1344 : ℤ) = -(1344) by norm_num, tinv1, show (3360 : ℤ) = ((120 * 42 : ℕ) : ℤ) - 1680 by norm_num,
    trefl1, show (-336 : ℤ) = -(336) by norm_num, tinv1, show (-2016 : ℤ) = -(2016) by norm_num, tinv1,
    show (2688 : ℤ) = ((120 * 42 : ℕ) : ℤ) - 2352 by norm_num, trefl1, show (-1680 : ℤ) = -(1680) by norm_num, tinv1,
    show (-3024 : ℤ) = -(3024) by norm_num, tinv1, show (3024 : ℤ) = ((120 * 42 : ℕ) : ℤ) - 2016 by norm_num,
    trefl1] at hw
  unfold j30
  norm_num
  have e1 : (mono (-1344) 1 : L) * mono (-336) 1 = mono (-1680) 1 := by rw [mono_mul]; exact mono_ext (by norm_num) (by norm_num)
  have e2 : (mono (((120 * 42 : ℕ) : ℤ) - 2352) 1 : L) * mono (-1680) 1 * mono (-(((120 * 42 : ℕ) : ℤ) - 2016)) 1 =
      mono (-2016) 1 := by
    rw [mono_mul, mono_mul]; exact mono_ext (by norm_num) (by norm_num)
  linear_combination hw - (θ (h120 hqT) 336 1 * θ (h120 hqT) 1008 1 * θ (h120 hqT) 1344 1 * θ (h120 hqT) 1680 1) * e1 +
    (θ (h120 hqT) 672 1 * θ (h120 hqT) 1344 1 * θ (h120 hqT) 1680 1 * θ (h120 hqT) 2016 1) * e2

/-- **F1′**. -/
theorem F1prime : j30 4 * j30 8 * j30 12 = j30 2 * j30 12 * j30 14 + mono 336 1 * (j30 2 * j30 6 * j30 8) := by
  have hw := weier_F1
  have h10 : j30 10 ≠ 0 := j30_ne 10 (by norm_num)
  have hQ := Qm_ne
  rw [show (-1680 : ℤ) = -(168 * ((10 : ℕ) : ℤ)) by norm_num, mneg, show (-2016 : ℤ) = -(168 * ((12 : ℕ) : ℤ)) by norm_num,
    mneg] at hw
  rw [m336]
  have hQ10 : (Qm ^ 10) ≠ 0 := pow_ne_zero _ hQ
  have hQ12 : (Qm ^ 12) ≠ 0 := pow_ne_zero _ hQ
  field_simp at hw
  linear_combination -hw
