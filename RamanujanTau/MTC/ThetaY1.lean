/-
# `θ_{3,4}(x₁, y₁)` as a theta product

With `K_a = j(−Q^a;Q⁸⁰)`: (1.4b) gives the four products `J̄_aJ̄_b` (`J̄` base `Q⁴⁰`), (1.2f) the dissections of
`J_{3,20}, J_{7,20}, J_{1,5}`, and (1.2c) `J_{3,20}J̄_{3,20} = J_{6,40}J_{20,40}`, `J_{7,20}J̄_{7,20} = J_{14,40}J_{20,40}`:

`S1_prod`: `S₁ · J̄₂J̄₈J̄₁₂J̄₁₈ J_{20,40} = −Q⁻³ J_{3,20} J_{5,20} J_{7,20} J_{1,5}`.
-/
import RamanujanTau.MTC.ThetaX1
import RamanujanTau.MTC.ThetaY373
import RamanujanTau.MTC.ThetaLem

set_option autoImplicit false

namespace MTC
open ALz HahnSeries

lemma prod_2_12 : jB 2 * jB 12 = K80 14 * K80 30 - mono 336 (-1) * (K80 26 * K80 10) := by
  unfold jB
  rw [θ_mul (h160 hqT) _ _ (by norm_num) (by norm_num)]
  simp only [b13440]
  norm_num
  rw [show (9072 : ℤ) = 13440 - 168 * 26 by norm_num, Kref, show (11760 : ℤ) = 13440 - 168 * 10 by norm_num, Kref]
  unfold K80; norm_num

lemma prod_8_18 : jB 8 * jB 18 = K80 26 * K80 30 - mono 1344 (-1) * (K80 14 * K80 10) := by
  unfold jB
  rw [θ_mul (h160 hqT) _ _ (by norm_num) (by norm_num)]
  simp only [b13440]
  norm_num
  rw [show (11088 : ℤ) = 13440 - 168 * 14 by norm_num, Kref, show (11760 : ℤ) = 13440 - 168 * 10 by norm_num, Kref]
  unfold K80; norm_num

lemma prod_12_18 : jB 12 * jB 18 = K80 30 * K80 34 - mono 2016 (-1) * (K80 10 * K80 6) := by
  unfold jB
  rw [θ_mul (h160 hqT) _ _ (by norm_num) (by norm_num)]
  simp only [b13440]
  norm_num
  rw [show (11760 : ℤ) = 13440 - 168 * 10 by norm_num, Kref, show (12432 : ℤ) = 13440 - 168 * 6 by norm_num, Kref]
  unfold K80; norm_num

lemma prod_2_8 : jB 2 * jB 8 = K80 10 * K80 34 - mono 336 (-1) * (K80 30 * K80 6) := by
  unfold jB
  rw [θ_mul (h160 hqT) _ _ (by norm_num) (by norm_num)]
  simp only [b13440]
  norm_num
  rw [show (8400 : ℤ) = 13440 - 168 * 30 by norm_num, Kref, show (12432 : ℤ) = 13440 - 168 * 6 by norm_num, Kref]
  unfold K80; norm_num

lemma dis_3 : J20 3 = K80 26 - mono 504 1 * K80 14 := by
  unfold J20
  rw [dissect2 h3360 _ one_ne_zero]
  simp only [b13440']
  norm_num
  rw [show (-2352 : ℤ) = -(2352) by norm_num, inv_m]
  unfold K80
  have e : (single (2856:ℤ) (1:ℂ) : L) * mono (-2352) (-1) = -mono 504 1 := by
    rw [show (single (2856:ℤ) (1:ℂ) : L) = mono 2856 1 from rfl, mono_mul, neg_mono_x]
    exact mono_ext (by norm_num) (by norm_num)
  rw [show (168:ℤ) * 26 = 4368 by norm_num, show (168:ℤ) * 14 = 2352 by norm_num]
  linear_combination (θ h13440 2352 (-1)) * e

lemma dis_7 : J20 7 = K80 34 - mono 1176 1 * K80 6 := by
  unfold J20
  rw [dissect2 h3360 _ one_ne_zero]
  simp only [b13440']
  norm_num
  rw [show (-1008 : ℤ) = -(1008) by norm_num, inv_m]
  unfold K80
  have e : (single (2184:ℤ) (1:ℂ) : L) * mono (-1008) (-1) = -mono 1176 1 := by
    rw [show (single (2184:ℤ) (1:ℂ) : L) = mono 2184 1 from rfl, mono_mul, neg_mono_x]
    exact mono_ext (by norm_num) (by norm_num)
  rw [show (168:ℤ) * 34 = 5712 by norm_num, show (168:ℤ) * 6 = 1008 by norm_num]
  linear_combination (θ h13440 1008 (-1)) * e

lemma c12c : J20 3 * B20 3 = jA 6 * jA 20 := by
  unfold J20 B20
  rw [θ_mul h3360 _ _ one_ne_zero (by norm_num)]
  simp only [b6720]
  norm_num
  rw [θ6720_qpow]
  unfold jA; norm_num

lemma c12d : J20 7 * B20 7 = jA 14 * jA 20 := by
  unfold J20 B20
  rw [θ_mul h3360 _ _ one_ne_zero (by norm_num)]
  simp only [b6720]
  norm_num
  rw [θ6720_qpow]
  unfold jA; norm_num

lemma dD1 : J5 1 = B20 7 - mono 168 1 * B20 3 := by
  unfold J5
  rw [dissect2 h840 _ one_ne_zero]
  simp only [b3360]
  norm_num
  rw [show (-504 : ℤ) = -(504) by norm_num, inv_m]
  unfold B20
  have e : (single (672:ℤ) (1:ℂ) : L) * mono (-504) (-1) = -mono 168 1 := by
    rw [show (single (672:ℤ) (1:ℂ) : L) = mono 672 1 from rfl, mono_mul, neg_mono_x]
    exact mono_ext (by norm_num) (by norm_num)
  rw [show (168:ℤ) * 7 = 1176 by norm_num, show (168:ℤ) * 3 = 504 by norm_num]
  linear_combination (θ h3360 504 (-1)) * e

/-- **`S₁` as a product**. -/
theorem S1_prod :
    (jA 14 / (jB 18 * jB 8) + mono (-336) 1 * jA 6 / (jB 2 * jB 8) -
      mono 504 1 * jA 6 / (jB 12 * jB 18) - mono (-504) 1 * jA 14 / (jB 12 * jB 2)) *
      ((jB 2 * jB 8 * jB 12 * jB 18) * jA 20) =
      -(mono (-504) 1 * (J20 3 * J20 5 * J20 7 * J5 1)) := by
  have hb : ∀ a : ℤ, jB a ≠ 0 := fun a => by
    unfold jB
    exact θ_ne_zero (h160 hqT) (by norm_num) fun _ _ => by norm_num
  have h2 := hb 2; have h8 := hb 8; have h12 := hb 12; have h18 := hb 18
  have hQ := Qm_ne
  have p1 := prod_2_12; have p2 := prod_8_18; have p3 := prod_12_18; have p4 := prod_2_8
  have d3 := dis_3; have d5 := dis_5; have d7 := dis_7; have dd := dD1; have c3 := c12c; have c7 := c12d
  rw [show (mono 336 (-1) : L) = -Qm ^ 2 by rw [← m336, neg_mono_x]] at p1 p4
  rw [show (mono 1344 (-1) : L) = -Qm ^ 8 by rw [← mQ 8 1344 (by norm_num), neg_mono_x]] at p2
  rw [show (mono 2016 (-1) : L) = -Qm ^ 12 by rw [← mQ 12 2016 (by norm_num), neg_mono_x]] at p3
  rw [mQ 3 504 (by norm_num)] at d3
  rw [m840] at d5
  rw [mQ 7 1176 (by norm_num)] at d7
  rw [show (mono 168 1 : L) = Qm from rfl] at dd
  rw [mneg336, mQ 3 504 (by norm_num), mQn 3 (-504) (by norm_num)]
  have e1 : (jA 14 / (jB 18 * jB 8) + (Qm ^ 2)⁻¹ * jA 6 / (jB 2 * jB 8) - Qm ^ 3 * jA 6 / (jB 12 * jB 18) -
      (Qm ^ 3)⁻¹ * jA 14 / (jB 12 * jB 2)) * ((jB 2 * jB 8 * jB 12 * jB 18) * jA 20) =
      (jA 14 * (jB 2 * jB 12 - (Qm ^ 3)⁻¹ * (jB 8 * jB 18)) +
        jA 6 * ((Qm ^ 2)⁻¹ * (jB 12 * jB 18) - Qm ^ 3 * (jB 2 * jB 8))) * jA 20 := by
    field_simp
    ring
  rw [e1, p1, p2, p3, p4]
  have key : (jA 14 * (K80 14 * K80 30 - -Qm ^ 2 * (K80 26 * K80 10) - (Qm ^ 3)⁻¹ *
      (K80 26 * K80 30 - -Qm ^ 8 * (K80 14 * K80 10))) +
      jA 6 * ((Qm ^ 2)⁻¹ * (K80 30 * K80 34 - -Qm ^ 12 * (K80 10 * K80 6)) -
        Qm ^ 3 * (K80 10 * K80 34 - -Qm ^ 2 * (K80 30 * K80 6)))) * jA 20 =
      J20 5 * ((Qm ^ 2)⁻¹ * (jA 6 * jA 20) * J20 7 - (Qm ^ 3)⁻¹ * (jA 14 * jA 20) * J20 3) := by
    rw [d3, d5, d7]
    field_simp
    ring
  rw [key, ← c3, ← c7, dd]
  field_simp
  ring

end MTC
