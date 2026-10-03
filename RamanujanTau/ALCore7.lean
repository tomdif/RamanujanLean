/-
# The 38 level-21 theta identities of the rank-mod-7 theta core (generated)

Each is a `linear_combination` of normalized Weierstrass instances `W_x_y_u_v` (certificates found by
sparse elimination, campaigns/rank7/m4). Atoms: `Jt a = θ(Q^a;Q^21)`, `Qt = Q`.
-/
import RamanujanTau.ALThetaCore

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace ALz
open HahnSeries
section Core7
variable {N : ℕ} (hN : 1 ≤ N) {d : ℕ} (hd : N = 21 * d)
include hN hd

theorem W_m5_m1_6_7 :
    (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 1 * Jt hN hd 4 * Jt hN hd 6 * Jt hN hd 8 + (1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 2 * Jt hN hd 5 * Jt hN hd 7 * Jt hN hd 9 + (-1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 1 * Jt hN hd 6 * Jt hN hd 8 * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-5) + (-1))) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-5) - (-1))) 1 = -((Qt hd ^ 4)⁻¹ * Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (6 + 7)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (6 - 7)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-5) + 7)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-5) - 7)) 1 = -((Qt hd ^ 12)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 (-1) (-12) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (6 + (-1))) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (6 - (-1))) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 7)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 7)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-5) + 6)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-5) - 6)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -5) (y := -1) (u := 6) (v := 7) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((6 : ℤ) - (-1)) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m4_m3_5_7 :
    (-1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 1 * Jt hN hd 2 * Jt hN hd 7 * Jt hN hd 9 + (1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 2 * Jt hN hd 3 * Jt hN hd 8 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 1 * Jt hN hd 4 * Jt hN hd 9 * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-4) + (-3))) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-4) - (-3))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (5 + 7)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (5 - 7)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-4) + 7)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-4) - 7)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (5 + (-3))) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (5 - (-3))) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-3) + 7)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-3) - 7)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-4) + 5)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-4) - 5)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -4) (y := -3) (u := 5) (v := 7) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((5 : ℤ) - (-3)) = ((8 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m4_m2_5_6 :
    (-1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 1 * Jt hN hd 2 * Jt hN hd 6 * Jt hN hd 10 + (1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 2 * Jt hN hd 3 * Jt hN hd 7 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 1 * Jt hN hd 4 * Jt hN hd 8 * Jt hN hd 9 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-4) + (-2))) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-4) - (-2))) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (5 + 6)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (5 - 6)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-4) + 6)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-4) - 6)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (5 + (-2))) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (5 - (-2))) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-2) + 6)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-2) - 6)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-4) + 5)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-4) - 5)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -4) (y := -2) (u := 5) (v := 6) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((5 : ℤ) - (-2)) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m4_m2_5_8 :
    (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 2 * Jt hN hd 3 * Jt hN hd 6 * Jt hN hd 8 + (1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * Jt hN hd 7 * Jt hN hd 9 + (-1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 1 * Jt hN hd 6 * Jt hN hd 9 * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-4) + (-2))) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-4) - (-2))) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (5 + 8)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (5 - 8)) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-4) + 8)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-4) - 8)) 1 = -((Qt hd ^ 12)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 (-1) (-12) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (5 + (-2))) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (5 - (-2))) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-2) + 8)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-2) - 8)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-4) + 5)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-4) - 5)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -4) (y := -2) (u := 5) (v := 8) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((5 : ℤ) - (-2)) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m4_m2_5_10 :
    (-1 : L) * (Qt hd ^ 13)⁻¹ * Jt hN hd 2 * Jt hN hd 5 * Jt hN hd 6 ^ 2 + (1 : L) * (Qt hd ^ 14)⁻¹ * Jt hN hd 3 * Jt hN hd 6 * Jt hN hd 7 ^ 2 + (-1 : L) * (Qt hd ^ 14)⁻¹ * Jt hN hd 1 * Jt hN hd 8 * Jt hN hd 9 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-4) + (-2))) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-4) - (-2))) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (5 + 10)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (5 - 10)) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-4) + 10)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-4) - 10)) 1 = -((Qt hd ^ 14)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 (-1) (-14) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (5 + (-2))) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (5 - (-2))) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-2) + 10)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-2) - 10)) 1 = -((Qt hd ^ 12)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 (-1) (-12) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-4) + 5)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-4) - 5)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -4) (y := -2) (u := 5) (v := 10) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((5 : ℤ) - (-2)) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m4_m2_6_7 :
    (-1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 1 * Jt hN hd 2 * Jt hN hd 6 * Jt hN hd 8 + (1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * Jt hN hd 8 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 2 * Jt hN hd 5 * Jt hN hd 9 * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-4) + (-2))) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-4) - (-2))) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (6 + 7)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (6 - 7)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-4) + 7)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-4) - 7)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (6 + (-2))) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (6 - (-2))) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-2) + 7)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-2) - 7)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-4) + 6)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-4) - 6)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -4) (y := -2) (u := 6) (v := 7) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((6 : ℤ) - (-2)) = ((8 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m4_m2_7_8 :
    (-1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 1 * Jt hN hd 2 * Jt hN hd 6 ^ 2 + (1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 4 * Jt hN hd 5 * Jt hN hd 9 ^ 2 + (-1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 3 * Jt hN hd 6 * Jt hN hd 10 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-4) + (-2))) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-4) - (-2))) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (7 + 8)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (7 - 8)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-4) + 8)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-4) - 8)) 1 = -((Qt hd ^ 12)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 (-1) (-12) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (7 + (-2))) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (7 - (-2))) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-2) + 8)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-2) - 8)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-4) + 7)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-4) - 7)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -4) (y := -2) (u := 7) (v := 8) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((7 : ℤ) - (-2)) = ((9 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m4_m1_5_7 :
    (-1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 2 * Jt hN hd 3 * Jt hN hd 5 * Jt hN hd 9 + (1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * Jt hN hd 6 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 1 * Jt hN hd 6 * Jt hN hd 8 * Jt hN hd 9 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-4) + (-1))) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-4) - (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (5 + 7)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (5 - 7)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-4) + 7)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-4) - 7)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (5 + (-1))) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (5 - (-1))) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 7)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 7)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-4) + 5)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-4) - 5)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -4) (y := -1) (u := 5) (v := 7) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((5 : ℤ) - (-1)) = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m4_m1_5_9 :
    (-1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * Jt hN hd 5 * Jt hN hd 7 + (1 : L) * (Qt hd ^ 13)⁻¹ * Jt hN hd 4 * Jt hN hd 5 * Jt hN hd 6 * Jt hN hd 8 + (-1 : L) * (Qt hd ^ 13)⁻¹ * Jt hN hd 1 * Jt hN hd 8 * Jt hN hd 9 * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-4) + (-1))) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-4) - (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (5 + 9)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (5 - 9)) 1 = -((Qt hd ^ 4)⁻¹ * Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-4) + 9)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-4) - 9)) 1 = -((Qt hd ^ 13)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 (-1) (-13) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (5 + (-1))) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (5 - (-1))) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 9)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 9)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-4) + 5)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-4) - 5)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -4) (y := -1) (u := 5) (v := 9) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((5 : ℤ) - (-1)) = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m4_m1_5_10 :
    (-1 : L) * (Qt hd ^ 13)⁻¹ * Jt hN hd 3 * Jt hN hd 5 ^ 2 * Jt hN hd 6 + (1 : L) * (Qt hd ^ 14)⁻¹ * Jt hN hd 4 * Jt hN hd 6 ^ 2 * Jt hN hd 7 + (-1 : L) * (Qt hd ^ 14)⁻¹ * Jt hN hd 1 * Jt hN hd 9 ^ 2 * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-4) + (-1))) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-4) - (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (5 + 10)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (5 - 10)) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-4) + 10)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-4) - 10)) 1 = -((Qt hd ^ 14)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 (-1) (-14) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (5 + (-1))) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (5 - (-1))) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 10)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 10)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-4) + 5)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-4) - 5)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -4) (y := -1) (u := 5) (v := 10) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((5 : ℤ) - (-1)) = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m4_m1_6_8 :
    (-1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 2 * Jt hN hd 3 * Jt hN hd 5 * Jt hN hd 7 + (1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 4 * Jt hN hd 5 * Jt hN hd 7 * Jt hN hd 9 + (-1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 2 * Jt hN hd 7 * Jt hN hd 9 * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-4) + (-1))) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-4) - (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (6 + 8)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (6 - 8)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-4) + 8)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-4) - 8)) 1 = -((Qt hd ^ 12)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 (-1) (-12) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (6 + (-1))) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (6 - (-1))) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 8)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 8)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-4) + 6)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-4) - 6)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -4) (y := -1) (u := 6) (v := 8) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((6 : ℤ) - (-1)) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m4_m1_7_9 :
    (-1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 2 * Jt hN hd 3 * Jt hN hd 5 ^ 2 + (1 : L) * (Qt hd ^ 13)⁻¹ * Jt hN hd 5 * Jt hN hd 6 * Jt hN hd 8 ^ 2 + (-1 : L) * (Qt hd ^ 13)⁻¹ * Jt hN hd 3 * Jt hN hd 8 * Jt hN hd 10 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-4) + (-1))) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-4) - (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (7 + 9)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (7 - 9)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-4) + 9)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-4) - 9)) 1 = -((Qt hd ^ 13)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 (-1) (-13) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (7 + (-1))) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (7 - (-1))) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 9)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 9)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-4) + 7)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-4) - 7)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -4) (y := -1) (u := 7) (v := 9) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((7 : ℤ) - (-1)) = ((8 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m3_m2_4_6 :
    (-1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 1 * Jt hN hd 2 * Jt hN hd 5 * Jt hN hd 10 + (1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 2 * Jt hN hd 3 * Jt hN hd 6 * Jt hN hd 9 + (-1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 1 * Jt hN hd 4 * Jt hN hd 7 * Jt hN hd 8 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-3) + (-2))) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-3) - (-2))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (4 + 6)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (4 - 6)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-3) + 6)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-3) - 6)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (4 + (-2))) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (4 - (-2))) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-2) + 6)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-2) - 6)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-3) + 4)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-3) - 4)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -3) (y := -2) (u := 4) (v := 6) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((4 : ℤ) - (-2)) = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m3_m2_4_8 :
    (-1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 1 * Jt hN hd 4 * Jt hN hd 5 * Jt hN hd 9 + (1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 2 * Jt hN hd 5 * Jt hN hd 6 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 1 * Jt hN hd 6 * Jt hN hd 7 * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-3) + (-2))) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-3) - (-2))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (4 + 8)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (4 - 8)) 1 = -((Qt hd ^ 4)⁻¹ * Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-3) + 8)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-3) - 8)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (4 + (-2))) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (4 - (-2))) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-2) + 8)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-2) - 8)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-3) + 4)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-3) - 4)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -3) (y := -2) (u := 4) (v := 8) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((4 : ℤ) - (-2)) = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m3_m2_4_10 :
    (-1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 1 * Jt hN hd 5 * Jt hN hd 6 * Jt hN hd 7 + (1 : L) * (Qt hd ^ 13)⁻¹ * Jt hN hd 2 * Jt hN hd 6 * Jt hN hd 7 * Jt hN hd 8 + (-1 : L) * (Qt hd ^ 13)⁻¹ * Jt hN hd 1 * Jt hN hd 7 * Jt hN hd 8 * Jt hN hd 9 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-3) + (-2))) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-3) - (-2))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (4 + 10)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (4 - 10)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-3) + 10)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-3) - 10)) 1 = -((Qt hd ^ 13)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 (-1) (-13) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (4 + (-2))) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (4 - (-2))) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-2) + 10)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-2) - 10)) 1 = -((Qt hd ^ 12)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 (-1) (-12) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-3) + 4)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-3) - 4)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -3) (y := -2) (u := 4) (v := 10) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((4 : ℤ) - (-2)) = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m3_m2_5_7 :
    (-1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 1 * Jt hN hd 2 * Jt hN hd 5 * Jt hN hd 9 + (1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * Jt hN hd 7 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 2 * Jt hN hd 5 * Jt hN hd 8 * Jt hN hd 9 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-3) + (-2))) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-3) - (-2))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (5 + 7)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (5 - 7)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-3) + 7)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-3) - 7)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (5 + (-2))) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (5 - (-2))) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-2) + 7)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-2) - 7)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-3) + 5)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-3) - 5)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -3) (y := -2) (u := 5) (v := 7) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((5 : ℤ) - (-2)) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m3_m2_5_10 :
    (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 1 * Jt hN hd 5 ^ 2 * Jt hN hd 6 + (1 : L) * (Qt hd ^ 13)⁻¹ * Jt hN hd 3 * Jt hN hd 7 ^ 2 * Jt hN hd 8 + (-1 : L) * (Qt hd ^ 13)⁻¹ * Jt hN hd 2 * Jt hN hd 8 ^ 2 * Jt hN hd 9 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-3) + (-2))) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-3) - (-2))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (5 + 10)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (5 - 10)) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-3) + 10)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-3) - 10)) 1 = -((Qt hd ^ 13)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 (-1) (-13) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (5 + (-2))) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (5 - (-2))) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-2) + 10)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-2) - 10)) 1 = -((Qt hd ^ 12)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 (-1) (-12) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-3) + 5)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-3) - 5)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -3) (y := -2) (u := 5) (v := 10) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((5 : ℤ) - (-2)) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m3_m2_6_8 :
    (-1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 1 * Jt hN hd 2 * Jt hN hd 5 * Jt hN hd 7 + (1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 4 * Jt hN hd 5 * Jt hN hd 8 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 3 * Jt hN hd 6 * Jt hN hd 9 * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-3) + (-2))) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-3) - (-2))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (6 + 8)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (6 - 8)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-3) + 8)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-3) - 8)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (6 + (-2))) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (6 - (-2))) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-2) + 8)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-2) - 8)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-3) + 6)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-3) - 6)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -3) (y := -2) (u := 6) (v := 8) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((6 : ℤ) - (-2)) = ((8 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m3_m1_4_5 :
    (-1 : L) * (Qt hd ^ 7)⁻¹ * Jt hN hd 1 * Jt hN hd 2 * Jt hN hd 4 * Jt hN hd 9 + (1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 2 * Jt hN hd 3 * Jt hN hd 5 * Jt hN hd 8 + (-1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 1 * Jt hN hd 4 * Jt hN hd 6 * Jt hN hd 7 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-3) + (-1))) 1 = -((Qt hd ^ 4)⁻¹ * Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-3) - (-1))) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (4 + 5)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (4 - 5)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-3) + 5)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-3) - 5)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (4 + (-1))) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (4 - (-1))) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 5)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 5)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-3) + 4)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-3) - 4)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -3) (y := -1) (u := 4) (v := 5) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((4 : ℤ) - (-1)) = ((5 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m3_m1_4_7 :
    (-1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 2 * Jt hN hd 3 * Jt hN hd 4 * Jt hN hd 10 + (1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * Jt hN hd 5 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 1 * Jt hN hd 6 * Jt hN hd 7 * Jt hN hd 8 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-3) + (-1))) 1 = -((Qt hd ^ 4)⁻¹ * Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-3) - (-1))) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (4 + 7)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (4 - 7)) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-3) + 7)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-3) - 7)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (4 + (-1))) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (4 - (-1))) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 7)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 7)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-3) + 4)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-3) - 4)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -3) (y := -1) (u := 4) (v := 7) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((4 : ℤ) - (-1)) = ((5 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m3_m1_4_10 :
    (-1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 2 * Jt hN hd 4 * Jt hN hd 6 * Jt hN hd 7 + (1 : L) * (Qt hd ^ 13)⁻¹ * Jt hN hd 3 * Jt hN hd 5 * Jt hN hd 7 * Jt hN hd 8 + (-1 : L) * (Qt hd ^ 13)⁻¹ * Jt hN hd 1 * Jt hN hd 7 * Jt hN hd 9 * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-3) + (-1))) 1 = -((Qt hd ^ 4)⁻¹ * Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-3) - (-1))) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (4 + 10)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (4 - 10)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-3) + 10)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-3) - 10)) 1 = -((Qt hd ^ 13)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 (-1) (-13) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (4 + (-1))) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (4 - (-1))) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 10)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 10)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-3) + 4)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-3) - 4)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -3) (y := -1) (u := 4) (v := 10) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((4 : ℤ) - (-1)) = ((5 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m3_m1_5_6 :
    (-1 : L) * (Qt hd ^ 7)⁻¹ * Jt hN hd 1 * Jt hN hd 2 * Jt hN hd 4 * Jt hN hd 10 + (1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * Jt hN hd 6 * Jt hN hd 9 + (-1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 2 * Jt hN hd 5 * Jt hN hd 7 * Jt hN hd 8 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-3) + (-1))) 1 = -((Qt hd ^ 4)⁻¹ * Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-3) - (-1))) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (5 + 6)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (5 - 6)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-3) + 6)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-3) - 6)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (5 + (-1))) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (5 - (-1))) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 6)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 6)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-3) + 5)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-3) - 5)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -3) (y := -1) (u := 5) (v := 6) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((5 : ℤ) - (-1)) = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m3_m1_6_9 :
    (-1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 2 * Jt hN hd 3 * Jt hN hd 4 * Jt hN hd 6 + (1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 5 * Jt hN hd 6 * Jt hN hd 7 * Jt hN hd 9 + (-1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 3 * Jt hN hd 8 * Jt hN hd 9 * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-3) + (-1))) 1 = -((Qt hd ^ 4)⁻¹ * Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-3) - (-1))) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (6 + 9)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (6 - 9)) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-3) + 9)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-3) - 9)) 1 = -((Qt hd ^ 12)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 (-1) (-12) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (6 + (-1))) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (6 - (-1))) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 9)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 9)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-3) + 6)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-3) - 6)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -3) (y := -1) (u := 6) (v := 9) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((6 : ℤ) - (-1)) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m3_m1_7_8 :
    (-1 : L) * (Qt hd ^ 7)⁻¹ * Jt hN hd 1 * Jt hN hd 2 * Jt hN hd 4 * Jt hN hd 6 + (1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 5 * Jt hN hd 6 * Jt hN hd 8 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 4 * Jt hN hd 7 * Jt hN hd 9 * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-3) + (-1))) 1 = -((Qt hd ^ 4)⁻¹ * Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-3) - (-1))) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (7 + 8)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (7 - 8)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-3) + 8)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-3) - 8)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (7 + (-1))) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (7 - (-1))) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 8)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 8)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-3) + 7)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-3) - 7)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -3) (y := -1) (u := 7) (v := 8) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((7 : ℤ) - (-1)) = ((8 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m3_0_4_6 :
    (-1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 2 * Jt hN hd 3 ^ 2 * Jt hN hd 10 + (1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 3 * Jt hN hd 4 ^ 2 * Jt hN hd 9 + (-1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 1 * Jt hN hd 6 ^ 2 * Jt hN hd 7 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-3) + 0)) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-3) - 0)) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (4 + 6)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (4 - 6)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-3) + 6)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-3) - 6)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (4 + 0)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (4 - 0)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 6)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 6)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-3) + 4)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-3) - 4)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -3) (y := 0) (u := 4) (v := 6) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((4 : ℤ) - 0) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m3_0_6_9 :
    (-1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 3 ^ 3 * Jt hN hd 6 + (1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 6 ^ 3 * Jt hN hd 9 + (-1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 3 * Jt hN hd 9 ^ 3 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-3) + 0)) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-3) - 0)) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (6 + 9)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (6 - 9)) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-3) + 9)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-3) - 9)) 1 = -((Qt hd ^ 12)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 (-1) (-12) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (6 + 0)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (6 - 0)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 9)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 9)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-3) + 6)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-3) - 6)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -3) (y := 0) (u := 6) (v := 9) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((6 : ℤ) - 0) = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_m1_3_5 :
    (-1 : L) * (Qt hd ^ 6)⁻¹ * Jt hN hd 1 * Jt hN hd 2 * Jt hN hd 3 * Jt hN hd 8 + (1 : L) * (Qt hd ^ 7)⁻¹ * Jt hN hd 2 * Jt hN hd 3 * Jt hN hd 4 * Jt hN hd 7 + (-1 : L) * (Qt hd ^ 7)⁻¹ * Jt hN hd 1 * Jt hN hd 4 * Jt hN hd 5 * Jt hN hd 6 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - (-1))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (3 + 5)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (3 - 5)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 5)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 5)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (3 + (-1))) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (3 - (-1))) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 5)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 5)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 3)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 3)) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := -1) (u := 3) (v := 5) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((3 : ℤ) - (-1)) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_m1_3_7 :
    (-1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 1 * Jt hN hd 3 * Jt hN hd 4 * Jt hN hd 10 + (1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 2 * Jt hN hd 4 * Jt hN hd 5 * Jt hN hd 9 + (-1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 1 * Jt hN hd 5 * Jt hN hd 6 * Jt hN hd 8 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - (-1))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (3 + 7)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (3 - 7)) 1 = -((Qt hd ^ 4)⁻¹ * Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 7)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 7)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (3 + (-1))) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (3 - (-1))) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 7)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 7)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 3)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 3)) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := -1) (u := 3) (v := 7) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((3 : ℤ) - (-1)) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_m1_3_8 :
    (-1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 1 * Jt hN hd 3 * Jt hN hd 5 * Jt hN hd 10 + (1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 2 * Jt hN hd 4 * Jt hN hd 6 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 1 * Jt hN hd 5 * Jt hN hd 7 * Jt hN hd 9 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - (-1))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (3 + 8)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (3 - 8)) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 8)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 8)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (3 + (-1))) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (3 - (-1))) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 8)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 8)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 3)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 3)) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := -1) (u := 3) (v := 8) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((3 : ℤ) - (-1)) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_m1_3_9 :
    (-1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 1 * Jt hN hd 3 * Jt hN hd 6 * Jt hN hd 9 + (1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 2 * Jt hN hd 4 * Jt hN hd 7 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 1 * Jt hN hd 5 * Jt hN hd 8 * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - (-1))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (3 + 9)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (3 - 9)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 9)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 9)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (3 + (-1))) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (3 - (-1))) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 9)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 9)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 3)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 3)) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := -1) (u := 3) (v := 9) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((3 : ℤ) - (-1)) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_m1_4_6 :
    (-1 : L) * (Qt hd ^ 6)⁻¹ * Jt hN hd 1 * Jt hN hd 2 * Jt hN hd 3 * Jt hN hd 10 + (1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * Jt hN hd 5 * Jt hN hd 8 + (-1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 2 * Jt hN hd 5 * Jt hN hd 6 * Jt hN hd 7 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - (-1))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (4 + 6)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (4 - 6)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 6)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 6)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (4 + (-1))) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (4 - (-1))) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 6)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 6)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 4)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 4)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := -1) (u := 4) (v := 6) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((4 : ℤ) - (-1)) = ((5 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_m1_4_8 :
    (-1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 1 * Jt hN hd 3 * Jt hN hd 4 * Jt hN hd 9 + (1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 3 * Jt hN hd 5 * Jt hN hd 6 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 2 * Jt hN hd 6 * Jt hN hd 7 * Jt hN hd 9 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - (-1))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (4 + 8)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (4 - 8)) 1 = -((Qt hd ^ 4)⁻¹ * Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 8)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 8)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (4 + (-1))) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (4 - (-1))) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 8)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 8)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 4)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 4)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := -1) (u := 4) (v := 8) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((4 : ℤ) - (-1)) = ((5 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_m1_4_9 :
    (-1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 1 * Jt hN hd 3 * Jt hN hd 5 * Jt hN hd 8 + (1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 3 * Jt hN hd 5 * Jt hN hd 7 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 2 * Jt hN hd 6 * Jt hN hd 8 * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - (-1))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (4 + 9)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (4 - 9)) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 9)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 9)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (4 + (-1))) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (4 - (-1))) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 9)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 9)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 4)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 4)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := -1) (u := 4) (v := 9) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((4 : ℤ) - (-1)) = ((5 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_m1_4_10 :
    (-1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 1 * Jt hN hd 3 * Jt hN hd 6 * Jt hN hd 7 + (1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 3 * Jt hN hd 5 * Jt hN hd 8 * Jt hN hd 9 + (-1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 2 * Jt hN hd 6 * Jt hN hd 9 * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - (-1))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (4 + 10)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (4 - 10)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 10)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 10)) 1 = -((Qt hd ^ 12)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 (-1) (-12) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (4 + (-1))) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (4 - (-1))) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 10)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 10)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 4)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 4)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := -1) (u := 4) (v := 10) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((4 : ℤ) - (-1)) = ((5 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_m1_5_7 :
    (-1 : L) * (Qt hd ^ 6)⁻¹ * Jt hN hd 1 * Jt hN hd 2 * Jt hN hd 3 * Jt hN hd 9 + (1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 4 * Jt hN hd 5 * Jt hN hd 6 * Jt hN hd 9 + (-1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 3 * Jt hN hd 6 * Jt hN hd 7 * Jt hN hd 8 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - (-1))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (5 + 7)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (5 - 7)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 7)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 7)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (5 + (-1))) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (5 - (-1))) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 7)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 7)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 5)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 5)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := -1) (u := 5) (v := 7) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((5 : ℤ) - (-1)) = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_m1_5_8 :
    (-1 : L) * (Qt hd ^ 7)⁻¹ * Jt hN hd 1 * Jt hN hd 3 ^ 2 * Jt hN hd 8 + (1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 4 * Jt hN hd 6 ^ 2 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 3 * Jt hN hd 7 ^ 2 * Jt hN hd 9 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - (-1))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (5 + 8)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (5 - 8)) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 8)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 8)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (5 + (-1))) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (5 - (-1))) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 8)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 8)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 5)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 5)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := -1) (u := 5) (v := 8) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((5 : ℤ) - (-1)) = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_m1_5_9 :
    (-1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 1 * Jt hN hd 3 * Jt hN hd 4 * Jt hN hd 7 + (1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 4 * Jt hN hd 6 * Jt hN hd 7 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 3 * Jt hN hd 7 * Jt hN hd 8 * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - (-1))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (5 + 9)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (5 - 9)) 1 = -((Qt hd ^ 4)⁻¹ * Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 9)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 9)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (5 + (-1))) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (5 - (-1))) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 9)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 9)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 5)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 5)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := -1) (u := 5) (v := 9) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((5 : ℤ) - (-1)) = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_m1_6_8 :
    (-1 : L) * (Qt hd ^ 6)⁻¹ * Jt hN hd 1 * Jt hN hd 2 * Jt hN hd 3 * Jt hN hd 7 + (1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 5 * Jt hN hd 6 * Jt hN hd 7 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 4 * Jt hN hd 7 * Jt hN hd 8 * Jt hN hd 9 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - (-1))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (6 + 8)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (6 - 8)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 8)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 8)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (6 + (-1))) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (6 - (-1))) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 8)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 8)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 6)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 6)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := -1) (u := 6) (v := 8) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((6 : ℤ) - (-1)) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_m1_6_9 :
    (-1 : L) * (Qt hd ^ 7)⁻¹ * Jt hN hd 1 * Jt hN hd 3 ^ 2 * Jt hN hd 6 + (1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 5 * Jt hN hd 7 ^ 2 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 4 * Jt hN hd 8 ^ 2 * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - (-1))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (6 + 9)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (6 - 9)) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 9)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 9)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (6 + (-1))) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (6 - (-1))) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 9)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 9)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 6)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 6)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := -1) (u := 6) (v := 9) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((6 : ℤ) - (-1)) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_m1_7_10 :
    (-1 : L) * (Qt hd ^ 7)⁻¹ * Jt hN hd 1 * Jt hN hd 3 ^ 2 * Jt hN hd 4 + (1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 6 * Jt hN hd 8 ^ 2 * Jt hN hd 9 + (-1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 5 * Jt hN hd 9 ^ 2 * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - (-1))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (7 + 10)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (7 - 10)) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 10)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 10)) 1 = -((Qt hd ^ 12)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 (-1) (-12) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (7 + (-1))) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (7 - (-1))) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 10)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 10)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 7)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 7)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := -1) (u := 7) (v := 10) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((7 : ℤ) - (-1)) = ((8 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_m1_8_10 :
    (-1 : L) * (Qt hd ^ 6)⁻¹ * Jt hN hd 1 * Jt hN hd 2 * Jt hN hd 3 ^ 2 + (1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 7 * Jt hN hd 8 * Jt hN hd 9 ^ 2 + (-1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 6 * Jt hN hd 9 * Jt hN hd 10 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - (-1))) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (8 + 10)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (8 - 10)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 10)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 10)) 1 = -((Qt hd ^ 12)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 (-1) (-12) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (8 + (-1))) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (8 - (-1))) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * ((-1) + 10)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * ((-1) - 10)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 8)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 8)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := -1) (u := 8) (v := 10) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((8 : ℤ) - (-1)) = ((9 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_0_3_9 :
    (-1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 2 ^ 2 * Jt hN hd 6 * Jt hN hd 9 + (1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 3 ^ 2 * Jt hN hd 7 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 1 * Jt hN hd 5 * Jt hN hd 9 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + 0)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - 0)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (3 + 9)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (3 - 9)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 9)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 9)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (3 + 0)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (3 - 0)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 9)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 9)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 3)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 3)) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := 0) (u := 3) (v := 9) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((3 : ℤ) - 0) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_0_4_5 :
    (-1 : L) * (Qt hd ^ 5)⁻¹ * Jt hN hd 1 * Jt hN hd 2 ^ 2 * Jt hN hd 9 + (1 : L) * (Qt hd ^ 7)⁻¹ * Jt hN hd 3 * Jt hN hd 4 ^ 2 * Jt hN hd 7 + (-1 : L) * (Qt hd ^ 7)⁻¹ * Jt hN hd 2 * Jt hN hd 5 ^ 2 * Jt hN hd 6 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + 0)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - 0)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (4 + 5)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (4 - 5)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 5)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 5)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (4 + 0)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (4 - 0)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 5)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 5)) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 4)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 4)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := 0) (u := 4) (v := 5) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((4 : ℤ) - 0) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_0_4_9 :
    (-1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 2 ^ 2 * Jt hN hd 5 * Jt hN hd 8 + (1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 4 ^ 2 * Jt hN hd 7 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 2 * Jt hN hd 6 * Jt hN hd 9 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + 0)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - 0)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (4 + 9)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (4 - 9)) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 9)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 9)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (4 + 0)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (4 - 0)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 9)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 9)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 4)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 4)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := 0) (u := 4) (v := 9) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((4 : ℤ) - 0) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_0_4_10 :
    (-1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 2 ^ 2 * Jt hN hd 6 * Jt hN hd 7 + (1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 4 ^ 2 * Jt hN hd 8 * Jt hN hd 9 + (-1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 2 * Jt hN hd 6 * Jt hN hd 10 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + 0)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - 0)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (4 + 10)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (4 - 10)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 10)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 10)) 1 = -((Qt hd ^ 12)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 (-1) (-12) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (4 + 0)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (4 - 0)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 10)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 10)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 4)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 4)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := 0) (u := 4) (v := 10) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((4 : ℤ) - 0) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_0_5_10 :
    (-1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 2 ^ 2 * Jt hN hd 5 * Jt hN hd 6 + (1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 5 ^ 2 * Jt hN hd 8 * Jt hN hd 9 + (-1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 3 * Jt hN hd 7 * Jt hN hd 10 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + 0)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - 0)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (5 + 10)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (5 - 10)) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 10)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 10)) 1 = -((Qt hd ^ 12)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 (-1) (-12) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (5 + 0)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (5 - 0)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 10)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 10)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 5)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 5)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := 0) (u := 5) (v := 10) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((5 : ℤ) - 0) = ((5 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m2_0_6_10 :
    (-1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 2 ^ 2 * Jt hN hd 4 * Jt hN hd 5 + (1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 6 ^ 2 * Jt hN hd 8 * Jt hN hd 9 + (-1 : L) * (Qt hd ^ 12)⁻¹ * Jt hN hd 4 * Jt hN hd 8 * Jt hN hd 10 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-2) + 0)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-2) - 0)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (6 + 10)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (6 - 10)) 1 = -((Qt hd ^ 4)⁻¹ * Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-2) + 10)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-2) - 10)) 1 = -((Qt hd ^ 12)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 (-1) (-12) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (6 + 0)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (6 - 0)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 10)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 10)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-2) + 6)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-2) - 6)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -2) (y := 0) (u := 6) (v := 10) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((6 : ℤ) - 0) = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m1_0_2_4 :
    (-1 : L) * (Qt hd ^ 4)⁻¹ * Jt hN hd 1 ^ 2 * Jt hN hd 2 * Jt hN hd 6 + (1 : L) * (Qt hd ^ 5)⁻¹ * Jt hN hd 2 ^ 2 * Jt hN hd 3 * Jt hN hd 5 + (-1 : L) * (Qt hd ^ 5)⁻¹ * Jt hN hd 1 * Jt hN hd 3 * Jt hN hd 4 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-1) + 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-1) - 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (2 + 4)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (2 - 4)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-1) + 4)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-1) - 4)) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (2 + 0)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (2 - 0)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 4)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 4)) 1 = -((Qt hd ^ 4)⁻¹ * Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-1) + 2)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-1) - 2)) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -1) (y := 0) (u := 2) (v := 4) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((2 : ℤ) - 0) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m1_0_2_7 :
    (-1 : L) * (Qt hd ^ 7)⁻¹ * Jt hN hd 1 ^ 2 * Jt hN hd 5 * Jt hN hd 9 + (1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 2 ^ 2 * Jt hN hd 6 * Jt hN hd 8 + (-1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 1 * Jt hN hd 3 * Jt hN hd 7 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-1) + 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-1) - 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (2 + 7)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (2 - 7)) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-1) + 7)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-1) - 7)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (2 + 0)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (2 - 0)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 7)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 7)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-1) + 2)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-1) - 2)) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -1) (y := 0) (u := 2) (v := 7) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((2 : ℤ) - 0) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m1_0_2_8 :
    (-1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 1 ^ 2 * Jt hN hd 6 * Jt hN hd 10 + (1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 2 ^ 2 * Jt hN hd 7 * Jt hN hd 9 + (-1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 1 * Jt hN hd 3 * Jt hN hd 8 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-1) + 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-1) - 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (2 + 8)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (2 - 8)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-1) + 8)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-1) - 8)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (2 + 0)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (2 - 0)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 8)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 8)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-1) + 2)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-1) - 2)) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -1) (y := 0) (u := 2) (v := 8) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((2 : ℤ) - 0) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m1_0_2_10 :
    (-1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 1 ^ 2 * Jt hN hd 8 * Jt hN hd 9 + (1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 2 ^ 2 * Jt hN hd 9 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 1 * Jt hN hd 3 * Jt hN hd 10 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-1) + 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-1) - 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (2 + 10)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (2 - 10)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-1) + 10)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-1) - 10)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (2 + 0)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (2 - 0)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 10)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 10)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-1) + 2)) 1 = (Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 1 0 (0) 1 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-1) - 2)) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -1) (y := 0) (u := 2) (v := 10) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((2 : ℤ) - 0) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m1_0_3_6 :
    (-1 : L) * (Qt hd ^ 5)⁻¹ * Jt hN hd 1 ^ 2 * Jt hN hd 3 * Jt hN hd 9 + (1 : L) * (Qt hd ^ 7)⁻¹ * Jt hN hd 3 ^ 2 * Jt hN hd 5 * Jt hN hd 7 + (-1 : L) * (Qt hd ^ 7)⁻¹ * Jt hN hd 2 * Jt hN hd 4 * Jt hN hd 6 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-1) + 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-1) - 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (3 + 6)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (3 - 6)) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-1) + 6)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-1) - 6)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (3 + 0)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (3 - 0)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 6)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 6)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-1) + 3)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-1) - 3)) 1 = -((Qt hd ^ 4)⁻¹ * Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -1) (y := 0) (u := 3) (v := 6) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((3 : ℤ) - 0) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m1_0_3_7 :
    (-1 : L) * (Qt hd ^ 6)⁻¹ * Jt hN hd 1 ^ 2 * Jt hN hd 4 * Jt hN hd 10 + (1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 3 ^ 2 * Jt hN hd 6 * Jt hN hd 8 + (-1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 2 * Jt hN hd 4 * Jt hN hd 7 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-1) + 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-1) - 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (3 + 7)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (3 - 7)) 1 = -((Qt hd ^ 4)⁻¹ * Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-1) + 7)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-1) - 7)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (3 + 0)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (3 - 0)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 7)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 7)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-1) + 3)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-1) - 3)) 1 = -((Qt hd ^ 4)⁻¹ * Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -1) (y := 0) (u := 3) (v := 7) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((3 : ℤ) - 0) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m1_0_3_10 :
    (-1 : L) * (Qt hd ^ 9)⁻¹ * Jt hN hd 1 ^ 2 * Jt hN hd 7 * Jt hN hd 8 + (1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 3 ^ 2 * Jt hN hd 9 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 2 * Jt hN hd 4 * Jt hN hd 10 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-1) + 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-1) - 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (3 + 10)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (3 - 10)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-1) + 10)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-1) - 10)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (3 + 0)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (3 - 0)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 10)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 10)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-1) + 3)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-1) - 3)) 1 = -((Qt hd ^ 4)⁻¹ * Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -1) (y := 0) (u := 3) (v := 10) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((3 : ℤ) - 0) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m1_0_4_9 :
    (-1 : L) * (Qt hd ^ 7)⁻¹ * Jt hN hd 1 ^ 2 * Jt hN hd 5 * Jt hN hd 8 + (1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 4 ^ 2 * Jt hN hd 8 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 3 * Jt hN hd 5 * Jt hN hd 9 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-1) + 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-1) - 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (4 + 9)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (4 - 9)) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-1) + 9)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-1) - 9)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (4 + 0)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (4 - 0)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 9)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 9)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-1) + 4)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-1) - 4)) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -1) (y := 0) (u := 4) (v := 9) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((4 : ℤ) - 0) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m1_0_4_10 :
    (-1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 1 ^ 2 * Jt hN hd 6 * Jt hN hd 7 + (1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 4 ^ 2 * Jt hN hd 9 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 3 * Jt hN hd 5 * Jt hN hd 10 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-1) + 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-1) - 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (4 + 10)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (4 - 10)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-1) + 10)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-1) - 10)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (4 + 0)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (4 - 0)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 10)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 10)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-1) + 4)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 3 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-1) - 4)) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -1) (y := 0) (u := 4) (v := 10) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((4 : ℤ) - 0) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m1_0_5_7 :
    (-1 : L) * (Qt hd ^ 4)⁻¹ * Jt hN hd 1 ^ 2 * Jt hN hd 2 * Jt hN hd 9 + (1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 5 ^ 2 * Jt hN hd 6 * Jt hN hd 8 + (-1 : L) * (Qt hd ^ 8)⁻¹ * Jt hN hd 4 * Jt hN hd 6 * Jt hN hd 7 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-1) + 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-1) - 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (5 + 7)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (5 - 7)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-1) + 7)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-1) - 7)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (5 + 0)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (5 - 0)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 7)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 7)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-1) + 5)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-1) - 5)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -1) (y := 0) (u := 5) (v := 7) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((5 : ℤ) - 0) = ((5 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m1_0_5_10 :
    (-1 : L) * (Qt hd ^ 7)⁻¹ * Jt hN hd 1 ^ 2 * Jt hN hd 5 * Jt hN hd 6 + (1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 5 ^ 2 * Jt hN hd 9 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 4 * Jt hN hd 6 * Jt hN hd 10 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-1) + 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-1) - 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (5 + 10)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (5 - 10)) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-1) + 10)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-1) - 10)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (5 + 0)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (5 - 0)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 10)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 10)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-1) + 5)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-1) - 5)) 1 = -((Qt hd ^ 6)⁻¹ * Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 15 (-1) (-6) 6 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -1) (y := 0) (u := 5) (v := 10) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((5 : ℤ) - 0) = ((5 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m1_0_6_10 :
    (-1 : L) * (Qt hd ^ 6)⁻¹ * Jt hN hd 1 ^ 2 * Jt hN hd 4 * Jt hN hd 5 + (1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 6 ^ 2 * Jt hN hd 9 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 5 * Jt hN hd 7 * Jt hN hd 10 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-1) + 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-1) - 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (6 + 10)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (6 - 10)) 1 = -((Qt hd ^ 4)⁻¹ * Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 (-1) (-4) 4 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-1) + 10)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-1) - 10)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (6 + 0)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (6 - 0)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 10)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 10)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-1) + 6)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-1) - 6)) 1 = -((Qt hd ^ 7)⁻¹ * Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 (-1) (-7) 7 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -1) (y := 0) (u := 6) (v := 10) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((6 : ℤ) - 0) = ((6 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m1_0_7_9 :
    (-1 : L) * (Qt hd ^ 4)⁻¹ * Jt hN hd 1 ^ 2 * Jt hN hd 2 * Jt hN hd 5 + (1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 7 ^ 2 * Jt hN hd 8 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 10)⁻¹ * Jt hN hd 6 * Jt hN hd 8 * Jt hN hd 9 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-1) + 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-1) - 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (7 + 9)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (7 - 9)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-1) + 9)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-1) - 9)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (7 + 0)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (7 - 0)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 9)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 9)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-1) + 7)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-1) - 7)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -1) (y := 0) (u := 7) (v := 9) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((7 : ℤ) - 0) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m1_0_7_10 :
    (-1 : L) * (Qt hd ^ 5)⁻¹ * Jt hN hd 1 ^ 2 * Jt hN hd 3 * Jt hN hd 4 + (1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 7 ^ 2 * Jt hN hd 9 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 6 * Jt hN hd 8 * Jt hN hd 10 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-1) + 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-1) - 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (7 + 10)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 17 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (7 - 10)) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-1) + 10)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-1) - 10)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (7 + 0)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (7 - 0)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 10)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 10)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-1) + 7)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-1) - 7)) 1 = -((Qt hd ^ 8)⁻¹ * Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 13 (-1) (-8) 8 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -1) (y := 0) (u := 7) (v := 10) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((7 : ℤ) - 0) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem W_m1_0_8_10 :
    (-1 : L) * (Qt hd ^ 4)⁻¹ * Jt hN hd 1 ^ 2 * Jt hN hd 2 * Jt hN hd 3 + (1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 8 ^ 2 * Jt hN hd 9 * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 11)⁻¹ * Jt hN hd 7 * Jt hN hd 9 * Jt hN hd 10 ^ 2 = 0 := by
  have hQ := Qt_ne hd
  have e0 : θ hN (↑d * ((-1) + 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-1) - 0)) 1 = -((Qt hd ^ 1)⁻¹ * Jt hN hd 1) := by
    rw [Jt_norm hN hd _ 20 (-1) (-1) 1 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (8 + 10)) 1 = (Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 0 (0) 3 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (8 - 10)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-1) + 10)) 1 = (Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 0 (0) 9 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-1) - 10)) 1 = -((Qt hd ^ 11)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 (-1) (-11) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e6 : θ hN (↑d * (8 + 0)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e7 : θ hN (↑d * (8 - 0)) 1 = (Jt hN hd 8) := by
    rw [Jt_norm hN hd _ 8 0 (0) 8 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e8 : θ hN (↑d * (0 + 10)) 1 = (Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 10 0 (0) 10 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e9 : θ hN (↑d * (0 - 10)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e10 : θ hN (↑d * ((-1) + 8)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-1) - 8)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w := weierQ hN hd (x := -1) (y := 0) (u := 8) (v := 10) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at w
  rw [show ((8 : ℤ) - 0) = ((8 : ℕ) : ℤ) by norm_num, zpow_natCast] at w
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) w
  field_simp
  ring

theorem core7_0_0 :
    (-1 : L) * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 + (-2 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 8 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 1 * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ + (2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 2)⁻¹ * Jt hN hd 10 + (2 : L) * Qt hd ^ 2 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 8 ^ 1)⁻¹ + (3 : L) * Qt hd ^ 1 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 9 + (2 : L) * Qt hd ^ 1 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 6 * Jt hN hd 7 * (Jt hN hd 10 ^ 1)⁻¹ + (-3 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 + (3 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ + (-2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (3 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_6_8 hN hd + (-2 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_0_4_6 hN hd + (2 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_4_10 hN hd + (-2 : L) * Qt hd ^ 12 * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_5_9 hN hd + (-3 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (-3 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * W_m1_0_2_7 hN hd + (2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m1_0_2_10 hN hd + (2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m1_7_8 hN hd + (-2 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_0_6_10 hN hd + (2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_6_10 hN hd + (-2 : L) * Qt hd ^ 12 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m3_m1_7_8 hN hd
  field_simp
  ring

theorem core7_0_1 :
    (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 2)⁻¹ * Jt hN hd 10 + (1 : L) * Qt hd ^ 2 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 8 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 9 + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 8 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 6 * Jt hN hd 7 * (Jt hN hd 10 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_0_4_6 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_4_10 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_5_9 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_6_8 hN hd + (-1 : L) * Qt hd ^ 13 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m2_5_8 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_0_4_6 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m2_0_4_9 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m1_0_4_9 hN hd + (-1 : L) * Qt hd ^ 9 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_4_6 hN hd
  field_simp
  ring

theorem core7_0_2 :
    (2 : L) * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 9 + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (1 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m1_0_2_8 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 2)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m1_0_8_10 hN hd + (-1 : L) * Qt hd ^ 13 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 2)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_8_10 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_6_8 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (1 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * W_m1_0_2_7 hN hd
  field_simp
  ring

theorem core7_0_3 :
    (-1 : L) * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 8 ^ 1)⁻¹ + (2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 2)⁻¹ * Jt hN hd 10 + (2 : L) * Qt hd ^ 2 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 8 ^ 1)⁻¹ + (2 : L) * Qt hd ^ 1 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 9 + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 + (2 : L) * Qt hd ^ 1 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 6 * Jt hN hd 7 * (Jt hN hd 10 ^ 1)⁻¹ + (-2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 + (2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ + (-2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-2 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_0_4_6 hN hd + (2 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_4_10 hN hd + (-2 : L) * Qt hd ^ 12 * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_5_9 hN hd + (-1 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m1_0_2_8 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 2)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m1_0_8_10 hN hd + (1 : L) * Qt hd ^ 13 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 2)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_8_10 hN hd + (2 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m1_0_4_9 hN hd + (-2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m2_0_4_9 hN hd + (2 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_0_4_6 hN hd + (2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (-2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (-2 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * W_m1_0_2_7 hN hd + (2 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_6_8 hN hd + (-2 : L) * Qt hd ^ 9 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_4_6 hN hd
  field_simp
  ring

theorem core7_0_4 :
    (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 2)⁻¹ * Jt hN hd 10 + (1 : L) * Qt hd ^ 2 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 8 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 9 + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 8 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 6 * Jt hN hd 7 * (Jt hN hd 10 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_0_4_6 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_4_10 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_5_9 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_6_8 hN hd + (-1 : L) * Qt hd ^ 13 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m2_5_8 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_0_4_6 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m2_0_4_9 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m1_0_4_9 hN hd + (-1 : L) * Qt hd ^ 9 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_4_6 hN hd
  field_simp
  ring

theorem core7_0_5 :
    (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 2)⁻¹ * Jt hN hd 10 + (1 : L) * Qt hd ^ 2 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 8 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 9 + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 8 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 6 * Jt hN hd 7 * (Jt hN hd 10 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_0_4_6 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_4_10 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_5_9 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_6_8 hN hd + (-1 : L) * Qt hd ^ 13 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m2_5_8 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_0_4_6 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m2_0_4_9 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m1_0_4_9 hN hd + (-1 : L) * Qt hd ^ 9 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_4_6 hN hd
  field_simp
  ring

theorem core7_1_0 :
    (1 : L) * (Jt hN hd 2 ^ 2)⁻¹ * Jt hN hd 4 + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 + (-1 : L) * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 2 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 10 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 5 * Jt hN hd 7 * (Jt hN hd 8 ^ 2)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 2 * Jt hN hd 1 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * Jt hN hd 7 * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 2)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_3_8 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 8 ^ 2)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 2)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m1_6_9 hN hd + (-1 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m1_0_3_6 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_0_3_9 hN hd + (1 : L) * Qt hd ^ 9 * (Jt hN hd 2 ^ 2)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_5_7 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 2 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m2_6_7 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd
  field_simp
  ring

theorem core7_1_1 :
    (1 : L) * (Jt hN hd 2 ^ 2)⁻¹ * Jt hN hd 4 + (1 : L) * Qt hd ^ 3 * Jt hN hd 3 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 2 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 5 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (1 : L) * Qt hd ^ 15 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m4_m1_5_10 hN hd + (-1 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 2)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * W_m3_m1_4_5 hN hd + (-1 : L) * Qt hd ^ 13 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * W_m4_m1_6_8 hN hd
  field_simp
  ring

theorem core7_1_2 :
    (1 : L) * (Jt hN hd 2 ^ 2)⁻¹ * Jt hN hd 4 + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 + (1 : L) * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 2 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 10 ^ 1)⁻¹ + (2 : L) * Qt hd ^ 3 * Jt hN hd 3 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 5 * Jt hN hd 7 * (Jt hN hd 8 ^ 2)⁻¹ + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 9 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 2 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 5 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ + (-2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 + (1 : L) * Qt hd ^ 2 * Jt hN hd 1 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * Jt hN hd 7 * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 2)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_3_8 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 8 ^ 2)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 2)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m1_6_9 hN hd + (1 : L) * Qt hd ^ 15 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m4_m1_5_10 hN hd + (-1 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 2)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * W_m3_m1_4_5 hN hd + (-1 : L) * Qt hd ^ 13 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * W_m4_m1_6_8 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m2_6_7 hN hd + (-1 : L) * Qt hd ^ 13 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m3_m2_4_8 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (-1 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_5_7 hN hd + (1 : L) * Qt hd ^ 15 * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_6_8 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ * W_m4_m1_6_8 hN hd + (-1 : L) * Qt hd ^ 13 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_0_4_10 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_4_10 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * W_m2_m1_5_9 hN hd
  field_simp
  ring

theorem core7_1_3 :
    (2 : L) * (Jt hN hd 2 ^ 2)⁻¹ * Jt hN hd 4 + (2 : L) * Qt hd ^ 3 * Jt hN hd 3 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 2 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 5 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ + (2 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 9 ^ 1)⁻¹ + (-2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-2 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 2)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * W_m3_m1_4_5 hN hd + (-2 : L) * Qt hd ^ 13 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * W_m4_m1_6_8 hN hd + (2 : L) * Qt hd ^ 15 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m4_m1_5_10 hN hd
  field_simp
  ring

theorem core7_1_5 :
    (2 : L) * (Jt hN hd 2 ^ 2)⁻¹ * Jt hN hd 4 + (2 : L) * Qt hd ^ 3 * Jt hN hd 3 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 2 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 5 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ + (2 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 9 ^ 1)⁻¹ + (-2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-2 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 2)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * W_m3_m1_4_5 hN hd + (-2 : L) * Qt hd ^ 13 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * W_m4_m1_6_8 hN hd + (2 : L) * Qt hd ^ 15 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m4_m1_5_10 hN hd
  field_simp
  ring

theorem core7_2_0 :
    (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 + (2 : L) * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ + (2 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 8 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 10 + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * Jt hN hd 3 * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 10 + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 5 * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 + (-1 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 + (-1 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 + (2 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 ^ 2 * (Jt hN hd 10 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * Jt hN hd 1 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 ^ 2 * Jt hN hd 7 * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 ^ 2 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_0_4_10 hN hd + (1 : L) * Qt hd ^ 13 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m1_6_9 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m1_7_8 hN hd + (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m1_0_8_10 hN hd + (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (1 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m1_0_2_7 hN hd + (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_3_9 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m1_0_7_9 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_0_5_10 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m2_6_7 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m4_m1_6_8 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m4_m1_5_7 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 3 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (-2 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m2_5_7 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m3_5_7 hN hd + (1 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m1_4_5 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_0_4_9 hN hd + (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 2)⁻¹ * W_m3_m2_6_8 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 2)⁻¹ * W_m4_m2_6_7 hN hd + (1 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m3_m2_4_6 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_0_4_9 hN hd + (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_5_7 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_5_10 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m3_m2_6_8 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_3_9 hN hd + (1 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m1_0_2_8 hN hd + (-1 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 * W_m3_m2_5_7 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 2)⁻¹ * W_m2_m1_8_10 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 9 ^ 2)⁻¹ * W_m2_m1_3_8 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 9 ^ 2)⁻¹ * W_m4_m1_5_7 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 ^ 2 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 2)⁻¹ * W_m3_m1_7_8 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m2_5_7 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_3_8 hN hd + (-1 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_3_5 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_0_4_6 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m3_m2_4_8 hN hd + (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_4_10 hN hd
  field_simp
  ring

theorem core7_2_1 :
    (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 + (1 : L) * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 8 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 10 + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * Jt hN hd 3 * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 10 + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 + (-1 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 ^ 2 * (Jt hN hd 10 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 ^ 2 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m4_m2_5_8 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (-1 : L) * Qt hd ^ 14 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * W_m3_m2_4_10 hN hd + (1 : L) * Qt hd ^ 14 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_5_9 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m3_5_7 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * W_m5_m1_6_7 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * W_m2_m1_5_9 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_7_10 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m2_5_7 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd
  field_simp
  ring

theorem core7_2_2 :
    (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 8 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 10 + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * Jt hN hd 3 * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 10 + (1 : L) * Qt hd ^ 2 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ + (1 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 5 * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 + (-1 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 ^ 2 * (Jt hN hd 10 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * Jt hN hd 1 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 ^ 2 * Jt hN hd 7 * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m4_m1_6_8 hN hd + (-1 : L) * Qt hd ^ 13 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_3_9 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ * W_m4_m1_6_8 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (-1 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_3_5 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 2)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m2_7_8 hN hd + (1 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 ^ 2 * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_4_6 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_6_9 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m1_6_9 hN hd + (1 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * W_m2_m1_5_8 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_5_7 hN hd + (1 : L) * Qt hd ^ 13 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_7_9 hN hd + (-1 : L) * Qt hd ^ 16 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_5_10 hN hd + (1 : L) * Qt hd ^ 13 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_7_10 hN hd + (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_5_7 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m5_m1_6_7 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_8_10 hN hd + (1 : L) * Qt hd ^ 6 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * W_m2_m1_3_5 hN hd + (-1 : L) * Qt hd ^ 14 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_5_9 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_0_4_10 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_4_10 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m1_4_7 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m3_m2_4_8 hN hd + (1 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_6_8 hN hd + (1 : L) * Qt hd ^ 6 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * W_m2_0_4_5 hN hd
  field_simp
  ring

theorem core7_2_3 :
    (2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 8 ^ 1)⁻¹ + (2 : L) * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ + (-2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 10 + (-2 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * Jt hN hd 3 * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 2 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 2 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 + (-2 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ + (2 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 10 + (3 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ + (-2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 ^ 2 * (Jt hN hd 10 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 ^ 2 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (2 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m3_5_7 hN hd + (-2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * W_m5_m1_6_7 hN hd + (-2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_7_10 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_3_9 hN hd + (-1 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m1_0_3_7 hN hd + (2 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m1_5_6 hN hd + (-2 : L) * Qt hd ^ 15 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m2_4_10 hN hd + (2 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * W_m2_m1_5_9 hN hd + (2 : L) * Qt hd ^ 14 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m2_5_10 hN hd + (2 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 2)⁻¹ * W_m5_m1_6_7 hN hd + (-2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 2)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m2_6_7 hN hd + (2 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 3 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (-2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m2_5_7 hN hd + (2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (-3 : L) * Qt hd ^ 13 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_3_10 hN hd + (3 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_4_10 hN hd + (-3 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_3_9 hN hd
  field_simp
  ring

theorem core7_2_4 :
    (-2 : L) * Qt hd ^ 2 * (Jt hN hd 7 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 8 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 2 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 ^ 2 * (Jt hN hd 10 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * Jt hN hd 1 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 ^ 2 * Jt hN hd 7 * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_4_8 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_3_8 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m2_6_7 hN hd + (1 : L) * Qt hd ^ 13 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m5_m1_6_7 hN hd + (-1 : L) * Qt hd ^ 14 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m1_4_10 hN hd + (-1 : L) * Qt hd ^ 13 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m1_4_7 hN hd + (1 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m1_4_5 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd
  field_simp
  ring

theorem core7_2_5 :
    (2 : L) * Qt hd ^ 2 * (Jt hN hd 7 ^ 1)⁻¹ + (2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 + (1 : L) * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 8 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * Jt hN hd 3 * (Jt hN hd 9 ^ 1)⁻¹ + (-2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 10 + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 + (-2 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ + (2 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 10 + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 ^ 2 * (Jt hN hd 10 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * Jt hN hd 1 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 ^ 2 * Jt hN hd 7 * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 ^ 2 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-1 : L) * Qt hd ^ 6 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m1_0_2_4 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_5_7 hN hd + (1 : L) * Qt hd ^ 7 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * W_m2_m1_3_5 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m1_4_7 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m2_5_6 hN hd + (-1 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_3_7 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_4_10 hN hd + (1 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m1_4_7 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * W_m5_m1_6_7 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * W_m2_m1_5_9 hN hd + (-2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m2_5_7 hN hd + (2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m3_5_7 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_7_10 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (2 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_4_10 hN hd + (-2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd
  field_simp
  ring

theorem core7_3_0 :
    (-2 : L) * (Jt hN hd 1 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 2 * (Jt hN hd 8 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * Jt hN hd 6 * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 4 * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-1 : L) * Qt hd ^ 13 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m4_m1_5_9 hN hd + (1 : L) * Qt hd ^ 14 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m4_m1_5_10 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 2)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_6_8 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (1 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m1_0_2_7 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m1_0_5_10 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (1 : L) * Qt hd ^ 13 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m2_6_7 hN hd
  field_simp
  ring

theorem core7_3_1 :
    (-2 : L) * (Jt hN hd 1 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 2 * (Jt hN hd 8 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * Jt hN hd 6 * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 4 * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-1 : L) * Qt hd ^ 13 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m4_m1_5_9 hN hd + (1 : L) * Qt hd ^ 14 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m4_m1_5_10 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 2)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_6_8 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (1 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m1_0_2_7 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m1_0_5_10 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (1 : L) * Qt hd ^ 13 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m2_6_7 hN hd
  field_simp
  ring

theorem core7_3_2 :
    (-2 : L) * (Jt hN hd 1 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 2 * (Jt hN hd 8 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * Jt hN hd 6 * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 4 * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-1 : L) * Qt hd ^ 13 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m4_m1_5_9 hN hd + (1 : L) * Qt hd ^ 14 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m4_m1_5_10 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 2)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_6_8 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (1 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m1_0_2_7 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m1_0_5_10 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (1 : L) * Qt hd ^ 13 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m2_6_7 hN hd
  field_simp
  ring

theorem core7_3_3 :
    (-4 : L) * (Jt hN hd 1 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 2 * (Jt hN hd 8 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * Jt hN hd 6 * (Jt hN hd 9 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 1 * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * Jt hN hd 7 * (Jt hN hd 10 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 9 ^ 1)⁻¹ + (2 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ + (-2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 4 * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ + (2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 + (2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_4_10 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (-2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m1_0_5_10 hN hd + (2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (2 : L) * Qt hd ^ 13 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m2_6_7 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_5_10 hN hd + (2 : L) * Qt hd ^ 7 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m1_0_3_6 hN hd + (2 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m1_6_9 hN hd + (-2 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 2)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_0_5_10 hN hd + (-2 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m2_5_7 hN hd + (2 : L) * Qt hd ^ 13 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (2 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_3_8 hN hd + (2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_5_7 hN hd + (-2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_5_7 hN hd + (-2 : L) * Qt hd ^ 13 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_5_7 hN hd + (-2 : L) * Qt hd ^ 12 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd
  field_simp
  ring

theorem core7_3_4 :
    (1 : L) * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 10 ^ 1)⁻¹ + (2 : L) * Qt hd ^ 1 * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * Jt hN hd 7 * (Jt hN hd 10 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 9 ^ 1)⁻¹ + (-2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 + (2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 4 * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_4_10 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_5_10 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 3)⁻¹ * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_0_6_9 hN hd + (-1 : L) * Qt hd ^ 14 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 3)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * W_m4_m2_5_10 hN hd + (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 2)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_5_8 hN hd + (2 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m5_m1_6_7 hN hd + (-2 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m1_0_2_8 hN hd + (2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_5_9 hN hd + (-2 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_4_9 hN hd
  field_simp
  ring

theorem core7_3_5 :
    (-4 : L) * (Jt hN hd 1 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 2 * (Jt hN hd 8 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 10 ^ 1)⁻¹ + (-4 : L) * Qt hd ^ 1 * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ + (3 : L) * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * Jt hN hd 6 * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 9 ^ 1)⁻¹ + (-4 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 4 * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ + (4 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 + (3 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-1 : L) * Qt hd ^ 12 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 3)⁻¹ * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_0_6_9 hN hd + (1 : L) * Qt hd ^ 14 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 3)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * W_m4_m2_5_10 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 2)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_5_8 hN hd + (2 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_0_4_5 hN hd + (-2 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m2_6_7 hN hd + (-2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m1_0_5_10 hN hd + (2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (2 : L) * Qt hd ^ 13 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m2_6_7 hN hd + (-4 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m5_m1_6_7 hN hd + (4 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m1_0_2_8 hN hd + (4 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_4_9 hN hd + (-4 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * Jt hN hd 8 * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_5_9 hN hd + (2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (-2 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_5_7 hN hd + (3 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd
  field_simp
  ring

theorem core7_4_0 :
    (1 : L) * Qt hd ^ 1 * (Jt hN hd 4 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 2 * (Jt hN hd 10 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 3 * Jt hN hd 3 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 + (1 : L) * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 7 * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * (Jt hN hd 6 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-1 : L) * Qt hd ^ 12 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_4_10 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * Jt hN hd 7 * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_5_10 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 4 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_4_9 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 2)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_3_9 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 4 ^ 2)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_5_10 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m5_m1_6_7 hN hd + (1 : L) * Qt hd ^ 5 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * W_m1_0_2_4 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd
  field_simp
  ring

theorem core7_4_2 :
    (-1 : L) * Qt hd ^ 1 * (Jt hN hd 4 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 2 * (Jt hN hd 10 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 3 * Jt hN hd 3 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * (Jt hN hd 6 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 + (-1 : L) * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 7 * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (1 : L) * Qt hd ^ 12 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_4_10 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * Jt hN hd 7 * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_5_10 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 4 ^ 2)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_4_9 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 2)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_3_9 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 4 ^ 2)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_5_10 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 2)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m5_m1_6_7 hN hd + (-1 : L) * Qt hd ^ 5 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * W_m1_0_2_4 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd
  field_simp
  ring

theorem core7_4_4 :
    (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ + (2 : L) * Qt hd ^ 3 * Jt hN hd 3 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 7 * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ + (-2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 + (-2 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ + (2 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 + (1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-1 : L) * Qt hd ^ 14 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 3)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m2_5_10 hN hd + (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 2)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_8 hN hd + (-2 : L) * Qt hd ^ 13 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_6_8 hN hd + (2 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m5_m1_6_7 hN hd + (-2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (2 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (-2 : L) * Qt hd ^ 15 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m5_m1_6_7 hN hd + (1 : L) * Qt hd ^ 12 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 3)⁻¹ * Jt hN hd 7 * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_0_6_9 hN hd
  field_simp
  ring

theorem core7_4_5 :
    (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 3 * Jt hN hd 3 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 7 * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ + (2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 + (-2 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 + (2 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (1 : L) * Qt hd ^ 14 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 3)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m2_5_10 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 2)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_8 hN hd + (-1 : L) * Qt hd ^ 12 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 3)⁻¹ * Jt hN hd 7 * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_0_6_9 hN hd + (2 : L) * Qt hd ^ 13 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_6_8 hN hd + (-2 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m5_m1_6_7 hN hd + (2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (-2 : L) * Qt hd ^ 12 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (2 : L) * Qt hd ^ 15 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m5_m1_6_7 hN hd
  field_simp
  ring

theorem core7_5_0 :
    (1 : L) * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 10 + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ + (2 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 7 + (3 : L) * Qt hd ^ 2 * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ + (-3 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ + (2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 + (-3 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 6 ^ 2 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_5_7 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 2)⁻¹ * W_m4_m2_6_7 hN hd + (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_0_3_9 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_4_9 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (-1 : L) * Qt hd ^ 7 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 * W_m1_0_2_7 hN hd + (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (3 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m5_m1_6_7 hN hd + (-3 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (-3 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd
  field_simp
  ring

theorem core7_5_1 :
    (1 : L) * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 10 + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ + (1 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 7 + (2 : L) * Qt hd ^ 2 * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ + (-2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 + (-2 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 6 ^ 2 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_5_7 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 2)⁻¹ * W_m4_m2_6_7 hN hd + (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_0_3_9 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_4_9 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (-1 : L) * Qt hd ^ 7 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 * W_m1_0_2_7 hN hd + (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m5_m1_6_7 hN hd + (-2 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (-2 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd
  field_simp
  ring

theorem core7_5_2 :
    (1 : L) * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 10 + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 2 * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 + (-1 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 6 ^ 2 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m3_5_7 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m5_m1_6_7 hN hd + (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (-1 : L) * Qt hd ^ 7 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 * W_m1_0_2_7 hN hd + (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd
  field_simp
  ring

theorem core7_5_3 :
    (-2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ + (2 : L) * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 10 + (2 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 7 + (4 : L) * Qt hd ^ 2 * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ + (-4 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ + (2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ + (2 : L) * Qt hd ^ 1 * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ + (2 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 + (-4 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 6 ^ 2 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 + (2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (2 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_5_7 hN hd + (-2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 2)⁻¹ * W_m4_m2_6_7 hN hd + (-2 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_0_3_9 hN hd + (2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_4_9 hN hd + (2 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (-2 : L) * Qt hd ^ 7 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 * W_m1_0_2_7 hN hd + (-2 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (4 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m5_m1_6_7 hN hd + (-4 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (-4 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd
  field_simp
  ring

theorem core7_5_4 :
    (1 : L) * Qt hd ^ 2 * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 7 + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 6 ^ 2 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m5_m1_6_7 hN hd + (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (-1 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd
  field_simp
  ring

theorem core7_5_5 :
    (-2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 5 ^ 1)⁻¹ + (2 : L) * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 10 + (1 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 7 + (3 : L) * Qt hd ^ 2 * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ + (-3 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ + (2 : L) * Qt hd ^ 1 * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ + (2 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 + (-3 : L) * (Qt hd ^ 1)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 6 ^ 2 * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 + (2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-2 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_0_3_9 hN hd + (2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 2 * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_4_9 hN hd + (2 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ * W_m4_m1_5_7 hN hd + (-2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 2)⁻¹ * W_m4_m2_6_7 hN hd + (2 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (-2 : L) * Qt hd ^ 7 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * Jt hN hd 10 * W_m1_0_2_7 hN hd + (-2 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (3 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m5_m1_6_7 hN hd + (-3 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (-3 : L) * Qt hd ^ 10 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd
  field_simp
  ring

theorem core7_6_0 :
    (2 : L) * (Jt hN hd 2 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 1 * (Jt hN hd 5 ^ 1)⁻¹ + (2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 7 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 1 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 9 + (-2 : L) * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ + (-2 : L) * (Qt hd ^ 2)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 10 + (2 : L) * (Qt hd ^ 2)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 + (-2 : L) * Jt hN hd 1 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * Jt hN hd 7 * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-2 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 2)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m2_5_7 hN hd + (2 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 2)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m4_m2_6_7 hN hd + (2 : L) * Qt hd ^ 9 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_0_4_6 hN hd + (-2 : L) * Qt hd ^ 11 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_4_10 hN hd + (2 : L) * Qt hd ^ 11 * Jt hN hd 1 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_5_9 hN hd + (-2 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (2 : L) * Qt hd ^ 7 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * W_m2_m1_5_7 hN hd + (2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd
  field_simp
  ring

theorem core7_6_1 :
    (1 : L) * (Jt hN hd 2 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 5 ^ 1)⁻¹ + (1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 7 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 9 + (-1 : L) * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * (Qt hd ^ 2)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 10 + (1 : L) * (Qt hd ^ 2)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 + (-1 : L) * Jt hN hd 1 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * Jt hN hd 7 * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-1 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 2)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m2_5_7 hN hd + (1 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 2)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m4_m2_6_7 hN hd + (1 : L) * Qt hd ^ 9 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_0_4_6 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_4_10 hN hd + (1 : L) * Qt hd ^ 11 * Jt hN hd 1 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_5_9 hN hd + (-1 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (1 : L) * Qt hd ^ 7 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * W_m2_m1_5_7 hN hd + (1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd
  field_simp
  ring

theorem core7_6_3 :
    (2 : L) * (Jt hN hd 2 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 1 * (Jt hN hd 5 ^ 1)⁻¹ + (2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 7 ^ 1)⁻¹ + (-2 : L) * Qt hd ^ 1 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 9 + (-2 : L) * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ + (-2 : L) * (Qt hd ^ 2)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 10 + (2 : L) * (Qt hd ^ 2)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 + (-2 : L) * Jt hN hd 1 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * Jt hN hd 7 * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-2 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 2)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m2_5_7 hN hd + (2 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 2)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m4_m2_6_7 hN hd + (2 : L) * Qt hd ^ 9 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_0_4_6 hN hd + (-2 : L) * Qt hd ^ 11 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_4_10 hN hd + (2 : L) * Qt hd ^ 11 * Jt hN hd 1 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_5_9 hN hd + (-2 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (2 : L) * Qt hd ^ 7 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * W_m2_m1_5_7 hN hd + (2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd
  field_simp
  ring

theorem core7_6_4 :
    (1 : L) * (Jt hN hd 2 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 5 ^ 1)⁻¹ + (3 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 7 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 10 ^ 1)⁻¹ + (-3 : L) * Qt hd ^ 1 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 9 + (-2 : L) * (Qt hd ^ 2)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 8 + (-2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * (Qt hd ^ 2)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 10 + (3 : L) * (Qt hd ^ 2)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 + (-2 : L) * Jt hN hd 1 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * Jt hN hd 7 * Jt hN hd 8 * (Jt hN hd 10 ^ 1)⁻¹ = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (-2 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_3_9 hN hd + (-2 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m1_0_3_7 hN hd + (2 : L) * Qt hd ^ 9 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m3_m1_5_6 hN hd + (-3 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (3 : L) * Qt hd ^ 7 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * W_m2_m1_5_7 hN hd + (3 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (1 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_6_8 hN hd + (1 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 10 ^ 1)⁻¹ * W_m1_0_3_10 hN hd + (-1 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 8 ^ 1)⁻¹ * W_m2_m1_4_9 hN hd + (1 : L) * Qt hd ^ 9 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_0_4_6 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 10 ^ 2)⁻¹ * W_m1_0_4_10 hN hd + (1 : L) * Qt hd ^ 11 * Jt hN hd 1 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 2)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * (Jt hN hd 10 ^ 2)⁻¹ * W_m2_m1_5_9 hN hd
  field_simp
  ring

theorem core7_6_5 :
    (1 : L) * (Jt hN hd 2 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 5 ^ 1)⁻¹ + (-1 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 7 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 9 + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 10 ^ 1)⁻¹ + (2 : L) * (Qt hd ^ 2)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 8 + (-2 : L) * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 6 * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ + (2 : L) * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * Jt hN hd 8 * (Jt hN hd 9 ^ 1)⁻¹ + (-1 : L) * (Qt hd ^ 2)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * Jt hN hd 10 + (-1 : L) * (Qt hd ^ 2)⁻¹ * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 8 * Jt hN hd 9 = 0 := by
  have hQ := Qt_ne hd
  have hJ1 := Jt_ne hN hd (a := 1) (by norm_num) (by norm_num)
  have hJ2 := Jt_ne hN hd (a := 2) (by norm_num) (by norm_num)
  have hJ3 := Jt_ne hN hd (a := 3) (by norm_num) (by norm_num)
  have hJ4 := Jt_ne hN hd (a := 4) (by norm_num) (by norm_num)
  have hJ5 := Jt_ne hN hd (a := 5) (by norm_num) (by norm_num)
  have hJ6 := Jt_ne hN hd (a := 6) (by norm_num) (by norm_num)
  have hJ7 := Jt_ne hN hd (a := 7) (by norm_num) (by norm_num)
  have hJ8 := Jt_ne hN hd (a := 8) (by norm_num) (by norm_num)
  have hJ9 := Jt_ne hN hd (a := 9) (by norm_num) (by norm_num)
  have hJ10 := Jt_ne hN hd (a := 10) (by norm_num) (by norm_num)
  linear_combination (norm := skip) (1 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * Jt hN hd 9 * (Jt hN hd 10 ^ 1)⁻¹ * W_m2_m1_5_9 hN hd + (-1 : L) * Qt hd ^ 7 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 3 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * W_m2_m1_5_7 hN hd + (-1 : L) * Qt hd ^ 11 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_4_8 hN hd + (1 : L) * Qt hd ^ 7 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * Jt hN hd 7 * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_3_5 hN hd + (1 : L) * Qt hd ^ 8 * (Jt hN hd 1 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m1_0_5_7 hN hd + (-1 : L) * Qt hd ^ 10 * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 2)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_m1_5_7 hN hd + (1 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * W_m3_m2_6_8 hN hd + (-1 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 2)⁻¹ * Jt hN hd 3 * (Jt hN hd 4 ^ 1)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m2_0_4_9 hN hd + (1 : L) * Qt hd ^ 9 * (Jt hN hd 1 ^ 1)⁻¹ * (Jt hN hd 2 ^ 2)⁻¹ * (Jt hN hd 5 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 8 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * W_m4_m2_6_7 hN hd
  field_simp
  ring


end Core7
end ALz
