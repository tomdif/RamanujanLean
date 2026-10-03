import RamanujanTau.ALThetaCore

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ALz
open HahnSeries
section T
variable {N : ℕ} (hN : 1 ≤ N) {d : ℕ} (hd : N = 21 * d)
include hN hd

theorem cubic_test :
    (1 : L) * Qt hd ^ 3 * Jt hN hd 3 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ + (1 : L) * Qt hd ^ 1 * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 7 * (Jt hN hd 10 ^ 1)⁻¹ + (-1 : L) * Qt hd ^ 1 * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 4 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * Jt hN hd 9 + (-1 : L) * Qt hd ^ 3 * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * Jt hN hd 4 * Jt hN hd 5 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ = 0 := by
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
  have e0 : θ hN (↑d * ((-3) + 0)) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e1 : θ hN (↑d * ((-3) - 0)) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e2 : θ hN (↑d * (7 + 9)) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e3 : θ hN (↑d * (7 - 9)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e4 : θ hN (↑d * ((-3) + 9)) 1 = (Jt hN hd 6) := by
    rw [Jt_norm hN hd _ 6 0 (0) 6 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e5 : θ hN (↑d * ((-3) - 9)) 1 = -((Qt hd ^ 12)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 (-1) (-12) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
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
  have e10 : θ hN (↑d * ((-3) + 7)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e11 : θ hN (↑d * ((-3) - 7)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e12 : θ hN (↑d * ((-4) + (-1))) 1 = -((Qt hd ^ 5)⁻¹ * Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 16 (-1) (-5) 5 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e13 : θ hN (↑d * ((-4) - (-1))) 1 = -((Qt hd ^ 3)⁻¹ * Jt hN hd 3) := by
    rw [Jt_norm hN hd _ 18 (-1) (-3) 3 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e14 : θ hN (↑d * (6 + 8)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 14 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e15 : θ hN (↑d * (6 - 8)) 1 = -((Qt hd ^ 2)⁻¹ * Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 19 (-1) (-2) 2 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e16 : θ hN (↑d * ((-4) + 8)) 1 = (Jt hN hd 4) := by
    rw [Jt_norm hN hd _ 4 0 (0) 4 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e17 : θ hN (↑d * ((-4) - 8)) 1 = -((Qt hd ^ 12)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 9 (-1) (-12) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e18 : θ hN (↑d * (6 + (-1))) 1 = (Jt hN hd 5) := by
    rw [Jt_norm hN hd _ 5 0 (0) 5 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e19 : θ hN (↑d * (6 - (-1))) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e20 : θ hN (↑d * ((-1) + 8)) 1 = (Jt hN hd 7) := by
    rw [Jt_norm hN hd _ 7 0 (0) 7 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e21 : θ hN (↑d * ((-1) - 8)) 1 = -((Qt hd ^ 9)⁻¹ * Jt hN hd 9) := by
    rw [Jt_norm hN hd _ 12 (-1) (-9) 9 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e22 : θ hN (↑d * ((-4) + 6)) 1 = (Jt hN hd 2) := by
    rw [Jt_norm hN hd _ 2 0 (0) 2 (1) (by norm_num) (by norm_num [c2]) (Or.inl rfl) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have e23 : θ hN (↑d * ((-4) - 6)) 1 = -((Qt hd ^ 10)⁻¹ * Jt hN hd 10) := by
    rw [Jt_norm hN hd _ 11 (-1) (-10) 10 (-1) (by norm_num) (by norm_num [c2]) (Or.inr (by norm_num)) (by norm_num)]
    simp only [zpow_neg, zpow_ofNat, zpow_one, zpow_zero, one_mul]; ring
  have w0 := weierQ hN hd (x := -3) (y := 0) (u := 7) (v := 9) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23] at w0
  rw [show ((7 : ℤ) - 0) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast] at w0
  have w1 := weierQ hN hd (x := -4) (y := -1) (u := 6) (v := 8) (by norm_num) (by norm_num) (by norm_num)
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23] at w1
  rw [show ((6 : ℤ) - (-1)) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast] at w1
  linear_combination (norm := skip) (1 : L) * Qt hd ^ 13 * (Jt hN hd 2 ^ 1)⁻¹ * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 1)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * w0 + (-1 : L) * Qt hd ^ 15 * (Jt hN hd 2 ^ 1)⁻¹ * Jt hN hd 3 * (Jt hN hd 6 ^ 1)⁻¹ * (Jt hN hd 7 ^ 2)⁻¹ * (Jt hN hd 9 ^ 1)⁻¹ * (Jt hN hd 10 ^ 1)⁻¹ * w1
  field_simp
  ring


end T
end ALz
