/-
# Ramanujan's conjecture for powers of 5 (Watson; Hirschhorn–Hunt), part 1: the modular equation

With `y = q·E(q²⁵)/E(q)` and `τ = q·E(q⁵)⁶/E(q)⁶` (here `y = E₅(1/N)·q·𝒬`, `τ = q/N` from the dissection):
  `y⁵ = τ(q⁵)·(25y⁴ + 25y³ + 15y² + 5y + 1)`   (Watson's modular equation),
and `U₅(yᵏ) = Σ_j m_{k,j} τʲ` with explicit integers for `k ≤ 4` — all as polynomial identities modulo `αβ = 1`.
-/
import RamanujanTau.MockTheta5PartitionCount
import RamanujanTau.RamanujanMostBeautiful

set_option autoImplicit false

namespace MockTheta5.JTP
open PowerSeries Finset MockTheta5.Bailey

lemma isUnit_normQ : IsUnit normQ := isUnit_of_mul_isUnit_right isUnit_eQ_mul_normQ

lemma E5_X' : E5 (X : PowerSeries ℤ) = X ^ 5 := E5_X

/-- `𝒬` as a polynomial in `A = α(q⁵)`, `B = β(q⁵)`, `q`. -/
lemma Qpoly_eq : Qpoly = E5 alphaQ ^ 4 + X * E5 alphaQ ^ 3 + 2 * X ^ 2 * E5 alphaQ ^ 2 + 3 * X ^ 3 * E5 alphaQ
    + 5 * X ^ 4 - 3 * X ^ 5 * E5 betaQ + 2 * X ^ 6 * E5 betaQ ^ 2 - X ^ 7 * E5 betaQ ^ 3 + X ^ 8 * E5 betaQ ^ 4 := by
  simp only [Qpoly, map_sub, map_add, map_mul, map_pow, map_ofNat, E5_X']
  ring

lemma E5_normQ : E5 normQ = E5 alphaQ ^ 5 - 11 * X ^ 5 - X ^ 10 * E5 betaQ ^ 5 := by
  simp only [normQ, map_sub, map_mul, map_pow, map_ofNat, E5_X']
  ring

set_option maxHeartbeats 4000000 in
/-- the modular equation, polynomial form: `𝒬⁵ = 25q⁴𝒬⁴ + 25q³𝒬³N + 15q²𝒬²N² + 5q𝒬N³ + N⁴`. -/
lemma modular_poly : Qpoly ^ 5 = 25 * X ^ 4 * Qpoly ^ 4 + 25 * X ^ 3 * Qpoly ^ 3 * E5 normQ
    + 15 * X ^ 2 * Qpoly ^ 2 * E5 normQ ^ 2 + 5 * X * Qpoly * E5 normQ ^ 3 + E5 normQ ^ 4 := by
  have hAB : E5 alphaQ * E5 betaQ = 1 := by rw [← map_mul, alphaQ_mul_betaQ, map_one]
  rw [Qpoly_eq, E5_normQ]
  set A := E5 alphaQ
  set B := E5 betaQ
  linear_combination (5*A^15*B^3*X^8 - 5*A^15*B^2*X^7 + 10*A^15*B*X^6 - 15*A^15*X^5 + 4*A^14*B^4*X^10 + 15*A^14*B^3*X^9 - 10*A^14*B^2*X^8 + 25*A^14*B*X^7 - 35*A^14*X^6 + 15*A^13*B^4*X^11 + 44*A^13*B^3*X^10 - 25*A^13*B^2*X^9 + 70*A^13*B*X^8 - 95*A^13*X^7 + 45*A^12*B^4*X^12 + 110*A^12*B^3*X^11 - 51*A^12*B^2*X^10 + 165*A^12*B*X^9 - 215*A^12*X^8 + 10*A^11*B^7*X^16 - 20*A^11*B^6*X^15 + 50*A^11*B^5*X^14 + 15*A^11*B^4*X^13 + 360*A^11*B^3*X^12 - 225*A^11*B^2*X^11 + 469*A^11*B*X^10 - 480*A^11*X^9 + 30*A^10*B^7*X^17 - 50*A^10*B^6*X^16 + 130*A^10*B^5*X^15 + 20*A^10*B^4*X^14 + 670*A^10*B^3*X^13 - 355*A^10*B^2*X^12 + 755*A^10*B*X^11 - 596*A^10*X^10 - 6*A^9*B^9*X^20 + 15*A^9*B^8*X^19 + 60*A^9*B^7*X^18 - 90*A^9*B^6*X^17 + 280*A^9*B^5*X^16 - 152*A^9*B^4*X^15 + 1365*A^9*B^3*X^14 - 825*A^9*B^2*X^13 + 1510*A^9*B*X^12 - 1030*A^9*X^11 - 15*A^8*B^9*X^21 + 54*A^8*B^8*X^20 + 100*A^8*B^7*X^19 - 110*A^8*B^6*X^18 + 455*A^8*B^5*X^17 - 350*A^8*B^4*X^16 + 2238*A^8*B^3*X^15 - 1315*A^8*B^2*X^14 + 2360*A^8*B*X^13 - 1310*A^8*X^12 + 10*A^7*B^11*X^24 - 30*A^7*B^10*X^23 + 60*A^7*B^9*X^22 - 100*A^7*B^8*X^21 + 564*A^7*B^7*X^20 - 770*A^7*B^6*X^19 + 1620*A^7*B^5*X^18 - 1750*A^7*B^4*X^17 + 4275*A^7*B^3*X^16 - 2687*A^7*B^2*X^15 + 3720*A^7*B*X^14 - 1345*A^7*X^13 + 20*A^6*B^11*X^25 - 50*A^6*B^10*X^24 + 90*A^6*B^9*X^23 - 110*A^6*B^8*X^22 + 770*A^6*B^7*X^21 - 876*A^6*B^6*X^20 + 1940*A^6*B^5*X^19 - 2115*A^6*B^4*X^18 + 4925*A^6*B^3*X^17 - 2700*A^6*B^2*X^16 + 3883*A^6*B*X^15 - 465*A^6*X^14 + 50*A^5*B^11*X^26 - 130*A^5*B^10*X^25 + 280*A^5*B^9*X^24 - 455*A^5*B^8*X^23 + 1620*A^5*B^7*X^22 - 1940*A^5*B^6*X^21 + 3434*A^5*B^5*X^20 - 4150*A^5*B^4*X^19 + 7160*A^5*B^3*X^18 - 3970*A^5*B^2*X^17 + 5115*A^5*B*X^16 - 1292*A^5*X^15 + 4*A^4*B^14*X^30 - 15*A^4*B^13*X^29 + 45*A^4*B^12*X^28 - 15*A^4*B^11*X^27 + 20*A^4*B^10*X^26 + 152*A^4*B^9*X^25 - 350*A^4*B^8*X^24 + 1750*A^4*B^7*X^23 - 2115*A^4*B^6*X^22 + 4150*A^4*B^5*X^21 - 4564*A^4*B^4*X^20 + 7190*A^4*B^3*X^19 - 3325*A^4*B^2*X^18 + 4175*A^4*B*X^17 + 795*A^4*X^16 + 5*A^3*B^15*X^32 - 15*A^3*B^14*X^31 + 44*A^3*B^13*X^30 - 110*A^3*B^12*X^29 + 360*A^3*B^11*X^28 - 670*A^3*B^10*X^27 + 1365*A^3*B^9*X^26 - 2238*A^3*B^8*X^25 + 4275*A^3*B^7*X^24 - 4925*A^3*B^6*X^23 + 7160*A^3*B^5*X^22 - 7190*A^3*B^4*X^21 + 8166*A^3*B^3*X^20 - 3665*A^3*B^2*X^19 + 3760*A^3*B*X^18 + 1850*A^3*X^17 + 5*A^2*B^15*X^33 - 10*A^2*B^14*X^32 + 25*A^2*B^13*X^31 - 51*A^2*B^12*X^30 + 225*A^2*B^11*X^29 - 355*A^2*B^10*X^28 + 825*A^2*B^9*X^27 - 1315*A^2*B^8*X^26 + 2687*A^2*B^7*X^25 - 2700*A^2*B^6*X^24 + 3970*A^2*B^5*X^23 - 3325*A^2*B^4*X^22 + 3665*A^2*B^3*X^21 + 266*A^2*B^2*X^20 + 480*A^2*B*X^19 + 2200*A^2*X^18 + 10*A*B^15*X^34 - 25*A*B^14*X^33 + 70*A*B^13*X^32 - 165*A*B^12*X^31 + 469*A*B^11*X^30 - 755*A*B^10*X^29 + 1510*A*B^9*X^28 - 2360*A*B^8*X^27 + 3720*A*B^7*X^26 - 3883*A*B^6*X^25 + 5115*A*B^5*X^24 - 4175*A*B^4*X^23 + 3760*A*B^3*X^22 - 480*A*B^2*X^21 + 1446*A*B*X^20 + 735*A*X^19 + 15*B^15*X^35 - 35*B^14*X^34 + 95*B^13*X^33 - 215*B^12*X^32 + 480*B^11*X^31 - 596*B^10*X^30 + 1030*B^9*X^29 - 1310*B^8*X^28 + 1345*B^7*X^27 - 465*B^6*X^26 + 1292*B^5*X^25 + 795*B^4*X^24 - 1850*B^3*X^23 + 2200*B^2*X^22 - 735*B*X^21 + 4866*X^20) * hAB

/-- `y = q·E(q²⁵)/E(q)`. -/
noncomputable def Ys : PowerSeries ℤ := E5 (Ring.inverse normQ) * (X * Qpoly)

/-- `τ = q·E(q⁵)⁶/E(q)⁶ = q/N`. -/
noncomputable def taus : PowerSeries ℤ := X * Ring.inverse normQ

lemma normQ_mul_inv : normQ * Ring.inverse normQ = 1 := Ring.mul_inverse_cancel _ isUnit_normQ

set_option maxHeartbeats 4000000 in
/-- **Watson's modular equation**: `y⁵ = τ(q⁵)·(25y⁴ + 25y³ + 15y² + 5y + 1)`. -/
theorem modular_eq : Ys ^ 5 = E5 taus * (25 * Ys ^ 4 + 25 * Ys ^ 3 + 15 * Ys ^ 2 + 5 * Ys + 1) := by
  have hme := modular_poly
  have hN : E5 normQ * E5 (Ring.inverse normQ) = 1 := by rw [← map_mul, normQ_mul_inv, map_one]
  simp only [Ys, taus, map_mul, E5_X']
  set N := E5 normQ
  set Ni := E5 (Ring.inverse normQ)
  set Q := Qpoly
  linear_combination X ^ 5 * Ni ^ 5 * hme + X ^ 5 * (25 * X ^ 3 * Q ^ 3 * Ni ^ 4
    + 15 * X ^ 2 * Q ^ 2 * Ni ^ 3 * (Ni * N + 1) + 5 * X * Q * Ni ^ 2 * ((Ni * N) ^ 2 + Ni * N + 1)
    + Ni * ((Ni * N) ^ 3 + (Ni * N) ^ 2 + Ni * N + 1)) * hN

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma Ys_base1 : dis5 0 (Ys ^ 1) = (0 : PowerSeries ℤ) * taus ^ 0 + (5 : PowerSeries ℤ) * taus ^ 1 := by
  have hab := alphaQ_mul_betaQ
  have hn := normQ_mul_inv
  have hnf : (X * Qpoly) ^ 1 = E5 (5*X) + X * E5 (-3*X*betaQ + alphaQ^4) + X ^ 2 * E5 (2*X*betaQ^2 + alphaQ^3) + X ^ 3 * E5 (-X*betaQ^3 + 2*alphaQ^2) + X ^ 4 * E5 (X*betaQ^4 + 3*alphaQ) := by
    rw [Qpoly_eq]; simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_neg, map_one, E5_X']; ring
  have hc0 : 5*X = (0 : PowerSeries ℤ) * X ^ 0 * normQ ^ 1 + (5 : PowerSeries ℤ) * X ^ 1 * normQ ^ 0 := by
    rw [normQ]; linear_combination (0) * hab
  rw [Ys, mul_pow, ← map_pow, dis5_E5_mul 0 (by norm_num), hnf, dis5_normal 0 (by norm_num)]
  simp only [if_true, show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 0 by omega,
    show (4 : ℕ) ≠ 0 by omega, if_false, mul_zero, add_zero]
  rw [hc0, taus]
  linear_combination (0) * hn

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma Ys_base2 : dis5 0 (Ys ^ 2) = (0 : PowerSeries ℤ) * taus ^ 0 + (10 : PowerSeries ℤ) * taus ^ 1 + (125 : PowerSeries ℤ) * taus ^ 2 := by
  have hab := alphaQ_mul_betaQ
  have hn := normQ_mul_inv
  have hnf : (X * Qpoly) ^ 2 = E5 (-10*X^3*betaQ^5 + 2*X^2*alphaQ^4*betaQ^4 - 2*X^2*alphaQ^3*betaQ^3 + 8*X^2*alphaQ^2*betaQ^2 - 18*X^2*alphaQ*betaQ + 25*X^2 + 10*X*alphaQ^5) + X * E5 (5*X^3*betaQ^6 + 2*X^2*alphaQ^3*betaQ^4 - 4*X^2*alphaQ^2*betaQ^3 + 12*X^2*alphaQ*betaQ^2 - 30*X^2*betaQ + 20*X*alphaQ^4) + X ^ 2 * E5 (-2*X^3*betaQ^7 + 4*X^2*alphaQ^2*betaQ^4 - 6*X^2*alphaQ*betaQ^3 + 29*X^2*betaQ^2 - 6*X*alphaQ^4*betaQ + 22*X*alphaQ^3 + alphaQ^8) + X ^ 3 * E5 (X^3*betaQ^8 + 6*X^2*alphaQ*betaQ^4 - 22*X^2*betaQ^3 + 4*X*alphaQ^4*betaQ^2 - 6*X*alphaQ^3*betaQ + 29*X*alphaQ^2 + 2*alphaQ^7) + X ^ 4 * E5 (20*X^2*betaQ^4 - 2*X*alphaQ^4*betaQ^3 + 4*X*alphaQ^3*betaQ^2 - 12*X*alphaQ^2*betaQ + 30*X*alphaQ + 5*alphaQ^6) := by
    rw [Qpoly_eq]; simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_neg, map_one, E5_X']; ring
  have hc0 : -10*X^3*betaQ^5 + 2*X^2*alphaQ^4*betaQ^4 - 2*X^2*alphaQ^3*betaQ^3 + 8*X^2*alphaQ^2*betaQ^2 - 18*X^2*alphaQ*betaQ + 25*X^2 + 10*X*alphaQ^5 = (0 : PowerSeries ℤ) * X ^ 0 * normQ ^ 2 + (10 : PowerSeries ℤ) * X ^ 1 * normQ ^ 1 + (125 : PowerSeries ℤ) * X ^ 2 * normQ ^ 0 := by
    rw [normQ]; linear_combination (2*X^2*alphaQ^3*betaQ^3 + 8*X^2*alphaQ*betaQ - 10*X^2) * hab
  rw [Ys, mul_pow, ← map_pow, dis5_E5_mul 0 (by norm_num), hnf, dis5_normal 0 (by norm_num)]
  simp only [if_true, show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 0 by omega,
    show (4 : ℕ) ≠ 0 by omega, if_false, mul_zero, add_zero]
  rw [hc0, taus]
  linear_combination ((10 : PowerSeries ℤ) * X ^ 1 * Ring.inverse normQ ^ 1 * ((normQ * Ring.inverse normQ) ^ 0)) * hn

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma Ys_base3 : dis5 0 (Ys ^ 3) = (0 : PowerSeries ℤ) * taus ^ 0 + (9 : PowerSeries ℤ) * taus ^ 1 + (375 : PowerSeries ℤ) * taus ^ 2 + (3125 : PowerSeries ℤ) * taus ^ 3 := by
  have hab := alphaQ_mul_betaQ
  have hn := normQ_mul_inv
  have hnf : (X * Qpoly) ^ 3 = E5 (9*X^5*betaQ^10 + 3*X^4*alphaQ^3*betaQ^8 - 12*X^4*alphaQ^2*betaQ^7 + 45*X^4*alphaQ*betaQ^6 - 213*X^4*betaQ^5 + 90*X^3*alphaQ^4*betaQ^4 - 102*X^3*alphaQ^3*betaQ^3 + 228*X^3*alphaQ^2*betaQ^2 - 270*X^3*alphaQ*betaQ + 125*X^3 - 3*X^2*alphaQ^8*betaQ^3 + 12*X^2*alphaQ^7*betaQ^2 - 45*X^2*alphaQ^6*betaQ + 213*X^2*alphaQ^5 + 9*X*alphaQ^10) + X * E5 (-3*X^5*betaQ^11 + 6*X^4*alphaQ^2*betaQ^8 - 18*X^4*alphaQ*betaQ^7 + 146*X^4*betaQ^6 - 30*X^3*alphaQ^4*betaQ^5 + 96*X^3*alphaQ^3*betaQ^4 - 159*X^3*alphaQ^2*betaQ^3 + 261*X^3*alphaQ*betaQ^2 - 225*X^3*betaQ + 3*X^2*alphaQ^8*betaQ^4 - 6*X^2*alphaQ^7*betaQ^3 + 30*X^2*alphaQ^6*betaQ^2 - 90*X^2*alphaQ^5*betaQ + 279*X^2*alphaQ^4 + 22*X*alphaQ^9) + X ^ 2 * E5 (X^5*betaQ^12 + 9*X^4*alphaQ*betaQ^8 - 87*X^4*betaQ^7 + 15*X^3*alphaQ^4*betaQ^6 - 30*X^3*alphaQ^3*betaQ^5 + 147*X^3*alphaQ^2*betaQ^4 - 198*X^3*alphaQ*betaQ^3 + 285*X^3*betaQ^2 + 6*X^2*alphaQ^7*betaQ^4 - 15*X^2*alphaQ^6*betaQ^3 + 60*X^2*alphaQ^5*betaQ^2 - 180*X^2*alphaQ^4*betaQ + 282*X^2*alphaQ^3 + 51*X*alphaQ^8) + X ^ 3 * E5 (51*X^4*betaQ^8 - 6*X^3*alphaQ^4*betaQ^7 + 15*X^3*alphaQ^3*betaQ^6 - 60*X^3*alphaQ^2*betaQ^5 + 180*X^3*alphaQ*betaQ^4 - 282*X^3*betaQ^3 + 15*X^2*alphaQ^6*betaQ^4 - 30*X^2*alphaQ^5*betaQ^3 + 147*X^2*alphaQ^4*betaQ^2 - 198*X^2*alphaQ^3*betaQ + 285*X^2*alphaQ^2 - 9*X*alphaQ^8*betaQ + 87*X*alphaQ^7 + alphaQ^12) + X ^ 4 * E5 (-22*X^4*betaQ^9 + 3*X^3*alphaQ^4*betaQ^8 - 6*X^3*alphaQ^3*betaQ^7 + 30*X^3*alphaQ^2*betaQ^6 - 90*X^3*alphaQ*betaQ^5 + 279*X^3*betaQ^4 + 30*X^2*alphaQ^5*betaQ^4 - 96*X^2*alphaQ^4*betaQ^3 + 159*X^2*alphaQ^3*betaQ^2 - 261*X^2*alphaQ^2*betaQ + 225*X^2*alphaQ + 6*X*alphaQ^8*betaQ^2 - 18*X*alphaQ^7*betaQ + 146*X*alphaQ^6 + 3*alphaQ^11) := by
    rw [Qpoly_eq]; simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_neg, map_one, E5_X']; ring
  have hc0 : 9*X^5*betaQ^10 + 3*X^4*alphaQ^3*betaQ^8 - 12*X^4*alphaQ^2*betaQ^7 + 45*X^4*alphaQ*betaQ^6 - 213*X^4*betaQ^5 + 90*X^3*alphaQ^4*betaQ^4 - 102*X^3*alphaQ^3*betaQ^3 + 228*X^3*alphaQ^2*betaQ^2 - 270*X^3*alphaQ*betaQ + 125*X^3 - 3*X^2*alphaQ^8*betaQ^3 + 12*X^2*alphaQ^7*betaQ^2 - 45*X^2*alphaQ^6*betaQ + 213*X^2*alphaQ^5 + 9*X*alphaQ^10 = (0 : PowerSeries ℤ) * X ^ 0 * normQ ^ 3 + (9 : PowerSeries ℤ) * X ^ 1 * normQ ^ 2 + (375 : PowerSeries ℤ) * X ^ 2 * normQ ^ 1 + (3125 : PowerSeries ℤ) * X ^ 3 * normQ ^ 0 := by
    rw [normQ]; linear_combination (3*X^4*alphaQ^2*betaQ^7 - 9*X^4*alphaQ*betaQ^6 + 36*X^4*betaQ^5 + 18*X^3*alphaQ^4*betaQ^4 + 108*X^3*alphaQ^3*betaQ^3 + 6*X^3*alphaQ^2*betaQ^2 + 234*X^3*alphaQ*betaQ - 36*X^3 - 3*X^2*alphaQ^7*betaQ^2 + 9*X^2*alphaQ^6*betaQ - 36*X^2*alphaQ^5) * hab
  rw [Ys, mul_pow, ← map_pow, dis5_E5_mul 0 (by norm_num), hnf, dis5_normal 0 (by norm_num)]
  simp only [if_true, show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 0 by omega,
    show (4 : ℕ) ≠ 0 by omega, if_false, mul_zero, add_zero]
  rw [hc0, taus]
  linear_combination ((9 : PowerSeries ℤ) * X ^ 1 * Ring.inverse normQ ^ 1 * ((normQ * Ring.inverse normQ) ^ 0 + (normQ * Ring.inverse normQ) ^ 1) + (375 : PowerSeries ℤ) * X ^ 2 * Ring.inverse normQ ^ 2 * ((normQ * Ring.inverse normQ) ^ 0)) * hn

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma Ys_base4 : dis5 0 (Ys ^ 4) = (0 : PowerSeries ℤ) * taus ^ 0 + (4 : PowerSeries ℤ) * taus ^ 1 + (550 : PowerSeries ℤ) * taus ^ 2 + (12500 : PowerSeries ℤ) * taus ^ 3 + (78125 : PowerSeries ℤ) * taus ^ 4 := by
  have hab := alphaQ_mul_betaQ
  have hn := normQ_mul_inv
  have hnf : (X * Qpoly) ^ 4 = E5 (-4*X^7*betaQ^15 + 8*X^6*alphaQ^2*betaQ^12 - 36*X^6*alphaQ*betaQ^11 + 446*X^6*betaQ^10 - 88*X^5*alphaQ^4*betaQ^9 + 276*X^5*alphaQ^3*betaQ^8 - 804*X^5*alphaQ^2*betaQ^7 + 1752*X^5*alphaQ*betaQ^6 - 2976*X^5*betaQ^5 + 6*X^4*alphaQ^8*betaQ^8 - 24*X^4*alphaQ^7*betaQ^7 + 150*X^4*alphaQ^6*betaQ^6 - 600*X^4*alphaQ^5*betaQ^5 + 2532*X^4*alphaQ^4*betaQ^4 - 2820*X^4*alphaQ^3*betaQ^3 + 3846*X^4*alphaQ^2*betaQ^2 - 2700*X^4*alphaQ*betaQ + 625*X^4 + 88*X^3*alphaQ^9*betaQ^4 - 276*X^3*alphaQ^8*betaQ^3 + 804*X^3*alphaQ^7*betaQ^2 - 1752*X^3*alphaQ^6*betaQ + 2976*X^3*alphaQ^5 + 8*X^2*alphaQ^12*betaQ^2 - 36*X^2*alphaQ^11*betaQ + 446*X^2*alphaQ^10 + 4*X*alphaQ^15) + X * E5 (X^7*betaQ^16 + 12*X^6*alphaQ*betaQ^12 - 224*X^6*betaQ^11 + 36*X^5*alphaQ^4*betaQ^10 - 88*X^5*alphaQ^3*betaQ^9 + 462*X^5*alphaQ^2*betaQ^8 - 1044*X^5*alphaQ*betaQ^7 + 2494*X^5*betaQ^6 + 12*X^4*alphaQ^7*betaQ^8 - 60*X^4*alphaQ^6*betaQ^7 + 300*X^4*alphaQ^5*betaQ^6 - 1452*X^4*alphaQ^4*betaQ^5 + 2664*X^4*alphaQ^3*betaQ^4 - 3444*X^4*alphaQ^2*betaQ^3 + 3420*X^4*alphaQ*betaQ^2 - 1500*X^4*betaQ + 264*X^3*alphaQ^8*betaQ^4 - 492*X^3*alphaQ^7*betaQ^3 + 1438*X^3*alphaQ^6*betaQ^2 - 2556*X^3*alphaQ^5*betaQ + 3161*X^3*alphaQ^4 - 4*X^2*alphaQ^12*betaQ^3 + 24*X^2*alphaQ^11*betaQ^2 - 108*X^2*alphaQ^10*betaQ + 796*X^2*alphaQ^9 + 14*X*alphaQ^14) + X ^ 2 * E5 (105*X^6*betaQ^12 - 12*X^5*alphaQ^4*betaQ^11 + 36*X^5*alphaQ^3*betaQ^10 - 176*X^5*alphaQ^2*betaQ^9 + 612*X^5*alphaQ*betaQ^8 - 1860*X^5*betaQ^7 + 30*X^4*alphaQ^6*betaQ^8 - 120*X^4*alphaQ^5*betaQ^7 + 884*X^4*alphaQ^4*betaQ^6 - 1572*X^4*alphaQ^3*betaQ^5 + 3312*X^4*alphaQ^2*betaQ^4 - 3384*X^4*alphaQ*betaQ^3 + 2350*X^4*betaQ^2 - 60*X^3*alphaQ^8*betaQ^5 + 468*X^3*alphaQ^7*betaQ^4 - 944*X^3*alphaQ^6*betaQ^3 + 2244*X^3*alphaQ^5*betaQ^2 - 3348*X^3*alphaQ^4*betaQ + 2840*X^3*alphaQ^3 + 4*X^2*alphaQ^12*betaQ^4 - 12*X^2*alphaQ^11*betaQ^3 + 72*X^2*alphaQ^10*betaQ^2 - 264*X^2*alphaQ^9*betaQ + 1300*X^2*alphaQ^8 + 40*X*alphaQ^13) + X ^ 3 * E5 (-40*X^6*betaQ^13 + 4*X^5*alphaQ^4*betaQ^12 - 12*X^5*alphaQ^3*betaQ^11 + 72*X^5*alphaQ^2*betaQ^10 - 264*X^5*alphaQ*betaQ^9 + 1300*X^5*betaQ^8 + 60*X^4*alphaQ^5*betaQ^8 - 468*X^4*alphaQ^4*betaQ^7 + 944*X^4*alphaQ^3*betaQ^6 - 2244*X^4*alphaQ^2*betaQ^5 + 3348*X^4*alphaQ*betaQ^4 - 2840*X^4*betaQ^3 + 30*X^3*alphaQ^8*betaQ^6 - 120*X^3*alphaQ^7*betaQ^5 + 884*X^3*alphaQ^6*betaQ^4 - 1572*X^3*alphaQ^5*betaQ^3 + 3312*X^3*alphaQ^4*betaQ^2 - 3384*X^3*alphaQ^3*betaQ + 2350*X^3*alphaQ^2 + 12*X^2*alphaQ^11*betaQ^4 - 36*X^2*alphaQ^10*betaQ^3 + 176*X^2*alphaQ^9*betaQ^2 - 612*X^2*alphaQ^8*betaQ + 1860*X^2*alphaQ^7 + 105*X*alphaQ^12) + X ^ 4 * E5 (14*X^6*betaQ^14 + 4*X^5*alphaQ^3*betaQ^12 - 24*X^5*alphaQ^2*betaQ^11 + 108*X^5*alphaQ*betaQ^10 - 796*X^5*betaQ^9 + 264*X^4*alphaQ^4*betaQ^8 - 492*X^4*alphaQ^3*betaQ^7 + 1438*X^4*alphaQ^2*betaQ^6 - 2556*X^4*alphaQ*betaQ^5 + 3161*X^4*betaQ^4 - 12*X^3*alphaQ^8*betaQ^7 + 60*X^3*alphaQ^7*betaQ^6 - 300*X^3*alphaQ^6*betaQ^5 + 1452*X^3*alphaQ^5*betaQ^4 - 2664*X^3*alphaQ^4*betaQ^3 + 3444*X^3*alphaQ^3*betaQ^2 - 3420*X^3*alphaQ^2*betaQ + 1500*X^3*alphaQ + 36*X^2*alphaQ^10*betaQ^4 - 88*X^2*alphaQ^9*betaQ^3 + 462*X^2*alphaQ^8*betaQ^2 - 1044*X^2*alphaQ^7*betaQ + 2494*X^2*alphaQ^6 - 12*X*alphaQ^12*betaQ + 224*X*alphaQ^11 + alphaQ^16) := by
    rw [Qpoly_eq]; simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_neg, map_one, E5_X']; ring
  have hc0 : -4*X^7*betaQ^15 + 8*X^6*alphaQ^2*betaQ^12 - 36*X^6*alphaQ*betaQ^11 + 446*X^6*betaQ^10 - 88*X^5*alphaQ^4*betaQ^9 + 276*X^5*alphaQ^3*betaQ^8 - 804*X^5*alphaQ^2*betaQ^7 + 1752*X^5*alphaQ*betaQ^6 - 2976*X^5*betaQ^5 + 6*X^4*alphaQ^8*betaQ^8 - 24*X^4*alphaQ^7*betaQ^7 + 150*X^4*alphaQ^6*betaQ^6 - 600*X^4*alphaQ^5*betaQ^5 + 2532*X^4*alphaQ^4*betaQ^4 - 2820*X^4*alphaQ^3*betaQ^3 + 3846*X^4*alphaQ^2*betaQ^2 - 2700*X^4*alphaQ*betaQ + 625*X^4 + 88*X^3*alphaQ^9*betaQ^4 - 276*X^3*alphaQ^8*betaQ^3 + 804*X^3*alphaQ^7*betaQ^2 - 1752*X^3*alphaQ^6*betaQ + 2976*X^3*alphaQ^5 + 8*X^2*alphaQ^12*betaQ^2 - 36*X^2*alphaQ^11*betaQ + 446*X^2*alphaQ^10 + 4*X*alphaQ^15 = (0 : PowerSeries ℤ) * X ^ 0 * normQ ^ 4 + (4 : PowerSeries ℤ) * X ^ 1 * normQ ^ 3 + (550 : PowerSeries ℤ) * X ^ 2 * normQ ^ 2 + (12500 : PowerSeries ℤ) * X ^ 3 * normQ ^ 1 + (78125 : PowerSeries ℤ) * X ^ 4 * normQ ^ 0 := by
    rw [normQ]; linear_combination (8*X^6*alphaQ*betaQ^11 - 28*X^6*betaQ^10 - 12*X^5*alphaQ^4*betaQ^9 - 100*X^5*alphaQ^3*betaQ^8 + 176*X^5*alphaQ^2*betaQ^7 - 628*X^5*alphaQ*betaQ^6 + 1124*X^5*betaQ^5 + 6*X^4*alphaQ^7*betaQ^7 - 18*X^4*alphaQ^6*betaQ^6 + 132*X^4*alphaQ^5*betaQ^5 + 368*X^4*alphaQ^4*betaQ^4 + 2900*X^4*alphaQ^3*betaQ^3 + 80*X^4*alphaQ^2*betaQ^2 + 3926*X^4*alphaQ*betaQ + 1226*X^4 + 12*X^3*alphaQ^9*betaQ^4 + 100*X^3*alphaQ^8*betaQ^3 - 176*X^3*alphaQ^7*betaQ^2 + 628*X^3*alphaQ^6*betaQ - 1124*X^3*alphaQ^5 + 8*X^2*alphaQ^11*betaQ - 28*X^2*alphaQ^10) * hab
  rw [Ys, mul_pow, ← map_pow, dis5_E5_mul 0 (by norm_num), hnf, dis5_normal 0 (by norm_num)]
  simp only [if_true, show (1 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 0 by omega,
    show (4 : ℕ) ≠ 0 by omega, if_false, mul_zero, add_zero]
  rw [hc0, taus]
  linear_combination ((4 : PowerSeries ℤ) * X ^ 1 * Ring.inverse normQ ^ 1 * ((normQ * Ring.inverse normQ) ^ 0 + (normQ * Ring.inverse normQ) ^ 1 + (normQ * Ring.inverse normQ) ^ 2) + (550 : PowerSeries ℤ) * X ^ 2 * Ring.inverse normQ ^ 2 * ((normQ * Ring.inverse normQ) ^ 0 + (normQ * Ring.inverse normQ) ^ 1) + (12500 : PowerSeries ℤ) * X ^ 3 * Ring.inverse normQ ^ 3 * ((normQ * Ring.inverse normQ) ^ 0)) * hn

/-! ## `U₅(yᵏ)` for all `k` -/

open Polynomial in
/-- the polynomials with `U₅(yᵏ) = Pm k (τ)`. -/
noncomputable def Pm : ℕ → Polynomial ℤ
  | 0 => 1
  | 1 => 5 * Polynomial.X
  | 2 => 10 * Polynomial.X + 125 * Polynomial.X ^ 2
  | 3 => 9 * Polynomial.X + 375 * Polynomial.X ^ 2 + 3125 * Polynomial.X ^ 3
  | 4 => 4 * Polynomial.X + 550 * Polynomial.X ^ 2 + 12500 * Polynomial.X ^ 3 + 78125 * Polynomial.X ^ 4
  | k + 5 => Polynomial.X * (25 * Pm (k + 4) + 25 * Pm (k + 3) + 15 * Pm (k + 2) + 5 * Pm (k + 1) + Pm k)

lemma dis5_one : dis5 0 (1 : PowerSeries ℤ) = 1 := by
  have := dis5_E5 0 (by norm_num) 1; simpa using this

lemma dis5_C_mul (r : ℕ) (a : ℤ) (F : PowerSeries ℤ) : dis5 r (C a * F) = C a * dis5 r F := by
  ext n; rw [dis5, dis5, coeff_mk, coeff_C_mul, coeff_C_mul, coeff_mk]

/-- **`U₅(yᵏ) = Pm k (τ)`** for every `k`. -/
theorem Ys_dis (k : ℕ) : dis5 0 (Ys ^ k) = Polynomial.aeval taus (Pm k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [Pm, dis5_one]
    | 1, _ => rw [Ys_base1]; simp [Pm, map_ofNat]
    | 2, _ => rw [Ys_base2]; simp [Pm, map_ofNat]
    | 3, _ => rw [Ys_base3]; simp [Pm, map_ofNat]
    | 4, _ => rw [Ys_base4]; simp [Pm, map_ofNat]
    | k + 5, ih =>
      have h5 : Ys ^ (k + 5) = E5 taus * (C 25 * Ys ^ (k + 4) + C 25 * Ys ^ (k + 3) + C 15 * Ys ^ (k + 2)
          + C 5 * Ys ^ (k + 1) + Ys ^ k) := by
        rw [show Ys ^ (k + 5) = Ys ^ k * Ys ^ 5 by ring, modular_eq]
        simp only [map_ofNat]; ring
      rw [h5, dis5_E5_mul 0 (by norm_num)]
      have lin : dis5 0 (C 25 * Ys ^ (k + 4) + C 25 * Ys ^ (k + 3) + C 15 * Ys ^ (k + 2)
          + C 5 * Ys ^ (k + 1) + Ys ^ k) = C 25 * dis5 0 (Ys ^ (k + 4)) + C 25 * dis5 0 (Ys ^ (k + 3))
          + C 15 * dis5 0 (Ys ^ (k + 2)) + C 5 * dis5 0 (Ys ^ (k + 1)) + dis5 0 (Ys ^ k) := by
        rw [dis5_add, dis5_add, dis5_add, dis5_add, dis5_C_mul, dis5_C_mul, dis5_C_mul, dis5_C_mul]
      rw [lin, ih (k + 4) (by omega), ih (k + 3) (by omega), ih (k + 2) (by omega), ih (k + 1) (by omega),
        ih k (by omega), Pm]
      simp only [map_mul, map_add, Polynomial.aeval_X, map_ofNat]

/-! ## The coefficients `m_{k,j}` -/

/-- `m_{k,j}`: `U₅(yᵏ) = Σ_j m_{k,j} τʲ`. -/
noncomputable def mc (k j : ℕ) : ℤ := (Pm k).coeff j

lemma mc_rec (k j : ℕ) : mc (k + 5) (j + 1) = 25 * mc (k + 4) j + 25 * mc (k + 3) j + 15 * mc (k + 2) j
    + 5 * mc (k + 1) j + mc k j := by
  simp only [mc, Pm, Polynomial.coeff_X_mul, Polynomial.coeff_add]
  simp only [show (25 : Polynomial ℤ) = Polynomial.C 25 by simp, show (15 : Polynomial ℤ) = Polynomial.C 15 by simp,
    show (5 : Polynomial ℤ) = Polynomial.C 5 by simp, Polynomial.coeff_C_mul]

lemma mc_rec0 (k : ℕ) : mc (k + 5) 0 = 0 := by
  simp [mc, Pm, Polynomial.coeff_X_mul_zero]

/-- the explicit table for `k ≤ 4`. -/
lemma mc_small (k j : ℕ) (hk : k ≤ 4) :
    mc k j = if k = 0 then (if j = 0 then 1 else 0) else if k = 1 then (if j = 1 then 5 else 0)
      else if k = 2 then (if j = 1 then 10 else if j = 2 then 125 else 0)
      else if k = 3 then (if j = 1 then 9 else if j = 2 then 375 else if j = 3 then 3125 else 0)
      else (if j = 1 then 4 else if j = 2 then 550 else if j = 3 then 12500 else if j = 4 then 78125 else 0) := by
  interval_cases k <;> rcases j with _ | _ | _ | _ | _ | j <;>
    simp [mc, Pm, Polynomial.coeff_one, Polynomial.coeff_X_pow, Polynomial.coeff_X]

/-- `m_{k,j} = 0` for `j > k`. -/
lemma mc_high (k j : ℕ) (h : k < j) : mc k j = 0 := by
  induction k using Nat.strong_induction_on generalizing j with
  | _ k ih =>
    rcases Nat.lt_or_ge k 5 with hk | hk
    · rw [mc_small k j (by omega)]; split_ifs <;> omega
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 5 := ⟨k - 5, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [mc_rec, ih (k + 4) (by omega) j (by omega), ih (k + 3) (by omega) j (by omega),
        ih (k + 2) (by omega) j (by omega), ih (k + 1) (by omega) j (by omega), ih k (by omega) j (by omega)]
      ring

/-- `m_{k,j} = 0` for `5j < k`. -/
lemma mc_low (k j : ℕ) (h : 5 * j < k) : mc k j = 0 := by
  induction k using Nat.strong_induction_on generalizing j with
  | _ k ih =>
    rcases Nat.lt_or_ge k 5 with hk | hk
    · rw [mc_small k j (by omega)]; split_ifs <;> omega
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 5 := ⟨k - 5, by omega⟩
      rcases j with _ | j
      · exact mc_rec0 k
      · rw [mc_rec, ih (k + 4) (by omega) j (by omega), ih (k + 3) (by omega) j (by omega),
          ih (k + 2) (by omega) j (by omega), ih (k + 1) (by omega) j (by omega), ih k (by omega) j (by omega)]
        ring

lemma dvd_mul_helper {c x : ℤ} {e d : ℕ} (hc : (5 : ℤ) ^ e ∣ c) (hx : e ≤ d → (5 : ℤ) ^ (d - e) ∣ x) :
    (5 : ℤ) ^ d ∣ c * x := by
  rcases Nat.lt_or_ge d e with h | h
  · exact (pow_dvd_pow 5 h.le).trans (hc.mul_right x)
  · rw [show d = e + (d - e) by omega, pow_add]; exact mul_dvd_mul hc (hx h)

/-- **the 5-adic bound** `ν₅(m_{k,j}) ≥ ⌊(5j − k − 1)/2⌋`. -/
lemma mc_dvd (k j d : ℕ) (h : 2 * d + k + 1 ≤ 5 * j) : (5 : ℤ) ^ d ∣ mc k j := by
  induction k using Nat.strong_induction_on generalizing j d with
  | _ k ih =>
    rcases Nat.lt_or_ge k 5 with hk | hk
    · rw [mc_small k j (by omega)]
      split_ifs <;> first
        | exact dvd_zero _
        | omega
        | (subst_vars
           first
            | exact (pow_dvd_pow (5 : ℤ) (by omega : d ≤ 0)).trans (by norm_num)
            | exact (pow_dvd_pow (5 : ℤ) (by omega : d ≤ 1)).trans (by norm_num)
            | exact (pow_dvd_pow (5 : ℤ) (by omega : d ≤ 2)).trans (by norm_num)
            | exact (pow_dvd_pow (5 : ℤ) (by omega : d ≤ 3)).trans (by norm_num)
            | exact (pow_dvd_pow (5 : ℤ) (by omega : d ≤ 4)).trans (by norm_num)
            | exact (pow_dvd_pow (5 : ℤ) (by omega : d ≤ 5)).trans (by norm_num)
            | exact (pow_dvd_pow (5 : ℤ) (by omega : d ≤ 6)).trans (by norm_num)
            | exact (pow_dvd_pow (5 : ℤ) (by omega : d ≤ 7)).trans (by norm_num))
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 5 := ⟨k - 5, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [mc_rec]
      refine dvd_add (dvd_add (dvd_add (dvd_add ?_ ?_) ?_) ?_) ?_
      · exact dvd_mul_helper (e := 2) (by norm_num) fun _ => ih (k + 4) (by omega) j _ (by omega)
      · exact dvd_mul_helper (e := 2) (by norm_num) fun _ => ih (k + 3) (by omega) j _ (by omega)
      · exact dvd_mul_helper (e := 1) (by norm_num) fun _ => ih (k + 2) (by omega) j _ (by omega)
      · exact dvd_mul_helper (e := 1) (by norm_num) fun _ => ih (k + 1) (by omega) j _ (by omega)
      · exact ih k (by omega) j d (by omega)

/-! ## `y`, `τ` and Euler's product -/

lemma eQ_pow6_normQ : eQ ^ 6 * normQ = qfacInf ^ 6 := by rw [← norm_identity, normQ]

/-- `y·E(q) = q·E(q²⁵)`. -/
lemma Ys_mul_E : Ys * qfacInf = X * E5 eQ := by
  have hD := qfacInf_dissection
  have hF := factor_mul_Qpoly
  have hN : E5 normQ * E5 (Ring.inverse normQ) = 1 := by rw [← map_mul, normQ_mul_inv, map_one]
  rw [Ys]
  conv_lhs => rw [hD]
  rw [show E5 (alphaQ ^ 5 - 11 * X - X ^ 2 * betaQ ^ 5) = E5 normQ from rfl] at hF
  linear_combination X * E5 eQ * (E5 (Ring.inverse normQ)) * hF + X * E5 eQ * hN

/-- `E5(1/N)·eQ⁶ = E(q²⁵)⁶`. -/
lemma E5_inv_normQ : E5 (Ring.inverse normQ) * eQ ^ 6 = E5 eQ ^ 6 := by
  have h := congrArg E5 eQ_pow6_normQ
  simp only [map_mul, map_pow] at h
  have hN : E5 normQ * E5 (Ring.inverse normQ) = 1 := by rw [← map_mul, normQ_mul_inv, map_one]
  rw [show E5 qfacInf = eQ from rfl] at h
  linear_combination -(E5 (Ring.inverse normQ) * h) + E5 eQ ^ 6 * hN

/-- **`τ(q)·τ(q⁵) = y⁶`**. -/
lemma taus_mul_E5 : taus * E5 taus = Ys ^ 6 := by
  have hu : IsUnit (qfacInf ^ 6) := isUnit_qfacInf.pow 6
  apply (hu.mul_left_inj).mp
  have h1 : (Ys * qfacInf) ^ 6 = (X * E5 eQ) ^ 6 := by rw [Ys_mul_E]
  have h2 := E5_inv_normQ
  have h3 := eQ_pow6_normQ
  have hn := normQ_mul_inv
  simp only [taus, map_mul, E5_X']
  linear_combination -h1 + X ^ 6 * h2 + X ^ 6 * E5 (Ring.inverse normQ) * eQ ^ 6 * hn
    - X ^ 6 * E5 (Ring.inverse normQ) * Ring.inverse normQ * h3

end MockTheta5.JTP
