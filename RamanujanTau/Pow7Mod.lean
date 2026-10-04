/-
# Watson's congruences for powers of 7, part 2: `U₇(yᵏ)` for all `k`
-/
import RamanujanTau.Pow7
import RamanujanTau.Pow7B
import RamanujanTau.Pow7Pm

set_option autoImplicit false

namespace MockTheta5.JTP
open PowerSeries Finset MockTheta5.Bailey


lemma hg1' : X*yQ*zQ^2 - xQ + yQ^2 = 0 := by linear_combination -rel4
lemma hg2' : xQ*yQ*zQ - 1 = 0 := by linear_combination rel1
lemma hg3' : X*zQ - xQ^2 + xQ*yQ^2 = 0 := by linear_combination -rel2
lemma hg4' : -X*zQ^2 + xQ^2*zQ - yQ = 0 := by linear_combination rel5

lemma c1_0 : dis7 0 (X ^ 2 * Qpoly7) = -7*X^3*xQ*zQ^3 + 7*X^2*yQ^3*zQ - 7*X^2 + 7*X*xQ^3*yQ := cls1_eq0 hg1' hg2' hg3' hg4'

lemma c1_1 : dis7 1 (X ^ 2 * Qpoly7) = 2*X^4*zQ^5 - 14*X^2*xQ*zQ - 3*X^2*yQ^2*zQ + 10*X*xQ^3 + X*yQ^6 := cls1_eq1 hg1' hg2' hg3' hg4'

lemma c1_2 : dis7 2 (X ^ 2 * Qpoly7) = 10*X^3*zQ^3 + 14*X^2*yQ*zQ + 3*X*xQ^2*yQ - 2*X*yQ^5 + xQ^6 := cls1_eq2 hg1' hg2' hg3' hg4'

lemma c1_3 : dis7 3 (X ^ 2 * Qpoly7) = -3*X^3*xQ*zQ^4 + X^2*zQ + 4*X*xQ^2 + 5*X*yQ^4 + xQ^5*yQ := cls1_eq3 hg1' hg2' hg3' hg4'

lemma c1_4 : dis7 4 (X ^ 2 * Qpoly7) = X^4*zQ^6 - 3*X^2*xQ*zQ^2 + 14*X*xQ*yQ - 10*X*yQ^3 + 2*xQ^5 := cls1_eq4 hg1' hg2' hg3' hg4'

lemma c1_5 : dis7 5 (X ^ 2 * Qpoly7) = 5*X^3*zQ^4 + X*xQ + X*yQ^5*zQ + 4*X*yQ^2 + 3*xQ^4*yQ := cls1_eq5 hg1' hg2' hg3' hg4'

lemma c1_6 : dis7 6 (X ^ 2 * Qpoly7) = -X^3*xQ*zQ^5 + 4*X^2*zQ^2 - 3*X*yQ^4*zQ - X*yQ + 5*xQ^4 := cls1_eq6 hg1' hg2' hg3' hg4'

lemma c2_0 : dis7 0 ((X ^ 2 * Qpoly7) ^ 2) = -10*X^8*xQ*zQ^10 + 221*X^7*zQ^7 - 38*X^5*xQ*zQ^3 + 38*X^4*yQ^3*zQ - 554*X^4 + 38*X^3*xQ^3*yQ - 10*X^3*yQ^10*zQ - 221*X^3*yQ^7 + 221*X^2*xQ^7 + 10*X*xQ^10*yQ :=
  cls2_eq0 hg1' hg2' hg3' hg4' (by rw [pow_one]; exact c1_0) (by rw [pow_one]; exact c1_1) (by rw [pow_one]; exact c1_2) (by rw [pow_one]; exact c1_3) (by rw [pow_one]; exact c1_4) (by rw [pow_one]; exact c1_5) (by rw [pow_one]; exact c1_6) c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c2_1 : dis7 1 ((X ^ 2 * Qpoly7) ^ 2) = X^9*zQ^12 - 82*X^7*xQ*zQ^8 + 267*X^6*zQ^5 + 533*X^4*xQ*zQ - 27*X^4*yQ^2*zQ - 314*X^3*xQ^3 + 36*X^3*yQ^9*zQ + 264*X^3*yQ^6 + 232*X^2*xQ^6*yQ + 20*X*xQ^10 :=
  cls2_eq1 hg1' hg2' hg3' hg4' (by rw [pow_one]; exact c1_0) (by rw [pow_one]; exact c1_1) (by rw [pow_one]; exact c1_2) (by rw [pow_one]; exact c1_3) (by rw [pow_one]; exact c1_4) (by rw [pow_one]; exact c1_5) (by rw [pow_one]; exact c1_6) c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c2_2 : dis7 2 ((X ^ 2 * Qpoly7) ^ 2) = 20*X^8*zQ^10 - 232*X^6*xQ*zQ^6 - 314*X^5*zQ^3 - 533*X^4*yQ*zQ + 27*X^3*xQ^2*yQ - 82*X^3*yQ^8*zQ - 267*X^3*yQ^5 + 264*X^2*xQ^6 + X^2*yQ^12 + 36*X*xQ^9*yQ :=
  cls2_eq2 hg1' hg2' hg3' hg4' (by rw [pow_one]; exact c1_0) (by rw [pow_one]; exact c1_1) (by rw [pow_one]; exact c1_2) (by rw [pow_one]; exact c1_3) (by rw [pow_one]; exact c1_4) (by rw [pow_one]; exact c1_5) (by rw [pow_one]; exact c1_6) c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c2_3 : dis7 3 ((X ^ 2 * Qpoly7) ^ 2) = -2*X^8*xQ*zQ^11 + 131*X^7*zQ^8 - 109*X^5*xQ*zQ^4 - 338*X^4*zQ + 48*X^3*xQ^2 + 165*X^3*yQ^7*zQ - 21*X^3*yQ^4 + 150*X^2*xQ^5*yQ - 5*X^2*yQ^11 + 65*X*xQ^9 :=
  cls2_eq3 hg1' hg2' hg3' hg4' (by rw [pow_one]; exact c1_0) (by rw [pow_one]; exact c1_1) (by rw [pow_one]; exact c1_2) (by rw [pow_one]; exact c1_3) (by rw [pow_one]; exact c1_4) (by rw [pow_one]; exact c1_5) (by rw [pow_one]; exact c1_6) c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c2_4 : dis7 4 ((X ^ 2 * Qpoly7) ^ 2) = -36*X^7*xQ*zQ^9 + 264*X^6*zQ^6 - 27*X^4*xQ*zQ^2 - 533*X^3*xQ*yQ - 232*X^3*yQ^6*zQ + 314*X^3*yQ^3 + 267*X^2*xQ^5 + 20*X^2*yQ^10 + 82*X*xQ^8*yQ + xQ^12 :=
  cls2_eq4 hg1' hg2' hg3' hg4' (by rw [pow_one]; exact c1_0) (by rw [pow_one]; exact c1_1) (by rw [pow_one]; exact c1_2) (by rw [pow_one]; exact c1_3) (by rw [pow_one]; exact c1_4) (by rw [pow_one]; exact c1_5) (by rw [pow_one]; exact c1_6) c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c2_5 : dis7 5 ((X ^ 2 * Qpoly7) ^ 2) = 5*X^8*zQ^11 - 165*X^6*xQ*zQ^7 - 21*X^5*zQ^4 - 338*X^3*xQ + 150*X^3*yQ^5*zQ + 48*X^3*yQ^2 + 109*X^2*xQ^4*yQ - 65*X^2*yQ^9 + 131*X*xQ^8 + 2*xQ^11*yQ :=
  cls2_eq5 hg1' hg2' hg3' hg4' (by rw [pow_one]; exact c1_0) (by rw [pow_one]; exact c1_1) (by rw [pow_one]; exact c1_2) (by rw [pow_one]; exact c1_3) (by rw [pow_one]; exact c1_4) (by rw [pow_one]; exact c1_5) (by rw [pow_one]; exact c1_6) c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c2_6 : dis7 6 ((X ^ 2 * Qpoly7) ^ 2) = 65*X^7*zQ^9 - 150*X^5*xQ*zQ^5 + 48*X^4*zQ^2 - 109*X^3*yQ^4*zQ + 338*X^3*yQ - 21*X^2*xQ^4 + 2*X^2*yQ^11*zQ + 131*X^2*yQ^8 + 165*X*xQ^7*yQ + 5*xQ^11 :=
  cls2_eq6 hg1' hg2' hg3' hg4' (by rw [pow_one]; exact c1_0) (by rw [pow_one]; exact c1_1) (by rw [pow_one]; exact c1_2) (by rw [pow_one]; exact c1_3) (by rw [pow_one]; exact c1_4) (by rw [pow_one]; exact c1_5) (by rw [pow_one]; exact c1_6) c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c3_0 : dis7 0 ((X ^ 2 * Qpoly7) ^ 3) = -3*X^13*xQ*zQ^17 + 687*X^12*zQ^14 - 6868*X^10*xQ*zQ^10 + 245*X^9*zQ^7 + 552*X^7*xQ*zQ^3 - 552*X^6*yQ^3*zQ - 20365*X^6 - 552*X^5*xQ^3*yQ - 6868*X^5*yQ^10*zQ - 245*X^5*yQ^7 + 245*X^4*xQ^7 + 3*X^4*yQ^17*zQ + 687*X^4*yQ^14 + 6868*X^3*xQ^10*yQ + 687*X^2*xQ^14 + 3*X*xQ^17*yQ :=
  cls3_eq0 hg1' hg2' hg3' hg4' c2_0 c2_1 c2_2 c2_3 c2_4 c2_5 c2_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c3_1 : dis7 1 ((X ^ 2 * Qpoly7) ^ 3) = -108*X^12*xQ*zQ^15 + 3656*X^11*zQ^12 - 4983*X^9*xQ*zQ^8 - 13905*X^8*zQ^5 - 5373*X^6*xQ*zQ + 1620*X^6*yQ^2*zQ - 12218*X^5*xQ^3 + 7524*X^5*yQ^9*zQ - 7220*X^5*yQ^6 - 6075*X^4*xQ^6*yQ - 22*X^4*yQ^16*zQ - 1760*X^4*yQ^13 + 8340*X^3*xQ^10 + 1110*X^2*xQ^13*yQ + 9*X*xQ^17 :=
  cls3_eq1 hg1' hg2' hg3' hg4' c2_0 c2_1 c2_2 c2_3 c2_4 c2_5 c2_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c3_2 : dis7 2 ((X ^ 2 * Qpoly7) ^ 3) = 9*X^13*zQ^17 - 1110*X^11*xQ*zQ^13 + 8340*X^10*zQ^10 + 6075*X^8*xQ*zQ^6 - 12218*X^7*zQ^3 + 5373*X^6*yQ*zQ - 1620*X^5*xQ^2*yQ - 4983*X^5*yQ^8*zQ + 13905*X^5*yQ^5 - 7220*X^4*xQ^6 + 108*X^4*yQ^15*zQ + 3656*X^4*yQ^12 + 7524*X^3*xQ^9*yQ + 1760*X^2*xQ^13 + 22*X*xQ^16*yQ :=
  cls3_eq2 hg1' hg2' hg3' hg4' c2_0 c2_1 c2_2 c2_3 c2_4 c2_5 c2_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c3_3 : dis7 3 ((X ^ 2 * Qpoly7) ^ 3) = 221*X^12*zQ^15 - 4590*X^10*xQ*zQ^11 + 6579*X^9*zQ^8 + 5362*X^7*xQ*zQ^4 - 14288*X^6*zQ - 15849*X^5*xQ^2 - 1107*X^5*yQ^7*zQ - 14499*X^5*yQ^4 - 5118*X^4*xQ^5*yQ - 387*X^4*yQ^14*zQ - 6228*X^4*yQ^11 + 8416*X^3*xQ^9 + X^3*yQ^18 + 2559*X^2*xQ^12*yQ + 51*X*xQ^16 :=
  cls3_eq3 hg1' hg2' hg3' hg4' c2_0 c2_1 c2_2 c2_3 c2_4 c2_5 c2_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c3_4 : dis7 4 ((X ^ 2 * Qpoly7) ^ 3) = -22*X^12*xQ*zQ^16 + 1760*X^11*zQ^13 - 7524*X^9*xQ*zQ^9 - 7220*X^8*zQ^6 + 1620*X^6*xQ*zQ^2 + 5373*X^5*xQ*yQ + 6075*X^5*yQ^6*zQ + 12218*X^5*yQ^3 - 13905*X^4*xQ^5 + 1110*X^4*yQ^13*zQ + 8340*X^4*yQ^10 + 4983*X^3*xQ^8*yQ - 9*X^3*yQ^17 + 3656*X^2*xQ^12 + 108*X*xQ^15*yQ :=
  cls3_eq4 hg1' hg2' hg3' hg4' c2_0 c2_1 c2_2 c2_3 c2_4 c2_5 c2_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c3_5 : dis7 5 ((X ^ 2 * Qpoly7) ^ 3) = X^13*zQ^18 - 387*X^11*xQ*zQ^14 + 6228*X^10*zQ^11 + 1107*X^8*xQ*zQ^7 - 14499*X^7*zQ^4 - 14288*X^5*xQ - 5118*X^5*yQ^5*zQ - 15849*X^5*yQ^2 - 5362*X^4*xQ^4*yQ - 2559*X^4*yQ^12*zQ - 8416*X^4*yQ^9 + 6579*X^3*xQ^8 + 51*X^3*yQ^16 + 4590*X^2*xQ^11*yQ + 221*X*xQ^15 :=
  cls3_eq5 hg1' hg2' hg3' hg4' c2_0 c2_1 c2_2 c2_3 c2_4 c2_5 c2_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c3_6 : dis7 6 ((X ^ 2 * Qpoly7) ^ 3) = 51*X^12*zQ^16 - 2559*X^10*xQ*zQ^12 + 8416*X^9*zQ^9 + 5118*X^7*xQ*zQ^5 - 15849*X^6*zQ^2 + 5362*X^5*yQ^4*zQ + 14288*X^5*yQ - 14499*X^4*xQ^4 + 4590*X^4*yQ^11*zQ + 6579*X^4*yQ^8 - 1107*X^3*xQ^7*yQ - 221*X^3*yQ^15 + 6228*X^2*xQ^11 + 387*X*xQ^14*yQ + xQ^18 :=
  cls3_eq6 hg1' hg2' hg3' hg4' c2_0 c2_1 c2_2 c2_3 c2_4 c2_5 c2_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c4_0 : dis7 0 ((X ^ 2 * Qpoly7) ^ 4) = 574*X^17*zQ^21 - 34538*X^15*xQ*zQ^17 + 258447*X^14*zQ^14 + 156170*X^12*xQ*zQ^10 - 656670*X^11*zQ^7 - 235928*X^9*xQ*zQ^3 + 235928*X^8*yQ^3*zQ - 686546*X^8 + 235928*X^7*xQ^3*yQ + 156170*X^7*yQ^10*zQ + 656670*X^7*yQ^7 - 656670*X^6*xQ^7 + 34538*X^6*yQ^17*zQ + 258447*X^6*yQ^14 - 156170*X^5*xQ^10*yQ - 574*X^5*yQ^21 + 258447*X^4*xQ^14 + 34538*X^3*xQ^17*yQ + 574*X^2*xQ^21 :=
  cls4_eq0 hg1' hg2' hg3' hg4' c3_0 c3_1 c3_2 c3_3 c3_4 c3_5 c3_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c4_1 : dis7 1 ((X ^ 2 * Qpoly7) ^ 4) = -40*X^17*xQ*zQ^22 + 7948*X^16*zQ^19 - 137160*X^14*xQ*zQ^15 + 245552*X^13*zQ^12 + 469006*X^11*xQ*zQ^8 - 725337*X^10*zQ^5 + 83554*X^8*xQ*zQ - 268309*X^8*yQ^2*zQ - 782021*X^7*xQ^3 - 375648*X^7*yQ^9*zQ - 763722*X^7*yQ^6 - 112272*X^6*xQ^6*yQ - 75064*X^6*yQ^16*zQ - 293916*X^6*yQ^13 - 117027*X^5*xQ^10 + 4*X^5*yQ^23*zQ + 2360*X^5*yQ^20 + 253498*X^4*xQ^13*yQ + 52918*X^3*xQ^17 + 1184*X^2*xQ^20*yQ + X*xQ^24 :=
  cls4_eq1 hg1' hg2' hg3' hg4' c3_0 c3_1 c3_2 c3_3 c3_4 c3_5 c3_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c4_2 : dis7 2 ((X ^ 2 * Qpoly7) ^ 4) = X^18*zQ^24 - 1184*X^16*xQ*zQ^20 + 52918*X^15*zQ^17 - 253498*X^13*xQ*zQ^13 - 117027*X^12*zQ^10 + 112272*X^10*xQ*zQ^6 - 782021*X^9*zQ^3 - 83554*X^8*yQ*zQ + 268309*X^7*xQ^2*yQ + 469006*X^7*yQ^8*zQ + 725337*X^7*yQ^5 - 763722*X^6*xQ^6 + 137160*X^6*yQ^15*zQ + 245552*X^6*yQ^12 - 375648*X^5*xQ^9*yQ - 40*X^5*yQ^22*zQ - 7948*X^5*yQ^19 + 293916*X^4*xQ^13 + 75064*X^3*xQ^16*yQ + 2360*X^2*xQ^20 + 4*X*xQ^23*yQ :=
  cls4_eq2 hg1' hg2' hg3' hg4' c3_0 c3_1 c3_2 c3_3 c3_4 c3_5 c3_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c4_3 : dis7 3 ((X ^ 2 * Qpoly7) ^ 4) = 105*X^17*zQ^22 - 13538*X^15*xQ*zQ^18 + 180705*X^14*zQ^15 - 87899*X^12*xQ*zQ^11 - 535080*X^11*zQ^8 - 120484*X^9*xQ*zQ^4 - 446376*X^8*zQ - 425768*X^7*xQ^2 - 362593*X^7*yQ^7*zQ - 783776*X^7*yQ^4 + 6377*X^6*xQ^5*yQ - 207914*X^6*yQ^14*zQ - 99568*X^6*yQ^11 - 336385*X^5*xQ^9 + 252*X^5*yQ^21*zQ + 22337*X^5*yQ^18 + 224294*X^4*xQ^12*yQ + 106421*X^3*xQ^16 + 4410*X^2*xQ^19*yQ + 14*X*xQ^23 :=
  cls4_eq3 hg1' hg2' hg3' hg4' c3_0 c3_1 c3_2 c3_3 c3_4 c3_5 c3_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c4_4 : dis7 4 ((X ^ 2 * Qpoly7) ^ 4) = -4*X^17*xQ*zQ^23 + 2360*X^16*zQ^20 - 75064*X^14*xQ*zQ^16 + 293916*X^13*zQ^13 + 375648*X^11*xQ*zQ^9 - 763722*X^10*zQ^6 - 268309*X^8*xQ*zQ^2 - 83554*X^7*xQ*yQ + 112272*X^7*yQ^6*zQ + 782021*X^7*yQ^3 - 725337*X^6*xQ^5 + 253498*X^6*yQ^13*zQ - 117027*X^6*yQ^10 - 469006*X^5*xQ^8*yQ - 1184*X^5*yQ^20*zQ - 52918*X^5*yQ^17 + 245552*X^4*xQ^12 + X^4*yQ^24 + 137160*X^3*xQ^15*yQ + 7948*X^2*xQ^19 + 40*X*xQ^22*yQ :=
  cls4_eq4 hg1' hg2' hg3' hg4' c3_0 c3_1 c3_2 c3_3 c3_4 c3_5 c3_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c4_5 : dis7 5 ((X ^ 2 * Qpoly7) ^ 4) = -252*X^16*xQ*zQ^21 + 22337*X^15*zQ^18 - 207914*X^13*xQ*zQ^14 + 99568*X^12*zQ^11 + 362593*X^10*xQ*zQ^7 - 783776*X^9*zQ^4 - 446376*X^7*xQ + 6377*X^7*yQ^5*zQ - 425768*X^7*yQ^2 + 120484*X^6*xQ^4*yQ - 224294*X^6*yQ^12*zQ + 336385*X^6*yQ^9 - 535080*X^5*xQ^8 + 4410*X^5*yQ^19*zQ + 106421*X^5*yQ^16 + 87899*X^4*xQ^11*yQ - 14*X^4*yQ^23 + 180705*X^3*xQ^15 + 13538*X^2*xQ^18*yQ + 105*X*xQ^22 :=
  cls4_eq5 hg1' hg2' hg3' hg4' c3_0 c3_1 c3_2 c3_3 c3_4 c3_5 c3_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c4_6 : dis7 6 ((X ^ 2 * Qpoly7) ^ 4) = 14*X^17*zQ^23 - 4410*X^15*xQ*zQ^19 + 106421*X^14*zQ^16 - 224294*X^12*xQ*zQ^12 - 336385*X^11*zQ^9 - 6377*X^9*xQ*zQ^5 - 425768*X^8*zQ^2 - 120484*X^7*yQ^4*zQ + 446376*X^7*yQ - 783776*X^6*xQ^4 + 87899*X^6*yQ^11*zQ - 535080*X^6*yQ^8 - 362593*X^5*xQ^7*yQ - 13538*X^5*yQ^18*zQ - 180705*X^5*yQ^15 + 99568*X^4*xQ^11 + 105*X^4*yQ^22 + 207914*X^3*xQ^14*yQ + 22337*X^2*xQ^18 + 252*X*xQ^21*yQ :=
  cls4_eq6 hg1' hg2' hg3' hg4' c3_0 c3_1 c3_2 c3_3 c3_4 c3_5 c3_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c5_0 : dis7 0 ((X ^ 2 * Qpoly7) ^ 5) = 190*X^22*zQ^28 - 50585*X^20*xQ*zQ^24 + 1616615*X^19*zQ^21 - 8221167*X^17*xQ*zQ^17 - 2222909*X^16*zQ^14 + 20193158*X^14*xQ*zQ^10 - 25190336*X^13*zQ^7 - 19153921*X^11*xQ*zQ^3 + 19153921*X^10*yQ^3*zQ - 7503571*X^10 + 19153921*X^9*xQ^3*yQ + 20193158*X^9*yQ^10*zQ + 25190336*X^9*yQ^7 - 25190336*X^8*xQ^7 + 8221167*X^8*yQ^17*zQ - 2222909*X^8*yQ^14 - 20193158*X^7*xQ^10*yQ - 50585*X^7*yQ^24*zQ - 1616615*X^7*yQ^21 - 2222909*X^6*xQ^14 + 190*X^6*yQ^28 + 8221167*X^5*xQ^17*yQ + 1616615*X^4*xQ^21 + 50585*X^3*xQ^24*yQ + 190*X^2*xQ^28 :=
  cls5_eq0 hg1' hg2' hg3' hg4' c4_0 c4_1 c4_2 c4_3 c4_4 c4_5 c4_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c5_1 : dis7 1 ((X ^ 2 * Qpoly7) ^ 5) = -5*X^22*xQ*zQ^29 + 6420*X^21*zQ^26 - 449868*X^19*xQ*zQ^22 + 5435584*X^18*zQ^19 - 5133053*X^16*xQ*zQ^15 - 19316691*X^15*zQ^12 + 3117356*X^13*xQ*zQ^8 - 47283404*X^12*zQ^5 - 45696389*X^10*xQ*zQ - 2387745*X^10*yQ^2*zQ - 20909137*X^9*xQ^3 - 12965783*X^9*yQ^9*zQ - 30149423*X^9*yQ^6 + 4049798*X^8*xQ^6*yQ - 8275520*X^8*yQ^16*zQ + 11237025*X^8*yQ^13 - 25467754*X^7*xQ^10 + 162415*X^7*yQ^23*zQ + 3183180*X^7*yQ^20 - 10935764*X^6*xQ^13*yQ - 1265*X^6*yQ^27 + 9735946*X^5*xQ^17 + 2257726*X^4*xQ^20*yQ + 92828*X^3*xQ^24 + 506*X^2*xQ^27*yQ :=
  cls5_eq1 hg1' hg2' hg3' hg4' c4_0 c4_1 c4_2 c4_3 c4_4 c4_5 c4_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c5_2 : dis7 2 ((X ^ 2 * Qpoly7) ^ 5) = -506*X^21*xQ*zQ^27 + 92828*X^20*zQ^24 - 2257726*X^18*xQ*zQ^20 + 9735946*X^17*zQ^17 + 10935764*X^15*xQ*zQ^13 - 25467754*X^14*zQ^10 - 4049798*X^12*xQ*zQ^6 - 20909137*X^11*zQ^3 + 45696389*X^10*yQ*zQ + 2387745*X^9*xQ^2*yQ + 3117356*X^9*yQ^8*zQ + 47283404*X^9*yQ^5 - 30149423*X^8*xQ^6 + 5133053*X^8*yQ^15*zQ - 19316691*X^8*yQ^12 - 12965783*X^7*xQ^9*yQ - 449868*X^7*yQ^22*zQ - 5435584*X^7*yQ^19 - 11237025*X^6*xQ^13 + 5*X^6*yQ^29*zQ + 6420*X^6*yQ^26 + 8275520*X^5*xQ^16*yQ + 3183180*X^4*xQ^20 + 162415*X^3*xQ^23*yQ + 1265*X^2*xQ^27 :=
  cls5_eq2 hg1' hg2' hg3' hg4' c4_0 c4_1 c4_2 c4_3 c4_4 c4_5 c4_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c5_3 : dis7 3 ((X ^ 2 * Qpoly7) ^ 5) = 20*X^22*zQ^29 - 13345*X^20*xQ*zQ^25 + 717055*X^19*zQ^22 - 6348450*X^17*xQ*zQ^18 + 5268455*X^16*zQ^15 + 22752700*X^14*xQ*zQ^11 - 27790890*X^13*zQ^8 - 34879802*X^11*xQ*zQ^4 - 30767181*X^10*zQ - 29480543*X^9*xQ^2 + 1298649*X^9*yQ^7*zQ - 37781798*X^9*yQ^4 + 24021998*X^8*xQ^5*yQ + 1703115*X^8*yQ^14*zQ + 24043425*X^8*yQ^11 - 27365196*X^7*xQ^9 + 1081050*X^7*yQ^21*zQ + 7959600*X^7*yQ^18 - 19034507*X^6*xQ^12*yQ - 65*X^6*yQ^28*zQ - 26607*X^6*yQ^25 + 9242165*X^5*xQ^16 + 4091025*X^4*xQ^19*yQ + 277080*X^3*xQ^23 + 2920*X^2*xQ^26*yQ + X*xQ^30 :=
  cls5_eq3 hg1' hg2' hg3' hg4' c4_0 c4_1 c4_2 c4_3 c4_4 c4_5 c4_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c5_4 : dis7 4 ((X ^ 2 * Qpoly7) ^ 5) = 1265*X^21*zQ^27 - 162415*X^19*xQ*zQ^23 + 3183180*X^18*zQ^20 - 8275520*X^16*xQ*zQ^16 - 11237025*X^15*zQ^13 + 12965783*X^13*xQ*zQ^9 - 30149423*X^12*zQ^6 - 2387745*X^10*xQ*zQ^2 + 45696389*X^9*xQ*yQ - 4049798*X^9*yQ^6*zQ + 20909137*X^9*yQ^3 - 47283404*X^8*xQ^5 - 10935764*X^8*yQ^13*zQ - 25467754*X^8*yQ^10 - 3117356*X^7*xQ^8*yQ - 2257726*X^7*yQ^20*zQ - 9735946*X^7*yQ^17 - 19316691*X^6*xQ^12 + 506*X^6*yQ^27*zQ + 92828*X^6*yQ^24 + 5133053*X^5*xQ^15*yQ + 5435584*X^4*xQ^19 + 449868*X^3*xQ^22*yQ + 6420*X^2*xQ^26 + 5*X*xQ^29*yQ :=
  cls5_eq4 hg1' hg2' hg3' hg4' c4_0 c4_1 c4_2 c4_3 c4_4 c4_5 c4_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c5_5 : dis7 5 ((X ^ 2 * Qpoly7) ^ 5) = -65*X^21*xQ*zQ^28 + 26607*X^20*zQ^25 - 1081050*X^18*xQ*zQ^21 + 7959600*X^17*zQ^18 + 1703115*X^15*xQ*zQ^14 - 24043425*X^14*zQ^11 - 1298649*X^12*xQ*zQ^7 - 37781798*X^11*zQ^4 - 30767181*X^9*xQ + 24021998*X^9*yQ^5*zQ - 29480543*X^9*yQ^2 + 34879802*X^8*xQ^4*yQ + 19034507*X^8*yQ^12*zQ + 27365196*X^8*yQ^9 - 27790890*X^7*xQ^8 + 4091025*X^7*yQ^19*zQ + 9242165*X^7*yQ^16 - 22752700*X^6*xQ^11*yQ - 2920*X^6*yQ^26*zQ - 277080*X^6*yQ^23 + 5268455*X^5*xQ^15 + X^5*yQ^30 + 6348450*X^4*xQ^18*yQ + 717055*X^3*xQ^22 + 13345*X^2*xQ^25*yQ + 20*X*xQ^29 :=
  cls5_eq5 hg1' hg2' hg3' hg4' c4_0 c4_1 c4_2 c4_3 c4_4 c4_5 c4_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c5_6 : dis7 6 ((X ^ 2 * Qpoly7) ^ 5) = X^22*zQ^30 - 2920*X^20*xQ*zQ^26 + 277080*X^19*zQ^23 - 4091025*X^17*xQ*zQ^19 + 9242165*X^16*zQ^16 + 19034507*X^14*xQ*zQ^12 - 27365196*X^13*zQ^9 - 24021998*X^11*xQ*zQ^5 - 29480543*X^10*zQ^2 - 34879802*X^9*yQ^4*zQ + 30767181*X^9*yQ - 37781798*X^8*xQ^4 - 22752700*X^8*yQ^11*zQ - 27790890*X^8*yQ^8 + 1298649*X^7*xQ^7*yQ - 6348450*X^7*yQ^18*zQ - 5268455*X^7*yQ^15 - 24043425*X^6*xQ^11 + 13345*X^6*yQ^25*zQ + 717055*X^6*yQ^22 - 1703115*X^5*xQ^14*yQ - 20*X^5*yQ^29 + 7959600*X^4*xQ^18 + 1081050*X^3*xQ^21*yQ + 26607*X^2*xQ^25 + 65*X*xQ^28*yQ :=
  cls5_eq6 hg1' hg2' hg3' hg4' c4_0 c4_1 c4_2 c4_3 c4_4 c4_5 c4_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c6_0 : dis7 0 ((X ^ 2 * Qpoly7) ^ 6) = 27*X^27*zQ^35 - 34039*X^25*xQ*zQ^31 + 3406628*X^24*zQ^28 - 68839839*X^22*xQ*zQ^24 + 315705410*X^21*zQ^21 + 284628408*X^19*xQ*zQ^17 - 1111296762*X^18*zQ^14 + 14571298*X^16*xQ*zQ^10 - 1905729875*X^15*zQ^7 - 2139849828*X^13*xQ*zQ^3 + 2139849828*X^12*yQ^3*zQ + 361326901*X^12 + 2139849828*X^11*xQ^3*yQ + 14571298*X^11*yQ^10*zQ + 1905729875*X^11*yQ^7 - 1905729875*X^10*xQ^7 - 284628408*X^10*yQ^17*zQ - 1111296762*X^10*yQ^14 - 14571298*X^9*xQ^10*yQ - 68839839*X^9*yQ^24*zQ - 315705410*X^9*yQ^21 - 1111296762*X^8*xQ^14 + 34039*X^8*yQ^31*zQ + 3406628*X^8*yQ^28 - 284628408*X^7*xQ^17*yQ - 27*X^7*yQ^35 + 315705410*X^6*xQ^21 + 68839839*X^5*xQ^24*yQ + 3406628*X^4*xQ^28 + 34039*X^3*xQ^31*yQ + 27*X^2*xQ^35 :=
  cls6_eq0 hg1' hg2' hg3' hg4' c5_0 c5_1 c5_2 c5_3 c5_4 c5_5 c5_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c6_1 : dis7 1 ((X ^ 2 * Qpoly7) ^ 6) = 2492*X^26*zQ^33 - 586152*X^24*xQ*zQ^29 + 22966062*X^23*zQ^26 - 194523294*X^21*xQ*zQ^22 + 229674480*X^20*zQ^19 + 901671288*X^18*xQ*zQ^15 - 890549352*X^17*zQ^12 - 417785991*X^15*xQ*zQ^8 - 1999178181*X^14*zQ^5 - 702364782*X^12*xQ*zQ - 2161105065*X^12*yQ^2*zQ - 1785456260*X^11*xQ^3 + 173688627*X^11*yQ^9*zQ - 2466944445*X^11*yQ^6 + 2237702082*X^10*xQ^6*yQ + 632893086*X^10*yQ^16*zQ + 1049102355*X^10*yQ^13 - 710626798*X^9*xQ^10 + 123778830*X^9*yQ^23*zQ + 326154738*X^9*yQ^20 - 861056819*X^8*xQ^13*yQ - 152964*X^8*yQ^30*zQ - 9387812*X^8*yQ^27 - 342359661*X^7*xQ^17 + 315*X^7*yQ^34 + 286025754*X^6*xQ^20*yQ + 96650162*X^5*xQ^24 + 5703726*X^4*xQ^27*yQ + 73780*X^3*xQ^31 + 98*X^2*xQ^34*yQ :=
  cls6_eq1 hg1' hg2' hg3' hg4' c5_0 c5_1 c5_2 c5_3 c5_4 c5_5 c5_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c6_2 : dis7 2 ((X ^ 2 * Qpoly7) ^ 6) = -98*X^26*xQ*zQ^34 + 73780*X^25*zQ^31 - 5703726*X^23*xQ*zQ^27 + 96650162*X^22*zQ^24 - 286025754*X^20*xQ*zQ^20 - 342359661*X^19*zQ^17 + 861056819*X^17*xQ*zQ^13 - 710626798*X^16*zQ^10 - 2237702082*X^14*xQ*zQ^6 - 1785456260*X^13*zQ^3 + 702364782*X^12*yQ*zQ + 2161105065*X^11*xQ^2*yQ - 417785991*X^11*yQ^8*zQ + 1999178181*X^11*yQ^5 - 2466944445*X^10*xQ^6 - 901671288*X^10*yQ^15*zQ - 890549352*X^10*yQ^12 + 173688627*X^9*xQ^9*yQ - 194523294*X^9*yQ^22*zQ - 229674480*X^9*yQ^19 - 1049102355*X^8*xQ^13 + 586152*X^8*yQ^29*zQ + 22966062*X^8*yQ^26 - 632893086*X^7*xQ^16*yQ - 2492*X^7*yQ^33 + 326154738*X^6*xQ^20 + 123778830*X^5*xQ^23*yQ + 9387812*X^4*xQ^27 + 152964*X^3*xQ^30*yQ + 315*X^2*xQ^34 :=
  cls6_eq2 hg1' hg2' hg3' hg4' c5_0 c5_1 c5_2 c5_3 c5_4 c5_5 c5_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c6_3 : dis7 3 ((X ^ 2 * Qpoly7) ^ 6) = X^27*zQ^36 - 6288*X^25*xQ*zQ^32 + 1091103*X^24*zQ^29 - 33823015*X^22*xQ*zQ^25 + 247212407*X^21*zQ^22 - 24655071*X^19*xQ*zQ^18 - 995175249*X^18*zQ^15 + 301902174*X^16*xQ*zQ^11 - 976619829*X^15*zQ^8 - 1913139073*X^13*xQ*zQ^4 - 877937056*X^12*zQ - 1106674074*X^11*xQ^2 + 1241159460*X^11*yQ^7*zQ - 2184496524*X^11*yQ^4 + 2069678571*X^10*xQ^5*yQ + 983817366*X^10*yQ^14*zQ + 775514889*X^10*yQ^11 - 644915759*X^9*xQ^9 + 261484611*X^9*yQ^21*zQ - 1131153*X^9*yQ^18 - 615028059*X^8*xQ^12*yQ - 1951050*X^8*yQ^28*zQ - 49975527*X^8*yQ^25 - 709020541*X^7*xQ^16 + 6*X^7*yQ^35*zQ + 15027*X^7*yQ^32 + 218510680*X^6*xQ^19*yQ + 165336636*X^5*xQ^23 + 14742630*X^4*xQ^26*yQ + 305693*X^3*xQ^30 + 918*X^2*xQ^33*yQ :=
  cls6_eq3 hg1' hg2' hg3' hg4' c5_0 c5_1 c5_2 c5_3 c5_4 c5_5 c5_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c6_4 : dis7 4 ((X ^ 2 * Qpoly7) ^ 6) = 315*X^26*zQ^34 - 152964*X^24*xQ*zQ^30 + 9387812*X^23*zQ^27 - 123778830*X^21*xQ*zQ^23 + 326154738*X^20*zQ^20 + 632893086*X^18*xQ*zQ^16 - 1049102355*X^17*zQ^13 - 173688627*X^15*xQ*zQ^9 - 2466944445*X^14*zQ^6 - 2161105065*X^12*xQ*zQ^2 + 702364782*X^11*xQ*yQ - 2237702082*X^11*yQ^6*zQ + 1785456260*X^11*yQ^3 - 1999178181*X^10*xQ^5 - 861056819*X^10*yQ^13*zQ - 710626798*X^10*yQ^10 + 417785991*X^9*xQ^8*yQ - 286025754*X^9*yQ^20*zQ + 342359661*X^9*yQ^17 - 890549352*X^8*xQ^12 + 5703726*X^8*yQ^27*zQ + 96650162*X^8*yQ^24 - 901671288*X^7*xQ^15*yQ - 98*X^7*yQ^34*zQ - 73780*X^7*yQ^31 + 229674480*X^6*xQ^19 + 194523294*X^5*xQ^22*yQ + 22966062*X^4*xQ^26 + 586152*X^3*xQ^29*yQ + 2492*X^2*xQ^33 :=
  cls6_eq4 hg1' hg2' hg3' hg4' c5_0 c5_1 c5_2 c5_3 c5_4 c5_5 c5_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c6_5 : dis7 5 ((X ^ 2 * Qpoly7) ^ 6) = -6*X^26*xQ*zQ^35 + 15027*X^25*zQ^32 - 1951050*X^23*xQ*zQ^28 + 49975527*X^22*zQ^25 - 261484611*X^20*xQ*zQ^21 - 1131153*X^19*zQ^18 + 983817366*X^17*xQ*zQ^14 - 775514889*X^16*zQ^11 - 1241159460*X^14*xQ*zQ^7 - 2184496524*X^13*zQ^4 - 877937056*X^11*xQ + 2069678571*X^11*yQ^5*zQ - 1106674074*X^11*yQ^2 + 1913139073*X^10*xQ^4*yQ + 615028059*X^10*yQ^12*zQ + 644915759*X^10*yQ^9 - 976619829*X^9*xQ^8 + 218510680*X^9*yQ^19*zQ - 709020541*X^9*yQ^16 - 301902174*X^8*xQ^11*yQ - 14742630*X^8*yQ^26*zQ - 165336636*X^8*yQ^23 - 995175249*X^7*xQ^15 + 918*X^7*yQ^33*zQ + 305693*X^7*yQ^30 + 24655071*X^6*xQ^18*yQ + 247212407*X^5*xQ^22 + 33823015*X^4*xQ^25*yQ + 1091103*X^3*xQ^29 + 6288*X^2*xQ^32*yQ + X*xQ^36 :=
  cls6_eq5 hg1' hg2' hg3' hg4' c5_0 c5_1 c5_2 c5_3 c5_4 c5_5 c5_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6

lemma c6_6 : dis7 6 ((X ^ 2 * Qpoly7) ^ 6) = -918*X^25*xQ*zQ^33 + 305693*X^24*zQ^30 - 14742630*X^22*xQ*zQ^26 + 165336636*X^21*zQ^23 - 218510680*X^19*xQ*zQ^19 - 709020541*X^18*zQ^16 + 615028059*X^16*xQ*zQ^12 - 644915759*X^15*zQ^9 - 2069678571*X^13*xQ*zQ^5 - 1106674074*X^12*zQ^2 - 1913139073*X^11*yQ^4*zQ + 877937056*X^11*yQ - 2184496524*X^10*xQ^4 - 301902174*X^10*yQ^11*zQ - 976619829*X^10*yQ^8 + 1241159460*X^9*xQ^7*yQ - 24655071*X^9*yQ^18*zQ + 995175249*X^9*yQ^15 - 775514889*X^8*xQ^11 + 33823015*X^8*yQ^25*zQ + 247212407*X^8*yQ^22 - 983817366*X^7*xQ^14*yQ - 6288*X^7*yQ^32*zQ - 1091103*X^7*yQ^29 - 1131153*X^6*xQ^18 + X^6*yQ^36 + 261484611*X^5*xQ^21*yQ + 49975527*X^4*xQ^25 + 1951050*X^3*xQ^28*yQ + 15027*X^2*xQ^32 + 6*X*xQ^35*yQ :=
  cls6_eq6 hg1' hg2' hg3' hg4' c5_0 c5_1 c5_2 c5_3 c5_4 c5_5 c5_6 c1_0 c1_1 c1_2 c1_3 c1_4 c1_5 c1_6


lemma isUnit_Fser : IsUnit Fser := by
  have h := eQ7_pow4_mul_Fser
  have hu : IsUnit (eQ7 ^ 4 * Fser) := by rw [h]; exact isUnit_qfacInf.pow 4
  exact isUnit_of_mul_isUnit_right hu

lemma Fser_mul_inv : Fser * Ring.inverse Fser = 1 := Ring.mul_inverse_cancel _ isUnit_Fser

lemma inv_Nser : Ring.inverse Nser = Ring.inverse Fser ^ 2 := by
  rw [← Fser_sq, Ring.inverse_pow]

/-- `y = q²E(q⁴⁹)/E(q)`. -/
noncomputable def Y7 : PowerSeries ℤ := E7 (Ring.inverse Nser) * (X ^ 2 * Qpoly7)

/-- `τ = qE(q⁷)⁴/E(q)⁴ = q/F`. -/
noncomputable def tau7 : PowerSeries ℤ := X * Ring.inverse Fser


lemma dis7_one : dis7 0 (1 : PowerSeries ℤ) = 1 := by
  ext n; rw [dis7, coeff_mk, coeff_one, coeff_one, add_zero]
  by_cases h : n = 0 <;> simp [h]

lemma dis7_C_mul (r : ℕ) (a : ℤ) (F : PowerSeries ℤ) : dis7 r (C a * F) = C a * dis7 r F := by
  ext n; rw [dis7, dis7, coeff_mk, coeff_C_mul, coeff_C_mul, coeff_mk]


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma Y7_base1 : dis7 0 (Y7 ^ 1) = (0 : PowerSeries ℤ) * tau7 ^ 0 + (7 : PowerSeries ℤ) * tau7 ^ 1 + (49 : PowerSeries ℤ) * tau7 ^ 2 := by
  rw [Y7, mul_pow, ← map_pow, dis7_E7_mul 0 (by norm_num), pow_one, pow_one, c1_0, c0_target1 hg1' hg2' hg3' hg4', inv_Nser, tau7]
  linear_combination ((7 : PowerSeries ℤ) * X ^ 1 * Ring.inverse Fser ^ 1 * ((Fser * Ring.inverse Fser) ^ 0) + (49 : PowerSeries ℤ) * X ^ 2 * Ring.inverse Fser ^ 2 * (0)) * Fser_mul_inv


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma Y7_base2 : dis7 0 (Y7 ^ 2) = (0 : PowerSeries ℤ) * tau7 ^ 0 + (10 : PowerSeries ℤ) * tau7 ^ 1 + (441 : PowerSeries ℤ) * tau7 ^ 2 + (4802 : PowerSeries ℤ) * tau7 ^ 3 + (16807 : PowerSeries ℤ) * tau7 ^ 4 := by
  rw [Y7, mul_pow, ← map_pow, dis7_E7_mul 0 (by norm_num), c2_0, c0_target2 hg1' hg2' hg3' hg4', inv_Nser, tau7]
  linear_combination ((10 : PowerSeries ℤ) * X ^ 1 * Ring.inverse Fser ^ 1 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2) + (441 : PowerSeries ℤ) * X ^ 2 * Ring.inverse Fser ^ 2 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1) + (4802 : PowerSeries ℤ) * X ^ 3 * Ring.inverse Fser ^ 3 * ((Fser * Ring.inverse Fser) ^ 0) + (16807 : PowerSeries ℤ) * X ^ 4 * Ring.inverse Fser ^ 4 * (0)) * Fser_mul_inv


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma Y7_base3 : dis7 0 (Y7 ^ 3) = (0 : PowerSeries ℤ) * tau7 ^ 0 + (3 : PowerSeries ℤ) * tau7 ^ 1 + (798 : PowerSeries ℤ) * tau7 ^ 2 + (29155 : PowerSeries ℤ) * tau7 ^ 3 + (403368 : PowerSeries ℤ) * tau7 ^ 4 + (2470629 : PowerSeries ℤ) * tau7 ^ 5 + (5764801 : PowerSeries ℤ) * tau7 ^ 6 := by
  rw [Y7, mul_pow, ← map_pow, dis7_E7_mul 0 (by norm_num), c3_0, c0_target3 hg1' hg2' hg3' hg4', inv_Nser, tau7]
  linear_combination ((3 : PowerSeries ℤ) * X ^ 1 * Ring.inverse Fser ^ 1 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2 + (Fser * Ring.inverse Fser) ^ 3 + (Fser * Ring.inverse Fser) ^ 4) + (798 : PowerSeries ℤ) * X ^ 2 * Ring.inverse Fser ^ 2 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2 + (Fser * Ring.inverse Fser) ^ 3) + (29155 : PowerSeries ℤ) * X ^ 3 * Ring.inverse Fser ^ 3 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2) + (403368 : PowerSeries ℤ) * X ^ 4 * Ring.inverse Fser ^ 4 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1) + (2470629 : PowerSeries ℤ) * X ^ 5 * Ring.inverse Fser ^ 5 * ((Fser * Ring.inverse Fser) ^ 0) + (5764801 : PowerSeries ℤ) * X ^ 6 * Ring.inverse Fser ^ 6 * (0)) * Fser_mul_inv


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma Y7_base4 : dis7 0 (Y7 ^ 4) = (0 : PowerSeries ℤ) * tau7 ^ 0 + (0 : PowerSeries ℤ) * tau7 ^ 1 + (574 : PowerSeries ℤ) * tau7 ^ 2 + (60368 : PowerSeries ℤ) * tau7 ^ 3 + (2028845 : PowerSeries ℤ) * tau7 ^ 4 + (32000528 : PowerSeries ℤ) * tau7 ^ 5 + (265180846 : PowerSeries ℤ) * tau7 ^ 6 + (1129900996 : PowerSeries ℤ) * tau7 ^ 7 + (1977326743 : PowerSeries ℤ) * tau7 ^ 8 := by
  rw [Y7, mul_pow, ← map_pow, dis7_E7_mul 0 (by norm_num), c4_0, c0_target4 hg1' hg2' hg3' hg4', inv_Nser, tau7]
  linear_combination ((574 : PowerSeries ℤ) * X ^ 2 * Ring.inverse Fser ^ 2 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2 + (Fser * Ring.inverse Fser) ^ 3 + (Fser * Ring.inverse Fser) ^ 4 + (Fser * Ring.inverse Fser) ^ 5) + (60368 : PowerSeries ℤ) * X ^ 3 * Ring.inverse Fser ^ 3 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2 + (Fser * Ring.inverse Fser) ^ 3 + (Fser * Ring.inverse Fser) ^ 4) + (2028845 : PowerSeries ℤ) * X ^ 4 * Ring.inverse Fser ^ 4 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2 + (Fser * Ring.inverse Fser) ^ 3) + (32000528 : PowerSeries ℤ) * X ^ 5 * Ring.inverse Fser ^ 5 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2) + (265180846 : PowerSeries ℤ) * X ^ 6 * Ring.inverse Fser ^ 6 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1) + (1129900996 : PowerSeries ℤ) * X ^ 7 * Ring.inverse Fser ^ 7 * ((Fser * Ring.inverse Fser) ^ 0) + (1977326743 : PowerSeries ℤ) * X ^ 8 * Ring.inverse Fser ^ 8 * (0)) * Fser_mul_inv


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma Y7_base5 : dis7 0 (Y7 ^ 5) = (0 : PowerSeries ℤ) * tau7 ^ 0 + (0 : PowerSeries ℤ) * tau7 ^ 1 + (190 : PowerSeries ℤ) * tau7 ^ 2 + (61985 : PowerSeries ℤ) * tau7 ^ 3 + (4549895 : PowerSeries ℤ) * tau7 ^ 4 + (145061217 : PowerSeries ℤ) * tau7 ^ 5 + (2491217575 : PowerSeries ℤ) * tau7 ^ 6 + (25019236340 : PowerSeries ℤ) * tau7 ^ 7 + (148299505725 : PowerSeries ℤ) * tau7 ^ 8 + (484445052035 : PowerSeries ℤ) * tau7 ^ 9 + (678223072849 : PowerSeries ℤ) * tau7 ^ 10 := by
  rw [Y7, mul_pow, ← map_pow, dis7_E7_mul 0 (by norm_num), c5_0, c0_target5 hg1' hg2' hg3' hg4', inv_Nser, tau7]
  linear_combination ((190 : PowerSeries ℤ) * X ^ 2 * Ring.inverse Fser ^ 2 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2 + (Fser * Ring.inverse Fser) ^ 3 + (Fser * Ring.inverse Fser) ^ 4 + (Fser * Ring.inverse Fser) ^ 5 + (Fser * Ring.inverse Fser) ^ 6 + (Fser * Ring.inverse Fser) ^ 7) + (61985 : PowerSeries ℤ) * X ^ 3 * Ring.inverse Fser ^ 3 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2 + (Fser * Ring.inverse Fser) ^ 3 + (Fser * Ring.inverse Fser) ^ 4 + (Fser * Ring.inverse Fser) ^ 5 + (Fser * Ring.inverse Fser) ^ 6) + (4549895 : PowerSeries ℤ) * X ^ 4 * Ring.inverse Fser ^ 4 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2 + (Fser * Ring.inverse Fser) ^ 3 + (Fser * Ring.inverse Fser) ^ 4 + (Fser * Ring.inverse Fser) ^ 5) + (145061217 : PowerSeries ℤ) * X ^ 5 * Ring.inverse Fser ^ 5 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2 + (Fser * Ring.inverse Fser) ^ 3 + (Fser * Ring.inverse Fser) ^ 4) + (2491217575 : PowerSeries ℤ) * X ^ 6 * Ring.inverse Fser ^ 6 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2 + (Fser * Ring.inverse Fser) ^ 3) + (25019236340 : PowerSeries ℤ) * X ^ 7 * Ring.inverse Fser ^ 7 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2) + (148299505725 : PowerSeries ℤ) * X ^ 8 * Ring.inverse Fser ^ 8 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1) + (484445052035 : PowerSeries ℤ) * X ^ 9 * Ring.inverse Fser ^ 9 * ((Fser * Ring.inverse Fser) ^ 0) + (678223072849 : PowerSeries ℤ) * X ^ 10 * Ring.inverse Fser ^ 10 * (0)) * Fser_mul_inv


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
lemma Y7_base6 : dis7 0 (Y7 ^ 6) = (0 : PowerSeries ℤ) * tau7 ^ 0 + (0 : PowerSeries ℤ) * tau7 ^ 1 + (27 : PowerSeries ℤ) * tau7 ^ 2 + (36064 : PowerSeries ℤ) * tau7 ^ 3 + (5756226 : PowerSeries ℤ) * tau7 ^ 4 + (343266168 : PowerSeries ℤ) * tau7 ^ 5 + (10561938975 : PowerSeries ℤ) * tau7 ^ 6 + (192486705390 : PowerSeries ℤ) * tau7 ^ 7 + (2211781199670 : PowerSeries ℤ) * tau7 ^ 8 + (16305036322778 : PowerSeries ℤ) * tau7 ^ 9 + (75282761086239 : PowerSeries ℤ) * tau7 ^ 10 + (199397583417606 : PowerSeries ℤ) * tau7 ^ 11 + (232630513987207 : PowerSeries ℤ) * tau7 ^ 12 := by
  rw [Y7, mul_pow, ← map_pow, dis7_E7_mul 0 (by norm_num), c6_0, c0_target6 hg1' hg2' hg3' hg4', inv_Nser, tau7]
  linear_combination ((27 : PowerSeries ℤ) * X ^ 2 * Ring.inverse Fser ^ 2 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2 + (Fser * Ring.inverse Fser) ^ 3 + (Fser * Ring.inverse Fser) ^ 4 + (Fser * Ring.inverse Fser) ^ 5 + (Fser * Ring.inverse Fser) ^ 6 + (Fser * Ring.inverse Fser) ^ 7 + (Fser * Ring.inverse Fser) ^ 8 + (Fser * Ring.inverse Fser) ^ 9) + (36064 : PowerSeries ℤ) * X ^ 3 * Ring.inverse Fser ^ 3 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2 + (Fser * Ring.inverse Fser) ^ 3 + (Fser * Ring.inverse Fser) ^ 4 + (Fser * Ring.inverse Fser) ^ 5 + (Fser * Ring.inverse Fser) ^ 6 + (Fser * Ring.inverse Fser) ^ 7 + (Fser * Ring.inverse Fser) ^ 8) + (5756226 : PowerSeries ℤ) * X ^ 4 * Ring.inverse Fser ^ 4 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2 + (Fser * Ring.inverse Fser) ^ 3 + (Fser * Ring.inverse Fser) ^ 4 + (Fser * Ring.inverse Fser) ^ 5 + (Fser * Ring.inverse Fser) ^ 6 + (Fser * Ring.inverse Fser) ^ 7) + (343266168 : PowerSeries ℤ) * X ^ 5 * Ring.inverse Fser ^ 5 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2 + (Fser * Ring.inverse Fser) ^ 3 + (Fser * Ring.inverse Fser) ^ 4 + (Fser * Ring.inverse Fser) ^ 5 + (Fser * Ring.inverse Fser) ^ 6) + (10561938975 : PowerSeries ℤ) * X ^ 6 * Ring.inverse Fser ^ 6 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2 + (Fser * Ring.inverse Fser) ^ 3 + (Fser * Ring.inverse Fser) ^ 4 + (Fser * Ring.inverse Fser) ^ 5) + (192486705390 : PowerSeries ℤ) * X ^ 7 * Ring.inverse Fser ^ 7 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2 + (Fser * Ring.inverse Fser) ^ 3 + (Fser * Ring.inverse Fser) ^ 4) + (2211781199670 : PowerSeries ℤ) * X ^ 8 * Ring.inverse Fser ^ 8 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2 + (Fser * Ring.inverse Fser) ^ 3) + (16305036322778 : PowerSeries ℤ) * X ^ 9 * Ring.inverse Fser ^ 9 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1 + (Fser * Ring.inverse Fser) ^ 2) + (75282761086239 : PowerSeries ℤ) * X ^ 10 * Ring.inverse Fser ^ 10 * ((Fser * Ring.inverse Fser) ^ 0 + (Fser * Ring.inverse Fser) ^ 1) + (199397583417606 : PowerSeries ℤ) * X ^ 11 * Ring.inverse Fser ^ 11 * ((Fser * Ring.inverse Fser) ^ 0) + (232630513987207 : PowerSeries ℤ) * X ^ 12 * Ring.inverse Fser ^ 12 * (0)) * Fser_mul_inv


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Watson's modular equation of degree 7**. -/
theorem modular7_eq : Y7 ^ 7 = E7 tau7 * (49 * Y7 ^ 6 + 35 * Y7 ^ 5 + 7 * Y7 ^ 4)
    + E7 tau7 ^ 2 * (343 * Y7 ^ 6 + 343 * Y7 ^ 5 + 147 * Y7 ^ 4 + 49 * Y7 ^ 3 + 21 * Y7 ^ 2 + 7 * Y7 + 1) := by
  have h1 : X^7*E7 yQ*E7 zQ^2 - E7 xQ + E7 yQ^2 = 0 := by
    have h := congrArg E7 hg1'
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_zero, E7_X] at h
    linear_combination h
  have h2 : E7 xQ*E7 yQ*E7 zQ - 1 = 0 := by
    have h := congrArg E7 hg2'
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_zero, E7_X] at h
    linear_combination h
  have h3 : X^7*E7 zQ - E7 xQ^2 + E7 xQ*E7 yQ^2 = 0 := by
    have h := congrArg E7 hg3'
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_zero, E7_X] at h
    linear_combination h
  have h4 : -X^7*E7 zQ^2 + E7 xQ^2*E7 zQ - E7 yQ = 0 := by
    have h := congrArg E7 hg4'
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_zero, E7_X] at h
    linear_combination h
  have hpoly := modular7_poly (E7 xQ) (E7 yQ) (E7 zQ) h1 h2 h3 h4
  have hFe : E7 Fser = -X^14*E7 xQ*E7 zQ^3 + X^7*E7 yQ^3*E7 zQ - 8*X^7 + E7 xQ^3*E7 yQ := by
    simp only [Fser, map_add, map_sub, map_mul, map_pow, map_ofNat, E7_X]; ring
  rw [← hFe] at hpoly
  have hyD : Y7 * L7 xQ yQ zQ = X ^ 2 := by
    have hF := factor_mul_Qpoly7
    have hN : E7 Nser * E7 (Ring.inverse Nser) = 1 := by
      rw [← map_mul, Ring.mul_inverse_cancel _ (by rw [← Fser_sq]; exact isUnit_Fser.pow 2), map_one]
    rw [Y7]; linear_combination X ^ 2 * E7 (Ring.inverse Nser) * hF + X ^ 2 * hN
  have hFF : E7 Fser * E7 (Ring.inverse Fser) = 1 := by rw [← map_mul, Fser_mul_inv, map_one]
  simp only [tau7, map_mul, E7_X]
  rw [show L7 xQ yQ zQ = E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ from rfl] at hyD
  linear_combination Y7 ^ 7 * E7 (Ring.inverse Fser) ^ 2 * hpoly + ((E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)^6*E7 (Ring.inverse Fser)^2*Y7^6 + 7*(E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)^5*E7 (Ring.inverse Fser)^2*X^2*Y7^6 + (E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)^5*E7 (Ring.inverse Fser)^2*X^2*Y7^5 + 21*(E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)^4*E7 (Ring.inverse Fser)^2*X^4*Y7^6 + 7*(E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)^4*E7 (Ring.inverse Fser)^2*X^4*Y7^5 + (E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)^4*E7 (Ring.inverse Fser)^2*X^4*Y7^4 + 49*(E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)^3*E7 (Ring.inverse Fser)^2*X^6*Y7^6 + 21*(E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)^3*E7 (Ring.inverse Fser)^2*X^6*Y7^5 + 7*(E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)^3*E7 (Ring.inverse Fser)^2*X^6*Y7^4 + (E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)^3*E7 (Ring.inverse Fser)^2*X^6*Y7^3 + 7*(E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)^2*E7 Fser*E7 (Ring.inverse Fser)^2*X*Y7^6 + 147*(E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)^2*E7 (Ring.inverse Fser)^2*X^8*Y7^6 + 49*(E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)^2*E7 (Ring.inverse Fser)^2*X^8*Y7^5 + 21*(E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)^2*E7 (Ring.inverse Fser)^2*X^8*Y7^4 + 7*(E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)^2*E7 (Ring.inverse Fser)^2*X^8*Y7^3 + (E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)^2*E7 (Ring.inverse Fser)^2*X^8*Y7^2 + 35*(E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)*E7 Fser*E7 (Ring.inverse Fser)^2*X^3*Y7^6 + 7*(E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)*E7 Fser*E7 (Ring.inverse Fser)^2*X^3*Y7^5 + 343*(E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)*E7 (Ring.inverse Fser)^2*X^10*Y7^6 + 147*(E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)*E7 (Ring.inverse Fser)^2*X^10*Y7^5 + 49*(E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)*E7 (Ring.inverse Fser)^2*X^10*Y7^4 + 21*(E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)*E7 (Ring.inverse Fser)^2*X^10*Y7^3 + 7*(E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)*E7 (Ring.inverse Fser)^2*X^10*Y7^2 + (E7 xQ - X * E7 yQ - X ^ 2 + X ^ 5 * E7 zQ)*E7 (Ring.inverse Fser)^2*X^10*Y7 + 49*E7 Fser*E7 (Ring.inverse Fser)^2*X^5*Y7^6 + 35*E7 Fser*E7 (Ring.inverse Fser)^2*X^5*Y7^5 + 7*E7 Fser*E7 (Ring.inverse Fser)^2*X^5*Y7^4 + 343*E7 (Ring.inverse Fser)^2*X^12*Y7^6 + 343*E7 (Ring.inverse Fser)^2*X^12*Y7^5 + 147*E7 (Ring.inverse Fser)^2*X^12*Y7^4 + 49*E7 (Ring.inverse Fser)^2*X^12*Y7^3 + 21*E7 (Ring.inverse Fser)^2*X^12*Y7^2 + 7*E7 (Ring.inverse Fser)^2*X^12*Y7 + E7 (Ring.inverse Fser)^2*X^12) * hyD + (-E7 Fser*E7 (Ring.inverse Fser)*Y7^7 + 49*E7 (Ring.inverse Fser)*X^7*Y7^6 + 35*E7 (Ring.inverse Fser)*X^7*Y7^5 + 7*E7 (Ring.inverse Fser)*X^7*Y7^4 - Y7^7) * hFF


/-- **`U₇(yᵏ) = Pm7 k (τ)`** for every `k`. -/
theorem Y7_dis (k : ℕ) : dis7 0 (Y7 ^ k) = Polynomial.aeval tau7 (Pm7 k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [Pm7, dis7_one]
    | 1, _ => rw [Y7_base1]; simp [Pm7, map_ofNat]
    | 2, _ => rw [Y7_base2]; simp [Pm7, map_ofNat]
    | 3, _ => rw [Y7_base3]; simp [Pm7, map_ofNat]
    | 4, _ => rw [Y7_base4]; simp [Pm7, map_ofNat]
    | 5, _ => rw [Y7_base5]; simp [Pm7, map_ofNat]
    | 6, _ => rw [Y7_base6]; simp [Pm7, map_ofNat]
    | k + 7, ih =>
      have h7 : Y7 ^ (k + 7) = E7 tau7 * (C 49 * Y7 ^ (k + 6) + C 35 * Y7 ^ (k + 5) + C 7 * Y7 ^ (k + 4))
          + E7 (tau7 ^ 2) * (C 343 * Y7 ^ (k + 6) + C 343 * Y7 ^ (k + 5) + C 147 * Y7 ^ (k + 4)
            + C 49 * Y7 ^ (k + 3) + C 21 * Y7 ^ (k + 2) + C 7 * Y7 ^ (k + 1) + Y7 ^ k) := by
        rw [show Y7 ^ (k + 7) = Y7 ^ k * Y7 ^ 7 by ring, modular7_eq, map_pow]
        simp only [map_ofNat]; ring
      rw [h7, dis7_add, dis7_E7_mul 0 (by norm_num), dis7_E7_mul 0 (by norm_num)]
      simp only [dis7_add, dis7_C_mul]
      rw [ih (k + 6) (by omega), ih (k + 5) (by omega), ih (k + 4) (by omega), ih (k + 3) (by omega),
        ih (k + 2) (by omega), ih (k + 1) (by omega), ih k (by omega), Pm7]
      simp only [map_mul, map_add, map_pow, Polynomial.aeval_X, map_ofNat]


end MockTheta5.JTP
