/-
# Atkin 11^k: the modular equation and (R2), proved

From the certified identities (pulled back to `ℤ⟦q⟧`), the norm identity and Cayley–Hamilton for `φ`:

* `modeq_proved`: `φ¹¹ = Σ_j (−1)ʲ V(e_{j+1}) φ^{10−j}`, the `modeq` field of `Inputs`;
* `r2_proved`: `g₃² = g₂³ − g₂g₃ − z`, the `r2` field.
-/
import RamanujanTau.Atkin11Coef

set_option autoImplicit false

namespace Atkin11
open PowerSeries Atkin11Cert SPoly Finset

lemma PQ_eq : PQ = Qm 1 := by decide

/-- the four relations used to clear denominators. -/
lemma base_facts : evalP cPs PGN = g2 * evalP cPs PGD ∧ (1 + g2) * g3 = g2 ^ 2 + 11 * z ∧
    z * evalP cPs PF11 = X ^ 5 ∧ evalP cPs PQ = X := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show gN = gN * Ring.inverse gD * gD
    rw [mul_assoc, Ring.inverse_mul_cancel _ isUnit_gD, mul_one]
  · rw [g3, ← mul_assoc, mul_comm (1 + g2), mul_assoc, Ring.mul_inverse_cancel _ isUnit_one_add_g2, mul_one]
  · have h := norm_E11
    rw [Et_E11, pow_zero, one_mul] at h
    rw [mul_comm]; exact h
  · rw [PQ_eq, Qm_eval _ (by norm_num), pow_one]

lemma coef_1 : z * (X ^ 1 * evalP cPs PF10) = X ^ 5 * (121 * g2 + 2662 * g3 + 14641 * (g2 ^ 2 - g3) + 161051 * z) := by
  have hM := pull eM1 (ALz11.M1_eval h11 hd1)
  obtain ⟨hgN, hR1, hnorm, hQ⟩ := base_facts
  set gN := evalP cPs PGN with hgN_def
  set gD := evalP cPs PGD with hgD_def
  set Q := evalP cPs PQ with hQ_def
  set aF3 := evalP cPs PF3 with haF3
  set aF4 := evalP cPs PF4 with haF4
  set aF5 := evalP cPs PF5 with haF5
  set aF6 := evalP cPs PF6 with haF6
  set aF7 := evalP cPs PF7 with haF7
  set aF8 := evalP cPs PF8 with haF8
  set aF9 := evalP cPs PF9 with haF9
  set aF10 := evalP cPs PF10 with haF10
  set aF11 := evalP cPs PF11 with haF11
  simp only [eM1, a2, a3, a4, az, ae, Atkin11Cert.L, Q5, PE.eval] at hM
  push_cast at hM
  have key : (1 + g2) * gD ^ 3 * (z * (X ^ 1 * aF10) - X ^ 5 * (121 * g2 + 2662 * g3 + 14641 * (g2 ^ 2 - g3) + 161051 * z)) = 0 := by
    linear_combination (-z) * hM + (-aF10*Q*gD^2*z + 14641*aF11*g2^2*gD^2*z + 2783*aF11*g2*gD^2*z + 14641*aF11*g2*gD*gN*z + 121*aF11*gD^2*z + 2783*aF11*gD*gN*z + 14641*aF11*gN^2*z + 161051*Q^5*gD^2*z) * hgN + (11979*X^5*gD^3) * hR1 + (14641*g2^3*gD^3 + 2783*g2^2*gD^3 + 121*g2*gD^3) * hnorm + (-aF10*g2*gD^3*z - aF10*gD^3*z + 161051*Q^4*g2*gD^3*z + 29282*Q^4*gD^3*z + 161051*Q^3*X*g2*gD^3*z + 29282*Q^3*X*gD^3*z + 161051*Q^2*X^2*g2*gD^3*z + 29282*Q^2*X^2*gD^3*z + 161051*Q*X^3*g2*gD^3*z + 29282*Q*X^3*gD^3*z + 161051*X^4*g2*gD^3*z + 29282*X^4*gD^3*z) * hQ
  have hu : IsUnit ((1 + g2) * gD ^ 3) := isUnit_one_add_g2.mul (isUnit_gD.pow 3)
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hu.ne_zero)

lemma coef_2 : z * (X ^ 1 * evalP cPs PF9) = X ^ 5 * (-11 * g2 + 968 * g3 + 11979 * (g2 ^ 2 - g3) + 161051 * z) := by
  have hM := pull eM2 (ALz11.M2_eval h11 hd1)
  obtain ⟨hgN, hR1, hnorm, hQ⟩ := base_facts
  set gN := evalP cPs PGN with hgN_def
  set gD := evalP cPs PGD with hgD_def
  set Q := evalP cPs PQ with hQ_def
  set aF3 := evalP cPs PF3 with haF3
  set aF4 := evalP cPs PF4 with haF4
  set aF5 := evalP cPs PF5 with haF5
  set aF6 := evalP cPs PF6 with haF6
  set aF7 := evalP cPs PF7 with haF7
  set aF8 := evalP cPs PF8 with haF8
  set aF9 := evalP cPs PF9 with haF9
  set aF10 := evalP cPs PF10 with haF10
  set aF11 := evalP cPs PF11 with haF11
  simp only [eM2, a2, a3, a4, az, ae, Atkin11Cert.L, Q5, PE.eval] at hM
  push_cast at hM
  have key : (1 + g2) * gD ^ 3 * (z * (X ^ 1 * aF9) - X ^ 5 * (-11 * g2 + 968 * g3 + 11979 * (g2 ^ 2 - g3) + 161051 * z)) = 0 := by
    linear_combination (-z) * hM + (11979*aF11*g2^2*gD^2*z + 957*aF11*g2*gD^2*z + 11979*aF11*g2*gD*gN*z - 11*aF11*gD^2*z + 957*aF11*gD*gN*z + 11979*aF11*gN^2*z - aF9*Q*gD^2*z + 161051*Q^5*gD^2*z) * hgN + (11011*X^5*gD^3) * hR1 + (11979*g2^3*gD^3 + 957*g2^2*gD^3 - 11*g2*gD^3) * hnorm + (-aF9*g2*gD^3*z - aF9*gD^3*z + 161051*Q^4*g2*gD^3*z + 39930*Q^4*gD^3*z + 161051*Q^3*X*g2*gD^3*z + 39930*Q^3*X*gD^3*z + 161051*Q^2*X^2*g2*gD^3*z + 39930*Q^2*X^2*gD^3*z + 161051*Q*X^3*g2*gD^3*z + 39930*Q*X^3*gD^3*z + 161051*X^4*g2*gD^3*z + 39930*X^4*gD^3*z) * hQ
  have hu : IsUnit ((1 + g2) * gD ^ 3) := isUnit_one_add_g2.mul (isUnit_gD.pow 3)
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hu.ne_zero)

lemma coef_3 : z * (X ^ 2 * evalP cPs PF8) = X ^ 5 * (242 * g3 + 5324 * (g2 ^ 2 - g3) + 73205 * z) := by
  have hM := pull eM3 (ALz11.M3_eval h11 hd1)
  obtain ⟨hgN, hR1, hnorm, hQ⟩ := base_facts
  set gN := evalP cPs PGN with hgN_def
  set gD := evalP cPs PGD with hgD_def
  set Q := evalP cPs PQ with hQ_def
  set aF3 := evalP cPs PF3 with haF3
  set aF4 := evalP cPs PF4 with haF4
  set aF5 := evalP cPs PF5 with haF5
  set aF6 := evalP cPs PF6 with haF6
  set aF7 := evalP cPs PF7 with haF7
  set aF8 := evalP cPs PF8 with haF8
  set aF9 := evalP cPs PF9 with haF9
  set aF10 := evalP cPs PF10 with haF10
  set aF11 := evalP cPs PF11 with haF11
  simp only [eM3, a2, a3, a4, az, ae, Atkin11Cert.L, Q5, PE.eval] at hM
  push_cast at hM
  have key : (1 + g2) * gD ^ 3 * (z * (X ^ 2 * aF8) - X ^ 5 * (242 * g3 + 5324 * (g2 ^ 2 - g3) + 73205 * z)) = 0 := by
    linear_combination (-z) * hM + (5324*aF11*g2^2*gD^2*z + 242*aF11*g2*gD^2*z + 5324*aF11*g2*gD*gN*z + 242*aF11*gD*gN*z + 5324*aF11*gN^2*z - aF8*Q^2*gD^2*z + 73205*Q^5*gD^2*z) * hgN + (5082*X^5*gD^3) * hR1 + (5324*g2^3*gD^3 + 242*g2^2*gD^3) * hnorm + (-aF8*Q*g2*gD^3*z - aF8*Q*gD^3*z - aF8*X*g2*gD^3*z - aF8*X*gD^3*z + 73205*Q^4*g2*gD^3*z + 17303*Q^4*gD^3*z + 73205*Q^3*X*g2*gD^3*z + 17303*Q^3*X*gD^3*z + 73205*Q^2*X^2*g2*gD^3*z + 17303*Q^2*X^2*gD^3*z + 73205*Q*X^3*g2*gD^3*z + 17303*Q*X^3*gD^3*z + 73205*X^4*g2*gD^3*z + 17303*X^4*gD^3*z) * hQ
  have hu : IsUnit ((1 + g2) * gD ^ 3) := isUnit_one_add_g2.mul (isUnit_gD.pow 3)
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hu.ne_zero)

lemma coef_4 : z * (X ^ 2 * evalP cPs PF7) = X ^ 5 * (22 * g3 + 1452 * (g2 ^ 2 - g3) + 14641 * z) := by
  have hM := pull eM4 (ALz11.M4_eval h11 hd1)
  obtain ⟨hgN, hR1, hnorm, hQ⟩ := base_facts
  set gN := evalP cPs PGN with hgN_def
  set gD := evalP cPs PGD with hgD_def
  set Q := evalP cPs PQ with hQ_def
  set aF3 := evalP cPs PF3 with haF3
  set aF4 := evalP cPs PF4 with haF4
  set aF5 := evalP cPs PF5 with haF5
  set aF6 := evalP cPs PF6 with haF6
  set aF7 := evalP cPs PF7 with haF7
  set aF8 := evalP cPs PF8 with haF8
  set aF9 := evalP cPs PF9 with haF9
  set aF10 := evalP cPs PF10 with haF10
  set aF11 := evalP cPs PF11 with haF11
  simp only [eM4, a2, a3, a4, az, ae, Atkin11Cert.L, Q5, PE.eval] at hM
  push_cast at hM
  have key : (1 + g2) * gD ^ 3 * (z * (X ^ 2 * aF7) - X ^ 5 * (22 * g3 + 1452 * (g2 ^ 2 - g3) + 14641 * z)) = 0 := by
    linear_combination (-z) * hM + (1452*aF11*g2^2*gD^2*z + 22*aF11*g2*gD^2*z + 1452*aF11*g2*gD*gN*z + 22*aF11*gD*gN*z + 1452*aF11*gN^2*z - aF7*Q^2*gD^2*z + 14641*Q^5*gD^2*z) * hgN + (1430*X^5*gD^3) * hR1 + (1452*g2^3*gD^3 + 22*g2^2*gD^3) * hnorm + (-aF7*Q*g2*gD^3*z - aF7*Q*gD^3*z - aF7*X*g2*gD^3*z - aF7*X*gD^3*z + 14641*Q^4*g2*gD^3*z - 1089*Q^4*gD^3*z + 14641*Q^3*X*g2*gD^3*z - 1089*Q^3*X*gD^3*z + 14641*Q^2*X^2*g2*gD^3*z - 1089*Q^2*X^2*gD^3*z + 14641*Q*X^3*g2*gD^3*z - 1089*Q*X^3*gD^3*z + 14641*X^4*g2*gD^3*z - 1089*X^4*gD^3*z) * hQ
  have hu : IsUnit ((1 + g2) * gD ^ 3) := isUnit_one_add_g2.mul (isUnit_gD.pow 3)
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hu.ne_zero)

lemma coef_5 : z * (X ^ 3 * evalP cPs PF6) = X ^ 5 * (242 * (g2 ^ 2 - g3) - 1331 * z) := by
  have hM := pull eM5 (ALz11.M5_eval h11 hd1)
  obtain ⟨hgN, hR1, hnorm, hQ⟩ := base_facts
  set gN := evalP cPs PGN with hgN_def
  set gD := evalP cPs PGD with hgD_def
  set Q := evalP cPs PQ with hQ_def
  set aF3 := evalP cPs PF3 with haF3
  set aF4 := evalP cPs PF4 with haF4
  set aF5 := evalP cPs PF5 with haF5
  set aF6 := evalP cPs PF6 with haF6
  set aF7 := evalP cPs PF7 with haF7
  set aF8 := evalP cPs PF8 with haF8
  set aF9 := evalP cPs PF9 with haF9
  set aF10 := evalP cPs PF10 with haF10
  set aF11 := evalP cPs PF11 with haF11
  simp only [eM5, a2, a3, a4, az, ae, Atkin11Cert.L, Q5, PE.eval] at hM
  push_cast at hM
  have key : (1 + g2) * gD ^ 3 * (z * (X ^ 3 * aF6) - X ^ 5 * (242 * (g2 ^ 2 - g3) - 1331 * z)) = 0 := by
    linear_combination (-z) * hM + (242*aF11*g2^2*gD^2*z + 242*aF11*g2*gD*gN*z + 242*aF11*gN^2*z - aF6*Q^3*gD^2*z - 1331*Q^5*gD^2*z) * hgN + (242*X^5*gD^3) * hR1 + (242*g2^3*gD^3) * hnorm + (-aF6*Q^2*g2*gD^3*z - aF6*Q^2*gD^3*z - aF6*Q*X*g2*gD^3*z - aF6*Q*X*gD^3*z - aF6*X^2*g2*gD^3*z - aF6*X^2*gD^3*z - 1331*Q^4*g2*gD^3*z - 3993*Q^4*gD^3*z - 1331*Q^3*X*g2*gD^3*z - 3993*Q^3*X*gD^3*z - 1331*Q^2*X^2*g2*gD^3*z - 3993*Q^2*X^2*gD^3*z - 1331*Q*X^3*g2*gD^3*z - 3993*Q*X^3*gD^3*z - 1331*X^4*g2*gD^3*z - 3993*X^4*gD^3*z) * hQ
  have hu : IsUnit ((1 + g2) * gD ^ 3) := isUnit_one_add_g2.mul (isUnit_gD.pow 3)
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hu.ne_zero)

lemma coef_6 : z * (X ^ 3 * evalP cPs PF5) = X ^ 5 * (22 * (g2 ^ 2 - g3) - 1331 * z) := by
  have hM := pull eM6 (ALz11.M6_eval h11 hd1)
  obtain ⟨hgN, hR1, hnorm, hQ⟩ := base_facts
  set gN := evalP cPs PGN with hgN_def
  set gD := evalP cPs PGD with hgD_def
  set Q := evalP cPs PQ with hQ_def
  set aF3 := evalP cPs PF3 with haF3
  set aF4 := evalP cPs PF4 with haF4
  set aF5 := evalP cPs PF5 with haF5
  set aF6 := evalP cPs PF6 with haF6
  set aF7 := evalP cPs PF7 with haF7
  set aF8 := evalP cPs PF8 with haF8
  set aF9 := evalP cPs PF9 with haF9
  set aF10 := evalP cPs PF10 with haF10
  set aF11 := evalP cPs PF11 with haF11
  simp only [eM6, a2, a3, a4, az, ae, Atkin11Cert.L, Q5, PE.eval] at hM
  push_cast at hM
  have key : (1 + g2) * gD ^ 3 * (z * (X ^ 3 * aF5) - X ^ 5 * (22 * (g2 ^ 2 - g3) - 1331 * z)) = 0 := by
    linear_combination (-z) * hM + (22*aF11*g2^2*gD^2*z + 22*aF11*g2*gD*gN*z + 22*aF11*gN^2*z - aF5*Q^3*gD^2*z - 1331*Q^5*gD^2*z) * hgN + (22*X^5*gD^3) * hR1 + (22*g2^3*gD^3) * hnorm + (-aF5*Q^2*g2*gD^3*z - aF5*Q^2*gD^3*z - aF5*Q*X*g2*gD^3*z - aF5*Q*X*gD^3*z - aF5*X^2*g2*gD^3*z - aF5*X^2*gD^3*z - 1331*Q^4*g2*gD^3*z - 1573*Q^4*gD^3*z - 1331*Q^3*X*g2*gD^3*z - 1573*Q^3*X*gD^3*z - 1331*Q^2*X^2*g2*gD^3*z - 1573*Q^2*X^2*gD^3*z - 1331*Q*X^3*g2*gD^3*z - 1573*Q*X^3*gD^3*z - 1331*X^4*g2*gD^3*z - 1573*X^4*gD^3*z) * hQ
  have hu : IsUnit ((1 + g2) * gD ^ 3) := isUnit_one_add_g2.mul (isUnit_gD.pow 3)
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hu.ne_zero)

/-- **the quintic** `g₂⁵ = z(1 + 13g₂ + 34g₂²) + 121z²`. -/
theorem quintic : g2 ^ 5 - z * (1 + 13 * g2 + 34 * g2 ^ 2) - 121 * z ^ 2 = 0 := by
  have hM := pull eQU (ALz11.QU_eval h11 hd1)
  obtain ⟨hgN, hR1, hnorm, hQ⟩ := base_facts
  set gN := evalP cPs PGN with hgN_def
  set gD := evalP cPs PGD with hgD_def
  set Q := evalP cPs PQ with hQ_def
  set aF3 := evalP cPs PF3 with haF3
  set aF4 := evalP cPs PF4 with haF4
  set aF5 := evalP cPs PF5 with haF5
  set aF6 := evalP cPs PF6 with haF6
  set aF7 := evalP cPs PF7 with haF7
  set aF8 := evalP cPs PF8 with haF8
  set aF9 := evalP cPs PF9 with haF9
  set aF10 := evalP cPs PF10 with haF10
  set aF11 := evalP cPs PF11 with haF11
  simp only [eQU, Atkin11Cert.L, Q5, PE.eval] at hM
  push_cast at hM
  have key : gD ^ 5 * aF11 ^ 2 * (g2 ^ 5 - z * (1 + 13 * g2 + 34 * g2 ^ 2) - 121 * z ^ 2) = 0 := by
    linear_combination hM + (-aF11^2*g2^4*gD^4 - aF11^2*g2^3*gD^3*gN - aF11^2*g2^2*gD^2*gN^2 - aF11^2*g2*gD*gN^3 - aF11^2*gN^4 + 34*aF11*Q^5*g2*gD^4 + 13*aF11*Q^5*gD^4 + 34*aF11*Q^5*gD^3*gN) * hgN + (-34*aF11*g2^2*gD^5 - 13*aF11*g2*gD^5 - 121*aF11*gD^5*z - aF11*gD^5 - 121*X^5*gD^5) * hnorm + (34*aF11*Q^4*g2^2*gD^5 + 13*aF11*Q^4*g2*gD^5 + aF11*Q^4*gD^5 + 34*aF11*Q^3*X*g2^2*gD^5 + 13*aF11*Q^3*X*g2*gD^5 + aF11*Q^3*X*gD^5 + 34*aF11*Q^2*X^2*g2^2*gD^5 + 13*aF11*Q^2*X^2*g2*gD^5 + aF11*Q^2*X^2*gD^5 + 34*aF11*Q*X^3*g2^2*gD^5 + 13*aF11*Q*X^3*g2*gD^5 + aF11*Q*X^3*gD^5 + 34*aF11*X^4*g2^2*gD^5 + 13*aF11*X^4*g2*gD^5 + aF11*X^4*gD^5 + 121*Q^9*gD^5 + 121*Q^8*X*gD^5 + 121*Q^7*X^2*gD^5 + 121*Q^6*X^3*gD^5 + 121*Q^5*X^4*gD^5 + 121*Q^4*X^5*gD^5 + 121*Q^3*X^6*gD^5 + 121*Q^2*X^7*gD^5 + 121*Q*X^8*gD^5 + 121*X^9*gD^5) * hQ
  have hF : aF11 ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hnorm; exact pow_ne_zero 5 X_ne_zero hnorm.symm
  have hne : gD ^ 5 * aF11 ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ isUnit_gD.ne_zero) (pow_ne_zero _ hF)
  exact (mul_eq_zero.mp key).resolve_left hne

/-- **(R2)** `g₃² = g₂³ − g₂g₃ − z`. -/
theorem r2_proved : g3 ^ 2 = g2 ^ 3 - g2 * g3 - z := by
  have hq := quintic
  have hR1 : (1 + g2) * g3 - g2 ^ 2 - 11 * z = 0 := by
    obtain ⟨-, h, -, -⟩ := base_facts; rw [h]; ring
  have key : (1 + g2) ^ 2 * (g3 ^ 2 - (g2 ^ 3 - g2 * g3 - z)) = 0 := by
    linear_combination -hq + (2*g2^2 + g2*g3 + g2 + g3 + 11*z) * hR1
  have hu : IsUnit ((1 + g2) ^ 2) := isUnit_one_add_g2.pow 2
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hu.ne_zero)

lemma lcE1 : lc (eF 1) = 121 * g2 + 2662 * g3 + 14641 * (g2 ^ 2 - g3) + 161051 * z := by
  rw [eF_eq]; simp [eList, J, gi, g4, zsmul_eq_mul] <;> ring
lemma lcE2 : lc (eF 2) = -11 * g2 + 968 * g3 + 11979 * (g2 ^ 2 - g3) + 161051 * z := by
  rw [eF_eq]; simp [eList, J, gi, g4, zsmul_eq_mul] <;> ring
lemma lcE3 : lc (eF 3) = 242 * g3 + 5324 * (g2 ^ 2 - g3) + 73205 * z := by
  rw [eF_eq]; simp [eList, J, gi, g4, zsmul_eq_mul] <;> ring
lemma lcE4 : lc (eF 4) = 22 * g3 + 1452 * (g2 ^ 2 - g3) + 14641 * z := by
  rw [eF_eq]; simp [eList, J, gi, g4, zsmul_eq_mul] <;> ring
lemma lcE5 : lc (eF 5) = 242 * (g2 ^ 2 - g3) - 1331 * z := by
  rw [eF_eq]; simp [eList, J, gi, g4, zsmul_eq_mul] <;> ring
lemma lcE6 : lc (eF 6) = 22 * (g2 ^ 2 - g3) - 1331 * z := by
  rw [eF_eq]; simp [eList, J, gi, g4, zsmul_eq_mul] <;> ring
lemma lcE7 : lc (eF 7) = -121 * z := by
  rw [eF_eq]; simp [eList, J, gi, g4, zsmul_eq_mul] <;> ring
lemma lcE8 : lc (eF 8) = 121 * z := by
  rw [eF_eq]; simp [eList, J, gi, g4, zsmul_eq_mul] <;> ring
lemma lcE9 : lc (eF 9) = 55 * z := by
  rw [eF_eq]; simp [eList, J, gi, g4, zsmul_eq_mul] <;> ring
lemma lcE10 : lc (eF 10) = 11 * z := by
  rw [eF_eq]; simp [eList, J, gi, g4, zsmul_eq_mul] <;> ring
lemma lcE11 : lc (eF 11) = z := by
  rw [eF_eq]; simp [eList, J, gi, g4, zsmul_eq_mul] <;> ring

lemma coefV (p : SPoly6.Poly) (hq : (p.all fun t => t.1 % 1024 == 0) = true) (w : PS)
    (h : z * Et p = X ^ 5 * w) : V z * eE p = X ^ 55 * V w := by
  rw [eE_V p hq, ← map_mul, h, map_mul, map_pow, V_X', ← pow_mul]

lemma coef_7 : z * Et CH_E4 = X ^ 5 * (-121 * z) := by
  have h := pull eE4 (ALz11.E4_eval h11 hd1)
  simp only [eE4, Atkin11Cert.L, PE.eval] at h
  rw [Et_E4, show evalP cPs PF4 = -121 * X by
    have hQ := base_facts.2.2.2; push_cast at h; linear_combination h - 121 * hQ]
  ring

lemma coef_8 : z * Et CH_E3 = X ^ 5 * (121 * z) := by
  have h := pull eE3 (ALz11.E3_eval h11 hd1)
  simp only [eE3, Atkin11Cert.L, PE.eval] at h
  rw [Et_E3, show evalP cPs PF3 = 121 * X by
    have hQ := base_facts.2.2.2; push_cast at h; linear_combination h + 121 * hQ]
  ring

/-- **the modular equation** (the `modeq` field of `Inputs`). -/
theorem modeq_proved : φ ^ 11 = ∑ j ∈ range 11, (-1) ^ j * V (lc (eF (j + 1))) * φ ^ (10 - j) := by
  have hφ := charpoly_φ
  have c1 : V z * eE CH_E10 = X ^ 55 * V (lc (eF 1)) :=
    coefV _ qfree_10 _ (by rw [lcE1, Et_E10]; exact coef_1)
  have c2 : V z * eE CH_E9 = X ^ 55 * V (lc (eF 2)) :=
    coefV _ qfree_9 _ (by rw [lcE2, Et_E9]; exact coef_2)
  have c3 : V z * eE CH_E8 = X ^ 55 * V (lc (eF 3)) :=
    coefV _ qfree_8 _ (by rw [lcE3, Et_E8]; exact coef_3)
  have c4 : V z * eE CH_E7 = X ^ 55 * V (lc (eF 4)) :=
    coefV _ qfree_7 _ (by rw [lcE4, Et_E7]; exact coef_4)
  have c5 : V z * eE CH_E6 = X ^ 55 * V (lc (eF 5)) :=
    coefV _ qfree_6 _ (by rw [lcE5, Et_E6]; exact coef_5)
  have c6 : V z * eE CH_E5 = X ^ 55 * V (lc (eF 6)) :=
    coefV _ qfree_5 _ (by rw [lcE6, Et_E5]; exact coef_6)
  have c7 : V z * eE CH_E4 = X ^ 55 * V (lc (eF 7)) := coefV _ qfree_4 _ (by rw [lcE7]; exact coef_7)
  have c8 : V z * eE CH_E3 = X ^ 55 * V (lc (eF 8)) := coefV _ qfree_3 _ (by rw [lcE8]; exact coef_8)
  have c9 : V z * eE CH_E2 = X ^ 55 * V (lc (eF 9)) := coefV _ qfree_2 _ (by rw [lcE9, Et_E2]; ring)
  have c10 : V z * eE CH_E1 = X ^ 55 * V (lc (eF 10)) := coefV _ qfree_1 _ (by rw [lcE10, Et_E1]; ring)
  have c11 : V z * X ^ 55 = X ^ 55 * V (lc (eF 11)) := by rw [lcE11]; ring
  have cE : V z * eE CH_E11 = X ^ 55 := by
    have := coefV _ qfree_11 1 (by rw [mul_comm, norm_E11, mul_one])
    rwa [map_one, mul_one] at this
  have key : X ^ 55 * ((V (lc (eF 1)) * φ ^ 10 - V (lc (eF 2)) * φ ^ 9 + V (lc (eF 3)) * φ ^ 8 - V (lc (eF 4)) * φ ^ 7 + V (lc (eF 5)) * φ ^ 6 - V (lc (eF 6)) * φ ^ 5 + V (lc (eF 7)) * φ ^ 4 - V (lc (eF 8)) * φ ^ 3 + V (lc (eF 9)) * φ ^ 2 - V (lc (eF 10)) * φ ^ 1 + V (lc (eF 11)) * φ ^ 0) - φ ^ 11) = 0 := by
    linear_combination (V z) * hφ - c11 + φ ^ 1 * c10 - φ ^ 2 * c9 + φ ^ 3 * c8 - φ ^ 4 * c7 + φ ^ 5 * c6 - φ ^ 6 * c5 + φ ^ 7 * c4 - φ ^ 8 * c3 + φ ^ 9 * c2 - φ ^ 10 * c1 + φ ^ 11 * cE
  have hS : (∑ j ∈ range 11, (-1) ^ j * V (lc (eF (j + 1))) * φ ^ (10 - j)) = V (lc (eF 1)) * φ ^ 10 - V (lc (eF 2)) * φ ^ 9 + V (lc (eF 3)) * φ ^ 8 - V (lc (eF 4)) * φ ^ 7 + V (lc (eF 5)) * φ ^ 6 - V (lc (eF 6)) * φ ^ 5 + V (lc (eF 7)) * φ ^ 4 - V (lc (eF 8)) * φ ^ 3 + V (lc (eF 9)) * φ ^ 2 - V (lc (eF 10)) * φ ^ 1 + V (lc (eF 11)) * φ ^ 0 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num
    try ring
  rw [hS]
  exact (sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left (pow_ne_zero _ X_ne_zero))).symm

end Atkin11
