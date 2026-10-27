/-
# H2: `P'(φ)·g = S(φ)` for `g = g₂, g₃, g₄, g₆`

The kernel checks `chkA`–`chkI4` give, with `y = S₂(φ)`, `s = S₃(φ)`, `w = P'(φ)`:
* `V(z)(y² − ys − sw) + 11φ¹²w² = 0` and `V(z)(s²w − y³ + ysw) + φ¹²w³ = 0`. With `z·V(z) = φ¹²` these
  are R1 and R2 for `(y/w, s/w)`. They imply the homogeneous quintic for `y`, which `w·g₂` also satisfies,
  so `y = w·g₂` (`quintic_unique`). Then R1 gives `s = w·g₃`.
* `w·S₄(φ) = y² − w·s` and `w·S₆(φ) = y·S₄(φ)` give `g₄` and `g₆`.
-/
import RamanujanTau.Atkin11Seed.Unique
import RamanujanTau.Atkin11Seed.H2CheckA
import RamanujanTau.Atkin11Seed.H2CheckC
import RamanujanTau.Atkin11Seed.H2CheckD
import RamanujanTau.Atkin11Seed.H2CheckI

set_option autoImplicit false

namespace Atkin11Seed
open Atkin11 PowerSeries

/-! ### evaluation of the helpers -/

lemma evY_replicate_zero (y : PS) (k : ℕ) (f : PY) : evY y (List.replicate k JE.zero ++ f) = y ^ k * evY y f := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.cons_append, evY_cons, ih, JE.eval_zero, map_zero]; ring

lemma evY_shiftY (y : PS) (k : ℕ) (f : PY) : evY y (shiftY k f) = y ^ k * evY y f := evY_replicate_zero y k f

lemma evY_subY (y : PS) (f g : PY) : evY y (subY f g) = evY y f - evY y g := by
  rw [subY, evY_addY, evY_smulY]; push_cast; ring

lemma evY_of_ckEq (y : PS) {f g : PY} (h : ckEq f g = true) : evY y g = evY y f := by
  have := evY_isZero y _ h
  rw [evY_subY] at this
  exact (sub_eq_zero.mp this).symm

lemma zJ_eval : zJ.eval = z := by simp [zJ, JE.eval_single, evZ, gi]

lemma evY_y12 (y : PS) : evY y y12 = y ^ 12 := by
  rw [y12, evY_shiftY, evY_cons, evY_nil, JE.eval_single]; simp [evZ, gi]

lemma evY_take_drop (y : PS) : ∀ (k : ℕ) (f : PY), evY y f = evY y (f.take k) + y ^ k * evY y (f.drop k)
  | 0, f => by simp [evY]
  | _ + 1, [] => by simp [evY]
  | k + 1, a :: f => by
    rw [List.take_succ_cons, List.drop_succ_cons, evY_cons, evY_cons, evY_take_drop y k f]; ring

lemma evY_zero_cons (y : PS) (f : PY) : evY y (JE.zero :: f) = y * evY y f := by
  rw [evY_cons, JE.eval_zero, map_zero, zero_add]

/-! ### the identities -/

local notation "y2" => evY φ S2
local notation "y3" => evY φ S3
local notation "y4" => evY φ S4
local notation "y6" => evY φ S6
local notation "w" => evY φ dP

lemma eA : evY φ PA = y2 * y2 := by rw [evY_of_ckEq φ chkA, evY_mulY]
lemma eB : evY φ PB = y2 * y3 := by rw [evY_of_ckEq φ chkB, evY_mulY]
lemma eC : evY φ PC3 = y3 * y3 := by rw [evY_of_ckEq φ chkC, evY_mulY]
lemma eD : evY φ (addY PD0 (shiftY 10 PD1)) = y2 * y2 * y2 := by
  rw [evY_addY, evY_shiftY, evY_of_ckEq φ chkD0, evY_of_ckEq φ chkD1, evY_mulY, evY_mulY, ← eA,
    evY_take_drop φ 10 PA]
  ring

lemma eI1 : V z * (y2 * y2 - y2 * y3 - y3 * w) + 11 * φ ^ 12 * (w * w) = 0 := by
  have h := evY_isZero φ _ chkI1
  rw [evY_redP φ φ_isRoot, evY_addY, evY_jmulY, zJ_eval, evY_subY, evY_subY, evY_smulY, evY_mulY, evY_mulY,
    evY_y12, evY_mulY, eA, eB] at h
  push_cast at h
  linear_combination h

lemma eI2 : V z * (y3 * y3 * w - y2 * y2 * y2 + y2 * y3 * w) + φ ^ 12 * (w * w * w) = 0 := by
  have h := evY_isZero φ _ chkI2
  rw [evY_redP φ φ_isRoot, evY_addY, evY_jmulY, zJ_eval, evY_addY, evY_subY, evY_mulY, evY_mulY, eC, eD, eB,
    evY_mulY, evY_y12, evY_mulY, evY_mulY] at h
  linear_combination h

lemma eI3 : w * y4 - y2 * y2 + w * y3 = 0 := by
  have h := evY_isZero φ _ chkI3
  rw [evY_redP φ φ_isRoot, evY_addY, evY_subY, evY_mulY, evY_mulY, eA] at h
  exact h

lemma eI4 : w * y6 - y2 * y4 = 0 := by
  have h := evY_isZero φ _ chkI4
  rw [evY_redP φ φ_isRoot, evY_subY, evY_mulY, evY_mulY] at h
  exact h

lemma Vz_ne : V z ≠ 0 := fun h => z_ne_zero (V_injective (h.trans (map_zero V).symm))

lemma w_ne : w ≠ 0 := by
  obtain ⟨w1, hw, hw1⟩ := dP_shape
  rw [hw]
  refine mul_ne_zero (pow_ne_zero _ X_ne_zero) fun h => ?_
  rw [h, map_zero] at hw1
  exact absurd hw1 (by norm_num)

lemma cc_z1 : constantCoeff (E11 ^ 12 * Ring.inverse E1 ^ 12) = 1 := by
  rw [map_mul, map_pow, map_pow, E11, cc_V, cc_E1, cc_inv isUnit_E1 cc_E1]; simp

/-- **H2** for `g₂` and `g₃`. -/
theorem H2_g2_g3 : w * g2 = y2 ∧ w * g3 = y3 := by
  have hz := z_mul_Vz
  have R1h : y2 ^ 2 - y2 * y3 - y3 * w + 11 * z * w ^ 2 = 0 := by
    refine (mul_eq_zero.mp ?_).resolve_left Vz_ne
    linear_combination eI1 + 11 * w ^ 2 * hz
  have R2h : y3 ^ 2 * w - y2 ^ 3 + y2 * y3 * w + z * w ^ 3 = 0 := by
    refine (mul_eq_zero.mp ?_).resolve_left Vz_ne
    linear_combination eI2 + w ^ 3 * hz
  have Qy : y2 ^ 5 = z * w ^ 3 * (34 * y2 ^ 2 + 13 * w * y2 + (1 + 121 * z) * w ^ 2) := by
    linear_combination (-11 * w ^ 3 * z - y3 * y2 * w - 2 * y2 ^ 2 * w - y3 * w ^ 2 - y2 * w ^ 2) * R1h
      + (-(y2 + w) ^ 2) * R2h
  have Qg : (w * g2) ^ 5 = z * w ^ 3 * (34 * (w * g2) ^ 2 + 13 * w * (w * g2) + (1 + 121 * z) * w ^ 2) := by
    linear_combination w ^ 5 * quintic
  obtain ⟨w1, hw, hw1⟩ := dP_shape
  have hy : y2 = w * g2 := quintic_unique 50 11 (by norm_num) w w1 z (E11 ^ 12 * Ring.inverse E1 ^ 12) _ _ hw hw1
    (by rw [z]; ring) cc_z1 Qy Qg
  refine ⟨hy.symm, ?_⟩
  have hg3 : (1 + g2) * g3 = g2 ^ 2 + 11 * z := by
    rw [g3, ← mul_assoc, mul_comm (1 + g2), mul_assoc, Ring.mul_inverse_cancel _ isUnit_one_add_g2, mul_one]
  have hne : w * (1 + g2) ≠ 0 := mul_ne_zero w_ne isUnit_one_add_g2.ne_zero
  have : (w * (1 + g2)) * (w * g3) = (w * (1 + g2)) * y3 := by
    rw [hy] at R1h
    linear_combination w ^ 2 * hg3 + R1h
  exact mul_left_cancel₀ hne this

/-- **H2** for all of `1, g₂, g₃, g₄, g₆`. -/
theorem H2_all (i : ℕ) (hi : i < 5) : w * gi i = evY φ (Snum i) := by
  obtain ⟨h2, h3⟩ := H2_g2_g3
  interval_cases i
  · simp [gi, Snum]
  · exact h2
  · exact h3
  · show w * g4 = y4
    refine mul_left_cancel₀ w_ne ?_
    rw [g4]; linear_combination -eI3 + (w * g2 + y2) * h2 - w * h3
  · show w * g6 = y6
    have h4 : w * g4 = y4 := by
      refine mul_left_cancel₀ w_ne ?_
      rw [g4]; linear_combination -eI3 + (w * g2 + y2) * h2 - w * h3
    refine mul_left_cancel₀ w_ne ?_
    rw [g6]; linear_combination -eI4 + (w * g4) * h2 + y2 * h4

end Atkin11Seed
