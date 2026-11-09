/-
# Entry 3.24: `G(−q⁶)H(−q) − qH(−q⁶)G(−q) = χ(q²)χ(q³)/(χ(q)χ(q⁶))`

Second proof of Entry 3.12 in Berndt et al. (§16):
* Watson's Lemma 4.1 at `q³`, substituted into Entry 3.7, gives `(16.5)`.
* Its even part is Entry 3.12 at `q²` (proved).
* The dissection (11.10) (`P11`) evaluates the odd part.
* Undoing `q ↦ q²` (`S_inj`) and then `q ↦ −q` gives Entry 3.24.
-/
import RamanujanTau.Forty.R11
import RamanujanTau.Forty.W41b
import RamanujanTau.Forty.E07
import RamanujanTau.Forty.E12

set_option autoImplicit false

namespace Forty
open PowerSeries Finset
open RankProof (Pinf isUnit_Pinf)

/-- (11.10) in the form used for Entries 3.23 and 3.24. -/
lemma star1110 : Pinf 24 48 * (Pinf 3 6 * Pinf 6 6 * Pinf 2 4 * Pinf 8 16 - Pinf 24 24 * Pinf 1 2 * Pinf 6 12 * Pinf 24 48)
      * Pinf 4 8 = X * Pinf 8 16 * Pinf 6 12 * Pinf 24 24 * Pinf 1 2 * Pinf 8 16 * Pinf 12 24 := by
  have K : Pinf 16 16 * Pinf 24 24 * Pinf 48 48 *
      (Pinf 24 48 * (Pinf 3 6 * Pinf 6 6 * Pinf 2 4 * Pinf 8 16 - Pinf 24 24 * Pinf 1 2 * Pinf 6 12 * Pinf 24 48)
        * Pinf 4 8 - X * Pinf 8 16 * Pinf 6 12 * Pinf 24 24 * Pinf 1 2 * Pinf 8 16 * Pinf 12 24) =
      Pinf 3 6 * (J 2 12 * J 6 12 * (J 8 24 * J 4 24) -
        (J 16 48 * J 24 48 * (J 1 6 * J 4 24) + X * (J 8 48 * J 24 48 * (J 1 6 * J 8 24)))) := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 48]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  rw [P11, sub_self, mul_zero] at K
  have hne : Pinf 16 16 * Pinf 24 24 * Pinf 48 48 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Pinf_ne 16 16 (by norm_num) (by norm_num)) (Pinf_ne 24 24 (by norm_num) (by norm_num)))
      (Pinf_ne 48 48 (by norm_num) (by norm_num))
  exact sub_eq_zero.mp ((mul_eq_zero.mp K).resolve_left hne)

/-- Entry 3.24 at `−q`: `H(q)G(−q⁶) + qG(q)H(−q⁶) = χ(q²)χ(−q³)/(χ(−q)χ(q⁶))`. -/
theorem entry_3_24_neg : (H * S 6 (Ng G) + X * G * S 6 (Ng H)) * (chim 1 * chip 6) = chip 2 * chim 3 := by
  have h7 := entry_3_7
  have h7' : (S 2 G * S 3 G + X * S 2 H * S 3 H) * Pinf 1 2 = Pinf 3 6 := by
    rw [h7, chim, chim, mul_assoc, Ring.inverse_mul_cancel _ (isUnit_Pinf 1 2 le_rfl (by norm_num)), mul_one]
  have a := congrArg (S 3) lemma41a
  have b := congrArg (S 3) lemma41b
  simp only [map_mul, map_add, map_pow, S_S 3 16 48 rfl, S_S 3 4 12 rfl, show (S 3) X = X ^ 3 from RankProof.Ea_X 3 _,
    S_Pinf 3 2 2 (by norm_num) (by norm_num), S_Pinf 3 8 8 (by norm_num) (by norm_num), Nat.reduceMul] at a b
  have h12 := congrArg (S 2) entry_3_12
  have u12 : IsUnit (chim 1 * chim 4) := (isUnit_Pinf 1 2 le_rfl (by norm_num)).mul (isUnit_Pinf 4 8 (by norm_num) (by norm_num))
  have h12' : (G * S 24 G + X ^ 5 * H * S 24 H) * (chim 1 * chim 4) = chim 3 * chim 12 := by
    rw [entry_3_12, mul_assoc, Ring.inverse_mul_cancel _ u12, mul_one]
  have h12s := congrArg (S 2) h12'
  simp only [chim, map_mul, map_add, map_pow, S_S 2 24 48 rfl, show (S 2) X = X ^ 2 from RankProof.Ea_X 2 _,
    S_Pinf 2 1 2 le_rfl (by norm_num), S_Pinf 2 4 8 (by norm_num) (by norm_num), S_Pinf 2 3 6 (by norm_num) (by norm_num),
    S_Pinf 2 12 24 (by norm_num) (by norm_num), Nat.reduceMul] at h12s
  have st := star1110
  have hc4 := chip_mul 4
  have hc12 := chip_mul 12
  norm_num at hc4 hc12
  -- the odd part `O` of (16.5)
  have hO : (S 2 H * S 12 (Ng G) + X ^ 2 * S 2 G * S 12 (Ng H)) * (Pinf 2 4 * chip 12) = chip 4 * Pinf 6 12 := by
    have hX : (X : PowerSeries ℤ) * Pinf 24 24 * Pinf 1 2 * Pinf 8 16 * (Pinf 12 24 * Pinf 4 8) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero X_ne_zero (Pinf_ne 24 24 (by norm_num) (by norm_num)))
        (Pinf_ne 1 2 le_rfl (by norm_num))) (Pinf_ne 8 16 (by norm_num) (by norm_num)))
        (mul_ne_zero (Pinf_ne 12 24 (by norm_num) (by norm_num)) (Pinf_ne 4 8 (by norm_num) (by norm_num)))
    apply mul_left_cancel₀ hX
    linear_combination (X * Pinf 24 24 * Pinf 1 2 * Pinf 8 16 * Pinf 4 8 * (S 2 H * S 12 (Ng G) + X ^ 2 * S 2 G * S 12 (Ng H)) * Pinf 2 4) * hc12 + ((Pinf 2 4 * Pinf 8 16 * Pinf 24 48 * Pinf 4 8) * Pinf 6 6) * h7' - ((Pinf 2 4 * Pinf 8 16 * Pinf 24 48 * Pinf 4 8) * Pinf 1 2 * S 2 G) * a
      - ((Pinf 2 4 * Pinf 8 16 * Pinf 24 48 * Pinf 4 8) * Pinf 1 2 * X * S 2 H) * b - (Pinf 24 48 * Pinf 4 8 * Pinf 24 24 * Pinf 1 2) * h12s + st
      - (X * Pinf 24 24 * Pinf 1 2 * Pinf 8 16 * Pinf 12 24 * Pinf 6 12) * hc4
  apply S_inj 2
  simp only [chip] at hO
  simp only [map_mul, map_add, map_pow, S_S 2 6 12 rfl, S_S 2 2 4 rfl, show (S 2) X = X ^ 2 from RankProof.Ea_X 2 _,
    chim, chip, S_Pinf 2 1 2 le_rfl (by norm_num), S_Pinf 2 3 6 (by norm_num) (by norm_num), Nat.reduceMul]
  linear_combination hO

lemma chip_unit (a : ℕ) [NeZero a] : IsUnit (chip a) := by
  have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr (NeZero.ne a)
  have h := chip_mul a
  have hu : IsUnit (chip a * Pinf a (2 * a)) := by rw [h]; exact isUnit_Pinf _ _ (by omega) (by omega)
  exact isUnit_of_mul_isUnit_left hu

lemma Ng_chim3 : Ng (chim 3) = chip 3 := by
  rw [chim, show (2 * 3 : ℕ) = 3 * 2 by rfl, ← S_Pinf 3 1 2 le_rfl (by norm_num), Ng_S_odd 3 (by decide), chip]

/-- **Entry 3.24** (Bressoud; Berndt et al. §16): `G(−q⁶)H(−q) − qH(−q⁶)G(−q) = χ(q²)χ(q³)/(χ(q)χ(q⁶))`. -/
theorem entry_3_24 : Ng H * S 6 (Ng G) - X * Ng G * S 6 (Ng H) = chip 2 * chip 3 * Ring.inverse (chip 1 * chip 6) := by
  have h := congrArg Ng entry_3_24_neg
  rw [map_mul, map_mul, map_mul, map_add, map_mul, map_mul, map_mul, Ng_S_ev 6 (by norm_num), Ng_S_ev 6 (by norm_num), Ng_X,
    Ng_chim3, chim, show (2 * 1 : ℕ) = 2 by rfl, Ng_P12] at h
  rw [show Ng (chip 6) = chip 6 by rw [chip, Ng_S_ev 6 (by norm_num)], show Ng (chip 2) = chip 2 by rw [chip, Ng_S_ev 2 (by norm_num)]] at h
  apply eq_mul_inv_of ((chip_unit 1).mul (chip_unit 6))
  linear_combination h

end Forty
