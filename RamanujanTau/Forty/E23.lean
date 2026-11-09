/-
# Entry 3.23: `G(−q²)G(−q³) + qH(−q²)H(−q³) = χ(q)χ(q⁶)/(χ(q²)χ(q³))`

Second proof of Entry 3.11 in Berndt et al. (§15):
* Watson's Lemma 4.1, substituted into Entry 3.8, gives (15.4).
* Its odd part is Entry 3.11 at `q²` (proved).
* Its even part is Entry 3.23 at `q ↦ −q²`, evaluated by (11.10) at `−q` (`star1110_neg`, from `star1110` by `q ↦ −q`).
-/
import RamanujanTau.Forty.E24
import RamanujanTau.Forty.E08
import RamanujanTau.Forty.E11
import RamanujanTau.Forty.E21

set_option autoImplicit false

namespace Forty
open PowerSeries Finset
open RankProof (Pinf isUnit_Pinf)

/-- (11.10) at `−q`, in product form (`⋆₂`). -/
lemma star1110_neg : (Pinf 1 2 * Pinf 2 2 * Pinf 6 12 * Pinf 24 48 + X * Pinf 2 4 * Pinf 8 16 * Pinf 8 8 * Pinf 3 6)
      * Pinf 8 16 * Pinf 12 24 = Pinf 2 4 * Pinf 24 48 * Pinf 8 8 * Pinf 3 6 * Pinf 24 48 * Pinf 4 8 := by
  have st := congrArg Ng star1110
  simp only [map_mul, map_sub, Ng_X, Ng_P12, show Ng (Pinf 3 6) = chip 3 from Ng_chim3,
    nE 12 24 (by norm_num) (by norm_num) (rfl : 24 = 2 * 12) (rfl : 48 = 2 * 24), nE 3 3 (by norm_num) (by norm_num) (rfl : 6 = 2 * 3) (rfl : 6 = 2 * 3),
    nE 1 2 le_rfl (by norm_num) (rfl : 2 = 2 * 1) (rfl : 4 = 2 * 2), nE 4 8 (by norm_num) (by norm_num) (rfl : 8 = 2 * 4) (rfl : 16 = 2 * 8),
    nE 12 12 (by norm_num) (by norm_num) (rfl : 24 = 2 * 12) (rfl : 24 = 2 * 12), nE 3 6 (by norm_num) (by norm_num) (rfl : 6 = 2 * 3) (rfl : 12 = 2 * 6),
    nE 2 4 (by norm_num) (by norm_num) (rfl : 4 = 2 * 2) (rfl : 8 = 2 * 4), nE 6 12 (by norm_num) (by norm_num) (rfl : 12 = 2 * 6) (rfl : 24 = 2 * 12)] at st
  have c1 := chip_mul 1
  have c3 := chip_mul 3
  norm_num at c1 c3
  -- `st · (q;q²)(q³;q⁶)`, with `χ(q)(q;q²) = (q²;q⁴)` and `χ(q³)(q³;q⁶) = (q⁶;q¹²)`
  have st2 : Pinf 24 48 * (Pinf 6 12 * Pinf 6 6 * Pinf 2 4 * Pinf 8 16 * Pinf 1 2 - Pinf 24 24 * Pinf 2 4 * Pinf 6 12 * Pinf 24 48 * Pinf 3 6)
      * Pinf 4 8 + X * Pinf 8 16 * Pinf 6 12 * Pinf 24 24 * Pinf 2 4 * Pinf 8 16 * Pinf 12 24 * Pinf 3 6 = 0 := by
    linear_combination (Pinf 1 2 * Pinf 3 6) * st
      - (Pinf 24 48 * Pinf 4 8 * (Pinf 6 6 * Pinf 2 4 * Pinf 8 16 * Pinf 1 2)) * c3
      + (Pinf 24 48 * Pinf 4 8 * Pinf 24 24 * Pinf 6 12 * Pinf 24 48 * Pinf 3 6) * c1
      - (X * Pinf 8 16 * Pinf 6 12 * Pinf 24 24 * Pinf 8 16 * Pinf 12 24 * Pinf 3 6) * c1
  have K : Pinf 6 12 * ((Pinf 1 2 * Pinf 2 2 * Pinf 6 12 * Pinf 24 48 + X * Pinf 2 4 * Pinf 8 16 * Pinf 8 8 * Pinf 3 6)
      * Pinf 8 16 * Pinf 12 24 - Pinf 2 4 * Pinf 24 48 * Pinf 8 8 * Pinf 3 6 * Pinf 24 48 * Pinf 4 8) =
      (Pinf 8 48 * Pinf 16 48 * Pinf 32 48 * Pinf 40 48) * (Pinf 24 48 * (Pinf 6 12 * Pinf 6 6 * Pinf 2 4 * Pinf 8 16 * Pinf 1 2 - Pinf 24 24 * Pinf 2 4 * Pinf 6 12 * Pinf 24 48 * Pinf 3 6)
      * Pinf 4 8 + X * Pinf 8 16 * Pinf 6 12 * Pinf 24 24 * Pinf 2 4 * Pinf 8 16 * Pinf 12 24 * Pinf 3 6) := by
    simp (disch := norm_num) only [atom _ _ 48]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  rw [st2, mul_zero] at K
  exact sub_eq_zero.mp ((mul_eq_zero.mp K).resolve_left (Pinf_ne 6 12 (by norm_num) (by norm_num)))


/-- Entry 3.23 at `q ↦ −q`: `G(−q²)G(q³) − qH(−q²)H(q³) = χ(−q)χ(q⁶)/(χ(q²)χ(−q³))`. -/
theorem entry_3_23_neg : (S 2 (Ng G) * S 3 G - X * S 2 (Ng H) * S 3 H) * (chip 2 * chim 3) = chim 1 * chip 6 := by
  have h8 := entry_3_8
  have h8' : (S 6 G * H - X * G * S 6 H) * Pinf 3 6 = Pinf 1 2 := by
    rw [h8, chim, chim, mul_assoc, Ring.inverse_mul_cancel _ (isUnit_Pinf 3 6 (by norm_num) (by norm_num)), mul_one]
  have a := lemma41a
  have b := lemma41b
  have u11 : IsUnit (chim 3 * chim 12) := (isUnit_Pinf 3 6 (by norm_num) (by norm_num)).mul (isUnit_Pinf 12 24 (by norm_num) (by norm_num))
  have h11' : (S 8 G * S 3 H - X * S 3 G * S 8 H) * (chim 3 * chim 12) = chim 1 * chim 4 := by
    rw [entry_3_11, mul_assoc, Ring.inverse_mul_cancel _ u11, mul_one]
  have h11s := congrArg (S 2) h11'
  simp only [chim, map_mul, map_sub, S_S 2 8 16 rfl, S_S 2 3 6 rfl, show (S 2) X = X ^ 2 from RankProof.Ea_X 2 _,
    S_Pinf 2 1 2 le_rfl (by norm_num), S_Pinf 2 4 8 (by norm_num) (by norm_num), S_Pinf 2 3 6 (by norm_num) (by norm_num),
    S_Pinf 2 12 24 (by norm_num) (by norm_num), Nat.reduceMul] at h11s
  have s2 := star1110_neg
  have hc4 := chip_mul 4
  have hc12 := chip_mul 12
  norm_num at hc4 hc12
  have hEv : (S 4 (Ng G) * S 6 G - X ^ 2 * S 4 (Ng H) * S 6 H) * (chip 4 * Pinf 6 12) = Pinf 2 4 * chip 12 := by
    have hF : Pinf 8 8 * Pinf 3 6 * Pinf 24 48 * Pinf 4 8 * Pinf 12 24 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (Pinf_ne 8 8 (by norm_num) (by norm_num)) (Pinf_ne 3 6 (by norm_num) (by norm_num)))
        (Pinf_ne 24 48 (by norm_num) (by norm_num))) (Pinf_ne 4 8 (by norm_num) (by norm_num))) (Pinf_ne 12 24 (by norm_num) (by norm_num))
    apply mul_left_cancel₀ hF
    linear_combination (Pinf 8 8 * Pinf 3 6 * (S 4 (Ng G) * S 6 G - X ^ 2 * S 4 (Ng H) * S 6 H) * Pinf 6 12 * Pinf 24 48 * Pinf 12 24) * hc4
      + (Pinf 6 12 * Pinf 24 48 * Pinf 8 16 * Pinf 12 24) * (Pinf 2 2 * h8' - Pinf 3 6 * S 6 G * b + X * Pinf 3 6 * S 6 H * a)
      + (X * Pinf 8 8 * Pinf 3 6 * Pinf 8 16 * Pinf 12 24) * h11s + s2
      - (Pinf 8 8 * Pinf 3 6 * Pinf 24 48 * Pinf 4 8 * Pinf 2 4) * hc12
  apply S_inj 2
  simp only [chip] at hEv
  simp only [map_mul, map_sub, map_pow, S_S 2 2 4 rfl, S_S 2 3 6 rfl, S_S 2 6 12 rfl,
    show (S 2) X = X ^ 2 from RankProof.Ea_X 2 _, chim, chip, S_Pinf 2 1 2 le_rfl (by norm_num),
    S_Pinf 2 3 6 (by norm_num) (by norm_num), Nat.reduceMul]
  linear_combination hEv

/-- **Entry 3.23** (Bressoud; Berndt et al. §15): `G(−q²)G(−q³) + qH(−q²)H(−q³) = χ(q)χ(q⁶)/(χ(q²)χ(q³))`. -/
theorem entry_3_23 : S 2 (Ng G) * S 3 (Ng G) + X * S 2 (Ng H) * S 3 (Ng H) = chip 1 * chip 6 * Ring.inverse (chip 2 * chip 3) := by
  have h := congrArg Ng entry_3_23_neg
  rw [map_mul, map_mul, map_mul, map_sub, map_mul, map_mul, map_mul, Ng_S_ev 2 (by norm_num), Ng_S_ev 2 (by norm_num),
    Ng_S_odd 3 (by decide), Ng_S_odd 3 (by decide), Ng_X, Ng_chim3, chim, show (2 * 1 : ℕ) = 2 by rfl, Ng_P12] at h
  rw [show Ng (chip 6) = chip 6 by rw [chip, Ng_S_ev 6 (by norm_num)],
    show Ng (chip 2) = chip 2 by rw [chip, Ng_S_ev 2 (by norm_num)]] at h
  apply eq_mul_inv_of ((chip_unit 2).mul (chip_unit 3))
  linear_combination h

end Forty
