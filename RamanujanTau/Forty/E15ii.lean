/-
# Entry 3.15(ii)

`G(q³)G(q⁷) + q²H(q³)H(q⁷) = (1/2√q)[χ(q^{1/2})χ(−q^{3/2})χ(q^{7/2})χ(−q^{21/2}) − χ(−q^{1/2})χ(q^{3/2})χ(−q^{7/2})χ(q^{21/2})]`,
stated with `q ↦ q²` (`entry_3_15_ii`):
`A(q) − A(−q) = 2q L(q²)`, `A(q) = χ(q)χ(−q³)χ(q⁷)χ(−q²¹)`, `L(q) = G(q³)G(q⁷) + q²H(q³)H(q⁷)`.

No modular forms and no new theta identity are used: only Entries 3.2, 3.7–3.10, 3.15(i) and 3.20, at `±q`, `q²`,
`q⁷`, `q¹⁴`.
* Cramer's rule (`E15iiA`): the systems (3.8, 3.7 at `q²`) for `G(q⁶)`, `H(q⁶)` and (3.10, 3.9 at `q²`) for `G(q¹⁴)`,
  `H(q¹⁴)` have the same coefficient vectors `(G(q), H(q))`, `(G(q⁴), H(q⁴))`; their determinant is Entry 3.2. So
  `χ²(q)L(q²)` and (at `−q`) `χ²(−q)L(q²)` are sums of two eta quotients (`F1`, `F2`). The same at level 21 through
  `L₂(q²) = L(q²)` (3.15(i)) gives `F3`, `F4`, with determinant Entry 3.2 at `±q⁷`.
* Entries 3.10 at `±q`, 3.20 and 3.9 at `q²` give the degree-7 equation `M7`:
  `χ(q)χ(q⁷) − χ(−q)χ(−q⁷) = 2q/(χ(−q²)χ(−q¹⁴))`.
* `F1`–`F4`, `M7` imply `t·g = 0` (times a unit) for `t = A(q) − A(−q) − 2qL(q²)` and
  `g = χ(−q³)χ³(−q⁷) − χ³(−q)χ(−q²¹)` (`alg15ii`). The coefficient of `q` in `g` is `3`, so `g ≠ 0` and `t = 0`.
-/
import RamanujanTau.Forty.E15iiA
import RamanujanTau.Forty.E15
import RamanujanTau.Forty.E02
import RamanujanTau.Forty.E24
import RamanujanTau.Forty.E35h

set_option autoImplicit false

namespace Forty
open PowerSeries
open RankProof (Pinf isUnit_Pinf)

private lemma clr' {a b c : PowerSeries ℤ} (h : a = b * Ring.inverse c) (hc : IsUnit c) : a * c = b := by
  rw [h, mul_assoc, Ring.inverse_mul_cancel _ hc, mul_one]

private lemma SXi (a : ℕ) [NeZero a] : S a X = X ^ a := RankProof.Ea_X a _

private lemma uchim (k : ℕ) (hk : 1 ≤ k) : IsUnit (chim k) := isUnit_Pinf k (2 * k) hk (by omega)

/-- `S a (χ(−q^b)) = χ(−q^{ab})`. -/
lemma S_chim (a : ℕ) [NeZero a] (b c : ℕ) (hb : 1 ≤ b) (h : c = a * b) : S a (chim b) = chim c := by
  subst h
  rw [chim, chim, S_Pinf a b (2 * b) hb (by omega), show a * (2 * b) = 2 * (a * b) by ring]

/-- `S a (χ(q^b)) = χ(q^{ab})`. -/
lemma S_chip15 (a b c : ℕ) [NeZero a] [NeZero b] [NeZero c] (h : c = a * b) : S a (chip b) = chip c := by
  rw [chip, chip, S_S a b c h]

/-- `χ(−q^{2k}) = χ(q^k)χ(−q^k)`. -/
lemma chim_two (k c : ℕ) [NeZero k] (h : c = 2 * k) : chim c = chip k * chim k := by
  subst h
  rw [chim, chim, chip_mul k, show 2 * (2 * k) = 4 * k by ring]

/-- `χ(−q^k) ↦ χ(q^k)` under `q ↦ −q`, `k` odd. -/
lemma Ng_chim_odd (k : ℕ) [NeZero k] (hk : Odd k) : Ng (chim k) = chip k := by
  rw [chim, show 2 * k = k * 2 by ring, show Pinf k (k * 2) = S k (Pinf 1 2) by
    rw [S_Pinf k 1 2 le_rfl (by norm_num), mul_one], Ng_S_odd k hk, chip]

lemma Ng_chip_odd (k : ℕ) [NeZero k] (hk : Odd k) : Ng (chip k) = chim k := by
  rw [← Ng_chim_odd k hk, Ng_Ng]

/-- `L(q²)`, the bracket of Entry 3.15 at `q²`. -/
noncomputable abbrev L15 : PowerSeries ℤ := S 6 G * S 14 G + X ^ 4 * S 6 H * S 14 H

/-! ### The entry instances -/

lemma i15_8 : (S 6 G * H - X * G * S 6 H) * chim 3 = chim 1 := clr' entry_3_8 (uchim 3 (by norm_num))

lemma i15_8n : (S 6 G * Ng H + X * Ng G * S 6 H) * chip 3 = chip 1 := by
  have h := congrArg Ng i15_8
  simp only [map_mul, map_sub, Ng_S_ev 6 (by norm_num), Ng_X, Ng_chim_odd 3 (by decide),
    Ng_chim_odd 1 (by decide)] at h
  linear_combination h

lemma i15_7q2 : (S 4 G * S 6 G + X ^ 2 * S 4 H * S 6 H) * (chip 1 * chim 1) = chip 3 * chim 3 := by
  have h := congrArg (S 2) (clr' entry_3_7 (uchim 1 le_rfl))
  simp only [map_mul, map_add, SXi, S_S 2 2 4 rfl, S_S 2 3 6 rfl, S_chim 2 1 2 le_rfl rfl,
    S_chim 2 3 6 (by norm_num) rfl, chim_two 1 2 rfl, chim_two 3 6 rfl] at h
  exact h

lemma i15_10 : (G * S 14 G + X ^ 3 * H * S 14 H) * chim 1 = chim 7 := clr' entry_3_10 (uchim 1 le_rfl)

lemma i15_10n : (Ng G * S 14 G - X ^ 3 * Ng H * S 14 H) * chip 1 = chip 7 := by
  have h := congrArg Ng i15_10
  simp only [map_mul, map_add, map_pow, Ng_S_ev 14 (by norm_num), Ng_X, Ng_chim_odd 7 (by decide),
    Ng_chim_odd 1 (by decide)] at h
  linear_combination h

lemma i15_9 : (S 7 G * S 2 H - X * S 2 G * S 7 H) * chim 7 = chim 1 := clr' entry_3_9 (uchim 7 (by norm_num))

lemma i15_9q2 : (S 14 G * S 4 H - X ^ 2 * S 4 G * S 14 H) * (chip 7 * chim 7) = chip 1 * chim 1 := by
  have h := congrArg (S 2) i15_9
  simp only [map_mul, map_sub, SXi, S_S 2 7 14 rfl, S_S 2 2 4 rfl, S_chim 2 1 2 le_rfl rfl,
    S_chim 2 7 14 (by norm_num) rfl, chim_two 1 2 rfl, chim_two 7 14 rfl] at h
  exact h

lemma i15_9n : (S 7 (Ng G) * S 2 H + X * S 2 G * S 7 (Ng H)) * chip 7 = chip 1 := by
  have h := congrArg Ng i15_9
  simp only [map_mul, map_sub, Ng_S_ev 2 (by norm_num), Ng_S_odd 7 (by decide), Ng_X,
    Ng_chim_odd 7 (by decide), Ng_chim_odd 1 (by decide)] at h
  linear_combination h

lemma i15_2 : G * S 4 G + X * H * S 4 H = chip 1 ^ 2 := entry_3_2

lemma i15_2n : Ng G * S 4 G - X * Ng H * S 4 H = chim 1 ^ 2 := by
  have h := congrArg Ng entry_3_2
  simp only [map_mul, map_add, map_pow, Ng_S_ev 4 (by norm_num), Ng_X, Ng_chip_odd 1 (by decide)] at h
  linear_combination h

lemma i15_8q7 : (S 42 G * S 7 H - X ^ 7 * S 7 G * S 42 H) * chim 21 = chim 7 := by
  have h := congrArg (S 7) i15_8
  simp only [map_mul, map_sub, SXi, S_S 7 6 42 rfl, S_chim 7 3 21 (by norm_num) rfl,
    S_chim 7 1 7 le_rfl rfl] at h
  linear_combination h

lemma i15_8nq7 : (S 42 G * S 7 (Ng H) + X ^ 7 * S 7 (Ng G) * S 42 H) * chip 21 = chip 7 := by
  have h := congrArg (S 7) i15_8n
  simp only [map_mul, map_add, SXi, S_S 7 6 42 rfl, S_chip15 7 3 21 rfl, S_chip15 7 1 7 rfl] at h
  linear_combination h

lemma i15_7q14 : (S 28 G * S 42 G + X ^ 14 * S 28 H * S 42 H) * (chip 7 * chim 7) = chip 21 * chim 21 := by
  have h := congrArg (S 7) i15_7q2
  simp only [map_mul, map_add, map_pow, SXi, S_S 7 4 28 rfl, S_S 7 6 42 rfl, S_chip15 7 1 7 rfl,
    S_chip15 7 3 21 rfl, S_chim 7 1 7 le_rfl rfl, S_chim 7 3 21 (by norm_num) rfl, ← pow_mul] at h
  linear_combination h

lemma i15_10q2 : (S 2 G * S 28 G + X ^ 6 * S 2 H * S 28 H) * (chip 1 * chim 1) = chip 7 * chim 7 := by
  have h := congrArg (S 2) i15_10
  simp only [map_mul, map_add, map_pow, SXi, S_S 2 14 28 rfl, S_chim 2 1 2 le_rfl rfl,
    S_chim 2 7 14 (by norm_num) rfl, chim_two 1 2 rfl, chim_two 7 14 rfl, ← pow_mul] at h
  linear_combination h

lemma i15_2q7 : S 7 G * S 28 G + X ^ 7 * S 7 H * S 28 H = chip 7 ^ 2 := by
  have h := congrArg (S 7) entry_3_2
  simp only [map_mul, map_add, map_pow, SXi, S_S 7 4 28 rfl, S_chip15 7 1 7 rfl] at h
  linear_combination h

lemma i15_2nq7 : S 7 (Ng G) * S 28 G - X ^ 7 * S 7 (Ng H) * S 28 H = chim 7 ^ 2 := by
  have h := congrArg (S 7) i15_2n
  simp only [map_mul, map_sub, map_pow, SXi, S_S 7 4 28 rfl, S_chim 7 1 7 le_rfl rfl] at h
  linear_combination h

lemma i15_20 : (G * Ng H + Ng G * H) * (chip 1 * chim 1) ^ 2 = 2 := by
  have h := clr' entry_3_20 ((uchim 2 (by norm_num)).pow 2)
  rw [chim_two 1 2 rfl] at h
  exact h

lemma i15_15 : L15 = S 42 G * S 2 H - X ^ 8 * S 2 G * S 42 H := by
  have h := congrArg (S 2) entry_3_15_i
  simp only [map_mul, map_add, map_sub, map_pow, SXi, S_S 2 3 6 rfl, S_S 2 7 14 rfl, S_S 2 21 42 rfl,
    ← pow_mul] at h
  rw [L15]; linear_combination h

/-! ### The relations `F1`–`F4`, `M7` -/

theorem F15_1 : L15 * chim 1 ^ 2 * chim 3 * chim 7 * chip 1 ^ 3 * chip 7 - chim 1 ^ 4 * chip 1 ^ 2 * X
    - chim 3 ^ 2 * chim 7 ^ 2 * chip 3 * chip 7 = 0 :=
  cramer1 X L15 G H (S 4 G) (S 4 H) (S 6 G) (S 6 H) (S 14 G) (S 14 H) (chip 1) (chim 1) (chip 3) (chim 3)
    (chip 7) (chim 7) rfl i15_8 i15_7q2 i15_10 i15_9q2 i15_2

theorem F15_2 : L15 * chim 1 ^ 3 * chim 7 * chip 1 ^ 2 * chip 3 * chip 7 + chim 1 ^ 2 * chip 1 ^ 4 * X
    - chim 3 * chim 7 * chip 3 ^ 2 * chip 7 ^ 2 = 0 :=
  cramer2 X L15 (Ng G) (Ng H) (S 4 G) (S 4 H) (S 6 G) (S 6 H) (S 14 G) (S 14 H) (chip 1) (chim 1) (chip 3)
    (chim 3) (chip 7) (chim 7) rfl i15_8n i15_7q2 i15_10n i15_9q2 i15_2n

theorem F15_3 : L15 * chim 1 * chim 21 * chim 7 ^ 2 * chip 1 * chip 7 ^ 3 - chim 1 ^ 2 * chim 21 ^ 2 * chip 1 * chip 21
    - chim 7 ^ 4 * chip 7 ^ 2 * X = 0 :=
  cramer3 X L15 (S 2 G) (S 2 H) (S 7 G) (S 7 H) (S 28 G) (S 28 H) (S 42 G) (S 42 H) (chip 1) (chim 1) (chip 7)
    (chim 7) (chip 21) (chim 21) i15_15 i15_8q7 i15_7q14 i15_9 i15_10q2 i15_2q7

theorem F15_4 : L15 * chim 1 * chim 7 ^ 3 * chip 1 * chip 21 * chip 7 ^ 2 - chim 1 * chim 21 * chip 1 ^ 2 * chip 21 ^ 2
    + chim 7 ^ 2 * chip 7 ^ 4 * X = 0 :=
  cramer4 X L15 (S 2 G) (S 2 H) (S 7 (Ng G)) (S 7 (Ng H)) (S 28 G) (S 28 H) (S 42 G) (S 42 H) (chip 1) (chim 1)
    (chip 7) (chim 7) (chip 21) (chim 21) i15_15 i15_8nq7 i15_7q14 i15_9n i15_10q2 i15_2nq7

/-- The degree-7 modular equation `χ(q)χ(q⁷) − χ(−q)χ(−q⁷) = 2q/(χ(−q²)χ(−q¹⁴))`, from Entries 3.2, 3.9, 3.10, 3.20. -/
theorem M7_chi : -chim 1 ^ 2 * chim 7 ^ 2 * chip 1 * chip 7 + chim 1 * chim 7 * chip 1 ^ 2 * chip 7 ^ 2 - 2 * X = 0 :=
  cramer7 X G H (Ng G) (Ng H) (S 4 G) (S 4 H) (S 14 G) (S 14 H) (chip 1) (chim 1) (chip 7) (chim 7)
    i15_10 i15_10n i15_2 i15_2n i15_20 i15_9q2

/-! ### The non-vanishing factor -/

local notation "π2" => Ideal.Quotient.mk I2

private lemma π2_chim (k : ℕ) (hk : 2 ≤ k) : π2 (chim k) = 1 := by
  rw [chim, π2Pinf k (2 * k) (by omega) (by omega), hx2n k hk, sub_zero]

private lemma π2_chim1 : π2 (chim 1) = 1 - π2 X := by
  rw [chim, π2Pinf 1 (2 * 1) le_rfl (by norm_num), pow_one]

lemma g15_ne : chim 3 * chim 7 ^ 3 - chim 1 ^ 3 * chim 21 ≠ 0 := by
  intro h
  have h1 := congrArg π2 h
  simp only [map_sub, map_mul, map_pow, map_zero, π2_chim 3 (by norm_num), π2_chim 7 (by norm_num),
    π2_chim 21 (by norm_num), π2_chim1] at h1
  have h2 : π2 (3 * X) = 0 := by
    rw [map_mul, map_ofNat]
    linear_combination h1 + (3 - π2 X) * hx2
  obtain ⟨c, hc⟩ := π2_zero h2
  have h3 := congrArg (coeff 1) hc
  rw [coeff_X_pow_mul', if_neg (by norm_num)] at h3
  have h4 := coeff_succ_mul_X 0 (3 : PowerSeries ℤ)
  simp only [zero_add] at h4
  rw [h4] at h3
  have h5 : constantCoeff (3 : PowerSeries ℤ) = 3 := map_ofNat _ 3
  rw [coeff_zero_eq_constantCoeff_apply, h5] at h3
  norm_num at h3

/-- **Entry 3.15(ii)** (with `q ↦ q²`):
`χ(q)χ(−q³)χ(q⁷)χ(−q²¹) − χ(−q)χ(q³)χ(−q⁷)χ(q²¹) = 2q{G(q⁶)G(q¹⁴) + q⁴H(q⁶)H(q¹⁴)}`. -/
theorem entry_3_15_ii : chip 1 * chim 3 * chip 7 * chim 21 - chim 1 * chip 3 * chim 7 * chip 21 =
    2 * X * (S 6 G * S 14 G + X ^ 4 * S 6 H * S 14 H) := by
  have h := alg15ii L15 (chip 1) (chim 1) (chip 3) (chim 3) (chip 7) (chim 7) (chip 21) (chim 21) X
    F15_1 F15_2 F15_3 F15_4 M7_chi
  have hmo : chip 1 * chim 1 * chip 3 * chim 3 * chip 7 * chim 7 * chip 21 * chim 21 * X ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (chip_unit 1).ne_zero (uchim 1 le_rfl).ne_zero) (chip_unit 3).ne_zero)
      (uchim 3 (by norm_num)).ne_zero) (chip_unit 7).ne_zero) (uchim 7 (by norm_num)).ne_zero)
      (chip_unit 21).ne_zero) (uchim 21 (by norm_num)).ne_zero) X_ne_zero
  have h' := (mul_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left two_ne)).resolve_right hmo)).resolve_right
    g15_ne
  rw [L15] at h'
  linear_combination h'

/-- **Entry 3.15(ii)**, other bracket: the same with `G(q⁴²)H(q²) − q⁸G(q²)H(q⁴²)`. -/
theorem entry_3_15_ii' : chip 1 * chim 3 * chip 7 * chim 21 - chim 1 * chip 3 * chim 7 * chip 21 =
    2 * X * (S 42 G * S 2 H - X ^ 8 * S 2 G * S 42 H) := by
  rw [entry_3_15_ii, ← i15_15]

/-- **Entry 3.15(ii)** in the form `A(q) − A(−q) = 2qL(q²)` with `A(−q)` written as `Ng A`. -/
theorem entry_3_15_ii_Ng : chip 1 * chim 3 * chip 7 * chim 21 - Ng (chip 1 * chim 3 * chip 7 * chim 21) =
    2 * X * (S 6 G * S 14 G + X ^ 4 * S 6 H * S 14 H) := by
  rw [map_mul, map_mul, map_mul, Ng_chip_odd 1 (by decide), Ng_chim_odd 3 (by decide), Ng_chip_odd 7 (by decide),
    Ng_chim_odd 21 (by decide), ← entry_3_15_ii]

end Forty
