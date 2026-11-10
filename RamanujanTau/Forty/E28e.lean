/-
# Entry 3.28(ii): Yesilyurt's level identities (3.1), (3.3), (3.15) and the 2-dissection (3.23)

With `Q = q¹⁷`, `U = G(Q)H(q²) − q³G(q²)H(Q)` (`U28`), `V = G(q)G(Q²) + q⁷H(q)H(Q²)` (`V28`),
`a1 = χ(q)`, `a2 = χ(−q)`, `b1 = χ(Q)`, `b2 = χ(−Q)`, `c = χ(−q²)`, `d = χ(−Q²)`:
* `Y14`: `U b2 = V a2` (Entry 3.28(i), Bressoud);
* `Y13A`: `a2² c b2 d V = a2 d² − q² b2 c²` (Yesilyurt (3.13), pulled back from `E28p`);
* `Y21`: `c² c4 d d4 V(q)V(−q) = c d4² + q⁴ d c4²` (his (3.21) = `E28m`), `c4 = χ(−q⁴)`, `d4 = χ(−Q⁴)`;
* `Y15`: `2q U(q²) = c² (V(−q) a1² − V(q) a2²)` (his (3.14)/(3.15): a `3 × 3` determinant, Entries 3.2 and 3.20);
* `phi_dis`: `φ(q) − φ(−q) = 4qψ(q⁸)`, `φ(q) + φ(−q) = 2φ(q⁴)` (product forms), giving his (3.23).
-/
import RamanujanTau.Forty.E28c
import RamanujanTau.Forty.E28
import RamanujanTau.Forty.E26
import RamanujanTau.Forty.E17
import RamanujanTau.Forty.E28d

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC PowerSeries
open RankProof (Pinf isUnit_Pinf)

local notation "φ" => RamanujanTau.Septic.phi

/-- `U(q) = G(q¹⁷)H(q²) − q³G(q²)H(q¹⁷)`. -/
noncomputable def U28 : PowerSeries ℤ := S 17 G * S 2 H - X ^ 3 * S 2 G * S 17 H

lemma SX28 (a : ℕ) [NeZero a] : S a X = X ^ a := RankProof.Ea_X a _

lemma Psp (b a : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a) {a2 b2 : ℕ} (h1 : a2 = 2 * a) (h2 : b2 = b + a) :
    Pinf b a = Pinf b a2 * Pinf b2 a2 := Pinf_split' b a hb ha h1 h2

lemma Pne (b a : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a) : Pinf b a ≠ 0 := Pinf_ne b a hb ha

/-- Entry 3.28(i), cleared: `U χ(−Q) = V χ(−q)`. -/
theorem Y14 : U28 * Pinf 17 34 = V28 * Pinf 1 2 := by
  have h := entry_3_28_i
  have hu := Ring.inverse_mul_cancel _ (isUnit_Pinf 17 34 (by norm_num) (by norm_num))
  simp only [chim, Nat.reduceMul] at h
  rw [U28, h, V28]
  linear_combination ((G * S 34 G + X ^ 7 * H * S 34 H) * Pinf 1 2) * hu

lemma Ng_U28 : Ng U28 = S 17 (Ng G) * S 2 H + X ^ 3 * S 2 G * S 17 (Ng H) := by
  simp only [U28, map_sub, map_mul, map_pow, Ng_S_ev 2 (by norm_num), Ng_S_odd 17 (by decide), Ng_X]
  ring

lemma Ng_P1734 : Ng (Pinf 17 34) = chip 17 := by
  rw [chip, ← Ng_S_odd 17 (by decide), S_Pinf 17 1 2 le_rfl (by norm_num)]

lemma Ng_chip17 : Ng (chip 17) = Pinf 17 34 := by rw [← Ng_P1734, Ng_Ng]

lemma S2_V28 : S 2 V28 = S 2 G * S 68 G + X ^ 14 * S 2 H * S 68 H := by
  simp only [V28, map_add, map_mul, map_pow, S_S 2 34 68 rfl, SX28]
  ring

lemma S2_U28 : S 2 U28 = S 34 G * S 4 H - X ^ 6 * S 4 G * S 34 H := by
  simp only [U28, map_sub, map_mul, map_pow, S_S 2 17 34 rfl, S_S 2 2 4 rfl, SX28]
  ring

/-- the `q²` atoms of `E28p`/`E28m`. -/
lemma E28_atoms : Pinf 2 4 = Pinf 2 8 * Pinf 6 8 ∧ Pinf 34 68 = Pinf 34 136 * Pinf 102 136 ∧
    Pinf 2 2 = Pinf 2 4 * Pinf 4 8 * Pinf 8 8 ∧ Pinf 34 34 = Pinf 34 68 * Pinf 68 136 * Pinf 136 136 := by
  refine ⟨Psp 2 4 (by norm_num) (by norm_num) rfl rfl, Psp 34 68 (by norm_num) (by norm_num) rfl rfl, ?_, ?_⟩
  · rw [Psp 2 2 (by norm_num) (by norm_num) (rfl : 4 = 2 * 2) rfl, Psp 4 4 (by norm_num) (by norm_num) (rfl : 8 = 2 * 4) rfl]
    ring
  · rw [Psp 34 34 (by norm_num) (by norm_num) (rfl : 68 = 2 * 34) rfl,
      Psp 68 68 (by norm_num) (by norm_num) (rfl : 136 = 2 * 68) rfl]
    ring

/-- Yesilyurt (3.13), cleared: `a2² c b2 d V = a2 d² − q² b2 c²`. -/
theorem Y13A : Pinf 1 2 ^ 2 * Pinf 2 4 * Pinf 17 34 * Pinf 34 68 * V28 =
    Pinf 1 2 * Pinf 34 68 ^ 2 - X ^ 2 * Pinf 17 34 * Pinf 2 4 ^ 2 := by
  apply S_inj 2
  simp only [map_mul, map_sub, map_pow, SX28, S2_V28,
    S_P' 2 1 2 le_rfl (by norm_num) (rfl : 2 = 2 * 1) (rfl : 4 = 2 * 2),
    S_P' 2 2 4 (by norm_num) (by norm_num) (rfl : 4 = 2 * 2) (rfl : 8 = 2 * 4),
    S_P' 2 17 34 (by norm_num) (by norm_num) (rfl : 34 = 2 * 17) (rfl : 68 = 2 * 34),
    S_P' 2 34 68 (by norm_num) (by norm_num) (rfl : 68 = 2 * 34) (rfl : 136 = 2 * 68)]
  have h := E28p
  obtain ⟨a1, a2, a3, a4⟩ := E28_atoms
  simp only [J, Nat.reduceSub] at h
  rw [← a1, ← a2, a3, a4] at h
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 (Pne 8 8 (by norm_num) (by norm_num)))
    (Pne 136 136 (by norm_num) (by norm_num)))
  linear_combination -h

/-- Yesilyurt (3.21), cleared: `c² c4 d d4 V(q)V(−q) = c d4² + q⁴ d c4²`. -/
theorem Y21 : Pinf 2 4 ^ 2 * Pinf 4 8 * Pinf 34 68 * Pinf 68 136 * (V28 * Ng V28) =
    Pinf 2 4 * Pinf 68 136 ^ 2 + X ^ 4 * Pinf 34 68 * Pinf 4 8 ^ 2 := by
  have h := E28m
  obtain ⟨a1, a2, a3, a4⟩ := E28_atoms
  simp only [J, Nat.reduceSub] at h
  rw [← a1, ← a2, a3, a4] at h
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 (Pne 8 8 (by norm_num) (by norm_num)))
    (Pne 136 136 (by norm_num) (by norm_num)))
  linear_combination -h

/-- Yesilyurt (3.15), cleared: `2q U(q²) = c² (V(−q) χ²(q) − V(q) χ²(−q))`. -/
theorem Y15 : 2 * X * S 2 U28 = Pinf 2 4 ^ 2 * (Ng V28 * chip 1 ^ 2 - V28 * Pinf 1 2 ^ 2) := by
  have e20 := entry_3_20
  have e2 := entry_3_2
  have e2n := congrArg Ng entry_3_2
  simp only [map_mul, map_add, map_pow, Ng_S_ev 4 (by norm_num), Ng_X, Ng_chip1] at e2n
  simp only [chim, Nat.reduceMul] at e20
  have hinv := Ring.inverse_mul_cancel _ ((isUnit_Pinf 2 4 (by norm_num) (by norm_num)).pow 2)
  rw [S2_U28, Ng_V28, V28]
  linear_combination (-(X * (S 34 G * S 4 H - X ^ 6 * S 4 G * S 34 H) * Pinf 2 4 ^ 2)) * e20
    - (Pinf 2 4 ^ 2 * (G * S 34 G + X ^ 7 * H * S 34 H)) * e2n
    + (Pinf 2 4 ^ 2 * (Ng G * S 34 G - X ^ 7 * Ng H * S 34 H)) * e2
    - (2 * X * (S 34 G * S 4 H - X ^ 6 * S 4 G * S 34 H)) * hinv

private lemma hm2r : 1 ≤ 2 := by norm_num
private lemma hm8r : 1 ≤ 8 := by norm_num

/-- the 2-dissection of `φ` in product form: `(φ(q) − φ(−q)) (q⁸;q¹⁶) = 4q (q¹⁶;q¹⁶)` and
`(φ(q) + φ(−q)) φ(q⁴)-denominator`: `(φ(q) + φ(−q)) J_{4,8} = 2 J_{8,16}²`. -/
theorem phi_dis : (φ - J 1 2) * Pinf 8 16 = 4 * X * Pinf 16 16 ∧ (φ + J 1 2) * J 4 8 = 2 * (J 8 16 * J 8 16) := by
  have d1 := dis2 hm2r hm8r rfl 1 (by norm_num : (-1 : ℂ) ≠ 0) 4 0 1 (-1) 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have d2 := dis2 hm2r hm8r rfl 1 one_ne_zero 4 0 1 (-1) (-1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hA := θ_bar hm2r 1 le_rfl (by norm_num)
  have hC := θ_bar hm8r 4 (by norm_num) (by norm_num)
  have hD := θ_bar0 hm8r
  norm_num at hA hC hD
  have pA := congrArg ι phi_J
  simp only [map_mul] at hA hC hD pA
  have iA : θ hm2r 1 (-1) = ι φ := by
    apply mul_right_cancel₀ (ι_ne29 (J_ne29 1 2 le_rfl (by norm_num)))
    rw [hA, pA]
  have iB : θ hm2r 1 1 = ι (J 1 2) := θu' hm2r 1 (by norm_num) le_rfl (by norm_num)
  rw [iA] at d1
  rw [iB, mono_neg1] at d2
  constructor
  · apply ι_inj
    simp only [map_mul, map_sub, map_ofNat, ι_X]
    rw [d1, d2]
    linear_combination (2 * mono 1 1) * hD
  · apply ι_inj
    simp only [map_mul, map_add, map_ofNat]
    rw [d1, d2]
    linear_combination 2 * hC

end Forty
