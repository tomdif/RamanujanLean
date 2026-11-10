/-
# Entry 3.28(ii): Yesilyurt's (3.1)–(3.6) as power-series identities

Notation: `a1 = χ(q) = chip 1`, `a2 = χ(−q) = Pinf 1 2`, `b1 = χ(Q) = chip 17`, `b2 = χ(−Q) = Pinf 17 34`,
`e1 = χ(q²)`, `e2 = χ(Q²)`, `g1 = χ(q⁴)`, `g2 = χ(Q⁴)`; `U = U28`, `V = V28`.
All statements are in the shape of the hypotheses of `alg28` (`E28d.lean`), with `χ(−q²) = a1a2`,
`χ(−q⁴) = e1a1a2`, `χ(−q⁸) = g1e1a1a2` and the same at `Q`.
-/
import RamanujanTau.Forty.E28e
import RamanujanTau.Forty.E28f

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC PowerSeries
open RankProof (Pinf isUnit_Pinf)

local notation "φ" => RamanujanTau.Septic.phi

lemma S_chip (k a b : ℕ) [NeZero k] [NeZero a] [NeZero b] (h : b = k * a) : S k (chip a) = chip b := by
  rw [chip, chip, S_S k a b h]

/-- `χ(−q^{2a}) = χ(q^a) χ(−q^a)`. -/
lemma rP (a : ℕ) [NeZero a] {b M : ℕ} (h1 : b = 2 * a) (h2 : M = 4 * a) : Pinf b M = chip a * Pinf a (2 * a) := by
  subst h1 h2; exact (chip_mul a).symm

lemma r24 : Pinf 2 4 = chip 1 * Pinf 1 2 := rP 1 rfl rfl
lemma r48 : Pinf 4 8 = chip 2 * (chip 1 * Pinf 1 2) := by rw [rP 2 rfl rfl, ← r24]
lemma r816 : Pinf 8 16 = chip 4 * (chip 2 * (chip 1 * Pinf 1 2)) := by rw [rP 4 rfl rfl, ← r48]
lemma r3468 : Pinf 34 68 = chip 17 * Pinf 17 34 := rP 17 rfl rfl
lemma r68136 : Pinf 68 136 = chip 34 * (chip 17 * Pinf 17 34) := by rw [rP 34 rfl rfl, ← r3468]
lemma r136272 : Pinf 136 272 = chip 68 * (chip 34 * (chip 17 * Pinf 17 34)) := by rw [rP 68 rfl rfl, ← r68136]

lemma S2P12 : S 2 (Pinf 1 2) = Pinf 2 4 := S_P' 2 1 2 le_rfl (by norm_num) rfl rfl
lemma S2P1734 : S 2 (Pinf 17 34) = Pinf 34 68 := S_P' 2 17 34 (by norm_num) (by norm_num) rfl rfl
lemma S4P12 : S 4 (Pinf 1 2) = Pinf 4 8 := S_P' 4 1 2 le_rfl (by norm_num) rfl rfl
lemma S4P1734 : S 4 (Pinf 17 34) = Pinf 68 136 := S_P' 4 17 34 (by norm_num) (by norm_num) rfl rfl

lemma S2S2 (f : PowerSeries ℤ) : S 2 (S 2 f) = S 4 f := S_S 2 2 4 rfl f

/-- (3.1): `c d b2 U = b1 d − q² a1 c`. -/
theorem Y1 : chip 1 * Pinf 1 2 * (chip 17 * Pinf 17 34) * Pinf 17 34 * U28 =
    chip 17 * (chip 17 * Pinf 17 34) - X ^ 2 * chip 1 * (chip 1 * Pinf 1 2) := by
  have hA := Y13A
  rw [r24, r3468] at hA
  exact glue1 X (chip 1) (Pinf 1 2) (chip 17) (Pinf 17 34) U28 V28 (Pne 1 2 le_rfl (by norm_num))
    (Pne 17 34 (by norm_num) (by norm_num)) hA Y14

lemma Y13Am : chip 1 ^ 2 * (chip 1 * Pinf 1 2) * chip 17 * (chip 17 * Pinf 17 34) * Ng V28 =
    chip 1 * (chip 17 * Pinf 17 34) ^ 2 - X ^ 2 * chip 17 * (chip 1 * Pinf 1 2) ^ 2 := by
  have h := congrArg Ng Y13A
  simp only [map_mul, map_sub, map_pow, Ng_P12, Ng_P1734, Ng_X, Ng_Pinf_even 1 2 le_rfl (by norm_num),
    Ng_Pinf_even 17 34 (by norm_num) (by norm_num)] at h
  simp only [Nat.reduceMul] at h
  rw [r24, r3468] at h
  linear_combination h

lemma Y14m : Ng U28 * chip 17 = Ng V28 * chip 1 := by
  have h := congrArg Ng Y14
  simp only [map_mul, Ng_P12, Ng_P1734] at h
  exact h

lemma Y14q : S 2 U28 * (chip 17 * Pinf 17 34) = S 2 V28 * (chip 1 * Pinf 1 2) := by
  have h := congrArg (S 2) Y14
  simp only [map_mul, S2P12, S2P1734] at h
  rw [r24, r3468] at h
  exact h

lemma Y14m2 : S 2 (Ng U28) * chip 34 = S 2 (Ng V28) * chip 2 := by
  have h := congrArg (S 2) Y14m
  simp only [map_mul, S_chip 2 17 34 rfl, S_chip 2 1 2 rfl] at h
  exact h

lemma Y14q4 : S 4 U28 * (chip 34 * (chip 17 * Pinf 17 34)) = S 4 V28 * (chip 2 * (chip 1 * Pinf 1 2)) := by
  have h := congrArg (S 4) Y14
  simp only [map_mul, S4P12, S4P1734] at h
  rw [r48, r68136] at h
  exact h

lemma cdne : chip 1 * Pinf 1 2 ≠ 0 := by rw [← r24]; exact Pne 2 4 (by norm_num) (by norm_num)
lemma ddne : chip 17 * Pinf 17 34 ≠ 0 := by rw [← r3468]; exact Pne 34 68 (by norm_num) (by norm_num)
lemma chip_ne (a : ℕ) [NeZero a] : chip a ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  rw [cc_chip, map_zero] at this
  exact one_ne_zero this

/-- (3.2): `2q V(q²) = d (a1 b2 − a2 b1)`. -/
theorem Y2 : 2 * X * S 2 V28 = chip 17 * Pinf 17 34 * (chip 1 * Pinf 17 34 - Pinf 1 2 * chip 17) := by
  have hA := Y13A
  rw [r24, r3468] at hA
  have h15 := Y15
  rw [r24] at h15
  exact glue2 X (chip 1) (Pinf 1 2) (chip 17) (Pinf 17 34) V28 (Ng V28) (S 2 U28) (S 2 V28) cdne ddne hA Y13Am
    h15 Y14q

/-- (3.3): `d U(q)U(−q) c4 d4 = e2 d4 + q⁴ e1 c4`. -/
theorem Y3 : chip 17 * Pinf 17 34 * U28 * Ng U28 * (chip 2 * (chip 1 * Pinf 1 2)) * (chip 34 * (chip 17 * Pinf 17 34)) =
    chip 34 * (chip 34 * (chip 17 * Pinf 17 34)) + X ^ 4 * chip 2 * (chip 2 * (chip 1 * Pinf 1 2)) := by
  have hB := Y21
  rw [r48, r68136, r24, r3468] at hB
  exact glue3 X (chip 1) (Pinf 1 2) (chip 17) (Pinf 17 34) (chip 2) (chip 34) U28 (Ng U28) V28 (Ng V28) cdne ddne
    hB Y14 Y14m

/-- (3.1) at `q²`. -/
lemma Y1q2 : chip 2 * (chip 1 * Pinf 1 2) * (chip 34 * (chip 17 * Pinf 17 34)) * (chip 17 * Pinf 17 34) * S 2 U28 =
    chip 34 * (chip 34 * (chip 17 * Pinf 17 34)) - X ^ 4 * chip 2 * (chip 2 * (chip 1 * Pinf 1 2)) := by
  have h := congrArg (S 2) Y1
  simp only [map_mul, map_sub, map_pow, S2P12, S2P1734, S_chip 2 17 34 rfl, S_chip 2 1 2 rfl, SX28] at h
  rw [r24, r3468] at h
  linear_combination h

/-- (3.5): `(S(q)S(−q) − S(q²)) T(q²) = 4q⁴`. -/
theorem Y5 : (U28 * V28 * (Ng U28 * Ng V28) - S 2 U28 * S 2 V28) * (chip 1 * Pinf 1 2 * (chip 17 * Pinf 17 34)) ^ 2 =
    4 * X ^ 4 :=
  alg5 X (chip 1) (Pinf 1 2) (chip 17) (Pinf 17 34) (chip 2) (chip 34) U28 (Ng U28) V28 (Ng V28) (S 2 U28) (S 2 V28)
    cdne ddne (chip_ne 2) (chip_ne 34) Y14 Y14m Y14q Y3 Y1q2

/-- (3.23) at `q`, in product form: `2χ²(q⁴) = χ(−q²)χ(−q⁴)(χ²(q) + χ²(−q))`,
`4q = χ(−q²)χ(−q⁴)χ²(−q⁸)(χ²(q) − χ²(−q))`. -/
theorem J23 : 2 * chip 4 ^ 2 = Pinf 2 4 * Pinf 4 8 * (chip 1 ^ 2 + Pinf 1 2 ^ 2) ∧
    4 * X = Pinf 2 4 * Pinf 4 8 * Pinf 8 16 ^ 2 * (chip 1 ^ 2 - Pinf 1 2 ^ 2) := by
  obtain ⟨d1, d2⟩ := phi_dis
  have hφ := phi_chip
  have j12 : J 1 2 = Pinf 1 2 ^ 2 * Pinf 2 2 := by simp only [J, Nat.reduceSub]; ring
  have j48 : J 4 8 = Pinf 4 8 ^ 2 * Pinf 8 8 := by simp only [J, Nat.reduceSub]; ring
  have j816 : J 8 16 = Pinf 8 16 ^ 2 * Pinf 16 16 := by simp only [J, Nat.reduceSub]; ring
  have p22 : Pinf 2 2 = Pinf 2 4 * Pinf 4 8 * Pinf 8 16 * Pinf 16 16 := by
    rw [Psp 2 2 (by norm_num) (by norm_num) (rfl : 4 = 2 * 2) rfl, Psp 4 4 (by norm_num) (by norm_num) (rfl : 8 = 2 * 4) rfl,
      Psp 8 8 (by norm_num) (by norm_num) (rfl : 16 = 2 * 8) rfl]
    ring
  have p88 : Pinf 8 8 = Pinf 8 16 * Pinf 16 16 := Psp 8 8 (by norm_num) (by norm_num) (rfl : 16 = 2 * 8) rfl
  have c816 : Pinf 8 16 = chip 4 * Pinf 4 8 := rP 4 rfl rfl
  rw [hφ, j12, p22] at d1 d2
  rw [j48, j816, p88] at d2
  have n16 := Pne 16 16 (by norm_num) (by norm_num)
  have n816 := Pne 8 16 (by norm_num) (by norm_num)
  have n48 := Pne 4 8 (by norm_num) (by norm_num)
  constructor
  · apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (pow_ne_zero 4 n48) (pow_ne_zero 2 (chip_ne 4))) (pow_ne_zero 2 n16))
    rw [c816] at d2
    linear_combination -d2
  · apply mul_left_cancel₀ n16
    linear_combination -d1

/-- (3.23) at `q` in the variables of `alg4`. -/
lemma J23r : 2 * chip 4 ^ 2 = chip 1 * Pinf 1 2 * (chip 2 * (chip 1 * Pinf 1 2)) * (chip 1 ^ 2 + Pinf 1 2 ^ 2) ∧
    4 * X = chip 1 * Pinf 1 2 * (chip 2 * (chip 1 * Pinf 1 2)) * (chip 4 * (chip 2 * (chip 1 * Pinf 1 2))) ^ 2 *
      (chip 1 ^ 2 - Pinf 1 2 ^ 2) := by
  obtain ⟨h1, h2⟩ := J23
  rw [r48, r24] at h1
  rw [r816, r48, r24] at h2
  exact ⟨h1, h2⟩

/-- (3.23) at `Q = q¹⁷`. -/
lemma J23Q : 2 * chip 68 ^ 2 = chip 17 * Pinf 17 34 * (chip 34 * (chip 17 * Pinf 17 34)) * (chip 17 ^ 2 + Pinf 17 34 ^ 2) ∧
    4 * X ^ 17 = chip 17 * Pinf 17 34 * (chip 34 * (chip 17 * Pinf 17 34)) * (chip 68 * (chip 34 * (chip 17 * Pinf 17 34))) ^ 2 *
      (chip 17 ^ 2 - Pinf 17 34 ^ 2) := by
  obtain ⟨h1, h2⟩ := J23
  have k1 := congrArg (S 17) h1
  have k2 := congrArg (S 17) h2
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, SX28, S_chip 17 4 68 rfl, S_chip 17 1 17 rfl,
    S_P' 17 1 2 le_rfl (by norm_num) (rfl : 17 = 17 * 1) (rfl : 34 = 17 * 2),
    S_P' 17 2 4 (by norm_num) (by norm_num) (rfl : 34 = 17 * 2) (rfl : 68 = 17 * 4),
    S_P' 17 4 8 (by norm_num) (by norm_num) (rfl : 68 = 17 * 4) (rfl : 136 = 17 * 8),
    S_P' 17 8 16 (by norm_num) (by norm_num) (rfl : 136 = 17 * 8) (rfl : 272 = 17 * 16)] at k1 k2
  rw [r68136, r3468] at k1
  rw [r136272, r68136, r3468] at k2
  exact ⟨k1, k2⟩

lemma ccV28 : constantCoeff V28 = 1 := by
  simp only [V28, map_add, map_mul, map_pow, constantCoeff_X, cc_S, cc_G]
  norm_num

lemma S2V_ne : S 2 V28 ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  rw [cc_S, ccV28, map_zero] at this
  exact one_ne_zero this

/-- (3.4): `2 U(−q²) V(q⁴) = d (a1 b2 + a2 b1)`. -/
theorem Y4 : 2 * (S 2 (Ng U28) * S 4 V28) = chip 17 * Pinf 17 34 * (chip 1 * Pinf 17 34 + Pinf 1 2 * chip 17) := by
  have h3q2 := congrArg (S 2) Y3
  simp only [map_mul, map_add, map_pow, S2P12, S2P1734, S_chip 2 17 34 rfl, S_chip 2 1 2 rfl, S_chip 2 2 4 rfl,
    S_chip 2 34 68 rfl, SX28] at h3q2
  rw [r24, r3468] at h3q2
  have h1q4 := congrArg (S 4) Y1
  simp only [map_mul, map_sub, map_pow, S4P12, S4P1734, S_chip 4 17 68 rfl, S_chip 4 1 4 rfl, SX28] at h1q4
  rw [r48, r68136] at h1q4
  obtain ⟨j1, j2⟩ := J23r
  obtain ⟨j3, j4⟩ := J23Q
  exact alg4 X (chip 1) (Pinf 1 2) (chip 17) (Pinf 17 34) (chip 2) (chip 34) (chip 4) (chip 68) (S 2 U28) (S 2 V28)
    (S 2 (Ng U28)) (S 4 U28) (S 4 V28) X_ne_zero cdne (chip_ne 2) (chip_ne 34) ddne S2V_ne two_ne
    (by linear_combination h3q2) (by linear_combination h1q4) j1 j2 j3 j4 Y14q Y14q4 Y2

/-- his (3.28) pulled back: `(U(−q)V(q²))² − q V(q)² = χ³(−Q) χ(−q)`. -/
theorem P28 : (Ng U28 * S 2 V28) ^ 2 - X * V28 ^ 2 = Pinf 17 34 ^ 3 * Pinf 1 2 := by
  have h := alg27 X (chip 1) (Pinf 1 2) (chip 17) (Pinf 17 34) (S 2 V28) (S 2 (Ng U28) * S 4 V28)
    (by rw [show (4 : PowerSeries ℤ) = 2 * 2 by norm_num]; exact mul_ne_zero two_ne two_ne) Y2 Y4
  apply S_inj 2
  simp only [map_mul, map_sub, map_pow, SX28, S2S2, S2P12, S2P1734]
  rw [r24, r3468]
  linear_combination h

/-- (3.6): `S(−q)S(q²) − qS(q) = χ²(−q)χ²(−Q)`. -/
theorem Y6 : Ng U28 * Ng V28 * (S 2 U28 * S 2 V28) - X * (U28 * V28) = Pinf 1 2 ^ 2 * Pinf 17 34 ^ 2 :=
  alg6 X (chip 1) (Pinf 1 2) (chip 17) (Pinf 17 34) U28 (Ng U28) V28 (Ng V28) (S 2 U28) (S 2 V28) (chip_ne 1)
    (Pne 17 34 (by norm_num) (by norm_num)) ddne Y14 Y14m Y14q P28

/-- (3.6) at `−q`. -/
theorem Y6m : U28 * V28 * (S 2 U28 * S 2 V28) + X * (Ng U28 * Ng V28) = chip 1 ^ 2 * chip 17 ^ 2 := by
  have h := congrArg Ng Y6
  simp only [map_mul, map_sub, map_pow, Ng_Ng, Ng_X, Ng_P12, Ng_P1734, Ng_S_ev 2 (by norm_num)] at h
  linear_combination h

/-- (3.6) at `q²`. -/
theorem Y6q2 : S 2 (Ng U28) * S 2 (Ng V28) * (S 4 U28 * S 4 V28) - X ^ 2 * (S 2 U28 * S 2 V28) =
    (chip 1 * Pinf 1 2 * (chip 17 * Pinf 17 34)) ^ 2 := by
  have h := congrArg (S 2) Y6
  simp only [map_mul, map_sub, map_pow, SX28, S2S2, S2P12, S2P1734] at h
  rw [r24, r3468] at h
  linear_combination h

end Forty
