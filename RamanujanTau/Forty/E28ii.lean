/-
# Entry 3.28(ii)

`U⁴V⁴ − qU²V² = (χ³(−q¹⁷)/χ³(−q)) (1 + q² χ³(−q)/χ³(−q¹⁷))²` with `U = G(q¹⁷)H(q²) − q³G(q²)H(q¹⁷)`,
`V = G(q)G(q³⁴) + q⁷H(q)H(q³⁴)`.

Proof: Yesilyurt, JMAA 388 (2012) §3. The level identities (3.1)–(3.6) are `E28g.lean`; the algebra (3.29)–(3.44)
is `alg28` (`E28d.lean`), run in the fraction field of `ℤ⟦q⟧`. The one non-algebraic step is the choice of the
square root at his (3.39) → (3.40): `(S²(q²) − R)² = 4q⁴` with `R = χ(−q²)V(q)V(−q)U(−q²)V(q⁴)/χ(−Q²)`, and
`R = S²(q²) − 2q²` is the root, because `S²(q²) + 2q² − R ≡ 4q² (mod q³)` is not zero (`hbr28`, computed in
`ℤ⟦q⟧ ⧸ (q³)`).
-/
import RamanujanTau.Forty.E28g

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC PowerSeries
open RankProof (Pinf isUnit_Pinf)

/-! ### The branch: computation modulo `q³` -/

/-- the ideal `(q³)`. -/
noncomputable abbrev I3 : Ideal (PowerSeries ℤ) := Ideal.span {(X : PowerSeries ℤ) ^ 3}

local notation "π3" => Ideal.Quotient.mk I3

lemma π3_eq {f g : PowerSeries ℤ} (h : (X : PowerSeries ℤ) ^ 3 ∣ f - g) : π3 f = π3 g :=
  Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h)

lemma hx3 : (π3 X) ^ 3 = 0 := by
  rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr dvd_rfl)

lemma hxn (n : ℕ) (hn : 3 ≤ n) : (π3 X) ^ n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [_root_.pow_add, hx3, zero_mul]

lemma πPinf (b a : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a) : π3 (Pinf b a) = (1 - π3 X ^ b) * (1 - π3 X ^ (b + a)) := by
  rw [π3_eq (RankProof.X_pow_dvd_Pinf_sub b a hb ha 2)]
  simp [RankProof.Pfin, prod_range_succ]

lemma πone (b a : ℕ) (hb : 3 ≤ b) (ha : 1 ≤ a) : π3 (Pinf b a) = 1 := by
  rw [πPinf b a (by omega) ha, hxn b hb, hxn (b + a) (by omega)]; ring

lemma πS (a : ℕ) [NeZero a] (ha : 3 ≤ a) (f : PowerSeries ℤ) (hf : constantCoeff f = 1) : π3 (S a f) = 1 := by
  rw [← map_one π3]
  apply π3_eq
  have h1 : (X : PowerSeries ℤ) ^ 1 ∣ f - 1 := by
    rw [pow_one, X_dvd_iff]; simp [hf]
  have h2 := RankProof.Ea_dvd a (NeZero.ne a) h1
  have h3 : S a f - 1 = S a (f - 1) := by rw [map_sub, map_one]
  rw [h3]
  exact (pow_dvd_pow X (by omega)).trans h2

lemma ccNgG : constantCoeff (Ng G) = 1 := by rw [cc_Ng, cc_G]
lemma ccNgH : constantCoeff (Ng H) = 1 := by rw [cc_Ng, cc_H]

lemma πG : π3 G = 1 + π3 X + π3 X ^ 2 := by
  have h := congrArg π3 G_mul_uu
  rw [uu, map_mul, map_mul, πPinf 1 5 le_rfl (by norm_num), πone 4 5 (by norm_num) (by norm_num), map_one] at h
  simp only [pow_one, Nat.reduceAdd, mul_one] at h
  linear_combination (1 + π3 X + π3 X ^ 2) * h
    + (-(π3 X) ^ 6 * π3 G + π3 X ^ 3 * π3 G + π3 G) * hx3

lemma πNgG : π3 (Ng G) = 1 - π3 X + π3 X ^ 2 := by
  have h := congrArg π3 NgG_prod
  simp only [map_mul, πPinf 2 20 (by norm_num) (by norm_num), πone 6 10 (by norm_num) (by norm_num),
    πone 4 10 (by norm_num) (by norm_num), πone 18 20 (by norm_num) (by norm_num), πPinf 1 10 le_rfl (by norm_num),
    πone 9 10 (by norm_num) (by norm_num), pow_one, Nat.reduceAdd, mul_one] at h
  linear_combination (1 + π3 X ^ 2) * h
    + (-(π3 X) ^ 23 * π3 (Ng G) + π3 X ^ 19 * π3 (Ng G) + π3 X ^ 11 - π3 X ^ 10 + π3 X ^ 9 - π3 X ^ 8
      + π3 X * π3 (Ng G) - 1) * hx3

lemma πS2G : π3 (S 2 G) = 1 + π3 X ^ 2 := by
  have h := SG_mul 2
  norm_num at h
  have h' := congrArg π3 h
  simp only [map_mul, map_one, πPinf 2 10 (by norm_num) (by norm_num), πone 8 10 (by norm_num) (by norm_num),
    Nat.reduceAdd, mul_one] at h'
  linear_combination (1 + π3 X ^ 2) * h'
    + (-(π3 X) ^ 13 * π3 (S 2 G) + π3 X ^ 9 * π3 (S 2 G) + π3 X * π3 (S 2 G)) * hx3

lemma S2_NgU28 : S 2 (Ng U28) = S 34 (Ng G) * S 4 H + X ^ 6 * S 4 G * S 34 (Ng H) := by
  simp only [Ng_U28, map_add, map_mul, map_pow, S_S 2 17 34 rfl, S_S 2 2 4 rfl, SX28]
  ring

lemma S4_V28 : S 4 V28 = S 4 G * S 136 G + X ^ 28 * S 4 H * S 136 H := by
  simp only [V28, map_add, map_mul, map_pow, S_S 4 34 136 rfl, SX28]
  ring

lemma four_x2_ne : 4 * π3 X ^ 2 ≠ 0 := by
  have e : 4 * π3 X ^ 2 = π3 (4 * X ^ 2) := by simp only [map_mul, map_pow, map_ofNat]
  rw [e]
  intro h
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
  obtain ⟨g, hg⟩ := h
  have h2 : (X : PowerSeries ℤ) ^ 2 * (4 - X * g) = 0 := by linear_combination hg
  have h3 := (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 2 X_ne_zero)
  have h4 := congrArg constantCoeff h3
  rw [map_sub, map_mul, constantCoeff_X, zero_mul, sub_zero, map_ofNat, map_zero] at h4
  norm_num at h4

/-- **The branch** (Yesilyurt (3.39) → (3.40)): `(S²(q²) + 2q²) χ(−Q²) − χ(−q²) V(q)V(−q) U(−q²)V(q⁴) ≠ 0`; it is
`≡ 4q² (mod q³)`. -/
theorem hbr28 : ((S 2 U28 * S 2 V28) ^ 2 + 2 * X ^ 2) * (chip 17 * Pinf 17 34) -
    chip 1 * Pinf 1 2 * (V28 * Ng V28) * (S 2 (Ng U28) * S 4 V28) ≠ 0 := by
  intro h0
  have h := congrArg π3 h0
  have one1 := πS 34 (by norm_num) G cc_G
  have vS2U : π3 (S 2 U28) = 1 := by
    rw [S2_U28, map_sub, map_mul, map_mul, map_mul, map_pow, one1, πS 4 (by norm_num) H cc_H,
      πS 4 (by norm_num) G cc_G, πS 34 (by norm_num) H cc_H]
    linear_combination (-(π3 X) ^ 3) * hx3
  have vS2V : π3 (S 2 V28) = 1 + π3 X ^ 2 := by
    rw [S2_V28, map_add, map_mul, map_mul, map_mul, map_pow, πS2G, πS 68 (by norm_num) G cc_G,
      πS 68 (by norm_num) H cc_H]
    have hS2H := SH_mul 2
    norm_num at hS2H
    have k := congrArg π3 hS2H
    simp only [map_mul, map_one, πone 4 10 (by norm_num) (by norm_num), πone 6 10 (by norm_num) (by norm_num),
      mul_one] at k
    rw [k]
    linear_combination π3 X ^ 11 * hx3
  have vV : π3 V28 = 1 + π3 X + π3 X ^ 2 := by
    rw [V28, map_add, map_mul, map_mul, map_mul, map_pow, πG, one1, πS 34 (by norm_num) H cc_H]
    linear_combination (π3 X ^ 4 * π3 H) * hx3
  have vNgV : π3 (Ng V28) = 1 - π3 X + π3 X ^ 2 := by
    rw [Ng_V28, map_sub, map_mul, map_mul, map_mul, map_pow, πNgG, one1, πS 34 (by norm_num) H cc_H]
    linear_combination (-(π3 X) ^ 4 * π3 (Ng H)) * hx3
  have vW : π3 (S 2 (Ng U28) * S 4 V28) = 1 := by
    rw [S2_NgU28, S4_V28]
    simp only [map_add, map_mul, map_pow, πS 34 (by norm_num) (Ng G) ccNgG, πS 34 (by norm_num) (Ng H) ccNgH,
      πS 4 (by norm_num) G cc_G, πS 4 (by norm_num) H cc_H, πS 136 (by norm_num) G cc_G, πS 136 (by norm_num) H cc_H]
    linear_combination (π3 X ^ 3 + π3 X ^ 25 + π3 X ^ 31) * hx3
  have vc : π3 (chip 1 * Pinf 1 2) = 1 - π3 X ^ 2 := by
    rw [← r24, πPinf 2 4 (by norm_num) (by norm_num)]
    linear_combination (-(π3 X) ^ 3 * (1 - π3 X ^ 2)) * hx3
  have vd : π3 (chip 17 * Pinf 17 34) = 1 := by rw [← r3468, πone 34 68 (by norm_num) (by norm_num)]
  simp only [map_sub, map_mul, map_add, map_pow, map_ofNat, map_zero] at h
  rw [← map_mul π3 (S 2 (Ng U28)), vW, ← map_mul π3 (chip 17), vd, ← map_mul π3 (chip 1), vc, vS2U, vS2V, vV,
    vNgV] at h
  apply four_x2_ne
  linear_combination h - (π3 X ^ 3 + π3 X) * hx3

/-! ### Assembly -/

/-- Yesilyurt (3.8) at `q²`, cleared: `(S⁴(q²) − q²S²(q²)) (cd)³ = (d³ + q⁴c³)²`. -/
theorem Y8q2 : ((S 2 U28 * S 2 V28) ^ 4 - X ^ 2 * (S 2 U28 * S 2 V28) ^ 2) *
    (chip 1 * Pinf 1 2 * (chip 17 * Pinf 17 34)) ^ 3 =
    ((chip 17 * Pinf 17 34) ^ 3 + X ^ 4 * (chip 1 * Pinf 1 2) ^ 3) ^ 2 := by
  let K := FractionRing (PowerSeries ℤ)
  let fr := algebraMap (PowerSeries ℤ) K
  have inj : Function.Injective fr := IsFractionRing.injective (PowerSeries ℤ) K
  have nz : ∀ {f : PowerSeries ℤ}, f ≠ 0 → fr f ≠ 0 := fun h => (map_ne_zero_iff fr inj).mpr h
  have key := alg28 (fr X) (fr (chip 1)) (fr (Pinf 1 2)) (fr (chip 17)) (fr (Pinf 17 34)) (fr (chip 2)) (fr (chip 34))
    (fr U28) (fr (Ng U28)) (fr V28) (fr (Ng V28)) (fr (S 2 U28)) (fr (S 2 V28)) (fr (S 2 (Ng U28)))
    (fr (S 2 (Ng V28))) (fr (S 4 U28)) (fr (S 4 V28))
    (nz X_ne_zero) (nz (chip_ne 1)) (nz (Pne 1 2 le_rfl (by norm_num))) (nz (chip_ne 17))
    (nz (Pne 17 34 (by norm_num) (by norm_num))) (nz (chip_ne 2)) (nz (chip_ne 34))
    (by simpa only [map_ofNat] using nz two_ne)
    (by simpa only [map_mul] using congrArg fr Y14)
    (by simpa only [map_mul] using congrArg fr Y14m)
    (by simpa only [map_mul] using congrArg fr Y14q)
    (by simpa only [map_mul] using congrArg fr Y14m2)
    (by simpa only [map_mul] using congrArg fr Y14q4)
    (by simpa only [map_mul, map_sub, map_pow] using congrArg fr Y1)
    (by
      have h := congrArg Ng Y1
      simp only [map_mul, map_sub, map_pow, Ng_P12, Ng_P1734, Ng_chip1, Ng_chip17, Ng_X] at h
      have h' : chip 1 * Pinf 1 2 * (chip 17 * Pinf 17 34) * chip 17 * Ng U28 =
          Pinf 17 34 * (chip 17 * Pinf 17 34) - X ^ 2 * Pinf 1 2 * (chip 1 * Pinf 1 2) := by
        linear_combination h
      simpa only [map_mul, map_sub, map_pow] using congrArg fr h')
    (by simpa only [map_mul, map_sub, map_ofNat] using congrArg fr Y2)
    (by simpa only [map_mul, map_add, map_ofNat] using congrArg fr Y4)
    (by simpa only [map_mul, map_sub, map_pow, map_ofNat] using congrArg fr Y5)
    (by simpa only [map_mul, map_sub, map_pow] using congrArg fr Y6)
    (by simpa only [map_mul, map_add, map_pow] using congrArg fr Y6m)
    (by simpa only [map_mul, map_sub, map_pow] using congrArg fr Y6q2)
    (by simpa only [map_mul, map_sub, map_add, map_pow, map_ofNat] using nz hbr28)
  apply inj
  simpa only [map_mul, map_sub, map_add, map_pow] using key

/-- **Entry 3.28(ii)**, cleared (Ramanujan; first proved by Yesilyurt, JMAA 2012):
`(U⁴V⁴ − qU²V²) χ³(−q)χ³(−q¹⁷) = (χ³(−q¹⁷) + q²χ³(−q))²`. -/
theorem entry_3_28_ii' : (((S 17 G * S 2 H - X ^ 3 * S 2 G * S 17 H) * (G * S 34 G + X ^ 7 * H * S 34 H)) ^ 4
      - X * ((S 17 G * S 2 H - X ^ 3 * S 2 G * S 17 H) * (G * S 34 G + X ^ 7 * H * S 34 H)) ^ 2) *
      (chim 1 * chim 17) ^ 3 = (chim 17 ^ 3 + X ^ 2 * chim 1 ^ 3) ^ 2 := by
  have h := Y8q2
  rw [← r24, ← r3468] at h
  rw [show S 17 G * S 2 H - X ^ 3 * S 2 G * S 17 H = U28 from rfl,
    show G * S 34 G + X ^ 7 * H * S 34 H = V28 from rfl]
  apply S_inj 2
  simp only [chim, Nat.reduceMul, map_mul, map_sub, map_add, map_pow, SX28, S2P12, S2P1734]
  linear_combination h

/-- **Entry 3.28(ii)** (Ramanujan): with `U = G(q¹⁷)H(q²) − q³G(q²)H(q¹⁷)` and `V = G(q)G(q³⁴) + q⁷H(q)H(q³⁴)`,
`U⁴V⁴ − qU²V² = (χ³(−q¹⁷)/χ³(−q)) (1 + q² χ³(−q)/χ³(−q¹⁷))²`. -/
theorem entry_3_28_ii : ((S 17 G * S 2 H - X ^ 3 * S 2 G * S 17 H) * (G * S 34 G + X ^ 7 * H * S 34 H)) ^ 4
      - X * ((S 17 G * S 2 H - X ^ 3 * S 2 G * S 17 H) * (G * S 34 G + X ^ 7 * H * S 34 H)) ^ 2 =
    chim 17 ^ 3 * Ring.inverse (chim 1 ^ 3) * (1 + X ^ 2 * chim 1 ^ 3 * Ring.inverse (chim 17 ^ 3)) ^ 2 := by
  have h := entry_3_28_ii'
  have u1 : IsUnit (chim 1 ^ 3) := (isUnit_Pinf 1 2 le_rfl (by norm_num)).pow 3
  have u17 : IsUnit (chim 17 ^ 3) := (isUnit_Pinf 17 34 (by norm_num) (by norm_num)).pow 3
  have i1 := Ring.mul_inverse_cancel _ u1
  have i17 := Ring.mul_inverse_cancel _ u17
  apply mul_left_cancel₀ (mul_ne_zero u1.ne_zero u17.ne_zero)
  set A := ((S 17 G * S 2 H - X ^ 3 * S 2 G * S 17 H) * (G * S 34 G + X ^ 7 * H * S 34 H))
  linear_combination h
    - ((chim 17 ^ 3) ^ 2 + 2 * X ^ 2 * chim 1 ^ 3 * chim 17 ^ 3 * (chim 17 ^ 3 * Ring.inverse (chim 17 ^ 3))
      + X ^ 4 * (chim 1 ^ 3) ^ 2 * (chim 17 ^ 3 * Ring.inverse (chim 17 ^ 3)) ^ 2) * i1
    - (2 * X ^ 2 * chim 1 ^ 3 * chim 17 ^ 3 + X ^ 4 * (chim 1 ^ 3) ^ 2 * (chim 17 ^ 3 * Ring.inverse (chim 17 ^ 3) + 1)) * i17

end Forty
