/-
# Entries 3.26 and 3.27(i) (Watson; Berndt et al. §29, with the degree-11 modular equation replaced by `M26chi`)

`T(q) = G(q¹¹)H(−q) + q²G(−q)H(q¹¹)`. Watson's argument, step by step:

* (29.7) (`T26_expand`): Lemma 4.1 (`lemma41a`, `lemma41b`) at `±q` and `q¹¹`, multiplied out; the terms with
  exponent `≡ 3 (mod 4)` are Entry 3.4 at `q¹⁶` and at `−q⁴`. This gives
  `χ(−q²)χ(−q⁴)χ(−q²²)χ(−q⁴⁴) T(q) = U(−q⁴) + q²V(−q⁴) − 2q³`, and the same with `+2q³` for `T(−q)`.
* (29.8) (`T26_diff`): `χ(−q²)χ(−q⁴)χ(−q²²)χ(−q⁴⁴) (T(−q) − T(q)) = 4q³`.
* (29.9) (`T26_prod`): `χ²(−q²)χ²(−q²²) (T(q)T(−q) − 1) = 4q²`. This is pure algebra: `T(q)T(−q) − 1` minus the
  product of Entry 3.4 at `q` and `−q` is `q²` times Entry 3.20 at `q` and at `q¹¹`.
* Watson takes a square root using Schröter's degree-11 modular equation. Here the modular equation is `M26chi2`
  (`E26a.lean`, a Type II identity). With `Y = χ(−q²)χ(−q²²)`, `Z = χ(−q⁴)χ(−q⁴⁴)`, `W = χ(q²)χ(q²²)` the three
  relations give `(TYZ + 2q³)² = (WZ)²`. The sign is fixed by the constant term.
* **Entry 3.26** (`entry_3_26`) follows. Then (29.14), `U(−q⁴) + q²V(−q⁴) = χ(q²)χ(q²²)χ(−q⁴)χ(−q⁴⁴)`
  (`entry_29_14`), follows from (29.7). Pulled back along `q ↦ q²` and multiplied by its image under `q ↦ −q`, it
  gives **Entry 3.27(i)** at `−q²` (`entry_3_27_i`).
-/
import RamanujanTau.Forty.E26a
import RamanujanTau.Forty.W41b
import RamanujanTau.Forty.E20

set_option autoImplicit false

namespace Forty
open PowerSeries
open RankProof (Pinf isUnit_Pinf)

private lemma SX (a : ℕ) [NeZero a] : S a X = X ^ a := RankProof.Ea_X a _

private lemma hN8 : Ng (Pinf 8 8) = Pinf 8 8 := Ng_Pinf_even 4 4 (by norm_num) (by norm_num)

/-- `G(−q)f(−q²) = f(−q⁸)(G(q¹⁶) − qH(−q⁴))` (Lemma 4.1 at `−q`). -/
lemma lemma41a_neg : Ng G * Pinf 2 2 = Pinf 8 8 * (S 16 G - X * S 4 (Ng H)) := by
  have h := congrArg Ng lemma41a
  simp only [map_mul, map_add, Ng_P22, hN8, Ng_S_ev 16 (by norm_num), Ng_S_ev 4 (by norm_num), Ng_X] at h
  linear_combination h

/-- `H(−q)f(−q²) = f(−q⁸)(−q³H(q¹⁶) + G(−q⁴))` (Lemma 4.1 at `−q`). -/
lemma lemma41b_neg : Ng H * Pinf 2 2 = Pinf 8 8 * (-(X ^ 3 * S 16 H) + S 4 (Ng G)) := by
  have h := congrArg Ng lemma41b
  simp only [map_mul, map_add, map_pow, Ng_P22, hN8, Ng_S_ev 16 (by norm_num), Ng_S_ev 4 (by norm_num), Ng_X] at h
  linear_combination h

private lemma S11_simp {A B : PowerSeries ℤ} (h : A * Pinf 2 2 = Pinf 8 8 * B) :
    S 11 A * Pinf 22 22 = Pinf 88 88 * S 11 B := by
  have h' := congrArg (S 11) h
  simp only [map_mul, S_P' 11 2 2 (by norm_num) (by norm_num) (rfl : 22 = 11 * 2) (rfl : 22 = 11 * 2),
    S_P' 11 8 8 (by norm_num) (by norm_num) (rfl : 88 = 11 * 8) (rfl : 88 = 11 * 8)] at h'
  exact h'

/-- Lemma 4.1 (4.23) at `q¹¹`. -/
lemma lemma41a_11 : S 11 G * Pinf 22 22 = Pinf 88 88 * (S 176 G + X ^ 11 * S 44 (Ng H)) := by
  have h := S11_simp lemma41a
  simp only [map_add, map_mul, SX, S_S 11 16 176 rfl, S_S 11 4 44 rfl] at h
  exact h

/-- Lemma 4.1 (4.24) at `q¹¹`. -/
lemma lemma41b_11 : S 11 H * Pinf 22 22 = Pinf 88 88 * (X ^ 33 * S 176 H + S 44 (Ng G)) := by
  have h := S11_simp lemma41b
  simp only [map_add, map_mul, map_pow, SX, S_S 11 16 176 rfl, S_S 11 4 44 rfl] at h
  linear_combination h

/-- Entry 3.4 at `q¹⁶`: `G(q¹⁷⁶)H(q¹⁶) − q³²G(q¹⁶)H(q¹⁷⁶) = 1`. -/
lemma e34_16 : S 176 G * S 16 H - X ^ 32 * S 16 G * S 176 H = 1 := by
  have h := congrArg (S 16) entry_3_4
  simp only [map_mul, map_sub, map_pow, map_one, SX, S_S 16 11 176 rfl] at h
  linear_combination h

/-- Entry 3.4 at `−q`. -/
lemma e34_neg : S 11 (Ng G) * Ng H - X ^ 2 * Ng G * S 11 (Ng H) = 1 := by
  have h := congrArg Ng entry_3_4
  simp only [map_mul, map_sub, map_pow, map_one, Ng_X, Ng_S_odd 11 (by decide)] at h
  linear_combination h

/-- Entry 3.4 at `−q⁴`: `G(−q⁴⁴)H(−q⁴) − q⁸G(−q⁴)H(−q⁴⁴) = 1`. -/
lemma e34_m4 : S 44 (Ng G) * S 4 (Ng H) - X ^ 8 * S 4 (Ng G) * S 44 (Ng H) = 1 := by
  have h := congrArg (S 4) e34_neg
  simp only [map_mul, map_sub, map_pow, map_one, SX, S_S 4 11 44 rfl] at h
  linear_combination h

/-- **(29.7)** for `T(q)`: `f(−q²)f(−q²²) T(q) = f(−q⁸)f(−q⁸⁸) (U(−q⁴) + q²V(−q⁴) − 2q³)`. -/
theorem T26_expand : Pinf 2 2 * Pinf 22 22 * (S 11 G * Ng H + X ^ 2 * Ng G * S 11 H) =
    Pinf 8 8 * Pinf 88 88 * ((S 4 (Ng G) * S 176 G - X ^ 36 * S 4 (Ng H) * S 176 H)
      + X ^ 2 * (S 16 G * S 44 (Ng G) - X ^ 12 * S 16 H * S 44 (Ng H)) - 2 * X ^ 3) := by
  have sa := lemma41a_11
  have sb := lemma41b_11
  have na := lemma41a_neg
  have nb := lemma41b_neg
  linear_combination (Ng H * Pinf 2 2) * sa
    + (Pinf 88 88 * (S 176 G + X ^ 11 * S 44 (Ng H))) * nb
    + X ^ 2 * (S 11 H * Pinf 22 22) * na
    + X ^ 2 * (Pinf 8 8 * (S 16 G - X * S 4 (Ng H))) * sb
    - X ^ 3 * Pinf 8 8 * Pinf 88 88 * e34_16 - X ^ 3 * Pinf 8 8 * Pinf 88 88 * e34_m4

/-- **(29.7)** for `T(−q)`: `f(−q²)f(−q²²) T(−q) = f(−q⁸)f(−q⁸⁸) (U(−q⁴) + q²V(−q⁴) + 2q³)`. -/
theorem T26_expand_neg : Pinf 2 2 * Pinf 22 22 * (S 11 (Ng G) * H + X ^ 2 * G * S 11 (Ng H)) =
    Pinf 8 8 * Pinf 88 88 * ((S 4 (Ng G) * S 176 G - X ^ 36 * S 4 (Ng H) * S 176 H)
      + X ^ 2 * (S 16 G * S 44 (Ng G) - X ^ 12 * S 16 H * S 44 (Ng H)) + 2 * X ^ 3) := by
  have h := congrArg Ng T26_expand
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, Ng_P22, hN8, Ng_X, Ng_Ng, Ng_S_odd 11 (by decide),
    Ng_S_ev 4 (by norm_num), Ng_S_ev 16 (by norm_num), Ng_S_ev 44 (by norm_num), Ng_S_ev 176 (by norm_num)] at h
  have h88 : Ng (Pinf 88 88) = Pinf 88 88 := Ng_Pinf_even 44 44 (by norm_num) (by norm_num)
  have h22 : Ng (Pinf 22 22) = Pinf 22 22 := Ng_Pinf_even 11 11 (by norm_num) (by norm_num)
  rw [h88, h22] at h
  linear_combination h

/-- `f(−q²) = χ(−q²)χ(−q⁴)f(−q⁸)`. -/
lemma P2_split : Pinf 2 2 = chim 2 * chim 4 * Pinf 8 8 := by
  have a1 := atom 2 2 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have a2 := atom 2 4 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul] at a1 a2
  norm_num at a1 a2
  simp only [chim, Nat.reduceMul]
  rw [a1, a2]; ring

lemma P22_split : Pinf 22 22 = chim 22 * chim 44 * Pinf 88 88 := by
  have h := congrArg (S 11) P2_split
  simp only [chim, Nat.reduceMul, map_mul,
    S_P' 11 2 2 (by norm_num) (by norm_num) (rfl : 22 = 11 * 2) (rfl : 22 = 11 * 2),
    S_P' 11 2 4 (by norm_num) (by norm_num) (rfl : 22 = 11 * 2) (rfl : 44 = 11 * 4),
    S_P' 11 4 8 (by norm_num) (by norm_num) (rfl : 44 = 11 * 4) (rfl : 88 = 11 * 8),
    S_P' 11 8 8 (by norm_num) (by norm_num) (rfl : 88 = 11 * 8) (rfl : 88 = 11 * 8)] at h ⊢
  exact h

private lemma P88ne : Pinf 8 8 * Pinf 88 88 ≠ 0 :=
  mul_ne_zero (Pinf_ne 8 8 (by norm_num) (by norm_num)) (Pinf_ne 88 88 (by norm_num) (by norm_num))

/-- **(29.8)**: `χ(−q²)χ(−q⁴)χ(−q²²)χ(−q⁴⁴) (T(−q) − T(q)) = 4q³`. -/
theorem T26_diff : chim 2 * chim 4 * chim 22 * chim 44 *
    ((S 11 (Ng G) * H + X ^ 2 * G * S 11 (Ng H)) - (S 11 G * Ng H + X ^ 2 * Ng G * S 11 H)) = 4 * X ^ 3 := by
  apply mul_left_cancel₀ P88ne
  have h1 := T26_expand
  have h2 := T26_expand_neg
  rw [P2_split, P22_split] at h1 h2
  linear_combination h2 - h1

/-- Entry 3.20, cleared: `(G(q)H(−q) + G(−q)H(q)) χ²(−q²) = 2`. -/
lemma e320c : (G * Ng H + Ng G * H) * chim 2 ^ 2 = 2 := by
  have hu : IsUnit (chim 2 ^ 2) := (isUnit_Pinf 2 4 (by norm_num) (by norm_num)).pow 2
  rw [entry_3_20, mul_assoc, Ring.inverse_mul_cancel _ hu, mul_one]

lemma e320c11 : (S 11 G * S 11 (Ng H) + S 11 (Ng G) * S 11 H) * chim 22 ^ 2 = 2 := by
  have h := congrArg (S 11) e320c
  simp only [map_mul, map_add, map_pow, map_ofNat, chim, Nat.reduceMul,
    S_P' 11 2 4 (by norm_num) (by norm_num) (rfl : 22 = 11 * 2) (rfl : 44 = 11 * 4)] at h
  simp only [chim, Nat.reduceMul]
  exact h

/-- **(29.9)**: `χ²(−q²)χ²(−q²²) (T(q)T(−q) − 1) = 4q²`. -/
theorem T26_prod : chim 2 ^ 2 * chim 22 ^ 2 *
    ((S 11 G * Ng H + X ^ 2 * Ng G * S 11 H) * (S 11 (Ng G) * H + X ^ 2 * G * S 11 (Ng H)) - 1) = 4 * X ^ 2 := by
  have e4 := entry_3_4
  have ne4 := e34_neg
  have s := e320c
  have s11 := e320c11
  linear_combination (chim 2 ^ 2 * chim 22 ^ 2 * (S 11 (Ng G) * Ng H - X ^ 2 * Ng G * S 11 (Ng H))) * e4
    + chim 2 ^ 2 * chim 22 ^ 2 * ne4
    + X ^ 2 * ((S 11 G * S 11 (Ng H) + S 11 (Ng G) * S 11 H) * chim 22 ^ 2) * s + 2 * X ^ 2 * s11

lemma cc_T26 : constantCoeff (S 11 G * Ng H + X ^ 2 * Ng G * S 11 H) = 1 := by
  simp [map_add, map_mul, cc_S, cc_Ng, cc_G, cc_H]

lemma cc_chim (a : ℕ) [NeZero a] : constantCoeff (chim a) = 1 := by
  have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr (NeZero.ne a)
  rw [chim]; exact cc_Pinf a (2 * a) ha (by omega)

lemma cc_chip (a : ℕ) [NeZero a] : constantCoeff (chip a) = 1 := by
  rw [chip, cc_S, cc_Ng, cc_Pinf 1 2 le_rfl (by norm_num)]

/-- **Entry 3.26**, denominators cleared:
`T(q) χ(−q²)χ(−q²²)χ(−q⁴)χ(−q⁴⁴) = χ(q²)χ(q²²)χ(−q⁴)χ(−q⁴⁴) − 2q³`. -/
theorem entry_3_26' : (S 11 G * Ng H + X ^ 2 * Ng G * S 11 H) * (chim 2 * chim 22 * (chim 4 * chim 44)) =
    chip 2 * chip 22 * (chim 4 * chim 44) - 2 * X ^ 3 := by
  set T := S 11 G * Ng H + X ^ 2 * Ng G * S 11 H with hT
  set T' := S 11 (Ng G) * H + X ^ 2 * G * S 11 (Ng H) with hT'
  have ha := T26_diff
  have hb := T26_prod
  have hM := M26chi2
  rw [← hT, ← hT'] at ha hb
  have hfac : (T * (chim 2 * chim 22 * (chim 4 * chim 44)) + 2 * X ^ 3 - chip 2 * chip 22 * (chim 4 * chim 44)) *
      (T * (chim 2 * chim 22 * (chim 4 * chim 44)) + 2 * X ^ 3 + chip 2 * chip 22 * (chim 4 * chim 44)) = 0 := by
    linear_combination (-(T * (chim 2 * chim 22 * (chim 4 * chim 44)))) * ha
      + (chim 4 ^ 2 * chim 44 ^ 2) * hb - hM
  rcases mul_eq_zero.mp hfac with h | h
  · linear_combination h
  · exfalso
    have := congrArg constantCoeff h
    rw [hT] at this
    simp only [map_add, map_mul, map_pow, map_ofNat, cc_S, cc_Ng, cc_G, cc_H, cc_chim, cc_chip, constantCoeff_X, map_zero] at this
    norm_num at this

/-- **Entry 3.26** (Watson 1933):
`G(q¹¹)H(−q) + q²G(−q)H(q¹¹) = χ(q²)χ(q²²)/(χ(−q²)χ(−q²²)) − 2q³/(χ(−q²)χ(−q⁴)χ(−q²²)χ(−q⁴⁴))`. -/
theorem entry_3_26 : S 11 G * Ng H + X ^ 2 * Ng G * S 11 H =
    chip 2 * chip 22 * Ring.inverse (chim 2 * chim 22)
      - 2 * X ^ 3 * Ring.inverse (chim 2 * chim 4 * chim 22 * chim 44) := by
  have hu : ∀ a : ℕ, 1 ≤ a → IsUnit (chim a) := fun a ha => isUnit_Pinf a (2 * a) ha (by omega)
  have u1 : IsUnit (chim 2 * chim 22) := (hu 2 (by norm_num)).mul (hu 22 (by norm_num))
  have u2 : IsUnit (chim 2 * chim 4 * chim 22 * chim 44) :=
    (((hu 2 (by norm_num)).mul (hu 4 (by norm_num))).mul (hu 22 (by norm_num))).mul (hu 44 (by norm_num))
  have i1 := Ring.inverse_mul_cancel _ u1
  have i2 := Ring.inverse_mul_cancel _ u2
  have h := entry_3_26'
  apply u2.mul_left_cancel
  linear_combination h - (chip 2 * chip 22 * (chim 4 * chim 44)) * i1 + 2 * X ^ 3 * i2

/-- **(29.14)** (Watson): `U(−q⁴) + q²V(−q⁴) = χ(q²)χ(q²²)χ(−q⁴)χ(−q⁴⁴)`. -/
theorem entry_29_14 : (S 4 (Ng G) * S 176 G - X ^ 36 * S 4 (Ng H) * S 176 H)
      + X ^ 2 * (S 16 G * S 44 (Ng G) - X ^ 12 * S 16 H * S 44 (Ng H)) =
    chip 2 * chip 22 * (chim 4 * chim 44) := by
  apply mul_left_cancel₀ P88ne
  have h1 := T26_expand
  have h2 := entry_3_26'
  rw [P2_split, P22_split] at h1
  linear_combination -h1 + Pinf 8 8 * Pinf 88 88 * h2

private lemma S2_chip1 : S 2 (chip 1) = chip 2 := by rw [chip, chip, S_one]
private lemma S2_chip11 : S 2 (chip 11) = chip 22 := by rw [chip, chip, S_S 2 11 22 rfl]

private lemma Ng_chip11 : Ng (chip 11) = chim 11 := by
  rw [chip, Ng_S_odd 11 (by decide), Ng_Ng, chim,
    S_P' 11 1 2 le_rfl (by norm_num) (rfl : 11 = 11 * 1) (rfl : 22 = 11 * 2)]

private lemma Ng_chim_ev (a : ℕ) (ha : 1 ≤ a) : Ng (chim (2 * a)) = chim (2 * a) := by
  rw [chim, show 2 * (2 * a) = 2 * (2 * a) from rfl]; exact Ng_Pinf_even a (2 * a) ha (by omega)

private lemma S2_chim (a : ℕ) [NeZero a] : S 2 (chim a) = chim (2 * a) := by
  have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr (NeZero.ne a)
  rw [chim, chim, S_Pinf 2 a (2 * a) ha (by omega)]

/-- (29.14) pulled back along `q ↦ q²`: `U(−q²) + qV(−q²) = χ(q)χ(q¹¹)χ(−q²)χ(−q²²)`. -/
theorem star26_plus : (S 2 (Ng G) * S 88 G - X ^ 18 * S 2 (Ng H) * S 88 H)
      + X * (S 8 G * S 22 (Ng G) - X ^ 6 * S 8 H * S 22 (Ng H)) =
    chip 1 * chip 11 * (chim 2 * chim 22) := by
  apply S_inj 2
  have h := entry_29_14
  simp only [map_add, map_sub, map_mul, map_pow, SX, S_S 2 2 4 rfl, S_S 2 88 176 rfl, S_S 2 8 16 rfl,
    S_S 2 22 44 rfl, S2_chip1, S2_chip11, S2_chim]
  linear_combination h

/-- the same at `−q`: `U(−q²) − qV(−q²) = χ(−q)χ(−q¹¹)χ(−q²)χ(−q²²)`. -/
theorem star26_minus : (S 2 (Ng G) * S 88 G - X ^ 18 * S 2 (Ng H) * S 88 H)
      - X * (S 8 G * S 22 (Ng G) - X ^ 6 * S 8 H * S 22 (Ng H)) =
    chim 1 * chim 11 * (chim 2 * chim 22) := by
  have h := congrArg Ng star26_plus
  have c2 : Ng (chim 2) = chim 2 := Ng_chim_ev 1 le_rfl
  have c22 : Ng (chim 22) = chim 22 := Ng_chim_ev 11 (by norm_num)
  simp only [map_add, map_sub, map_mul, map_pow, Ng_X, Ng_chip1, Ng_chip11, c2, c22, Ng_S_ev 2 (by norm_num),
    Ng_S_ev 88 (by norm_num), Ng_S_ev 8 (by norm_num), Ng_S_ev 22 (by norm_num)] at h
  simp only [chim, Nat.reduceMul] at h ⊢
  linear_combination h

/-- **Entry 3.27(i)** (Watson 1933): with `U = G(q)G(q⁴⁴) + q⁹H(q)H(q⁴⁴)`, `V = G(q⁴)G(q¹¹) + q³H(q⁴)H(q¹¹)`,
`U² + qV² = χ³(q)χ³(q¹¹)`. -/
theorem entry_3_27_i :
    (G * S 44 G + X ^ 9 * H * S 44 H) ^ 2 + X * (S 4 G * S 11 G + X ^ 3 * S 4 H * S 11 H) ^ 2 =
      chip 1 ^ 3 * chip 11 ^ 3 := by
  have hp := star26_plus
  have hm := star26_minus
  have hc1 := chip_mul 1
  have hc11 := chip_mul 11
  norm_num at hc1 hc11
  -- `U(−q²)² − q²V(−q²)² = χ³(−q²)χ³(−q²²)`
  have hprod : (S 2 (Ng G) * S 88 G - X ^ 18 * S 2 (Ng H) * S 88 H) ^ 2
      - X ^ 2 * (S 8 G * S 22 (Ng G) - X ^ 6 * S 8 H * S 22 (Ng H)) ^ 2 = chim 2 ^ 3 * chim 22 ^ 3 := by
    simp only [chim, Nat.reduceMul] at hp hm ⊢
    linear_combination ((S 2 (Ng G) * S 88 G - X ^ 18 * S 2 (Ng H) * S 88 H)
        - X * (S 8 G * S 22 (Ng G) - X ^ 6 * S 8 H * S 22 (Ng H))) * hp
      + (chip 1 * chip 11 * (Pinf 2 4 * Pinf 22 44)) * hm
      + (chip 11 * Pinf 11 22 * Pinf 2 4 ^ 2 * Pinf 22 44 ^ 2) * hc1
      + (Pinf 2 4 ^ 3 * Pinf 22 44 ^ 2) * hc11
  have key : S 2 (Ng ((G * S 44 G + X ^ 9 * H * S 44 H) ^ 2 + X * (S 4 G * S 11 G + X ^ 3 * S 4 H * S 11 H) ^ 2
      - chip 1 ^ 3 * chip 11 ^ 3)) = S 2 (Ng 0) := by
    simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_neg, Ng_X, Ng_chip1, Ng_chip11,
      S_P' 2 1 2 le_rfl (by norm_num) (rfl : 2 = 2 * 1) (rfl : 4 = 2 * 2),
      Ng_S_ev 44 (by norm_num), Ng_S_ev 4 (by norm_num), Ng_S_odd 11 (by decide), SX,
      S_S 2 44 88 rfl, S_S 2 4 8 rfl, S_S 2 11 22 rfl, S2_chim]
    simp only [chim, Nat.reduceMul] at hprod ⊢
    linear_combination hprod
  have k2 := S_inj 2 key
  have k3 : (G * S 44 G + X ^ 9 * H * S 44 H) ^ 2 + X * (S 4 G * S 11 G + X ^ 3 * S 4 H * S 11 H) ^ 2
      - chip 1 ^ 3 * chip 11 ^ 3 = 0 := by
    have := congrArg Ng k2
    rwa [Ng_Ng, Ng_Ng] at this
  linear_combination k3

end Forty
