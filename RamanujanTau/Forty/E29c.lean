/-
# Entry 3.29: product identities and the evaluation of the lattice identities

Base product identities (Yesilyurt (3.11), (3.19), (4.4), (4.6); Entry 3.3 at `−q`), then the four evaluations
* `D5p_ι`: `D5p = f(−q²)f(−Q²)A(q²)`,           * `D5m_ι`: `D5m = f(−q²)f(−Q²)A(q)A(−q)`,
* `Yo_ι`: `Yo = q²f(−q⁴)f(−Q⁴)A(q²)`,           * `Ye_ι`: `Ye = f(−q⁴)f(−Q⁴)A(q⁴)B(−q²)`,
with `Q = q²³`, `A(q) = G(q²)G(Q) + q⁵H(q²)H(Q)`, `B(q) = H(q)G(Q²) − q⁹G(q)H(Q²)`.
-/
import RamanujanTau.Forty.E29b
import RamanujanTau.Forty.E21

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC PowerSeries
open RankProof (Pinf isUnit_Pinf)

local notation "φ" => RamanujanTau.Septic.phi
local notation "ψ" => RamanujanTau.Septic.ramF 1 3

/-- `A(q) = G(q²)G(q²³) + q⁵H(q²)H(q²³)`. -/
noncomputable def A29 : PowerSeries ℤ := S 2 G * S 23 G + X ^ 5 * S 2 H * S 23 H
/-- `B(q) = H(q)G(q⁴⁶) − q⁹G(q)H(q⁴⁶)`. -/
noncomputable def B29 : PowerSeries ℤ := S 46 G * H - X ^ 9 * G * S 46 H

lemma J_ne29 (e N : ℕ) (h1 : 1 ≤ e) (h2 : e < N) : J e N ≠ 0 :=
  mul_ne_zero (mul_ne_zero (Pinf_ne e N h1 (by omega)) (Pinf_ne (N - e) N (by omega) (by omega)))
    (Pinf_ne N N (by omega) (by omega))

lemma ι_ne29 {f : PowerSeries ℤ} (h : f ≠ 0) : ι f ≠ 0 := fun h0 => h (ι_inj (h0.trans (map_zero ι).symm))

lemma Ng_S_odd8 (a : ℕ) [NeZero a] (ha : Odd a) (f : PowerSeries ℤ) : Ng (S a f) = S a (Ng f) := by
  ext n
  rw [Ng, coeff_rescale, coeff_S, coeff_S]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne a)), ← Ng, Ng, coeff_rescale, pow_mul]
    obtain ⟨k, rfl⟩ := ha
    rw [_root_.pow_add, pow_mul]; norm_num
  · simp

lemma J10_30 : J 10 30 = Pinf 10 10 := by
  simp only [J, Nat.reduceSub]
  simp (disch := norm_num) only [atom _ _ 30]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
    add_zero, mul_one]

lemma J460_1380 : J 460 1380 = Pinf 460 460 := by
  simp only [J, Nat.reduceSub]
  simp (disch := norm_num) only [atom 460 460 1380]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
    add_zero, mul_one]

lemma J8_10 : J 8 10 = J 2 10 := by simp only [J, Nat.reduceSub]; ring

/-- (4.4): `f(−q²,−q⁸) f(−q¹⁰) = f(−q,−q⁹) f(−q²) G(q)`. -/
lemma R44a : J 2 10 * Pinf 10 10 = J 1 10 * Pinf 2 2 * G := by
  have k : J 2 10 * Pinf 10 10 * (Pinf 1 5 * Pinf 4 5) = J 1 10 * Pinf 2 2 := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 10]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  have hG := G_mul_uu
  simp only [uu] at hG
  linear_combination -(J 2 10 * Pinf 10 10) * hG + G * k

/-- (4.4): `f(−q⁴,−q⁶) f(−q¹⁰) = f(−q³,−q⁷) f(−q²) H(q)`. -/
lemma R44b : J 4 10 * Pinf 10 10 = J 3 10 * Pinf 2 2 * H := by
  have k : J 4 10 * Pinf 10 10 * (Pinf 2 5 * Pinf 3 5) = J 3 10 * Pinf 2 2 := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 10]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  have hH := H_mul_vv
  simp only [vv] at hH
  linear_combination -(J 4 10 * Pinf 10 10) * hH + H * k

/-- (3.11) at `q²`: `f(−q⁴,−q⁶) f(−q²,−q⁸) f(−q¹⁰) f(−q⁴) = f(−q²) f(−q⁸,−q¹²) f(−q⁴,−q¹⁶) f(−q¹⁰,−q¹⁰)`. -/
lemma K1 : J 4 10 * J 2 10 * Pinf 10 10 * Pinf 4 4 = Pinf 2 2 * J 8 20 * J 4 20 * J 10 20 := by
  simp only [J, Nat.reduceSub]
  simp (disch := norm_num) only [atom _ _ 20]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
    add_zero, mul_one]
  ring

/-- (4.6): `f(−q³,−q⁷) = f(−q²) H(−q) G(q⁴)`. -/
lemma R46a : J 3 10 = Pinf 2 2 * Ng H * S 4 G := by
  have hN := NgH_prod
  have hG := SG_mul 4
  norm_num at hG
  have k : J 3 10 * (Pinf 2 10 * Pinf 8 10 * Pinf 14 20 * Pinf 6 20) * (Pinf 4 20 * Pinf 16 20) =
      Pinf 2 2 * (Pinf 7 10 * Pinf 3 10) := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 20]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  have hD : (Pinf 2 10 * Pinf 8 10 * Pinf 14 20 * Pinf 6 20) * (Pinf 4 20 * Pinf 16 20) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨⟨⟨Pinf_ne _ _ (by norm_num) (by norm_num), Pinf_ne _ _ (by norm_num) (by norm_num)⟩,
      Pinf_ne _ _ (by norm_num) (by norm_num)⟩, Pinf_ne _ _ (by norm_num) (by norm_num)⟩,
      Pinf_ne _ _ (by norm_num) (by norm_num), Pinf_ne _ _ (by norm_num) (by norm_num)⟩
  apply mul_right_cancel₀ hD
  linear_combination k - (Pinf 2 2 * S 4 G * (Pinf 4 20 * Pinf 16 20)) * hN
    - (Pinf 2 2 * Pinf 7 10 * Pinf 3 10) * hG

/-- (4.6): `f(−q,−q⁹) = f(−q²) G(−q) H(q⁴)`. -/
lemma R46b : J 1 10 = Pinf 2 2 * Ng G * S 4 H := by
  have hN := NgG_prod
  have hH := SH_mul 4
  norm_num at hH
  have k : J 1 10 * (Pinf 2 20 * Pinf 6 10 * Pinf 4 10 * Pinf 18 20) * (Pinf 8 20 * Pinf 12 20) =
      Pinf 2 2 * (Pinf 1 10 * Pinf 9 10) := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 20]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  have hD : (Pinf 2 20 * Pinf 6 10 * Pinf 4 10 * Pinf 18 20) * (Pinf 8 20 * Pinf 12 20) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨⟨⟨Pinf_ne _ _ (by norm_num) (by norm_num), Pinf_ne _ _ (by norm_num) (by norm_num)⟩,
      Pinf_ne _ _ (by norm_num) (by norm_num)⟩, Pinf_ne _ _ (by norm_num) (by norm_num)⟩,
      Pinf_ne _ _ (by norm_num) (by norm_num), Pinf_ne _ _ (by norm_num) (by norm_num)⟩
  apply mul_right_cancel₀ hD
  linear_combination k - (Pinf 2 2 * S 4 H * (Pinf 8 20 * Pinf 12 20)) * hN
    - (Pinf 2 2 * Pinf 1 10 * Pinf 9 10) * hH

/-- (3.19): `G(q)G(−q) f(−q²) f(−q⁴,−q⁶) = f(q⁴,q⁶)`-numerator. -/
lemma GNgG : G * Ng G * Pinf 2 2 * J 4 10 = J 8 20 * J 10 20 := by
  have hN := NgG_prod
  have hG := G_mul_uu
  simp only [uu] at hG
  have k : (Pinf 1 10 * Pinf 9 10) * Pinf 2 2 * J 4 10 =
      J 8 20 * J 10 20 * (Pinf 2 20 * Pinf 6 10 * Pinf 4 10 * Pinf 18 20) * (Pinf 1 5 * Pinf 4 5) := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 20]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  have hD : (Pinf 2 20 * Pinf 6 10 * Pinf 4 10 * Pinf 18 20) * (Pinf 1 5 * Pinf 4 5) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨⟨⟨Pinf_ne _ _ (by norm_num) (by norm_num), Pinf_ne _ _ (by norm_num) (by norm_num)⟩,
      Pinf_ne _ _ (by norm_num) (by norm_num)⟩, Pinf_ne _ _ (by norm_num) (by norm_num)⟩,
      Pinf_ne _ _ (by norm_num) (by norm_num), Pinf_ne _ _ (by norm_num) (by norm_num)⟩
  apply mul_right_cancel₀ hD
  linear_combination (Pinf 2 2 * J 4 10 * G * (Pinf 1 5 * Pinf 4 5)) * hN
    + (Pinf 2 2 * J 4 10 * Pinf 1 10 * Pinf 9 10) * hG + k

lemma HNgH : H * Ng H * Pinf 2 2 * J 2 10 = J 4 20 * J 10 20 := by
  have hN := NgH_prod
  have hH := H_mul_vv
  simp only [vv] at hH
  have k : (Pinf 7 10 * Pinf 3 10) * Pinf 2 2 * J 2 10 =
      J 4 20 * J 10 20 * (Pinf 2 10 * Pinf 8 10 * Pinf 14 20 * Pinf 6 20) * (Pinf 2 5 * Pinf 3 5) := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 20]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  have hD : (Pinf 2 10 * Pinf 8 10 * Pinf 14 20 * Pinf 6 20) * (Pinf 2 5 * Pinf 3 5) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨⟨⟨Pinf_ne _ _ (by norm_num) (by norm_num), Pinf_ne _ _ (by norm_num) (by norm_num)⟩,
      Pinf_ne _ _ (by norm_num) (by norm_num)⟩, Pinf_ne _ _ (by norm_num) (by norm_num)⟩,
      Pinf_ne _ _ (by norm_num) (by norm_num), Pinf_ne _ _ (by norm_num) (by norm_num)⟩
  apply mul_right_cancel₀ hD
  linear_combination (Pinf 2 2 * J 2 10 * H * (Pinf 2 5 * Pinf 3 5)) * hN
    + (Pinf 2 2 * J 2 10 * Pinf 7 10 * Pinf 3 10) * hH + k

/-- Entry 3.3 at `−q`: `(G(−q)G(q⁴) + qH(−q)H(q⁴)) f(−q²) = φ(−q⁵)`. -/
lemma NgE33 : (Ng G * S 4 G + X * Ng H * S 4 H) * Pinf 2 2 = J 5 10 := by
  have h := entry_3_3
  have hu := Ring.inverse_mul_cancel _ (isUnit_Pinf 2 2 (by norm_num) (by norm_num))
  have h2 : (G * S 4 G - X * H * S 4 H) * Pinf 2 2 = S 5 φ := by
    rw [h, fm, mul_assoc, hu, mul_one]
  have h3 := congrArg Ng h2
  simp only [map_mul, map_sub, Ng_X, Ng_S_ev 4 (by norm_num), Ng_P22, Ng_phi5] at h3
  simp only [J, Nat.reduceSub]
  linear_combination h3

/-- Entry 3.21 cleared: `(G(q)H(−q) − G(−q)H(q)) f(−q²) = 2qψ(q¹⁰)`. -/
lemma E21c : (G * Ng H - Ng G * H) * Pinf 2 2 = 2 * X * S 10 ψ := by
  have h := entry_3_21
  have hu := Ring.inverse_mul_cancel _ (isUnit_Pinf 2 2 (by norm_num) (by norm_num))
  rw [h, fm, mul_assoc, hu, mul_one]

lemma GH2 : J 4 10 * J 2 10 = Pinf 10 10 * Pinf 2 2 := by
  have h := SGH_E 2
  have e1 := SG_E 2
  have e2 := SH_E 2
  norm_num at h e1 e2
  linear_combination -(S 2 H * Pinf 2 2) * e1 - J 4 10 * e2 + Pinf 2 2 * h

end Forty
