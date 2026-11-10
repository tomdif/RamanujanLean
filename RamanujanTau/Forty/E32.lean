/-
# Entry 3.32: `{G(q³)G(q²²) + q⁵H(q³)H(q²²)} / {G(q¹¹)H(q⁶) − qG(q⁶)H(q¹¹)} = χ(−q³³)/χ(−q)`

Biagioli proved this with modular forms; Yesilyurt (J. Number Theory 129 (2009) §5) gave an elementary proof from his
generalised Rogers identity plus a 3-dissection. The route here avoids the 3-dissection. Write `g(q) = f(−q²,−q³)`, `h(q) = f(−q,−q⁴)` and
`Φ(q) = f(q³,q⁵)f(q⁹⁹,q¹⁶⁵) − q¹⁷f(q,q⁷)f(q³³,q²³¹)`. Then
* `g(q³)g(q²²) + q⁵h(q³)h(q²²) = χ(−q³)χ(−q³³)Φ(q)` (numerator bracket, from `L32T`), and
* `h(q⁶)g(q¹¹) − q g(q⁶)h(q¹¹) = χ(−q)χ(−q¹¹)Φ(q)` (denominator bracket, from `L32U`).
Both come from Type II identities whose det-4 sides collapse, by the quintuple product at `c = −1` (`quintm`), to
the same `Φ`; the det-5 sides collapse by `quint1` and Cao (59) (`R59a`, `R59b`). Everything is done at `q ↦ q²`
(the forms are read at `t = q`) and pulled back by `S_inj 2`. The barred thetas are cleared with `θ_bar`; the only
remaining product identity is Yesilyurt's (5.3), `f(q,q⁷)f(q³,q⁵) = f(−q²,−q⁶)f(−q⁸)/χ(−q)` (`Z32`, at `q²`).
-/
import RamanujanTau.Forty.E32a
import RamanujanTau.Forty.E33

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm16 : 1 ≤ 16 := by norm_num
private lemma hm48 : 1 ≤ 48 := by norm_num
private lemma hm60 : 1 ≤ 60 := by norm_num
private lemma hm180 : 1 ≤ 180 := by norm_num
private lemma hm220 : 1 ≤ 220 := by norm_num
private lemma hm528 : 1 ≤ 528 := by norm_num
private lemma hm660 : 1 ≤ 660 := by norm_num
private lemma hm1584 : 1 ≤ 1584 := by norm_num

/-- `L32U` with its quintuple collapses: with `Φ = θ₁₆(6,−1)θ₅₂₈(198,−1) − t³⁴θ₁₆(2,−1)θ₅₂₈(66,−1)`,
`θ₁₆(2,−1)θ₁₆(6,−1)·θ₆₆₀(220)·A_U = θ₂₂₀(22)θ₂₂₀(66)·θ₄₈(16)θ₁₆(4)·Φ`. -/
theorem M32U : θ hm16 2 (-1) * θ hm16 6 (-1) * θ hm660 220 1 *
      (θ hm60 12 1 * θ hm220 44 1 * θ hm220 66 1 - mono 2 1 * (θ hm60 24 1 * θ hm220 88 1 * θ hm220 22 1)) =
    θ hm220 22 1 * θ hm220 66 1 * θ hm48 16 1 * θ hm16 4 1 *
      (θ hm16 6 (-1) * θ hm528 198 (-1) - mono 34 1 * (θ hm16 2 (-1) * θ hm528 66 (-1))) := by
  have hLat := L32U
  have Qa := quint1 hm220 hm660 rfl 22 286 506 220 44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Qb := quint1 hm220 hm660 rfl 66 418 638 220 132 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Qc := quintm hm16 hm48 rfl 2 22 38 16 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Qd := quintm hm16 hm48 rfl 6 34 50 16 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_refl1 hm660 154 506 (by norm_num)] at Qa
  rw [θ_refl1 hm660 242 418 (by norm_num), θ_refl1 hm660 22 638 (by norm_num), θ_refl1 hm220 88 132 (by norm_num)] at Qb
  rw [θ_reflm hm48 10 38 (by norm_num)] at Qc
  rw [θ_reflm hm48 14 34 (by norm_num), θ_refl1 hm16 4 12 (by norm_num),
    θ_sh hm48 2 1 (by norm_num : (-1 : ℂ) ≠ 0) (-2) 1 (e := 50) (by norm_num) (by norm_num [c2]) (by norm_num)] at Qd
  have m1 : (mono 2 1 : L) * mono 66 1 = mono 68 1 := by rw [mono_mul]; norm_num
  have m2 : (mono 34 1 : L) * (mono 6 1 * mono (-2) 1) = mono 38 1 := by rw [mono_mul, mono_mul]; norm_num
  linear_combination
    (θ hm16 2 (-1) * θ hm16 6 (-1) * θ hm220 22 1 * θ hm220 66 1) * hLat
    - (θ hm16 2 (-1) * θ hm16 6 (-1) * θ hm220 22 1 * θ hm220 66 1 * (θ hm60 24 1 * θ hm660 22 1)) * m1
    - (θ hm16 2 (-1) * θ hm16 6 (-1) * θ hm220 22 1 * θ hm220 66 1 * (θ hm48 2 (-1) * θ hm528 66 (-1))) * m2
    - (θ hm16 2 (-1) * θ hm16 6 (-1) * θ hm60 12 1 * θ hm220 66 1) * Qa
    + (θ hm16 2 (-1) * θ hm16 6 (-1) * mono 2 1 * θ hm60 24 1 * θ hm220 22 1) * Qb
    + (θ hm220 22 1 * θ hm220 66 1 * θ hm16 6 (-1) * θ hm528 198 (-1)) * Qc
    - (θ hm220 22 1 * θ hm220 66 1 * mono 34 1 * θ hm16 2 (-1) * θ hm528 66 (-1)) * Qd

/-- `L32T` with its quintuple collapses:
`θ₅₂₈(66,−1)θ₅₂₈(198,−1)·θ₁₈₀(60)·A_T = θ₆₀(6)θ₆₀(18)·θ₁₅₈₄(528)θ₅₂₈(132)·Φ`. -/
theorem M32T : θ hm528 66 (-1) * θ hm528 198 (-1) * θ hm180 60 1 *
      (θ hm220 88 1 * θ hm60 12 1 * θ hm60 18 1 + mono 10 1 * (θ hm220 44 1 * θ hm60 24 1 * θ hm60 6 1)) =
    θ hm60 6 1 * θ hm60 18 1 * θ hm1584 528 1 * θ hm528 132 1 *
      (θ hm16 6 (-1) * θ hm528 198 (-1) - mono 34 1 * (θ hm16 2 (-1) * θ hm528 66 (-1))) := by
  have hT := L32T
  have Qe := quint1 hm60 hm180 rfl 6 78 138 60 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Qf := quint1 hm60 hm180 rfl 18 114 174 60 36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Qg := quintm hm528 hm1584 rfl 66 726 1254 528 132 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have Qh := quintm hm528 hm1584 rfl 198 1122 1650 528 396 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [θ_refl1 hm180 42 138 (by norm_num)] at Qe
  rw [θ_refl1 hm180 66 114 (by norm_num), θ_refl1 hm180 6 174 (by norm_num), θ_refl1 hm60 24 36 (by norm_num)] at Qf
  rw [θ_reflm hm1584 330 1254 (by norm_num)] at Qg
  rw [θ_reflm hm1584 462 1122 (by norm_num), θ_refl1 hm528 132 396 (by norm_num),
    θ_sh hm1584 66 1 (by norm_num : (-1 : ℂ) ≠ 0) (-66) 1 (e := 1650) (by norm_num) (by norm_num [c2]) (by norm_num)] at Qh
  have m3 : (mono 10 1 : L) * mono 18 1 = mono 28 1 := by rw [mono_mul]; norm_num
  have m4 : (mono 34 1 : L) * (mono 198 1 * mono (-66) 1) = mono 166 1 := by rw [mono_mul, mono_mul]; norm_num
  linear_combination
    (θ hm60 6 1 * θ hm60 18 1 * θ hm528 66 (-1) * θ hm528 198 (-1)) * hT
    - (θ hm60 6 1 * θ hm60 18 1 * θ hm528 66 (-1) * θ hm528 198 (-1) * (θ hm16 2 (-1) * θ hm1584 66 (-1))) * m4
    + (θ hm60 6 1 * θ hm60 18 1 * θ hm528 66 (-1) * θ hm528 198 (-1) * (θ hm180 6 1 * θ hm220 44 1)) * m3
    - (θ hm528 66 (-1) * θ hm528 198 (-1) * θ hm220 88 1 * θ hm60 18 1) * Qe
    - (θ hm528 66 (-1) * θ hm528 198 (-1) * mono 10 1 * θ hm220 44 1 * θ hm60 6 1) * Qf
    + (θ hm60 6 1 * θ hm60 18 1 * θ hm16 6 (-1) * θ hm528 198 (-1)) * Qg
    - (θ hm60 6 1 * θ hm60 18 1 * mono 34 1 * θ hm16 2 (-1) * θ hm528 66 (-1)) * Qh


/-- `Φ` in product form, after multiplying by `J_{2,16}J_{6,16}J_{198,528}J_{66,528}` (`θ_bar`). -/
noncomputable def PhiJ : PowerSeries ℤ :=
  J 12 32 * J 16 32 * J 2 16 * (J 396 1056 * J 528 1056) * J 66 528
    - PowerSeries.X ^ 34 * (J 4 32 * J 16 32 * J 6 16 * (J 132 1056 * J 528 1056) * J 198 528)

/-- the product form of `M32U`. -/
theorem P32U : J 4 32 * J 16 32 * (J 12 32 * J 16 32) * J 198 528 * J 66 528 * J 220 660 *
      (J 12 60 * J 44 220 * J 66 220 - PowerSeries.X ^ 2 * (J 24 60 * J 88 220 * J 22 220)) =
    J 22 220 * J 66 220 * J 16 48 * J 4 16 * PhiJ := by
  apply ι_inj
  have h := congrArg (· * ι (J 2 16 * J 6 16 * J 198 528 * J 66 528)) M32U
  simp only at h
  have hb1 := θ_bar hm16 2 (by norm_num) (by norm_num)
  have hb2 := θ_bar hm16 6 (by norm_num) (by norm_num)
  have hb3 := θ_bar hm528 198 (by norm_num) (by norm_num)
  have hb4 := θ_bar hm528 66 (by norm_num) (by norm_num)
  norm_num at hb1 hb2 hb3 hb4
  rw [θu' hm660 220 (e' := 220) (by norm_num) (by norm_num) (by norm_num),
    θu' hm60 12 (e' := 12) (by norm_num) (by norm_num) (by norm_num),
    θu' hm60 24 (e' := 24) (by norm_num) (by norm_num) (by norm_num),
    θu' hm220 44 (e' := 44) (by norm_num) (by norm_num) (by norm_num),
    θu' hm220 66 (e' := 66) (by norm_num) (by norm_num) (by norm_num),
    θu' hm220 88 (e' := 88) (by norm_num) (by norm_num) (by norm_num),
    θu' hm220 22 (e' := 22) (by norm_num) (by norm_num) (by norm_num),
    θu' hm48 16 (e' := 16) (by norm_num) (by norm_num) (by norm_num),
    θu' hm16 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num)] at h
  unfold PhiJ
  simp only [map_mul, map_sub, ι_Xpow] at hb1 hb2 hb3 hb4 h ⊢
  push_cast at h ⊢
  linear_combination h
    - (hb1 * (θ hm16 6 (-1) * ι (J 6 16)) + (ι (J 4 32) * ι (J 16 32)) * hb2) *
      (ι (J 198 528) * ι (J 66 528) * ι (J 220 660) *
        (ι (J 12 60) * ι (J 44 220) * ι (J 66 220) - mono 2 1 * (ι (J 24 60) * ι (J 88 220) * ι (J 22 220))))
    + (ι (J 22 220) * ι (J 66 220) * ι (J 16 48) * ι (J 4 16)) *
      ((hb2 * (θ hm528 198 (-1) * ι (J 198 528)) + (ι (J 12 32) * ι (J 16 32)) * hb3) * ι (J 2 16) * ι (J 66 528)
        - mono 34 1 * (hb1 * (θ hm528 66 (-1) * ι (J 66 528)) + (ι (J 4 32) * ι (J 16 32)) * hb4) *
          ι (J 6 16) * ι (J 198 528))

/-- the product form of `M32T`. -/
theorem P32T : J 132 1056 * J 528 1056 * (J 396 1056 * J 528 1056) * J 2 16 * J 6 16 * J 60 180 *
      (J 88 220 * J 12 60 * J 18 60 + PowerSeries.X ^ 10 * (J 44 220 * J 24 60 * J 6 60)) =
    J 6 60 * J 18 60 * J 528 1584 * J 132 528 * PhiJ := by
  apply ι_inj
  have h := congrArg (· * ι (J 66 528 * J 198 528 * J 2 16 * J 6 16)) M32T
  simp only at h
  have hb1 := θ_bar hm16 2 (by norm_num) (by norm_num)
  have hb2 := θ_bar hm16 6 (by norm_num) (by norm_num)
  have hb3 := θ_bar hm528 198 (by norm_num) (by norm_num)
  have hb4 := θ_bar hm528 66 (by norm_num) (by norm_num)
  norm_num at hb1 hb2 hb3 hb4
  rw [θu' hm180 60 (e' := 60) (by norm_num) (by norm_num) (by norm_num),
    θu' hm60 12 (e' := 12) (by norm_num) (by norm_num) (by norm_num),
    θu' hm60 18 (e' := 18) (by norm_num) (by norm_num) (by norm_num),
    θu' hm60 24 (e' := 24) (by norm_num) (by norm_num) (by norm_num),
    θu' hm60 6 (e' := 6) (by norm_num) (by norm_num) (by norm_num),
    θu' hm220 44 (e' := 44) (by norm_num) (by norm_num) (by norm_num),
    θu' hm220 88 (e' := 88) (by norm_num) (by norm_num) (by norm_num),
    θu' hm1584 528 (e' := 528) (by norm_num) (by norm_num) (by norm_num),
    θu' hm528 132 (e' := 132) (by norm_num) (by norm_num) (by norm_num)] at h
  unfold PhiJ
  simp only [map_mul, map_sub, map_add, ι_Xpow] at hb1 hb2 hb3 hb4 h ⊢
  push_cast at h ⊢
  linear_combination h
    - (hb4 * (θ hm528 198 (-1) * ι (J 198 528)) + (ι (J 132 1056) * ι (J 528 1056)) * hb3) *
      (ι (J 2 16) * ι (J 6 16) * ι (J 60 180) *
        (ι (J 88 220) * ι (J 12 60) * ι (J 18 60) + mono 10 1 * (ι (J 44 220) * ι (J 24 60) * ι (J 6 60))))
    + (ι (J 6 60) * ι (J 18 60) * ι (J 528 1584) * ι (J 132 528)) *
      ((hb2 * (θ hm528 198 (-1) * ι (J 198 528)) + (ι (J 12 32) * ι (J 16 32)) * hb3) * ι (J 2 16) * ι (J 66 528)
        - mono 34 1 * (hb1 * (θ hm528 66 (-1) * ι (J 66 528)) + (ι (J 4 32) * ι (J 16 32)) * hb4) *
          ι (J 6 16) * ι (J 198 528))

/-- (5.3) of Yesilyurt at `q²`: `f(q²,q¹⁴)f(q⁶,q¹⁰)·χ(−q²) = f(−q⁴,−q¹²)f(−q¹⁶)` after clearing the barred
thetas (`J_{2e,2N}J_{N,2N} = f(q^e,q^{N−e})f(−q^e,−q^{N−e})`). -/
lemma Z32 : J 4 32 * J 16 32 * (J 12 32 * J 16 32) * Pinf 2 4 = J 2 16 * J 6 16 * Pinf 16 16 * J 4 16 := by
  simp only [J, Nat.reduceSub]
  simp (disch := norm_num) only [atom _ _ 32]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
    add_zero, mul_one]
  ring

lemma Z32' : J 132 1056 * J 528 1056 * (J 396 1056 * J 528 1056) * Pinf 66 132 =
    J 66 528 * J 198 528 * Pinf 528 528 * J 132 528 := by
  have h := congrArg (S 33) Z32
  simp only [map_mul, S_J' 33 4 32 (by norm_num) (by norm_num) (rfl : 132 = 33 * 4) (rfl : 1056 = 33 * 32),
    S_J' 33 16 32 (by norm_num) (by norm_num) (rfl : 528 = 33 * 16) (rfl : 1056 = 33 * 32),
    S_J' 33 12 32 (by norm_num) (by norm_num) (rfl : 396 = 33 * 12) (rfl : 1056 = 33 * 32),
    S_J' 33 2 16 (by norm_num) (by norm_num) (rfl : 66 = 33 * 2) (rfl : 528 = 33 * 16),
    S_J' 33 6 16 (by norm_num) (by norm_num) (rfl : 198 = 33 * 6) (rfl : 528 = 33 * 16),
    S_J' 33 4 16 (by norm_num) (by norm_num) (rfl : 132 = 33 * 4) (rfl : 528 = 33 * 16),
    S_P' 33 2 4 (by norm_num) (by norm_num) (rfl : 66 = 33 * 2) (rfl : 132 = 33 * 4),
    S_P' 33 16 16 (by norm_num) (by norm_num) (rfl : 528 = 33 * 16) (rfl : 528 = 33 * 16)] at h
  exact h

lemma j32a : J 220 660 = Pinf 220 220 := by
  simp only [J, Nat.reduceSub]
  simp (disch := norm_num) only [atom _ _ 660]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv]

lemma j32b : J 16 48 = Pinf 16 16 := by
  simp only [J, Nat.reduceSub]
  simp (disch := norm_num) only [atom _ _ 48]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv]

lemma j32c : J 60 180 = Pinf 60 60 := by
  simp only [J, Nat.reduceSub]
  simp (disch := norm_num) only [atom _ _ 180]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv]

lemma j32d : J 528 1584 = Pinf 528 528 := by
  simp only [J, Nat.reduceSub]
  simp (disch := norm_num) only [atom _ _ 1584]
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv]

private lemma Jn (e N : ℕ) (h1 : 1 ≤ e) (h2 : e < N) : J e N ≠ 0 := J_ne e N h1 h2

/-- **Entry 3.32 at `q²`**: `{G(q⁶)G(q⁴⁴) + q¹⁰H(q⁶)H(q⁴⁴)} χ(−q²) = {G(q²²)H(q¹²) − q²G(q¹²)H(q²²)} χ(−q⁶⁶)`. -/
theorem E32sq : (S 6 G * S 44 G + PowerSeries.X ^ 10 * S 6 H * S 44 H) * Pinf 2 4 =
    (S 22 G * S 12 H - PowerSeries.X ^ 2 * S 12 G * S 22 H) * Pinf 66 132 := by
  -- the two brackets as theta products
  have e1 := SG_E 22
  have e2 := SH_E 22
  have e3 := SG_E 12
  have e4 := SH_E 12
  have e5 := SG_E 6
  have e6 := SH_E 6
  have e7 := SG_E 44
  have e8 := SH_E 44
  norm_num at e1 e2 e3 e4 e5 e6 e7 e8
  have hL : (S 22 G * S 12 H - PowerSeries.X ^ 2 * S 12 G * S 22 H) * (Pinf 12 12 * Pinf 22 22) =
      J 44 110 * J 12 60 - PowerSeries.X ^ 2 * (J 24 60 * J 22 110) := by
    linear_combination (S 12 H * Pinf 12 12) * e1 + J 44 110 * e4
      - PowerSeries.X ^ 2 * (S 22 H * Pinf 22 22) * e3 - PowerSeries.X ^ 2 * J 24 60 * e2
  have hL' : (S 6 G * S 44 G + PowerSeries.X ^ 10 * S 6 H * S 44 H) * (Pinf 6 6 * Pinf 44 44) =
      J 12 30 * J 88 220 + PowerSeries.X ^ 10 * (J 6 30 * J 44 220) := by
    linear_combination (S 44 G * Pinf 44 44) * e5 + J 12 30 * e7
      + PowerSeries.X ^ 10 * (S 44 H * Pinf 44 44) * e6 + PowerSeries.X ^ 10 * J 6 30 * e8
  -- Cao (59) at `q²²` and `q⁶`
  have r1 := congrArg (S 22) R59a
  have r2 := congrArg (S 22) R59b
  have r3 := congrArg (S 6) R59a
  have r4 := congrArg (S 6) R59b
  simp only [map_mul, S_J' 22 4 10 (by norm_num) (by norm_num) (rfl : 88 = 22 * 4) (rfl : 220 = 22 * 10),
    S_J' 22 3 10 (by norm_num) (by norm_num) (rfl : 66 = 22 * 3) (rfl : 220 = 22 * 10),
    S_J' 22 1 5 le_rfl (by norm_num) (rfl : 22 = 22 * 1) (rfl : 110 = 22 * 5),
    S_J' 22 2 10 (by norm_num) (by norm_num) (rfl : 44 = 22 * 2) (rfl : 220 = 22 * 10),
    S_J' 22 1 10 le_rfl (by norm_num) (rfl : 22 = 22 * 1) (rfl : 220 = 22 * 10),
    S_J' 22 2 5 (by norm_num) (by norm_num) (rfl : 44 = 22 * 2) (rfl : 110 = 22 * 5),
    S_P' 22 1 2 le_rfl (by norm_num) (rfl : 22 = 22 * 1) (rfl : 44 = 22 * 2),
    S_P' 22 10 10 (by norm_num) (by norm_num) (rfl : 220 = 22 * 10) (rfl : 220 = 22 * 10)] at r1 r2
  simp only [map_mul, S_J' 6 4 10 (by norm_num) (by norm_num) (rfl : 24 = 6 * 4) (rfl : 60 = 6 * 10),
    S_J' 6 3 10 (by norm_num) (by norm_num) (rfl : 18 = 6 * 3) (rfl : 60 = 6 * 10),
    S_J' 6 1 5 le_rfl (by norm_num) (rfl : 6 = 6 * 1) (rfl : 30 = 6 * 5),
    S_J' 6 2 10 (by norm_num) (by norm_num) (rfl : 12 = 6 * 2) (rfl : 60 = 6 * 10),
    S_J' 6 1 10 le_rfl (by norm_num) (rfl : 6 = 6 * 1) (rfl : 60 = 6 * 10),
    S_J' 6 2 5 (by norm_num) (by norm_num) (rfl : 12 = 6 * 2) (rfl : 30 = 6 * 5),
    S_P' 6 1 2 le_rfl (by norm_num) (rfl : 6 = 6 * 1) (rfl : 12 = 6 * 2),
    S_P' 6 10 10 (by norm_num) (by norm_num) (rfl : 60 = 6 * 10) (rfl : 60 = 6 * 10)] at r3 r4
  set Ub := S 22 G * S 12 H - PowerSeries.X ^ 2 * S 12 G * S 22 H with hUb
  set Tb := S 6 G * S 44 G + PowerSeries.X ^ 10 * S 6 H * S 44 H with hTb
  have hU : Ub * Pinf 12 12 * Pinf 22 22 * J 22 220 * J 66 220 = Pinf 22 44 * Pinf 220 220 *
      (J 12 60 * J 44 220 * J 66 220 - PowerSeries.X ^ 2 * (J 24 60 * J 88 220 * J 22 220)) := by
    linear_combination (J 22 220 * J 66 220) * hL - (J 12 60 * J 66 220) * r2
      + PowerSeries.X ^ 2 * J 24 60 * J 22 220 * r1
  have hT : Tb * Pinf 6 6 * Pinf 44 44 * J 6 60 * J 18 60 = Pinf 6 12 * Pinf 60 60 *
      (J 88 220 * J 12 60 * J 18 60 + PowerSeries.X ^ 10 * (J 44 220 * J 24 60 * J 6 60)) := by
    linear_combination (J 6 60 * J 18 60) * hL' - (J 88 220 * J 18 60) * r4
      - PowerSeries.X ^ 10 * (J 44 220 * J 6 60) * r3
  have PU := P32U
  have PT := P32T
  rw [j32a, j32b] at PU
  rw [j32c, j32d] at PT
  set AU := J 12 60 * J 44 220 * J 66 220 - PowerSeries.X ^ 2 * (J 24 60 * J 88 220 * J 22 220) with hAU
  set AT := J 88 220 * J 12 60 * J 18 60 + PowerSeries.X ^ 10 * (J 44 220 * J 24 60 * J 6 60) with hAT
  set K2 := J 4 32 * J 16 32
  set K6 := J 12 32 * J 16 32
  set K66 := J 132 1056 * J 528 1056
  set K198 := J 396 1056 * J 528 1056
  have Z := Z32
  have Z' := Z32'
  have X1 : K2 * K6 * J 198 528 * J 66 528 * Pinf 220 220 * AU * (J 6 60 * J 18 60 * Pinf 528 528 * J 132 528) =
      K66 * K198 * J 2 16 * J 6 16 * Pinf 60 60 * AT * (J 22 220 * J 66 220 * Pinf 16 16 * J 4 16) := by
    linear_combination (J 6 60 * J 18 60 * Pinf 528 528 * J 132 528) * PU
      - (J 22 220 * J 66 220 * Pinf 16 16 * J 4 16) * PT
  set R1 := J 198 528 * J 66 528 * Pinf 528 528 * J 132 528 * Pinf 12 12 * Pinf 22 22 * Pinf 6 12
  set R2 := J 2 16 * J 6 16 * Pinf 16 16 * J 4 16 * Pinf 6 6 * Pinf 44 44 * Pinf 22 44
  have X2 : (J 22 220 * J 66 220 * J 6 60 * J 18 60) * (Ub * (K2 * K6) * R1) =
      (J 22 220 * J 66 220 * J 6 60 * J 18 60) * (Tb * (K66 * K198) * R2) := by
    linear_combination (K2 * K6 * J 198 528 * J 66 528 * Pinf 528 528 * J 132 528 * Pinf 6 12 * J 6 60 * J 18 60) * hU
      - (K66 * K198 * J 2 16 * J 6 16 * Pinf 16 16 * J 4 16 * Pinf 22 44 * J 22 220 * J 66 220) * hT
      + (Pinf 22 44 * Pinf 6 12) * X1
  have X3 := mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero (Jn 22 220 (by norm_num) (by norm_num))
    (Jn 66 220 (by norm_num) (by norm_num))) (Jn 6 60 (by norm_num) (by norm_num))) (Jn 18 60 (by norm_num) (by norm_num))) X2
  set C := J 2 16 * J 6 16 * Pinf 16 16 * J 4 16 * (J 66 528 * J 198 528 * Pinf 528 528 * J 132 528)
  have X4 : C * (Ub * Pinf 66 132 * (Pinf 12 12 * Pinf 22 22 * Pinf 6 12)) =
      C * (Tb * Pinf 2 4 * (Pinf 6 6 * Pinf 44 44 * Pinf 22 44)) := by
    linear_combination (Pinf 2 4 * Pinf 66 132) * X3 - (Ub * Pinf 66 132 * R1) * Z + (Tb * Pinf 2 4 * R2) * Z'
  have hC : C ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (Jn 2 16 (by norm_num) (by norm_num))
      (Jn 6 16 (by norm_num) (by norm_num))) (Pinf_ne 16 16 (by norm_num) (by norm_num))) (Jn 4 16 (by norm_num) (by norm_num)))
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (Jn 66 528 (by norm_num) (by norm_num))
      (Jn 198 528 (by norm_num) (by norm_num))) (Pinf_ne 528 528 (by norm_num) (by norm_num))) (Jn 132 528 (by norm_num) (by norm_num)))
  have X5 := mul_left_cancel₀ hC X4
  have s6 := congrArg (S 6) E1_split
  have s22 := congrArg (S 22) E1_split
  rw [map_mul, S_P' 6 1 1 le_rfl le_rfl (rfl : 6 = 6 * 1) (rfl : 6 = 6 * 1),
    S_P' 6 1 2 le_rfl (by norm_num) (rfl : 6 = 6 * 1) (rfl : 12 = 6 * 2),
    S_P' 6 2 2 (by norm_num) (by norm_num) (rfl : 12 = 6 * 2) (rfl : 12 = 6 * 2)] at s6
  rw [map_mul, S_P' 22 1 1 le_rfl le_rfl (rfl : 22 = 22 * 1) (rfl : 22 = 22 * 1),
    S_P' 22 1 2 le_rfl (by norm_num) (rfl : 22 = 22 * 1) (rfl : 44 = 22 * 2),
    S_P' 22 2 2 (by norm_num) (by norm_num) (rfl : 44 = 22 * 2) (rfl : 44 = 22 * 2)] at s22
  have hF : Pinf 12 12 * Pinf 44 44 * Pinf 22 44 * Pinf 6 12 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (Pinf_ne 12 12 (by norm_num) (by norm_num)) (Pinf_ne 44 44 (by norm_num) (by norm_num)))
      (Pinf_ne 22 44 (by norm_num) (by norm_num))) (Pinf_ne 6 12 (by norm_num) (by norm_num))
  apply mul_left_cancel₀ hF
  linear_combination -X5 + (Ub * Pinf 66 132 * Pinf 12 12 * Pinf 6 12) * s22
    - (Tb * Pinf 2 4 * Pinf 44 44 * Pinf 22 44) * s6

/-- **Entry 3.32** (Biagioli; elementary proof after Yesilyurt 2009, without the 3-dissection):
`G(q³)G(q²²) + q⁵H(q³)H(q²²) = {G(q¹¹)H(q⁶) − qG(q⁶)H(q¹¹)} χ(−q³³)/χ(−q)`. -/
theorem entry_3_32 : S 3 G * S 22 G + PowerSeries.X ^ 5 * S 3 H * S 22 H =
    (S 11 G * S 6 H - PowerSeries.X * S 6 G * S 11 H) * chim 33 * Ring.inverse (chim 1) := by
  apply eq_mul_inv_of (isUnit_Pinf 1 2 le_rfl (by norm_num))
  simp only [chim, Nat.reduceMul]
  apply S_inj 2
  have h := E32sq
  simp only [map_mul, map_add, map_sub, map_pow, S_comp 2 3 6 (by norm_num), S_comp 2 22 44 (by norm_num),
    S_comp 2 11 22 (by norm_num), S_comp 2 6 12 (by norm_num),
    S_P' 2 1 2 le_rfl (by norm_num) (rfl : 2 = 2 * 1) (rfl : 4 = 2 * 2),
    S_P' 2 33 66 (by norm_num) (by norm_num) (rfl : 66 = 2 * 33) (rfl : 132 = 2 * 66),
    show (S 2) PowerSeries.X = PowerSeries.X ^ 2 from RankProof.Ea_X 2 _]
  linear_combination h

end Forty
