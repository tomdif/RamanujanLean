/-
# `φ(q)` as three Appell–Lerch numerators (the first step of HM L5)

With `x = q = t^N` and the Lambert numerators `A_b = Σ_n (−1)^n q^{15C(n,2) + bn}/(1 − q^{15n+3})`
(`A(q^{18−b}, q^b; q^{15})`, `b = 10, 15, 20`):

  `(1 + φ(q)) (q⁵;q⁵)_∞ = A₁₀ + q A₁₅ + q² A₂₀`   (`L5_lam`).

From `rank_AL_m` (`a = 1`, `b = 5`) the left side is `(1 − q)⁻¹ Σ_{r≥0} q^{5r²} α_r`; each `α_r` splits by partial
fractions into the `n = ±r` terms of `Σ_{n∈ℤ} (−1)^n q^{5n(3n+1)/2}/(1 − q^{5n+1})`, and
`1/(1 − y) = (1 + y + y²)/(1 − y³)` with `y = q^{5n+1}` turns that bilateral series into the three Lambert series.
-/
import RamanujanTau.MTC.RankALm
import RamanujanTau.MTC.Hecke373

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset RankProof

/-! ## Generic facts -/

lemma sum_Icc_symC (f : ℤ → ℂ) (n : ℕ) :
    ∑ j ∈ Finset.Icc (-(n : ℤ)) n, f j = f 0 + ∑ i ∈ Finset.range n, (f ((i : ℤ) + 1) + f (-((i : ℤ) + 1))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 by push_cast; ring,
      show Finset.Icc (-((n : ℤ) + 1)) ((n : ℤ) + 1) =
        insert (-((n : ℤ) + 1)) (insert ((n : ℤ) + 1) (Finset.Icc (-(n : ℤ)) n)) by
        ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega,
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih, Finset.sum_range_succ]
    ring

lemma natAbs_bound {n : ℤ} {B : ℕ} (h : n.natAbs ≤ B) : -(B : ℤ) ≤ n ∧ n ≤ B := by
  have h1 : |n| ≤ B := by rw [Int.abs_eq_natAbs]; exact_mod_cast h
  exact abs_le.mp h1

/-- folding a `ℤ`-indexed family onto `ℕ` by pairing `n` with `−n`. -/
lemma hs_int_pair (F : SummableFamily ℤ ℂ ℤ) (G : SummableFamily ℤ ℂ ℕ)
    (hG : ∀ r : ℕ, G r = if r = 0 then F 0 else F r + F (-(r : ℤ))) : hs F = hs G := by
  ext m
  rw [hs, hs, SummableFamily.coeff_hsum, SummableFamily.coeff_hsum]
  obtain ⟨B, hB⟩ := ((F.finite_co_support m).image Int.natAbs).bddAbove
  have hB' : ∀ n : ℤ, (F n).coeff m ≠ 0 → n.natAbs ≤ B := fun n hn =>
    hB ⟨n, Function.mem_support.mpr hn, rfl⟩
  have hz : ∀ n : ℤ, B < n.natAbs → (F n).coeff m = 0 := fun n hn => by
    by_contra h; have := hB' n h; omega
  rw [finsum_eq_sum_of_support_subset (s := Finset.Icc (-(B : ℤ)) B) (f := fun n => (F n).coeff m)
      (fun n hn => by
        have := natAbs_bound (hB' n (Function.mem_support.mp hn))
        simp only [Finset.coe_Icc, Set.mem_Icc]; omega),
    finsum_eq_sum_of_support_subset (s := Finset.range (B + 1)) (f := fun r => (G r).coeff m)
      (fun r hr => by
        rw [Function.mem_support, hG] at hr
        simp only [Finset.coe_range, Set.mem_Iio]
        by_contra hlt
        apply hr
        rw [if_neg (by omega), HahnSeries.coeff_add, hz _ (by simp; omega), hz _ (by simp; omega), add_zero])]
  rw [sum_Icc_symC, Finset.sum_range_succ', hG 0, if_pos rfl, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hG, if_neg (by omega), HahnSeries.coeff_add]
  push_cast; rfl

/-! ## `ιN` of a coefficientwise-defined series -/

section Transfer
variable {N : ℕ} (hN : 1 ≤ N)

/-- the family `r ↦ ιN (g r)`, for `g r = O(X^r)`. -/
noncomputable def trF (g : ℕ → PowerSeries ℤ) (hg : ∀ r k, k < r → PowerSeries.coeff k (g r) = 0) :
    SummableFamily ℤ ℂ ℕ :=
  ofSupp (fun r => ιN hN (g r)) 0 (fun r m hm => ιN_coeff_neg hN _ hm)
    (fun m => (Set.finite_Iic m.toNat).subset fun r hr => by
      simp only [Set.mem_setOf_eq] at hr
      simp only [Set.mem_Iic]
      rcases lt_or_ge m 0 with h | h
      · exact absurd (ιN_coeff_neg hN _ h) hr
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k := ⟨m.toNat, by omega⟩
        rw [ιN_coeff_nat] at hr
        split_ifs at hr with hd
        · by_contra hlt
          apply hr
          rw [hg r (k / N) (by have := Nat.div_le_self k N; simp at hlt; omega)]
          simp
        · simp at hr)

theorem ιN_mkSum (g : ℕ → PowerSeries ℤ) (hg : ∀ r k, k < r → PowerSeries.coeff k (g r) = 0) :
    ιN hN (PowerSeries.mk fun c => PowerSeries.coeff c (∑ r ∈ range (c + 1), g r)) = hs (trF hN g hg) := by
  ext m
  rw [hs, SummableFamily.coeff_hsum]
  rcases lt_or_ge m 0 with hm | hm
  · rw [ιN_coeff_neg hN _ hm]
    exact (finsum_eq_zero_of_forall_eq_zero fun n => ιN_coeff_neg hN _ hm).symm
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k := ⟨m.toNat, by omega⟩
    simp only [trF, ofSupp_apply, ιN_coeff_nat]
    split_ifs with hd
    · rw [PowerSeries.coeff_mk, map_sum, Int.cast_sum,
        finsum_eq_sum_of_support_subset (s := Finset.range (k / N + 1))]
      intro n hn
      rw [Function.mem_support] at hn
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hlt
      apply hn
      rw [hg n (k / N) (by omega)]
      simp
    · simp

end Transfer

/-! ## Monomials and `C(r,2)` -/

lemma choose_succ2 (r : ℕ) : (r + 1).choose 2 = r.choose 2 + r := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]

lemma sq_choose (r : ℕ) : r ^ 2 = 2 * r.choose 2 + r := by
  induction r with
  | zero => simp
  | succ r ih => rw [choose_succ2, add_sq, ih]; ring

lemma c2_nat (r : ℕ) : c2 r = (r.choose 2 : ℤ) := by
  have h := two_c2 (r : ℤ)
  have h2 : ((r ^ 2 : ℕ) : ℤ) = 2 * (r.choose 2 : ℤ) + r := by rw [sq_choose]; push_cast; ring
  push_cast at h2
  have : 2 * c2 r = 2 * (r.choose 2 : ℤ) := by linear_combination h + h2
  omega

lemma c2_neg (k : ℤ) : c2 (-k) = c2 k + k := by
  have := c2_one_sub (k + 1)
  rw [c2_succ, show 1 - (k + 1) = -k by ring] at this
  exact this

section L5
variable {N : ℕ} (hN : 1 ≤ N)

lemma mono_nat (k : ℕ) (c : ℂ) : (mono (N * k) c : L) = mono 0 c * (mono N 1) ^ k := by
  rw [mono_pow1, mono_mul]; exact mono_ext (by ring) (by ring)

lemma mono_add1 (A B : ℤ) (c : ℂ) : (mono (A + B) c : L) = mono A c * mono B 1 := by
  rw [mono_mul, mul_one]

lemma xq_ne : (mono N 1 : L) ≠ 0 := by simp [mono]

include hN in
lemma one_sub_xpow_ne (m : ℕ) (hm : 1 ≤ m) : (1 : L) - mono N 1 ^ m ≠ 0 := by
  rw [mono_pow1]
  refine one_sub_mono_ne_zero fun h => ?_
  exact mul_ne_zero (by exact_mod_cast (show m ≠ 0 by omega)) (by exact_mod_cast (show N ≠ 0 by omega)) h.1

lemma inv_flip (E : ℤ) (hE : E ≠ 0) :
    (1 - mono (-E) 1 : L)⁻¹ = -mono E 1 * (1 - mono E 1)⁻¹ := by
  have hw : (mono E 1 : L) ≠ 0 := by simp [mono]
  have h1 : (1 : L) - mono E 1 ≠ 0 := one_sub_mono_ne_zero (by simp [hE])
  have h2 : (mono E 1 : L) - 1 ≠ 0 := fun h => h1 (by linear_combination -h)
  have hm : (mono (-E) 1 : L) = (mono E 1)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [mono_mul, show (1 : L) = mono 0 1 from rfl]
    exact mono_ext (by ring) (by norm_num)
  rw [hm]
  field_simp
  ring

include hN in
lemma h15 : 1 ≤ 15 * N := by omega

include hN in
lemma lamOK18 (b : ℤ) : LamOK (15 * N) ((18 - b) * N) 1 (b * N) 1 := fun r ⟨h1, _⟩ => by
  unfold wE at h1
  have h2 : (N : ℤ) * (15 * r + 3) = 0 := by push_cast at h1; linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3 <;> omega

lemma lamT_pos (b : ℕ) (r k1 k2 : ℕ) (hk1 : k1 = 15 * r.choose 2 + b * r) (hk2 : k2 = 15 * r + 3) :
    lamT (15 * N) ((18 - (b : ℤ)) * N) 1 ((b : ℤ) * N) 1 r =
      (-1) ^ r * mono N 1 ^ k1 * (1 - mono N 1 ^ k2)⁻¹ := by
  unfold lamT
  rw [show ((15 * N : ℕ) : ℤ) * c2 (r : ℤ) + (b : ℤ) * N * (r : ℤ) = N * (k1 : ℤ) by
      rw [c2_nat, hk1]; push_cast; ring,
    show wE (15 * N) ((18 - (b : ℤ)) * N) ((b : ℤ) * N) (r : ℤ) = N * (k2 : ℤ) by
      unfold wE; rw [hk2]; push_cast; ring,
    show ((-1 : ℂ) ^ (r : ℤ) * 1 ^ (r : ℤ)) = (-1) ^ r by rw [one_zpow, mul_one, zpow_natCast],
    show ((1 : ℂ) * 1) = 1 from mul_one 1, mono_nat, mono_nat, show (mono 0 1 : L) = 1 from rfl, one_mul,
    ← neg_one_pow_L]

include hN in
lemma lamT_neg (b : ℕ) (hb : b ≤ 30) (r k1 k2 : ℕ) (hk1 : k1 + 3 = 15 * r.choose 2 + (30 - b) * r)
    (hk2 : k2 + 3 = 15 * r) (hk20 : k2 ≠ 0) :
    lamT (15 * N) ((18 - (b : ℤ)) * N) 1 ((b : ℤ) * N) 1 (-(r : ℤ)) =
      -((-1) ^ r * mono N 1 ^ k1 * (1 - mono N 1 ^ k2)⁻¹) := by
  have hk1' : (k1 : ℤ) + 3 = 15 * (r.choose 2 : ℤ) + (30 - (b : ℤ)) * r := by
    have := congrArg (fun n : ℕ => (n : ℤ)) hk1; push_cast [Nat.cast_sub hb] at this; exact this
  have hk2' : (k2 : ℤ) + 3 = 15 * r := by exact_mod_cast hk2
  have hN0 : (N : ℤ) * k2 ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (show N ≠ 0 by omega)) (by exact_mod_cast hk20)
  unfold lamT
  rw [show ((15 * N : ℕ) : ℤ) * c2 (-(r : ℤ)) + (b : ℤ) * N * (-(r : ℤ)) = N * (k1 : ℤ) + -(N * (k2 : ℤ)) by
      rw [c2_neg, c2_nat]; push_cast; linear_combination (-(N : ℤ)) * hk1' + (N : ℤ) * hk2',
    show wE (15 * N) ((18 - (b : ℤ)) * N) ((b : ℤ) * N) (-(r : ℤ)) = -(N * (k2 : ℤ)) by
      unfold wE; push_cast; linear_combination (N : ℤ) * hk2',
    show ((-1 : ℂ) ^ (-(r : ℤ)) * 1 ^ (-(r : ℤ))) = (-1) ^ r by
      rw [zpow_neg, one_zpow, mul_one, zpow_natCast, ← inv_pow, inv_neg, inv_one],
    show ((1 : ℂ) * 1) = 1 from mul_one 1, mono_add1, inv_flip _ hN0]
  have hm : (mono (-(N * (k2 : ℤ))) 1 : L) * mono N 1 ^ k2 = 1 := by
    rw [mono_pow1, mono_mul, show (1 : L) = mono 0 1 from rfl]
    exact mono_ext (by ring) (by norm_num)
  rw [mono_nat, mono_nat, show (mono 0 1 : L) = 1 from rfl, one_mul, ← neg_one_pow_L]
  linear_combination (-((-1 : L) ^ r * mono N 1 ^ k1 * (1 - mono N 1 ^ k2)⁻¹)) * hm

/-- the `r`-th term `q^{5r²} α_r` of `rank_AL_m` at `a = 1`, `b = 5`. -/
noncomputable def gR (r : ℕ) : PowerSeries ℤ := PowerSeries.X ^ (5 * r ^ 2) * αm 1 5 r

lemma gR_ord : ∀ r k, k < r → PowerSeries.coeff k (gR r) = 0 := fun r k hk => by
  unfold gR
  have := Nat.le_self_pow two_ne_zero r
  exact coeffZ_Xpow_zero (by omega) _

lemma gR_term (r : ℕ) (hr : r ≠ 0) (k0 k3 : ℕ) (hk0 : 5 * r ^ 2 + (5 * (r + 1).choose 2 - 1) = k0)
    (hk3 : 5 * r - 1 = k3) :
    ιN hN (gR r) = (-1) ^ r * mono N 1 ^ k0 * (1 + mono N 1 ^ (5 * r)) * (-(1 - mono N 1) ^ 2) *
      ((1 - mono N 1 ^ (1 + 5 * r)) * (1 - mono N 1 ^ k3))⁻¹ := by
  have hu : IsUnit ((1 - PowerSeries.X ^ (1 + 5 * r)) * (1 - PowerSeries.X ^ (5 * r - 1)) : PowerSeries ℤ) :=
    (isUnit_one_sub_Xpow (by omega)).mul (isUnit_one_sub_Xpow (by omega))
  rw [gR, αm, if_neg hr, map_mul, map_mul, CrankProof.map_inverse _ hu, Ring.inverse_eq_inv']
  simp only [map_mul, map_pow, map_neg, map_add, map_sub, map_one, ιN_X hN, pow_one]
  rw [← hk0, ← hk3, _root_.pow_add]
  ring

/-- the three Lambert families. -/
noncomputable def LF (b : ℤ) : SummableFamily ℤ ℂ ℤ :=
  lamF (h15 hN) one_ne_zero one_ne_zero (lamOK18 hN b)

/-- `(1 − q)(A₁₀ + q A₁₅ + q² A₂₀)` termwise. -/
noncomputable def FF : SummableFamily ℤ ℂ ℤ :=
  (1 - mono N 1) • (LF hN 10 + mono N 1 • LF hN 15 + mono N 1 ^ 2 • LF hN 20)

lemma FF_apply (n : ℤ) : FF hN n = (1 - mono N 1) *
    (lamT (15 * N) ((18 - ((10 : ℕ) : ℤ)) * N) 1 (((10 : ℕ) : ℤ) * N) 1 n +
      mono N 1 * lamT (15 * N) ((18 - ((15 : ℕ) : ℤ)) * N) 1 (((15 : ℕ) : ℤ) * N) 1 n +
      mono N 1 ^ 2 * lamT (15 * N) ((18 - ((20 : ℕ) : ℤ)) * N) 1 (((20 : ℕ) : ℤ) * N) 1 n) := by
  simp only [FF, LF, SummableFamily.add_apply, SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul,
    lamF, ofSupp_apply, Nat.cast_ofNat]

lemma hs_FF : hs (FF hN) = (1 - mono N 1) *
    (hs (LF hN 10) + mono N 1 * hs (LF hN 15) + mono N 1 ^ 2 * hs (LF hN 20)) := by
  simp only [FF, hs, SummableFamily.hsum_smul, SummableFamily.hsum_add]

lemma pair_term (r : ℕ) : trF hN gR gR_ord r = if r = 0 then FF hN 0 else FF hN r + FF hN (-(r : ℤ)) := by
  show ιN hN (gR r) = _
  have hx : (mono N 1 : L) ≠ 0 := xq_ne
  split_ifs with h0
  · subst h0
    have e10 := lamT_pos (N := N) 10 0 0 3 (by simp) (by simp)
    have e15 := lamT_pos (N := N) 15 0 0 3 (by simp) (by simp)
    have e20 := lamT_pos (N := N) 20 0 0 3 (by simp) (by simp)
    simp only [Nat.cast_zero] at e10 e15 e20
    rw [FF_apply, e10, e15, e20]
    have h3 := one_sub_xpow_ne hN 3 (by norm_num)
    have hg0 : ιN hN (gR 0) = 1 := by simp [gR, αm]
    rw [hg0]
    simp only [pow_zero, one_mul]
    field_simp
    ring
  · have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr h0
    have hsq := sq_choose r
    have hcs := choose_succ2 r
    obtain ⟨k0, hk0⟩ : ∃ k, 5 * r ^ 2 + (5 * (r + 1).choose 2 - 1) = k := ⟨_, rfl⟩
    have hk0' : k0 + 1 = 15 * r.choose 2 + 10 * r := by omega
    obtain ⟨k3, hk3⟩ : ∃ k, 5 * r - 1 = k := ⟨_, rfl⟩
    have hk3' : k3 + 1 = 5 * r := by omega
    obtain ⟨k2, hk2⟩ : ∃ k, k + 3 = 15 * r := ⟨15 * r - 3, by omega⟩
    obtain ⟨ka, hka⟩ : ∃ k, k + 3 = 15 * r.choose 2 + 20 * r := ⟨_, Nat.sub_add_cancel (by omega)⟩
    obtain ⟨kb, hkb⟩ : ∃ k, k + 3 = 15 * r.choose 2 + 15 * r := ⟨_, Nat.sub_add_cancel (by omega)⟩
    obtain ⟨kc, hkc⟩ : ∃ k, k + 3 = 15 * r.choose 2 + 10 * r := ⟨_, Nat.sub_add_cancel (by omega)⟩
    have hk20 : k2 ≠ 0 := by omega
    rw [gR_term hN r h0 k0 k3 hk0 hk3, FF_apply, FF_apply,
      lamT_pos 10 r _ _ rfl rfl, lamT_pos 15 r _ _ rfl rfl, lamT_pos 20 r _ _ rfl rfl,
      lamT_neg hN 10 (by norm_num) r ka k2 (by omega) hk2 hk20, lamT_neg hN 15 (by norm_num) r kb k2 (by omega) hk2 hk20,
      lamT_neg hN 20 (by norm_num) r kc k2 (by omega) hk2 hk20]
    -- everything in `x = q`, `P = q^{C(r,2)}`, `Y = q^r`
    set x : L := mono N 1 with hxdef
    set P : L := x ^ r.choose 2
    set Y : L := x ^ r
    have e0 : x ^ k0 = P ^ 15 * Y ^ 10 / x := by
      rw [eq_div_iff hx, ← pow_succ, hk0', _root_.pow_add, pow_mul', pow_mul']
    have e3 : x ^ k3 = Y ^ 5 / x := by rw [eq_div_iff hx, ← pow_succ, hk3', pow_mul']
    have e5 : x ^ (5 * r) = Y ^ 5 := pow_mul' _ _ _
    have e15 : x ^ (1 + 5 * r) = x * Y ^ 5 := by rw [_root_.pow_add, pow_one, pow_mul']
    have p10 : x ^ (15 * r.choose 2 + 10 * r) = P ^ 15 * Y ^ 10 := by rw [_root_.pow_add, pow_mul', pow_mul']
    have p15 : x ^ (15 * r.choose 2 + 15 * r) = P ^ 15 * Y ^ 15 := by rw [_root_.pow_add, pow_mul', pow_mul']
    have p20 : x ^ (15 * r.choose 2 + 20 * r) = P ^ 15 * Y ^ 20 := by rw [_root_.pow_add, pow_mul', pow_mul']
    have d3 : x ^ (15 * r + 3) = Y ^ 15 * x ^ 3 := by rw [_root_.pow_add, pow_mul']
    have hx3 : x ^ 3 ≠ 0 := pow_ne_zero 3 hx
    have ea : x ^ ka = P ^ 15 * Y ^ 20 / x ^ 3 := by rw [eq_div_iff hx3, ← _root_.pow_add, hka, _root_.pow_add, pow_mul', pow_mul']
    have eb : x ^ kb = P ^ 15 * Y ^ 15 / x ^ 3 := by rw [eq_div_iff hx3, ← _root_.pow_add, hkb, _root_.pow_add, pow_mul', pow_mul']
    have ec : x ^ kc = P ^ 15 * Y ^ 10 / x ^ 3 := by rw [eq_div_iff hx3, ← _root_.pow_add, hkc, _root_.pow_add, pow_mul', pow_mul']
    have e2 : x ^ k2 = Y ^ 15 / x ^ 3 := by rw [eq_div_iff hx3, ← _root_.pow_add, hk2, pow_mul']
    have n1 := one_sub_xpow_ne hN (15 * r + 3) (by omega)
    have n2 := one_sub_xpow_ne hN k2 (by omega)
    have n3 := one_sub_xpow_ne hN (1 + 5 * r) (by omega)
    have n4 := one_sub_xpow_ne hN k3 (by omega)
    rw [← hxdef] at n1 n2 n3 n4
    rw [d3] at n1; rw [e2] at n2; rw [e15] at n3; rw [e3] at n4
    have n2' : x ^ 3 - Y ^ 15 ≠ 0 := fun h => n2 (by field_simp; linear_combination h)
    have n4' : x - Y ^ 5 ≠ 0 := fun h => n4 (by field_simp; linear_combination h)
    have n3' : 1 - Y ^ 5 * x ≠ 0 := fun h => n3 (by linear_combination h)
    have n1' : 1 - x ^ 3 * Y ^ 15 ≠ 0 := fun h => n1 (by linear_combination h)
    rw [e0, e3, e5, e15, p10, p15, p20, d3, ea, eb, ec, e2]
    field_simp
    ring

/-- **`(1 + φ(q))(q⁵;q⁵)_∞ = A₁₀ + q A₁₅ + q² A₂₀`**. -/
theorem L5_lam :
    ιN hN (Phi 1) * ιN hN (Ea 5 (by norm_num) MockTheta5.JTP.qfacInf) =
      hs (LF hN 10) + mono N 1 * hs (LF hN 15) + mono N 1 ^ 2 * hs (LF hN 20) := by
  have hA : ιN hN (ALm 1 5) = hs (trF hN gR gR_ord) := ιN_mkSum hN gR gR_ord
  have hP := hs_int_pair (FF hN) (trF hN gR gR_ord) (pair_term hN)
  have hF := hs_FF hN
  have hU : Ea 5 (by norm_num) MockTheta5.JTP.qfacInf * Ea 5 (by norm_num) (Ring.inverse MockTheta5.JTP.qfacInf) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel _ MockTheta5.JTP.isUnit_qfacInf, map_one]
  have h1 := rank_AL_m (a := 1) (b := 5) one_pos (by norm_num)
  have h2 := Phi_Dm
  have hAL : ALm 1 5 = (1 - PowerSeries.X) * Phi 1 * Ea 5 (by norm_num) MockTheta5.JTP.qfacInf := by
    linear_combination (-(Ea 5 (by norm_num) MockTheta5.JTP.qfacInf)) * h2 +
      (-(Ea 5 (by norm_num) MockTheta5.JTP.qfacInf)) * h1 + (-(ALm 1 5)) * hU
  have hx : (1 : L) - mono N 1 ≠ 0 := by
    have := one_sub_xpow_ne hN 1 le_rfl; rwa [pow_one] at this
  apply mul_left_cancel₀ hx
  rw [← hF, hP, ← hA, hAL]
  simp only [map_mul, map_sub, map_one, ιN_X hN]
  ring

end L5

end MTC
