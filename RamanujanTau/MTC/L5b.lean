/-
# `ψ(q)` as three Appell–Lerch numerators

As `L5` with `a = 2`: from `rank_AL_m` at `z = X²`, `q = X⁵`,

  `(1 + ψ(q)) (q⁵;q⁵)_∞ = A₁₀ + q² A₁₅ + q⁴ A₂₀`,  `A_b = Σ_n (−1)^n q^{15C(n,2) + bn}/(1 − q^{15n+6})`

(`L5_lam₂`), via `1/(1 − y) = (1 + y + y²)/(1 − y³)` with `y = q^{5n+2}`.
-/
import RamanujanTau.MTC.L5

set_option autoImplicit false

namespace MTC
open ALz HahnSeries Finset RankProof

lemma Pfin_2_5 (n : ℕ) : Pfin 2 5 (n + 1) = (1 - PowerSeries.X ^ 2) * Pfin 7 5 n := by
  rw [Pfin, Pfin, Finset.prod_range_succ', mul_comm,
    Finset.prod_congr rfl (fun i _ => show (1 - PowerSeries.X ^ (2 + 5 * (i + 1)) : PowerSeries ℤ) =
      1 - PowerSeries.X ^ (7 + 5 * i) by ring_nf)]

/-- `(1 − q²)(1 + ψ(q)) = Σ q^{5n²}/((q⁷;q⁵)_n (q³;q⁵)_n)`. -/
theorem Phi_Dm2 : (1 - PowerSeries.X ^ 2) * Phi 2 = Dm 2 5 := by
  ext c
  rw [coeffZ_congr (Phi_dvd 2 c), Dm, PowerSeries.coeff_mk]
  congr 1
  rw [PhiTr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Pfin_2_5, show (5 : ℕ) - 2 = 3 from rfl, show (2 : ℕ) + 5 = 7 from rfl]
  have hu : IsUnit (1 - PowerSeries.X ^ 2 : PowerSeries ℤ) := isUnit_one_sub_Xpow (k := 2) two_pos
  rw [show (1 - PowerSeries.X ^ 2) * (PowerSeries.X ^ (5 * n ^ 2) * Ring.inverse ((1 - PowerSeries.X ^ 2) * Pfin 7 5 n) *
      Ring.inverse (Pfin 3 5 n)) = PowerSeries.X ^ (5 * n ^ 2) * ((1 - PowerSeries.X ^ 2) *
      Ring.inverse ((1 - PowerSeries.X ^ 2) * Pfin 7 5 n)) * Ring.inverse (Pfin 3 5 n) by ring, mul_inverse_mul hu]

section L5b
variable {N : ℕ} (hN : 1 ≤ N)

include hN in
lemma lamOK21 (b : ℤ) : LamOK (15 * N) ((21 - b) * N) 1 (b * N) 1 := fun r ⟨h1, _⟩ => by
  unfold wE at h1
  have h2 : (N : ℤ) * (15 * r + 6) = 0 := by push_cast at h1; linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3 <;> omega

lemma lamT_pos₂ (b : ℕ) (r k1 k2 : ℕ) (hk1 : k1 = 15 * r.choose 2 + b * r) (hk2 : k2 = 15 * r + 6) :
    lamT (15 * N) ((21 - (b : ℤ)) * N) 1 ((b : ℤ) * N) 1 r =
      (-1) ^ r * mono N 1 ^ k1 * (1 - mono N 1 ^ k2)⁻¹ := by
  unfold lamT
  rw [show ((15 * N : ℕ) : ℤ) * c2 (r : ℤ) + (b : ℤ) * N * (r : ℤ) = N * (k1 : ℤ) by
      rw [c2_nat, hk1]; push_cast; ring,
    show wE (15 * N) ((21 - (b : ℤ)) * N) ((b : ℤ) * N) (r : ℤ) = N * (k2 : ℤ) by
      unfold wE; rw [hk2]; push_cast; ring,
    show ((-1 : ℂ) ^ (r : ℤ) * 1 ^ (r : ℤ)) = (-1) ^ r by rw [one_zpow, mul_one, zpow_natCast],
    show ((1 : ℂ) * 1) = 1 from mul_one 1, mono_nat, mono_nat, show (mono 0 1 : L) = 1 from rfl, one_mul,
    ← neg_one_pow_L]

include hN in
lemma lamT_neg₂ (b : ℕ) (hb : b ≤ 30) (r k1 k2 : ℕ) (hk1 : k1 + 6 = 15 * r.choose 2 + (30 - b) * r)
    (hk2 : k2 + 6 = 15 * r) (hk20 : k2 ≠ 0) :
    lamT (15 * N) ((21 - (b : ℤ)) * N) 1 ((b : ℤ) * N) 1 (-(r : ℤ)) =
      -((-1) ^ r * mono N 1 ^ k1 * (1 - mono N 1 ^ k2)⁻¹) := by
  have hk1' : (k1 : ℤ) + 6 = 15 * (r.choose 2 : ℤ) + (30 - (b : ℤ)) * r := by
    have := congrArg (fun n : ℕ => (n : ℤ)) hk1; push_cast [Nat.cast_sub hb] at this; exact this
  have hk2' : (k2 : ℤ) + 6 = 15 * r := by exact_mod_cast hk2
  have hN0 : (N : ℤ) * k2 ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (show N ≠ 0 by omega)) (by exact_mod_cast hk20)
  unfold lamT
  rw [show ((15 * N : ℕ) : ℤ) * c2 (-(r : ℤ)) + (b : ℤ) * N * (-(r : ℤ)) = N * (k1 : ℤ) + -(N * (k2 : ℤ)) by
      rw [c2_neg, c2_nat]; push_cast; linear_combination (-(N : ℤ)) * hk1' + (N : ℤ) * hk2',
    show wE (15 * N) ((21 - (b : ℤ)) * N) ((b : ℤ) * N) (-(r : ℤ)) = -(N * (k2 : ℤ)) by
      unfold wE; push_cast; linear_combination (N : ℤ) * hk2',
    show ((-1 : ℂ) ^ (-(r : ℤ)) * 1 ^ (-(r : ℤ))) = (-1) ^ r by
      rw [zpow_neg, one_zpow, mul_one, zpow_natCast, ← inv_pow, inv_neg, inv_one],
    show ((1 : ℂ) * 1) = 1 from mul_one 1, mono_add1, inv_flip _ hN0]
  have hm : (mono (-(N * (k2 : ℤ))) 1 : L) * mono N 1 ^ k2 = 1 := by
    rw [mono_pow1, mono_mul, show (1 : L) = mono 0 1 from rfl]
    exact mono_ext (by ring) (by norm_num)
  rw [mono_nat, mono_nat, show (mono 0 1 : L) = 1 from rfl, one_mul, ← neg_one_pow_L]
  linear_combination (-((-1 : L) ^ r * mono N 1 ^ k1 * (1 - mono N 1 ^ k2)⁻¹)) * hm

/-- the `r`-th term `q^{5r²} α_r` of `rank_AL_m` at `a = 2`, `b = 5`. -/
noncomputable def gR₂ (r : ℕ) : PowerSeries ℤ := PowerSeries.X ^ (5 * r ^ 2) * αm 2 5 r

lemma gR_ord₂ : ∀ r k, k < r → PowerSeries.coeff k (gR₂ r) = 0 := fun r k hk => by
  unfold gR₂
  have := Nat.le_self_pow two_ne_zero r
  exact coeffZ_Xpow_zero (by omega) _

lemma gR_term₂ (r : ℕ) (hr : r ≠ 0) (k0 k3 : ℕ) (hk0 : 5 * r ^ 2 + (5 * (r + 1).choose 2 - 2) = k0)
    (hk3 : 5 * r - 2 = k3) :
    ιN hN (gR₂ r) = (-1) ^ r * mono N 1 ^ k0 * (1 + mono N 1 ^ (5 * r)) * (-(1 - mono N 1 ^ 2) ^ 2) *
      ((1 - mono N 1 ^ (2 + 5 * r)) * (1 - mono N 1 ^ k3))⁻¹ := by
  have hu : IsUnit ((1 - PowerSeries.X ^ (2 + 5 * r)) * (1 - PowerSeries.X ^ (5 * r - 2)) : PowerSeries ℤ) :=
    (isUnit_one_sub_Xpow (by omega)).mul (isUnit_one_sub_Xpow (by omega))
  rw [gR₂, αm, if_neg hr, map_mul, map_mul, CrankProof.map_inverse _ hu, Ring.inverse_eq_inv']
  simp only [map_mul, map_pow, map_neg, map_add, map_sub, map_one, ιN_X hN, pow_one]
  rw [← hk0, ← hk3, _root_.pow_add]
  ring

/-- the three Lambert families. -/
noncomputable def LF₂ (b : ℤ) : SummableFamily ℤ ℂ ℤ :=
  lamF (h15 hN) one_ne_zero one_ne_zero (lamOK21 hN b)

/-- `(1 − q)(A₁₀ + q A₁₅ + q² A₂₀)` termwise. -/
noncomputable def FF₂ : SummableFamily ℤ ℂ ℤ :=
  (1 - mono N 1 ^ 2) • (LF₂ hN 10 + mono N 1 ^ 2 • LF₂ hN 15 + mono N 1 ^ 4 • LF₂ hN 20)

lemma FF_apply₂ (n : ℤ) : FF₂ hN n = (1 - mono N 1 ^ 2) *
    (lamT (15 * N) ((21 - ((10 : ℕ) : ℤ)) * N) 1 (((10 : ℕ) : ℤ) * N) 1 n +
      mono N 1 ^ 2 * lamT (15 * N) ((21 - ((15 : ℕ) : ℤ)) * N) 1 (((15 : ℕ) : ℤ) * N) 1 n +
      mono N 1 ^ 4 * lamT (15 * N) ((21 - ((20 : ℕ) : ℤ)) * N) 1 (((20 : ℕ) : ℤ) * N) 1 n) := by
  simp only [FF₂, LF₂, SummableFamily.add_apply, SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul,
    lamF, ofSupp_apply, Nat.cast_ofNat]

lemma hs_FF₂ : hs (FF₂ hN) = (1 - mono N 1 ^ 2) *
    (hs (LF₂ hN 10) + mono N 1 ^ 2 * hs (LF₂ hN 15) + mono N 1 ^ 4 * hs (LF₂ hN 20)) := by
  simp only [FF₂, hs, SummableFamily.hsum_smul, SummableFamily.hsum_add]

lemma pair_term₂ (r : ℕ) : trF hN gR₂ gR_ord₂ r = if r = 0 then FF₂ hN 0 else FF₂ hN r + FF₂ hN (-(r : ℤ)) := by
  show ιN hN (gR₂ r) = _
  have hx : (mono N 1 : L) ≠ 0 := xq_ne
  split_ifs with h0
  · subst h0
    have e10 := lamT_pos₂ (N := N) 10 0 0 6 (by simp) (by simp)
    have e15 := lamT_pos₂ (N := N) 15 0 0 6 (by simp) (by simp)
    have e20 := lamT_pos₂ (N := N) 20 0 0 6 (by simp) (by simp)
    simp only [Nat.cast_zero] at e10 e15 e20
    rw [FF_apply₂, e10, e15, e20]
    have h3 := one_sub_xpow_ne hN 6 (by norm_num)
    have h2' := one_sub_xpow_ne hN 2 (by norm_num)
    have hg0 : ιN hN (gR₂ 0) = 1 := by simp [gR₂, αm]
    rw [hg0]
    simp only [pow_zero, one_mul]
    field_simp
    ring
  · have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr h0
    have hsq := sq_choose r
    have hcs := choose_succ2 r
    obtain ⟨k0, hk0⟩ : ∃ k, 5 * r ^ 2 + (5 * (r + 1).choose 2 - 2) = k := ⟨_, rfl⟩
    have hk0' : k0 + 2 = 15 * r.choose 2 + 10 * r := by omega
    obtain ⟨k3, hk3⟩ : ∃ k, 5 * r - 2 = k := ⟨_, rfl⟩
    have hk3' : k3 + 2 = 5 * r := by omega
    obtain ⟨k2, hk2⟩ : ∃ k, k + 6 = 15 * r := ⟨15 * r - 6, by omega⟩
    obtain ⟨ka, hka⟩ : ∃ k, k + 6 = 15 * r.choose 2 + 20 * r := ⟨_, Nat.sub_add_cancel (by omega)⟩
    obtain ⟨kb, hkb⟩ : ∃ k, k + 6 = 15 * r.choose 2 + 15 * r := ⟨_, Nat.sub_add_cancel (by omega)⟩
    obtain ⟨kc, hkc⟩ : ∃ k, k + 6 = 15 * r.choose 2 + 10 * r := ⟨_, Nat.sub_add_cancel (by omega)⟩
    have hk20 : k2 ≠ 0 := by omega
    rw [gR_term₂ hN r h0 k0 k3 hk0 hk3, FF_apply₂, FF_apply₂,
      lamT_pos₂ 10 r _ _ rfl rfl, lamT_pos₂ 15 r _ _ rfl rfl, lamT_pos₂ 20 r _ _ rfl rfl,
      lamT_neg₂ hN 10 (by norm_num) r ka k2 (by omega) hk2 hk20, lamT_neg₂ hN 15 (by norm_num) r kb k2 (by omega) hk2 hk20,
      lamT_neg₂ hN 20 (by norm_num) r kc k2 (by omega) hk2 hk20]
    -- everything in `x = q`, `P = q^{C(r,2)}`, `Y = q^r`
    set x : L := mono N 1 with hxdef
    set P : L := x ^ r.choose 2
    set Y : L := x ^ r
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    have e0 : x ^ k0 = P ^ 15 * Y ^ 10 / x ^ 2 := by
      rw [eq_div_iff hx2, ← _root_.pow_add, hk0', _root_.pow_add, pow_mul', pow_mul']
    have e3 : x ^ k3 = Y ^ 5 / x ^ 2 := by rw [eq_div_iff hx2, ← _root_.pow_add, hk3', pow_mul']
    have e5 : x ^ (5 * r) = Y ^ 5 := pow_mul' _ _ _
    have e15 : x ^ (2 + 5 * r) = x ^ 2 * Y ^ 5 := by rw [_root_.pow_add, pow_mul']
    have p10 : x ^ (15 * r.choose 2 + 10 * r) = P ^ 15 * Y ^ 10 := by rw [_root_.pow_add, pow_mul', pow_mul']
    have p15 : x ^ (15 * r.choose 2 + 15 * r) = P ^ 15 * Y ^ 15 := by rw [_root_.pow_add, pow_mul', pow_mul']
    have p20 : x ^ (15 * r.choose 2 + 20 * r) = P ^ 15 * Y ^ 20 := by rw [_root_.pow_add, pow_mul', pow_mul']
    have d3 : x ^ (15 * r + 6) = Y ^ 15 * x ^ 6 := by rw [_root_.pow_add, pow_mul']
    have hx3 : x ^ 6 ≠ 0 := pow_ne_zero 6 hx
    have ea : x ^ ka = P ^ 15 * Y ^ 20 / x ^ 6 := by rw [eq_div_iff hx3, ← _root_.pow_add, hka, _root_.pow_add, pow_mul', pow_mul']
    have eb : x ^ kb = P ^ 15 * Y ^ 15 / x ^ 6 := by rw [eq_div_iff hx3, ← _root_.pow_add, hkb, _root_.pow_add, pow_mul', pow_mul']
    have ec : x ^ kc = P ^ 15 * Y ^ 10 / x ^ 6 := by rw [eq_div_iff hx3, ← _root_.pow_add, hkc, _root_.pow_add, pow_mul', pow_mul']
    have e2 : x ^ k2 = Y ^ 15 / x ^ 6 := by rw [eq_div_iff hx3, ← _root_.pow_add, hk2, pow_mul']
    have n1 := one_sub_xpow_ne hN (15 * r + 6) (by omega)
    have n2 := one_sub_xpow_ne hN k2 (by omega)
    have n3 := one_sub_xpow_ne hN (2 + 5 * r) (by omega)
    have n4 := one_sub_xpow_ne hN k3 (by omega)
    rw [← hxdef] at n1 n2 n3 n4
    rw [d3] at n1; rw [e2] at n2; rw [e15] at n3; rw [e3] at n4
    have n2' : x ^ 6 - Y ^ 15 ≠ 0 := fun h => n2 (by field_simp; linear_combination h)
    have n4' : x ^ 2 - Y ^ 5 ≠ 0 := fun h => n4 (by field_simp; linear_combination h)
    have n3' : 1 - Y ^ 5 * x ^ 2 ≠ 0 := fun h => n3 (by linear_combination h)
    have n1' : 1 - x ^ 6 * Y ^ 15 ≠ 0 := fun h => n1 (by linear_combination h)
    rw [e0, e3, e5, e15, p10, p15, p20, d3, ea, eb, ec, e2]
    field_simp
    ring

/-- **`(1 + ψ(q))(q⁵;q⁵)_∞ = A₁₀ + q² A₁₅ + q⁴ A₂₀`** (Lambert data `x z = q²¹`). -/
theorem L5_lam₂ :
    ιN hN (Phi 2) * ιN hN (Ea 5 (by norm_num) MockTheta5.JTP.qfacInf) =
      hs (LF₂ hN 10) + mono N 1 ^ 2 * hs (LF₂ hN 15) + mono N 1 ^ 4 * hs (LF₂ hN 20) := by
  have hA : ιN hN (ALm 2 5) = hs (trF hN gR₂ gR_ord₂) := ιN_mkSum hN gR₂ gR_ord₂
  have hP := hs_int_pair (FF₂ hN) (trF hN gR₂ gR_ord₂) (pair_term₂ hN)
  have hF := hs_FF₂ hN
  have hU : Ea 5 (by norm_num) MockTheta5.JTP.qfacInf * Ea 5 (by norm_num) (Ring.inverse MockTheta5.JTP.qfacInf) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel _ MockTheta5.JTP.isUnit_qfacInf, map_one]
  have h1 := rank_AL_m (a := 2) (b := 5) two_pos (by norm_num)
  have h2 := Phi_Dm2
  have hAL : ALm 2 5 = (1 - PowerSeries.X ^ 2) * Phi 2 * Ea 5 (by norm_num) MockTheta5.JTP.qfacInf := by
    linear_combination (-(Ea 5 (by norm_num) MockTheta5.JTP.qfacInf)) * h2 +
      (-(Ea 5 (by norm_num) MockTheta5.JTP.qfacInf)) * h1 + (-(ALm 2 5)) * hU
  have hx : (1 : L) - mono N 1 ^ 2 ≠ 0 := one_sub_xpow_ne hN 2 (by norm_num)
  apply mul_left_cancel₀ hx
  rw [← hF, hP, ← hA, hAL]
  simp only [map_mul, map_sub, map_one, map_pow, ιN_X hN]
  ring

end L5b

end MTC
