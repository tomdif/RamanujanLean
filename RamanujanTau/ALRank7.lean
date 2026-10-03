/-
# Rank mod 7 via Appell–Lerch sums: the bridge

`(q;q)_∞ R(ζ;q) = (1−ζ)·Σ_{i<3} ζ^i (−q^{1−i}) A(ζ³q^{1−i}, q^{i−1}; q³)` in `ℂ((t))`, `t = q`.
-/
import RamanujanTau.ALSplit
import RamanujanTau.RankAL

set_option autoImplicit false

namespace ALz
open HahnSeries Finset

/-! ## Geometric series of monomials -/

section Geo

lemma orderTop_mono_pos {e : ℤ} {c : ℂ} (he : 0 < e) : 0 < (mono e c).orderTop := by
  by_cases hc : c = 0
  · simp [mono, hc]
  · rw [mono, orderTop_single hc]; exact_mod_cast he

/-- `j ↦ yʲ` for `j ≥ 0`, as a family over `ℤ`. -/
noncomputable def geoP (e : ℤ) (c : ℂ) (he : 0 < e) : SummableFamily ℤ ℂ ℤ :=
  (SummableFamily.powers (mono e c)).embDomain ⟨((↑) : ℕ → ℤ), Nat.cast_injective⟩

lemma geoP_apply (e : ℤ) (c : ℂ) (he : 0 < e) (j : ℤ) :
    geoP e c he j = if 0 ≤ j then mono (j * e) (c ^ j) else 0 := by
  unfold geoP
  split_ifs with hj
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k := ⟨j.toNat, by omega⟩
    rw [show (k : ℤ) = (⟨((↑) : ℕ → ℤ), Nat.cast_injective⟩ : ℕ ↪ ℤ) k from rfl,
      SummableFamily.embDomain_image, SummableFamily.powers_of_orderTop_pos (orderTop_mono_pos he),
      ← zpow_natCast, mono_zpow]
    simp
  · rw [SummableFamily.embDomain_notin_range]
    rintro ⟨k, hk⟩; simp at hk; omega

lemma hs_geoP (e : ℤ) (c : ℂ) (he : 0 < e) : (1 - mono e c) * hs (geoP e c he) = 1 := by
  rw [geoP, hs_eq, SummableFamily.hsum_embDomain]
  exact SummableFamily.one_sub_self_mul_hsum_powers (orderTop_mono_pos he)

end Geo


section AbSum
variable {N : ℕ} (hN : 1 ≤ N)
include hN

/-- the `r`-th term of the Appell–Lerch sum, `(−1)^r q^{C(r,2)} p^r / (1 − q^{r−1} x p)`. -/
noncomputable def aTerm (N : ℕ) (a β : ℤ) (cx cp : ℂ) (r : ℤ) : L :=
  mono (N * c2 r + β * r) ((-1) ^ r * cp ^ r) * (1 - mono (N * (r - 1) + a + β) (cx * cp))⁻¹

/-- the Appell–Lerch sum as a summable family of field elements. -/
noncomputable def aSumF {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) (cx cp : ℂ) : SummableFamily ℤ ℂ ℤ :=
  rowFam (asF2 hN hlo hhi cx cp) +
    SummableFamily.single (1 : ℤ) (-mono β cp * (1 - mono (a + β) (cx * cp))⁻¹)

theorem aSumF_apply {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) {cx cp : ℂ} (hx : cx ≠ 0) (hp : cp ≠ 0)
    (r : ℤ) : aSumF hN hlo hhi cx cp r = aTerm N a β cx cp r := by
  have hxp : cx * cp ≠ 0 := mul_ne_zero hx hp
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  simp only [aSumF, SummableFamily.add_apply, rowFam_apply]
  change _ + (Pi.single (1 : ℤ) (-mono β cp * (1 - mono (a + β) (cx * cp))⁻¹) : ℤ → L) r = _
  rcases lt_trichotomy r 1 with hr | rfl | hr
  · -- `r ≤ 0`: reverse geometric series
    rw [Pi.single_apply, if_neg (by omega), add_zero]
    set e := N * (r - 1) + a + β with he
    have he' : 0 < -e := by
      have : (N : ℤ) * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      have : (N : ℤ) * (r - 1) = N * r - N := by ring
      omega
    set M := mono (N * c2 r + β * r) ((-1) ^ r * cp ^ r) with hM
    set y := mono e (cx * cp) with hydef
    have hy : y ≠ 0 := by simp [y, mono, hxp]
    have hyinv : y⁻¹ = mono (-e) (cx * cp)⁻¹ := by rw [mono, inv_single]
    set M' : L := -(M * y⁻¹) with hM'
    have hM'' : M' = mono (N * c2 r + β * r - e) (-((-1) ^ r * cp ^ r * (cx * cp)⁻¹)) := by
      rw [hM', hyinv, hM, mono_mul, mono, mono, ← single_neg]; ring_nf
    have hrow : hs (row (asF2 hN hlo hhi cx cp) r) = M' * hs (geoP (-e) (cx * cp)⁻¹ he') := by
      refine hsum_reindex' (geoP (-e) (cx * cp)⁻¹ he') _ (Equiv.subLeft (-1)) _ fun k => ?_
      simp only [sv, row_apply, Equiv.subLeft_apply, asF2_apply, geoP_apply]
      by_cases hk : 0 ≤ k
      · have hc : cone2 r (-1 - k) := ⟨Or.inr ⟨by omega, by omega⟩, by omega⟩
        rw [if_pos hc, if_pos hk, hM'', mono_mul]
        congr 1
        · unfold asExp; rw [he]; ring
        · unfold sgnC
          rw [if_neg (by omega), show (-1 : ℤ) - k = -(k + 1) by ring, zpow_neg, ← inv_zpow,
            zpow_add₀ (inv_ne_zero hxp), zpow_one]
          ring
      · rw [if_neg (fun h => by unfold cone2 cone at h; omega), if_neg hk, mul_zero]
    rw [hrow, aTerm]
    have hg := hs_geoP (-e) (cx * cp)⁻¹ he'
    rw [← hyinv] at hg
    have h1y : (1 : L) - y ≠ 0 := by
      intro h
      have := congrArg (fun f : L => f.coeff 0) h
      simp [y, mono, coeff_single_of_ne (show (0 : ℤ) ≠ e by omega)] at this
    have h1y' : (1 : L) - y⁻¹ ≠ 0 := by
      intro h; apply h1y; have : y⁻¹ = 1 := by linear_combination -h
      rw [inv_eq_one] at this; rw [this, sub_self]
    have hG : hs (geoP (-e) (cx * cp)⁻¹ he') = (1 - y⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right hg
    rw [hG, hM', ← he, ← hydef, ← hM]
    have h2 : (-1 + y : L) ≠ 0 := by intro h; apply h1y; linear_combination -h
    field_simp
    linear_combination M * mul_inv_cancel₀ h2
  · -- `r = 1`
    rw [Pi.single_apply, if_pos rfl, aTerm]
    have : hs (row (asF2 hN hlo hhi cx cp) 1) = 0 := by
      rw [hs_eq]
      convert SummableFamily.hsum_zero using 2
      ext j; simp [row_apply, asF2_apply, cone2]
    rw [this, zero_add]
    simp [c2, mono]
  · -- `r ≥ 2`: geometric series
    rw [Pi.single_apply, if_neg (by omega), add_zero]
    set e := N * (r - 1) + a + β with he
    have he' : 0 < e := by
      have : (N : ℤ) ≤ N * (r - 1) := by nlinarith
      omega
    set M := mono (N * c2 r + β * r) ((-1) ^ r * cp ^ r) with hM
    have hrow : hs (row (asF2 hN hlo hhi cx cp) r) = M * hs (geoP e (cx * cp) he') := by
      refine hsum_reindex' (geoP e (cx * cp) he') _ (Equiv.refl ℤ) _ fun j => ?_
      simp only [sv, row_apply, Equiv.refl_apply, asF2_apply, geoP_apply]
      by_cases hj : 0 ≤ j
      · have hc : cone2 r j := ⟨Or.inl ⟨by omega, hj⟩, by omega⟩
        rw [if_pos hc, if_pos hj, hM, mono_mul]
        congr 1
        · unfold asExp; rw [he]; ring
        · unfold sgnC; rw [if_pos (by omega)]; ring
      · rw [if_neg (fun h => by unfold cone2 cone at h; omega), if_neg hj, mul_zero]
    rw [hrow, aTerm]
    have hg := hs_geoP e (cx * cp) he'
    have hG : hs (geoP e (cx * cp) he') = (1 - mono e (cx * cp))⁻¹ := eq_inv_of_mul_eq_one_right hg
    rw [hG]

/-- **`A(x,p)` is the honest sum** `Σ_r (−1)^r q^{C(r,2)} p^r/(1 − q^{r−1}xp)`. -/
theorem Ab_eq_sum {a β : ℤ} (hlo : -N < a + β) (hhi : a + β < N) (cx cp : ℂ) :
    Ab hN hlo hhi cx cp = hs (aSumF hN hlo hhi cx cp) := by
  rw [aSumF, hs_eq, SummableFamily.hsum_add, SummableFamily.hsum_single, ← hs_eq, hs_rowFam, Ab, Aser2]
  ring

end AbSum


/-! ## The bilateral Lambert sum `Σ_n (−1)^n q^{n(3n+1)/2}/(1 − ζqⁿ)` as three Appell sums -/

section Lambert
variable (z : ℂ)

lemma h3 : (1 : ℕ) ≤ 3 := by norm_num

/-- `Σ_i ζ^i (−q^{1−i}) A(ζ³q^{1−i}, q^{i−1}; q³)`, reindexed by `n = r − 1`. -/
noncomputable def lamF : SummableFamily ℤ ℂ ℤ :=
  (-mono 1 (z ^ 0)) • SummableFamily.Equiv (Equiv.addRight (-1))
      (aSumF h3 (a := 1) (β := -1) (by norm_num) (by norm_num) (z ^ 3) 1) +
  (-mono 0 (z ^ 1)) • SummableFamily.Equiv (Equiv.addRight (-1))
      (aSumF h3 (a := 0) (β := 0) (by norm_num) (by norm_num) (z ^ 3) 1) +
  (-mono (-1) (z ^ 2)) • SummableFamily.Equiv (Equiv.addRight (-1))
      (aSumF h3 (a := -1) (β := 1) (by norm_num) (by norm_num) (z ^ 3) 1)

variable {z}

lemma lamF_apply (hz : z ≠ 0) (hz1 : z ≠ 1) (hz3 : z ^ 3 ≠ 1) (n : ℤ) :
    lamF z n = mono (3 * c2 n + 2 * n) ((-1) ^ n) * (1 - mono n z)⁻¹ := by
  have hz3' : z ^ 3 ≠ 0 := pow_ne_zero 3 hz
  simp only [lamF, SummableFamily.add_apply, SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul,
    SummableFamily.Equiv_toFun, Equiv.addRight_symm_apply]
  rw [aSumF_apply _ _ _ hz3' one_ne_zero, aSumF_apply _ _ _ hz3' one_ne_zero,
    aSumF_apply _ _ _ hz3' one_ne_zero]
  simp only [aTerm, one_zpow, mul_one, neg_neg]
  set y := mono n z with hy
  have hy3 : mono (3 * n) (z ^ 3) = y ^ 3 := by
    rw [hy, mono, mono, single_pow]; simp
  have e1 : ((3 : ℕ) : ℤ) * (n + 1 - 1) + 1 + -1 = 3 * n := by push_cast; ring
  have e2 : ((3 : ℕ) : ℤ) * (n + 1 - 1) + 0 + 0 = 3 * n := by push_cast; ring
  have e3 : ((3 : ℕ) : ℤ) * (n + 1 - 1) + -1 + 1 = 3 * n := by push_cast; ring
  rw [e1, e2, e3, hy3]
  have hy1 : (1 : L) - y ≠ 0 := by
    intro h
    by_cases hn : n = 0
    · subst hn
      have := congrArg (fun f : L => f.coeff 0) h
      simp [hy, mono] at this
      exact hz1 (by linear_combination -this)
    · have := congrArg (fun f : L => f.coeff 0) h
      simp [hy, mono, coeff_single_of_ne (Ne.symm hn)] at this
  have hy3' : (1 : L) - y ^ 3 ≠ 0 := by
    intro h
    rw [← hy3] at h
    have := congrArg (fun f : L => f.coeff 0) h
    by_cases hn : n = 0
    · subst hn
      simp [mono] at this
      exact hz3 (by linear_combination -this)
    · simp [mono, coeff_single_of_ne (show (0 : ℤ) ≠ 3 * n by omega)] at this
  have hfac : (1 : L) - y ^ 3 = (1 - y) * (1 + y + y ^ 2) := by ring
  -- express all monomials through `y` and a common factor
  set M := mono (3 * c2 n + 2 * n) ((-1 : ℂ) ^ n) with hM
  have m0 : -mono 1 (z ^ 0) * mono (((3 : ℕ) : ℤ) * c2 (n + 1) + -1 * (n + 1)) ((-1) ^ (n + 1)) = M := by
    rw [show -mono 1 (z ^ 0) = mono 1 (-(z ^ 0)) from (single_neg _ _).symm, mono_mul, hM]
    congr 1
    · rw [c2_succ]; push_cast; ring
    · rw [zpow_add₀ (by norm_num)]; ring
  have m1 : -mono 0 (z ^ 1) * mono (((3 : ℕ) : ℤ) * c2 (n + 1) + 0 * (n + 1)) ((-1) ^ (n + 1)) = M * y := by
    rw [show -mono 0 (z ^ 1) = mono 0 (-(z ^ 1)) from (single_neg _ _).symm, mono_mul, hM, hy, mono_mul]
    congr 1
    · rw [c2_succ]; push_cast; ring
    · rw [zpow_add₀ (by norm_num)]; ring
  have m2 : -mono (-1) (z ^ 2) * mono (((3 : ℕ) : ℤ) * c2 (n + 1) + 1 * (n + 1)) ((-1) ^ (n + 1)) = M * y ^ 2 := by
    rw [show -mono (-1) (z ^ 2) = mono (-1) (-(z ^ 2)) from (single_neg _ _).symm, mono_mul, hM, hy,
      mono, mono, single_pow, ← mono, ← mono, mono_mul]
    congr 1
    · rw [c2_succ]; push_cast; ring
    · rw [zpow_add₀ (by norm_num)]; ring
  have hq : (1 : L) + y + y ^ 2 ≠ 0 := by
    intro h; apply hy3'; rw [hfac, h, mul_zero]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, m0, m1, m2, hfac]
  field_simp

end Lambert


/-! ## From `ℂ⟦X⟧` to `ℂ((t))` -/

section Iota
open PowerSeries

/-- `ℂ⟦X⟧ → ℂ((t))`, `X ↦ t`. -/
noncomputable abbrev ι1 : PowerSeries ℂ →+* L := HahnSeries.ofPowerSeries ℤ ℂ

lemma ι1_coeff_neg (f : PowerSeries ℂ) {n : ℤ} (hn : n < 0) : (ι1 f).coeff n = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  exact HahnSeries.embDomain_notin_range (by rintro ⟨k, hk⟩; simp at hk; omega)

lemma ι1_coeff_nat (f : PowerSeries ℂ) (k : ℕ) : (ι1 f).coeff (k : ℤ) = PowerSeries.coeff k f :=
  HahnSeries.ofPowerSeries_apply_coeff f k

lemma ι1_X : ι1 X = mono 1 1 := HahnSeries.ofPowerSeries_X
lemma ι1_C (c : ℂ) : ι1 (PowerSeries.C c) = mono 0 c := by
  rw [HahnSeries.ofPowerSeries_C]; rfl

lemma ι1_inverse {u : PowerSeries ℂ} (hu : IsUnit u) : ι1 (Ring.inverse u) = (ι1 u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, Ring.inverse_mul_cancel _ hu, map_one])

lemma ι1_Xpow_coeff (k : ℕ) (g : PowerSeries ℂ) {n : ℤ} (hn : n < k) : (ι1 (X ^ k * g)).coeff n = 0 := by
  rcases lt_or_ge n 0 with h | h
  · exact ι1_coeff_neg _ h
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
    rw [ι1_coeff_nat, coeff_X_pow_mul', if_neg (by omega)]

end Iota


section Bridge
open PowerSeries

lemma ι1_Xpow (k : ℕ) : ι1 (X ^ k) = mono k 1 := by
  rw [map_pow, ι1_X, mono, single_pow]; simp

/-- the summands of `ALser z`, carried to `ℂ((t))`. -/
noncomputable def alF (z : ℂ) : SummableFamily ℤ ℂ ℕ :=
  ofSupp (fun r => ι1 (X ^ (r ^ 2) * RankProof.αser z r)) 0
    (fun r n hn => ι1_coeff_neg _ hn)
    (fun n => (Set.finite_Iic n.toNat).subset fun r hr => by
      simp only [Set.mem_setOf_eq] at hr
      simp only [Set.mem_Iic]
      by_contra h
      apply hr
      apply ι1_Xpow_coeff
      have : r ≤ r ^ 2 := Nat.le_self_pow two_ne_zero r
      have h1 : (r : ℤ) ≤ ((r ^ 2 : ℕ) : ℤ) := by exact_mod_cast this
      push Not at h
      have : (n.toNat : ℤ) < r := by exact_mod_cast h
      have := Int.self_le_toNat n
      omega)

lemma ι1_ALser (z : ℂ) : ι1 (RankProof.ALser z) = hs (alF z) := by
  ext n
  rw [hs, SummableFamily.coeff_hsum]
  rcases lt_or_ge n 0 with hn | hn
  · rw [ι1_coeff_neg _ hn]
    exact (finsum_eq_zero_of_forall_eq_zero fun r => ι1_coeff_neg _ hn).symm
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, by omega⟩
    rw [ι1_coeff_nat, RankProof.ALser, coeff_mk, map_sum,
      finsum_eq_sum_of_support_subset (s := Finset.range (k + 1))]
    · exact Finset.sum_congr rfl fun r _ => (ι1_coeff_nat _ k).symm
    · intro r hr
      rw [Function.mem_support] at hr
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra h
      apply hr
      apply ι1_Xpow_coeff
      have : r ≤ r ^ 2 := Nat.le_self_pow two_ne_zero r
      have h1 : (r : ℤ) ≤ ((r ^ 2 : ℕ) : ℤ) := by exact_mod_cast this
      push Not at h
      omega


lemma mono0_sub (a b : ℂ) : mono 0 (a - b) = mono 0 a - mono 0 b := by simp [mono, single_sub]
lemma mono0_one : mono 0 (1 : ℂ) = 1 := rfl
lemma mono0_mul (a b : ℂ) : mono 0 (a * b) = mono 0 a * mono 0 b := by rw [mono_mul, add_zero]
lemma mono0_inv (a : ℂ) : mono 0 a⁻¹ = (mono 0 a)⁻¹ := by rw [mono, inv_single, neg_zero]

lemma ne_of_coeff {X : L} (n : ℤ) (h : X.coeff n ≠ 0) : X ≠ 0 := by
  rintro rfl; simp at h

/-- the partial-fraction step: each `ALser` summand is a pair of Lambert terms. -/
theorem alF_pt {z : ℂ} (hz : z ≠ 0) (hz1 : z ≠ 1) (hz3 : z ^ 3 ≠ 1) (r : ℕ) :
    alF z r = mono 0 (1 - z) * (lamF z r + if 1 ≤ r then lamF z (-(r : ℤ)) else 0) := by
  have hZ1 : (1 : L) - mono 0 z ≠ 0 := ne_of_coeff 0 (by
    rw [coeff_sub]; simp [mono]; exact sub_ne_zero.mpr (Ne.symm hz1))
  rw [alF, ofSupp_apply, lamF_apply hz hz1 hz3]
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp only [pow_two, mul_zero, pow_zero, RankProof.αser, if_true, mul_one, map_one, Nat.cast_zero,
      le_refl, Nat.not_succ_le_zero, if_false, add_zero]
    rw [show (3 : ℤ) * c2 0 = 0 by simp [c2], zpow_zero, mono0_one, one_mul, mono0_sub, mono0_one,
      if_neg (by norm_num)]
    simp only [add_zero]
    rw [mul_inv_cancel₀ hZ1]
  · rw [if_pos (show 1 ≤ r from hr), lamF_apply hz hz1 hz3]
    have hr0 : r ≠ 0 := by omega
    simp only [RankProof.αser, if_neg hr0]
    have hu : IsUnit ((1 - PowerSeries.C z * PowerSeries.X ^ r) * (1 - PowerSeries.C z⁻¹ * PowerSeries.X ^ r) :
        PowerSeries ℂ) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]; simp [zero_pow hr0]
    simp only [map_mul, ι1_inverse hu, map_sub, map_add, map_one, ι1_C, ι1_Xpow]
    set Z := mono 0 z with hZ
    set y : L := mono (r : ℤ) 1 with hy
    set T := mono (3 * c2 r + 2 * r) ((-1 : ℂ) ^ (r : ℤ)) with hT
    have hy0 : y ≠ 0 := by simp [hy, mono]
    have hZ0 : Z ≠ 0 := by simp [hZ, mono, hz]
    have hyinv : y⁻¹ = mono (-(r : ℤ)) 1 := by rw [hy, mono, inv_single, inv_one]
    have hZinv : mono 0 z⁻¹ = Z⁻¹ := mono0_inv z
    have e1 : mono ((r : ℤ)) z = Z * y := by rw [hZ, hy, mono_mul]; simp
    have e2 : mono (-(r : ℤ)) z = Z * y⁻¹ := by rw [hZ, hyinv, mono_mul]; simp
    have e3 : mono (3 * c2 (-(r : ℤ)) + 2 * -(r : ℤ)) ((-1 : ℂ) ^ (-(r : ℤ))) = T * y⁻¹ := by
      rw [hT, hyinv, mono_mul]
      congr 1
      · have h1 := two_c2 (-(r : ℤ)); have h2 := two_c2 (r : ℤ); nlinarith
      · rw [zpow_neg, ← inv_zpow, inv_neg, inv_one, mul_one]
    have key : mono ((r ^ 2 : ℕ) : ℤ) (1 : ℂ) * mono 0 ((-1) ^ r) * mono (((r + 1).choose 2 : ℕ) : ℤ) 1 = T := by
      rw [mono_mul, mono_mul, hT]
      congr 1
      · have h1 := two_c2 (r : ℤ)
        have h2 : (((r + 1).choose 2 : ℕ) : ℤ) * 2 = (r + 1) * r := by
          have := Nat.choose_two_right (r + 1)
          have hd : 2 ∣ (r + 1) * r := by
            rcases Nat.even_or_odd r with ⟨m, hm⟩ | ⟨m, hm⟩
            · exact ⟨(r + 1) * m, by rw [hm]; ring⟩
            · exact ⟨(m + 1) * r, by rw [hm]; ring⟩
          rw [show r + 1 - 1 = r by omega] at this
          obtain ⟨k, hk⟩ := hd
          rw [this, hk, Nat.mul_div_cancel_left _ (by norm_num)]
          have : (((r + 1) * r : ℕ) : ℤ) = 2 * k := by exact_mod_cast hk
          push_cast at this ⊢; linarith
        push_cast; nlinarith
      · rw [zpow_natCast]; ring
    rw [hZinv, e1, e2, e3, show mono 0 (1 - z) = 1 - Z by rw [mono0_sub, mono0_one]]
    rw [show mono ((r ^ 2 : ℕ) : ℤ) (1 : ℂ) * (mono 0 ((-1) ^ r) * ((1 - Z) * (1 - Z⁻¹)) *
        mono (((r + 1).choose 2 : ℕ) : ℤ) 1 * (1 + y) * ((1 - Z * y) * (1 - Z⁻¹ * y))⁻¹)
        = (mono ((r ^ 2 : ℕ) : ℤ) (1 : ℂ) * mono 0 ((-1) ^ r) * mono (((r + 1).choose 2 : ℕ) : ℤ) 1) *
          ((1 - Z) * (1 - Z⁻¹)) * (1 + y) * ((1 - Z * y) * (1 - Z⁻¹ * y))⁻¹ by ring, key]
    have hA : (1 : L) - Z * y ≠ 0 := ne_of_coeff 0 (by
      rw [coeff_sub, hZ, hy, mono_mul]
      simp [mono, coeff_single_of_ne (show (0 : ℤ) ≠ 0 + r by omega), coeff_single_of_ne (show (0 : ℤ) ≠ r by omega)])
    have hB : (1 : L) - Z⁻¹ * y ≠ 0 := ne_of_coeff 0 (by
      rw [coeff_sub, ← hZinv, hy, mono_mul]
      simp [mono, coeff_single_of_ne (show (0 : ℤ) ≠ 0 + r by omega), coeff_single_of_ne (show (0 : ℤ) ≠ r by omega)])
    have hC : (1 : L) - Z * y⁻¹ ≠ 0 := ne_of_coeff (-(r : ℤ)) (by
      rw [coeff_sub, hZ, hyinv, mono_mul]
      simp [mono, coeff_single_of_ne (show (-(r : ℤ)) ≠ 0 by omega), hz, hr0])
    have hD : Z - y ≠ 0 := ne_of_coeff 0 (by
      rw [coeff_sub, hZ, hy]; simp [mono, coeff_single_of_ne (show (0 : ℤ) ≠ r by omega), hz])
    have hD' : -Z + y ≠ 0 := by intro h; apply hD; linear_combination -h
    field_simp
    linear_combination (-T * (Z * y - 1)) * mul_inv_cancel₀ hD'


/-- a summable family composed with an injection. -/
noncomputable def compF {ι κ : Type*} (S : SummableFamily ℤ ℂ ι) (f : κ ↪ ι) : SummableFamily ℤ ℂ κ where
  toFun k := S (f k)
  isPWO_iUnion_support' := S.isPWO_iUnion_support.mono fun n hn => by
    simp only [Set.mem_iUnion] at hn ⊢; obtain ⟨k, hk⟩ := hn; exact ⟨f k, hk⟩
  finite_co_support' n := (S.finite_co_support n).preimage f.injective.injOn

def natE : ℕ ↪ ℤ := ⟨fun r => (r : ℤ), Nat.cast_injective⟩
def negE : ℕ ↪ ℤ := ⟨fun r => -((r : ℤ) + 1), fun a b h => by simpa using h⟩
def succE : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩

lemma hs_split_Z (S : SummableFamily ℤ ℂ ℤ) : hs S = hs (compF S natE) + hs (compF S negE) := by
  have h := hsum_congr S ((compF S natE).embDomain natE + (compF S negE).embDomain negE) fun n => by
    rw [SummableFamily.add_apply]
    rcases le_or_gt 0 n with hn | hn
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, by omega⟩
      rw [show (k : ℤ) = natE k from rfl, SummableFamily.embDomain_image,
        SummableFamily.embDomain_notin_range, add_zero]
      · rfl
      · rintro ⟨m, hm⟩; simp [negE, natE] at hm; omega
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -((k : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩
      rw [show -((k : ℤ) + 1) = negE k from rfl, SummableFamily.embDomain_image,
        SummableFamily.embDomain_notin_range, zero_add]
      · rfl
      · rintro ⟨m, hm⟩; simp [negE, natE] at hm; omega
  rw [h, hs_eq, SummableFamily.hsum_add, SummableFamily.hsum_embDomain, SummableFamily.hsum_embDomain]; rfl

/-- **the bridge**: `ι(ALser z) = (1 − z)·Σ_n (−1)^n q^{n(3n+1)/2}/(1 − zqⁿ)`. -/
theorem ALser_lam {z : ℂ} (hz : z ≠ 0) (hz1 : z ≠ 1) (hz3 : z ^ 3 ≠ 1) :
    ι1 (RankProof.ALser z) = mono 0 (1 - z) * hs (lamF z) := by
  rw [ι1_ALser, hs_split_Z (lamF z)]
  have h := hsum_congr (alF z) (mono 0 (1 - z) • (compF (lamF z) natE + (compF (lamF z) negE).embDomain succE))
    fun r => by
      simp only [SummableFamily.smul_apply, HahnSeries.of_symm_smul_of_eq_mul, SummableFamily.add_apply]
      rw [alF_pt hz hz1 hz3]
      congr 2
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · rw [SummableFamily.embDomain_notin_range, if_neg (by norm_num)]
        rintro ⟨m, hm⟩; simp [succE] at hm
      · obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
        rw [show m + 1 = succE m from rfl, SummableFamily.embDomain_image, if_pos (by simp [succE])]
        show lamF z (-((m + 1 : ℕ) : ℤ)) = lamF z (-((m : ℤ) + 1))
        push_cast; rfl
  rw [h, hs_eq, SummableFamily.hsum_smul, SummableFamily.hsum_add, SummableFamily.hsum_embDomain]; rfl

end Bridge


section RankBridge
open PowerSeries

/-- the three Appell–Lerch sums of `R(ζ;q)` (base `q³`, `t = q`). -/
noncomputable def Ai (z : ℂ) : Fin 3 → L
  | 0 => Ab h3 (a := 1) (β := -1) (by norm_num) (by norm_num) (z ^ 3) 1
  | 1 => Ab h3 (a := 0) (β := 0) (by norm_num) (by norm_num) (z ^ 3) 1
  | 2 => Ab h3 (a := -1) (β := 1) (by norm_num) (by norm_num) (z ^ 3) 1

lemma hs_lamF (z : ℂ) : hs (lamF z) =
    -mono 1 (z ^ 0) * Ai z 0 + -mono 0 (z ^ 1) * Ai z 1 + -mono (-1) (z ^ 2) * Ai z 2 := by
  simp only [lamF, Ai]
  rw [hs_eq, SummableFamily.hsum_add, SummableFamily.hsum_add, SummableFamily.hsum_smul,
    SummableFamily.hsum_smul, SummableFamily.hsum_smul, SummableFamily.hsum_equiv,
    SummableFamily.hsum_equiv, SummableFamily.hsum_equiv, ← hs_eq, ← hs_eq, ← hs_eq,
    ← Ab_eq_sum, ← Ab_eq_sum, ← Ab_eq_sum]

/-- **`(q;q)_∞ R(ζ;q)` as Appell–Lerch sums**: for `z ≠ 0`, `z ≠ 1`, `z³ ≠ 1`,
`(q)_∞ R(z;q) = (1−z) Σ_{i<3} (−z^i q^{1−i}) A(z³q^{1−i}, q^{i−1}; q³)` (in `ℂ((q))`). -/
theorem rank_bridge {z : ℂ} (hz : z ≠ 0) (hz1 : z ≠ 1) (hz3 : z ^ 3 ≠ 1) :
    ι1 (MockTheta5.JTP.ψC MockTheta5.JTP.qfacInf) * ι1 (CrankProof.Dser z z⁻¹) =
      mono 0 (1 - z) * (-mono 1 (z ^ 0) * Ai z 0 + -mono 0 (z ^ 1) * Ai z 1 + -mono (-1) (z ^ 2) * Ai z 2) := by
  rw [← map_mul, RankProof.rank_AL hz, ← mul_assoc, ← map_mul, Ring.mul_inverse_cancel _
    MockTheta5.JTP.isUnit_qfacInf, map_one, one_mul, ALser_lam hz hz1 hz3, hs_lamF]

end RankBridge

end ALz
