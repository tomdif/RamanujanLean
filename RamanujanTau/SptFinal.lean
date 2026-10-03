/-
# Andrews' spt congruences mod 5 and 7

`spt(n)` counts the smallest parts of all partitions of `n`. From `rank_sub_crank`,
`R(z) − C(z) = (1−z)(1−z⁻¹)·C(z)U(z)`, the series `S = C·U` has integer Laurent coefficients in `z` whose sum
is `spt(n)` (at `z = 1`, `C(1)U(1) = Σ_k q^k/((1−q^k)²(q^{k+1})_∞)`). At `z = ζ₅`, `n = 5m+4`, both the rank
and the crank sums vanish (Dyson/Atkin–Swinnerton-Dyer, Andrews–Garvan), so `[qⁿ]S(ζ₅) = 0`: the Laurent
coefficients grouped by exponent mod 5 are equal, and `5 ∣ spt(5m+4)`. Likewise mod 7 for `7m+5`.
-/
import RamanujanTau.SptSeries
import RamanujanTau.RankMod5
import RamanujanTau.ALRank7Main
import RamanujanTau.SptGF

set_option autoImplicit false

namespace CrankProof
open PowerSeries Finset
open MockTheta5.JTP (ω5 ω5_prim ω5_pow5)

/-! ## Integer relations among powers of a primitive 5th / 7th root -/

lemma cycZ5 (c : ℕ → ℤ) (h : ∑ k ∈ range 5, (c k : ℂ) * ω5 ^ k = 0) {k : ℕ} (hk : k < 4) : c k = c 4 := by
  set q : Polynomial ℚ := ∑ j ∈ range 4, Polynomial.C ((c j : ℚ) - c 4) * Polynomial.X ^ j with hq
  have hg := ω5_prim.geom_sum_eq_zero (by norm_num)
  have hev : Polynomial.aeval ω5 q = 0 := by
    simp only [hq, map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, eq_ratCast]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h hg ⊢
    push_cast
    linear_combination h - (c 4 : ℂ) * hg
  have hdvd : minpoly ℚ ω5 ∣ q := minpoly.dvd ℚ ω5 hev
  rw [← Polynomial.cyclotomic_eq_minpoly_rat ω5_prim (by norm_num)] at hdvd
  have hdeg : q.degree < (Polynomial.cyclotomic 5 ℚ).degree := by
    rw [Polynomial.degree_cyclotomic, Nat.totient_prime Nat.prime_five]
    refine lt_of_le_of_lt (b := ((3 : ℕ) : WithBot ℕ)) ?_ (by decide)
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]; compute_degree
    all_goals norm_num
  have hq0 := Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hdeg
  have ck := congrArg (Polynomial.coeff · k) hq0
  simp only [hq, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_range, if_pos hk, Polynomial.coeff_zero] at ck
  exact_mod_cast sub_eq_zero.mp ck

lemma cycZ7 (c : ℕ → ℤ) (h : ∑ k ∈ range 7, (c k : ℂ) * ω7 ^ k = 0) {k : ℕ} (hk : k < 6) : c k = c 6 := by
  set q : Polynomial ℚ := ∑ j ∈ range 6, Polynomial.C ((c j : ℚ) - c 6) * Polynomial.X ^ j with hq
  have hg := ω7_prim.geom_sum_eq_zero (by norm_num)
  have hev : Polynomial.aeval ω7 q = 0 := by
    simp only [hq, map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, eq_ratCast]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h hg ⊢
    push_cast
    linear_combination h - (c 6 : ℂ) * hg
  have hdvd : minpoly ℚ ω7 ∣ q := minpoly.dvd ℚ ω7 hev
  rw [← Polynomial.cyclotomic_eq_minpoly_rat ω7_prim (by norm_num)] at hdvd
  have hdeg : q.degree < (Polynomial.cyclotomic 7 ℚ).degree := by
    rw [Polynomial.degree_cyclotomic, Nat.totient_prime Nat.prime_seven]
    refine lt_of_le_of_lt (b := ((5 : ℕ) : WithBot ℕ)) ?_ (by decide)
    rw [hq]; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]; compute_degree
    all_goals norm_num
  have hq0 := Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hdeg
  have ck := congrArg (Polynomial.coeff · k) hq0
  simp only [hq, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_range, if_pos hk, Polynomial.coeff_zero] at ck
  exact_mod_cast sub_eq_zero.mp ck

/-! ## Grouping a Laurent polynomial's coefficients mod `p` -/

open LaurentPolynomial in
/-- the sum of the coefficients of `L` at exponents `≡ i (mod p)`. -/
noncomputable def lgrp (p : ℕ) (i : ℕ) (L : LaurentPolynomial ℤ) : ℤ :=
  Finsupp.sum L fun k c => if (k % p).toNat = i then c else 0

lemma lgrp_add (p i : ℕ) (L M : LaurentPolynomial ℤ) : lgrp p i (L + M) = lgrp p i L + lgrp p i M := by
  unfold lgrp
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by split_ifs <;> simp)

lemma lgrp_CT (p i : ℕ) (a : ℤ) (n : ℤ) :
    lgrp p i (LaurentPolynomial.C a * LaurentPolynomial.T n) = if (n % p).toNat = i then a else 0 := by
  unfold lgrp
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  exact Finsupp.sum_single_index (by simp)

/-- at a `p`-th root of unity, a Laurent polynomial is `Σ_{i<p} (grouped coefficient) uⁱ`. -/
lemma evU_group {p : ℕ} (hp : 0 < p) (u : ℂˣ) (hu : (u : ℂ) ^ p = 1) (L : LaurentPolynomial ℤ) :
    evU u L = ∑ i ∈ range p, (lgrp p i L : ℂ) * (u : ℂ) ^ i := by
  induction L using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, hP, hQ, ← sum_add_distrib]; simp_rw [lgrp_add]; push_cast; simp_rw [add_mul]
  | C_mul_T n a =>
    rw [map_mul, evU_C, evU_T]
    simp_rw [lgrp_CT]
    rw [sum_eq_single ((n % p).toNat) (fun b _ hb => by rw [if_neg (Ne.symm hb)]; simp)
      (fun h => absurd (mem_range.mpr (by have := Int.emod_lt_of_pos n (show (0:ℤ) < p by omega); omega)) h), if_pos rfl]
    congr 1
    have hu0 : (u : ℂ) ≠ 0 := u.ne_zero
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg n (by omega))]
    conv_lhs => rw [← Int.mul_ediv_add_emod n p]
    rw [zpow_add₀ hu0, zpow_mul, show ((p : ℤ)) = ((p : ℕ) : ℤ) from rfl, zpow_natCast, hu, one_zpow, one_mul]

lemma evU_one_group {p : ℕ} (hp : 0 < p) (L : LaurentPolynomial ℤ) :
    evU 1 L = ((∑ i ∈ range p, lgrp p i L : ℤ) : ℂ) := by
  rw [evU_group hp 1 (by simp) L]; push_cast; simp

/-! ## The Laurent lift of `S = C·U` -/

section Laurent
open LaurentPolynomial
local notation "ψ" => MockTheta5.JTP.ψC

/-- `(c q^s; q)_n` over `ℤ[z,z⁻¹]`. -/
noncomputable def pochL (c : LaurentPolynomial ℤ) (s n : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  ∏ i ∈ range n, (1 - PowerSeries.C c * X ^ (s + i))

noncomputable def pochInfL (c : LaurentPolynomial ℤ) (s : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  mk fun k => coeff k (pochL c s (k + 1))

lemma constantCoeff_pochL (c : LaurentPolynomial ℤ) {s : ℕ} (hs : 1 ≤ s) (n : ℕ) :
    constantCoeff (pochL c s n) = 1 := by
  rw [pochL, map_prod]
  refine prod_eq_one fun i _ => ?_
  rw [map_sub, map_one, map_mul, map_pow, constantCoeff_X, zero_pow (by omega), mul_zero, sub_zero]

lemma isUnit_pochL (c : LaurentPolynomial ℤ) {s : ℕ} (hs : 1 ≤ s) (n : ℕ) : IsUnit (pochL c s n) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_pochL c hs]; exact isUnit_one

lemma isUnit_pochInfL (c : LaurentPolynomial ℤ) {s : ℕ} (hs : 1 ≤ s) : IsUnit (pochInfL c s) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, pochInfL, coeff_mk,
    coeff_zero_eq_constantCoeff_apply, constantCoeff_pochL c hs]
  exact isUnit_one

noncomputable def CgfL : PowerSeries (LaurentPolynomial ℤ) :=
  pochInfL 1 1 * Ring.inverse (pochInfL (T 1) 1 * pochInfL (T (-1)) 1)

noncomputable def userL (j : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  if j = 0 then 0 else pochL (T 1) 1 (j - 1) * pochL (T (-1)) 1 (j - 1) * X ^ j * Ring.inverse (pochL 1 1 j)

noncomputable def UL : PowerSeries (LaurentPolynomial ℤ) := mk fun c => coeff c (∑ j ∈ range (c + 1), userL j)

lemma evU_T1 (u : ℂˣ) : evU u (T 1) = u := by rw [evU_T]; simp
lemma evU_Tm1 (u : ℂˣ) : evU u (T (-1)) = (u : ℂ)⁻¹ := by rw [evU_T]; simp

lemma map_pochL (u : ℂˣ) (c : LaurentPolynomial ℤ) (s n : ℕ) :
    PowerSeries.map (evU u) (pochL c s n) = poch (evU u c) s n := by
  rw [pochL, map_prod, poch]
  exact prod_congr rfl fun i _ => by simp [map_sub, map_mul, map_pow]

lemma map_pochInfL (u : ℂˣ) (c : LaurentPolynomial ℤ) (s : ℕ) :
    PowerSeries.map (evU u) (pochInfL c s) = pochInf (evU u c) s := by
  ext k; rw [coeff_map, pochInfL, coeff_mk, pochInf, coeff_mk, ← coeff_map, map_pochL]

lemma ψ_qfac (j : ℕ) : ψ (MockTheta5.Bailey.qfac j) = poch 1 1 j := by
  rw [MockTheta5.Bailey.qfac, map_prod, poch]
  exact prod_congr rfl fun i _ => by simp [map_sub, map_pow, add_comm]

lemma map_CgfL (u : ℂˣ) : PowerSeries.map (evU u) CgfL = RankProof.Cgf u := by
  rw [CgfL, map_mul, map_inverse _ ((isUnit_pochInfL _ le_rfl).mul (isUnit_pochInfL _ le_rfl)), map_mul,
    map_pochInfL, map_pochInfL, map_pochInfL, evU_T1, evU_Tm1, map_one, RankProof.Cgf]

lemma map_UL (u : ℂˣ) : PowerSeries.map (evU u) UL = RankProof.User u := by
  ext c
  rw [coeff_map, UL, coeff_mk, RankProof.User, coeff_mk, ← coeff_map, map_sum]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [userL, RankProof.user]
  split_ifs
  · simp
  · rw [map_mul, map_mul, map_mul, map_pow, map_X, map_inverse _ (isUnit_pochL _ le_rfl _), map_pochL, map_pochL,
      map_pochL, evU_T1, evU_Tm1, map_one, map_inverse ψ (MockTheta5.Bailey.isUnit_qfac j), ψ_qfac]

lemma evU_coeff_S (u : ℂˣ) (m : ℕ) :
    evU u (coeff m (CgfL * UL)) = coeff m (RankProof.Cgf u * RankProof.User u) := by
  rw [← coeff_map, map_mul, map_CgfL, map_UL]

end Laurent

/-! ## The congruences -/

/-- `spt(n)`: the total number of appearances of the smallest part over all partitions of `n`
(`count_k λ` for the `k` with every part `≥ k`; only the smallest part contributes). -/
noncomputable def spt (n : ℕ) : ℕ :=
  ∑ l : n.Partition, ∑ k ∈ range (n + 1), if ∀ j ∈ l.parts, k ≤ j then l.parts.count k else 0

section SptGF
local notation "ψ" => MockTheta5.JTP.ψC
open MockTheta5.Bailey MockTheta5.JTP

lemma Cgf_one : RankProof.Cgf 1 = ψ (Ring.inverse qfacInf) := by
  obtain ⟨u, hu⟩ := isUnit_qfacInf.map ψ
  rw [RankProof.Cgf, inv_one, pochInf_one_eq, map_inverse ψ isUnit_qfacInf, ← hu, ← Units.val_mul,
    Ring.inverse_unit, Ring.inverse_unit]
  simp [mul_inv_rev]

lemma user_one {k : ℕ} (hk : 1 ≤ k) :
    RankProof.user 1 k = ψ (qfac (k - 1) * X ^ k * Ring.inverse (1 - X ^ k)) := by
  have hu1 : IsUnit (1 - X ^ k : PowerSeries ℤ) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp [zero_pow (by omega : k ≠ 0)]
  rw [RankProof.user, if_neg (by omega), inv_one, ← ψ_qfac,
    show qfac k = qfac (k - 1) * (1 - X ^ k) by
      rw [show k = k - 1 + 1 by omega, qfac, prod_range_succ, ← qfac, show k - 1 + 1 - 1 = k - 1 by omega]]
  rw [Ring.mul_inverse_rev']
  · simp only [map_mul, map_pow, PowerSeries.map_X]
    have h1 : ψ (qfac (k - 1)) * ψ (Ring.inverse (qfac (k - 1))) = 1 := by
      rw [← map_mul, Ring.mul_inverse_cancel _ (isUnit_qfac _), map_one]
    linear_combination (ψ (qfac (k - 1)) * X ^ k * ψ (Ring.inverse (1 - X ^ k))) * h1
  · exact Commute.all _ _

lemma User_dvd (z : ℂ) (m : ℕ) :
    (X : PowerSeries ℂ) ^ (m + 1) ∣ RankProof.User z - ∑ k ∈ range (m + 1), RankProof.user z k := by
  rw [PowerSeries.X_pow_dvd_iff]; intro i hi
  rw [map_sub, RankProof.User, coeff_mk, sub_eq_zero, map_sum, map_sum]
  refine sum_subset (range_subset_range.mpr (by omega)) fun k _ hk => ?_
  simp only [mem_range, not_lt] at hk
  rw [RankProof.user, if_neg (by omega), show poch z 1 (k - 1) * poch z⁻¹ 1 (k - 1) * X ^ k
    * ψ (Ring.inverse (qfac k)) = X ^ k * (poch z 1 (k - 1) * poch z⁻¹ 1 (k - 1) * ψ (Ring.inverse (qfac k))) by ring]
  exact coeffC_Xpow_zero (by omega) _

lemma count_zero_parts {n : ℕ} (l : n.Partition) : l.parts.count 0 = 0 :=
  Multiset.count_eq_zero.mpr fun h => (l.parts_pos h).ne' rfl

/-- **the spt generating function**: `[qᵐ] C(1)U(1) = spt(m)`. -/
theorem spt_gf (m : ℕ) : coeff m (RankProof.Cgf 1 * RankProof.User 1) = (spt m : ℂ) := by
  rw [coeffC_congr (User_dvd 1 m), mul_sum, map_sum]
  have hk : ∀ k ∈ range (m + 1), coeff m (RankProof.Cgf 1 * RankProof.user 1 k)
      = ((∑ l : m.Partition, if ∀ j ∈ l.parts, k ≤ j then (l.parts.count k : ℤ) else 0 : ℤ) : ℂ) := by
    intro k _
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · simp [RankProof.user, count_zero_parts]
    · rw [Cgf_one, user_one hk1, ← map_mul, PowerSeries.coeff_map, ← coeff_wf_diff k m, ← map_sub,
        genFun_wf_diff hk1, eq_intCast]
      congr 2; ring
  rw [sum_congr rfl hk, spt]
  push_cast
  rw [sum_comm]

end SptGF

lemma S_at_root {z : ℂ} (hz : z ≠ 0) (hz1 : (1 - z) * (1 - z⁻¹) ≠ 0) {m : ℕ} (hm : 2 ≤ m)
    (hR : ∑ l : m.Partition, z ^ rank l = 0) (hC : ∑ l : m.Partition, z ^ crank l = 0) :
    coeff m (RankProof.Cgf z * RankProof.User z) = 0 := by
  have h := congrArg (coeff m) (RankProof.rank_sub_crank hz)
  rw [map_sub, coeff_C_mul, ← rank_durfee hz, RankProof.Cgf, ← crank_generating_function hz hm, hR, hC,
    sub_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hz1

/-- **Andrews (2008): `spt(5n+4) ≡ 0 (mod 5)`.** -/
theorem spt_mod5 (n : ℕ) : 5 ∣ spt (5 * n + 4) := by
  set m := 5 * n + 4
  set u : ℂˣ := Units.mk0 ω5 (ω5_prim.ne_zero (by norm_num))
  have hu5 : (u : ℂ) ^ 5 = 1 := ω5_pow5
  have hS := S_at_root (z := ω5) (ω5_prim.ne_zero (by norm_num)) ?_ (by omega) (rank_sum_root_zero n)
    (crank_sum_root_zero n)
  · rw [← show ((u : ℂ)) = ω5 from rfl] at hS
    rw [← evU_coeff_S u m, evU_group (by norm_num) u hu5] at hS
    set L := coeff m (CgfL * UL)
    have e : ∀ k < 4, lgrp 5 k L = lgrp 5 4 L := fun k hk => cycZ5 (fun i => lgrp 5 i L) hS hk
    have h1 := evU_one_group (p := 5) (by norm_num) L
    rw [evU_coeff_S, show ((1 : ℂˣ) : ℂ) = 1 from rfl] at h1
    have h2 := spt_gf m
    rw [h2] at h1
    have h3 : (spt m : ℤ) = ∑ i ∈ range 5, lgrp 5 i L := by exact_mod_cast h1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h3
    rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num)] at h3
    have : (5 : ℤ) ∣ (spt m : ℤ) := ⟨lgrp 5 4 L, by rw [h3]; ring⟩
    exact_mod_cast this
  · have h1 : ω5 ≠ 1 := ω5_prim.ne_one (by norm_num)
    have h0 : ω5 ≠ 0 := ω5_prim.ne_zero (by norm_num)
    refine mul_ne_zero (sub_ne_zero.mpr (Ne.symm h1)) (sub_ne_zero.mpr ?_)
    intro h; apply h1; rw [eq_comm, inv_eq_one] at h; exact h

/-- **Andrews (2008): `spt(7n+5) ≡ 0 (mod 7)`.** -/
theorem spt_mod7 (n : ℕ) : 7 ∣ spt (7 * n + 5) := by
  set m := 7 * n + 5
  set u : ℂˣ := Units.mk0 ω7 ω7_ne
  have hu7 : (u : ℂ) ^ 7 = 1 := ω7_pow7
  have hS := S_at_root (z := ω7) ω7_ne ?_ (by omega) (rank_sum_root7_zero n) (crank_sum_root7_zero n)
  · rw [← show ((u : ℂ)) = ω7 from rfl] at hS
    rw [← evU_coeff_S u m, evU_group (by norm_num) u hu7] at hS
    set L := coeff m (CgfL * UL)
    have e : ∀ k < 6, lgrp 7 k L = lgrp 7 6 L := fun k hk => cycZ7 (fun i => lgrp 7 i L) hS hk
    have h1 := evU_one_group (p := 7) (by norm_num) L
    rw [evU_coeff_S, show ((1 : ℂˣ) : ℂ) = 1 from rfl, spt_gf m] at h1
    have h3 : (spt m : ℤ) = ∑ i ∈ range 7, lgrp 7 i L := by exact_mod_cast h1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h3
    rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num), e 4 (by norm_num),
      e 5 (by norm_num)] at h3
    have : (7 : ℤ) ∣ (spt m : ℤ) := ⟨lgrp 7 6 L, by rw [h3]; ring⟩
    exact_mod_cast this
  · have h1 : ω7 ≠ 1 := ω7_prim.ne_one (by norm_num)
    refine mul_ne_zero (sub_ne_zero.mpr (Ne.symm h1)) (sub_ne_zero.mpr ?_)
    intro h; apply h1; rw [eq_comm, inv_eq_one] at h; exact h

end CrankProof
