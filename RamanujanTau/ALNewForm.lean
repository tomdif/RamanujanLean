/-
# The `z = x²` Appell–Lerch form of the rank generating function at a 7th root of unity

`R(ζ;q) θ(ζ²;q³) = (1−ζ) [θ(ζ²;q³) − A(q²ζ⁴, ζ²; q³) − ζ⁶ A(q ζ⁴, ζ²; q³)]`, derived from `rank_bridge`
by inversion, `x`/`z`-shifts, two changes of `z` per sum, and one five-term theta identity
(five `weierstrass0` instances).
-/
import RamanujanTau.ALWeier0
import RamanujanTau.ALNormal
import RamanujanTau.RankMod7a

set_option autoImplicit false

namespace ALz
open HahnSeries Finset

section Aux
variable {N : ℕ} (hN : 1 ≤ N)
include hN

/-- `θ(c) ≠ 0` for a constant `c ≠ 1` (its `t⁰` coefficient is `1 − c`). -/
theorem θ_ne0 {c : ℂ} (hc : c ≠ 1) : θ hN 0 c ≠ 0 := by
  intro h
  have hcoef := congrArg (fun f : L => f.coeff 0) h
  simp only [θ, coeff_zero] at hcoef
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hE : ∀ k : ℤ, thE N 0 k = N * c2 k := fun k => by unfold thE; ring
  have hpos : ∀ k : ℤ, k ≠ 0 → k ≠ 1 → 0 < (N : ℤ) * c2 k := by
    intro k h0 h1
    have h2 := two_c2 k
    have : 0 < k * (k - 1) := by
      rcases lt_or_gt_of_ne h0 with h | h
      · nlinarith
      · have : 2 ≤ k := by omega
        nlinarith
    have : 0 < c2 k := by omega
    positivity
  rw [thF, monoFam_coeff, finsum_eq_sum_of_support_subset (s := {0, 1})] at hcoef
  · rw [Finset.sum_pair (by norm_num)] at hcoef
    simp only [hE, c2, thC] at hcoef
    norm_num at hcoef
    exact hc (by linear_combination -hcoef)
  · intro k hk
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hk
    obtain ⟨h1, -⟩ := hk
    by_contra hk'
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or] at hk'
    have := hpos k hk'.1 hk'.2
    rw [hE] at h1; omega

omit hN in
theorem mono_ne_one_of {e : ℤ} {c : ℂ} (h : e ≠ 0 ∨ c ≠ 1) : mono e c ≠ 1 := by
  intro h1
  rcases h with h | h
  · have := congrArg (fun f : L => f.coeff e) h1
    simp [mono, HahnSeries.coeff_one, h] at this
    by_cases hc : c = 0
    · subst hc
      have := congrArg (fun f : L => f.coeff 0) h1
      simp [mono] at this
    · exact hc this
  · have := congrArg (fun f : L => f.coeff 0) h1
    by_cases he : e = 0
    · subst he; simp [mono] at this; exact h this
    · simp [mono, Ne.symm he] at this

end Aux

section Pent3
open RankProof (Pinf Pfin Pfin_succ X_pow_dvd_Pfin_sub X_pow_dvd_Pinf_sub Pinf_ext)
open PowerSeries

lemma Pfin_split3 : ∀ N, Pfin 1 1 (3 * N) = ∏ r ∈ range 3, Pfin (r + 1) 3 N
  | 0 => by simp [Pfin]
  | N + 1 => by
    rw [show 3 * (N + 1) = 3 * N + 3 by ring, Pfin, prod_range_add, ← Pfin, Pfin_split3 N]
    simp only [Pfin_succ, prod_mul_distrib]
    congr 1
    refine prod_congr rfl fun r _ => ?_
    congr 2; ring

/-- `(q;q)_∞ = (q;q³)_∞ (q²;q³)_∞ (q³;q³)_∞`. -/
theorem Pinf_split3 : Pinf 1 1 = ∏ r ∈ range 3, Pinf (r + 1) 3 := by
  symm
  refine Pinf_ext le_rfl le_rfl fun N => ?_
  have h1 : (X : PowerSeries ℤ) ^ (N + 1) ∣ ∏ r ∈ range 3, Pinf (r + 1) 3 - ∏ r ∈ range 3, Pfin (r + 1) 3 N :=
    CrankProof.dvd_sub_prod _ _ fun r _ => X_pow_dvd_Pinf_sub (r + 1) 3 (by omega) (by norm_num) N
  have h2 := X_pow_dvd_Pfin_sub 1 1 N le_rfl le_rfl (3 * N) (by omega)
  rw [Pfin_split3] at h2
  have := dvd_add h1 h2
  rwa [sub_add_sub_cancel] at this

/-- **Euler**: `(q;q)_∞ = θ(q; q³)` in `ℂ((t))`. -/
theorem qfac_eq_θ3 : ι1 (MockTheta5.JTP.ψC MockTheta5.JTP.qfacInf) = θ (N := 3) (by norm_num) 1 1 := by
  have hsplit : MockTheta5.JTP.qfacInf = RankProof.thetaS 3 1 := by
    rw [← RankProof.Pinf_one_one, Pinf_split3, ← RankProof.jtp_ab 3 1 le_rfl (by norm_num)]
    simp [prod_range_succ]
  rw [hsplit, CrankProof.thetaS_eq_thL le_rfl (by norm_num)]
  ext n
  rcases lt_or_ge n 0 with hn | hn
  · rw [ι1_coeff_neg _ hn, θ, thF, monoFam_coeff_zero]
    intro k hk
    have := two_c2 k
    unfold thE at hk
    have hkk : 0 ≤ k * (k - 1) := by rcases le_or_gt k 0 with h | h <;> nlinarith
    push_cast at hk; nlinarith
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
    rw [ι1_coeff_nat, CrankProof.thL, CrankProof.coeff_lat _ (CrankProof.proper_expo (by norm_num) (by norm_num)),
      θ, thF, monoFam_coeff]
    have hfin : (Function.support fun k : ℤ =>
        if CrankProof.expo 3 1 k = m then (-(1 : ℂ)) ^ k else 0).Finite :=
      (CrankProof.proper_expo (a := 3) (b := 1) (by norm_num) (by norm_num) m).subset fun k hk => by
        simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hk
        simp only [Set.mem_setOf_eq]; omega
    rw [tsum_eq_finsum hfin]
    refine finsum_congr fun k => ?_
    have h2 := CrankProof.two_triE k
    have h3 := two_c2 k
    have hnn := CrankProof.expo_nonneg (a := 3) (b := 1) (by norm_num) k
    have hk : ((CrankProof.expo 3 1 k : ℕ) : ℤ) = thE 3 1 k := by
      unfold CrankProof.expo thE
      rw [Int.toNat_of_nonneg hnn]; push_cast; linarith
    simp only [thC, one_zpow, mul_one]
    by_cases h : thE 3 1 k = (m : ℤ)
    · rw [if_pos h, if_pos (by exact_mod_cast hk.trans h)]
    · rw [if_neg h, if_neg (fun h' => h (by rw [← hk]; exact_mod_cast h'))]
end Pent3

section Norm3
/-! normal forms of `θ(c q^e; q³)` for `e ∈ {−3,−2,−1,2}` and `θ(c⁻¹)` at `e = 0` -/

theorem θ3_two {c : ℂ} (hc : c ≠ 0) : θ h3 2 c = θ h3 1 c⁻¹ := by
  have h := θ_reflect h3 1 (inv_ne_zero hc)
  rw [inv_inv] at h
  rw [← h]; norm_num

theorem θ3_m1 {c : ℂ} (hc : c ≠ 0) : θ h3 (-1) c = -mono (-1) c * θ h3 1 c⁻¹ := by
  have h := θ_inv h3 1 (inv_ne_zero hc)
  rw [inv_inv] at h
  exact h

theorem θ3_m2 {c : ℂ} (hc : c ≠ 0) : θ h3 (-2) c = -mono (-2) c * θ h3 1 c := by
  have h := θ_inv h3 2 (inv_ne_zero hc)
  rw [inv_inv, θ3_two (inv_ne_zero hc), inv_inv] at h
  exact h

theorem θ3_m3 {c : ℂ} (hc : c ≠ 0) : θ h3 (-3) c = mono (-3) (-c) * θ h3 0 c := by
  have h := θ_qshift h3 0 hc (-1)
  rw [show (0 : ℤ) + (3 : ℕ) * (-1) = -3 by norm_num] at h
  rw [h]; congr 2
  simp

theorem θ3_0inv {c : ℂ} (hc : c ≠ 0) : θ h3 0 c⁻¹ = -mono 0 c⁻¹ * θ h3 0 c := by
  have h := θ_inv h3 0 hc
  rw [neg_zero] at h
  exact h

end Norm3

section Subst
variable {ζ : ℂ} (h7 : ζ ^ 7 = 1) (hζ : ζ ≠ 1)
include h7 hζ

omit hζ in
lemma zeta_ne0 : ζ ≠ 0 := by
  rintro rfl; norm_num at h7

/-- `ζ^k ≠ 1` for `0 < k < 7` (7 is prime). -/
lemma zeta_pow_ne {k : ℕ} (hk0 : 0 < k) (hk : k < 7) : ζ ^ k ≠ 1 := by
  intro h
  apply hζ
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, a * k = 1 + 7 * b := by
    interval_cases k
    · exact ⟨1, 0, rfl⟩
    · exact ⟨4, 1, rfl⟩
    · exact ⟨5, 2, rfl⟩
    · exact ⟨2, 1, rfl⟩
    · exact ⟨3, 2, rfl⟩
    · exact ⟨6, 5, rfl⟩
  calc ζ = ζ ^ (1 + 7 * b) := by rw [_root_.pow_add, pow_mul, h7, one_pow, pow_one, mul_one]
    _ = (ζ ^ k) ^ a := by rw [← hab, ← pow_mul, mul_comm]
    _ = 1 := by rw [h, one_pow]

omit hζ in
lemma zeta_inv (k : ℕ) (hk : k ≤ 7) : (ζ ^ k)⁻¹ = ζ ^ (7 - k) := by
  exact inv_eq_of_mul_eq_one_right (by rw [← _root_.pow_add, Nat.add_sub_cancel' hk, h7])

omit hζ in
lemma zeta_mul (a b : ℕ) : ζ ^ a * ζ ^ b = ζ ^ ((a + b) % 7) := by
  conv_lhs => rw [← _root_.pow_add, ← Nat.mod_add_div (a + b) 7, _root_.pow_add, pow_mul, h7, one_pow, mul_one]

/-- the substitution facts behind the `z = x²` form. -/
theorem nf_facts :
    θ h3 0 (ζ ^ 3) * Ab h3 (a := 0) (β := 0) (by norm_num) (by norm_num) (ζ ^ 3) 1 = hs (kF h3 0) ∧
    Ab h3 (a := 1) (β := 0) (by norm_num) (by norm_num) (ζ ^ 4) (ζ ^ 2) =
      -mono (-1) (ζ ^ 5) * Ab h3 (a := -1) (β := 0) (by norm_num) (by norm_num) (ζ ^ 3) (ζ ^ 5) ∧
    Ab h3 (a := -2) (β := 0) (by norm_num) (by norm_num) (ζ ^ 3) (ζ ^ 5) =
      -mono 2 (ζ ^ 2) * Ab h3 (a := 2) (β := 0) (by norm_num) (by norm_num) (ζ ^ 4) (ζ ^ 2) := by
  have h0 := zeta_ne0 h7
  refine ⟨?_, ?_, ?_⟩
  · exact kappa_eq h3 (a := 0) (by norm_num) (by norm_num) (pow_ne_zero _ h0)
      (mono_ne_one_of (Or.inr (zeta_pow_ne h7 hζ (by norm_num) (by norm_num))))
  · have h := Ab_inv h3 (a := -1) (β := 0) (by norm_num) (by norm_num) (pow_ne_zero 3 h0) (pow_ne_zero 5 h0)
      (mono_ne_one_of (Or.inl (by norm_num)))
    rw [zeta_inv h7 3 (by norm_num), zeta_inv h7 5 (by norm_num)] at h
    rw [show ζ ^ 3 * ζ ^ (7 - 5) = ζ ^ 5 by rw [zeta_mul h7]] at h
    convert h using 2
  · have h := Ab_inv h3 (a := 2) (β := 0) (by norm_num) (by norm_num) (pow_ne_zero 4 h0) (pow_ne_zero 2 h0)
      (mono_ne_one_of (Or.inl (by norm_num)))
    rw [zeta_inv h7 4 (by norm_num), zeta_inv h7 2 (by norm_num)] at h
    rw [show ζ ^ 4 * ζ ^ (7 - 2) = ζ ^ 2 by rw [zeta_mul h7]] at h
    convert h using 2


theorem nf_facts2 :
    Ab h3 (a := 1) (β := -3) (by norm_num) (by norm_num) (ζ ^ 3) (ζ ^ 5) =
      θ h3 (-3) (ζ ^ 5) + mono (-5) ζ * Ab h3 (a := -2) (β := 0) (by norm_num) (by norm_num) (ζ ^ 3) (ζ ^ 5) ∧
    Ab h3 (a := 1) (β := 0) (by norm_num) (by norm_num) (ζ ^ 3) (ζ ^ 5) =
      -mono 3 (ζ ^ 2) * Ab h3 (a := 1) (β := -3) (by norm_num) (by norm_num) (ζ ^ 3) (ζ ^ 5) ∧
    Ab h3 (a := 1) (β := 0) (by norm_num) (by norm_num) (ζ ^ 3) (ζ ^ 5) =
      θ h3 0 (ζ ^ 5) * Ab h3 (a := 1) (β := 1) (by norm_num) (by norm_num) (ζ ^ 3) 1 / θ h3 1 1 -
        mono 1 1 * hs (kF h3 0) * θ h3 (-1) (ζ ^ 5) * θ h3 2 ζ /
          (θ h3 1 1 * θ h3 2 (ζ ^ 3) * θ h3 1 ζ) ∧
    Ab h3 (a := 1) (β := -1) (by norm_num) (by norm_num) (ζ ^ 3) 1 =
      θ h3 (-1) 1 * Ab h3 (a := 1) (β := 1) (by norm_num) (by norm_num) (ζ ^ 3) 1 / θ h3 1 1 -
        mono 1 1 * hs (kF h3 0) * θ h3 (-2) 1 * θ h3 1 (ζ ^ 3) /
          (θ h3 1 1 * θ h3 2 (ζ ^ 3) * θ h3 0 (ζ ^ 3)) ∧
    Ab h3 (a := -1) (β := 0) (by norm_num) (by norm_num) (ζ ^ 3) (ζ ^ 5) =
      θ h3 0 (ζ ^ 5) * Ab h3 (a := -1) (β := 2) (by norm_num) (by norm_num) (ζ ^ 3) 1 / θ h3 2 1 -
        mono 2 1 * hs (kF h3 0) * θ h3 (-2) (ζ ^ 5) * θ h3 1 ζ /
          (θ h3 2 1 * θ h3 1 (ζ ^ 3) * θ h3 (-1) ζ) ∧
    Ab h3 (a := -1) (β := 1) (by norm_num) (by norm_num) (ζ ^ 3) 1 =
      θ h3 1 1 * Ab h3 (a := -1) (β := 2) (by norm_num) (by norm_num) (ζ ^ 3) 1 / θ h3 2 1 -
        mono 2 1 * hs (kF h3 0) * θ h3 (-1) 1 * θ h3 2 (ζ ^ 3) /
          (θ h3 2 1 * θ h3 1 (ζ ^ 3) * θ h3 0 (ζ ^ 3)) := by
  have h0 := zeta_ne0 h7
  have hz3 : ζ ^ 3 ≠ 1 := zeta_pow_ne h7 hζ (by norm_num) (by norm_num)
  have e35 : ζ ^ 3 * ζ ^ 5 = ζ := by rw [zeta_mul h7]; norm_num
  have i5 : (ζ ^ 5)⁻¹ = ζ ^ 2 := by rw [zeta_inv h7 5 (by norm_num)]
  have hm1 : θ h3 (-1) ζ ≠ 0 := by
    have := θ_inv h3 1 (inv_ne_zero h0)
    rw [inv_inv] at this
    rw [show (-1 : ℤ) = -(1 : ℤ) from rfl, this]
    exact mul_ne_zero (neg_ne_zero.mpr (by simp [mono, h0])) (θ_ne h3 (by norm_num) (by norm_num) _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have r := Ab_xshift h3 (a := -2) (β := 0) (by norm_num) (by norm_num) (pow_ne_zero 3 h0) (pow_ne_zero 5 h0)
      (fun r => mono_ne_one_of (Or.inl (by push_cast; omega)))
    rw [e35] at r
    convert r using 2
  · have r := Ab_zshift h3 (a := 1) (β := -3) (by norm_num) (by norm_num) (pow_ne_zero 3 h0) (pow_ne_zero 5 h0)
    rw [i5] at r
    convert r using 3
  · have r := coz_solve h3 (a := 1) (b₀ := 1) (b₁ := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (pow_ne_zero 3 h0) one_ne_zero (pow_ne_zero 5 h0)
      (mono_ne_one_of (Or.inl (by norm_num))) (mono_ne_one_of (Or.inl (by norm_num)))
      (θ_ne h3 (by norm_num) (by norm_num) _)
    rw [show ζ ^ 3 * 1 * ζ ^ 5 = ζ by rw [mul_one, e35], e35] at r
    norm_num at r
    exact r
  · have r := coz_solve h3 (a := 1) (b₀ := 1) (b₁ := -1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (pow_ne_zero 3 h0) one_ne_zero one_ne_zero
      (mono_ne_one_of (Or.inl (by norm_num))) (mono_ne_one_of (Or.inr (by simpa using hz3)))
      (by norm_num; exact θ_ne0 h3 hz3)
    norm_num at r
    exact r
  · have r := coz_solve h3 (a := -1) (b₀ := 2) (b₁ := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (pow_ne_zero 3 h0) one_ne_zero (pow_ne_zero 5 h0)
      (mono_ne_one_of (Or.inl (by norm_num))) (mono_ne_one_of (Or.inl (by norm_num)))
      (by rw [e35]; norm_num; exact hm1)
    rw [show ζ ^ 3 * 1 * ζ ^ 5 = ζ by rw [mul_one, e35], e35] at r
    norm_num at r
    exact r
  · have r := coz_solve h3 (a := -1) (b₀ := 2) (b₁ := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (pow_ne_zero 3 h0) one_ne_zero one_ne_zero
      (mono_ne_one_of (Or.inl (by norm_num))) (mono_ne_one_of (Or.inr (by simpa using hz3)))
      (by norm_num; exact θ_ne0 h3 hz3)
    norm_num at r
    exact r

omit hζ in
lemma zeta_pow_mod (n : ℕ) : ζ ^ n = ζ ^ (n % 7) := by
  conv_lhs => rw [← Nat.mod_add_div n 7, _root_.pow_add, pow_mul, h7, one_pow, mul_one]

lemma zeta_pow_ne' {a b : ℕ} (hab : a < b) (hb : b < 7) : ζ ^ a ≠ ζ ^ b := by
  intro h
  have h0 := zeta_ne0 h7
  apply zeta_pow_ne h7 hζ (k := b - a) (by omega) (by omega)
  have : ζ ^ b = ζ ^ a * ζ ^ (b - a) := by rw [← _root_.pow_add, Nat.add_sub_cancel' hab.le]
  rw [h] at this
  exact (mul_eq_left₀ (pow_ne_zero b h0)).mp this.symm

omit hζ in
lemma θ0_inv' (k : ℕ) (hk : 3 < k) (hk7 : k < 7) :
    θ h3 0 (ζ ^ k) = -mono 0 (ζ ^ k) * θ h3 0 (ζ ^ (7 - k)) := by
  have h0 := zeta_ne0 h7
  have h := θ3_0inv (pow_ne_zero (7 - k) h0)
  rw [zeta_inv h7 (7 - k) (by omega), Nat.sub_sub_self (by omega)] at h
  exact h

omit h7 hζ in
lemma mono_zeta (e : ℤ) (k : ℕ) : mono e (ζ ^ k) = mono e 1 * mono 0 ζ ^ k := by
  rw [mono, mono, mono, single_pow, single_mul_single]; simp

/-- **the five-term theta identity** behind the `z = x²` form (five `weierstrass0` instances). -/
theorem nf_theta :
    θ h3 0 (ζ ^ 2) * θ h3 1 (ζ ^ 1) * θ h3 1 (ζ ^ 3) ^ 2 * θ h3 1 (ζ ^ 6)
      + mono 0 (ζ ^ 1) * θ h3 0 (ζ ^ 2) * θ h3 1 (ζ ^ 1) * θ h3 1 (ζ ^ 3) * θ h3 1 (ζ ^ 4) * θ h3 1 (ζ ^ 6)
      + mono 0 (ζ ^ 2) * θ h3 0 (ζ ^ 2) * θ h3 1 (ζ ^ 1) * θ h3 1 (ζ ^ 4) ^ 2 * θ h3 1 (ζ ^ 6)
      - mono 0 (ζ ^ 1) * θ h3 0 (ζ ^ 3) * θ h3 1 (ζ ^ 1) ^ 2 * θ h3 1 (ζ ^ 4) * θ h3 1 (ζ ^ 5)
      - θ h3 0 (ζ ^ 3) * θ h3 1 (ζ ^ 2) * θ h3 1 (ζ ^ 3) * θ h3 1 (ζ ^ 6) ^ 2 = 0 := by
  have h0 := zeta_ne0 h7
  have hp : ∀ k : ℕ, ζ ^ k ≠ 0 := fun k => pow_ne_zero k h0
  have hm : ∀ k : ℕ, 0 < k → k < 7 → ζ ^ k ≠ 1 := fun k a b => zeta_pow_ne h7 hζ a b
  have w0 := weierstrass0 h3 (by' := 1) (bx := 1) (cy := ζ ^ 1) (cu := ζ ^ 0) (cv := ζ ^ 2) (cx := ζ ^ 0)
    (hp 1) (hp 0) (hp 2) (hp 0) (zeta_pow_ne' h7 hζ (by norm_num) (by norm_num))
    (by rw [zeta_mul h7]; exact hm _ (by norm_num) (by norm_num))
  have w1 := weierstrass0 h3 (by' := 1) (bx := 1) (cy := ζ ^ 2) (cu := ζ ^ 1) (cv := ζ ^ 2) (cx := ζ ^ 0)
    (hp 2) (hp 1) (hp 2) (hp 0) (zeta_pow_ne' h7 hζ (by norm_num) (by norm_num))
    (by rw [zeta_mul h7]; exact hm _ (by norm_num) (by norm_num))
  have w2 := weierstrass0 h3 (by' := 1) (bx := 1) (cy := ζ ^ 6) (cu := ζ ^ 0) (cv := ζ ^ 2) (cx := ζ ^ 0)
    (hp 6) (hp 0) (hp 2) (hp 0) (zeta_pow_ne' h7 hζ (by norm_num) (by norm_num))
    (by rw [zeta_mul h7]; exact hm _ (by norm_num) (by norm_num))
  have w3 := weierstrass0 h3 (by' := 1) (bx := 1) (cy := ζ ^ 6) (cu := ζ ^ 1) (cv := ζ ^ 2) (cx := ζ ^ 1)
    (hp 6) (hp 1) (hp 2) (hp 1) (zeta_pow_ne' h7 hζ (by norm_num) (by norm_num))
    (by rw [zeta_mul h7]; exact hm _ (by norm_num) (by norm_num))
  have w4 := weierstrass0 h3 (by' := 1) (bx := 1) (cy := ζ ^ 2) (cu := ζ ^ 0) (cv := ζ ^ 2) (cx := ζ ^ 1)
    (hp 2) (hp 0) (hp 2) (hp 1) (zeta_pow_ne' h7 hζ (by norm_num) (by norm_num))
    (by rw [zeta_mul h7]; exact hm _ (by norm_num) (by norm_num))
  simp only [zeta_inv h7 _ (by norm_num : 0 ≤ 7), zeta_inv h7 _ (by norm_num : 1 ≤ 7), zeta_inv h7 _ (by norm_num : 2 ≤ 7),
    zeta_inv h7 _ (by norm_num : 6 ≤ 7), zeta_mul h7, Nat.reduceAdd, Nat.reduceMod, Nat.reduceSub, Int.reduceAdd,
    Int.reduceSub, Int.reduceNeg] at w0 w1 w2 w3 w4
  simp only [θ3_two (hp _), θ3_m1 (hp _), θ0_inv' h7 5 (by norm_num) (by norm_num),
    θ0_inv' h7 6 (by norm_num) (by norm_num)] at w0 w1 w2 w3 w4
  simp only [zeta_inv h7 _ (by norm_num : 0 ≤ 7), zeta_inv h7 _ (by norm_num : 1 ≤ 7), zeta_inv h7 _ (by norm_num : 2 ≤ 7),
    zeta_inv h7 _ (by norm_num : 3 ≤ 7), zeta_inv h7 _ (by norm_num : 4 ≤ 7), zeta_inv h7 _ (by norm_num : 5 ≤ 7),
    zeta_inv h7 _ (by norm_num : 6 ≤ 7), Nat.reduceSub] at w0 w1 w2 w3 w4
  have z7 : ζ ^ 7 = ζ ^ 0 := by rw [h7, pow_zero]
  rw [z7] at w3
  have t01 : θ h3 0 (ζ ^ 1) ≠ 0 := θ_ne0 h3 (hm 1 (by norm_num) (by norm_num))
  have t02 : θ h3 0 (ζ ^ 2) ≠ 0 := θ_ne0 h3 (hm 2 (by norm_num) (by norm_num))
  have t10 : θ h3 1 (ζ ^ 0) ≠ 0 := θ_ne h3 (by norm_num) (by norm_num) _
  have t01' : θ h3 0 ζ ≠ 0 := by simpa using t01
  have t10' : θ h3 1 1 ≠ 0 := θ_ne h3 (by norm_num) (by norm_num) _
  linear_combination (norm := skip) (mono 0 (ζ ^ 4) * (θ h3 0 (ζ ^ 1))⁻¹ * (θ h3 0 (ζ ^ 2))⁻¹ * θ h3 1 (ζ ^ 1) * θ h3 1 (ζ ^ 3) * θ h3 1 (ζ ^ 4)) * w0 + (-mono 0 (ζ ^ 4) * (θ h3 0 (ζ ^ 1))⁻¹ * (θ h3 0 (ζ ^ 2))⁻¹ * θ h3 1 (ζ ^ 1) ^ 2 * θ h3 1 (ζ ^ 4)) * w1 + (-mono 0 (ζ ^ 2) * (θ h3 0 (ζ ^ 1))⁻¹ * (θ h3 0 (ζ ^ 2))⁻¹ * θ h3 1 (ζ ^ 3) ^ 2 * θ h3 1 (ζ ^ 6)) * w2 + (mono 0 (ζ ^ 1) * (θ h3 0 (ζ ^ 1))⁻¹ * (θ h3 0 (ζ ^ 2))⁻¹ * (θ h3 1 (ζ ^ 0))⁻¹ * θ h3 1 (ζ ^ 2) * θ h3 1 (ζ ^ 3) * θ h3 1 (ζ ^ 6) ^ 2) * w3 + (mono 0 (ζ ^ 5) * (θ h3 0 (ζ ^ 1))⁻¹ * (θ h3 0 (ζ ^ 2))⁻¹ * θ h3 1 (ζ ^ 1) * θ h3 1 (ζ ^ 4) * θ h3 1 (ζ ^ 6)) * w4
  simp only [mono_zeta, show mono 0 (1 : ℂ) = 1 from HahnSeries.single_zero_one]
  set Z := mono 0 ζ with hZ
  set Q := mono (-1) (1 : ℂ) with hQ
  have hZ7 : Z ^ 7 = 1 := by
    rw [hZ, mono, single_pow, h7]; exact HahnSeries.single_zero_one
  have hΦc : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6 = 0 := by
    have h : (ζ - 1) * (1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6) = 0 := by
      linear_combination h7
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hζ)
  have hZ6 : Z ^ 6 = -(1 + Z + Z ^ 2 + Z ^ 3 + Z ^ 4 + Z ^ 5) := by
    have h := congrArg (HahnSeries.C (Γ := ℤ) (R := ℂ)) hΦc
    simp only [map_add, map_pow, map_one, map_zero] at h
    rw [show HahnSeries.C (Γ := ℤ) (R := ℂ) ζ = Z from rfl] at h
    linear_combination h
  have r7 : Z ^ 7 = Z ^ 0 := by rw [show 7 = 0 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r8 : Z ^ 8 = Z ^ 1 := by rw [show 8 = 1 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r9 : Z ^ 9 = Z ^ 2 := by rw [show 9 = 2 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r10 : Z ^ 10 = Z ^ 3 := by rw [show 10 = 3 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r11 : Z ^ 11 = Z ^ 4 := by rw [show 11 = 4 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r12 : Z ^ 12 = Z ^ 5 := by rw [show 12 = 5 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r13 : Z ^ 13 = Z ^ 6 := by rw [show 13 = 6 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r14 : Z ^ 14 = Z ^ 0 := by rw [show 14 = 0 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r15 : Z ^ 15 = Z ^ 1 := by rw [show 15 = 1 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r16 : Z ^ 16 = Z ^ 2 := by rw [show 16 = 2 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r17 : Z ^ 17 = Z ^ 3 := by rw [show 17 = 3 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r18 : Z ^ 18 = Z ^ 4 := by rw [show 18 = 4 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r19 : Z ^ 19 = Z ^ 5 := by rw [show 19 = 5 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r20 : Z ^ 20 = Z ^ 6 := by rw [show 20 = 6 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r21 : Z ^ 21 = Z ^ 0 := by rw [show 21 = 0 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r22 : Z ^ 22 = Z ^ 1 := by rw [show 22 = 1 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r23 : Z ^ 23 = Z ^ 2 := by rw [show 23 = 2 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r24 : Z ^ 24 = Z ^ 3 := by rw [show 24 = 3 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r25 : Z ^ 25 = Z ^ 4 := by rw [show 25 = 4 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r26 : Z ^ 26 = Z ^ 5 := by rw [show 26 = 5 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r27 : Z ^ 27 = Z ^ 6 := by rw [show 27 = 6 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r28 : Z ^ 28 = Z ^ 0 := by rw [show 28 = 0 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r29 : Z ^ 29 = Z ^ 1 := by rw [show 29 = 1 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r30 : Z ^ 30 = Z ^ 2 := by rw [show 30 = 2 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r31 : Z ^ 31 = Z ^ 3 := by rw [show 31 = 3 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r32 : Z ^ 32 = Z ^ 4 := by rw [show 32 = 4 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r33 : Z ^ 33 = Z ^ 5 := by rw [show 33 = 5 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r34 : Z ^ 34 = Z ^ 6 := by rw [show 34 = 6 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r35 : Z ^ 35 = Z ^ 0 := by rw [show 35 = 0 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r36 : Z ^ 36 = Z ^ 1 := by rw [show 36 = 1 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r37 : Z ^ 37 = Z ^ 2 := by rw [show 37 = 2 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r38 : Z ^ 38 = Z ^ 3 := by rw [show 38 = 3 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r39 : Z ^ 39 = Z ^ 4 := by rw [show 39 = 4 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r40 : Z ^ 40 = Z ^ 5 := by rw [show 40 = 5 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r41 : Z ^ 41 = Z ^ 6 := by rw [show 41 = 6 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r42 : Z ^ 42 = Z ^ 0 := by rw [show 42 = 0 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r43 : Z ^ 43 = Z ^ 1 := by rw [show 43 = 1 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r44 : Z ^ 44 = Z ^ 2 := by rw [show 44 = 2 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r45 : Z ^ 45 = Z ^ 3 := by rw [show 45 = 3 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r46 : Z ^ 46 = Z ^ 4 := by rw [show 46 = 4 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r47 : Z ^ 47 = Z ^ 5 := by rw [show 47 = 5 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r48 : Z ^ 48 = Z ^ 6 := by rw [show 48 = 6 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r49 : Z ^ 49 = Z ^ 0 := by rw [show 49 = 0 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r50 : Z ^ 50 = Z ^ 1 := by rw [show 50 = 1 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r51 : Z ^ 51 = Z ^ 2 := by rw [show 51 = 2 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r52 : Z ^ 52 = Z ^ 3 := by rw [show 52 = 3 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r53 : Z ^ 53 = Z ^ 4 := by rw [show 53 = 4 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r54 : Z ^ 54 = Z ^ 5 := by rw [show 54 = 5 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r55 : Z ^ 55 = Z ^ 6 := by rw [show 55 = 6 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r56 : Z ^ 56 = Z ^ 0 := by rw [show 56 = 0 + 7 * 8 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r57 : Z ^ 57 = Z ^ 1 := by rw [show 57 = 1 + 7 * 8 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r58 : Z ^ 58 = Z ^ 2 := by rw [show 58 = 2 + 7 * 8 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r59 : Z ^ 59 = Z ^ 3 := by rw [show 59 = 3 + 7 * 8 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  field_simp
  ring_nf
  simp only [r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59]
  ring_nf
  try simp only [hZ6]
  try ring_nf

omit h7 hζ in
lemma mono_split (e : ℤ) (c : ℂ) : mono e c = mono 1 (1 : ℂ) ^ e * mono 0 c := by
  rw [mono_zpow, one_zpow, mul_one, mono, mono, single_mul_single]; simp

set_option maxHeartbeats 4000000 in
/-- **The `z = x²` Appell–Lerch form of `R(ζ;q)`** at a 7th root of unity `ζ ≠ 1`:
`R(ζ;q) θ(ζ²;q³) = (1−ζ) [θ(ζ²;q³) − A(q²ζ⁴, ζ²; q³) − ζ⁶ A(qζ⁴, ζ²; q³)]`. -/
theorem newform :
    ι1 (CrankProof.Dser ζ ζ⁻¹) * θ h3 0 (ζ ^ 2) =
      mono 0 (1 - ζ) * (θ h3 0 (ζ ^ 2) - Ab h3 (a := 2) (β := 0) (by norm_num) (by norm_num) (ζ ^ 4) (ζ ^ 2)
        - mono 0 (ζ ^ 6) * Ab h3 (a := 1) (β := 0) (by norm_num) (by norm_num) (ζ ^ 4) (ζ ^ 2)) := by
  have h0 := zeta_ne0 h7
  have hp : ∀ k : ℕ, ζ ^ k ≠ 0 := fun k => pow_ne_zero k h0
  have hz3 : ζ ^ 3 ≠ 1 := zeta_pow_ne h7 hζ (by norm_num) (by norm_num)
  have hrb := rank_bridge (z := ζ) h0 hζ hz3
  rw [qfac_eq_θ3] at hrb
  obtain ⟨ea, eb1, eb2⟩ := nf_facts h7 hζ
  obtain ⟨eg1, eg2, eg3, eg4, eg5, eg6⟩ := nf_facts2 h7 hζ
  have th := nf_theta h7 hζ
  have zi1 : ζ⁻¹ = ζ ^ 6 := by have := zeta_inv h7 1 (by norm_num); simpa using this
  simp only [θ3_m1 (hp _), θ3_m1 h0, θ3_m1 one_ne_zero, θ3_two (hp _), θ3_two h0, θ3_two one_ne_zero,
    θ3_m2 (hp _), θ3_m2 one_ne_zero, θ3_m3 (hp _), θ0_inv' h7 5 (by norm_num) (by norm_num),
    zeta_inv h7 5 (by norm_num), zeta_inv h7 3 (by norm_num), zi1, inv_one, Nat.reduceSub] at eg1 eg3 eg4 eg5 eg6
  have t03 : θ h3 0 (ζ ^ 3) ≠ 0 := θ_ne0 h3 hz3
  have tE : θ h3 1 1 ≠ 0 := θ_ne h3 (by norm_num) (by norm_num) _
  have tP : ∀ c : ℂ, θ h3 1 c ≠ 0 := fun c => θ_ne h3 (by norm_num) (by norm_num) c
  have hq : mono 1 (1 : ℂ) ≠ 0 := by simp [mono]
  have hZ0 : mono 0 ζ ≠ 0 := by simp [mono, h0]
  linear_combination (norm := skip) (θ h3 0 (ζ ^ 2) / θ h3 1 1) * hrb + (θ h3 0 (ζ ^ 2) * mono 1 (1:ℂ) * (mono 0 ζ - 1) / θ h3 1 1) * eg4 + (θ h3 0 (ζ ^ 2) * mono 0 ζ * (mono 0 ζ - 1) / (θ h3 1 1 * θ h3 0 (ζ ^ 3))) * ea + (θ h3 0 (ζ ^ 2) * mono 0 ζ ^ 2 * (mono 0 ζ - 1) / (θ h3 1 1 * mono 1 (1:ℂ))) * eg6 + (-mono 0 ζ ^ 6 * (mono 0 ζ - 1)) * eb1 + (-(mono 0 ζ - 1) / (mono 0 ζ ^ 2 * mono 1 (1:ℂ) ^ 2)) * eb2 + (mono 0 ζ ^ 11 * (mono 0 ζ - 1) / mono 1 (1:ℂ)) * eg5 + (-mono 1 (1:ℂ) ^ 3 * (mono 0 ζ - 1) / mono 0 ζ ^ 3) * eg1 + ((mono 0 ζ - 1) / mono 0 ζ ^ 5) * eg2 + (-(mono 0 ζ - 1) / mono 0 ζ ^ 5) * eg3 + (hs (kF h3 0) * (mono 0 ζ - 1) / (θ h3 1 1 * θ h3 1 (ζ ^ 1) * θ h3 1 (ζ ^ 3) * θ h3 1 (ζ ^ 4) * θ h3 1 (ζ ^ 6) * θ h3 0 (ζ ^ 3))) * th
  have m1 : ∀ (e : ℤ) (k : ℕ), mono e (ζ ^ k) = mono e 1 * HahnSeries.C ζ ^ k := fun e k => by
    rw [← map_pow, HahnSeries.C_apply, mono, mono, single_mul_single]; simp
  have m2 : ∀ e : ℤ, mono e ζ = mono e 1 * HahnSeries.C ζ := fun e => by
    rw [HahnSeries.C_apply, mono, mono, single_mul_single]; simp
  have m3 : ∀ (e : ℤ) (k : ℕ), mono e (-(ζ ^ k)) = -(mono e 1 * HahnSeries.C ζ ^ k) := fun e k => by
    rw [← m1, mono, mono, single_neg]
  have m4 : ∀ e : ℤ, mono e (1 - ζ) = mono e 1 * (1 - HahnSeries.C ζ) := fun e => by
    rw [mul_sub, mul_one, ← m2, mono, mono, mono, single_sub]
  have m5 : mono 0 (1 : ℂ) = 1 := HahnSeries.single_zero_one
  have m6 : ∀ e : ℤ, e ≠ 0 → e ≠ 1 → mono e (1 : ℂ) = mono 1 (1 : ℂ) ^ e := fun e _ _ => by
    rw [mono_zpow, one_zpow, mul_one]
  simp only [Ai] at hrb ⊢
  simp only [m1, m2, m3, m4] at hrb ea eb1 eb2 eg1 eg2 eg3 eg4 eg5 eg6 th ⊢
  simp (disch := norm_num) only [m5, m6] at hrb ea eb1 eb2 eg1 eg2 eg3 eg4 eg5 eg6 th ⊢
  set Z := HahnSeries.C (Γ := ℤ) (R := ℂ) ζ with hZ
  set q := mono 1 (1 : ℂ) with hqd
  have hZ7 : Z ^ 7 = 1 := by rw [hZ, ← map_pow, h7, map_one]
  have hΦc : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6 = 0 := by
    have h : (ζ - 1) * (1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6) = 0 := by
      linear_combination h7
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hζ)
  have hZ6 : Z ^ 6 = -(1 + Z + Z ^ 2 + Z ^ 3 + Z ^ 4 + Z ^ 5) := by
    have h := congrArg (HahnSeries.C (Γ := ℤ) (R := ℂ)) hΦc
    simp only [map_add, map_pow, map_one, map_zero] at h
    rw [show HahnSeries.C (Γ := ℤ) (R := ℂ) ζ = Z from rfl] at h
    linear_combination h
  have r7 : Z ^ 7 = Z ^ 0 := by rw [show 7 = 0 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r8 : Z ^ 8 = Z ^ 1 := by rw [show 8 = 1 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r9 : Z ^ 9 = Z ^ 2 := by rw [show 9 = 2 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r10 : Z ^ 10 = Z ^ 3 := by rw [show 10 = 3 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r11 : Z ^ 11 = Z ^ 4 := by rw [show 11 = 4 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r12 : Z ^ 12 = Z ^ 5 := by rw [show 12 = 5 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r13 : Z ^ 13 = Z ^ 6 := by rw [show 13 = 6 + 7 * 1 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r14 : Z ^ 14 = Z ^ 0 := by rw [show 14 = 0 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r15 : Z ^ 15 = Z ^ 1 := by rw [show 15 = 1 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r16 : Z ^ 16 = Z ^ 2 := by rw [show 16 = 2 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r17 : Z ^ 17 = Z ^ 3 := by rw [show 17 = 3 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r18 : Z ^ 18 = Z ^ 4 := by rw [show 18 = 4 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r19 : Z ^ 19 = Z ^ 5 := by rw [show 19 = 5 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r20 : Z ^ 20 = Z ^ 6 := by rw [show 20 = 6 + 7 * 2 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r21 : Z ^ 21 = Z ^ 0 := by rw [show 21 = 0 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r22 : Z ^ 22 = Z ^ 1 := by rw [show 22 = 1 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r23 : Z ^ 23 = Z ^ 2 := by rw [show 23 = 2 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r24 : Z ^ 24 = Z ^ 3 := by rw [show 24 = 3 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r25 : Z ^ 25 = Z ^ 4 := by rw [show 25 = 4 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r26 : Z ^ 26 = Z ^ 5 := by rw [show 26 = 5 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r27 : Z ^ 27 = Z ^ 6 := by rw [show 27 = 6 + 7 * 3 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r28 : Z ^ 28 = Z ^ 0 := by rw [show 28 = 0 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r29 : Z ^ 29 = Z ^ 1 := by rw [show 29 = 1 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r30 : Z ^ 30 = Z ^ 2 := by rw [show 30 = 2 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r31 : Z ^ 31 = Z ^ 3 := by rw [show 31 = 3 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r32 : Z ^ 32 = Z ^ 4 := by rw [show 32 = 4 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r33 : Z ^ 33 = Z ^ 5 := by rw [show 33 = 5 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r34 : Z ^ 34 = Z ^ 6 := by rw [show 34 = 6 + 7 * 4 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r35 : Z ^ 35 = Z ^ 0 := by rw [show 35 = 0 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r36 : Z ^ 36 = Z ^ 1 := by rw [show 36 = 1 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r37 : Z ^ 37 = Z ^ 2 := by rw [show 37 = 2 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r38 : Z ^ 38 = Z ^ 3 := by rw [show 38 = 3 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r39 : Z ^ 39 = Z ^ 4 := by rw [show 39 = 4 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r40 : Z ^ 40 = Z ^ 5 := by rw [show 40 = 5 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r41 : Z ^ 41 = Z ^ 6 := by rw [show 41 = 6 + 7 * 5 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r42 : Z ^ 42 = Z ^ 0 := by rw [show 42 = 0 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r43 : Z ^ 43 = Z ^ 1 := by rw [show 43 = 1 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r44 : Z ^ 44 = Z ^ 2 := by rw [show 44 = 2 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r45 : Z ^ 45 = Z ^ 3 := by rw [show 45 = 3 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r46 : Z ^ 46 = Z ^ 4 := by rw [show 46 = 4 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r47 : Z ^ 47 = Z ^ 5 := by rw [show 47 = 5 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r48 : Z ^ 48 = Z ^ 6 := by rw [show 48 = 6 + 7 * 6 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r49 : Z ^ 49 = Z ^ 0 := by rw [show 49 = 0 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r50 : Z ^ 50 = Z ^ 1 := by rw [show 50 = 1 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r51 : Z ^ 51 = Z ^ 2 := by rw [show 51 = 2 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r52 : Z ^ 52 = Z ^ 3 := by rw [show 52 = 3 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r53 : Z ^ 53 = Z ^ 4 := by rw [show 53 = 4 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r54 : Z ^ 54 = Z ^ 5 := by rw [show 54 = 5 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r55 : Z ^ 55 = Z ^ 6 := by rw [show 55 = 6 + 7 * 7 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r56 : Z ^ 56 = Z ^ 0 := by rw [show 56 = 0 + 7 * 8 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r57 : Z ^ 57 = Z ^ 1 := by rw [show 57 = 1 + 7 * 8 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r58 : Z ^ 58 = Z ^ 2 := by rw [show 58 = 2 + 7 * 8 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r59 : Z ^ 59 = Z ^ 3 := by rw [show 59 = 3 + 7 * 8 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r60 : Z ^ 60 = Z ^ 4 := by rw [show 60 = 4 + 7 * 8 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r61 : Z ^ 61 = Z ^ 5 := by rw [show 61 = 5 + 7 * 8 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r62 : Z ^ 62 = Z ^ 6 := by rw [show 62 = 6 + 7 * 8 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r63 : Z ^ 63 = Z ^ 0 := by rw [show 63 = 0 + 7 * 9 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r64 : Z ^ 64 = Z ^ 1 := by rw [show 64 = 1 + 7 * 9 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r65 : Z ^ 65 = Z ^ 2 := by rw [show 65 = 2 + 7 * 9 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r66 : Z ^ 66 = Z ^ 3 := by rw [show 66 = 3 + 7 * 9 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r67 : Z ^ 67 = Z ^ 4 := by rw [show 67 = 4 + 7 * 9 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r68 : Z ^ 68 = Z ^ 5 := by rw [show 68 = 5 + 7 * 9 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r69 : Z ^ 69 = Z ^ 6 := by rw [show 69 = 6 + 7 * 9 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r70 : Z ^ 70 = Z ^ 0 := by rw [show 70 = 0 + 7 * 10 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r71 : Z ^ 71 = Z ^ 1 := by rw [show 71 = 1 + 7 * 10 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r72 : Z ^ 72 = Z ^ 2 := by rw [show 72 = 2 + 7 * 10 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r73 : Z ^ 73 = Z ^ 3 := by rw [show 73 = 3 + 7 * 10 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r74 : Z ^ 74 = Z ^ 4 := by rw [show 74 = 4 + 7 * 10 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r75 : Z ^ 75 = Z ^ 5 := by rw [show 75 = 5 + 7 * 10 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r76 : Z ^ 76 = Z ^ 6 := by rw [show 76 = 6 + 7 * 10 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r77 : Z ^ 77 = Z ^ 0 := by rw [show 77 = 0 + 7 * 11 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r78 : Z ^ 78 = Z ^ 1 := by rw [show 78 = 1 + 7 * 11 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have r79 : Z ^ 79 = Z ^ 2 := by rw [show 79 = 2 + 7 * 11 by norm_num, _root_.pow_add, pow_mul, hZ7, one_pow, mul_one]
  have tP1 : θ h3 1 ζ ≠ 0 := tP ζ
  have tP2' : θ h3 1 (ζ ^ 2) ≠ 0 := tP _
  have tP3' : θ h3 1 (ζ ^ 3) ≠ 0 := tP _
  have tP4' : θ h3 1 (ζ ^ 4) ≠ 0 := tP _
  have tP5' : θ h3 1 (ζ ^ 5) ≠ 0 := tP _
  have tP6' : θ h3 1 (ζ ^ 6) ≠ 0 := tP _
  have hZne : Z ≠ 0 := by rw [hZ]; simpa using h0
  have tPk : ∀ k : ℕ, θ h3 1 (ζ ^ k) ≠ 0 := fun k => tP _
  have hq' : q ≠ 0 := hq
  field_simp
  ring_nf
  simp only [r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47, r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63, r64, r65, r66, r67, r68, r69, r70, r71, r72, r73, r74, r75, r76, r77, r78, r79]
  ring_nf
  try simp only [hZ6]
  try ring_nf

end Subst
end ALz
