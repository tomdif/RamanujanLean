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

end Subst
end ALz
