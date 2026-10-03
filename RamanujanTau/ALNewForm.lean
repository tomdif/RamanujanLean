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
end ALz
