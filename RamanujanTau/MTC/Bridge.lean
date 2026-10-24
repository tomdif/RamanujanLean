/-
# From theta sums in `ℂ((t))` to theta products in `ℤ⟦q⟧`

`θ_eq_ιN`: for `0 < b < a` and `d ≥ 1`, `θ(t^{db}; t^{da}) = ιN_d (J_{b,a})`, where `ιN_d : ℤ⟦X⟧ → ℂ((t))` sends
`X ↦ t^d` and `J_{b,a} = (q^b;q^a)_∞ (q^{a−b};q^a)_∞ (q^a;q^a)_∞` (`RankProof.jtp_ab`).
-/
import RamanujanTau.ALJacobi
import RamanujanTau.RankDissect

set_option autoImplicit false

namespace MTC
open ALz HahnSeries

lemma triE_eq_c2 (k : ℤ) : (MockTheta5.JTP.triE k : ℤ) = c2 k := by
  have h1 := CrankProof.two_triE k
  have h2 := two_c2 k
  omega

lemma expo_eq (a b : ℕ) (hba : b ≤ a) (k : ℤ) :
    ((CrankProof.expo a b k : ℕ) : ℤ) = a * c2 k + b * k := by
  unfold CrankProof.expo
  rw [Int.toNat_of_nonneg (CrankProof.expo_nonneg hba k), triE_eq_c2]

/-- **the sum–product bridge**: `θ(t^{db}; t^{da}) = ιN_d (J_{b,a})`. -/
theorem θ_eq_ιN {d a b : ℕ} (hd : 1 ≤ d) (hb : 1 ≤ b) (hab : b < a) (h : 1 ≤ d * a) :
    θ h ((d * b : ℕ) : ℤ) 1 = ιN hd (RankProof.thetaS a b) := by
  have hpsi := CrankProof.thetaS_eq_thL hb hab
  have hd0 : (0 : ℤ) < d := by exact_mod_cast hd
  ext n
  rcases lt_or_ge n 0 with hn | hn
  · rw [ιN_coeff_neg hd _ hn, θ, thF, monoFam_coeff_zero]
    intro k hk
    have := expo_eq a b hab.le k
    have hnn : (0 : ℤ) ≤ ((CrankProof.expo a b k : ℕ) : ℤ) := Nat.cast_nonneg _
    unfold thE at hk
    push_cast at hk
    nlinarith [mul_nonneg hd0.le hnn]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
    rw [ιN_coeff_nat, θ, thF, monoFam_coeff]
    split_ifs with hdm
    · obtain ⟨K, rfl⟩ := hdm
      rw [Nat.mul_div_cancel_left K (by omega)]
      have hcoeff : ((PowerSeries.coeff K (RankProof.thetaS a b) : ℤ) : ℂ) =
          PowerSeries.coeff K (CrankProof.thL a b 1) := by
        rw [← hpsi, MockTheta5.JTP.ψC, PowerSeries.coeff_map]; rfl
      rw [hcoeff, CrankProof.thL, CrankProof.coeff_lat _ (CrankProof.proper_expo (by omega) hab.le)]
      have hfin : (Function.support fun k : ℤ =>
          if CrankProof.expo a b k = K then (-(1 : ℂ)) ^ k else 0).Finite :=
        (CrankProof.proper_expo (a := a) (b := b) (by omega) hab.le K).subset fun k hk => by
          simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hk
          simp only [Set.mem_setOf_eq]; omega
      rw [tsum_eq_finsum hfin]
      refine finsum_congr fun k => ?_
      have hk := expo_eq a b hab.le k
      simp only [thC, one_zpow, mul_one]
      by_cases h' : thE (d * a) ((d * b : ℕ) : ℤ) k = ((d * K : ℕ) : ℤ)
      · rw [if_pos h', if_pos]
        unfold thE at h'
        push_cast at h'
        have : (d : ℤ) * (CrankProof.expo a b k : ℤ) = d * K := by rw [hk]; linarith
        exact_mod_cast mul_left_cancel₀ hd0.ne' this
      · rw [if_neg h', if_neg]
        intro he
        apply h'
        unfold thE
        rw [he] at hk
        push_cast
        rw [hk]; ring
    · refine (finsum_eq_zero_of_forall_eq_zero fun k => if_neg ?_).trans (by simp)
      intro he
      apply hdm
      refine ⟨CrankProof.expo a b k, ?_⟩
      have hk := expo_eq a b hab.le k
      unfold thE at he
      push_cast at he
      have : ((m : ℕ) : ℤ) = ((d * CrankProof.expo a b k : ℕ) : ℤ) := by push_cast; rw [hk]; linarith
      exact_mod_cast this

/-- the same with the product form `J_{b,a}` (`RankProof.jtp_ab`). -/
theorem θ_eq_ιN_prod {d a b : ℕ} (hd : 1 ≤ d) (hb : 1 ≤ b) (hab : b < a) (h : 1 ≤ d * a) :
    θ h ((d * b : ℕ) : ℤ) 1 =
      ιN hd (RankProof.Pinf b a * RankProof.Pinf (a - b) a * RankProof.Pinf a a) := by
  rw [θ_eq_ιN hd hb hab h, RankProof.jtp_ab a b hb hab]

end MTC
