import RamanujanTau.BWSharpAll.DetCriterion
import RamanujanTau.TheoremA.BWDictionary

/-!
# The first open step `b_ℓ(2) = 3` as a non-congruence for `p(n)` modulo `ℓ²`

`bEll_two_eq_three_iff`: for every prime `ℓ ≥ 13`, `b_ℓ(2) = 3` holds iff there is **no**
congruence

  `p(ℓn − (ℓ²−1)/24) ≡ Σᵢ cᵢ · p(ℓ^{2i+3} n − (ℓ^{2i+4}−1)/24)   (mod ℓ²)`, for all `n ≥ 0`,

with finitely many coefficients `cᵢ ∈ ℤ/ℓ²` (`p(x) = 0` for `x < 0`). By Theorem A one always
has `b_ℓ(2) ≤ 3`; the alternative is `b_ℓ(2) = 1`. This is an exact restatement of the
first instance of sharpness in classical terms; it is the mod-`ℓ²` analogue of the
nonexistence of Ramanujan-type congruences `p(ℓn+β) ≡ 0 (mod ℓ)` for `ℓ ≥ 13`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.BWSharpAll
open PowerSeries BoylanWebb BLBound

noncomputable section

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- `b_ℓ(2) = 3` iff `L(1) ∉ Λ^odd(3, 2)`. -/
theorem bEll_two_eq_three_iff_not_mem (h13 : 13 ≤ ℓ) :
    bEll ℓ 2 = 3 ↔ redm ℓ 2 (L ℓ 1) ∉ Lam ℓ 2 3 := by
  constructor
  · intro h hmem
    have heq : Lam ℓ 2 (2 * 0 + 1) = Lam ℓ 2 (2 * (0 + 1) + 1) := by
      apply le_antisymm _ (Lam_anti 2 0)
      rw [Lam, Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · exact hmem
      · exact Submodule.subset_span ⟨j, by omega, rfl⟩
    have hfin : Finite (Lam ℓ 2 (2 * 0 + 1)) := by
      rw [heq]; exact (chain_structure h13 2 (by norm_num) 1 (by norm_num)).2
    have h1 := mem_bSet_of_eq 2 0 heq hfin
    have : bEll ℓ 2 ≤ 1 := Nat.sInf_le h1
    omega
  · intro h
    apply bEll_eq_of_not_mem h13 2 (by norm_num)
    intro k hk
    obtain rfl : k = 0 := by omega
    simpa using h

lemma Lam3_eq : Lam ℓ 2 3 = Submodule.span (Rm ℓ 2)
    (Set.range fun i : ℕ => redm ℓ 2 (L ℓ (2 * (1 + i) + 1))) := by
  rw [show (3 : ℕ) = 2 * 1 + 1 from rfl, Lam_eq]
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_range, gm]
  exact ⟨fun ⟨j, hj⟩ => ⟨j, hj.symm⟩, fun ⟨j, hj⟩ => ⟨j, hj.symm⟩⟩

/-- **`b_ℓ(2) = 3` is equivalent to the absence of one mod-`ℓ²` partition congruence.** -/
theorem bEll_two_eq_three_iff (h13 : 13 ≤ ℓ) :
    bEll ℓ 2 = 3 ↔ ¬ ∃ c : ℕ →₀ ZMod (ℓ ^ 2), ∀ n : ℕ,
      ((pZ ((ℓ : ℤ) * n - ek ℓ 1) : ℤ) : ZMod (ℓ ^ 2)) =
        c.sum fun i a => a * ((pZ ((ℓ : ℤ) ^ (2 * (1 + i) + 1) * n - ek ℓ (i + 2)) : ℤ) :
          ZMod (ℓ ^ 2)) := by
  have h24 := TheoremA.HalfIntegral.h24 (ℓ := ℓ) h13
  rw [bEll_two_eq_three_iff_not_mem h13, Lam3_eq, Finsupp.mem_span_range_iff_exists_finsupp]
  apply not_congr
  set φ := Int.castRingHom (ZMod (ℓ ^ 2))
  set u := PowerSeries.map φ (RankProof.Ea ℓ (hℓ0 ℓ) MockTheta5.JTP.qfacInf)
  have hu : IsUnit u := (MockTheta5.JTP.isUnit_qfacInf.map (RankProof.Ea ℓ (hℓ0 ℓ))).map _
  have hL : ∀ b, redm ℓ 2 (L ℓ (2 * b + 1)) = u * PowerSeries.map φ (Pser ℓ (2 * b + 1)) := by
    intro b
    rw [(L_eq_partition ℓ h24 b).2, map_mul]
  have hcoeff : ∀ b n, coeff n (PowerSeries.map φ (Pser ℓ (2 * b + 1))) =
      ((pZ ((ℓ : ℤ) ^ (2 * b + 1) * n - ek ℓ (b + 1)) : ℤ) : ZMod (ℓ ^ 2)) := by
    intro b n
    rw [PowerSeries.coeff_map, Pser, PowerSeries.coeff_mk, eB,
      show (2 * b + 1 + 1) / 2 = b + 1 by omega]
    rfl
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun n => ?_⟩
    have hc' : u * (c.sum fun i a => a • PowerSeries.map φ (Pser ℓ (2 * (1 + i) + 1))) =
        u * PowerSeries.map φ (Pser ℓ (2 * 0 + 1)) := by
      rw [← hL 0, ← hc, Finsupp.mul_sum]
      refine Finsupp.sum_congr fun i _ => ?_
      rw [hL, mul_smul_comm]
    have hP := congrArg (coeff n) (hu.mul_left_cancel hc')
    rw [hcoeff] at hP
    simp only [Nat.mul_zero, Nat.zero_add, pow_one] at hP
    rw [← hP, map_finsuppSum]
    refine Finsupp.sum_congr fun i _ => ?_
    rw [LinearMap.map_smul, smul_eq_mul, hcoeff, show 1 + i + 1 = i + 2 by ring]
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hP : (c.sum fun i a => a • PowerSeries.map φ (Pser ℓ (2 * (1 + i) + 1))) =
        PowerSeries.map φ (Pser ℓ (2 * 0 + 1)) := by
      ext n
      rw [hcoeff, map_finsuppSum]
      simp only [Nat.mul_zero, Nat.zero_add, pow_one] at hc ⊢
      rw [hc n]
      refine Finsupp.sum_congr fun i _ => ?_
      rw [LinearMap.map_smul, smul_eq_mul, hcoeff, show 1 + i + 1 = i + 2 by ring]
    rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, hL 0, ← hP, Finsupp.mul_sum]
    refine Finsupp.sum_congr fun i _ => ?_
    rw [hL, mul_smul_comm]

end

end RamanujanTau.BWSharpAll
