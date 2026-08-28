/-
# The fixed four-dual-shell cutoff is false

The exact Poisson-dual scanner finds the first four-shell false positive at

  p = 1439,  (i,j,k) = (1,63,391),  R = 229.

This file kernel-checks the arithmetic half of that certificate: the datum is
prime, canonical, and isotropic, but it has no projective lift of norm `p` or
`2p`.  Therefore it has no `ProjectiveRootTargetCertificate`, for any target
residue.  The companion `dual-candidate` command enumerates the complete dual
shells and verifies their exact phase counters.
-/
import RamanujanTau.MultiQuintupleRootVanishingClassification

namespace Ramanujan.MultiQuintuple

/-- The counterexample modulus is prime. -/
theorem prime_1439 : Nat.Prime 1439 := by norm_num

/-- The projective datum lies on the isotropic conic. -/
theorem isotropic_1439_1_63_391 :
    (1 : ℤ) ^ 2 + 63 ^ 2 + 391 ^ 2 = 1439 * 109 := by
  norm_num

/-- No lift of `(1,63,391)` modulo `1439` has norm `1439` or `2878`.

The root equation bounds every coordinate by `53`.  Inside that box the two
projective congruences leave only the lifts `0` and
`±(-22,53,32)`, whose norms are respectively `0` and `3*1439`.
-/
theorem no_short_projective_lift_1439_1_63_391
    (lambda e w1 w2 w3 a1 a2 a3 : ℤ)
    (he : e = 1 ∨ e = 2)
    (hw1 : w1 = lambda + 1439 * a1)
    (hw2 : w2 = lambda * 63 + 1439 * a2)
    (hw3 : w3 = lambda * 391 + 1439 * a3)
    (hroot : ternaryNorm w1 w2 w3 = e * 1439) : False := by
  have he0 : 0 ≤ e := by rcases he with rfl | rfl <;> norm_num
  have he2 : e ≤ 2 := by rcases he with rfl | rfl <;> norm_num
  have hnorm : w1 ^ 2 + w2 ^ 2 + w3 ^ 2 = e * 1439 := by
    simpa only [ternaryNorm] using hroot
  have hnorm_le : w1 ^ 2 + w2 ^ 2 + w3 ^ 2 ≤ 2878 := by
    nlinarith
  have hw1sq : w1 ^ 2 ≤ 2878 := by nlinarith [sq_nonneg w2, sq_nonneg w3]
  have hw2sq : w2 ^ 2 ≤ 2878 := by nlinarith [sq_nonneg w1, sq_nonneg w3]
  have hw3sq : w3 ^ 2 ≤ 2878 := by nlinarith [sq_nonneg w1, sq_nonneg w2]
  have hw1lo : -53 ≤ w1 := by nlinarith
  have hw1hi : w1 ≤ 53 := by nlinarith
  have hw2lo : -53 ≤ w2 := by nlinarith
  have hw2hi : w2 ≤ 53 := by nlinarith
  have hw3lo : -53 ≤ w3 := by nlinarith
  have hw3hi : w3 ≤ 53 := by nlinarith
  have hcong2 : w2 = 63 * w1 + 1439 * (a2 - 63 * a1) := by
    rw [hw1, hw2]
    ring
  have hcong3 : w3 = 391 * w1 + 1439 * (a3 - 391 * a1) := by
    rw [hw1, hw3]
    ring
  have hcases :
      (w1 = -22 ∧ w2 = 53 ∧ w3 = 32) ∨
      (w1 = 0 ∧ w2 = 0 ∧ w3 = 0) ∨
      (w1 = 22 ∧ w2 = -53 ∧ w3 = -32) := by
    interval_cases w1 <;> omega
  rcases hcases with hcase | hcase | hcase
  · rcases hcase with ⟨rfl, rfl, rfl⟩
    norm_num [ternaryNorm] at hroot
    omega
  · rcases hcase with ⟨rfl, rfl, rfl⟩
    norm_num [ternaryNorm] at hroot
    omega
  · rcases hcase with ⟨rfl, rfl, rfl⟩
    norm_num [ternaryNorm] at hroot
    omega

/-- The four-shell false positive is not a short-root target at any residue. -/
theorem no_projectiveRootTarget_1439_1_63_391 (R : ℕ) :
    ¬HasProjectiveRootTarget 1439 1 63 391 R := by
  rintro ⟨root⟩
  apply no_short_projective_lift_1439_1_63_391
      root.lambda root.e root.w1 root.w2 root.w3 root.a1 root.a2 root.a3
      root.he
  · simpa using root.hw1
  · simpa using root.hw2
  · simpa using root.hw3
  · exact root.hroot

end Ramanujan.MultiQuintuple
