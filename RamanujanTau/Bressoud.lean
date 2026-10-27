/-
# Bressoud's identities (the even-modulus Andrews–Gordon identities)

For `k ≥ 2` and `1 ≤ i ≤ k − 1` (Bressoud 1980):

  `Σ_{n₁ ≥ ⋯ ≥ n_{k−1} ≥ 0} q^{n₁²+⋯+n_{k−1}² + n_i+⋯+n_{k−1}} / ((q)_{n₁−n₂} ⋯ (q)_{n_{k−2}−n_{k−1}} (q²;q²)_{n_{k−1}})
     = ∏_{n ≢ 0, ±i (mod 2k)} 1/(1 − qⁿ)`.

The route is the same as `AndrewsGordonAll`, but the base is the `a = q` pair
`(αₙ = (−1)ⁿq^{n²}(1+⋯+q^{2n}), βₙ = 1/(q²;q²)ₙ)` (`isBaileyPairQ_A`):
* `i = 1`: `k − 2` steps of the `a = q` chain, then the `a = q` Bailey transform;
* `2 ≤ i ≤ k − 1`: `k − i` steps of the `a = q` chain, the switch to `a = 1` (`isBaileyPair_toOne`), then `i − 2`
  steps of the `a = 1` chain and the Bailey transform.

The `α` side is the theta series `Σ_{n∈ℤ}(−1)ⁿq^{k n² + (k−i)n} = J_{2k,i}`.
-/
import RamanujanTau.AndrewsGordonAll
import RamanujanTau.MockTheta5BaileyQPairA

set_option autoImplicit false

namespace MockTheta5.JTP.AG
open PowerSeries Finset MockTheta5.Bailey MockTheta5.JTP MockTheta5.JTP.RR
open RankProof (Pinf Pfin Pfin_succ X_pow_dvd_Pfin_sub X_pow_dvd_Pinf_sub Pinf_ext Pinf_one_one thetaS thA thB
  thetaTr thetaTr_eq thetaS_dvd jtp_ab)

/-- `β` after `s` steps of the `a = q` chain from `1/(q²;q²)_n`. -/
noncomputable def brBetaQ : ℕ → ℕ → PowerSeries ℤ
  | 0 => fun n => Ring.inverse (q2q2 n)
  | s + 1 => chainBetaQ (brBetaQ s)

noncomputable def brAlphaQ : ℕ → ℕ → PowerSeries ℤ
  | 0 => alphaA
  | s + 1 => chainAlphaQ (brAlphaQ s)

lemma brAlphaQ_eq (s n : ℕ) : brAlphaQ s n = X ^ (s * (n ^ 2 + n)) * alphaA n := by
  induction s with
  | zero => simp [brAlphaQ]
  | succ s ih => rw [brAlphaQ, chainAlphaQ, ih, ← mul_assoc, ← pow_add]; ring_nf

lemma isBaileyPairQ_br (s : ℕ) : IsBaileyPairQ (brAlphaQ s) (brBetaQ s) := by
  induction s with
  | zero => exact isBaileyPairQ_A
  | succ s ih => exact isBaileyPairQ_chain ih

/-- the product split shared by both families. -/
lemma prod_split (a b : ℕ) (hb : 1 ≤ b) (hab : b < a - b) :
    partitionGF * thetaS a b * agProd a b = 1 := by
  rw [← jtp_ab a b hb (by omega)]
  have hs := Pinf_split a (by omega)
  rw [Pinf_one_one] at hs
  have hprod : ∏ r ∈ range a, Pinf (r + 1) a = Pinf b a * Pinf (a - b) a * Pinf a a * agProd a b := by
    rw [agProd, ← prod_filter_mul_prod_filter_not (range a) (fun r => r + 1 ≠ b ∧ r + 1 ≠ a - b ∧ r + 1 ≠ a)]
    have hn : (range a).filter (fun r => ¬ (r + 1 ≠ b ∧ r + 1 ≠ a - b ∧ r + 1 ≠ a)) = {b - 1, a - b - 1, a - 1} := by
      ext r; simp only [mem_filter, mem_range, mem_insert, mem_singleton]; omega
    rw [hn, prod_insert (by simp; omega), prod_insert (by simp; omega), prod_singleton,
      show b - 1 + 1 = b by omega, show a - b - 1 + 1 = a - b by omega, show a - 1 + 1 = a by omega]
    ring
  rw [← hs] at hprod
  rw [show partitionGF * (Pinf b a * Pinf (a - b) a * Pinf a a) * agProd a b
      = partitionGF * (Pinf b a * Pinf (a - b) a * Pinf a a * agProd a b) by ring, ← hprod]
  exact Ring.inverse_mul_cancel _ isUnit_qfacInf

/-! ## `i = 1` -/

lemma term_brQ (s n : ℕ) :
    (1 - X) * (X ^ (n ^ 2 + n) * brAlphaQ s n)
      = (if n = 0 then thA (2 * s + 4) 1 0 else thB (2 * s + 4) 1 (n - 1)) + thA (2 * s + 4) 1 (n + 1) := by
  rw [brAlphaQ_eq]
  have hg := geom_mul (2 * n + 1)
  rw [alphaA, show (1 - X) * (X ^ (n ^ 2 + n) * (X ^ (s * (n ^ 2 + n)) * ((-1) ^ n * X ^ (n ^ 2) * geom (2 * n + 1))))
      = X ^ (n ^ 2 + n) * (X ^ (s * (n ^ 2 + n)) * ((-1) ^ n * X ^ (n ^ 2) * ((1 - X) * geom (2 * n + 1)))) by ring,
    hg]
  rcases n with _ | n
  · simp [RankProof.thA]; ring
  · rw [if_neg (by omega), Nat.add_sub_cancel]
    simp only [RankProof.thA, RankProof.thB]
    have h2 := two_choose (n + 1)
    have hc := RR.choose_two_succ (n + 1)
    have e1 : (n + 1) ^ 2 + (n + 1) + (s * ((n + 1) ^ 2 + (n + 1)) + (n + 1) ^ 2)
        = (2 * s + 4) * (n + 1).choose 2 + (2 * s + 4 - 1) * (n + 1) := by
      rw [show 2 * s + 4 - 1 = 2 * s + 3 by omega, ← h2]; ring
    have e2 : (n + 1) ^ 2 + (n + 1) + (s * ((n + 1) ^ 2 + (n + 1)) + (n + 1) ^ 2) + (2 * (n + 1) + 1)
        = (2 * s + 4) * (n + 1 + 1).choose 2 + 1 * (n + 1 + 1) := by
      rw [hc, ← h2]; ring
    rw [← e1, ← e2]
    simp only [map_mul, map_neg, map_pow, map_one, pow_add, pow_one]
    ring

lemma sum_term_brQ (s N : ℕ) :
    (1 - X) * ∑ n ∈ range (N + 1), X ^ (n ^ 2 + n) * brAlphaQ s n
      = ∑ d ∈ range (N + 2), thA (2 * s + 4) 1 d + ∑ d ∈ range N, thB (2 * s + 4) 1 d := by
  induction N with
  | zero => rw [sum_range_one, term_brQ]; simp [sum_range_succ]
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih, term_brQ, if_neg (by omega), Nat.add_sub_cancel,
      sum_range_succ (thA _ _) (N + 2), sum_range_succ (thB _ _)]
    ring

theorem brAlphaQ_theta (s : ℕ) : (1 - X) * tsumQsqQ (brAlphaQ s) = thetaS (2 * s + 4) 1 := by
  refine eq_of_dvd_all fun N => ?_
  have h1 := dvd_mul_of_dvd_right (RR.tsumQsqQ_dvd (brAlphaQ s) N) (1 - X)
  rw [mul_sub, sum_term_brQ] at h1
  have h2 := thetaS_dvd (2 * s + 4) 1 (by norm_num) (by omega) N
  rw [thetaTr_eq, sum_range_succ (thB _ _) N] at h2
  have h3 : (X : PowerSeries ℤ) ^ (N + 1) ∣ thA (2 * s + 4) 1 (N + 1) := thA_deg _ 1 (N + 1) le_rfl
  have h4 : (X : PowerSeries ℤ) ^ (N + 1) ∣ thB (2 * s + 4) 1 N := thB_deg _ 1 N (by omega)
  have := dvd_add (dvd_sub (dvd_sub h1 h2) h4) h3
  rw [sum_range_succ (thA _ _) (N + 1)] at this
  rw [show (1 - X) * tsumQsqQ (brAlphaQ s) - (∑ d ∈ range (N + 1), thA (2 * s + 4) 1 d + thA (2 * s + 4) 1 (N + 1)
      + ∑ d ∈ range N, thB (2 * s + 4) 1 d) - (thetaS (2 * s + 4) 1 - (∑ d ∈ range (N + 1), thA (2 * s + 4) 1 d
      + (∑ d ∈ range N, thB (2 * s + 4) 1 d + thB (2 * s + 4) 1 N))) - thB (2 * s + 4) 1 N + thA (2 * s + 4) 1 (N + 1)
      = (1 - X) * tsumQsqQ (brAlphaQ s) - thetaS (2 * s + 4) 1 by ring] at this
  exact this

/-- **Bressoud's identity, `i = 1`** (`k = s + 2`): `Σ q^{Σnⱼ² + Σnⱼ}/(⋯(q²;q²)_{n_{k−1}}) = ∏_{n ≢ 0,±1 (mod 2k)} 1/(1−qⁿ)`. -/
theorem bressoud_one (s : ℕ) : tsumQsqQ (brBetaQ s) * agProd (2 * s + 4) 1 = 1 := by
  rw [bailey_transform_q (isBaileyPairQ_br s), show (1 - X) * partitionGF * tsumQsqQ (brAlphaQ s)
      = partitionGF * ((1 - X) * tsumQsqQ (brAlphaQ s)) by ring, brAlphaQ_theta]
  exact prod_split _ _ le_rfl (by omega)

/-! ## `2 ≤ i ≤ k − 1` -/

noncomputable def brBetaI (s : ℕ) : ℕ → ℕ → PowerSeries ℤ
  | 0 => brBetaQ s
  | t + 1 => chainBeta (brBetaI s t)

noncomputable def brAlphaI (s : ℕ) : ℕ → ℕ → PowerSeries ℤ
  | 0 => toOne (brAlphaQ s)
  | t + 1 => chainAlpha (brAlphaI s t)

lemma isBaileyPair_brI (s t : ℕ) : IsBaileyPair (brAlphaI s t) (brBetaI s t) := by
  induction t with
  | zero => exact isBaileyPair_toOne (isBaileyPairQ_br s)
  | succ t ih => exact isBaileyPair_chain ih

lemma brAlphaI_eq (s t n : ℕ) : brAlphaI s t n = X ^ (t * n ^ 2) * toOne (brAlphaQ s) n := by
  induction t with
  | zero => simp [brAlphaI]
  | succ t ih => rw [brAlphaI, chainAlpha, ih, ← mul_assoc, ← pow_add]; ring_nf

lemma toOneT_br (s r : ℕ) : toOneT (brAlphaQ s) r = (-1) ^ r * X ^ (s * (r ^ 2 + r) + r ^ 2) := by
  rw [toOneT, brAlphaQ_eq, alphaA]
  have hg := geom_mul (2 * r + 1)
  have hu : Ring.inverse (1 - X ^ (2 * r + 1) : PowerSeries ℤ) * (1 - X ^ (2 * r + 1)) = 1 :=
    Ring.inverse_mul_cancel _ (isUnit_one_sub_X_pow (by omega))
  calc (1 - X) * Ring.inverse (1 - X ^ (2 * r + 1)) * (X ^ (s * (r ^ 2 + r)) * ((-1) ^ r * X ^ (r ^ 2) *
        geom (2 * r + 1)))
      = (-1) ^ r * X ^ (s * (r ^ 2 + r)) * X ^ (r ^ 2) *
          (Ring.inverse (1 - X ^ (2 * r + 1)) * ((1 - X) * geom (2 * r + 1))) := by ring
    _ = (-1) ^ r * X ^ (s * (r ^ 2 + r) + r ^ 2) := by rw [hg, hu]; ring

lemma term_brI (s t n : ℕ) :
    X ^ (n ^ 2) * brAlphaI s t n =
      thA (2 * s + 2 * t + 4) (t + 2) n + (if n = 0 then 0 else thB (2 * s + 2 * t + 4) (t + 2) (n - 1)) := by
  rw [brAlphaI_eq, toOne]
  rcases n with _ | m
  · simp [toOneT_br, RankProof.thA]
  · rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel, toOneT_br, toOneT_br,
      show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
    simp only [RankProof.thA, RankProof.thB]
    have h2 := two_choose m
    have hc : (m + 1).choose 2 = m.choose 2 + m := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    have hsq : (m + 1) ^ 2 = 2 * m.choose 2 + 3 * m + 1 := by
      rw [show (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 by ring, ← h2]; ring
    have e1 : (m + 1) ^ 2 + (t * (m + 1) ^ 2 + (s * ((m + 1) ^ 2 + (m + 1)) + (m + 1) ^ 2)) =
        (2 * s + 2 * t + 4) * (m + 1).choose 2 + (2 * s + 2 * t + 4 - (t + 2)) * (m + 1) := by
      rw [show 2 * s + 2 * t + 4 - (t + 2) = 2 * s + t + 2 by omega, hc, hsq]; ring
    have e2 : (m + 1) ^ 2 + (t * (m + 1) ^ 2 + (2 * m + 1 + (s * (m ^ 2 + m) + m ^ 2))) =
        (2 * s + 2 * t + 4) * (m + 1).choose 2 + (t + 2) * (m + 1) := by
      rw [hc, hsq, ← h2]; ring
    rw [← e1, ← e2]
    simp only [map_mul, map_neg, map_pow, map_one, pow_add, pow_one]
    ring

lemma sum_term_brI (s t N : ℕ) :
    ∑ n ∈ range (N + 1), X ^ (n ^ 2) * brAlphaI s t n
      = ∑ d ∈ range (N + 1), thA (2 * s + 2 * t + 4) (t + 2) d +
          ∑ d ∈ range N, thB (2 * s + 2 * t + 4) (t + 2) d := by
  induction N with
  | zero => simp [term_brI]
  | succ N ih =>
    rw [sum_range_succ, ih, term_brI, if_neg (by omega), Nat.add_sub_cancel, sum_range_succ (thA _ _) (N + 1),
      sum_range_succ (thB _ _) N]
    ring

theorem brAlphaI_theta (s t : ℕ) : tsumQsq (brAlphaI s t) = thetaS (2 * s + 2 * t + 4) (t + 2) := by
  refine eq_of_dvd_all fun N => ?_
  have h1 := RR.tsumQsq_dvd (brAlphaI s t) N
  have h2 := thetaS_dvd (2 * s + 2 * t + 4) (t + 2) (by omega) (by omega) N
  rw [sum_term_brI] at h1
  have h3 : (X : PowerSeries ℤ) ^ (N + 1) ∣ thB (2 * s + 2 * t + 4) (t + 2) N := thB_deg _ _ N (by omega)
  rw [thetaTr_eq, sum_range_succ (thB _ _)] at h2
  have := dvd_sub (dvd_sub h1 h2) h3
  rw [show tsumQsq (brAlphaI s t) - (∑ d ∈ range (N + 1), thA (2 * s + 2 * t + 4) (t + 2) d
        + ∑ d ∈ range N, thB (2 * s + 2 * t + 4) (t + 2) d)
      - (thetaS (2 * s + 2 * t + 4) (t + 2) - (∑ d ∈ range (N + 1), thA (2 * s + 2 * t + 4) (t + 2) d
        + (∑ d ∈ range N, thB (2 * s + 2 * t + 4) (t + 2) d + thB (2 * s + 2 * t + 4) (t + 2) N)))
      - thB (2 * s + 2 * t + 4) (t + 2) N
      = tsumQsq (brAlphaI s t) - thetaS (2 * s + 2 * t + 4) (t + 2) by ring] at this
  exact this

/-- **Bressoud's identities, `2 ≤ i ≤ k − 1`** (`k = s + t + 3`, `i = t + 2`, so `k − i = s + 1 ≥ 1`):
`Σ q^{n₁²+⋯+n_{k−1}² + n_i+⋯+n_{k−1}}/((q)_{n₁−n₂}⋯(q²;q²)_{n_{k−1}}) = ∏_{n ≢ 0,±i (mod 2k)} 1/(1−qⁿ)`. -/
theorem bressoud_i (s t : ℕ) :
    tsumQsq (brBetaI (s + 1) t) * agProd (2 * (s + 1) + 2 * t + 4) (t + 2) = 1 := by
  rw [bailey_transform (isBaileyPair_brI (s + 1) t), brAlphaI_theta]
  exact prod_split _ _ (by omega) (by omega)

end MockTheta5.JTP.AG
