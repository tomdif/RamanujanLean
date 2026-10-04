/-
# The Andrews–Gordon identities (the `i = k` family)

For every `k ≥ 2`:

  `Σ_{n₁ ≥ ⋯ ≥ n_{k−1} ≥ 0} q^{n₁²+⋯+n_{k−1}²} / ((q)_{n₁−n₂} ⋯ (q)_{n_{k−2}−n_{k−1}} (q)_{n_{k−1}})
     = ∏_{n ≢ 0, ±k (mod 2k+1)} 1/(1 − qⁿ)`.

`k = 2` is the first Rogers–Ramanujan identity. The proof is Andrews's Bailey chain: start from the
Rogers–Ramanujan pair `(αₙ, 1/(q)_n)` (`isBaileyPair_C`) and apply the limiting Bailey lemma
(`isBaileyPair_chain`) `k − 2` times. The `β` side builds the multisum and the `α` side becomes `q^{(k−2)n²} αₙ`.
The Bailey transform then gives `(1/(q)_∞) Σ q^{(k−1)n²} αₙ`, which is the Jacobi triple product
`J_{2k+1,k}/(q)_∞`.
-/
import RamanujanTau.RogersRamanujan

set_option autoImplicit false

namespace MockTheta5.JTP.AG
open PowerSeries Finset MockTheta5.Bailey MockTheta5.JTP MockTheta5.JTP.RR
open RankProof (Pinf Pfin Pfin_succ X_pow_dvd_Pfin_sub X_pow_dvd_Pinf_sub Pinf_ext Pinf_one_one thetaS thA thB
  thetaTr thetaTr_eq thetaS_dvd jtp_ab)

/-- the `β` side after `j` chain steps: `β⁽⁰⁾ₙ = 1/(q)_n`, `β⁽ʲ⁺¹⁾ₙ = Σ_{m ≤ n} q^{m²}/(q)_{n−m} β⁽ʲ⁾_m`. -/
noncomputable def agBeta : ℕ → ℕ → PowerSeries ℤ
  | 0 => fun n => Ring.inverse (qfac n)
  | j + 1 => chainBeta (agBeta j)

/-- the `α` side after `j` chain steps. -/
noncomputable def agAlpha : ℕ → ℕ → PowerSeries ℤ
  | 0 => alphaC
  | j + 1 => chainAlpha (agAlpha j)

lemma agAlpha_eq (j n : ℕ) : agAlpha j n = X ^ (j * n ^ 2) * alphaC n := by
  induction j with
  | zero => simp [agAlpha]
  | succ j ih => rw [agAlpha, chainAlpha, ih, ← mul_assoc, ← pow_add]; ring_nf

lemma isBaileyPair_ag (j : ℕ) : IsBaileyPair (agAlpha j) (agBeta j) := by
  induction j with
  | zero => exact isBaileyPair_C
  | succ j ih => exact isBaileyPair_chain ih

/-! ## the theta side: `Σ q^{(j+1)n²} αₙ = J_{2j+5, j+2}` -/

lemma term_ag (j n : ℕ) :
    X ^ (n ^ 2) * agAlpha j n = thA (2 * j + 5) (j + 2) n + (if n = 0 then 0 else thB (2 * j + 5) (j + 2) (n - 1)) := by
  rw [agAlpha_eq]
  rcases n with _ | n
  · simp [alphaC, RankProof.thA]
  · rw [alphaC, if_neg (by omega), if_neg (by omega), RankProof.thA, RankProof.thB, Nat.add_sub_cancel, Apent_eq]
    have h2 := two_choose (n + 1)
    have e1 : (n + 1) ^ 2 + (j * (n + 1) ^ 2 + (3 * (n + 1).choose 2 + (n + 1)))
        = (2 * j + 5) * (n + 1).choose 2 + (j + 2) * (n + 1) := by
      rw [← h2]; ring
    have e2 : (n + 1) ^ 2 + (j * (n + 1) ^ 2 + (3 * (n + 1).choose 2 + (n + 1))) + (n + 1)
        = (2 * j + 5) * (n + 1).choose 2 + (2 * j + 5 - (j + 2)) * (n + 1) := by
      rw [show 2 * j + 5 - (j + 2) = j + 3 by omega, ← h2]; ring
    rw [← e1, ← e2]
    simp only [map_mul, map_neg, map_pow, map_one, pow_add, pow_one]
    ring

lemma sum_term_ag (j N : ℕ) :
    ∑ n ∈ range (N + 1), X ^ (n ^ 2) * agAlpha j n
      = ∑ d ∈ range (N + 1), thA (2 * j + 5) (j + 2) d + ∑ d ∈ range N, thB (2 * j + 5) (j + 2) d := by
  induction N with
  | zero => simp [term_ag]
  | succ N ih =>
    rw [sum_range_succ, ih, term_ag, if_neg (by omega), Nat.add_sub_cancel, sum_range_succ (thA _ _) (N + 1),
      sum_range_succ (thB _ _) N]
    ring

theorem agAlpha_theta (j : ℕ) : tsumQsq (agAlpha j) = thetaS (2 * j + 5) (j + 2) := by
  refine eq_of_dvd_all fun N => ?_
  have h1 := RR.tsumQsq_dvd (agAlpha j) N
  have h2 := thetaS_dvd (2 * j + 5) (j + 2) (by omega) (by omega) N
  rw [sum_term_ag] at h1
  have h3 : (X : PowerSeries ℤ) ^ (N + 1) ∣ thB (2 * j + 5) (j + 2) N := thB_deg _ _ N (by omega)
  rw [thetaTr_eq, sum_range_succ (thB _ _)] at h2
  have := dvd_sub (dvd_sub h1 h2) h3
  rw [show tsumQsq (agAlpha j) - (∑ d ∈ range (N + 1), thA (2 * j + 5) (j + 2) d + ∑ d ∈ range N, thB (2 * j + 5) (j + 2) d)
      - (thetaS (2 * j + 5) (j + 2) - (∑ d ∈ range (N + 1), thA (2 * j + 5) (j + 2) d
        + (∑ d ∈ range N, thB (2 * j + 5) (j + 2) d + thB (2 * j + 5) (j + 2) N))) - thB (2 * j + 5) (j + 2) N
      = tsumQsq (agAlpha j) - thetaS (2 * j + 5) (j + 2) by ring] at this
  exact this

/-! ## `(q;q)_∞ = ∏_{r=1}^{a} (q^r;q^a)_∞` -/

lemma Pfin_split (a : ℕ) : ∀ N, Pfin 1 1 (a * N) = ∏ r ∈ range a, Pfin (r + 1) a N
  | 0 => by simp [Pfin]
  | N + 1 => by
    rw [show a * (N + 1) = a * N + a by ring, Pfin, prod_range_add, ← Pfin, Pfin_split a N]
    simp only [Pfin_succ, prod_mul_distrib]
    congr 1
    refine prod_congr rfl fun r _ => ?_
    congr 2; ring

theorem Pinf_split (a : ℕ) (ha : 1 ≤ a) : Pinf 1 1 = ∏ r ∈ range a, Pinf (r + 1) a := by
  symm
  refine Pinf_ext le_rfl le_rfl fun N => ?_
  have h1 : (X : PowerSeries ℤ) ^ (N + 1) ∣ ∏ r ∈ range a, Pinf (r + 1) a - ∏ r ∈ range a, Pfin (r + 1) a N :=
    dvd_sub_prod' _ _ fun r _ => X_pow_dvd_Pinf_sub (r + 1) a (by omega) ha N
  have h2 := X_pow_dvd_Pfin_sub 1 1 N le_rfl le_rfl (a * N) (Nat.le_mul_of_pos_left N ha)
  rw [Pfin_split] at h2
  have := dvd_add h1 h2
  rwa [sub_add_sub_cancel] at this

/-- the product `∏_{n ≢ 0, ±b (mod a)} (1 − qⁿ)`. -/
noncomputable def agProd (a b : ℕ) : PowerSeries ℤ :=
  ∏ r ∈ (range a).filter (fun r => r + 1 ≠ b ∧ r + 1 ≠ a - b ∧ r + 1 ≠ a), Pinf (r + 1) a

/-- **The Andrews–Gordon identities** (`i = k`, `k = j + 2 ≥ 2`): the `(k−1)`-fold multisum `Σ q^{n²} β⁽ᵏ⁻²⁾ₙ` equals
`∏_{n ≢ 0, ±k (mod 2k+1)} 1/(1 − qⁿ)`. -/
theorem andrews_gordon (j : ℕ) : tsumQsq (agBeta j) * agProd (2 * j + 5) (j + 2) = 1 := by
  set a := 2 * j + 5
  set b := j + 2
  rw [bailey_transform (isBaileyPair_ag j), agAlpha_theta, ← jtp_ab a b (by omega) (by omega)]
  have hs := Pinf_split a (by omega)
  rw [Pinf_one_one] at hs
  -- split off the three excluded classes `b, a − b, a`
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


/-! ## the `i = 1` family, via the `a = q` Bailey chain -/

/-- `β` after `j` steps of the `a = q` chain from the RR2 pair. -/
noncomputable def agBetaQ : ℕ → ℕ → PowerSeries ℤ
  | 0 => fun n => Ring.inverse (qfac n)
  | j + 1 => chainBetaQ (agBetaQ j)

noncomputable def agAlphaQ : ℕ → ℕ → PowerSeries ℤ
  | 0 => alphaB
  | j + 1 => chainAlphaQ (agAlphaQ j)

lemma agAlphaQ_eq (j n : ℕ) : agAlphaQ j n = X ^ (j * (n ^ 2 + n)) * alphaB n := by
  induction j with
  | zero => simp [agAlphaQ]
  | succ j ih => rw [agAlphaQ, chainAlphaQ, ih, ← mul_assoc, ← pow_add]; ring_nf

lemma isBaileyPairQ_ag (j : ℕ) : IsBaileyPairQ (agAlphaQ j) (agBetaQ j) := by
  induction j with
  | zero => exact isBaileyPairQ_B
  | succ j ih => exact isBaileyPairQ_chain ih

lemma term_agQ (j n : ℕ) :
    (1 - X) * (X ^ (n ^ 2 + n) * agAlphaQ j n)
      = (if n = 0 then thA (2 * j + 5) 1 0 else thB (2 * j + 5) 1 (n - 1)) + thA (2 * j + 5) 1 (n + 1) := by
  rw [agAlphaQ_eq]
  have hg := geom_mul (2 * n + 1)
  rw [alphaB, show (1 - X) * (X ^ (n ^ 2 + n) * (X ^ (j * (n ^ 2 + n)) * ((-1) ^ n * X ^ (pentM n + n) * geom (2 * n + 1))))
      = X ^ (n ^ 2 + n) * (X ^ (j * (n ^ 2 + n)) * ((-1) ^ n * X ^ (pentM n + n) * ((1 - X) * geom (2 * n + 1)))) by ring,
    hg, pentM_eq]
  rcases n with _ | n
  · simp [RankProof.thA]; ring
  · rw [if_neg (by omega), Nat.add_sub_cancel]
    simp only [RankProof.thA, RankProof.thB]
    have h2 := two_choose (n + 1)
    have hc := RR.choose_two_succ (n + 1)
    have e1 : (n + 1) ^ 2 + (n + 1) + (j * ((n + 1) ^ 2 + (n + 1)) + (3 * (n + 1).choose 2 + (n + 1) + (n + 1)))
        = (2 * j + 5) * (n + 1).choose 2 + (2 * j + 5 - 1) * (n + 1) := by
      rw [show 2 * j + 5 - 1 = 2 * j + 4 by omega, ← h2]; ring
    have e2 : (n + 1) ^ 2 + (n + 1) + (j * ((n + 1) ^ 2 + (n + 1)) + (3 * (n + 1).choose 2 + (n + 1) + (n + 1)))
        + (2 * (n + 1) + 1) = (2 * j + 5) * (n + 1 + 1).choose 2 + 1 * (n + 1 + 1) := by
      rw [hc, ← h2]; ring
    rw [← e1, ← e2]
    simp only [map_mul, map_neg, map_pow, map_one, pow_add, pow_one]
    ring

lemma sum_term_agQ (j N : ℕ) :
    (1 - X) * ∑ n ∈ range (N + 1), X ^ (n ^ 2 + n) * agAlphaQ j n
      = ∑ d ∈ range (N + 2), thA (2 * j + 5) 1 d + ∑ d ∈ range N, thB (2 * j + 5) 1 d := by
  induction N with
  | zero => rw [sum_range_one, term_agQ]; simp [sum_range_succ]
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih, term_agQ, if_neg (by omega), Nat.add_sub_cancel,
      sum_range_succ (thA _ _) (N + 2), sum_range_succ (thB _ _)]
    ring

theorem agAlphaQ_theta (j : ℕ) : (1 - X) * tsumQsqQ (agAlphaQ j) = thetaS (2 * j + 5) 1 := by
  refine eq_of_dvd_all fun N => ?_
  have h1 := dvd_mul_of_dvd_right (RR.tsumQsqQ_dvd (agAlphaQ j) N) (1 - X)
  rw [mul_sub, sum_term_agQ] at h1
  have h2 := thetaS_dvd (2 * j + 5) 1 (by norm_num) (by omega) N
  rw [thetaTr_eq, sum_range_succ (thB _ _) N] at h2
  have h3 : (X : PowerSeries ℤ) ^ (N + 1) ∣ thA (2 * j + 5) 1 (N + 1) := thA_deg _ 1 (N + 1) le_rfl
  have h4 : (X : PowerSeries ℤ) ^ (N + 1) ∣ thB (2 * j + 5) 1 N := thB_deg _ 1 N (by omega)
  have := dvd_add (dvd_sub (dvd_sub h1 h2) h4) h3
  rw [sum_range_succ (thA _ _) (N + 1)] at this
  rw [show (1 - X) * tsumQsqQ (agAlphaQ j) - (∑ d ∈ range (N + 1), thA (2 * j + 5) 1 d + thA (2 * j + 5) 1 (N + 1)
      + ∑ d ∈ range N, thB (2 * j + 5) 1 d) - (thetaS (2 * j + 5) 1 - (∑ d ∈ range (N + 1), thA (2 * j + 5) 1 d
      + (∑ d ∈ range N, thB (2 * j + 5) 1 d + thB (2 * j + 5) 1 N))) - thB (2 * j + 5) 1 N + thA (2 * j + 5) 1 (N + 1)
      = (1 - X) * tsumQsqQ (agAlphaQ j) - thetaS (2 * j + 5) 1 by ring] at this
  exact this

/-- **The Andrews–Gordon identities, `i = 1`** (`k = j + 2 ≥ 2`):
`Σ q^{n₁²+⋯+n_{k−1}² + n₁+⋯+n_{k−1}}/((q)_{n₁−n₂}⋯(q)_{n_{k−1}}) = ∏_{n ≢ 0, ±1 (mod 2k+1)} 1/(1 − qⁿ)`.
`k = 2` is the second Rogers–Ramanujan identity. -/
theorem andrews_gordon_one (j : ℕ) : tsumQsqQ (agBetaQ j) * agProd (2 * j + 5) 1 = 1 := by
  set a := 2 * j + 5
  rw [bailey_transform_q (isBaileyPairQ_ag j), show (1 - X) * partitionGF * tsumQsqQ (agAlphaQ j)
      = partitionGF * ((1 - X) * tsumQsqQ (agAlphaQ j)) by ring, agAlphaQ_theta, ← jtp_ab a 1 le_rfl (by omega)]
  have hs := Pinf_split a (by omega)
  rw [Pinf_one_one] at hs
  have hprod : ∏ r ∈ range a, Pinf (r + 1) a = Pinf 1 a * Pinf (a - 1) a * Pinf a a * agProd a 1 := by
    rw [agProd, ← prod_filter_mul_prod_filter_not (range a) (fun r => r + 1 ≠ 1 ∧ r + 1 ≠ a - 1 ∧ r + 1 ≠ a)]
    have hn : (range a).filter (fun r => ¬ (r + 1 ≠ 1 ∧ r + 1 ≠ a - 1 ∧ r + 1 ≠ a)) = {0, a - 1 - 1, a - 1} := by
      ext r; simp only [mem_filter, mem_range, mem_insert, mem_singleton]; omega
    rw [hn, prod_insert (by simp; omega), prod_insert (by simp; omega), prod_singleton,
      show a - 1 - 1 + 1 = a - 1 by omega, show a - 1 + 1 = a by omega]
    ring
  rw [← hs] at hprod
  rw [show partitionGF * (Pinf 1 a * Pinf (a - 1) a * Pinf a a) * agProd a 1
      = partitionGF * (Pinf 1 a * Pinf (a - 1) a * Pinf a a * agProd a 1) by ring, ← hprod]
  exact Ring.inverse_mul_cancel _ isUnit_qfacInf

end MockTheta5.JTP.AG
