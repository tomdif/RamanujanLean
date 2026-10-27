/-
# The Andrews–Gordon identities for every `1 ≤ i ≤ k`

For `k ≥ 2` and `1 ≤ i ≤ k`:

  `Σ_{n₁ ≥ ⋯ ≥ n_{k−1} ≥ 0} q^{n₁²+⋯+n_{k−1}² + n_i+⋯+n_{k−1}} / ((q)_{n₁−n₂} ⋯ (q)_{n_{k−2}−n_{k−1}} (q)_{n_{k−1}})
     = ∏_{n ≢ 0, ±i (mod 2k+1)} 1/(1 − qⁿ)`.

`AndrewsGordon` covers `i = k` (the `a = 1` chain) and `i = 1` (the `a = q` chain). The intermediate `i` use
one step of the **Bailey lattice** (Agarwal–Andrews–Bressoud). A Bailey pair `(α, β)` relative to `a = q` is
also a pair `(α°, β)` relative to `a = 1`, with the same `β` and

  `α°_r = (1−q)(α_r/(1−q^{2r+1}) − q^{2r−1} α_{r−1}/(1−q^{2r−1}))`   (`isBaileyPair_toOne`).

This comes from the partial fraction

  `1/((q)_{n−r}(q)_{n+r+1}) = [1/((q)_{n−r}(q)_{n+r}) − q^{2r+1}/((q)_{n−r−1}(q)_{n+r+1})]/(1−q^{2r+1})`.

So the steps are: `k − i` steps of the `a = q` chain from the RR2 pair (these give the linear terms on the
innermost `k − i` variables), the switch to `a = 1`, then `i − 2` steps of the `a = 1` chain, and finally the
Bailey transform. On the `α` side, `q^{(i−1)n²}α°_n` is exactly the `n`-th term of the two-sided theta series
`Σ_{n∈ℤ} (−1)ⁿ q^{(2k+1)n(n−1)/2 + in}`, so the Jacobi triple product finishes.
-/
import RamanujanTau.AndrewsGordon

set_option autoImplicit false

namespace MockTheta5.JTP.AG
open PowerSeries Finset MockTheta5.Bailey MockTheta5.JTP MockTheta5.JTP.RR
open RankProof (Pinf Pfin Pfin_succ X_pow_dvd_Pfin_sub X_pow_dvd_Pinf_sub Pinf_ext Pinf_one_one thetaS thA thB
  thetaTr thetaTr_eq thetaS_dvd jtp_ab)

/-! ## the switch from `a = q` to `a = 1` -/

lemma isUnit_one_sub_X_pow {m : ℕ} (hm : 1 ≤ m) : IsUnit (1 - X ^ m : PowerSeries ℤ) := by
  rw [isUnit_iff_constantCoeff]; simp [zero_pow (by omega : m ≠ 0)]

lemma inverse_eq_of_mul {B C D : PowerSeries ℤ} (hC : IsUnit C) (hB : IsUnit B) (h : B = C * D) :
    Ring.inverse C = D * Ring.inverse B := by
  calc Ring.inverse C = Ring.inverse C * (B * Ring.inverse B) := by rw [Ring.mul_inverse_cancel _ hB, mul_one]
    _ = (Ring.inverse C * C) * D * Ring.inverse B := by rw [h]; ring
    _ = D * Ring.inverse B := by rw [Ring.inverse_mul_cancel _ hC, one_mul]

/-- `T_r = (1−q)α_r/(1−q^{2r+1})`. -/
noncomputable def toOneT (α : ℕ → PowerSeries ℤ) (r : ℕ) : PowerSeries ℤ :=
  (1 - X) * Ring.inverse (1 - X ^ (2 * r + 1)) * α r

/-- the switched `α°_r = T_r − q^{2r−1}T_{r−1}`. -/
noncomputable def toOne (α : ℕ → PowerSeries ℤ) (r : ℕ) : PowerSeries ℤ :=
  toOneT α r - if r = 0 then 0 else X ^ (2 * r - 1) * toOneT α (r - 1)

/-- the partial fraction, for `r ≤ n`. -/
lemma partial_frac (n r : ℕ) (hr : r ≤ n) :
    Ring.inverse (qfac (n - r)) * Ring.inverse (q2fac (n + r)) =
      (1 - X) * Ring.inverse (1 - X ^ (2 * r + 1)) *
        (Ring.inverse (qfac (n - r)) * Ring.inverse (qfac (n + r)) -
          if r < n then X ^ (2 * r + 1) * (Ring.inverse (qfac (n - (r + 1))) * Ring.inverse (qfac (n + (r + 1))))
          else 0) := by
  have hu : Ring.inverse (1 - X ^ (2 * r + 1) : PowerSeries ℤ) * (1 - X ^ (2 * r + 1)) = 1 :=
    Ring.inverse_mul_cancel _ (isUnit_one_sub_X_pow (by omega))
  have e1 : Ring.inverse (q2fac (n + r)) = (1 - X) * Ring.inverse (qfac (n + r + 1)) :=
    inverse_eq_of_mul (isUnit_q2fac _) (isUnit_qfac _) (qfac_succ_eq_q2fac _)
  have e2 : Ring.inverse (qfac (n + r)) = (1 - X ^ (n + r + 1)) * Ring.inverse (qfac (n + r + 1)) :=
    inverse_eq_of_mul (isUnit_qfac _) (isUnit_qfac _) (qfac_succ _)
  rcases Nat.lt_or_ge r n with hlt | hge
  · obtain ⟨d, rfl⟩ : ∃ d, n = r + 1 + d := ⟨n - r - 1, by omega⟩
    rw [if_pos hlt, show r + 1 + d - (r + 1) = d by omega, show r + 1 + d - r = d + 1 by omega,
      show r + 1 + d + (r + 1) = r + 1 + d + r + 1 by omega]
    have e3 : Ring.inverse (qfac d) = (1 - X ^ (d + 1)) * Ring.inverse (qfac (d + 1)) :=
      inverse_eq_of_mul (isUnit_qfac _) (isUnit_qfac _) (qfac_succ _)
    rw [e1, e2, e3]
    have hx : (X : PowerSeries ℤ) ^ (2 * r + 1) * X ^ (d + 1) = X ^ (r + 1 + d + r + 1) := by
      rw [← pow_add]; congr 1; ring
    linear_combination (-(1 - X) * Ring.inverse (qfac (d + 1)) * Ring.inverse (qfac (r + 1 + d + r + 1))) * hu
      + ((1 - X) * Ring.inverse (1 - X ^ (2 * r + 1)) * Ring.inverse (qfac (d + 1)) *
        Ring.inverse (qfac (r + 1 + d + r + 1))) * hx
  · obtain rfl : r = n := le_antisymm hr hge
    rw [if_neg (lt_irrefl _), Nat.sub_self, qfac_zero, Ring.inverse_one, e1, e2,
      show r + r + 1 = 2 * r + 1 by ring]
    linear_combination (-(1 - X) * Ring.inverse (qfac (2 * r + 1))) * hu

/-- **the Bailey-lattice switch**: an `a = q` pair `(α, β)` gives the `a = 1` pair `(α°, β)`. -/
theorem isBaileyPair_toOne {α β : ℕ → PowerSeries ℤ} (h : IsBaileyPairQ α β) : IsBaileyPair (toOne α) β := by
  intro n
  rw [h n]
  have hL : ∀ r ∈ range (n + 1), α r * Ring.inverse (qfac (n - r)) * Ring.inverse (q2fac (n + r)) =
      toOneT α r * (Ring.inverse (qfac (n - r)) * Ring.inverse (qfac (n + r))) -
        if r < n then X ^ (2 * r + 1) * toOneT α r *
          (Ring.inverse (qfac (n - (r + 1))) * Ring.inverse (qfac (n + (r + 1)))) else 0 := by
    intro r hr
    rw [mul_assoc, partial_frac n r (by have := mem_range.mp hr; omega), toOneT]
    split_ifs <;> ring
  rw [sum_congr rfl hL, sum_sub_distrib, sum_range_succ (fun r => if r < n then X ^ (2 * r + 1) * toOneT α r *
      (Ring.inverse (qfac (n - (r + 1))) * Ring.inverse (qfac (n + (r + 1)))) else 0), if_neg (lt_irrefl n),
    add_zero, sum_ite_of_true (s := range n) (p := fun r => r < n) (fun r hr => mem_range.mp hr)]
  simp only [toOne, sub_mul, sum_sub_distrib]
  congr 1
  · exact sum_congr rfl fun r _ => by ring
  · rw [sum_range_succ', if_pos rfl]
    simp only [zero_mul, add_zero]
    refine sum_congr rfl fun r _ => ?_
    rw [if_neg (Nat.succ_ne_zero r), show 2 * (r + 1) - 1 = 2 * r + 1 by omega, Nat.add_sub_cancel]
    ring

/-! ## the `i`-family: `k − i` steps at `a = q`, switch, `i − 2` steps at `a = 1` -/

/-- `β` for `s = k − i` steps at `a = q`, then `t = i − 2` steps at `a = 1`. -/
noncomputable def agBetaI (s : ℕ) : ℕ → ℕ → PowerSeries ℤ
  | 0 => agBetaQ s
  | t + 1 => chainBeta (agBetaI s t)

noncomputable def agAlphaI (s : ℕ) : ℕ → ℕ → PowerSeries ℤ
  | 0 => toOne (agAlphaQ s)
  | t + 1 => chainAlpha (agAlphaI s t)

lemma isBaileyPair_agI (s t : ℕ) : IsBaileyPair (agAlphaI s t) (agBetaI s t) := by
  induction t with
  | zero => exact isBaileyPair_toOne (isBaileyPairQ_ag s)
  | succ t ih => exact isBaileyPair_chain ih

lemma agAlphaI_eq (s t n : ℕ) : agAlphaI s t n = X ^ (t * n ^ 2) * toOne (agAlphaQ s) n := by
  induction t with
  | zero => simp [agAlphaI]
  | succ t ih => rw [agAlphaI, chainAlpha, ih, ← mul_assoc, ← pow_add]; ring_nf

lemma toOneT_agQ (s r : ℕ) : toOneT (agAlphaQ s) r = (-1) ^ r * X ^ (s * (r ^ 2 + r) + (pentM r + r)) := by
  rw [toOneT, agAlphaQ_eq, alphaB]
  have hg := geom_mul (2 * r + 1)
  have hu : Ring.inverse (1 - X ^ (2 * r + 1) : PowerSeries ℤ) * (1 - X ^ (2 * r + 1)) = 1 :=
    Ring.inverse_mul_cancel _ (isUnit_one_sub_X_pow (by omega))
  calc (1 - X) * Ring.inverse (1 - X ^ (2 * r + 1)) * (X ^ (s * (r ^ 2 + r)) * ((-1) ^ r * X ^ (pentM r + r) *
        geom (2 * r + 1)))
      = (-1) ^ r * X ^ (s * (r ^ 2 + r)) * X ^ (pentM r + r) *
          (Ring.inverse (1 - X ^ (2 * r + 1)) * ((1 - X) * geom (2 * r + 1))) := by ring
    _ = (-1) ^ r * X ^ (s * (r ^ 2 + r) + (pentM r + r)) := by rw [hg, hu]; ring

lemma term_agI (s t n : ℕ) :
    X ^ (n ^ 2) * agAlphaI s t n =
      thA (2 * s + 2 * t + 5) (t + 2) n + (if n = 0 then 0 else thB (2 * s + 2 * t + 5) (t + 2) (n - 1)) := by
  rw [agAlphaI_eq, toOne]
  rcases n with _ | m
  · simp [toOneT_agQ, pentM, RankProof.thA]
  · rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel, toOneT_agQ, toOneT_agQ,
      show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
    simp only [RankProof.thA, RankProof.thB]
    have h2 := two_choose m
    have hc : (m + 1).choose 2 = m.choose 2 + m := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    have hp := pentM_eq m
    have hp1 : pentM (m + 1) = pentM m + (3 * m + 1) := rfl
    have hsq : (m + 1) ^ 2 = 2 * m.choose 2 + 3 * m + 1 := by rw [show (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 by ring, ← h2]; ring
    have e1 : (m + 1) ^ 2 + (t * (m + 1) ^ 2 + (s * ((m + 1) ^ 2 + (m + 1)) + (pentM (m + 1) + (m + 1)))) =
        (2 * s + 2 * t + 5) * (m + 1).choose 2 + (2 * s + 2 * t + 5 - (t + 2)) * (m + 1) := by
      rw [show 2 * s + 2 * t + 5 - (t + 2) = 2 * s + t + 3 by omega, hc, hp1, hp, hsq]; ring
    have e2 : (m + 1) ^ 2 + (t * (m + 1) ^ 2 + (2 * m + 1 + (s * (m ^ 2 + m) + (pentM m + m)))) =
        (2 * s + 2 * t + 5) * (m + 1).choose 2 + (t + 2) * (m + 1) := by
      rw [hc, hp, hsq, ← h2]; ring
    rw [← e1, ← e2]
    simp only [map_mul, map_neg, map_pow, map_one, pow_add, pow_one]
    ring

lemma sum_term_agI (s t N : ℕ) :
    ∑ n ∈ range (N + 1), X ^ (n ^ 2) * agAlphaI s t n
      = ∑ d ∈ range (N + 1), thA (2 * s + 2 * t + 5) (t + 2) d +
          ∑ d ∈ range N, thB (2 * s + 2 * t + 5) (t + 2) d := by
  induction N with
  | zero => simp [term_agI]
  | succ N ih =>
    rw [sum_range_succ, ih, term_agI, if_neg (by omega), Nat.add_sub_cancel, sum_range_succ (thA _ _) (N + 1),
      sum_range_succ (thB _ _) N]
    ring

theorem agAlphaI_theta (s t : ℕ) : tsumQsq (agAlphaI s t) = thetaS (2 * s + 2 * t + 5) (t + 2) := by
  refine eq_of_dvd_all fun N => ?_
  have h1 := RR.tsumQsq_dvd (agAlphaI s t) N
  have h2 := thetaS_dvd (2 * s + 2 * t + 5) (t + 2) (by omega) (by omega) N
  rw [sum_term_agI] at h1
  have h3 : (X : PowerSeries ℤ) ^ (N + 1) ∣ thB (2 * s + 2 * t + 5) (t + 2) N := thB_deg _ _ N (by omega)
  rw [thetaTr_eq, sum_range_succ (thB _ _)] at h2
  have := dvd_sub (dvd_sub h1 h2) h3
  rw [show tsumQsq (agAlphaI s t) - (∑ d ∈ range (N + 1), thA (2 * s + 2 * t + 5) (t + 2) d
        + ∑ d ∈ range N, thB (2 * s + 2 * t + 5) (t + 2) d)
      - (thetaS (2 * s + 2 * t + 5) (t + 2) - (∑ d ∈ range (N + 1), thA (2 * s + 2 * t + 5) (t + 2) d
        + (∑ d ∈ range N, thB (2 * s + 2 * t + 5) (t + 2) d + thB (2 * s + 2 * t + 5) (t + 2) N)))
      - thB (2 * s + 2 * t + 5) (t + 2) N
      = tsumQsq (agAlphaI s t) - thetaS (2 * s + 2 * t + 5) (t + 2) by ring] at this
  exact this

/-- **The Andrews–Gordon identities, `2 ≤ i ≤ k`** (`k = s + t + 2`, `i = t + 2`): the multisum
`Σ q^{n²} β_n`, built from `s = k − i` steps of the `a = q` chain then `t = i − 2` steps of the `a = 1` chain,
equals `∏_{n ≢ 0, ±i (mod 2k+1)} 1/(1 − qⁿ)`. With `andrews_gordon_one` (`i = 1`) this is the full family. -/
theorem andrews_gordon_i (s t : ℕ) : tsumQsq (agBetaI s t) * agProd (2 * s + 2 * t + 5) (t + 2) = 1 := by
  set a := 2 * s + 2 * t + 5
  set b := t + 2
  rw [bailey_transform (isBaileyPair_agI s t), agAlphaI_theta, ← jtp_ab a b (by omega) (by omega)]
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

end MockTheta5.JTP.AG
