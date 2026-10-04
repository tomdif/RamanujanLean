/-
# The second Göllnitz–Gordon identity

  `Σ_{n≥0} q^{n²+2n} (−q;q²)_n / (q²;q²)_n = 1/((q³;q⁸)_∞ (q⁴;q⁸)_∞ (q⁵;q⁸)_∞)`.

The proof is the `a = q²` analogue of `GollnitzGordon.lean`: Bailey's lemma in base `q²` relative to `a = q²` with
`ρ = −q` (so `aq/ρ = −q³`). Its inner sum is `inner_gg2`. It is applied to the second Rogers–Ramanujan pair in
base `q²`, and the resulting theta series is `J_{8,1}`.
-/
import RamanujanTau.GollnitzGordon2WZ
import RamanujanTau.GollnitzGordon

set_option autoImplicit false

namespace GG
open PowerSeries Finset MockTheta5.Bailey MockTheta5.JTP MockTheta5.JTP.RR
open RankProof (Ea Ea_X Pinf Pfin Pfin_succ X_pow_dvd_Pinf_sub X_pow_dvd_Pfin_sub Pinf_ext thetaS thA thB thetaTr
  thetaTr_eq thetaS_dvd jtp_ab)
open FourSquares (π π_eq_iff π_inverse π_X_pow)

/-- a Bailey pair relative to `a = q²` in base `q²`. -/
def IsBaileyPairQ2 (α β : ℕ → PowerSeries ℤ) : Prop :=
  ∀ n, β n = ∑ r ∈ range (n + 1), α r * Ring.inverse (Qf (n - r)) * Ring.inverse (Q2 (n + r))

lemma Ea2_q2fac (n : ℕ) : Ea 2 two_ne_zero (q2fac n) = Q2 n := by
  rw [q2fac, Q2, map_prod]
  refine prod_congr rfl fun i _ => ?_
  rw [map_sub, map_one, map_pow, Ea_X, ← pow_mul]; ring_nf

theorem isBaileyPairQ2_B : IsBaileyPairQ2 (fun r => Ea 2 two_ne_zero (alphaB r)) (fun n => Ring.inverse (Qf n)) := by
  intro n
  have h := congrArg (Ea 2 two_ne_zero) (isBaileyPairQ_B n)
  simp only at h
  rw [map_inverse' _ (isUnit_qfac n), Ea2_qfac, map_sum] at h
  show Ring.inverse (Qf n) = _
  rw [h]
  refine sum_congr rfl fun r _ => ?_
  rw [map_mul, map_mul, map_inverse' _ (isUnit_qfac _), map_inverse' _ (isUnit_q2fac _), Ea2_qfac, Ea2_q2fac]

/-! ## the chain step -/

noncomputable def rhoBetaQ (β : ℕ → PowerSeries ℤ) (n : ℕ) : PowerSeries ℤ :=
  Ring.inverse (M3 n) * ∑ j ∈ range (n + 1), Mq j * X ^ (j ^ 2 + 2 * j) * Ring.inverse (Qf (n - j)) * β j

noncomputable def rhoAlphaQ (α : ℕ → PowerSeries ℤ) (n : ℕ) : PowerSeries ℤ :=
  Mq n * X ^ (n ^ 2 + 2 * n) * Ring.inverse (M3 n) * α n

theorem isBaileyPairQ2_rho {α β : ℕ → PowerSeries ℤ} (h : IsBaileyPairQ2 α β) :
    IsBaileyPairQ2 (rhoAlphaQ α) (rhoBetaQ β) := by
  unfold IsBaileyPairQ2 at h
  intro n
  rw [rhoBetaQ]
  set T : ℕ → ℕ → PowerSeries ℤ := fun j r =>
    Mq j * X ^ (j ^ 2 + 2 * j) * Ring.inverse (Qf (n - j)) * (α r * Ring.inverse (Qf (j - r)) * Ring.inverse (Q2 (j + r)))
    with hT
  have hswap : ∑ j ∈ range (n + 1), Mq j * X ^ (j ^ 2 + 2 * j) * Ring.inverse (Qf (n - j)) * β j
      = ∑ r ∈ range (n + 1), α r * X ^ (r ^ 2 + 2 * r)
          * (Mq r * M3 n * Ring.inverse (M3 r * (Qf (n - r) * Q2 (n + r)))) := by
    calc ∑ j ∈ range (n + 1), Mq j * X ^ (j ^ 2 + 2 * j) * Ring.inverse (Qf (n - j)) * β j
        = ∑ j ∈ range (n + 1), ∑ r ∈ range (j + 1), T j r := by simp_rw [h, mul_sum, hT]
      _ = ∑ r ∈ Ico 0 (n + 1), ∑ j ∈ Ico r (n + 1), T j r := by
          rw [range_eq_Ico]; simp_rw [range_eq_Ico]
          exact (sum_Ico_Ico_comm 0 (n + 1) (fun r j => T j r)).symm
      _ = ∑ r ∈ range (n + 1), ∑ i ∈ range (n + 1 - r), T (r + i) r := by
          rw [← range_eq_Ico]; exact sum_congr rfl fun r _ => sum_Ico_eq_sum_range _ _ _
      _ = _ := by
          refine sum_congr rfl fun r hr => ?_
          rw [mem_range] at hr
          have hin := inner_gg2 r (n - r)
          rw [show n - r + 1 = n + 1 - r by omega, show r + (n - r) = n by omega,
            show 2 * r + (n - r) = n + r by omega] at hin
          rw [← hin, mul_sum]
          refine sum_congr rfl fun i hi => ?_
          rw [mem_range] at hi
          simp only [hT]
          rw [show n - (r + i) = n - r - i by omega, show r + i - r = i by omega, show r + i + r = 2 * r + i by ring,
            inv_mul3 _ _ _ (isUnit_Qf _) (isUnit_Qf _) (isUnit_Q2 _),
            show (r + i) ^ 2 + 2 * (r + i) = (r ^ 2 + 2 * r) + (2 * r * i + i ^ 2 + 2 * i) by ring, pow_add]
          ring
  rw [hswap, mul_sum]
  refine sum_congr rfl fun r _ => ?_
  have h1 := Ring.inverse_mul_cancel _ (isUnit_M3 n)
  rw [rhoAlphaQ, Ring.mul_inverse_rev' (Commute.all _ _), Ring.mul_inverse_rev' (Commute.all _ _)]
  linear_combination (α r * X ^ (r ^ 2 + 2 * r) * Mq r * Ring.inverse (Q2 (n + r)) * Ring.inverse (Qf (n - r))
    * Ring.inverse (M3 r)) * h1


/-! ## the transform -/

lemma Qf_succ_eq (k : ℕ) : Qf (k + 1) = (1 - X ^ 2) * Q2 k := by
  induction k with
  | zero => simp [Qf, Q2]
  | succ k ih => rw [Qf_succ, ih, Q2_succ]; ring_nf

lemma Mq_succ_eq (k : ℕ) : Mq (k + 1) = (1 + X) * M3 k := by
  induction k with
  | zero => simp [Mq, M3]
  | succ k ih => rw [Mq_succ, ih, M3_succ]; ring_nf

/-- **the `a = q²`, `ρ = −q` Bailey transform** in base `q²`. -/
theorem bailey_transform_rhoQ {α β : ℕ → PowerSeries ℤ} (h : IsBaileyPairQ2 α β) :
    tsumQsq (fun n => X ^ (2 * n) * (Mq n * β n))
      = Minf * (1 - X) * Ring.inverse Qinf2 * tsumQsq (fun n => X ^ (2 * n) * Mq n * Ring.inverse (M3 n) * α n) := by
  refine eq_of_dvd_all fun m => ?_
  rw [← π_eq_iff]
  set n := 2 * m + 2 with hn
  have hc := isBaileyPairQ2_rho h n
  rw [rhoBetaQ] at hc
  have hc' : ∑ j ∈ range (n + 1), Mq j * X ^ (j ^ 2 + 2 * j) * Ring.inverse (Qf (n - j)) * β j
      = M3 n * ∑ r ∈ range (n + 1), rhoAlphaQ α r * Ring.inverse (Qf (n - r)) * Ring.inverse (Q2 (n + r)) := by
    rw [← hc, ← mul_assoc, Ring.mul_inverse_cancel _ (isUnit_M3 n), one_mul]
  have hP := congrArg (π (m + 1)) hc'
  set I := Ring.inverse (π (m + 1) Qinf2) with hI
  have hQ : ∀ k, m + 1 ≤ k → π (m + 1) (Ring.inverse (Qf k)) = I := fun k hk => by
    rw [π_inverse (isUnit_Qf k), π_Qf hk]
  have hQ2 : ∀ k, m ≤ k → π (m + 1) (Ring.inverse (Q2 k)) = π (m + 1) (1 - X ^ 2) * I := fun k hk => by
    have e : Ring.inverse (Q2 k) = (1 - X ^ 2) * Ring.inverse (Qf (k + 1)) := by
      rw [Qf_succ_eq, Ring.mul_inverse_rev' (Commute.all _ _)]
      have := Ring.mul_inverse_cancel _ (FourSquares.isUnit_one_sub (m := 2) (by norm_num))
      linear_combination (-Ring.inverse (Q2 k)) * this
    rw [e, map_mul, hQ _ (by omega)]
  have hL := π_sum_split (m := m) (n := n) (by omega)
    (fun j => Mq j * X ^ (j ^ 2 + 2 * j) * Ring.inverse (Qf (n - j)) * β j) (fun j => X ^ (2 * j) * (Mq j * β j)) I
    (fun j hj => by
      show π (m + 1) (Mq j * X ^ (j ^ 2 + 2 * j) * Ring.inverse (Qf (n - j)) * β j) = _
      rw [show Mq j * X ^ (j ^ 2 + 2 * j) * Ring.inverse (Qf (n - j)) * β j
          = X ^ (j ^ 2) * (X ^ (2 * j) * (Mq j * β j)) * Ring.inverse (Qf (n - j)) by rw [pow_add]; ring,
        map_mul, hQ _ (by omega)])
    (fun j hj => by
      show π (m + 1) (Mq j * X ^ (j ^ 2 + 2 * j) * Ring.inverse (Qf (n - j)) * β j) = 0
      rw [show (X : PowerSeries ℤ) ^ (j ^ 2 + 2 * j) = X ^ (j ^ 2) * X ^ (2 * j) from pow_add _ _ _]
      simp only [map_mul, π_Xsq_zero hj, mul_zero, zero_mul])
  have hR := π_sum_split (m := m) (n := n) (by omega)
    (fun r => rhoAlphaQ α r * Ring.inverse (Qf (n - r)) * Ring.inverse (Q2 (n + r)))
    (fun r => X ^ (2 * r) * Mq r * Ring.inverse (M3 r) * α r) (I * (π (m + 1) (1 - X ^ 2) * I))
    (fun j hj => by
      show π (m + 1) (rhoAlphaQ α j * Ring.inverse (Qf (n - j)) * Ring.inverse (Q2 (n + j))) = _
      rw [rhoAlphaQ, map_mul, map_mul, hQ _ (by omega), hQ2 _ (by omega),
        show Mq j * X ^ (j ^ 2 + 2 * j) * Ring.inverse (M3 j) * α j
          = X ^ (j ^ 2) * (X ^ (2 * j) * Mq j * Ring.inverse (M3 j) * α j) by rw [pow_add]; ring]
      ring)
    (fun j hj => by
      show π (m + 1) (rhoAlphaQ α j * Ring.inverse (Qf (n - j)) * Ring.inverse (Q2 (n + j))) = 0
      rw [rhoAlphaQ, show (X : PowerSeries ℤ) ^ (j ^ 2 + 2 * j) = X ^ (j ^ 2) * X ^ (2 * j) from pow_add _ _ _]
      simp only [map_mul, π_Xsq_zero hj, mul_zero, zero_mul])
  have hM3 : π (m + 1) (M3 n) * π (m + 1) (1 + X) = π (m + 1) Minf := by
    rw [← map_mul, mul_comm, ← Mq_succ_eq, π_Mq (show m + 1 ≤ n + 1 by omega)]
  rw [hL, map_mul, hR] at hP
  have hu : I * π (m + 1) Qinf2 = 1 := Ring.inverse_mul_cancel _ (isUnit_Qinf2.map _)
  rw [map_mul, map_mul, map_mul, π_inverse isUnit_Qinf2]
  have hsq : π (m + 1) (1 - X ^ 2 : PowerSeries ℤ) = π (m + 1) (1 - X) * π (m + 1) (1 + X) := by
    rw [← map_mul]; ring_nf
  rw [hsq] at hP
  rw [← hM3]
  linear_combination π (m + 1) Qinf2 * hP
    - (π (m + 1) (tsumQsq fun n => X ^ (2 * n) * (Mq n * β n))
      - π (m + 1) (M3 n) * π (m + 1) (1 + X) * π (m + 1) (1 - X) * I
        * π (m + 1) (tsumQsq fun n => X ^ (2 * n) * Mq n * Ring.inverse (M3 n) * α n)) * hu


/-! ## GG2 -/

lemma Mq_div_M3 (r : ℕ) : Mq r * Ring.inverse (M3 r) = (1 + X) * Ring.inverse (1 + X ^ (2 * r + 1)) := by
  have e : Mq r * (1 + X ^ (2 * r + 1)) = (1 + X) * M3 r := by rw [← Mq_succ, Mq_succ_eq]
  have h1 := Ring.mul_inverse_cancel _ (isUnit_M3 r)
  have h2 := Ring.mul_inverse_cancel _ (FourSquares.isUnit_one_add (m := 2 * r + 1) (by omega))
  linear_combination (Ring.inverse (M3 r) * Ring.inverse (1 + X ^ (2 * r + 1))) * e
    - Mq r * Ring.inverse (M3 r) * h2 + (1 + X) * Ring.inverse (1 + X ^ (2 * r + 1)) * h1

lemma Ea2_geom (m : ℕ) : (1 - X ^ 2) * Ea 2 two_ne_zero (geom m) = 1 - X ^ (2 * m) := by
  have := congrArg (Ea 2 two_ne_zero) (geom_mul m)
  simp only [map_mul, map_sub, map_one, map_pow, Ea_X, ← pow_mul] at this
  rw [← this]

lemma term_val (r : ℕ) :
    (1 - X) * (X ^ (r ^ 2) * (X ^ (2 * r) * Mq r * Ring.inverse (M3 r) * Ea 2 two_ne_zero (alphaB r)))
      = (-1) ^ r * X ^ (r ^ 2 + 2 * r + 2 * (pentM r + r)) * (1 - X ^ (2 * r + 1)) := by
  have hG := Ea2_geom (2 * r + 1)
  have h2 := Ring.mul_inverse_cancel _ (FourSquares.isUnit_one_add (m := 2 * r + 1) (by omega))
  rw [mul_assoc (X ^ (2 * r)), Mq_div_M3, alphaB]
  simp only [map_mul, map_pow, map_neg, map_one, Ea_X, ← pow_mul]
  rw [show 2 * (2 * r + 1) = (2 * r + 1) + (2 * r + 1) by ring, pow_add] at hG
  rw [show (X : PowerSeries ℤ) ^ (r ^ 2 + 2 * r + 2 * (pentM r + r)) = X ^ (r ^ 2) * X ^ (2 * r) * X ^ ((pentM r + r) * 2) by
    rw [← pow_add, ← pow_add]; ring_nf]
  linear_combination (X ^ r ^ 2 * X ^ (2 * r) * (-1) ^ r * X ^ ((pentM r + r) * 2) * Ring.inverse (1 + X ^ (2 * r + 1))) * hG
    + ((-1) ^ r * X ^ r ^ 2 * X ^ (2 * r) * X ^ ((pentM r + r) * 2) * (1 - X ^ (2 * r + 1))) * h2

lemma term_gg2 (n : ℕ) :
    (1 - X) * (X ^ (n ^ 2) * (X ^ (2 * n) * Mq n * Ring.inverse (M3 n) * Ea 2 two_ne_zero (alphaB n)))
      = (if n = 0 then thA 8 1 0 else thB 8 1 (n - 1)) + thA 8 1 (n + 1) := by
  rw [term_val, pentM_eq]
  rcases n with _ | n
  · simp [RankProof.thA]; ring
  · rw [if_neg (by omega), Nat.add_sub_cancel]
    simp only [RankProof.thA, RankProof.thB]
    have h2 := two_choose (n + 1)
    have hc := RR.choose_two_succ (n + 1)
    have e1 : (n + 1) ^ 2 + 2 * (n + 1) + 2 * (3 * (n + 1).choose 2 + (n + 1) + (n + 1))
        = 8 * (n + 1).choose 2 + (8 - 1) * (n + 1) := by rw [← h2]; ring
    have e2 : (n + 1) ^ 2 + 2 * (n + 1) + 2 * (3 * (n + 1).choose 2 + (n + 1) + (n + 1)) + (2 * (n + 1) + 1)
        = 8 * (n + 1 + 1).choose 2 + 1 * (n + 1 + 1) := by rw [hc, ← h2]; ring
    rw [mul_sub, mul_one, mul_assoc, ← pow_add, e2, e1]
    simp only [map_mul, map_neg, map_pow, map_one, pow_add, pow_one]
    ring

lemma sum_term_gg2 (N : ℕ) :
    (1 - X) * ∑ n ∈ range (N + 1), X ^ (n ^ 2) * (X ^ (2 * n) * Mq n * Ring.inverse (M3 n) * Ea 2 two_ne_zero (alphaB n))
      = ∑ d ∈ range (N + 2), thA 8 1 d + ∑ d ∈ range N, thB 8 1 d := by
  induction N with
  | zero => rw [sum_range_one, term_gg2]; simp [sum_range_succ]
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih, term_gg2, if_neg (by omega), Nat.add_sub_cancel,
      sum_range_succ (thA _ _) (N + 2), sum_range_succ (thB _ _)]
    ring

theorem alphaB_gg_theta :
    (1 - X) * tsumQsq (fun n => X ^ (2 * n) * Mq n * Ring.inverse (M3 n) * Ea 2 two_ne_zero (alphaB n))
      = thetaS 8 1 := by
  refine eq_of_dvd_all fun N => ?_
  have h1 := dvd_mul_of_dvd_right
    (RR.tsumQsq_dvd (fun n => X ^ (2 * n) * Mq n * Ring.inverse (M3 n) * Ea 2 two_ne_zero (alphaB n)) N) (1 - X)
  rw [mul_sub, sum_term_gg2] at h1
  have h2 := thetaS_dvd 8 1 (by norm_num) (by norm_num) N
  rw [thetaTr_eq, sum_range_succ (thB _ _) N] at h2
  have h3 : (X : PowerSeries ℤ) ^ (N + 1) ∣ thA 8 1 (N + 1) := thA_deg _ 1 (N + 1) le_rfl
  have h4 : (X : PowerSeries ℤ) ^ (N + 1) ∣ thB 8 1 N := thB_deg _ 1 N (by norm_num)
  have := dvd_add (dvd_sub (dvd_sub h1 h2) h4) h3
  rw [sum_range_succ (thA _ _) (N + 1)] at this
  set T := tsumQsq (fun n => X ^ (2 * n) * Mq n * Ring.inverse (M3 n) * Ea 2 two_ne_zero (alphaB n))
  rw [show (1 - X) * T - (∑ d ∈ range (N + 1), thA 8 1 d + thA 8 1 (N + 1) + ∑ d ∈ range N, thB 8 1 d)
      - (thetaS 8 1 - (∑ d ∈ range (N + 1), thA 8 1 d + (∑ d ∈ range N, thB 8 1 d + thB 8 1 N))) - thB 8 1 N
      + thA 8 1 (N + 1) = (1 - X) * T - thetaS 8 1 by ring] at this
  exact this

/-- **The second Göllnitz–Gordon identity**:
`Σ_{n≥0} q^{n²+2n}(−q;q²)_n/(q²;q²)_n = 1/((q³;q⁸)_∞(q⁴;q⁸)_∞(q⁵;q⁸)_∞)`. -/
theorem gollnitz_gordon_2 :
    tsumQsq (fun n => X ^ (2 * n) * (Mq n * Ring.inverse (Qf n))) * (Pinf 3 8 * Pinf 4 8 * Pinf 5 8) = 1 := by
  rw [bailey_transform_rhoQ isBaileyPairQ2_B, show Minf * (1 - X) * Ring.inverse Qinf2
      * tsumQsq (fun n => X ^ (2 * n) * Mq n * Ring.inverse (M3 n) * Ea 2 two_ne_zero (alphaB n))
      = Minf * Ring.inverse Qinf2 * ((1 - X)
        * tsumQsq (fun n => X ^ (2 * n) * Mq n * Ring.inverse (M3 n) * Ea 2 two_ne_zero (alphaB n))) by ring,
    alphaB_gg_theta, ← jtp_ab 8 1 (by norm_num) (by norm_num), Qinf2_eq]
  have h22 : Pinf 2 2 = Pinf 2 4 * (Pinf 4 8 * Pinf 8 8) := by
    rw [Pinf_split_two (b := 2) (a := 2) (by norm_num) (by norm_num), Pinf_split_two (b := 4) (a := 4) (by norm_num) (by norm_num)]
  have h12 : Pinf 1 2 = (Pinf 1 8 * Pinf 5 8) * (Pinf 3 8 * Pinf 7 8) := by
    rw [Pinf_split_two (b := 1) (a := 2) (by norm_num) (by norm_num), Pinf_split_two (b := 1) (a := 4) (by norm_num) (by norm_num),
      Pinf_split_two (b := 3) (a := 4) (by norm_num) (by norm_num)]
  have hM := Minf_mul
  rw [h12] at hM
  rw [h22]
  norm_num
  have hu : IsUnit (Pinf 2 4 * (Pinf 4 8 * Pinf 8 8)) := by
    rw [← h22, ← Qinf2_eq]; exact isUnit_Qinf2
  have hinv := Ring.mul_inverse_cancel _ hu
  linear_combination (Ring.inverse (Pinf 2 4 * (Pinf 4 8 * Pinf 8 8)) * Pinf 4 8 * Pinf 8 8) * hM
    + hinv

end GG
