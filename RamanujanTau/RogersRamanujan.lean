/-
# The Rogers–Ramanujan identities (product forms)

  `Σ_{n≥0} q^{n²}/(q;q)_n = 1/((q;q⁵)_∞ (q⁴;q⁵)_∞)`,   `Σ_{n≥0} q^{n²+n}/(q;q)_n = 1/((q²;q⁵)_∞ (q³;q⁵)_∞)`.

The Bailey-transform forms `rogersRamanujan1_transform` and `rogersRamanujan2_transform` reduce these to the
theta series `Σ q^{n²}αₙ` and `(1−q)Σ q^{n²+n}αₙ`. Those series are the Jacobi triple products
`J_{5,2} = Σ_m (−1)^m q^{m(5m−1)/2}` and `J_{5,1} = Σ_m (−1)^m q^{m(5m−3)/2}`, already proved as `jtp_ab`. The
quintuple product is not needed. The residue split `(q;q)_∞ = ∏_{r=1}^{5} (q^r;q⁵)_∞` then cancels the denominator.
-/
import RamanujanTau.RankTheta
import RamanujanTau.MockTheta5BaileyRR1
import RamanujanTau.MockTheta5BaileyQPairB

set_option autoImplicit false

namespace MockTheta5.JTP.RR
open PowerSeries Finset MockTheta5.Bailey
open RankProof (Pinf Pfin Pfin_succ X_pow_dvd_Pfin_sub X_pow_dvd_Pinf_sub Pinf_ext Pinf_one_one thetaS thA thB
  thetaTr thetaTr_eq thetaS_dvd jtp_ab)

lemma coeff_eq_of_dvd {f g : PowerSeries ℤ} {K k : ℕ} (h : (X : PowerSeries ℤ) ^ K ∣ f - g) (hk : k < K) :
    coeff k f = coeff k g := by
  have := (PowerSeries.X_pow_dvd_iff.mp h) k hk
  rwa [map_sub, sub_eq_zero] at this

lemma eq_of_dvd_all {f g : PowerSeries ℤ} (h : ∀ N, (X : PowerSeries ℤ) ^ (N + 1) ∣ f - g) : f = g := by
  ext k; exact coeff_eq_of_dvd (h k) (Nat.lt_succ_self k)

lemma dvd_sub_prod' {d : PowerSeries ℤ} {s : Finset ℕ} (f g : ℕ → PowerSeries ℤ) (h : ∀ j ∈ s, d ∣ f j - g j) :
    d ∣ ∏ j ∈ s, f j - ∏ j ∈ s, g j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha,
      show f a * ∏ j ∈ s, f j - g a * ∏ j ∈ s, g j
        = (f a - g a) * ∏ j ∈ s, f j + g a * (∏ j ∈ s, f j - ∏ j ∈ s, g j) by ring]
    exact dvd_add (dvd_mul_of_dvd_left (h a (mem_insert_self a s)) _)
      (dvd_mul_of_dvd_right (ih fun j hj => h j (mem_insert_of_mem hj)) _)

/-! ## `(q;q)_∞ = ∏_{r=1}^5 (q^r;q⁵)_∞` -/

lemma Pfin_split5 : ∀ N, Pfin 1 1 (5 * N) = ∏ r ∈ range 5, Pfin (r + 1) 5 N
  | 0 => by simp [Pfin]
  | N + 1 => by
    rw [show 5 * (N + 1) = 5 * N + 5 by ring, Pfin, prod_range_add, ← Pfin, Pfin_split5 N]
    simp only [Pfin_succ, prod_mul_distrib]
    congr 1
    refine prod_congr rfl fun r _ => ?_
    congr 2; ring

theorem Pinf_split5 : Pinf 1 1 = ∏ r ∈ range 5, Pinf (r + 1) 5 := by
  symm
  refine Pinf_ext le_rfl le_rfl fun N => ?_
  have h1 : (X : PowerSeries ℤ) ^ (N + 1) ∣ ∏ r ∈ range 5, Pinf (r + 1) 5 - ∏ r ∈ range 5, Pfin (r + 1) 5 N :=
    dvd_sub_prod' _ _ fun r _ => X_pow_dvd_Pinf_sub (r + 1) 5 (by omega) (by norm_num) N
  have h2 := X_pow_dvd_Pfin_sub 1 1 N le_rfl le_rfl (5 * N) (by omega)
  rw [Pfin_split5] at h2
  have := dvd_add h1 h2
  rwa [sub_add_sub_cancel] at this

/-! ## exponent bookkeeping -/

lemma two_choose (n : ℕ) : 2 * n.choose 2 + n = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.choose_succ_succ, Nat.choose_one_right]; nlinarith

lemma Apent_eq (n : ℕ) : Apent n = 3 * n.choose 2 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Apent_succ, ih, Nat.choose_succ_succ, Nat.choose_one_right]; ring

lemma pentM_eq (n : ℕ) : pentM n = 3 * n.choose 2 + n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pentM_succ, ih, Nat.choose_succ_succ, Nat.choose_one_right]; ring

lemma thA_deg (a b d : ℕ) (hb : 1 ≤ b) : (X : PowerSeries ℤ) ^ d ∣ thA a b d := by
  rw [RankProof.thA]
  exact dvd_mul_of_dvd_right (pow_dvd_pow X (le_add_left (Nat.le_mul_of_pos_left d hb))) _

lemma thB_deg (a b d : ℕ) (hab : b < a) : (X : PowerSeries ℤ) ^ (d + 1) ∣ thB a b d := by
  rw [RankProof.thB]
  exact dvd_mul_of_dvd_right (pow_dvd_pow X (le_add_left (Nat.le_mul_of_pos_left _ (by omega)))) _

/-! ## RR1: `Σ q^{n²} αₙ = J_{5,2}` -/

lemma term_C (n : ℕ) :
    X ^ (n ^ 2) * alphaC n = thA 5 2 n + (if n = 0 then 0 else thB 5 2 (n - 1)) := by
  rcases n with _ | n
  · simp [alphaC, RankProof.thA]
  · rw [alphaC, if_neg (by omega), if_neg (by omega), RankProof.thA, RankProof.thB, Nat.add_sub_cancel,
      Apent_eq]
    have e1 : (n + 1) ^ 2 + (3 * (n + 1).choose 2 + (n + 1)) = 5 * (n + 1).choose 2 + 2 * (n + 1) := by
      have := two_choose (n + 1); omega
    have e2 : (n + 1) ^ 2 + (3 * (n + 1).choose 2 + (n + 1)) + (n + 1) = 5 * (n + 1).choose 2 + (5 - 2) * (n + 1) := by
      have := two_choose (n + 1); omega
    rw [← e1, ← e2]
    simp only [map_mul, map_neg, map_pow, map_one, pow_add, pow_one]
    ring

lemma sum_term_C (N : ℕ) :
    ∑ n ∈ range (N + 1), X ^ (n ^ 2) * alphaC n = ∑ d ∈ range (N + 1), thA 5 2 d + ∑ d ∈ range N, thB 5 2 d := by
  induction N with
  | zero => simp [term_C]
  | succ N ih =>
    rw [sum_range_succ, ih, term_C, if_neg (by omega), Nat.add_sub_cancel, sum_range_succ (thA 5 2) (N + 1),
      sum_range_succ (thB 5 2) N]
    ring

lemma tsumQsq_dvd (f : ℕ → PowerSeries ℤ) (N : ℕ) :
    (X : PowerSeries ℤ) ^ (N + 1) ∣ tsumQsq f - ∑ n ∈ range (N + 1), X ^ (n ^ 2) * f n := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro k hk
  rw [map_sub, coeff_tsumQsq f (show k + 1 ≤ N + 1 by omega), map_sum, sub_self]

lemma tsumQsqQ_dvd (f : ℕ → PowerSeries ℤ) (N : ℕ) :
    (X : PowerSeries ℤ) ^ (N + 1) ∣ tsumQsqQ f - ∑ n ∈ range (N + 1), X ^ (n ^ 2 + n) * f n := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro k hk
  rw [map_sub, coeff_tsumQsqQ f (show k + 1 ≤ N + 1 by omega), map_sum, sub_self]

theorem alphaC_theta : tsumQsq alphaC = thetaS 5 2 := by
  refine eq_of_dvd_all fun N => ?_
  have h1 := tsumQsq_dvd alphaC N
  have h2 := thetaS_dvd 5 2 (by norm_num) (by norm_num) N
  rw [sum_term_C] at h1
  have h3 : (X : PowerSeries ℤ) ^ (N + 1) ∣ thB 5 2 N := thB_deg 5 2 N (by norm_num)
  rw [thetaTr_eq, sum_range_succ (thB 5 2)] at h2
  have := dvd_sub (dvd_sub h1 h2) h3
  rw [show tsumQsq alphaC - (∑ d ∈ range (N + 1), thA 5 2 d + ∑ d ∈ range N, thB 5 2 d)
      - (thetaS 5 2 - (∑ d ∈ range (N + 1), thA 5 2 d + (∑ d ∈ range N, thB 5 2 d + thB 5 2 N))) - thB 5 2 N
      = tsumQsq alphaC - thetaS 5 2 by ring] at this
  exact this

/-! ## RR2: `(1−q) Σ q^{n²+n} αₙ = J_{5,1}` -/

lemma choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right]; ring

lemma term_B (n : ℕ) :
    (1 - X) * (X ^ (n ^ 2 + n) * alphaB n)
      = (if n = 0 then thA 5 1 0 else thB 5 1 (n - 1)) + thA 5 1 (n + 1) := by
  have hg := geom_mul (2 * n + 1)
  rw [alphaB, show (1 - X) * (X ^ (n ^ 2 + n) * ((-1) ^ n * X ^ (pentM n + n) * geom (2 * n + 1)))
      = X ^ (n ^ 2 + n) * ((-1) ^ n * X ^ (pentM n + n) * ((1 - X) * geom (2 * n + 1))) by ring, hg, pentM_eq]
  rcases n with _ | n
  · simp [RankProof.thA]; ring
  · rw [if_neg (by omega), Nat.add_sub_cancel]
    simp only [RankProof.thA, RankProof.thB]
    have h2 := two_choose (n + 1)
    have hc := choose_two_succ (n + 1)
    have e1 : (n + 1) ^ 2 + (n + 1) + (3 * (n + 1).choose 2 + (n + 1) + (n + 1))
        = 5 * (n + 1).choose 2 + (5 - 1) * (n + 1) := by omega
    have e2 : (n + 1) ^ 2 + (n + 1) + (3 * (n + 1).choose 2 + (n + 1) + (n + 1)) + (2 * (n + 1) + 1)
        = 5 * (n + 1 + 1).choose 2 + 1 * (n + 1 + 1) := by omega
    rw [← e1, ← e2]
    simp only [map_mul, map_neg, map_pow, map_one, pow_add, pow_one]
    ring

lemma sum_term_B (N : ℕ) :
    (1 - X) * ∑ n ∈ range (N + 1), X ^ (n ^ 2 + n) * alphaB n
      = ∑ d ∈ range (N + 2), thA 5 1 d + ∑ d ∈ range N, thB 5 1 d := by
  induction N with
  | zero => rw [sum_range_one, term_B]; simp [sum_range_succ]
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih, term_B, if_neg (by omega), Nat.add_sub_cancel, sum_range_succ (thA 5 1) (N + 2),
      sum_range_succ (thB 5 1)]
    ring

theorem alphaB_theta : (1 - X) * tsumQsqQ alphaB = thetaS 5 1 := by
  refine eq_of_dvd_all fun N => ?_
  have h1 := dvd_mul_of_dvd_right (tsumQsqQ_dvd alphaB N) (1 - X)
  rw [mul_sub, sum_term_B] at h1
  have h2 := thetaS_dvd 5 1 (by norm_num) (by norm_num) N
  rw [thetaTr_eq, sum_range_succ (thB 5 1)] at h2
  have h3 : (X : PowerSeries ℤ) ^ (N + 1) ∣ thA 5 1 (N + 1) := thA_deg 5 1 (N + 1) le_rfl
  have h4 : (X : PowerSeries ℤ) ^ (N + 1) ∣ thB 5 1 N := thB_deg 5 1 N (by norm_num)
  have := dvd_add (dvd_sub (dvd_sub h1 h2) h4) h3
  rw [sum_range_succ (thA 5 1) (N + 1)] at this
  rw [show (1 - X) * tsumQsqQ alphaB - (∑ d ∈ range (N + 1), thA 5 1 d + thA 5 1 (N + 1) + ∑ d ∈ range N, thB 5 1 d)
      - (thetaS 5 1 - (∑ d ∈ range (N + 1), thA 5 1 d + (∑ d ∈ range N, thB 5 1 d + thB 5 1 N))) - thB 5 1 N
      + thA 5 1 (N + 1) = (1 - X) * tsumQsqQ alphaB - thetaS 5 1 by ring] at this
  exact this

/-! ## the product forms -/

lemma inverse_eq_of_mul {a b : PowerSeries ℤ} (h : a * b = 1) : Ring.inverse a = b := by
  have ha : IsUnit a := ⟨⟨a, b, h, by rw [mul_comm]; exact h⟩, rfl⟩
  calc Ring.inverse a = Ring.inverse a * (a * b) := by rw [h, mul_one]
    _ = b := by rw [← mul_assoc, Ring.inverse_mul_cancel a ha, one_mul]

lemma qfacInf_mul_P : qfacInf * partitionGF = 1 := by
  rw [partitionGF, Ring.mul_inverse_cancel _ isUnit_qfacInf]

/-- **The first Rogers–Ramanujan identity**: `Σ_{n≥0} q^{n²}/(q;q)_n = 1/((q;q⁵)_∞ (q⁴;q⁵)_∞)`. -/
theorem rogers_ramanujan_1 :
    tsumQsq (fun n => Ring.inverse (qfac n)) = Ring.inverse (Pinf 1 5 * Pinf 4 5) := by
  rw [rogersRamanujan1_transform, alphaC_theta, ← jtp_ab 5 2 (by norm_num) (by norm_num)]
  symm
  apply inverse_eq_of_mul
  have hs := Pinf_split5
  rw [Pinf_one_one] at hs
  simp only [prod_range_succ, prod_range_zero, one_mul] at hs
  norm_num at hs ⊢
  linear_combination -partitionGF * hs + qfacInf_mul_P

/-- **The second Rogers–Ramanujan identity**: `Σ_{n≥0} q^{n²+n}/(q;q)_n = 1/((q²;q⁵)_∞ (q³;q⁵)_∞)`. -/
theorem rogers_ramanujan_2 :
    tsumQsqQ (fun n => Ring.inverse (qfac n)) = Ring.inverse (Pinf 2 5 * Pinf 3 5) := by
  rw [rogersRamanujan2_transform, mul_assoc, mul_left_comm, alphaB_theta, ← jtp_ab 5 1 (by norm_num) (by norm_num)]
  symm
  apply inverse_eq_of_mul
  have hs := Pinf_split5
  rw [Pinf_one_one] at hs
  simp only [prod_range_succ, prod_range_zero, one_mul] at hs
  norm_num at hs ⊢
  linear_combination -partitionGF * hs + qfacInf_mul_P

end MockTheta5.JTP.RR
