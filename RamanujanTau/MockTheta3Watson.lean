/-
# Watson's third-order identities (Ramanujan's last letter)

  `2φ(−q) − f(q) = b(q)`,   `f(q) + 4ψ(−q) = b(q)`,
with `f = Σ q^{n²}/(−q;q)_n²`, `φ(q) = Σ q^{n²}/(−q²;q²)_n`, `ψ(q) = Σ_{n≥1} q^{n²}/(q;q²)_n`, and Ramanujan's
`b(q) = (1−q)(1−q³)(1−q⁵)⋯(1 − 2q + 2q⁴ − 2q⁹ + ⋯)`.

Elementary proof through the chain `α = q^j` of Andrews' one-parameter generalization:
* `F_j = Σ q^{jn+n²−n}/((−q;q)_n(−q^j;q)_n)` and `A_j = Σ (−1)ⁿ q^{n²}/(−q^{j+1};q²)_n`;
* (T1) `F_{j+1} + (1+q^j)F_j = 2(1+q^j)` (telescoping), (T2) `A_{j+2} = (1+q^{j+1})((1+q^j)A_j − q^j)`;
* so `M_j = 2A_j − F_j` satisfies `M_{j+2} = (1+q^j)(1+q^{j+1})M_j` and `M_j ≡ Θ (mod q^j)`, `Θ = Σ_ℤ (−1)ⁿq^{n²}`;
* hence `(−q^j;q)_∞ M_j = Θ`, and Euler's `(−q;q)_∞ (q;q²)_∞ = 1` gives `M_1 = (q;q²)_∞ Θ = b`.
-/
import RamanujanTau.Watson.Prod
import Mathlib.RingTheory.Localization.FractionRing

set_option autoImplicit false

namespace MockTheta3.Watson3
open PowerSeries Finset Watson

local notation "K" => FractionRing (PowerSeries ℤ)

noncomputable abbrev φ : PowerSeries ℤ →+* K := algebraMap (PowerSeries ℤ) K

lemma φ_inj : Function.Injective φ := IsFractionRing.injective _ _

lemma φ_inverse {u : PowerSeries ℤ} (hu : IsUnit u) : φ (Ring.inverse u) = (φ u)⁻¹ := by
  refine (eq_inv_of_mul_eq_one_right ?_)
  rw [← map_mul, Ring.mul_inverse_cancel u hu, map_one]

lemma φ_ne {u : PowerSeries ℤ} (hu : IsUnit u) : φ u ≠ 0 :=
  fun h => by
    have := congrArg φ (Ring.mul_inverse_cancel u hu)
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this

lemma isUnit_one_add {m : ℕ} (hm : 1 ≤ m) : IsUnit (1 + X ^ m : PowerSeries ℤ) := by
  rw [isUnit_iff_constantCoeff]; simp [zero_pow (by omega : m ≠ 0)]

/-- `(−q^a;q^b)_n`. -/
noncomputable abbrev NP (a b n : ℕ) : PowerSeries ℤ := FP (-1) a b n

lemma NP_succ (a b n : ℕ) : NP a b (n + 1) = NP a b n * (1 + X ^ (a + b * n)) := by
  rw [NP, FP_succ]; simp

lemma NP_shift (a b n : ℕ) : NP a b (n + 1) = (1 + X ^ a) * NP (a + b) b n := by
  rw [NP, add_comm n 1, FP_add, FP_succ, FP_zero]; simp

lemma isUnit_NP {a : ℕ} (ha : 1 ≤ a) (b n : ℕ) : IsUnit (NP a b n) := isUnit_FP (-1) ha b n

/-! ### the families -/

/-- the `n`-th term of `F_j`. -/
noncomputable def tF (j n : ℕ) : PowerSeries ℤ :=
  X ^ (j * n + n * (n - 1)) * Ring.inverse (NP 1 1 n) * Ring.inverse (NP j 1 n)

/-- the `n`-th term of `A_j`. -/
noncomputable def uA (j n : ℕ) : PowerSeries ℤ := (-1) ^ n * X ^ (n ^ 2) * Ring.inverse (NP (j + 1) 2 n)

noncomputable def F (j : ℕ) : PowerSeries ℤ := osum (tF j)
noncomputable def A (j : ℕ) : PowerSeries ℤ := osum (uA j)

/-- `Θ = 2Σ_{n≥0}(−1)ⁿq^{n²} − 1 = Σ_{n∈ℤ}(−1)ⁿq^{n²}`. -/
noncomputable def Θ : PowerSeries ℤ := 2 * osum (fun n => (-1) ^ n * X ^ (n ^ 2)) - 1

noncomputable def M (j : ℕ) : PowerSeries ℤ := 2 * A j - F j

lemma coeff_Xpow_mul_zero {e k : ℕ} (h : k < e) (g : PowerSeries ℤ) : coeff k (X ^ e * g) = 0 := by
  rw [coeff_X_pow_mul', if_neg (by omega)]

lemma LF_tF {j : ℕ} (hj : 1 ≤ j) : LF (tF j) := LF.of_nat fun n k hk => by
  rw [tF, mul_assoc]; exact coeff_Xpow_mul_zero (by nlinarith [Nat.zero_le (n * (n - 1))]) _

lemma LF_uA (j : ℕ) : LF (uA j) := LF.of_nat fun n k hk => by
  rw [uA, mul_comm ((-1 : PowerSeries ℤ) ^ n), mul_assoc]
  exact coeff_Xpow_mul_zero (by nlinarith) _

lemma LF_theta : LF (fun n : ℕ => (-1 : PowerSeries ℤ) ^ n * X ^ (n ^ 2)) := LF.of_nat fun n k hk => by
  rw [mul_comm]; exact coeff_Xpow_mul_zero (by nlinarith) _

/-- telescoping: `Σ (g n − g (n+1)) = g 0` when `g n = O(qⁿ)`. -/
lemma osum_telescope (g : ℕ → PowerSeries ℤ) (hg : ∀ n k, k < n → coeff k (g n) = 0) :
    osum (fun n => g n - g (n + 1)) = g 0 := by
  ext k
  rw [coeff_osum]
  rw [finsum_eq_sum_of_support_subset (s := range (k + 1)) _ fun n hn => by
    simp only [Function.mem_support, coe_range, Set.mem_Iio] at hn ⊢
    by_contra hc
    exact hn (by rw [map_sub, hg n k (by omega), hg (n + 1) k (by omega), sub_zero])]
  simp only [map_sub]
  rw [Finset.sum_range_sub', hg (k + 1) k (by omega), sub_zero]

/-! ### (T1) -/

/-- `h_m = q^{j(m+1)+(m+1)m}/((−q;q)_m (−q^{j+1};q)_m)`. -/
noncomputable def hT (j m : ℕ) : PowerSeries ℤ :=
  X ^ (j * (m + 1) + (m + 1) * m) * Ring.inverse (NP 1 1 m) * Ring.inverse (NP (j + 1) 1 m)

lemma T1_step (j m : ℕ) (hj : 1 ≤ j) :
    (1 + X ^ j) * tF j (m + 1) + tF (j + 1) (m + 1) = hT j m - hT j (m + 1) := by
  apply φ_inj
  have uP := isUnit_NP (a := 1) le_rfl 1 m
  have uQ := isUnit_NP (a := j + 1) (by omega) 1 m
  have u1 := isUnit_one_add (m := 1 + 1 * m) (by omega)
  have u2 := isUnit_one_add (m := j + 1 + 1 * m) (by omega)
  have uj := isUnit_one_add (m := j) hj
  simp only [tF, hT, show m + 1 - 1 = m from rfl, NP_succ 1 1 m, NP_succ (j + 1) 1 m, NP_shift j 1 m]
  simp only [map_sub, map_add, map_mul, map_one, map_pow, φ_inverse uP, φ_inverse uQ,
    φ_inverse (uP.mul u1), φ_inverse (uj.mul uQ), φ_inverse (uQ.mul u2)]
  have hP := φ_ne uP
  have hQ := φ_ne uQ
  have h1 := φ_ne u1
  have h2 := φ_ne u2
  have h3 := φ_ne uj
  simp only [map_add, map_one, map_pow] at h1 h2 h3
  generalize φ (NP 1 1 m) = P at *
  generalize φ (NP (j + 1) 1 m) = Q at *
  generalize φ X = x at *
  field_simp
  ring

lemma LF_shift {f : ℕ → PowerSeries ℤ} (hf : LF f) : LF (fun n => f (n + 1)) :=
  hf.comp_injective (add_left_injective 1)

lemma LF_hT (j : ℕ) : LF (hT j) := LF.of_nat fun n k hk => by
  rw [hT, mul_assoc]; exact coeff_Xpow_mul_zero (by nlinarith) _

lemma tF_zero (j : ℕ) : tF j 0 = 1 := by simp [tF, NP, FP_zero]

lemma uA_zero (j : ℕ) : uA j 0 = 1 := by simp [uA, NP, FP_zero]

/-- **(T1)** `F_{j+1} + (1+q^j)F_j = 2(1+q^j)`. -/
theorem T1 {j : ℕ} (hj : 1 ≤ j) : F (j + 1) + (1 + X ^ j) * F j = 2 * (1 + X ^ j) := by
  have hL := LF_tF hj
  have hL' := LF_tF (j := j + 1) (by omega)
  rw [F, F, osum_succ hL, osum_succ hL', tF_zero, tF_zero, mul_add, mul_one, mul_osum (LF_shift hL)]
  have hS := osum_add (LF_shift hL') ((LF_shift hL).mul_left (1 + X ^ j))
  have hT1 : osum (fun n => tF (j + 1) (n + 1) + (1 + X ^ j) * tF j (n + 1)) = X ^ j := by
    rw [osum_ext fun n => (add_comm _ _).trans (T1_step j n hj),
      osum_telescope (hT j) fun n k hk => by rw [hT, mul_assoc]; exact coeff_Xpow_mul_zero (by nlinarith) _]
    simp [hT, NP, FP_zero]
  rw [hS] at hT1
  linear_combination hT1

/-! ### (T2) -/

lemma T2_step (j n : ℕ) :
    (-1) ^ n * X ^ (n ^ 2) * Ring.inverse (NP (j + 1) 2 (n + 1)) = uA j n + X ^ j * uA j (n + 1) := by
  apply φ_inj
  have uP := isUnit_NP (a := j + 1) (by omega) 2 n
  have u1 := isUnit_one_add (m := j + 1 + 2 * n) (by omega)
  simp only [uA, NP_succ (j + 1) 2 n]
  simp only [map_add, map_mul, map_one, map_pow, map_neg, φ_inverse uP, φ_inverse (uP.mul u1)]
  have hP := φ_ne uP
  have h1 := φ_ne u1
  simp only [map_add, map_one, map_pow] at h1
  generalize φ (NP (j + 1) 2 n) = P at *
  generalize φ X = x at *
  field_simp
  ring

/-- **(T2)** `A_{j+2} = (1+q^{j+1})((1+q^j)A_j − q^j)`. -/
theorem T2 (j : ℕ) : A (j + 2) = (1 + X ^ (j + 1)) * ((1 + X ^ j) * A j - X ^ j) := by
  set v : ℕ → PowerSeries ℤ := fun n => (-1) ^ n * X ^ (n ^ 2) * Ring.inverse (NP (j + 1) 2 (n + 1))
  have hv : ∀ n, uA (j + 2) n = (1 + X ^ (j + 1)) * v n := fun n => by
    have u1 := isUnit_one_add (m := j + 1) (by omega)
    have u2 := isUnit_NP (a := j + 1 + 2) (by omega) 2 n
    simp only [v, uA, NP_shift (j + 1) 2 n, show j + 2 + 1 = j + 1 + 2 by omega]
    apply φ_inj
    simp only [map_add, map_mul, map_one, map_pow, φ_inverse u2, φ_inverse (u1.mul u2)]
    have h1 := φ_ne u1
    have h2 := φ_ne u2
    simp only [map_add, map_one, map_pow] at h1
    field_simp
  have hLv : LF v := LF.of_nat fun n k hk => by
    simp only [v]; rw [mul_comm ((-1 : PowerSeries ℤ) ^ n), mul_assoc]; exact coeff_Xpow_mul_zero (by nlinarith) _
  have hL := LF_uA j
  have hA : A (j + 2) = (1 + X ^ (j + 1)) * osum v := by
    rw [A, osum_ext hv, mul_osum hLv]
  have hv2 : osum v = A j + X ^ j * (A j - 1) := by
    have e1 : osum v = osum (fun n => uA j n + X ^ j * uA j (n + 1)) := osum_ext fun n => T2_step j n
    rw [e1, osum_add hL ((LF_shift hL).mul_left _), ← mul_osum (LF_shift hL)]
    have e2 := osum_succ hL
    rw [uA_zero] at e2
    rw [A, e2]; ring
  rw [hA, hv2]; ring

/-! ### the recursion, the congruence, the contraction -/

theorem M_rec {j : ℕ} (hj : 1 ≤ j) : M (j + 2) = (1 + X ^ j) * (1 + X ^ (j + 1)) * M j := by
  have e0 := T1 hj
  have e1 := T1 (j := j + 1) (by omega)
  have e2 := T2 j
  rw [show j + 1 + 1 = j + 2 by omega] at e1
  unfold M
  linear_combination 2 * e2 - e1 + (1 + X ^ (j + 1)) * e0

lemma osum_dvd {f : ℕ → PowerSeries ℤ} {m : ℕ} (h : ∀ n, (X : PowerSeries ℤ) ^ m ∣ f n) :
    (X : PowerSeries ℤ) ^ m ∣ osum f := by
  rw [X_pow_dvd_iff]
  intro k hk
  rw [coeff_osum]
  have : ∀ n, coeff k (f n) = 0 := fun n => (X_pow_dvd_iff.mp (h n)) k hk
  simp [this]

lemma inverse_sub_one_dvd {u : PowerSeries ℤ} (hu : IsUnit u) {m : ℕ} (h : (X : PowerSeries ℤ) ^ m ∣ u - 1) :
    (X : PowerSeries ℤ) ^ m ∣ Ring.inverse u - 1 := by
  have : Ring.inverse u - 1 = -(Ring.inverse u * (u - 1)) := by
    rw [mul_sub, Ring.inverse_mul_cancel _ hu]; ring
  rw [this]; exact (h.mul_left _).neg_right

theorem M_cong {j : ℕ} (hj : 1 ≤ j) : (X : PowerSeries ℤ) ^ j ∣ M j - Θ := by
  have hL := LF_uA j
  have hθ := LF_theta
  have hF : (X : PowerSeries ℤ) ^ j ∣ F j - 1 := by
    rw [F, osum_succ (LF_tF hj), tF_zero, add_sub_cancel_left]
    refine osum_dvd fun n => ?_
    rw [tF, mul_assoc]
    exact dvd_mul_of_dvd_left (pow_dvd_pow _ (by nlinarith)) _
  have hA : (X : PowerSeries ℤ) ^ j ∣ A j - osum (fun n => (-1 : PowerSeries ℤ) ^ n * X ^ (n ^ 2)) := by
    rw [A, ← osum_sub hL hθ]
    refine osum_dvd fun n => ?_
    rw [uA, show (-1 : PowerSeries ℤ) ^ n * X ^ (n ^ 2) * Ring.inverse (NP (j + 1) 2 n) - (-1) ^ n * X ^ (n ^ 2)
      = (-1) ^ n * X ^ (n ^ 2) * (Ring.inverse (NP (j + 1) 2 n) - 1) by ring]
    exact dvd_mul_of_dvd_right ((pow_dvd_pow _ (by omega)).trans
      (inverse_sub_one_dvd (isUnit_NP (by omega) 2 n) (FP_sub_one_dvd (-1) (j + 1) 2 n))) _
  have : M j - Θ = 2 * (A j - osum (fun n => (-1 : PowerSeries ℤ) ^ n * X ^ (n ^ 2))) - (F j - 1) := by
    unfold M Θ; ring
  rw [this]
  exact dvd_sub (hA.mul_left _) hF

lemma M_iter {j : ℕ} (hj : 1 ≤ j) : ∀ k, M (j + 2 * k) = FP (-1) j 1 (2 * k) * M j := by
  intro k
  induction k with
  | zero => simp [FP_zero]
  | succ k ih =>
    rw [show j + 2 * (k + 1) = j + 2 * k + 2 by ring, M_rec (by omega), ih,
      show 2 * (k + 1) = 2 * k + 1 + 1 by ring, FP_succ, FP_succ]
    simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, sub_neg_eq_add]
    ring_nf

/-- **contraction**: `(−q^j;q)_∞ · M_j = Θ`. -/
theorem M_contract {j : ℕ} (hj : 1 ≤ j) : IP (-1) j 1 * M j = Θ := by
  ext n
  have hd : (X : PowerSeries ℤ) ^ (2 * n + 1) ∣ IP (-1) j 1 * M j - Θ := by
    have h1 := IP_sub_FP_dvd (-1) hj le_rfl (2 * (n + 1))
    have h2 := M_cong (j := j + 2 * (n + 1)) (by omega)
    rw [M_iter hj] at h2
    have : IP (-1) j 1 * M j - Θ = (IP (-1) j 1 - FP (-1) j 1 (2 * (n + 1))) * M j
        + (FP (-1) j 1 (2 * (n + 1)) * M j - Θ) := by ring
    rw [this]
    exact dvd_add ((((pow_dvd_pow _ (by omega)).trans h1)).mul_right _) ((pow_dvd_pow _ (by omega)).trans h2)
  have := (X_pow_dvd_iff.mp hd) n (by omega)
  rwa [map_sub, sub_eq_zero] at this

/-! ### Watson's identities -/

/-- `b(q) = (q;q²)_∞ · Θ(q) = (1−q)(1−q³)⋯(1 − 2q + 2q⁴ − ⋯)`. -/
noncomputable def bR : PowerSeries ℤ := IP 1 1 2 * Θ

/-- **Watson (W1)**: `2φ(−q) − f(q) = b(q)` (`A₁ = φ(−q)`, `F₁ = f(q)`). -/
theorem watson_W1 : 2 * A 1 - F 1 = bR := by
  have h := M_contract (j := 1) le_rfl
  have hE := euler_E4
  rw [bR, ← h, M]
  linear_combination (-(2 * A 1 - F 1)) * hE

/-- **Watson (W2)**: `f(q) + 4ψ(−q) = b(q)` (`A₀ − 1 = ψ(−q)`). -/
theorem watson_W2 : F 1 + 4 * (A 0 - 1) = bR := by
  have h := M_contract (j := 2) (by norm_num)
  have e1 := T1 (j := 1) le_rfl
  have e2 := T2 0
  have hs := IP_split (-1) (a := 1) (b := 1) le_rfl le_rfl 1
  simp only [FP_succ, FP_zero] at hs
  norm_num at e1 e2 hs
  have hE := euler_E4
  have hM : M 2 = (1 + X) * (F 1 + 4 * (A 0 - 1)) := by
    unfold M; linear_combination 2 * e2 - e1
  rw [hM] at h
  rw [bR, ← h]
  linear_combination (-(F 1 + 4 * (A 0 - 1))) * hE + (F 1 + 4 * (A 0 - 1)) * IP 1 1 2 * hs

end MockTheta3.Watson3
