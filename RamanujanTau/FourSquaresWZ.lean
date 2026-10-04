/-
# Jacobi's four-square theorem, part 1: a terminating identity with a WZ certificate

The specialization `a = 1`, `b = c = d = −1`, `e = −q^{n+1}` of Jackson's terminating ₈φ₇ summation, normalized:

  `S(n) = (−q;q)ₙ⁴/(q;q)ₙ⁴ + Σ_{k=1}^{n} 8(−1)^k q^k/(1+q^k)² · (−q)_{n−k}(−q)_{n+k}(−q)ₙ² / ((q)_{n−k}(q)_{n+k}(q)ₙ²) = 1`.

It is proved by the WZ method: with
`G(n,k) = 8(−1)^k c(n) (−q)_{n+1−k}(−q)_{n+k}(−q)ₙ²/((q)_{n+1−k}(q)_{n+k}(q)ₙ²)`,
`c(n) = −q^{n+1}(1+q^{2n+2})/((1−q^{n+1})³(1+q^{n+1}))`,
we have `T(n+1,k) − T(n,k) = G(n,k+1) − G(n,k)` for `1 ≤ k ≤ n`, together with the two boundary relations
`C(n+1) − C(n) = G(n,1)` and `T(n+1,n+1) = −G(n,n+1)`. Each is a rational-function identity, checked in the
fraction field of `ℤ⟦q⟧`.
-/
import RamanujanTau.MockTheta5BaileyPair
import Mathlib.RingTheory.Localization.FractionRing

set_option autoImplicit false

namespace FourSquares
open PowerSeries Finset MockTheta5.Bailey

/-- `(−q;q)_n`. -/
noncomputable def mfac (n : ℕ) : PowerSeries ℤ := ∏ i ∈ range n, (1 + X ^ (i + 1))

lemma isUnit_of_cc {f : PowerSeries ℤ} (h : constantCoeff f = 1) : IsUnit f := by
  rw [PowerSeries.isUnit_iff_constantCoeff, h]; exact isUnit_one

lemma isUnit_mfac (n : ℕ) : IsUnit (mfac n) := isUnit_of_cc (by rw [mfac, map_prod]; exact prod_eq_one fun i _ => by simp)

lemma isUnit_one_add {m : ℕ} (hm : 1 ≤ m) : IsUnit (1 + X ^ m : PowerSeries ℤ) :=
  isUnit_of_cc (by simp [zero_pow (by omega : m ≠ 0)])

lemma isUnit_one_sub {m : ℕ} (hm : 1 ≤ m) : IsUnit (1 - X ^ m : PowerSeries ℤ) :=
  isUnit_of_cc (by simp [zero_pow (by omega : m ≠ 0)])

lemma mfac_zero : mfac 0 = 1 := by simp [mfac]
lemma qfac_zero : qfac 0 = 1 := by simp [qfac]

lemma mfac_succ (n : ℕ) : mfac (n + 1) = mfac n * (1 + X ^ (n + 1)) := by rw [mfac, mfac, prod_range_succ]
lemma qfac_succ' (n : ℕ) : qfac (n + 1) = qfac n * (1 - X ^ (n + 1)) := by rw [qfac, qfac, prod_range_succ]

noncomputable def ccoef (n : ℕ) : PowerSeries ℤ :=
  -(X ^ (n + 1) * (1 + (X ^ (n + 1)) ^ 2)) * Ring.inverse ((1 - X ^ (n + 1)) ^ 3 * (1 + X ^ (n + 1)))

noncomputable def Ct (n : ℕ) : PowerSeries ℤ := mfac n ^ 4 * Ring.inverse (qfac n ^ 4)

noncomputable def Tt (n k : ℕ) : PowerSeries ℤ :=
  8 * (-1) ^ k * X ^ k * Ring.inverse ((1 + X ^ k) ^ 2) * (mfac (n - k) * mfac (n + k) * mfac n ^ 2)
    * Ring.inverse (qfac (n - k) * qfac (n + k) * qfac n ^ 2)

noncomputable def Gt (n k : ℕ) : PowerSeries ℤ :=
  8 * (-1) ^ k * ccoef n * (mfac (n + 1 - k) * mfac (n + k) * mfac n ^ 2)
    * Ring.inverse (qfac (n + 1 - k) * qfac (n + k) * qfac n ^ 2)

noncomputable def St (n : ℕ) : PowerSeries ℤ := Ct n + ∑ i ∈ range n, Tt n (i + 1)

/-! ## transfer to the fraction field -/

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


macro "unit_tac" : tactic =>
  `(tactic| repeat' (first | exact isUnit_qfac _ | exact isUnit_mfac _ | exact isUnit_one_add (by omega) | exact isUnit_one_sub (by omega) | apply IsUnit.mul | apply IsUnit.pow))

/-- boundary: `C(n+1) − C(n) = G(n,1)`. -/
lemma wz_C (n : ℕ) : Ct (n + 1) - Ct n = Gt n 1 := by
  apply φ_inj
  have hq := φ_ne (isUnit_qfac n)
  have hm := φ_ne (isUnit_mfac n)
  have h1 := φ_ne (isUnit_one_sub (m := n + 1) (by omega))
  have h2 := φ_ne (isUnit_one_add (m := n + 1) (by omega))
  simp only [map_sub, map_add, map_one, map_pow] at h1 h2
  simp only [Ct, Gt, ccoef, show n + 1 - 1 = n by omega, mfac_succ, qfac_succ', pow_one]
  simp (disch := unit_tac) only [φ_inverse, map_sub, map_add, map_mul, map_neg, map_one, map_pow, map_ofNat]
  generalize φ (X ^ (n + 1)) = u at *
  field_simp
  ring


/-- the WZ relation `T(n+1,k) − T(n,k) = G(n,k+1) − G(n,k)` for `1 ≤ k ≤ n` (`n = j + k`). -/
lemma wz_step (j k : ℕ) (hk : 1 ≤ k) :
    Tt (j + k + 1) k - Tt (j + k) k = Gt (j + k) (k + 1) - Gt (j + k) k := by
  apply φ_inj
  have hq1 := φ_ne (isUnit_qfac j)
  have hq2 := φ_ne (isUnit_qfac (j + k + k))
  have hq3 := φ_ne (isUnit_qfac (j + k))
  have hm1 := φ_ne (isUnit_mfac j)
  have hm2 := φ_ne (isUnit_mfac (j + k + k))
  have hm3 := φ_ne (isUnit_mfac (j + k))
  have h1 := φ_ne (isUnit_one_sub (m := j + 1) (by omega))
  have h2 := φ_ne (isUnit_one_sub (m := j + k + k + 1) (by omega))
  have h3 := φ_ne (isUnit_one_sub (m := j + k + 1) (by omega))
  have h4 := φ_ne (isUnit_one_add (m := j + k + 1) (by omega))
  have h5 := φ_ne (isUnit_one_add (m := k) hk)
  simp only [map_sub, map_add, map_one, map_pow, map_mul, pow_add, pow_one] at h1 h2 h3 h4 h5
  simp only [Tt, Gt, ccoef, show j + k + 1 - k = j + 1 by omega, show j + k + 1 + k = j + k + k + 1 by ring,
    show j + k - k = j by omega, show j + k + 1 - (k + 1) = j by omega, show j + k + (k + 1) = j + k + k + 1 by ring,
    mfac_succ, qfac_succ']
  simp (disch := unit_tac) only [φ_inverse, map_sub, map_add, map_mul, map_neg, map_one, map_pow, map_ofNat]
  simp only [pow_add, pow_one]
  generalize φ X ^ j = a at *
  generalize φ X ^ k = b at *
  generalize φ X = x at *
  generalize φ (qfac j) = p1 at *
  generalize φ (qfac (j + k + k)) = p2 at *
  generalize φ (qfac (j + k)) = p3 at *
  generalize φ (mfac j) = m1 at *
  generalize φ (mfac (j + k + k)) = m2 at *
  generalize φ (mfac (j + k)) = m3 at *
  generalize hv : a * b * b * x = v at *
  generalize hu : a * b * x = u at *
  generalize hw : a * x = w at *
  field_simp
  subst hu hv hw
  ring

/-- boundary: `T(n+1,n+1) = −G(n,n+1)`. -/
lemma wz_end (n : ℕ) : Tt (n + 1) (n + 1) = -Gt n (n + 1) := by
  apply φ_inj
  have hq1 := φ_ne (isUnit_qfac (n + n + 1))
  have hq3 := φ_ne (isUnit_qfac n)
  have hm1 := φ_ne (isUnit_mfac (n + n + 1))
  have hm3 := φ_ne (isUnit_mfac n)
  have h2 := φ_ne (isUnit_one_sub (m := n + n + 1 + 1) (by omega))
  have h3 := φ_ne (isUnit_one_sub (m := n + 1) (by omega))
  have h4 := φ_ne (isUnit_one_add (m := n + 1) (by omega))
  have h6 := φ_ne (isUnit_one_add (m := n + n + 1 + 1) (by omega))
  rw [Tt, Gt, ccoef, show n + 1 - (n + 1) = 0 by omega, show n + 1 + (n + 1) = n + n + 1 + 1 by ring,
    show n + (n + 1) = n + n + 1 by ring, mfac_succ (n + n + 1), qfac_succ' (n + n + 1), mfac_succ n,
    qfac_succ' n, mfac_zero, qfac_zero]
  simp only [one_mul]
  simp (disch := unit_tac) only [φ_inverse, map_sub, map_add, map_mul, map_neg, map_one, map_pow, map_ofNat]
  simp only [map_sub, map_add, map_one, map_pow] at h2 h3 h4 h6
  have e2 : φ X ^ (n + n + 1 + 1) = (φ X ^ (n + 1)) ^ 2 := by rw [← pow_mul]; ring_nf
  rw [e2] at h2 h6 ⊢
  generalize φ X ^ (n + 1) = u at *
  generalize φ (qfac (n + n + 1)) = p1 at *
  generalize φ (qfac n) = p3 at *
  generalize φ (mfac (n + n + 1)) = m1 at *
  generalize φ (mfac n) = m3 at *
  generalize hv : u ^ 2 = v at *
  field_simp
  subst hv
  ring


lemma wz_step' {n k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ n) : Tt (n + 1) k - Tt n k = Gt n (k + 1) - Gt n k := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + k := ⟨n - k, by omega⟩
  exact wz_step j k h1

/-- **the terminating identity** `S(n) = 1`. -/
theorem St_eq_one (n : ℕ) : St n = 1 := by
  induction n with
  | zero => simp [St, Ct, mfac_zero, qfac_zero]
  | succ n ih =>
    rw [← ih, St, St, sum_range_succ, wz_end]
    have hC := wz_C n
    have hT : ∑ i ∈ range n, Tt (n + 1) (i + 1)
        = ∑ i ∈ range n, Tt n (i + 1) + ∑ i ∈ range n, (Gt n (i + 1 + 1) - Gt n (i + 1)) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun i hi => ?_
      have := wz_step' (n := n) (k := i + 1) (by omega) (by simp at hi; omega)
      linear_combination this
    rw [hT, sum_range_sub (fun i => Gt n (i + 1))]
    linear_combination hC

end FourSquares
