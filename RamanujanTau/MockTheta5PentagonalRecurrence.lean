/-
# Euler's pentagonal recurrence for the partition function

Since `(q;q)_∞ = pentSeries` (Euler pentagonal) and `partitionGF = 1/(q;q)_∞`, we have
`pentSeries · partitionGF = 1`. Reading off the coefficient of `q^n` (`n ≥ 1`) gives Euler's recurrence

  **`partition_pentagonal_recurrence`:**
    `p(n) = Σ_{m≥0} (−1)ᵐ ( p(n − g₁(m)) + p(n − g₂(m)) )`,

where `g₁(m) = (m+1)(3m+2)/2` and `g₂(m) = (m+1)(3m+4)/2` are the generalized pentagonal numbers
`k(3k−1)/2` for `k = m+1` and `k = −(m+1)` (terms with argument `< 0` omitted). With the partition-count
bridge this is a statement about the honest count `#(Nat.Partition n)`. No `sorry`.
-/
import RamanujanTau.MockTheta5PartitionCount

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- `pentSeries` is the reciprocal of the partition generating function. -/
lemma pentSeries_mul_partitionGF : pentSeries * partitionGF = 1 := by
  rw [← euler_pentagonal, partitionGF, Ring.mul_inverse_cancel _ isUnit_qfacInf]

/-- `map evm1` of the finite pentagonal truncation, spelled as a sum of monomials with signs. -/
lemma map_evm1_pentFiniteP (M : ℕ) :
    PowerSeries.map evm1 (pentFiniteP M)
      = 1 + ∑ m ∈ Finset.range M,
          (X ^ ((m + 1) * (3 * m + 2) / 2) * PowerSeries.C (sgn ((m : ℤ) + 1))
           + X ^ ((m + 1) * (3 * m + 4) / 2) * PowerSeries.C (sgn (-((m : ℤ) + 1)))) := by
  rw [pentFiniteP, map_add, map_one, map_sum]
  exact congrArg (1 + ·) (Finset.sum_congr rfl (fun m _ => map_evm1_pentTermP m))

/-- `pentSeries` agrees with the finite truncation `map evm1 (pentFiniteP M)` up to degree `M − 1`. -/
lemma coeff_pentSeries_lt {a M : ℕ} (hM : a + 1 ≤ M) :
    coeff a pentSeries = coeff a (PowerSeries.map evm1 (pentFiniteP M)) := by
  rw [pentSeries, PowerSeries.coeff_map, coeff_pentTheta hM, ← PowerSeries.coeff_map]

/-- `sgn (m+1) = (−1)^{m+1}`. -/
private lemma sgn_succ_natCast (m : ℕ) : sgn ((m : ℤ) + 1) = (-1 : ℤ) ^ (m + 1) := by
  rw [sgn_succ, sgn_natCast, pow_succ]; ring

/-- coefficient of a single pentagonal monomial times the partition series. -/
private lemma coeff_monomial_mul (g : ℕ) (s : ℤ) (n : ℕ) :
    coeff n (X ^ g * PowerSeries.C s * partitionGF)
      = s * (if g ≤ n then coeff (n - g) partitionGF else 0) := by
  rw [mul_comm (X ^ g) (PowerSeries.C s), mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X_pow_mul']

/-- **Euler's pentagonal recurrence for the partition function** (for `n ≥ 1`). -/
theorem partition_pentagonal_recurrence (n : ℕ) (hn : 0 < n) :
    coeff n partitionGF = ∑ m ∈ Finset.range (n + 1), (-1 : ℤ) ^ m *
      ((if (m + 1) * (3 * m + 2) / 2 ≤ n then coeff (n - (m + 1) * (3 * m + 2) / 2) partitionGF else 0)
       + (if (m + 1) * (3 * m + 4) / 2 ≤ n then coeff (n - (m + 1) * (3 * m + 4) / 2) partitionGF else 0)) := by
  -- coefficient of q^n in pentSeries·partitionGF = 1 vanishes for n ≥ 1
  have h0 : coeff n (pentSeries * partitionGF) = 0 := by
    rw [pentSeries_mul_partitionGF, PowerSeries.coeff_one, if_neg hn.ne']
  -- replace pentSeries by its degree-≤ n truncation
  have hdvd : (X : PowerSeries ℤ) ^ (n + 1) ∣ (pentSeries - PowerSeries.map evm1 (pentFiniteP (n + 1))) := by
    rw [PowerSeries.X_pow_dvd_iff]; intro i hi
    rw [map_sub, coeff_pentSeries_lt (show i + 1 ≤ n + 1 by omega), sub_self]
  rw [coeff_mul_congr_left hdvd, map_evm1_pentFiniteP, add_mul, one_mul, Finset.sum_mul, map_add,
      map_sum] at h0
  -- simplify each summand
  have hterm : ∀ m ∈ Finset.range (n + 1),
      coeff n ((X ^ ((m + 1) * (3 * m + 2) / 2) * PowerSeries.C (sgn ((m : ℤ) + 1))
                + X ^ ((m + 1) * (3 * m + 4) / 2) * PowerSeries.C (sgn (-((m : ℤ) + 1)))) * partitionGF)
        = (-1 : ℤ) ^ (m + 1) *
          ((if (m + 1) * (3 * m + 2) / 2 ≤ n then coeff (n - (m + 1) * (3 * m + 2) / 2) partitionGF else 0)
           + (if (m + 1) * (3 * m + 4) / 2 ≤ n then coeff (n - (m + 1) * (3 * m + 4) / 2) partitionGF else 0)) := by
    intro m _
    rw [add_mul, map_add, coeff_monomial_mul, coeff_monomial_mul, sgn_neg, sgn_succ_natCast]
    ring
  rw [Finset.sum_congr rfl hterm] at h0
  -- h0 : coeff n partitionGF + Σ (−1)^{m+1}·B m = 0  ⟹  coeff n partitionGF = Σ (−1)^m·B m
  rw [eq_neg_of_add_eq_zero_left h0, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun m _ => by rw [pow_succ]; ring)

end MockTheta5.JTP
