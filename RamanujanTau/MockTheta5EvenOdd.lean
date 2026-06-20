/-
# Even/odd factorization of `(q;q)_∞`, and Euler's distinct = odd made manifest

`(q²;q²)_∞ · (q;q²)_∞ = (q;q)_∞` — splitting the factors of `∏_{n≥1}(1−qⁿ)` by parity of `n` into the
even-index product `(q²;q²)_∞ = ∏(1−q^{2n})` and the odd-index product `(q;q²)_∞ = ∏(1−q^{2n−1})`.

Combined with `prodOnePlus_mul_qfacInf` (`∏(1+qⁿ)·(q;q)_∞ = (q²;q²)_∞`), this gives Euler's theorem in
its cleanest form: `∏_{n≥1}(1+qⁿ) · (q;q²)_∞ = 1`, i.e. the distinct-part generating function is exactly
`1/(q;q²)_∞`, the odd-part generating function.

The factorization is proved by an index split `range(2m) = evens ⊔ odds` (`evenOdd_eq`, by induction)
lifted to the infinite products by coefficient stabilization. No `sorry`.
-/
import RamanujanTau.MockTheta5EulerDistinctOdd

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- the finite odd-index product `∏_{k<m}(1 − q^{2k+1})` (generating odd partitions). -/
noncomputable def oddFac (m : ℕ) : PowerSeries ℤ := ∏ k ∈ Finset.range m, (1 - X ^ (2 * k + 1))

lemma oddFac_succ (m : ℕ) : oddFac (m + 1) = oddFac m * (1 - X ^ (2 * m + 1)) := by
  rw [oddFac, oddFac, Finset.prod_range_succ]

lemma coeff_oddFac_stable {k : ℕ} : ∀ {M N : ℕ}, k < M → M ≤ N →
    coeff k (oddFac N) = coeff k (oddFac M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · rw [oddFac_succ, mul_sub, mul_one, map_sub]
        have hz : coeff k (oddFac N * X ^ (2 * N + 1)) = 0 := by
          rw [mul_comm]; exact MockTheta5.mt_coeff_Xpow_mul_zero (oddFac N) (2 * N + 1) k (by omega)
        rw [hz, sub_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

/-- **`(q;q²)_∞ = ∏_{n≥1}(1 − q^{2n−1})`** (odd-partition generating function), by stabilization. -/
noncomputable def oddPochInf : PowerSeries ℤ := mk fun k => coeff k (oddFac (k + 1))

lemma coeff_oddPochInf {k N : ℕ} (hN : k + 1 ≤ N) : coeff k oddPochInf = coeff k (oddFac N) := by
  rw [oddPochInf, coeff_mk, coeff_oddFac_stable (Nat.lt_succ_self k) hN]

/-- finite even/odd factorization: `∏(1−q^{2k})·∏(1−q^{2k−1}) = ∏_{j<2m}(1−q^{j+1}) = (q;q)_{2m}`. -/
lemma evenOdd_eq (m : ℕ) : E2 (qfac m) * oddFac m = qfac (2 * m) := by
  induction m with
  | zero => simp [qfac, oddFac]
  | succ m ih =>
      have he2 : E2 (qfac (m + 1)) = E2 (qfac m) * (1 - X ^ (2 * (m + 1))) := by
        rw [qfac_succ, map_mul, map_sub, map_one, map_pow, E2_X, ← pow_mul]
      rw [he2, oddFac_succ, show 2 * (m + 1) = 2 * m + 1 + 1 from by ring,
          qfac_succ (2 * m + 1), qfac_succ (2 * m), ← ih]
      ring

/-- `(q²;q²)_∞` agrees with the finite even product `E2((q;q)_M)` below degree `2M`. -/
lemma coeff_qfac2Inf_eq {i M : ℕ} (h : i + 1 ≤ M) : coeff i qfac2Inf = coeff i (E2 (qfac M)) := by
  have hdvd : (X : PowerSeries ℤ) ^ M ∣ (qfacInf - qfac M) := by
    rw [PowerSeries.X_pow_dvd_iff]; intro j hj
    rw [map_sub, coeff_qfacInf (show j + 1 ≤ M by omega), sub_self]
  obtain ⟨g, hg⟩ := hdvd
  have hz : coeff i qfac2Inf - coeff i (E2 (qfac M)) = 0 := by
    rw [qfac2Inf, ← map_sub, ← map_sub, hg, map_mul, E2_X_pow]
    exact MockTheta5.mt_coeff_Xpow_mul_zero _ _ i (by omega)
  exact sub_eq_zero.mp hz

/-- **even/odd factorization of `(q;q)_∞`: `(q²;q²)_∞ · (q;q²)_∞ = (q;q)_∞`.** -/
theorem qfac2Inf_mul_oddPochInf : qfac2Inf * oddPochInf = qfacInf := by
  ext N
  have h1 : coeff N (qfac2Inf * oddPochInf) = coeff N (E2 (qfac (N + 1)) * oddFac (N + 1)) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [coeff_qfac2Inf_eq (show p.1 + 1 ≤ N + 1 by omega),
        coeff_oddPochInf (show p.2 + 1 ≤ N + 1 by omega)]
  rw [h1, evenOdd_eq, coeff_qfacInf (show N + 1 ≤ 2 * (N + 1) by omega)]

/-- **Euler's distinct = odd, fully manifest: `∏_{n≥1}(1+qⁿ) · (q;q²)_∞ = 1`** — the distinct-part
generating function is exactly `1/(q;q²)_∞`, the odd-part generating function. -/
theorem prodOnePlus_mul_oddPochInf : prodOnePlus * oddPochInf = 1 := by
  rw [prodOnePlus_eq, partitionGF, mul_right_comm, qfac2Inf_mul_oddPochInf,
      Ring.mul_inverse_cancel _ isUnit_qfacInf]

end MockTheta5.JTP
