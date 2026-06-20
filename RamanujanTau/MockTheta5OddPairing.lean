/-
# Odd-index pairing: `(−q;q²)_∞ · (q;q²)_∞ = (q²;q⁴)_∞`

The factorwise pairing `(1+q^{2k−1})(1−q^{2k−1}) = 1−q^{2(2k−1)}` lifted to infinite products: the
distinct-odd-part product `(−q;q²)_∞ = ∏(1+q^{2n−1})` times the odd-part product `(q;q²)_∞ = ∏(1−q^{2n−1})`
equals `(q²;q⁴)_∞ = ∏(1−q^{4n−2}) = E2((q;q²)_∞)`.

Same shape as `prodOnePlus_mul_qfacInf`, but in the odd sub-lattice. No `sorry`.
-/
import RamanujanTau.MockTheta5EvenOdd

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- the finite distinct-odd product `∏_{k<m}(1 + q^{2k+1})` (`(−q;q²)`-Pochhammer). -/
noncomputable def negOddFac (m : ℕ) : PowerSeries ℤ := ∏ k ∈ Finset.range m, (1 + X ^ (2 * k + 1))

lemma negOddFac_succ (m : ℕ) : negOddFac (m + 1) = negOddFac m * (1 + X ^ (2 * m + 1)) := by
  rw [negOddFac, negOddFac, Finset.prod_range_succ]

lemma coeff_negOddFac_stable {k : ℕ} : ∀ {M N : ℕ}, k < M → M ≤ N →
    coeff k (negOddFac N) = coeff k (negOddFac M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · rw [negOddFac_succ, mul_add, mul_one, map_add]
        have hz : coeff k (negOddFac N * X ^ (2 * N + 1)) = 0 := by
          rw [mul_comm]; exact MockTheta5.mt_coeff_Xpow_mul_zero (negOddFac N) (2 * N + 1) k (by omega)
        rw [hz, add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

/-- **`(−q;q²)_∞ = ∏_{n≥1}(1 + q^{2n−1})`** (distinct-odd-part generating function). -/
noncomputable def negOddPochInf : PowerSeries ℤ := mk fun k => coeff k (negOddFac (k + 1))

lemma coeff_negOddPochInf {k N : ℕ} (hN : k + 1 ≤ N) :
    coeff k negOddPochInf = coeff k (negOddFac N) := by
  rw [negOddPochInf, coeff_mk, coeff_negOddFac_stable (Nat.lt_succ_self k) hN]

/-- finite odd-index pairing `∏(1+q^{2k−1})·∏(1−q^{2k−1}) = ∏(1−q^{2(2k−1)}) = E2(∏(1−q^{2k−1}))`. -/
lemma negOddFac_mul_oddFac (m : ℕ) : negOddFac m * oddFac m = E2 (oddFac m) := by
  have hL : negOddFac m * oddFac m
      = ∏ k ∈ Finset.range m, (1 - X ^ (2 * (2 * k + 1)) : PowerSeries ℤ) := by
    rw [negOddFac, oddFac, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by ring
  have hR : E2 (oddFac m) = ∏ k ∈ Finset.range m, (1 - X ^ (2 * (2 * k + 1)) : PowerSeries ℤ) := by
    rw [oddFac, map_prod]
    exact Finset.prod_congr rfl fun k _ => by rw [map_sub, map_one, map_pow, E2_X, ← pow_mul]
  rw [hL, hR]

/-- `(q²;q⁴)_∞ = E2((q;q²)_∞)` agrees with the finite even product below degree `2M`. -/
lemma coeff_E2oddPochInf_eq {i M : ℕ} (h : i + 1 ≤ M) :
    coeff i (E2 oddPochInf) = coeff i (E2 (oddFac M)) := by
  have hdvd : (X : PowerSeries ℤ) ^ M ∣ (oddPochInf - oddFac M) := by
    rw [PowerSeries.X_pow_dvd_iff]; intro j hj
    rw [map_sub, coeff_oddPochInf (show j + 1 ≤ M by omega), sub_self]
  obtain ⟨g, hg⟩ := hdvd
  have hz : coeff i (E2 oddPochInf) - coeff i (E2 (oddFac M)) = 0 := by
    rw [← map_sub, ← map_sub, hg, map_mul, E2_X_pow]
    exact MockTheta5.mt_coeff_Xpow_mul_zero _ _ i (by omega)
  exact sub_eq_zero.mp hz

/-- **`(−q;q²)_∞ · (q;q²)_∞ = (q²;q⁴)_∞`** — distinct odd parts × odd parts. -/
theorem negOddPochInf_mul_oddPochInf : negOddPochInf * oddPochInf = E2 oddPochInf := by
  ext N
  have h1 : coeff N (negOddPochInf * oddPochInf)
      = coeff N (negOddFac (N + 1) * oddFac (N + 1)) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [coeff_negOddPochInf (show p.1 + 1 ≤ N + 1 by omega),
        coeff_oddPochInf (show p.2 + 1 ≤ N + 1 by omega)]
  rw [h1, negOddFac_mul_oddFac, coeff_E2oddPochInf_eq (le_refl (N + 1))]

end MockTheta5.JTP
