/-
# Euler's pentagonal number theorem — statement side (the generalized pentagonal series)

**Target.** `qfac2Inf = pentSum`, i.e. in the variable `t` (with `t² = q`)

  `∏_{m≥1} (1 − t^{2m})  =  Σ_{n∈ℤ} (−1)ⁿ t^{n(3n+1)}`,

which is Euler's pentagonal number theorem `∏(1−qᵐ) = Σ_k (−1)ᵏ q^{k(3k−1)/2}` (the exponents `n(3n+1)`
are `2×` generalized pentagonal numbers; the `(−1)ⁿ` signs match under the reindexing `n ↔ −k`).

**Proof route (worked out; the substitution is the pending build).** Apply the two-variable substitution
`q ↦ t³`, `z ↦ −t` to the bilateral Jacobi triple product `qfac2InfL · SZ · SZinv = bilateralTheta`:

  * `Φ(bilateralTheta) = Σ_n z^n q^{n²} ↦ Σ_n (−t)ⁿ (t³)^{n²} = Σ_n (−1)ⁿ t^{n(3n+1)} = pentSum`;
  * `Φ(qfac2InfL · SZ · SZinv) = ∏(1−t^{6n}) · ∏(1−t^{6i+4}) · ∏(1−t^{6i+2}) = ∏_{m≥1}(1−t^{2m}) = qfac2Inf`
    (the `z⁻¹` of `SZinv` combines with the large `q`-powers to keep every exponent `≥ 0`, landing in `ℤ[[t]]`).

The map `Φ` is a *topological* power-series substitution (`z⁻¹ ↦ −t⁻¹` forces an intermediate Laurent/Hahn
series ring where `t` is invertible, and `q ↦ t³` substitutes the variable by a positive-order element). That
`PowerSeries.subst` / `HahnSeries` machinery is the remaining build; this file fixes the **statement side**:
`pentSum` and its coefficient stabilization, ready for that proof. No `sorry`.
-/
import RamanujanTau.MockTheta5JacobiL8

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- the paired generalized-pentagonal term `(−1)^{j+1}(t^{(j+1)(3(j+1)−1)} + t^{(j+1)(3(j+1)+1)})`
(the `n = ±(j+1)` contributions). -/
noncomputable def pentTerm (j : ℕ) : PowerSeries ℤ :=
  PowerSeries.C ((-1 : ℤ) ^ (j + 1)) *
    (X ^ ((j + 1) * (3 * (j + 1) - 1)) + X ^ ((j + 1) * (3 * (j + 1) + 1)))

/-- the paired term has `t`-degree `≥ (j+1)(3(j+1)−1)`, so its lower coefficients vanish. -/
lemma coeff_pentTerm_zero {j k : ℕ} (h : k < (j + 1) * (3 * (j + 1) - 1)) :
    coeff k (pentTerm j) = 0 := by
  have hb : (j + 1) * (3 * (j + 1) - 1) ≤ (j + 1) * (3 * (j + 1) + 1) := by
    apply Nat.mul_le_mul_left; omega
  rw [pentTerm, PowerSeries.coeff_C_mul, map_add, PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow,
      if_neg (by omega), if_neg (by omega), add_zero, mul_zero]

/-- the finite truncation `1 + Σ_{j<M} pentTerm j` (the leading `1` is the `n = 0` term). -/
noncomputable def pentFinite (M : ℕ) : PowerSeries ℤ := 1 + ∑ j ∈ Finset.range M, pentTerm j

/-- **The generalized pentagonal series** `Σ_{n∈ℤ} (−1)ⁿ t^{n(3n+1)}`, by coefficient stabilization.
With `t² = q` this is the right side of Euler's pentagonal number theorem. -/
noncomputable def pentSum : PowerSeries ℤ := mk fun k => coeff k (pentFinite (k + 1))

lemma coeff_pent_stable {k : ℕ} : ∀ {M N : ℕ}, k < M → M ≤ N →
    coeff k (pentFinite N) = coeff k (pentFinite M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · have hsucc : pentFinite (N + 1) = pentFinite N + pentTerm N := by
          rw [pentFinite, pentFinite, Finset.sum_range_succ]; ring
        rw [hsucc, map_add,
            coeff_pentTerm_zero (show k < (N + 1) * (3 * (N + 1) - 1) by
              have : N + 1 ≤ (N + 1) * (3 * (N + 1) - 1) :=
                Nat.le_mul_of_pos_right _ (by omega); omega),
            add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

/-- coeff `k` of the pentagonal series equals any truncation past `k`. -/
lemma coeff_pentSum {k M : ℕ} (hM : k + 1 ≤ M) : coeff k pentSum = coeff k (pentFinite M) := by
  rw [pentSum, coeff_mk, coeff_pent_stable (Nat.lt_succ_self k) hM]

/-- The constant term is `1` (the `n = 0` term). -/
@[simp] lemma coeff_zero_pentSum : coeff 0 pentSum = 1 := by
  rw [coeff_pentSum (le_refl 1), pentFinite, Finset.sum_range_one, map_add,
      coeff_pentTerm_zero (by norm_num)]
  simp

end MockTheta5.JTP
