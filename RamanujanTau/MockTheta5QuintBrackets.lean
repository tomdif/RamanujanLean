/-
# Quintuple product, stone 3 (RHS objects): the two "bracket" theta series

The quintuple product side factors as two brackets, each an existing bilateral JTP with a sign/substitution:

  * **Bracket 1** (base `q`):  `qfacInfL · P_z · P_{z⁻¹} = Σ_{n∈ℤ} (−1)ⁿ z⁻ⁿ q^{n(n−1)/2}`  (`= thetaA`),
    the triangular bilateral JTP under `z ↦ −z⁻¹`;
  * **Bracket 2** (base `q²`): `qfac2InfL · P_{z²} · P_{z⁻²} = Σ_{n∈ℤ} (−1)ⁿ z^{2n} q^{n²}`  (`= thetaB`),
    the square bilateral JTP under `z ↦ −z²`.

Then `quintTheta = thetaA · thetaB · (q²;q²)_∞⁻¹`, equivalently `thetaA · thetaB = qfac2InfL · quintTheta`,
which is the final assembly.

**This file** builds the two right-hand *series* objects `thetaA`, `thetaB` (mirrors of `triTheta`,
`bilateralTheta` with the signs and the `z⁻¹`/`z²` substitutions), by coefficient stabilization, with base
coefficient checks. The bracket identities themselves (the signed Durfee convolutions) and the final assembly
are the remaining stone-3 work. No `sorry`.
-/
import RamanujanTau.MockTheta5JacobiBilateral
import RamanujanTau.MockTheta5TriangularTheta

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial

/-! ### `thetaB = Σ_{n∈ℤ} (−1)ⁿ z^{2n} q^{n²}` — the square bracket RHS (base `q²`, `z ↦ −z²`). -/

/-- the paired `n = ±(m+1)` term: `(−1)^{m+1}(z^{2(m+1)} + z^{−2(m+1)}) q^{(m+1)²}`. -/
noncomputable def thetaBTerm (m : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  X ^ ((m + 1) ^ 2) * PowerSeries.C (LaurentPolynomial.C ((-1 : ℤ) ^ (m + 1))
    * (LaurentPolynomial.T (2 * ((m : ℤ) + 1)) + LaurentPolynomial.T (-(2 * ((m : ℤ) + 1)))))

noncomputable def thetaBFinite (M : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  1 + ∑ m ∈ Finset.range M, thetaBTerm m

/-- **`Σ_{n∈ℤ} (−1)ⁿ z^{2n} q^{n²}`.** -/
noncomputable def thetaB : PowerSeries (LaurentPolynomial ℤ) :=
  mk fun k => coeff k (thetaBFinite (k + 1))

lemma coeff_thetaBTerm_zero {m k : ℕ} (h : k < (m + 1) ^ 2) : coeff k (thetaBTerm m) = 0 := by
  rw [thetaBTerm, coeff_X_pow_mul', if_neg (Nat.not_le.mpr h)]

lemma coeff_thetaB_stable {k : ℕ} : ∀ {M N : ℕ}, k < M → M ≤ N →
    coeff k (thetaBFinite N) = coeff k (thetaBFinite M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · have hsucc : thetaBFinite (N + 1) = thetaBFinite N + thetaBTerm N := by
          rw [thetaBFinite, thetaBFinite, Finset.sum_range_succ]; ring
        rw [hsucc, map_add, coeff_thetaBTerm_zero (by nlinarith [hkM, h]), add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

lemma coeff_thetaB {k M : ℕ} (hM : k + 1 ≤ M) : coeff k thetaB = coeff k (thetaBFinite M) := by
  rw [thetaB, coeff_mk, coeff_thetaB_stable (Nat.lt_succ_self k) hM]

/-- constant term is `1` (the `n = 0` term). -/
lemma coeff_zero_thetaB : coeff 0 thetaB = 1 := by
  rw [coeff_thetaB (le_refl 1), thetaBFinite, Finset.sum_range_one, map_add,
      coeff_thetaBTerm_zero (by norm_num)]
  simp

/-- `q¹` coefficient is `−(z² + z⁻²)` (the `n = ±1` terms, sign `(−1)¹`). -/
lemma coeff_one_thetaB : coeff 1 thetaB = -(T 2 + T (-2)) := by
  rw [coeff_thetaB (show 1 + 1 ≤ 2 from le_refl 2), thetaBFinite, Finset.sum_range_succ,
      Finset.sum_range_one, map_add, map_add,
      show coeff 1 (1 : PowerSeries (LaurentPolynomial ℤ)) = 0 by
        rw [← map_one (PowerSeries.C (R := LaurentPolynomial ℤ)), coeff_C]; norm_num,
      coeff_thetaBTerm_zero (show (1 : ℕ) < (1 + 1) ^ 2 by norm_num), add_zero, zero_add, thetaBTerm]
  simp

/-! ### `thetaA = Σ_{n∈ℤ} (−1)ⁿ z⁻ⁿ q^{n(n−1)/2}` — the triangular bracket RHS (base `q`, `z ↦ −z⁻¹`). -/

/-- the paired `n = m+1` (`(−1)^{m+1} z^{−(m+1)}`) and `n = −m` (`(−1)^m z^{m}`) term, `q`-degree `m(m+1)/2`. -/
noncomputable def thetaATerm (m : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  X ^ (m * (m + 1) / 2) * PowerSeries.C (LaurentPolynomial.C ((-1 : ℤ) ^ m)
    * (LaurentPolynomial.T (m : ℤ) - LaurentPolynomial.T (-((m : ℤ) + 1))))

noncomputable def thetaAFinite (M : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  ∑ m ∈ Finset.range M, thetaATerm m

/-- **`Σ_{n∈ℤ} (−1)ⁿ z⁻ⁿ q^{n(n−1)/2}`.** -/
noncomputable def thetaA : PowerSeries (LaurentPolynomial ℤ) :=
  mk fun k => coeff k (thetaAFinite (k + 1))

lemma coeff_thetaATerm_zero {m k : ℕ} (h : k < m * (m + 1) / 2) : coeff k (thetaATerm m) = 0 := by
  rw [thetaATerm, coeff_X_pow_mul', if_neg (Nat.not_le.mpr h)]

lemma coeff_thetaA_stable {k : ℕ} : ∀ {M N : ℕ}, k < M → M ≤ N →
    coeff k (thetaAFinite N) = coeff k (thetaAFinite M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · have hsucc : thetaAFinite (N + 1) = thetaAFinite N + thetaATerm N := by
          rw [thetaAFinite, thetaAFinite, Finset.sum_range_succ]
        rw [hsucc, map_add, coeff_thetaATerm_zero (by have := tri_ge' N; omega), add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

lemma coeff_thetaA {k M : ℕ} (hM : k + 1 ≤ M) : coeff k thetaA = coeff k (thetaAFinite M) := by
  rw [thetaA, coeff_mk, coeff_thetaA_stable (Nat.lt_succ_self k) hM]

/-- constant term is `1 − z⁻¹` (the `n = 0` term `z⁰` and `n = 1` term `−z⁻¹`). -/
lemma coeff_zero_thetaA : coeff 0 thetaA = T 0 - T (-1) := by
  rw [coeff_thetaA (le_refl 1), thetaAFinite, Finset.sum_range_one, thetaATerm]
  simp

/-- `q¹` coefficient is `z⁻² − z¹` (the `n = 2` term `z⁻²` and `n = −1` term `−z¹`). -/
lemma coeff_one_thetaA : coeff 1 thetaA = T (-2) - T 1 := by
  rw [coeff_thetaA (show 1 + 1 ≤ 2 from le_refl 2), thetaAFinite, Finset.sum_range_succ,
      Finset.sum_range_one, map_add]
  have h0 : coeff 1 (thetaATerm 0) = 0 := by rw [thetaATerm]; simp
  have h1 : coeff 1 (thetaATerm 1) = T (-2) - T 1 := by rw [thetaATerm]; simp
  rw [h0, h1, zero_add]

end MockTheta5.JTP
