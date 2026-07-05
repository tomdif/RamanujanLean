/-
# Triangular Jacobi triple product, stone 1: the bilateral theta `Σ_{n∈ℤ} zⁿ q^{n(n−1)/2}`

The keystone toward **base-`q` Jacobi's cube** `(q;q)³ = Σ(−1)ᵐ(2m+1)q^{m(m+1)/2}` (and the pentagonal
*product* form) is the **triangular** bilateral Jacobi triple product

  `Σ_{n∈ℤ} zⁿ q^{n(n−1)/2}  =  ∏_{n≥1}(1−qⁿ) · ∏_{n≥1}(1+z qⁿ⁻¹) · ∏_{n≥1}(1+z⁻¹ qⁿ)`     (†)

— the base-`q` analogue of the repo's square `bilateralTheta`/`classical_jacobi_triple_product`. Base-`q`
Jacobi's cube then falls out of (†) by `d/dz|_{z=−1}` (the `(1+z)` factor of the middle product vanishes at
`z=−1`, its derivative dropping the cube `(q;q)³`; the series side pairs `n ↔ 1−n` into the `(2m+1)` weight).
`z=−1` is a **unit**, so this sidesteps the non-unit `ℤ((q))` wall — the route is reachable.

**This file (stone 1, fully verified, no `sorry`):** the right-hand-*series* object of (†), `triTheta`, as a
genuine `PowerSeries (LaurentPolynomial ℤ)` via coefficient stabilization — exactly mirroring how
`MockTheta5JacobiBilateral` built the square `bilateralTheta`. The exponent `C(n,2) = n(n−1)/2` is constant on
the pairs `n = m+1` and `n = −m` (both `= m(m+1)/2`), so the paired term is `(z^{m+1} + z^{−m}) q^{m(m+1)/2}`.
Correctness is pinned by `coeff_zero_triTheta` (`= 1 + z`) and `coeff_one_triTheta` (`= z⁻¹ + z²`).

**Remaining stones (multi-session, tracked):** (2) the one-sided products `∏(1+zqⁱ)`, `∏(1+z⁻¹qⁱ)` in the
`z`-outer ring from `euler_cauchy` (mirror of `SZ_eq_jtpProdQInf`); (3) the bilateral assembly (†) via the
existing generic `zProj`/`zProj_ext` machinery; (4) the `d/dz|_{z=−1}` functional (buildable from `zProj`) and
the vanishing-factor evaluation giving `(q;q)³`. Stones (2)–(3) reuse the base-`q` Cauchy `euler_cauchy` and
the *generic* z-projection lemmas, so no new z-machinery is needed — only the base-`q` transport.
-/
import RamanujanTau.MockTheta5JacobiBilateral

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial

/-- the `m`-th term order `m(m+1)/2` dominates `m` (so partial sums stabilize per coefficient). -/
lemma tri_ge' (m : ℕ) : m ≤ m * (m + 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  rcases Nat.eq_zero_or_pos m with h | h
  · simp [h]
  · exact Nat.mul_le_mul_left m (by omega)

/-- The paired `n = m+1, n = −m` term of the triangular theta: `(z^{m+1} + z^{−m})·q^{m(m+1)/2}`
(both indices have `C(n,2) = m(m+1)/2`). -/
noncomputable def triTerm (m : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  X ^ (m * (m + 1) / 2) * PowerSeries.C (T ((m : ℤ) + 1) + T (-(m : ℤ)))

/-- The finite truncation `Σ_{m<M} triTerm m` (covers indices `n = −M+1 .. M`). -/
noncomputable def triFinite (M : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  ∑ m ∈ Finset.range M, triTerm m

/-- **The triangular bilateral theta `Σ_{n∈ℤ} zⁿ q^{n(n−1)/2}`**, over `ℤ[z;z⁻¹]`, by stabilization. -/
noncomputable def triTheta : PowerSeries (LaurentPolynomial ℤ) :=
  mk fun k => coeff k (triFinite (k + 1))

/-- The paired term has `q`-degree `m(m+1)/2`, so its coefficients below that vanish. -/
lemma coeff_triTerm_zero {m k : ℕ} (h : k < m * (m + 1) / 2) : coeff k (triTerm m) = 0 := by
  rw [triTerm, coeff_X_pow_mul', if_neg (Nat.not_le.mpr h)]

/-- coeff `k` of the truncated sum stabilizes once `M > k`. -/
lemma coeff_tri_stable {k : ℕ} : ∀ {M N : ℕ}, k < M → M ≤ N →
    coeff k (triFinite N) = coeff k (triFinite M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · have hsucc : triFinite (N + 1) = triFinite N + triTerm N := by
          rw [triFinite, triFinite, Finset.sum_range_succ]
        rw [hsucc, map_add, coeff_triTerm_zero (by have := tri_ge' N; omega), add_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

/-- coeff `k` of the triangular theta equals any finite truncation with `M ≥ k+1`. -/
lemma coeff_triTheta {k M : ℕ} (hM : k + 1 ≤ M) :
    coeff k triTheta = coeff k (triFinite M) := by
  rw [triTheta, coeff_mk, coeff_tri_stable (Nat.lt_succ_self k) hM]

/-- **Correctness (constant term): `q⁰` coefficient is `z⁰ + z¹ = 1 + z`** (the `n = 0, 1` terms). -/
lemma coeff_zero_triTheta : coeff 0 triTheta = T 1 + T 0 := by
  rw [coeff_triTheta (le_refl 1), triFinite, Finset.sum_range_one, triTerm]
  simp

/-- **Correctness (`q¹`): coefficient is `z⁻¹ + z²`** (the `n = −1, 2` terms, both `C(n,2)=1`). -/
lemma coeff_one_triTheta : coeff 1 triTheta = T (-1) + T 2 := by
  rw [coeff_triTheta (show 1 + 1 ≤ 2 from le_refl 2), triFinite,
      Finset.sum_range_succ, Finset.sum_range_one, map_add]
  have h0 : coeff 1 (triTerm 0) = 0 := by rw [triTerm]; simp
  have h1 : coeff 1 (triTerm 1) = T 2 + T (-1) := by
    rw [triTerm]; simp
  rw [h0, h1, zero_add, add_comm]

end MockTheta5.JTP
