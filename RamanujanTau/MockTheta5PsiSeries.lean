/-
# Gauss's series form of Ramanujan's `ψ`: `ψ(q) = Σ_{n≥0} q^{n(n+1)/2}`

The bilateral triangular Jacobi triple product `triTheta = Σ_{n∈ℤ} zⁿ q^{n(n−1)/2}` double-covers the
triangular numbers (`n = k+1` and `n = −k` both give `T(k)`). Evaluating at `z = 1`:

  * **series side:** `map ev1 triTheta = 2 · Σ_{n≥0} q^{n(n+1)/2}`  (`map_ev1_triTheta_double`),
  * **product side:** via `triProdQInf = (1+z)·triProdQ1Inf`, `map ev1 triTheta = 2 · ((q;q)_∞ · ∏(1+qⁿ)²)`
    (`map_ev1_triTheta_prod`).

Cancelling the `2` (valid — `PowerSeries ℤ` is a domain) and using the distinct = odd algebra gives

  **`psi_eq_series`:**  `ψ(q) = Σ_{n≥0} q^{n(n+1)/2}`.

No `sorry`.
-/
import RamanujanTau.MockTheta5RamanujanTheta
import RamanujanTau.MockTheta5EvenOdd
import RamanujanTau.MockTheta5EulerDistinctOdd
import RamanujanTau.MockTheta5TriangularBilateral

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

private lemma two_eq_C : (2 : PowerSeries ℤ) = PowerSeries.C 2 := (map_ofNat PowerSeries.C 2).symm

private lemma coeff_two_mul (k : ℕ) (Y : PowerSeries ℤ) : coeff k (2 * Y) = 2 * coeff k Y := by
  rw [two_eq_C, PowerSeries.coeff_C_mul]

private lemma two_ne_zero' : (2 : PowerSeries ℤ) ≠ 0 := by
  rw [two_eq_C]
  intro h
  exact (two_ne_zero : (2 : ℤ) ≠ 0) (PowerSeries.C_injective (h.trans (map_zero _).symm))

/-! ### `z = 1` is `z ↦ z⁻¹`-invariant -/

lemma ev1_CT (b κ : ℤ) : ev1 (LaurentPolynomial.C b * T κ) = b := by
  rw [map_mul, ev1_C, ev1_T, mul_one]

lemma ev1_single (κ b : ℤ) : ev1 (Finsupp.single κ b : LaurentPolynomial ℤ) = b := by
  rw [show (Finsupp.single κ b : LaurentPolynomial ℤ) = LaurentPolynomial.C b * T κ from
        LaurentPolynomial.single_eq_C_mul_T b κ]
  exact ev1_CT b κ

lemma ev1_invertHom (p : LaurentPolynomial ℤ) : ev1 (invertHom p) = ev1 p := by
  have h : (ev1 : LaurentPolynomial ℤ →+* ℤ).toAddMonoidHom.comp invertHom.toAddMonoidHom
      = (ev1 : LaurentPolynomial ℤ →+* ℤ).toAddMonoidHom := by
    apply Finsupp.addHom_ext
    intro κ b
    show ev1 (invertHom (Finsupp.single κ b)) = ev1 (Finsupp.single κ b)
    rw [invert_single, ev1_single, ev1_single]
  exact DFunLike.congr_fun h p

lemma map_ev1_map_invert (Y : PowerSeries (LaurentPolynomial ℤ)) :
    PowerSeries.map ev1 (PowerSeries.map invertHom Y) = PowerSeries.map ev1 Y := by
  ext n; rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map, ev1_invertHom]

/-! ### `map ev1` of the product factors -/

lemma map_ev1_qfacInfL : PowerSeries.map ev1 qfacInfL = qfacInf := by
  ext n; rw [qfacInfL, PowerSeries.coeff_map, PowerSeries.coeff_map, ev1_C]

lemma map_ev1_factor (i : ℕ) :
    PowerSeries.map ev1 (1 + X ^ (i + 1) * PowerSeries.C (T 1)) = 1 + X ^ (i + 1) := by
  rw [map_add, map_one, map_mul, map_pow, PowerSeries.map_X, PowerSeries.map_C, ev1_T, map_one, mul_one]

lemma map_ev1_triProdQ1 (n : ℕ) : PowerSeries.map ev1 (triProdQ1 n) = qfacPos n := by
  rw [triProdQ1, qfacPos, map_prod]
  exact Finset.prod_congr rfl (fun i _ => map_ev1_factor i)

lemma map_ev1_triProdQ1Inf : PowerSeries.map ev1 triProdQ1Inf = prodOnePlus := by
  ext n
  rw [PowerSeries.coeff_map, coeff_triProdQ1Inf (le_refl (n + 1)), ← PowerSeries.coeff_map,
      map_ev1_triProdQ1]
  simp only [prodOnePlus, PowerSeries.coeff_mk]

lemma map_ev1_one_add : PowerSeries.map ev1 (1 + PowerSeries.C (T 1)) = 2 := by
  rw [map_add, map_one, PowerSeries.map_C, ev1_T, map_one]; exact one_add_one_eq_two

/-! ### the `z = 1` corollary (product side) -/

lemma map_ev1_triTheta_prod :
    PowerSeries.map ev1 triTheta = 2 * (qfacInf * prodOnePlus ^ 2) := by
  have key := congrArg (PowerSeries.map ev1) bilateral_triangular_JTP
  rw [triProdQInf_eq_split, map_mul, map_mul, map_mul, map_ev1_qfacInfL, map_ev1_one_add,
      map_ev1_triProdQ1Inf, map_ev1_map_invert, map_ev1_triProdQ1Inf] at key
  rw [← key]; ring

/-! ### the double cover (series side) -/

/-- `ψ(q) = Σ_{n≥0} q^{n(n+1)/2}`, the Gauss series, defined by coefficient stabilization. -/
noncomputable def psiSum : PowerSeries ℤ := mtSum (fun n => n * (n + 1) / 2) (fun _ => 1)

lemma map_ev1_triTerm (m : ℕ) :
    PowerSeries.map ev1 (triTerm m) = 2 * X ^ (m * (m + 1) / 2) := by
  rw [triTerm, map_mul, map_pow, PowerSeries.map_X, PowerSeries.map_C, map_add, ev1_T, ev1_T,
      show PowerSeries.C ((1 : ℤ) + 1) = 2 from by rw [map_add, map_one]; exact one_add_one_eq_two,
      mul_comm]

lemma map_ev1_triTheta_double : PowerSeries.map ev1 triTheta = 2 * psiSum := by
  ext k
  rw [coeff_two_mul, PowerSeries.coeff_map, coeff_triTheta (le_refl (k + 1)), ← PowerSeries.coeff_map,
      triFinite, map_sum, map_sum, psiSum, coeff_mtSum _ _ (fun n => tri_ge n) (le_refl (k + 1)),
      Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [map_ev1_triTerm, coeff_two_mul, mul_one]

/-! ### the capstone -/

/-- **Gauss's identity `ψ(q) = Σ_{n≥0} q^{n(n+1)/2}`** — the series form of Ramanujan's theta `ψ`. -/
theorem psi_eq_series : psi = psiSum := by
  have h2 : psiSum = qfacInf * prodOnePlus ^ 2 :=
    mul_left_cancel₀ two_ne_zero' (by rw [← map_ev1_triTheta_double, map_ev1_triTheta_prod])
  rw [h2, show psi = qfac2Inf * Ring.inverse oddPochInf from rfl, ← prodOnePlus_eq_inverse,
      ← prodOnePlus_mul_qfacInf]
  ring

end MockTheta5.JTP
