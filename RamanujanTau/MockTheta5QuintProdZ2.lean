/-
# Quintuple product, stone 2 (z²-side): the product `∏_{i≥0}(1 − z² q^{2i+1})`

The quintuple product side carries the base-`q²` factors `∏_{n≥1}(1 − z² q^{2n−1})` and its `z⁻²` mirror.
This is the one-sided Jacobi product `jtpProdQInf = ∏_{i≥0}(1 + z q^{2i+1})` with `z ↦ −z²`: the sign gives
`(−1)ᵏ` and the doubling puts the `k`-th term at **z-degree 2k**, so

  `zProj_jtp2ProdInf k :  zProj (2k) (∏_{i≥0}(1 − z² q^{2i+1})) = (−1)ᵏ · q^{k²} / (q²;q²)_k`,

with `zProj = 0` at odd or negative z-degrees. Transport mirrors `jtpProdQ_eq_sum` (base change `q ↦ q²` via
`finite_jtp`), plus the sign hom `negX` (reused from the base-`q` side) and a variable map `Psi2 : X ↦ C(T 2)`
carrying `z ↦ z²`. The sign is kept outside `map C` as `(− C(T 2))ᵏ`, converted to the signed Laurent
monomial `C((−1)ᵏ · T (2k))` inside `zProj` (`negC2T_pow`, `zProj_mapC_scaledCT`). No `sorry`.
-/
import RamanujanTau.MockTheta5QuintProdZ

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-- variable map `z ↦ z²` (`X ↦ C(T 2)`), base-change coeffs `a(q) ↦ map C a`. -/
noncomputable def Psi2 : Polynomial (PowerSeries ℤ) →+* PowerSeries (LaurentPolynomial ℤ) :=
  Polynomial.eval₂RingHom (PowerSeries.map (LaurentPolynomial.C)) (PowerSeries.C (LaurentPolynomial.T 2))

@[simp] lemma Psi2_C (a : PowerSeries ℤ) :
    Psi2 (Polynomial.C a) = PowerSeries.map (LaurentPolynomial.C) a := by
  rw [Psi2, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]

@[simp] lemma Psi2_X : Psi2 Polynomial.X = PowerSeries.C (LaurentPolynomial.T 2) := by
  rw [Psi2, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

/-- `(− z²)ᵏ` as a signed Laurent monomial at degree `2k`: `(− C(T 2))ᵏ = C((−1)ᵏ · T (2k))`. -/
lemma negC2T_pow (k : ℕ) :
    (- PowerSeries.C (LaurentPolynomial.T (2 : ℤ))) ^ k
      = PowerSeries.C (LaurentPolynomial.C ((-1 : ℤ) ^ k) * LaurentPolynomial.T (2 * (k : ℤ))) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, mul_neg, ← map_mul, mul_assoc,
        show LaurentPolynomial.T (2 * (k : ℤ)) * LaurentPolynomial.T 2 = LaurentPolynomial.T (2 * ((k : ℤ) + 1)) from by
          rw [← LaurentPolynomial.T_add, show 2 * (k : ℤ) + 2 = 2 * ((k : ℤ) + 1) from by ring],
        ← map_neg, ← neg_mul, ← map_neg,
        show (-(-1 : ℤ) ^ k) = (-1 : ℤ) ^ (k + 1) from by rw [pow_succ]; ring,
        show (2 * ((k : ℤ) + 1)) = 2 * ((k + 1 : ℕ) : ℤ) from by push_cast; ring]

/-- signed/scaled variant of `zProj_mapC_CT`: `zProj κ (map C a · C(s·T d)) = if d=κ then C(s)·a else 0`. -/
lemma zProj_mapC_scaledCT (a : PowerSeries ℤ) (s d : ℤ) (κ : ℤ) :
    zProj κ (PowerSeries.map (LaurentPolynomial.C) a
        * PowerSeries.C (LaurentPolynomial.C s * LaurentPolynomial.T d))
      = if d = κ then PowerSeries.C s * a else 0 := by
  ext m
  rw [coeff_zProj, PowerSeries.coeff_mul_C, PowerSeries.coeff_map, ← mul_assoc, ← map_mul,
      ← LaurentPolynomial.single_eq_C_mul_T, Finsupp.single_apply]
  split_ifs with h
  · rw [PowerSeries.coeff_C_mul, mul_comm]
  · simp

/-- the finite signed product `∏_{i<n}(1 − z² q^{2i+1})` in the `q`-outer ring. -/
noncomputable def jtp2Prod (n : ℕ) : PowerSeries (LaurentPolynomial ℤ) :=
  ∏ i ∈ Finset.range n, (1 - X ^ (2 * i + 1) * PowerSeries.C (LaurentPolynomial.T 2))

/-- transport the sign-flipped base-`q²` JTP: `∏(1 − z² q^{2i+1}) = Σ q^{k²} [n,k]_{q²} (−z²)ᵏ`. -/
lemma jtp2Prod_eq_sum (n : ℕ) :
    jtp2Prod n = ∑ k ∈ Finset.range (n + 1),
      X ^ (k ^ 2) * PowerSeries.map (LaurentPolynomial.C) (E2 (gaussBinom n k))
        * (- PowerSeries.C (LaurentPolynomial.T (2 : ℤ))) ^ k := by
  have hpoly := finite_jtp n
  have hL : (∏ i ∈ Finset.range n, (1 - Polynomial.C (qq ^ (2 * i + 1)) * Polynomial.X))
      = negX (∏ i ∈ Finset.range n, (1 + Polynomial.C (qq ^ (2 * i + 1)) * Polynomial.X)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ => by rw [map_add, map_one, map_mul negX, negX_C, negX_X]; ring)
  have hR : (∑ k ∈ Finset.range (n + 1),
        Polynomial.C (qq ^ (k ^ 2) * E2 (gaussBinom n k)) * (-Polynomial.X) ^ k)
      = negX (∑ k ∈ Finset.range (n + 1),
        Polynomial.C (qq ^ (k ^ 2) * E2 (gaussBinom n k)) * Polynomial.X ^ k) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [map_mul negX, negX_C, map_pow negX, negX_X])
  have psigned : (∏ i ∈ Finset.range n, (1 - Polynomial.C (qq ^ (2 * i + 1)) * Polynomial.X))
      = ∑ k ∈ Finset.range (n + 1),
        Polynomial.C (qq ^ (k ^ 2) * E2 (gaussBinom n k)) * (-Polynomial.X) ^ k := by
    rw [hL, hR, hpoly]
  have hq : jtp2Prod n = Psi2 (∏ i ∈ Finset.range n, (1 - Polynomial.C (qq ^ (2 * i + 1)) * Polynomial.X)) := by
    rw [jtp2Prod, map_prod]
    exact Finset.prod_congr rfl (fun i _ => by
      rw [map_sub, map_one, map_mul, Psi2_C, Psi2_X, qq, map_pow, PowerSeries.map_X])
  rw [hq, psigned, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul Psi2, Psi2_C, map_pow Psi2, map_neg, Psi2_X,
      map_mul (PowerSeries.map (LaurentPolynomial.C)),
      map_pow (PowerSeries.map (LaurentPolynomial.C)), qq, PowerSeries.map_X]

lemma jtp2Prod_succ (n : ℕ) :
    jtp2Prod (n + 1) = jtp2Prod n * (1 - X ^ (2 * n + 1) * PowerSeries.C (LaurentPolynomial.T 2)) := by
  rw [jtp2Prod, jtp2Prod, Finset.prod_range_succ]

lemma coeff_jtp2Prod_stable {k : ℕ} : ∀ {M N : ℕ}, k < M → M ≤ N →
    coeff k (jtp2Prod N) = coeff k (jtp2Prod M) := by
  intro M N hkM hMN
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_or_ge M (N + 1) with h | h
      · rw [jtp2Prod_succ, mul_sub, mul_one, map_sub]
        have hz : coeff k (jtp2Prod N * (X ^ (2 * N + 1) * PowerSeries.C (LaurentPolynomial.T 2))) = 0 := by
          rw [mul_left_comm, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
        rw [hz, sub_zero, ih (by omega)]
      · rw [show M = N + 1 from by omega]

/-- **`∏_{i≥0}(1 − z² q^{2i+1})`** as a formal power series. -/
noncomputable def jtp2ProdInf : PowerSeries (LaurentPolynomial ℤ) := mk fun k => coeff k (jtp2Prod (k + 1))

lemma coeff_jtp2ProdInf {k N : ℕ} (hN : k + 1 ≤ N) : coeff k jtp2ProdInf = coeff k (jtp2Prod N) := by
  rw [jtp2ProdInf, coeff_mk, coeff_jtp2Prod_stable (Nat.lt_succ_self k) hN]

lemma zProj_jtp2Prod_term (k n : ℕ) (κ : ℤ) :
    zProj κ (X ^ (k ^ 2) * PowerSeries.map (LaurentPolynomial.C) (E2 (gaussBinom n k))
      * (- PowerSeries.C (LaurentPolynomial.T (2 : ℤ))) ^ k)
      = if (2 * (k : ℤ)) = κ then PowerSeries.C ((-1 : ℤ) ^ k) * (X ^ (k ^ 2) * E2 (gaussBinom n k)) else 0 := by
  rw [negC2T_pow,
      show X ^ (k ^ 2) * PowerSeries.map (LaurentPolynomial.C) (E2 (gaussBinom n k))
        = PowerSeries.map (LaurentPolynomial.C) (X ^ (k ^ 2) * E2 (gaussBinom n k)) from by
        rw [map_mul, map_pow, PowerSeries.map_X],
      zProj_mapC_scaledCT]

lemma zProj_jtp2Prod (k M : ℕ) (h : k < M) :
    zProj (2 * (k : ℤ)) (jtp2Prod M)
      = PowerSeries.C ((-1 : ℤ) ^ k) * (X ^ (k ^ 2) * E2 (gaussBinom M k)) := by
  rw [jtp2Prod_eq_sum, zProj_sum,
      Finset.sum_eq_single k
        (fun i _ hik => by rw [zProj_jtp2Prod_term, if_neg (by omega)])
        (fun hk => absurd (Finset.mem_range.mpr (by omega)) hk),
      zProj_jtp2Prod_term, if_pos rfl]

lemma coeff_X_signed_E2gauss_stable (m k : ℕ) :
    coeff m (PowerSeries.C ((-1 : ℤ) ^ k) * (X ^ (k ^ 2) * E2 (gaussBinom (m + k + 1) k)))
      = coeff m (PowerSeries.C ((-1 : ℤ) ^ k) * (X ^ (k ^ 2) * Ring.inverse (E2 (qfac k)))) := by
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, coeff_X_E2gauss_stable]

/-- **The signed base-`q²` one-sided Cauchy identity, projected**: the `z^{2k}`-coefficient of
`∏_{i≥0}(1 − z² q^{2i+1})` is `(−1)ᵏ q^{k²} / (q²;q²)_k`. -/
lemma zProj_jtp2ProdInf (k : ℕ) :
    zProj (2 * (k : ℤ)) jtp2ProdInf
      = PowerSeries.C ((-1 : ℤ) ^ k) * (X ^ (k ^ 2) * Ring.inverse (E2 (qfac k))) := by
  ext m
  rw [coeff_zProj, coeff_jtp2ProdInf (show m + 1 ≤ m + k + 1 by omega), ← coeff_zProj,
      zProj_jtp2Prod k (m + k + 1) (by omega), coeff_X_signed_E2gauss_stable]

/-- odd z-degrees vanish (only even degrees `2k` appear). -/
lemma zProj_jtp2Prod_odd {κ : ℤ} (hκ : ¬ ∃ k : ℕ, (2 * (k : ℤ)) = κ) : zProj κ jtp2ProdInf = 0 := by
  ext m
  rw [coeff_zProj, coeff_jtp2ProdInf (le_refl (m + 1)), ← coeff_zProj, jtp2Prod_eq_sum, zProj_sum,
      Finset.sum_eq_zero (fun k _ => by rw [zProj_jtp2Prod_term, if_neg (fun heq => hκ ⟨k, heq⟩)])]

end MockTheta5.JTP
