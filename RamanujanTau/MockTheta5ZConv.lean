/-
# JTP step L8 (the z-Cauchy product): `SZ · SZinv`

The genuine crux of the bilateral Jacobi triple product. `SZ` carries z-degrees `≥ 0`, `SZinv` carries
z-degrees `≤ 0`; their product's `z^N` coefficient is the Cauchy convolution
`Σ_{k-j=N} (q^{k²}/(q²;q²)_k)(q^{j²}/(q²;q²)_j)`. We compute it *without* infinite-support `Finsupp`
machinery: each q-degree coefficient of `SZ`/`SZinv` is a finite sum of `single`s, so the product is a
finite `single`-convolution (`single a x * single b y = single (a+b) (x·y)`), and applying at z-degree `N`
selects the diagonal `k - j = N`.

This file builds that diagonal double-sum (`prodSZ_apply`). The downstream assembly collapses the diagonal
(`k = N + j` for `N ≥ 0`) into `Σ_j coeff m (q^{(N+j)²+j²}/((q²;q²)_{N+j}(q²;q²)_j))`, recognises the summand
as `q^{N²}·E2(rectTerm N j)` via `(N+j)²+j² = N² + 2(j²+Nj)`, and finishes with `durfee_rect_base_Q`.
No `sorry`.
-/
import RamanujanTau.MockTheta5ZProj

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial MockTheta5.Bailey

/-- the `k`-th Cauchy coefficient at q-degree `p`: `[q^p] q^{k²}/(q²;q²)_k`. -/
noncomputable def szc (p k : ℕ) : ℤ := coeff p (X ^ (k ^ 2) * Ring.inverse (E2 (qfac k)))

lemma coeff_SZterm_single (p k : ℕ) : coeff p (SZterm k) = Finsupp.single (k : ℤ) (szc p k) := by
  ext n; rw [SZterm_apply, Finsupp.single_apply]; rfl

lemma coeff_SZinvTerm_single (r j : ℕ) :
    coeff r (SZinvTerm j) = Finsupp.single (-(j : ℤ)) (szc r j) := by
  ext n; rw [SZinvTerm_apply, Finsupp.single_apply]; rfl

/-- **the z-Cauchy product, diagonal form**: the `z^N` coefficient of `coeff p SZ · coeff r SZinv`
is the diagonal double-sum `Σ_{k,j} [k - j = N] szc p k · szc r j` over the finite ranges. -/
lemma prodSZ_apply (p r : ℕ) (N : ℤ) :
    (coeff p SZ * coeff r SZinv) N
      = ∑ k ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (r + 1),
          (if (k : ℤ) - j = N then szc p k * szc r j else 0) := by
  rw [coeff_SZ (le_refl (p + 1)), coeff_SZinv (le_refl (r + 1)), SZfinite, SZinvFinite,
      map_sum, map_sum]
  simp_rw [coeff_SZterm_single, coeff_SZinvTerm_single]
  rw [Finset.sum_mul_sum]
  simp_rw [AddMonoidAlgebra.single_mul_single]
  rw [laurentSum_apply]
  simp_rw [laurentSum_apply, Finsupp.single_apply, ← sub_eq_add_neg]

/-! ### Recognising the diagonal summand as `E2 (rectTerm N j)` -/

lemma E2_X_pow (e : ℕ) : E2 (X ^ e : PowerSeries ℤ) = X ^ (2 * e) := by
  rw [map_pow, E2_X, ← pow_mul]

/-- `q^{N²}·E2(rectTerm N j)` is exactly the assembled `szc`-product summand
`q^{(N+j)²}/(q²;q²)_{N+j} · q^{j²}/(q²;q²)_j`, via `(N+j)²+j² = N²+2(j²+Nj)`. -/
lemma E2_rectTerm (N j : ℕ) :
    X ^ (N ^ 2) * E2 (rectTerm N j)
      = X ^ ((N + j) ^ 2) * Ring.inverse (E2 (qfac (N + j))) *
          (X ^ (j ^ 2) * Ring.inverse (E2 (qfac j))) := by
  rw [rectTerm, map_mul, map_mul, E2_X_pow, E2_inverse_qfac, E2_inverse_qfac]; ring

/-! ### Assembling the z-Cauchy product (z-degree `N ≥ 0`)

The diagonal `k - j = N` collapses (`k = N + j`); extending the `j`-range to a common bound and
swapping sums identifies the `z^N` coefficient with `coeff m (q^{N²}·E2(rectInf N))` summand-by-summand.
The single open obstruction `(q²;q²)_∞` will be discharged later by `durfee_rect_base_Q`. -/

lemma szc_zero (p k : ℕ) (h : p < k ^ 2) : szc p k = 0 := by
  rw [szc]; exact MockTheta5.mt_coeff_Xpow_mul_zero _ _ _ h

/-- collapse the `k`-sum against the diagonal indicator `k - j = N` (so `k = N + j`). -/
lemma kcollapse (p N j : ℕ) (c : ℤ) :
    ∑ k ∈ Finset.range (p + 1), (if (k : ℤ) - (j : ℤ) = (N : ℤ) then szc p k * c else 0)
      = szc p (N + j) * c := by
  rw [Finset.sum_eq_single (N + j)]
  · rw [if_pos (by push_cast; ring)]
  · intro k _ hk; rw [if_neg (by omega)]
  · intro hk
    rw [if_pos (by push_cast; ring),
        szc_zero p (N + j) (by have := Nat.le_self_pow (n := 2) (by norm_num) (N + j)
                               simp only [Finset.mem_range, not_lt] at hk; omega), zero_mul]

/-- `coeff m (q^{N²}·E2(rectInf N))` as a finite sum over the Durfee-rectangle terms (stabilization). -/
lemma coeff_rhs (N m : ℕ) :
    coeff m (X ^ (N ^ 2) * E2 (rectInf N))
      = ∑ j ∈ Finset.range (m + 1), coeff m (X ^ (N ^ 2) * E2 (rectTerm N j)) := by
  have hstab : coeff m (X ^ (N ^ 2) * E2 (rectInf N))
      = coeff m (X ^ (N ^ 2) * E2 (rectPartial N (m + 1))) := by
    have hdvd : (X : PowerSeries ℤ) ^ (m + 1) ∣ (rectInf N - rectPartial N (m + 1)) := by
      rw [PowerSeries.X_pow_dvd_iff]; intro i hi
      rw [map_sub, coeff_rectInf N (show i + 1 ≤ m + 1 by omega), sub_self]
    obtain ⟨g, hg⟩ := hdvd
    have hkey : X ^ (N ^ 2) * E2 (rectInf N) - X ^ (N ^ 2) * E2 (rectPartial N (m + 1))
        = X ^ (N ^ 2 + 2 * (m + 1)) * E2 g := by
      rw [← mul_sub, ← map_sub, hg, map_mul, E2_X_pow, ← mul_assoc, ← pow_add]
    have hz : coeff m (X ^ (N ^ 2) * E2 (rectInf N))
        - coeff m (X ^ (N ^ 2) * E2 (rectPartial N (m + 1))) = 0 := by
      rw [← map_sub, hkey]; exact MockTheta5.mt_coeff_Xpow_mul_zero _ _ m (by omega)
    exact sub_eq_zero.mp hz
  rw [hstab, rectPartial, map_sum, Finset.mul_sum, map_sum]

/-- per-`(p,r)`: the z-Cauchy product coefficient collapses to `Σ_j szc p (N+j) · szc r j`. -/
lemma prodSZ_collapsed (p r N : ℕ) :
    (coeff p SZ * coeff r SZinv) (N : ℤ) = ∑ j ∈ Finset.range (r + 1), szc p (N + j) * szc r j := by
  rw [prodSZ_apply, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => kcollapse p N j (szc r j)

/-- the `E2(rectTerm)` coefficient as a `szc`-product antidiagonal sum (one `coeff_mul`, defeq fold). -/
lemma coeff_rhs_szc (N m j : ℕ) :
    coeff m (X ^ (N ^ 2) * E2 (rectTerm N j))
      = ∑ pr ∈ Finset.antidiagonal m, szc pr.1 (N + j) * szc pr.2 j := by
  rw [E2_rectTerm, PowerSeries.coeff_mul]
  rfl

/-- **the z-Cauchy product** `SZ · SZinv` at z-degree `N ≥ 0` equals `q^{N²}·E2(rectInf N)` — the
diagonal Durfee-rectangle sum. With `durfee_rect_base_Q` this is `q^{N²}/(q²;q²)_∞`. -/
lemma zProj_SZ_SZinv (N : ℕ) : zProj (N : ℤ) (SZ * SZinv) = X ^ (N ^ 2) * E2 (rectInf N) := by
  ext m
  rw [coeff_zProj, PowerSeries.coeff_mul, laurentSum_apply, coeff_rhs]
  simp_rw [prodSZ_collapsed, coeff_rhs_szc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun pr hpr => ?_
  rw [Finset.mem_antidiagonal] at hpr
  refine Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at *; omega)
    (fun j _ hj => ?_)
  simp only [Finset.mem_range, not_lt] at hj
  rw [szc_zero pr.2 j (by nlinarith [Nat.le_self_pow (n := 2) (by norm_num : 2 ≠ 0) j]), mul_zero]

/-! ### The `z ↦ z⁻¹` symmetry — the z-Cauchy product at negative z-degree

`SZ` and `SZinv` are exchanged by the Laurent involution `invert` (`z ↦ z⁻¹`), so `SZ · SZinv` is
`invert`-invariant and `zProj (-M) (SZ·SZinv) = zProj M (SZ·SZinv)`. This delivers the `N ≤ 0` case from
`zProj_SZ_SZinv` without redoing the assembly. -/

/-- the `z ↦ z⁻¹` involution as a `RingHom` (for use in `PowerSeries.map`). -/
noncomputable def invertHom : LaurentPolynomial ℤ →+* LaurentPolynomial ℤ :=
  (LaurentPolynomial.invert (R := ℤ) : LaurentPolynomial ℤ →+* LaurentPolynomial ℤ)

lemma invertHom_apply (g : LaurentPolynomial ℤ) (n : ℤ) : (invertHom g) n = g (-n) :=
  LaurentPolynomial.invert_apply g n

/-- `map invertHom` flips the z-degree of every projection. -/
lemma zProj_map_invert (n : ℤ) (φ : PowerSeries (LaurentPolynomial ℤ)) :
    zProj n (PowerSeries.map invertHom φ) = zProj (-n) φ := by
  ext m; rw [coeff_zProj, PowerSeries.coeff_map, coeff_zProj]; exact invertHom_apply _ _

lemma invert_single (k a : ℤ) : invertHom (Finsupp.single k a) = Finsupp.single (-k) a := by
  ext n
  rw [invertHom_apply, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

/-- `SZ` and `SZinv` are exchanged by `z ↦ z⁻¹`. -/
lemma map_invert_SZ : PowerSeries.map invertHom SZ = SZinv := by
  refine PowerSeries.ext fun m => ?_
  rw [PowerSeries.coeff_map, coeff_SZ (le_refl (m + 1)), coeff_SZinv (le_refl (m + 1)),
      SZfinite, SZinvFinite]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun k _ => by
    rw [coeff_SZterm_single, coeff_SZinvTerm_single, invert_single]

lemma map_invert_SZinv : PowerSeries.map invertHom SZinv = SZ := by
  refine PowerSeries.ext fun m => ?_
  rw [PowerSeries.coeff_map, coeff_SZ (le_refl (m + 1)), coeff_SZinv (le_refl (m + 1)),
      SZfinite, SZinvFinite]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun k _ => by
    rw [coeff_SZterm_single, coeff_SZinvTerm_single, invert_single, neg_neg]

lemma map_invert_SZmul : PowerSeries.map invertHom (SZ * SZinv) = SZ * SZinv := by
  rw [map_mul, map_invert_SZ, map_invert_SZinv, mul_comm]

/-- **the z-Cauchy product at z-degree `-M ≤ 0`** — same Durfee-rectangle sum, by `z ↦ z⁻¹` symmetry. -/
lemma zProj_SZ_SZinv_neg (M : ℕ) :
    zProj (-(M : ℤ)) (SZ * SZinv) = X ^ (M ^ 2) * E2 (rectInf M) := by
  rw [← map_invert_SZmul, zProj_map_invert, neg_neg, zProj_SZ_SZinv]

end MockTheta5.JTP
