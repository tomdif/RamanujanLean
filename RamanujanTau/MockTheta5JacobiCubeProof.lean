/-
# Jacobi's cube identity, rung-3 proof — stone 4: differentiate the triangular JTP at `z = −1`

Applying `d/dz|_{z=−1}` to `bilateral_triangular_JTP`:
  * series side  `Σ_{n∈ℤ} zⁿ q^{n(n−1)/2}`  →  `Σ_n n(−1)^{n−1} q^{n(n−1)/2} = Σ_m (−1)ᵐ(2m+1)q^{m(m+1)/2}`
    (pairing `n = m+1, −m`), i.e. `jacobiCubeSum`;
  * product side  `(1+z)·G`  →  `G|_{z=−1}` (the `(1+z)` factor vanishes), `= (q;q)_∞³`.

The functional is `L f = mk (n ↦ D₁(coeff n f))` with `D₁` the linear "derivative at `−1`" on the
`LaurentPolynomial` coefficients (`D₁(zᵏ) = k(−1)^{k−1} = wt k`). This file builds `L`, `D₁`, and the **series
side** `L_triTheta : L triTheta = jacobiCubeSum`. No `sorry`.
-/
import RamanujanTau.MockTheta5TriangularBilateral
import RamanujanTau.MockTheta5JacobiCube
import RamanujanTau.MockTheta5AltTheta

namespace MockTheta5.JTP
open PowerSeries LaurentPolynomial

/-- `sgn k = (−1)ᵏ`. -/
def sgn (κ : ℤ) : ℤ := if Even κ then 1 else -1
/-- derivative-at-`(−1)` weight `d/dz(zᵏ)|_{−1} = k(−1)^{k−1} = −k·(−1)ᵏ`. -/
def wt (κ : ℤ) : ℤ := -κ * sgn κ

lemma sgn_neg (κ : ℤ) : sgn (-κ) = sgn κ := by simp only [sgn, even_neg]
lemma sgn_succ (κ : ℤ) : sgn (κ + 1) = -sgn κ := by
  unfold sgn
  by_cases h : Even κ <;> simp [h, Int.even_add_one]
lemma sgn_natCast (m : ℕ) : sgn (m : ℤ) = (-1 : ℤ) ^ m := by
  simp only [sgn, Int.even_coe_nat]
  by_cases h : Even m
  · rw [if_pos h]; exact (h.neg_one_pow).symm
  · rw [if_neg h]; exact ((Nat.not_even_iff_odd.mp h).neg_one_pow).symm

/-- the key pairing `wt(m+1) + wt(−m) = (2m+1)(−1)ᵐ` (the `(2m+1)` weight of Jacobi's cube). -/
lemma wt_theta (m : ℕ) : wt ((m : ℤ) + 1) + wt (-(m : ℤ)) = (2 * (m : ℤ) + 1) * sgn (m : ℤ) := by
  unfold wt; rw [sgn_succ, sgn_neg]; ring

/-- `wt j + wt(j+1) = sgn j` (the identity behind the vanishing rule). -/
lemma wt_add_succ (j : ℤ) : wt j + wt (j + 1) = sgn j := by
  unfold wt; rw [sgn_succ]; ring

/-- the linear derivative-at-`(−1)` functional on `LaurentPolynomial ℤ`. -/
noncomputable def D1 : LaurentPolynomial ℤ →+ ℤ where
  toFun p := p.sum (fun κ c => c * wt κ)
  map_zero' := Finsupp.sum_zero_index
  map_add' p q := Finsupp.sum_add_index' (fun i => zero_mul (wt i)) (fun i a b => add_mul a b (wt i))

lemma D1_T (κ : ℤ) : D1 (T κ) = wt κ := by
  rw [show (T κ : LaurentPolynomial ℤ) = LaurentPolynomial.C (1 : ℤ) * T κ by rw [map_one, one_mul],
      ← LaurentPolynomial.single_eq_C_mul_T]
  simp only [D1, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finsupp.sum_single_index, zero_mul, one_mul]

/-- the derivative-at-`(−1)` functional on power series (coefficient-wise). -/
noncomputable def L (f : PowerSeries (LaurentPolynomial ℤ)) : PowerSeries ℤ := mk fun n => D1 (coeff n f)

@[simp] lemma coeff_L (f : PowerSeries (LaurentPolynomial ℤ)) (n : ℕ) : coeff n (L f) = D1 (coeff n f) := by
  rw [L, coeff_mk]

lemma L_add (f g : PowerSeries (LaurentPolynomial ℤ)) : L (f + g) = L f + L g := by
  ext n; rw [coeff_L, map_add, map_add, map_add, coeff_L, coeff_L]

/-! ### Series side: `L triTheta = jacobiCubeSum` -/

/-- generic: `coeff n (X^e · C c) = if n = e then c else 0`. -/
lemma coeff_Xpow_mul_C {R : Type*} [CommRing R] (e n : ℕ) (c : R) :
    coeff n (X ^ e * PowerSeries.C c) = if n = e then c else 0 := by
  rw [coeff_X_pow_mul']
  split_ifs with h1 h2 h2
  · rw [h2, Nat.sub_self, coeff_C, if_pos rfl]
  · rw [coeff_C, if_neg (by omega)]
  · omega
  · rfl

/-- the `q^n` coefficient of `triTerm m`: `T(m+1)+T(−m)` at `n = m(m+1)/2`, else `0`. -/
lemma coeff_triTerm_val (m n : ℕ) :
    coeff n (triTerm m) = if n = m * (m + 1) / 2 then T ((m : ℤ) + 1) + T (-(m : ℤ)) else 0 := by
  rw [triTerm, coeff_Xpow_mul_C]

lemma L_triTheta : L triTheta = jacobiCubeSum := by
  ext n
  rw [coeff_L, coeff_triTheta (le_refl (n + 1)), triFinite, map_sum, map_sum,
      coeff_jacobiCubeSum (le_refl (n + 1))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_triTerm_val, coeff_Xpow_mul_C]
  split_ifs with h
  · rw [map_add, D1_T, D1_T, wt_theta, sgn_natCast]; ring
  · rw [map_zero]

/-! ### Product side: the vanishing rule `L((1+z)·G) = map evm1 G` -/

lemma evm1_T_eq_sgn (κ : ℤ) : evm1 (T κ) = sgn κ := by
  rcases le_total 0 κ with h | h
  · lift κ to ℕ using h with k; rw [evm1_T_nat, sgn_natCast]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, κ = -(k : ℤ) := ⟨κ.natAbs, by omega⟩
    rw [evm1_T_negnat, sgn_neg, sgn_natCast]

lemma D1_CT (b κ : ℤ) : D1 (LaurentPolynomial.C b * T κ) = b * wt κ := by
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  simp only [D1, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finsupp.sum_single_index, zero_mul]

lemma evm1_CT (b κ : ℤ) : evm1 (LaurentPolynomial.C b * T κ) = b * sgn κ := by
  rw [map_mul, evm1_C, evm1_T_eq_sgn]

/-- the vanishing identity on a single monomial `C b · T κ`. -/
lemma D1_one_add_T1_CT (b κ : ℤ) :
    D1 ((1 + T 1) * (LaurentPolynomial.C b * T κ)) = evm1 (LaurentPolynomial.C b * T κ) := by
  rw [add_mul, one_mul,
      show (T 1 : LaurentPolynomial ℤ) * (LaurentPolynomial.C b * T κ)
            = LaurentPolynomial.C b * T (κ + 1) from by
        rw [← mul_assoc, mul_comm (T (1 : ℤ)) (LaurentPolynomial.C b), mul_assoc,
            ← LaurentPolynomial.T_add, add_comm (1 : ℤ) κ],
      map_add, D1_CT, D1_CT, evm1_CT, ← mul_add, wt_add_succ]

lemma D1_one_add_T1_mul (c : LaurentPolynomial ℤ) : D1 ((1 + T 1) * c) = evm1 c := by
  have h : D1.comp (AddMonoidHom.mulLeft (1 + T 1 : LaurentPolynomial ℤ))
      = (evm1 : LaurentPolynomial ℤ →+* ℤ).toAddMonoidHom := by
    apply Finsupp.addHom_ext
    intro κ b
    rw [show (Finsupp.single κ b : LaurentPolynomial ℤ) = LaurentPolynomial.C b * T κ from
          LaurentPolynomial.single_eq_C_mul_T b κ]
    exact D1_one_add_T1_CT b κ
  exact DFunLike.congr_fun h c

/-- **the vanishing rule**: `L((1+z)·G) = G|_{z=−1}` (the `(1+z)` factor drops the derivative). -/
lemma L_one_add_z_mul (G : PowerSeries (LaurentPolynomial ℤ)) :
    L ((1 + PowerSeries.C (T 1)) * G) = PowerSeries.map evm1 G := by
  rw [show (1 + PowerSeries.C (T 1) : PowerSeries (LaurentPolynomial ℤ)) = PowerSeries.C (1 + T 1) from by
        rw [map_add, map_one]]
  ext n
  rw [coeff_L, PowerSeries.coeff_C_mul, PowerSeries.coeff_map, D1_one_add_T1_mul]

/-! ### The three `z = −1` evaluations, and the capstone -/

lemma map_evm1_qfacInfL : PowerSeries.map evm1 qfacInfL = qfacInf := by
  ext n
  rw [qfacInfL, PowerSeries.coeff_map, PowerSeries.coeff_map, evm1_C]

lemma evm1_single (κ b : ℤ) : evm1 (Finsupp.single κ b : LaurentPolynomial ℤ) = b * sgn κ := by
  rw [show (Finsupp.single κ b : LaurentPolynomial ℤ) = LaurentPolynomial.C b * T κ from
        LaurentPolynomial.single_eq_C_mul_T b κ]
  exact evm1_CT b κ

/-- `z=−1` evaluation is `z↦z⁻¹`-invariant (`sgn(−κ)=sgn κ`). -/
lemma evm1_invertHom (p : LaurentPolynomial ℤ) : evm1 (invertHom p) = evm1 p := by
  have h : (evm1 : LaurentPolynomial ℤ →+* ℤ).toAddMonoidHom.comp invertHom.toAddMonoidHom
      = (evm1 : LaurentPolynomial ℤ →+* ℤ).toAddMonoidHom := by
    apply Finsupp.addHom_ext
    intro κ b
    show evm1 (invertHom (Finsupp.single κ b)) = evm1 (Finsupp.single κ b)
    rw [invert_single, evm1_single, evm1_single, sgn_neg]
  exact DFunLike.congr_fun h p

lemma map_evm1_map_invert (Y : PowerSeries (LaurentPolynomial ℤ)) :
    PowerSeries.map evm1 (PowerSeries.map invertHom Y) = PowerSeries.map evm1 Y := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map, evm1_invertHom]

/-- `map evm1` of a single factor `1 + z q^{i+1}` is `1 − q^{i+1}`. -/
lemma map_evm1_factor (i : ℕ) :
    PowerSeries.map evm1 (1 + X ^ (i + 1) * PowerSeries.C (T 1)) = 1 - X ^ (i + 1) := by
  rw [map_add, map_one, map_mul, map_pow, PowerSeries.map_X, PowerSeries.map_C, evm1_T_eq_sgn,
      show sgn 1 = -1 from by decide, map_neg, map_one, mul_neg, mul_one]
  ring

lemma map_evm1_triProdQ1 (n : ℕ) : PowerSeries.map evm1 (triProdQ1 n) = MockTheta5.Bailey.qfac n := by
  rw [triProdQ1, MockTheta5.Bailey.qfac, map_prod]
  exact Finset.prod_congr rfl (fun i _ => map_evm1_factor i)

lemma map_evm1_triProdQ1Inf : PowerSeries.map evm1 triProdQ1Inf = qfacInf := by
  ext n
  rw [PowerSeries.coeff_map, coeff_triProdQ1Inf (le_refl (n + 1)), ← PowerSeries.coeff_map,
      map_evm1_triProdQ1]
  simp only [qfacInf, PowerSeries.coeff_mk]

/-- **Jacobi's cube identity** `(q;q)_∞³ = Σ_{m≥0} (−1)ᵐ(2m+1) q^{m(m+1)/2}` (rung-3, fully proven). -/
theorem jacobi_cube_identity : qfacInf ^ 3 = jacobiCubeSum := by
  have key := congrArg L bilateral_triangular_JTP
  rw [L_triTheta, triProdQInf_eq_split,
      show qfacInfL * ((1 + PowerSeries.C (T 1)) * triProdQ1Inf)
            * (PowerSeries.map invertHom triProdQ1Inf)
          = (1 + PowerSeries.C (T 1))
            * (qfacInfL * triProdQ1Inf * (PowerSeries.map invertHom triProdQ1Inf)) from by ring,
      L_one_add_z_mul, map_mul, map_mul, map_evm1_qfacInfL, map_evm1_triProdQ1Inf,
      map_evm1_map_invert, map_evm1_triProdQ1Inf] at key
  rw [← key]; ring

end MockTheta5.JTP
