/-
# The Rogers–Ramanujan continued fraction

  `1/(1 + q/(1 + q²/(1 + q³/(1 + ⋯)))) = (q;q⁵)_∞ (q⁴;q⁵)_∞ / ((q²;q⁵)_∞ (q³;q⁵)_∞)`

(Rogers 1894, Ramanujan's first letter to Hardy), as a statement about convergents: the depth-`N` convergent
agrees with the product up to `q^N`.

With `G_m = Σ_n q^{n²+mn}/(q;q)_n`, we have `G_m = G_{m+1} + q^{m+1} G_{m+2}`, so `ρ_m = G_{m+1}/G_m` satisfies
`ρ_m = 1/(1 + q^{m+1} ρ_{m+1})`. The convergents approximate `ρ_m` to one more power of `q` at each depth.
Finally `G₀`, `G₁` are the two Rogers–Ramanujan sums (`rogers_ramanujan_1/2`).
-/
import RamanujanTau.RogersRamanujan

set_option autoImplicit false

namespace MockTheta5.JTP.RR
open PowerSeries Finset MockTheta5.Bailey
open RankProof (Pinf)

/-- the truncation `Σ_{n<N} q^{n²+mn}/(q;q)_n`. -/
noncomputable def Gtr (m N : ℕ) : PowerSeries ℤ := ∑ n ∈ range N, X ^ (n ^ 2 + m * n) * Ring.inverse (qfac n)

/-- `G_m = Σ_n q^{n²+mn}/(q;q)_n`. -/
noncomputable def Gs (m : ℕ) : PowerSeries ℤ := mk fun j => coeff j (Gtr m (j + 1))

lemma Gtr_dvd (m : ℕ) {N M : ℕ} (h : N ≤ M) : (X : PowerSeries ℤ) ^ N ∣ Gtr m M - Gtr m N := by
  rw [Gtr, Gtr, show M = N + (M - N) by omega, sum_range_add, add_sub_cancel_left]
  exact dvd_sum fun i _ => dvd_mul_of_dvd_left (pow_dvd_pow X (by nlinarith)) _

lemma Gs_dvd (m N : ℕ) : (X : PowerSeries ℤ) ^ N ∣ Gs m - Gtr m N := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro k hk
  rw [map_sub, Gs, coeff_mk, sub_eq_zero]
  rcases Nat.le_total (k + 1) N with h | h
  · exact (coeff_eq_of_dvd (Gtr_dvd m h) (by omega)).symm
  · exact coeff_eq_of_dvd (Gtr_dvd m h) (by omega)

lemma Gs_zero : Gs 0 = tsumQsq fun n => Ring.inverse (qfac n) := by
  ext j; rw [Gs, coeff_mk, tsumQsq, coeff_mk, Gtr]; simp

lemma Gs_one : Gs 1 = tsumQsqQ fun n => Ring.inverse (qfac n) := by
  ext j; rw [Gs, coeff_mk, tsumQsqQ, coeff_mk, Gtr]; simp

lemma inv_qfac_step (n : ℕ) : (1 - X ^ (n + 1)) * Ring.inverse (qfac (n + 1)) = Ring.inverse (qfac n) := by
  symm; apply inverse_eq_of_mul
  rw [show qfac n * ((1 - X ^ (n + 1)) * Ring.inverse (qfac (n + 1))) = qfac (n + 1) * Ring.inverse (qfac (n + 1)) by
    rw [qfac, qfac, prod_range_succ]; ring, Ring.mul_inverse_cancel _ (isUnit_qfac _)]

lemma Gtr_func (m N : ℕ) : Gtr m (N + 1) = Gtr (m + 1) (N + 1) + X ^ (m + 1) * Gtr (m + 2) N := by
  have h : Gtr m (N + 1) - Gtr (m + 1) (N + 1) = X ^ (m + 1) * Gtr (m + 2) N := by
    simp only [Gtr]
    rw [← sum_sub_distrib, sum_range_succ', mul_sum]
    simp only [pow_two, mul_zero, add_zero, sub_self]
    refine sum_congr rfl fun i _ => ?_
    rw [← inv_qfac_step i,
      show (i + 1) * (i + 1) + (m + 1) * (i + 1) = (m + 1) + (i * i + (m + 2) * i) + (i + 1) by ring,
      show (i + 1) * (i + 1) + m * (i + 1) = (m + 1) + (i * i + (m + 2) * i) by ring, pow_add, pow_add]
    ring
  linear_combination h

/-- **the functional equation** `G_m = G_{m+1} + q^{m+1} G_{m+2}`. -/
theorem Gs_func (m : ℕ) : Gs m = Gs (m + 1) + X ^ (m + 1) * Gs (m + 2) := by
  refine eq_of_dvd_all fun N => ?_
  have h1 := Gs_dvd m (N + 1)
  have h2 := Gs_dvd (m + 1) (N + 1)
  have h3 := dvd_mul_of_dvd_right (Gs_dvd (m + 2) N) (X ^ (m + 1))
  rw [Gtr_func] at h1
  have h4 : (X : PowerSeries ℤ) ^ (N + 1) ∣ X ^ (m + 1) * (Gs (m + 2) - Gtr (m + 2) N) :=
    (pow_dvd_pow X (by omega : N + 1 ≤ m + 1 + N)).trans (by rw [pow_add]; exact mul_dvd_mul_left _ (Gs_dvd (m + 2) N))
  have := dvd_sub (dvd_sub h1 h2) h4
  rw [show Gs m - (Gtr (m + 1) (N + 1) + X ^ (m + 1) * Gtr (m + 2) N) - (Gs (m + 1) - Gtr (m + 1) (N + 1))
      - X ^ (m + 1) * (Gs (m + 2) - Gtr (m + 2) N) = Gs m - (Gs (m + 1) + X ^ (m + 1) * Gs (m + 2)) by ring] at this
  exact this

lemma isUnit_Gs (m : ℕ) : IsUnit (Gs m) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, Gs, coeff_mk, Gtr]
  simp [qfac]


/-- `ρ_m = G_{m+1}/G_m`. -/
noncomputable def rho (m : ℕ) : PowerSeries ℤ := Gs (m + 1) * Ring.inverse (Gs m)

lemma rho_rec (m : ℕ) : rho m * (1 + X ^ (m + 1) * rho (m + 1)) = 1 := by
  have h1 := Ring.mul_inverse_cancel _ (isUnit_Gs (m + 1))
  have h0 := Ring.mul_inverse_cancel _ (isUnit_Gs m)
  have hf := Gs_func m
  rw [rho, rho]
  linear_combination (-Ring.inverse (Gs m)) * hf + (X ^ (m + 1) * Gs (m + 2) * Ring.inverse (Gs m)) * h1 + h0

/-- the convergents: `cf 0 m = 1`, `cf (d+1) m = 1/(1 + q^{m+1} cf d (m+1))`. So `cf N 0` is
`1/(1 + q/(1 + q²/(⋯/(1 + q^N))))`. -/
noncomputable def cf : ℕ → ℕ → PowerSeries ℤ
  | 0, _ => 1
  | d + 1, m => Ring.inverse (1 + X ^ (m + 1) * cf d (m + 1))

lemma isUnit_one_add_X {m : ℕ} (f : PowerSeries ℤ) : IsUnit (1 + X ^ (m + 1) * f) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]; simp

lemma rho_eq (m : ℕ) : rho m = Ring.inverse (1 + X ^ (m + 1) * rho (m + 1)) :=
  (inverse_eq_of_mul (by rw [mul_comm]; exact rho_rec m)).symm

lemma rho_sub_cf (d : ℕ) : ∀ m, (X : PowerSeries ℤ) ^ (d + 1) ∣ rho m - cf d m := by
  induction d with
  | zero =>
    intro m
    have h := rho_rec m
    rw [cf, show rho m - 1 = -(rho m * X ^ (m + 1) * rho (m + 1)) by linear_combination h]
    exact dvd_neg.mpr (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (pow_dvd_pow X (by omega)) _) _)
  | succ d ih =>
    intro m
    rw [cf, rho_eq m]
    set A := 1 + X ^ (m + 1) * rho (m + 1)
    set B := 1 + X ^ (m + 1) * cf d (m + 1)
    have hA := Ring.mul_inverse_cancel A (isUnit_one_add_X _)
    have hB := Ring.mul_inverse_cancel B (isUnit_one_add_X _)
    rw [show Ring.inverse A - Ring.inverse B
        = X ^ (m + 1) * (cf d (m + 1) - rho (m + 1)) * Ring.inverse A * Ring.inverse B by
      linear_combination (-Ring.inverse A) * hB + Ring.inverse B * hA]
    rw [pow_succ']
    obtain ⟨c, hc⟩ := ih (m + 1)
    rw [show cf d (m + 1) - rho (m + 1) = -(rho (m + 1) - cf d (m + 1)) by ring, hc]
    exact ⟨-(X ^ m * c * Ring.inverse A * Ring.inverse B), by ring⟩

/-- **The Rogers–Ramanujan continued fraction**: the depth-`N` convergent
`1/(1 + q/(1 + q²/(⋯/(1 + q^N))))` agrees with `(q;q⁵)_∞(q⁴;q⁵)_∞/((q²;q⁵)_∞(q³;q⁵)_∞)` through `q^N`. -/
theorem rogers_ramanujan_cf (N : ℕ) :
    (X : PowerSeries ℤ) ^ (N + 1) ∣ cf N 0 - Pinf 1 5 * Pinf 4 5 * Ring.inverse (Pinf 2 5 * Pinf 3 5) := by
  have h := rho_sub_cf N 0
  rw [rho, Gs_zero, Gs_one, rogers_ramanujan_1, rogers_ramanujan_2] at h
  have hu : IsUnit (Pinf 1 5 * Pinf 4 5) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, map_mul, ← coeff_zero_eq_constantCoeff_apply,
      ← coeff_zero_eq_constantCoeff_apply,
      coeff_eq_of_dvd (RankProof.X_pow_dvd_Pinf_sub 1 5 le_rfl (by norm_num) 0) Nat.zero_lt_one,
      coeff_eq_of_dvd (RankProof.X_pow_dvd_Pinf_sub 4 5 (by norm_num) (by norm_num) 0) Nat.zero_lt_one]
    simp [RankProof.Pfin]
  rw [show Ring.inverse (Ring.inverse (Pinf 1 5 * Pinf 4 5)) = Pinf 1 5 * Pinf 4 5 from
    inverse_eq_of_mul (Ring.inverse_mul_cancel _ hu)] at h
  rw [← dvd_neg, neg_sub]
  convert h using 2
  ring

/-- the continued fraction as a power series: its coefficients are those of any deep enough convergent. -/
theorem coeff_cf_stable {k N : ℕ} (h : k ≤ N) :
    coeff k (cf N 0) = coeff k (Pinf 1 5 * Pinf 4 5 * Ring.inverse (Pinf 2 5 * Pinf 3 5)) :=
  coeff_eq_of_dvd (rogers_ramanujan_cf N) (by omega)

end MockTheta5.JTP.RR
