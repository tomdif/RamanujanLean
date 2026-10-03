/-
# The spt identity, step 2: `R(z)·(zq)_∞(q/z)_∞ = (q)_∞ · Σ_j (z)_j(z⁻¹)_j q^j/(q)_j` in `ℂ⟦q⟧`

From the finite identity `SF_eq_TS` (transferred to `ℂ⟦X⟧` through its fraction field) by coefficient
stabilization, and the Appell–Lerch form `rank_AL`.
-/
import RamanujanTau.SptT

set_option autoImplicit false

namespace RankProof
open PowerSeries Finset MockTheta5.Bailey MockTheta5.JTP CrankProof
local notation "ψ" => MockTheta5.JTP.ψC

/-- `t_j = (z)_j(z⁻¹)_j q^j/(q)_j`. -/
noncomputable def tser (z : ℂ) (j : ℕ) : PowerSeries ℂ :=
  poch z 0 j * poch z⁻¹ 0 j * X ^ j * ψ (Ring.inverse (qfac j))

lemma φC_zp (z : ℂ) (j : ℕ) : φC (poch z 0 j) = zp (φC X) (φC (C z)) j := by
  rw [poch, map_prod, zp]
  refine prod_congr rfl fun i _ => ?_
  simp [map_sub, map_mul, map_pow]

lemma φC_zp' {z : ℂ} (j : ℕ) : φC (poch z⁻¹ 0 j) = zp (φC X) (φC (C z))⁻¹ j := by
  rw [poch, map_prod, zp]
  refine prod_congr rfl fun i _ => ?_
  simp [map_sub, map_mul, map_pow, φC_Cinv]

/-- **the finite identity in `ℂ⟦X⟧`**. -/
theorem SF_series {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    ∑ r ∈ range (n + 1), X ^ (r ^ 2) * αser z r * (poch z 1 n * poch z⁻¹ 1 n)
        * ψ (Ring.inverse (qfac (n - r))) * ψ (Ring.inverse (qfac (n + r)))
      = ∑ j ∈ range (n + 1), tser z j := by
  apply φC_inj
  have h := SF_eq_TS hqC (hwC hz) (hwqC z) (hwqC' hz) n
  have hψ : ∀ m, φC (ψ (Ring.inverse (qfac m))) = (P (φC X) m)⁻¹ := fun m => by
    rw [map_inverse ψ (isUnit_qfac m), φC_inverse ((isUnit_qfac m).map ψ), φC_qfac]
  unfold SF TS at h
  rw [map_sum, map_sum]
  have e1 : ∀ r ∈ range (n + 1), φC (X ^ (r ^ 2) * αser z r * (poch z 1 n * poch z⁻¹ 1 n)
      * ψ (Ring.inverse (qfac (n - r))) * ψ (Ring.inverse (qfac (n + r)))) = Fs (φC X) (φC (C z)) n r := by
    intro r _
    rw [map_mul, map_mul, map_mul, map_mul, map_pow, hψ, hψ, φC_αser, map_mul, φC_poch, Fs, Fr]
    have h1 := P_ne hqC (n - r)
    have h2 := P_ne hqC (n + r)
    field_simp
  have e2 : ∀ j ∈ range (n + 1), φC (tser z j) = tz (φC X) (φC (C z)) j := by
    intro j _
    rw [tser, map_mul, map_mul, map_mul, map_pow, hψ, φC_zp, φC_zp', tz, div_eq_mul_inv]
  rw [sum_congr rfl e1, sum_congr rfl e2, h]

/-- `Σ_j (z)_j(z⁻¹)_j q^j/(q)_j`, coefficientwise. -/
noncomputable def Tser (z : ℂ) : PowerSeries ℂ := mk fun c => coeff c (∑ j ∈ range (c + 1), tser z j)

lemma coeff_Tser (z : ℂ) {c N : ℕ} (h : c ≤ N) :
    coeff c (Tser z) = coeff c (∑ j ∈ range (N + 1), tser z j) := by
  rw [Tser, coeff_mk, map_sum, map_sum]
  refine sum_subset (range_subset_range.mpr (by omega)) fun j _ hj => ?_
  simp only [mem_range, not_lt] at hj
  rw [tser, show poch z 0 j * poch z⁻¹ 0 j * X ^ j * ψ (Ring.inverse (qfac j))
    = X ^ j * (poch z 0 j * poch z⁻¹ 0 j * ψ (Ring.inverse (qfac j))) by ring]
  exact coeffC_Xpow_zero (by omega) _

/-- the limit of the finite identity: `Σ_r q^{r²}α_r · (zq)_∞(q/z)_∞/(q)_∞² = Σ_j t_j`. -/
theorem ALser_limit {z : ℂ} (hz : z ≠ 0) :
    ALser z * ((pochInf z 1 * pochInf z⁻¹ 1) * ψ (Ring.inverse qfacInf) * ψ (Ring.inverse qfacInf)) = Tser z := by
  ext c
  set N := 2 * c + 1 with hN
  set Y := (pochInf z 1 * pochInf z⁻¹ 1) * ψ (Ring.inverse qfacInf) * ψ (Ring.inverse qfacInf)
  rw [coeff_Tser z (show c ≤ N by omega), ← SF_series hz N, mul_comm, coeffC_congr (ALser_dvd z c), mul_sum,
    map_sum, map_sum]
  rw [← sum_subset (range_subset_range.mpr (show c + 1 ≤ N + 1 by omega)) ?_]
  · refine sum_congr rfl fun r hr => ?_
    have hr' := mem_range.mp hr
    have hY : (X : PowerSeries ℂ) ^ (c + 1) ∣ Y - (poch z 1 N * poch z⁻¹ 1 N) * ψ (Ring.inverse (qfac (N - r)))
        * ψ (Ring.inverse (qfac (N + r))) := by
      have hW : (X : PowerSeries ℂ) ^ (c + 1) ∣ pochInf z 1 * pochInf z⁻¹ 1 - poch z 1 N * poch z⁻¹ 1 N := by
        have a1 := (pow_dvd_pow X (show c + 1 ≤ N by omega)).trans (X_pow_dvd_pochInf_sub z le_rfl N)
        have a2 := (pow_dvd_pow X (show c + 1 ≤ N by omega)).trans (X_pow_dvd_pochInf_sub z⁻¹ le_rfl N)
        rw [show pochInf z 1 * pochInf z⁻¹ 1 - poch z 1 N * poch z⁻¹ 1 N
          = (pochInf z 1 - poch z 1 N) * pochInf z⁻¹ 1 + poch z 1 N * (pochInf z⁻¹ 1 - poch z⁻¹ 1 N) by ring]
        exact dvd_add (dvd_mul_of_dvd_left a1 _) (dvd_mul_of_dvd_right a2 _)
      have hi1 := ψ_dvd (inv_qfac_dvd (k := c) (N := N - r) (by omega))
      have hi2 := ψ_dvd (inv_qfac_dvd (k := c) (N := N + r) (by omega))
      rw [map_sub] at hi1 hi2
      rw [show Y - (poch z 1 N * poch z⁻¹ 1 N) * ψ (Ring.inverse (qfac (N - r))) * ψ (Ring.inverse (qfac (N + r)))
        = (pochInf z 1 * pochInf z⁻¹ 1 - poch z 1 N * poch z⁻¹ 1 N) * ψ (Ring.inverse qfacInf)
            * ψ (Ring.inverse qfacInf)
          - (poch z 1 N * poch z⁻¹ 1 N) * (ψ (Ring.inverse (qfac (N - r))) - ψ (Ring.inverse qfacInf))
            * ψ (Ring.inverse qfacInf)
          - (poch z 1 N * poch z⁻¹ 1 N) * ψ (Ring.inverse (qfac (N - r)))
            * (ψ (Ring.inverse (qfac (N + r))) - ψ (Ring.inverse qfacInf)) by simp only [Y]; ring]
      exact dvd_sub (dvd_sub (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hW _) _)
        (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hi1 _) _)) (dvd_mul_of_dvd_right hi2 _)
    rw [show X ^ (r ^ 2) * αser z r * (poch z 1 N * poch z⁻¹ 1 N) * ψ (Ring.inverse (qfac (N - r)))
        * ψ (Ring.inverse (qfac (N + r)))
      = (X ^ (r ^ 2) * αser z r) * ((poch z 1 N * poch z⁻¹ 1 N) * ψ (Ring.inverse (qfac (N - r)))
        * ψ (Ring.inverse (qfac (N + r)))) by ring, mul_comm Y]
    exact coeffC_congr hY
  · intro r _ hr
    simp only [mem_range, not_lt] at hr
    rw [show X ^ (r ^ 2) * αser z r * (poch z 1 N * poch z⁻¹ 1 N) * ψ (Ring.inverse (qfac (N - r)))
        * ψ (Ring.inverse (qfac (N + r)))
      = X ^ (r ^ 2) * (αser z r * (poch z 1 N * poch z⁻¹ 1 N) * ψ (Ring.inverse (qfac (N - r)))
        * ψ (Ring.inverse (qfac (N + r)))) by ring]
    exact coeffC_Xpow_zero (by nlinarith) _

/-- **`R(z;q)·(zq)_∞(q/z)_∞ = (q)_∞ · Σ_j (z)_j(z⁻¹)_j q^j/(q)_j`.** -/
theorem rank_crank_T {z : ℂ} (hz : z ≠ 0) :
    Dser z z⁻¹ * (pochInf z 1 * pochInf z⁻¹ 1) = pochInf 1 1 * Tser z := by
  rw [rank_AL hz, ← ALser_limit hz, pochInf_one_eq]
  have hu : ψ qfacInf * ψ (Ring.inverse qfacInf) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel _ isUnit_qfacInf, map_one]
  linear_combination -(ALser z * (pochInf z 1 * pochInf z⁻¹ 1) * ψ (Ring.inverse qfacInf)) * hu

/-- `u_j = (zq)_{j−1}(q/z)_{j−1} q^j/(q)_j` (`j ≥ 1`), `u_0 = 0`. -/
noncomputable def user (z : ℂ) (j : ℕ) : PowerSeries ℂ :=
  if j = 0 then 0 else poch z 1 (j - 1) * poch z⁻¹ 1 (j - 1) * X ^ j * ψ (Ring.inverse (qfac j))

/-- `U(z) = Σ_{j≥1} (zq)_{j−1}(q/z)_{j−1} q^j/(q)_j`. -/
noncomputable def User (z : ℂ) : PowerSeries ℂ := mk fun c => coeff c (∑ j ∈ range (c + 1), user z j)

lemma poch_zero_split (c : ℂ) (j : ℕ) : poch c 0 (j + 1) = (1 - C c) * poch c 1 j := by
  rw [poch, prod_range_succ', poch]
  simp only [zero_add, pow_zero, mul_one]
  rw [mul_comm]; congr 1
  exact prod_congr rfl fun i _ => by rw [add_comm]

lemma tser_eq (z : ℂ) (j : ℕ) :
    tser z j = (if j = 0 then 1 else 0) + C ((1 - z) * (1 - z⁻¹)) * user z j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [tser, user, poch_zero, qfac]
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [tser, user, if_neg (by omega), if_neg (by omega), poch_zero_split, poch_zero_split,
      show i + 1 - 1 = i by omega, map_mul, map_sub, map_sub, map_one]
    ring

/-- `T(z) = 1 + (1−z)(1−z⁻¹)·U(z)`. -/
lemma Tser_eq (z : ℂ) : Tser z = 1 + C ((1 - z) * (1 - z⁻¹)) * User z := by
  ext c
  rw [Tser, coeff_mk, map_add, coeff_C_mul, User, coeff_mk, ← coeff_C_mul, ← map_add]
  congr 1
  rw [sum_congr rfl fun j _ => tser_eq z j, sum_add_distrib, ← mul_sum, sum_ite_eq' (range (c + 1)) 0]
  simp

/-- the crank generating function `C(z) = (q)_∞/((zq)_∞(q/z)_∞)`. -/
noncomputable def Cgf (z : ℂ) : PowerSeries ℂ := pochInf 1 1 * Ring.inverse (pochInf z 1 * pochInf z⁻¹ 1)

/-- **`R(z) − C(z) = (1−z)(1−z⁻¹)·C(z)·U(z)`** (the spt-crank identity). -/
theorem rank_sub_crank {z : ℂ} (hz : z ≠ 0) :
    Dser z z⁻¹ - Cgf z = C ((1 - z) * (1 - z⁻¹)) * (Cgf z * User z) := by
  have hu : IsUnit (pochInf z 1 * pochInf z⁻¹ 1) := (isUnit_pochInf z le_rfl).mul (isUnit_pochInf z⁻¹ le_rfl)
  have h := rank_crank_T hz
  have hD : Dser z z⁻¹ = Cgf z * Tser z := by
    rw [Cgf, mul_comm (pochInf 1 1), mul_assoc, ← h, mul_comm (Dser z z⁻¹), ← mul_assoc,
      Ring.inverse_mul_cancel _ hu, one_mul]
  rw [hD, Tser_eq]; ring

end RankProof
