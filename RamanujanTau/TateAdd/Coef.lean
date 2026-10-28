/-
# Leading coefficients of the kernel points (non-vanishing, symmetry, distinctness)

* `⟨s⟩` (`u = s^k`, `q = s^p`): with `m = min(k, p−k)`, `θ^e x(s^k) = s^k(1+…) + (−1)^e s^{p−k}(1+…)`
  (`e = 0, 1`): `coeff_tB_lt`, `coeff_tB_k`, `coeff_tB_pk`.
* `μ_p`: the constant terms `cK 0`, `cK 1` of `x(ζ^k)`, `θx(ζ^k)`.
-/
import RamanujanTau.TateAdd.Spec

set_option autoImplicit false

noncomputable section

namespace TateAdd

open PowerSeries TateQuot Finset

local notation "aX" => (Polynomial.X : P)

variable {K : Type*} [Field K] [CharZero K] {p : ℕ} [hp : Fact p.Prime]

/-! ### `⟨s⟩` -/

lemma φk_sub_pow (k e : ℕ) : φk K k ((aX - 1) ^ e) = Us K k ^ e := by
  simp [φk, Us]

lemma tB_split {e k : ℕ} (hk1 : 1 ≤ k) :
    tB K p e k = φk K k (cpoly e) * (Us K k ^ (e + 2))⁻¹ + evB K k (p - k) (mk (Rm e)) := by
  rw [tB, zB, map_add, map_mul, evB_C, evB_C, φk_sub_pow, add_mul, mul_comm (Us K k ^ (e + 2)),
    mul_assoc, PowerSeries.mul_inv_cancel _ (cc_Us_pow hk1 _), mul_one]

lemma Rm_zero (e : ℕ) : Rm e 0 = 0 := by simp [Rm]

lemma coeff_evB_Rm_lt (e : ℕ) {k : ℕ} (hk : k < p) {j : ℕ} (hj : j < p - k) :
    coeff j (evB K k (p - k) (mk (Rm e))) = 0 := by
  rw [coeff_evB k (p - k) (by omega)]
  refine sum_eq_zero fun N hN => ?_
  rw [coeff_mk, coeff_mul_X_pow']
  rcases N with _ | N
  · simp [Rm_zero]
  · rw [if_neg]; nlinarith

lemma coeff_evB_Rm_eq (e : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < p) :
    coeff (p - k) (evB K k (p - k) (mk (Rm e))) = (-1) ^ e := by
  rw [coeff_evB k (p - k) (by omega), sum_eq_single 1]
  · rw [coeff_mk, mul_one, coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self]
    simp only [Rm, Nat.divisors_one, sum_singleton, Nat.cast_one, one_pow, one_mul]
    simp only [map_sub, map_add, map_mul, map_pow, φk_aX, coeff_zero_eq_constantCoeff]
    simp only [map_sub, map_add, map_mul, map_pow, constantCoeff_X]
    rw [zero_pow (by omega), zero_pow (by omega)]
    split_ifs <;> simp [φk]
  · intro N _ hN
    rw [coeff_mk, coeff_mul_X_pow']
    rcases N with _ | N
    · simp [Rm_zero]
    · rw [if_neg]; rcases N with _ | N
      · exact absurd rfl hN
      · have : 1 ≤ p - k := by omega
        nlinarith
  · intro h; simp at h; omega

lemma cc_Us {k : ℕ} (hk1 : 1 ≤ k) : constantCoeff (Us K k) = -1 := by
  simp [Us, zero_pow (by omega : k ≠ 0)]

/-- `φk(cpoly e) = X^k g_e` with `g_e(0) (Us(0))^{-(e+2)} = 1`. -/
lemma term1 {e k : ℕ} (he : e ≤ 1) (hk1 : 1 ≤ k) :
    ∃ g : PowerSeries K, φk K k (cpoly e) * (Us K k ^ (e + 2))⁻¹ = X ^ k * g ∧
      constantCoeff g = 1 := by
  interval_cases e
  · refine ⟨(Us K k ^ 2)⁻¹, by simp [cpoly, φk_aX], ?_⟩
    rw [constantCoeff_inv, map_pow, cc_Us hk1]; norm_num
  · refine ⟨-(1 + X ^ k) * (Us K k ^ 3)⁻¹, by simp [cpoly, φk_aX]; ring, ?_⟩
    rw [map_mul, constantCoeff_inv, map_pow, cc_Us hk1]
    simp [zero_pow (by omega : k ≠ 0)]; norm_num

lemma coeff_tB_lt {e k j : ℕ} (he : e ≤ 1) (hk1 : 1 ≤ k) (hk : k < p) (hj1 : j < k)
    (hj2 : j < p - k) : coeff j (tB K p e k) = 0 := by
  obtain ⟨g, hg, -⟩ := term1 (K := K) he hk1
  rw [tB_split hk1, map_add, hg, coeff_X_pow_mul', if_neg (by omega), coeff_evB_Rm_lt e hk hj2,
    add_zero]

lemma coeff_tB_k {e k : ℕ} (he : e ≤ 1) (hk1 : 1 ≤ k) (hk : k < p - k) :
    coeff k (tB K p e k) = 1 := by
  obtain ⟨g, hg, hg0⟩ := term1 (K := K) he hk1
  rw [tB_split hk1, map_add, hg, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    coeff_zero_eq_constantCoeff, hg0, coeff_evB_Rm_lt e (by omega) hk, add_zero]

lemma coeff_tB_pk {e k : ℕ} (he : e ≤ 1) (hk1 : 1 ≤ k) (hkp : k < p) (hk : p - k < k) :
    coeff (p - k) (tB K p e k) = (-1) ^ e := by
  obtain ⟨g, hg, -⟩ := term1 (K := K) he hk1
  rw [tB_split hk1, map_add, hg, coeff_X_pow_mul', if_neg (by omega),
    coeff_evB_Rm_eq e hk1 hkp, zero_add]

end TateAdd
