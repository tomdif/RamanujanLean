/-
# Uniqueness of the root of the homogeneous quintic

`y⁵ = z w³ (34y² + 13wy + (1 + 121z)w²)` with `w = qᵐ·w₁` (`w₁(0) = c ≠ 0`) and `z = q⁵·z₁`
(`z₁(0) = 1`) has at most one solution in `ℤ⟦q⟧`. Every solution is `q^{m+1}·t` with `t(0) = c`, and
the cofactor of `y − y'` in `Q(y) − Q(y')` is `q^{4m+4}·(5c⁴ + O(q))`.

Applied with `w = P'(φ)` (`m = 50`, `c = 11`): Atkin's `g₂` determines `S₂(φ) = P'(φ)·g₂` (`H2_core`).
-/
import RamanujanTau.Atkin11Seed.Trace

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Atkin11Seed
open Atkin11 PowerSeries

lemma X_dvd_of_pow5 {t : PS} (h : constantCoeff (t ^ 5) = 0) : X ∣ t := by
  rw [X_dvd_iff]
  rw [map_pow] at h
  exact pow_eq_zero_iff (by norm_num) |>.mp h

lemma cancelX {k : ℕ} {a b : PS} (h : X ^ k * a = X ^ k * b) : a = b :=
  mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) h

/-- the shape `y = q^{m+1} t`, `t(0) = c` of a root. -/
theorem quintic_shape (m : ℕ) (c : ℤ) (w w1 zz z1 y : PS) (hw : w = X ^ m * w1) (hw1 : constantCoeff w1 = c)
    (hz : zz = X ^ 5 * z1) (hz1 : constantCoeff z1 = 1)
    (hy : y ^ 5 = zz * w ^ 3 * (34 * y ^ 2 + 13 * w * y + (1 + 121 * zz) * w ^ 2)) :
    ∃ t, y = X ^ (m + 1) * t ∧ constantCoeff t = c := by
  subst hw hz
  have hA : ∀ n ≤ m + 1, ∃ t, y = X ^ n * t := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨y, by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨t, rfl⟩ := ih (by omega)
      obtain ⟨d, rfl⟩ : ∃ d, m = n + d := ⟨m - n, by omega⟩
      have h5 : X ^ (5 * n) * t ^ 5 = X ^ (5 * n) * (X ^ (5 + 3 * d) *
          (z1 * w1 ^ 3 * (34 * t ^ 2 + 13 * X ^ d * w1 * t + (1 + 121 * (X ^ 5 * z1)) * X ^ (2 * d) * w1 ^ 2))) := by
        linear_combination hy
      have ht := cancelX h5
      have : X ∣ t := X_dvd_of_pow5 (by
        rw [ht, map_mul, map_pow, constantCoeff_X, zero_pow (by omega), zero_mul])
      obtain ⟨t', rfl⟩ := this
      exact ⟨t', by ring⟩
  obtain ⟨t, rfl⟩ := hA (m + 1) le_rfl
  refine ⟨t, rfl, ?_⟩
  have h5 : X ^ (5 * m + 5) * t ^ 5 = X ^ (5 * m + 5) *
      (z1 * w1 ^ 3 * (34 * X ^ 2 * t ^ 2 + 13 * X * w1 * t + (1 + 121 * (X ^ 5 * z1)) * w1 ^ 2)) := by
    linear_combination hy
  have ht := congrArg constantCoeff (cancelX h5)
  simp only [map_mul, map_pow, map_add, map_ofNat, constantCoeff_X, hw1, hz1, map_one] at ht
  norm_num at ht
  exact (Odd.strictMono_pow (by decide : Odd 5)).injective (show constantCoeff t ^ 5 = c ^ 5 by linear_combination ht)

/-- **uniqueness**. -/
theorem quintic_unique (m : ℕ) (c : ℤ) (hc : c ≠ 0) (w w1 zz z1 y y' : PS) (hw : w = X ^ m * w1)
    (hw1 : constantCoeff w1 = c) (hz : zz = X ^ 5 * z1) (hz1 : constantCoeff z1 = 1)
    (hy : y ^ 5 = zz * w ^ 3 * (34 * y ^ 2 + 13 * w * y + (1 + 121 * zz) * w ^ 2))
    (hy' : y' ^ 5 = zz * w ^ 3 * (34 * y' ^ 2 + 13 * w * y' + (1 + 121 * zz) * w ^ 2)) : y = y' := by
  obtain ⟨t, rfl, ht⟩ := quintic_shape m c w w1 zz z1 _ hw hw1 hz hz1 hy
  obtain ⟨t', rfl, ht'⟩ := quintic_shape m c w w1 zz z1 _ hw hw1 hz hz1 hy'
  subst hw hz
  set B : PS := t ^ 4 + t ^ 3 * t' + t ^ 2 * t' ^ 2 + t * t' ^ 3 + t' ^ 4 - X ^ 2 * z1 * w1 ^ 3 * 34 * (t + t')
    - X * z1 * w1 ^ 4 * 13 with hB
  have key : (X ^ (m + 1) * t - X ^ (m + 1) * t') * (X ^ (4 * m + 4) * B) = 0 := by
    rw [hB]; linear_combination hy - hy'
  have hB0 : B ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    simp only [hB, map_sub, map_add, map_mul, map_pow, map_ofNat, constantCoeff_X, ht, ht', hz1] at this
    norm_num at this
    exact hc (by
      have h5 : (5 : ℤ) * c ^ 4 = 0 := by linear_combination this
      simpa using h5)
  have hne : X ^ (4 * m + 4) * B ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hB0
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hne)

/-! ### the q-adic shape of `P'(φ)` -/

lemma X_dvd_V {k : ℕ} {f : PS} (h : X ^ k ∣ f) : X ^ (11 * k) ∣ V f := by
  obtain ⟨d, rfl⟩ := h
  exact ⟨V d, by rw [map_mul, map_pow, V_X, ← pow_mul]⟩

lemma X_dvd_g2 : X ∣ g2 := X_dvd_iff.mpr constantCoeff_g2

lemma X5_dvd_z : X ^ 5 ∣ z := ⟨E11 ^ 12 * Ring.inverse E1 ^ 12, by rw [z]; ring⟩

lemma X2_dvd_g3 : X ^ 2 ∣ g3 := by
  rw [g3]
  refine Dvd.dvd.mul_right (dvd_add (pow_dvd_pow_of_dvd X_dvd_g2 2) (Dvd.dvd.mul_left ?_ _)) _
  exact (pow_dvd_pow X (by norm_num)).trans X5_dvd_z

lemma X3_dvd_g4 : X ^ 3 ∣ g4 := by
  have h : (1 + g2) * g4 = g2 ^ 3 - 11 * z := by
    have := R1
    simp only [g4]; linear_combination (-1 : PS) * this
  have hd : X ^ 3 ∣ (1 + g2) * g4 := by
    rw [h]; exact dvd_sub (pow_dvd_pow_of_dvd X_dvd_g2 3) (Dvd.dvd.mul_left ((pow_dvd_pow X (by norm_num)).trans X5_dvd_z) _)
  obtain ⟨d, hd⟩ := hd
  refine ⟨Ring.inverse (1 + g2) * d, ?_⟩
  have hu := isUnit_one_add_g2
  calc g4 = Ring.inverse (1 + g2) * ((1 + g2) * g4) := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
    _ = _ := by rw [hd]; ring

lemma dvd_le {a b : ℕ} {f : PS} (h : X ^ a ∣ f) (hb : b ≤ a) : X ^ b ∣ f := (pow_dvd_pow X hb).trans h

/-- lower bounds for the `q`-orders of `e_1, …, e_10`. -/
def oe : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 3
  | 5 => 3
  | _ => 5

lemma X_dvd_e (j : ℕ) (hj : j < 10) : X ^ oe j ∣ lc (eF (j + 1)) := by
  have d1 : X ^ 1 ∣ g2 := by simpa using X_dvd_g2
  have d2 := X2_dvd_g3
  have d3 : X ^ 3 ∣ g2 ^ 2 - g3 := X3_dvd_g4
  have d5 := X5_dvd_z
  interval_cases j
  · show X ^ 1 ∣ lc (eF 1)
    rw [lcE1]
    exact dvd_add (dvd_add (dvd_add (d1.mul_left _) ((dvd_le d2 (by norm_num)).mul_left _)) ((dvd_le d3 (by norm_num)).mul_left _)) ((dvd_le d5 (by norm_num)).mul_left _)
  · show X ^ 1 ∣ lc (eF 2)
    rw [lcE2]
    exact dvd_add (dvd_add (dvd_add (d1.mul_left _) ((dvd_le d2 (by norm_num)).mul_left _)) ((dvd_le d3 (by norm_num)).mul_left _)) ((dvd_le d5 (by norm_num)).mul_left _)
  · show X ^ 2 ∣ lc (eF 3)
    rw [lcE3]
    exact dvd_add (dvd_add (d2.mul_left _) ((dvd_le d3 (by norm_num)).mul_left _)) ((dvd_le d5 (by norm_num)).mul_left _)
  · show X ^ 2 ∣ lc (eF 4)
    rw [lcE4]
    exact dvd_add (dvd_add (d2.mul_left _) ((dvd_le d3 (by norm_num)).mul_left _)) ((dvd_le d5 (by norm_num)).mul_left _)
  · show X ^ 3 ∣ lc (eF 5)
    rw [lcE5]
    exact dvd_sub (d3.mul_left _) ((dvd_le d5 (by norm_num)).mul_left _)
  · show X ^ 3 ∣ lc (eF 6)
    rw [lcE6]
    exact dvd_sub (d3.mul_left _) ((dvd_le d5 (by norm_num)).mul_left _)
  · show X ^ 5 ∣ lc (eF 7)
    rw [lcE7]
    exact d5.mul_left _
  · show X ^ 5 ∣ lc (eF 8)
    rw [lcE8]
    exact d5.mul_left _
  · show X ^ 5 ∣ lc (eF 9)
    rw [lcE9]
    exact d5.mul_left _
  · show X ^ 5 ∣ lc (eF 10)
    rw [lcE10]
    exact d5.mul_left _

lemma φ_shape : φ = X ^ 5 * (E121 * Ring.inverse E1) := by rw [φ]; ring

lemma cc_V (f : PS) : constantCoeff (V f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_ex]; simp

lemma cc_E1 : constantCoeff E1 = 1 := by
  rw [E1, ← coeff_zero_eq_constantCoeff_apply]; exact MockTheta5.JTP.coeff_zero_qfacInf

lemma cc_E121' : constantCoeff E121 * constantCoeff (Ring.inverse E1) = 1 := by
  rw [E121, cc_V, cc_V, cc_E1, cc_inv isUnit_E1 cc_E1, one_mul]

lemma cc_φ1 : constantCoeff (E121 * Ring.inverse E1) = 1 := by
  rw [map_mul, E121, cc_V, cc_V, cc_E1, cc_inv isUnit_E1 cc_E1, one_mul]

/-- `P'(φ) = q⁵⁰·w₁` with `w₁(0) = 11`. -/
theorem dP_shape : ∃ w1 : PS, evY φ dP = X ^ 50 * w1 ∧ constantCoeff w1 = 11 := by
  have hsum : X ^ 51 ∣ ∑ j ∈ Finset.range 10,
      ((10 - j : ℕ) : PS) * ((-1) ^ j * V (lc (eF (j + 1)))) * φ ^ (9 - j) := by
    refine Finset.dvd_sum fun j hj => ?_
    rw [Finset.mem_range] at hj
    have he := X_dvd_V (X_dvd_e j hj)
    have hφ : X ^ (5 * (9 - j)) ∣ φ ^ (9 - j) := by
      rw [φ_shape, mul_pow, ← pow_mul]; exact dvd_mul_right _ _
    have hm := mul_dvd_mul (he.mul_left ((-1) ^ j)) hφ
    rw [← pow_add] at hm
    rw [mul_assoc]
    exact Dvd.dvd.mul_left (dvd_le hm (by interval_cases j <;> simp [oe])) _
  obtain ⟨r, hr⟩ := hsum
  refine ⟨11 * (E121 * Ring.inverse E1) ^ 10 - X * r, ?_, ?_⟩
  · rw [dP_eval, hr, φ_shape]; ring
  · simp only [map_sub, map_mul, map_pow, cc_φ1, constantCoeff_X, zero_mul, sub_zero, one_pow, mul_one]
    rw [cc_E121', one_pow, mul_one]
    exact map_ofNat (constantCoeff (R := ℤ)) 11

end Atkin11Seed
