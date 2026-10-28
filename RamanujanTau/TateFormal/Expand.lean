import RamanujanTau.TateFormal.Formal
import RamanujanTau.TateFormal.Swap

/-!
# Expanding at `u = 1 + T`: the Tate point over `K⟦q⟧⟦T⟧`
-/

set_option autoImplicit false

noncomputable section

namespace TateFormal

open PowerSeries

variable (K : Type*) [CommRing K]

local notation "LT" => LaurentPolynomial.T (R := ℤ)

/-- the unit `1 + T` of `K⟦T⟧`. -/
def uT : (PowerSeries K)ˣ :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr (by simp) : IsUnit (1 + X : PowerSeries K)).unit

lemma uT_val : ((uT K : (PowerSeries K)ˣ) : PowerSeries K) = 1 + X := rfl

/-- `u ↦ 1 + T`. -/
def ι : A →+* PowerSeries K := LaurentPolynomial.eval₂ (Int.castRingHom _) (uT K)

variable {K}

lemma ι_T (n : ℤ) : ι K (LT n) = ((uT K ^ n : (PowerSeries K)ˣ) : PowerSeries K) := by
  rw [ι, LaurentPolynomial.eval₂_T]

lemma ι_U : ι K U = 1 + X := by rw [U, ι_T, zpow_one, uT_val]

/-- `(1+T) d/dT (1+T)ⁿ = n (1+T)ⁿ`. -/
lemma theta_T (n : ℤ) : (1 + X) * derivative K (ι K (LT n)) = (n : PowerSeries K) * ι K (LT n) := by
  rw [ι_T]
  rcases Int.eq_nat_or_neg n with ⟨d, rfl | rfl⟩
  · rw [zpow_natCast, Units.val_pow_eq_pow_val, uT_val]
    cases d with
    | zero => simp
    | succ d =>
      rw [Derivation.leibniz_pow, map_add, derivative_X, Derivation.map_one_eq_zero]
      simp only [zero_add, smul_eq_mul, mul_one, nsmul_eq_mul]
      push_cast; ring
  · rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
    set v : PowerSeries K := ((uT K)⁻¹ : (PowerSeries K)ˣ).val
    have hv : (1 + X) * v = 1 := by rw [← uT_val]; exact (uT K).mul_inv
    have hdv : (1 + X) * derivative K v = -v := by
      have h := congrArg (derivative K) hv
      rw [Derivation.leibniz, map_add, derivative_X, Derivation.map_one_eq_zero] at h
      simp only [zero_add, smul_eq_mul, mul_one] at h
      linear_combination h
    cases d with
    | zero => simp
    | succ d =>
      rw [Derivation.leibniz_pow]
      simp only [smul_eq_mul, nsmul_eq_mul]
      push_cast
      linear_combination (((d : PowerSeries K) + 1) * v ^ d) * hdv

lemma deriv_natCast (c : ℕ) : derivative K (c : PowerSeries K) = 0 := by
  rw [show (c : PowerSeries K) = C (c : K) by simp]; exact derivativeFun_C _

lemma deriv_natCast_mul (c : ℕ) (f : PowerSeries K) :
    derivative K ((c : PowerSeries K) * f) = c * derivative K f := by
  rw [Derivation.leibniz, deriv_natCast, smul_zero, add_zero, smul_eq_mul]

lemma theta_Pc (N : ℕ) : (1 + X) * derivative K (ι K (Pc N)) = ι K (Qc N) := by
  simp only [Pc, Qc, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have h2 : derivative K (2 : PowerSeries K) = 0 := by exact_mod_cast deriv_natCast (K := K) 2
  simp only [map_mul (ι K), map_natCast (ι K), map_sub (ι K), map_add (ι K), map_pow (ι K),
    map_ofNat (ι K)]
  rw [deriv_natCast_mul, map_sub (derivative K), map_add (derivative K), h2, sub_zero]
  have t1 := theta_T (K := K) (d : ℤ)
  have t2 := theta_T (K := K) (-(d : ℤ))
  push_cast at t1 t2
  linear_combination (d : PowerSeries K) * t1 + (d : PowerSeries K) * t2

lemma ι_U_sub : ι K (U - 1) = X := by rw [map_sub, ι_U, map_one]; ring

lemma Pc_zero : Pc 0 = 0 := by simp [Pc]
lemma Qc_zero : Qc 0 = 0 := by simp [Qc]

lemma coeff_xA (N : ℕ) : coeff N xA = (if N = 0 then U else 0) + (U - 1) ^ 2 * Pc N := by
  rw [xA, map_add, coeff_C, coeff_C_mul, coeff_mk]

lemma coeff_qA (N : ℕ) : coeff N qA = (if N = 0 then -(U * (1 + U)) else 0) + (U - 1) ^ 3 * Qc N := by
  rw [qA, map_add, coeff_C, coeff_C_mul, coeff_mk]

variable (K)

/-- `X̃ = T² x` over `K⟦q⟧⟦T⟧`. -/
def Xs : PowerSeries (PowerSeries K) := sw (PowerSeries.map (ι K) xA)
/-- `Q̃ = T³ (2y + x)` over `K⟦q⟧⟦T⟧`. -/
def Qs : PowerSeries (PowerSeries K) := sw (PowerSeries.map (ι K) qA)

variable {K}

lemma map_ι_int (f : PowerSeries ℤ) :
    PowerSeries.map (ι K) (PowerSeries.map (Int.castRingHom A) f) =
      PowerSeries.map (C (R := K)) (PowerSeries.map (Int.castRingHom K) f) := by
  ext N : 1; simp [coeff_map]

lemma sw_C_ι_pow (k : ℕ) : sw (C (ι K ((U - 1) ^ k))) = X ^ k := by
  rw [map_pow, ι_U_sub, map_pow, map_pow, sw_C_X]

theorem E4_K : Qs K ^ 2 = 4 * Xs K ^ 3 + X ^ 2 * Xs K ^ 2 +
    4 * C (PowerSeries.map (Int.castRingHom K) TateCurve.a4) * X ^ 4 * Xs K +
    4 * C (PowerSeries.map (Int.castRingHom K) TateCurve.a6) * X ^ 6 := by
  have h := congrArg (fun f => sw (PowerSeries.map (ι K) f)) EA_eq_zero
  simp only [EA, map_sub, map_add, map_mul, map_pow, map_ofNat, map_zero, PowerSeries.map_C] at h
  have hX1 : sw (C (ι K U)) - sw (C (ι K 1)) = X := by
    rw [← map_sub sw, ← map_sub C, ← map_sub (ι K), ι_U_sub, sw_C_X]
  rw [hX1, a4A, a6A, map_ι_int, map_ι_int, sw_map_C, sw_map_C] at h
  simp only [Xs, Qs]
  linear_combination h

lemma cc_Xs : PowerSeries.constantCoeff (Xs K) = 1 := by
  ext N
  rw [← coeff_zero_eq_constantCoeff_apply, Xs, coeff_sw, coeff_map, coeff_xA, map_add, map_mul,
    map_pow, ι_U_sub, coeff_one]
  rw [show (X : PowerSeries K) ^ 2 * ι K (Pc N) = X * (X * ι K (Pc N)) by ring, map_add,
    coeff_zero_X_mul, add_zero]
  split_ifs with h
  · simp [ι_U]
  · simp

lemma cc_Qs : PowerSeries.constantCoeff (Qs K) = -2 := by
  ext N
  rw [← coeff_zero_eq_constantCoeff_apply, Qs, coeff_sw, coeff_map, coeff_qA, map_add, map_mul,
    map_pow, ι_U_sub]
  rw [show (X : PowerSeries K) ^ 3 * ι K (Qc N) = X * (X ^ 2 * ι K (Qc N)) by ring, map_add,
    coeff_zero_X_mul, add_zero]
  rw [show (-2 : PowerSeries K) = C (-2) by rw [map_neg, map_ofNat], coeff_C]
  split_ifs with h
  · subst h; simp [ι_U]
    norm_num
  · simp

lemma pre_D : C (1 + X) * (C X * dI (PowerSeries.map (ι K) xA) - 2 * PowerSeries.map (ι K) xA) =
    PowerSeries.map (ι K) qA := by
  ext N : 1
  rw [coeff_C_mul, map_sub, coeff_C_mul, show (2 : PowerSeries (PowerSeries K)) = C 2 by
    rw [map_ofNat], coeff_C_mul, dI, coeff_mk, coeff_map, coeff_map, coeff_xA, coeff_qA]
  simp only [map_add, map_mul, map_pow, ι_U_sub]
  have hθ := theta_Pc (K := K) N
  by_cases h : N = 0
  · subst h
    simp only [if_true, Pc_zero, Qc_zero, map_zero, mul_zero, add_zero, map_neg, map_mul, map_add,
      map_one, ι_U, derivative_X, Derivation.map_one_eq_zero]
    ring
  · simp only [h, if_false, map_zero, zero_add]
    rw [Derivation.leibniz, Derivation.leibniz_pow, derivative_X]
    simp only [smul_eq_mul, nsmul_eq_mul]
    push_cast
    linear_combination X ^ 3 * hθ

theorem D_K : (1 + X) * (X * MvPowerSeries.pd () (Xs K : MvPowerSeries Unit (PowerSeries K)) -
    2 * Xs K) = Qs K := by
  rw [Xs, pd_sw, Qs, ← pre_D]
  simp only [map_mul, map_sub, map_add, map_one, map_ofNat, sw_C_X]

end TateFormal
