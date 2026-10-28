/-
# The derivation `θ = u d/du` on `ℤ[a]⟦b⟧` and the differential equations of the Tate point

`Θ = a∂_a − b∂_b`: on `ℤ[a]⟦b⟧`, `[bᴺ] Θ F = a·(d/da)[bᴺ]F − N·[bᴺ]F`. Under `a = u`, `b = q/u` this is
`u d/du` at fixed `q`.
-/
import RamanujanTau.TateQuot.Ring

set_option autoImplicit false

noncomputable section

namespace TateQuot

open PowerSeries

local notation "aX" => (Polynomial.X : P)

/-- the underlying map of `Θ`. -/
def Θf (F : R2) : R2 :=
  mk fun N => aX * Polynomial.derivative (coeff N F) - (N : P) * coeff N F

lemma coeff_Θf (F : R2) (N : ℕ) :
    coeff N (Θf F) = aX * Polynomial.derivative (coeff N F) - (N : P) * coeff N F := coeff_mk _ _

/-- `Θ` as a `ℤ`-linear map. -/
def ΘL : R2 →ₗ[ℤ] R2 where
  toFun := Θf
  map_add' F G := by
    refine PowerSeries.ext fun N => ?_
    simp only [coeff_Θf, map_add]; ring
  map_smul' c F := by
    refine PowerSeries.ext fun N => ?_
    simp only [coeff_Θf, RingHom.id_apply, zsmul_eq_mul]
    rw [show ((c : R2) * F) = PowerSeries.C (c : P) * F by simp]
    rw [coeff_C_mul, show ((c : R2) * Θf F) = PowerSeries.C (c : P) * Θf F by simp, coeff_C_mul,
      coeff_Θf, Polynomial.derivative_mul]
    simp only [Polynomial.derivative_intCast, zero_mul, zero_add]
    ring

lemma Θf_mul (F G : R2) : Θf (F * G) = F • Θf G + G • Θf F := by
  refine PowerSeries.ext fun N => ?_
  rw [smul_eq_mul, smul_eq_mul, map_add, coeff_Θf, coeff_mul, coeff_mul, coeff_mul,
    map_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [show (∑ x ∈ Finset.antidiagonal N, coeff x.1 G * coeff x.2 (Θf F)) =
      ∑ x ∈ Finset.antidiagonal N, coeff x.2 G * coeff x.1 (Θf F) from
    Finset.sum_equiv (Equiv.prodComm ℕ ℕ) (by simp [add_comm]) (by simp)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [coeff_Θf, coeff_Θf, Polynomial.derivative_mul, ← hx]
  push_cast; ring

/-- **The derivation `Θ = u d/du`** on `ℤ[a]⟦b⟧`. -/
def Θ : Derivation ℤ R2 R2 := Derivation.mk' ΘL Θf_mul

lemma Θ_apply (F : R2) : Θ F = Θf F := rfl

lemma coeff_Θ (F : R2) (N : ℕ) :
    coeff N (Θ F) = aX * Polynomial.derivative (coeff N F) - (N : P) * coeff N F := coeff_Θf F N

lemma Θ_C (c : P) : Θ (C c) = C (aX * Polynomial.derivative c) := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_Θ, coeff_C, coeff_C]
  split_ifs with h <;> simp [h]

lemma Θ_ofNat (n : ℕ) [n.AtLeastTwo] : Θ (OfNat.ofNat n : R2) = 0 := by
  rw [← map_ofNat (C (R := P)) n, Θ_C, Polynomial.derivative_ofNat, mul_zero, map_zero]

lemma Θ_resc (f : PowerSeries ℤ) : Θ (rescale aX (PowerSeries.map (Int.castRingHom P) f)) = 0 := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_Θ, coeff_rescale, coeff_map, map_zero]
  simp only [eq_intCast, Polynomial.derivative_mul, Polynomial.derivative_X_pow,
    Polynomial.derivative_intCast, mul_zero, add_zero]
  rcases N with _ | N
  · simp
  · simp only [Nat.add_sub_cancel]; push_cast; ring

lemma Θ_a4B : Θ a4B = 0 := Θ_resc _
lemma Θ_a6B : Θ a6B = 0 := Θ_resc _

lemma X_mul_deriv_X_pow (n : ℕ) : aX * Polynomial.derivative (aX ^ n) = (n : P) * aX ^ n := by
  rw [Polynomial.derivative_X_pow]
  rcases n with _ | n
  · simp
  · simp only [Nat.add_sub_cancel, map_natCast]; push_cast; ring

lemma X_mul_deriv_C_X_pow (c : ℤ) (n : ℕ) :
    aX * Polynomial.derivative (Polynomial.C c * aX ^ n) = Polynomial.C c * (n : P) * aX ^ n := by
  rw [Polynomial.derivative_C_mul, mul_left_comm, X_mul_deriv_X_pow]; ring

lemma Rm_term (m N d : ℕ) :
    ((d : P) ^ (m + 1)) * (aX ^ (N + d) + (-1) ^ m * aX ^ (N - d) - (if m = 0 then 2 else 0) * aX ^ N)
      = Polynomial.C ((d : ℤ) ^ (m + 1)) * aX ^ (N + d) +
        Polynomial.C ((d : ℤ) ^ (m + 1) * (-1) ^ m) * aX ^ (N - d) -
        Polynomial.C ((d : ℤ) ^ (m + 1) * (if m = 0 then 2 else 0)) * aX ^ N := by
  split_ifs <;> simp <;> ring

lemma Θ_mk_Rm (m : ℕ) : Θ (mk (Rm m)) = mk (Rm (m + 1)) := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_Θ, coeff_mk, coeff_mk, Rm, Rm, map_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdN : d ≤ N := Nat.divisor_le hd
  rw [Rm_term, Rm_term, map_sub, map_add, mul_sub, mul_add, X_mul_deriv_C_X_pow,
    X_mul_deriv_C_X_pow, X_mul_deriv_C_X_pow]
  have hc : (((N - d : ℕ) : P)) = (N : P) - d := by push_cast [hdN]; ring
  rw [hc]
  simp only [add_eq_zero, one_ne_zero, and_false, if_false, mul_zero, map_zero, zero_mul, sub_zero]
  split_ifs with h1
  · subst h1; simp; ring
  · simp; ring

/-! ### `θ` on the explicit series -/

/-- `v = a − 1` (`= u − 1`). -/
abbrev vB : R2 := C (aX - 1)
/-- `a` (`= u`). -/
abbrev wB : R2 := C aX

lemma Θ_vB : Θ vB = wB := by
  rw [Θ_C]; simp

lemma Θ_C_mul (c : P) (F : R2) : Θ (C c * F) = C c * Θ F + C (aX * Polynomial.derivative c) * F := by
  rw [Derivation.leibniz, Θ_C, smul_eq_mul, smul_eq_mul]; ring

lemma Θ_zB (m : ℕ) : Θ (zB m) = C (aX * Polynomial.derivative (cpoly m)) +
    ((m : R2) + 2) * wB * vB ^ (m + 1) * mk (Rm m) + vB ^ (m + 2) * mk (Rm (m + 1)) := by
  rw [zB, map_add, Θ_C, Θ_C_mul, Θ_mk_Rm, Polynomial.derivative_pow]
  simp only [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_one,
    sub_zero, mul_one, map_mul, map_pow, map_natCast]
  push_cast
  ring

/-- **`θ` raises the index**: `(u−1)·θ(zB m) = (m+2) u · zB m + zB (m+1)` (`m ≤ 3`). -/
theorem zB_rel (m : ℕ) (hm : m ≤ 3) :
    vB * Θ (zB m) = ((m : R2) + 2) * wB * zB m + zB (m + 1) := by
  rw [Θ_zB]
  unfold zB
  have hc : (aX - 1) * (aX * Polynomial.derivative (cpoly m)) =
      ((m : P) + 2) * aX * cpoly m + cpoly (m + 1) := by
    interval_cases m <;> simp [cpoly] <;> ring
  have hC := congrArg (C (R := P)) hc
  simp only [map_mul, map_add, map_sub, map_pow, map_natCast, map_one, map_ofNat] at hC ⊢
  linear_combination hC

/-! ### The differential equations -/

lemma EB_v : zB 1 ^ 2 = 4 * zB 0 ^ 3 + vB ^ 2 * zB 0 ^ 2 + 4 * vB ^ 4 * a4B * zB 0 +
    4 * vB ^ 6 * a6B := by
  have h := EB_eq_zero
  rw [EB, sub_eq_zero] at h
  simpa only [map_pow] using h

lemma Θ_pow_v (k : ℕ) : Θ (vB ^ (k + 1)) = ((k : R2) + 1) * wB * vB ^ k := by
  rw [Derivation.leibniz_pow, Θ_vB]; simp; ring

lemma Θ_ofNat_mul (n : ℕ) [n.AtLeastTwo] (F : R2) : Θ (OfNat.ofNat n * F) = OfNat.ofNat n * Θ F := by
  rw [Derivation.leibniz, Θ_ofNat, smul_zero, add_zero, smul_eq_mul]

lemma two_ne_zero_R2 : (2 : R2) ≠ 0 := by
  intro h
  have h1 := congrArg (constantCoeff (R := P)) h
  rw [map_ofNat, map_zero] at h1
  have h2 := congrArg (Polynomial.eval (0 : ℤ)) h1
  simp at h2

lemma Θ_four : Θ (4 : R2) = 0 := Θ_ofNat 4

lemma zB1_ne_zero : zB 1 ≠ 0 := by
  intro h
  have := congrArg (fun F : R2 => Polynomial.coeff (constantCoeff F) 1) h
  simp [zB, cpoly, Rm] at this

/-- **`θ²x = 6x² + x + 2a₄`** (times `(u−1)⁴`). -/
theorem zB2_eq : zB 2 = 6 * zB 0 ^ 2 + vB ^ 2 * zB 0 + 2 * vB ^ 4 * a4B := by
  have hE := EB_v
  have hΘ := congrArg Θ hE
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    Θ_four, Θ_a4B, Θ_a6B, Θ_vB] at hΘ
  have h0 := zB_rel 0 (by norm_num)
  have h1 := zB_rel 1 (by norm_num)
  push_cast at h0 h1 hΘ
  have key : 2 * zB 1 * (zB 2 - (6 * zB 0 ^ 2 + vB ^ 2 * zB 0 + 2 * vB ^ 4 * a4B)) = 0 := by
    linear_combination vB * hΘ - 2 * zB 1 * h1 +
      (12 * zB 0 ^ 2 + 2 * vB ^ 2 * zB 0 + 4 * vB ^ 4 * a4B) * h0 - 6 * wB * hE
  rcases mul_eq_zero.mp key with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd h two_ne_zero_R2
    · exact absurd h zB1_ne_zero
  · exact sub_eq_zero.mp h

lemma Θ_two : Θ (2 : R2) = 0 := Θ_ofNat 2
lemma Θ_six : Θ (6 : R2) = 0 := Θ_ofNat 6
lemma Θ_twelve : Θ (12 : R2) = 0 := Θ_ofNat 12

/-- `θ³x = 12 x θx + θx` (times `(u−1)⁵`). -/
theorem zB3_eq : zB 3 = 12 * zB 0 * zB 1 + vB ^ 2 * zB 1 := by
  have hI := zB2_eq
  have hΘ := congrArg Θ hI
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    Θ_two, Θ_six, Θ_a4B, Θ_vB] at hΘ
  have h0 := zB_rel 0 (by norm_num)
  have h2 := zB_rel 2 (by norm_num)
  push_cast at h0 h2 hΘ
  linear_combination -h2 + vB * hΘ + (12 * zB 0 + vB ^ 2) * h0 - 4 * wB * hI

/-- **`θ⁴x = 120x³ + 30x² + (72a₄+1)x + 48a₆ + 2a₄`** (times `(u−1)⁶`). -/
theorem zB4_eq : zB 4 = 120 * zB 0 ^ 3 + 30 * vB ^ 2 * zB 0 ^ 2 + (72 * a4B + 1) * vB ^ 4 * zB 0 +
    (48 * a6B + 2 * a4B) * vB ^ 6 := by
  have hI := zB3_eq
  have hΘ := congrArg Θ hI
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
    Θ_twelve, Θ_vB] at hΘ
  have h0 := zB_rel 0 (by norm_num)
  have h1 := zB_rel 1 (by norm_num)
  have h3 := zB_rel 3 (by norm_num)
  have hE := EB_v
  have h2 := zB2_eq
  push_cast at h0 h1 h3 hΘ
  linear_combination -h3 + vB * hΘ + 12 * zB 1 * h0 + (12 * zB 0 + vB ^ 2) * h1 - 5 * wB * hI +
    12 * hE + (12 * zB 0 + vB ^ 2) * h2

end TateQuot
