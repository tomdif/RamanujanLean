/-
# Hecke facts for `λ(n) = τ(n) n^{−11/2}` and the local power series at a prime

* `lam_mul_coprime`: `λ(mn) = λ(m)λ(n)` for coprime `m, n` (Mordell).
* `lam_hecke`: `λ(p^{r+2}) = λ(p)λ(p^{r+1}) − λ(p^r)`.
* `lam_sq_eq_bb`: `λ(n)² = τ(n)²/n¹¹` (the repo's `bb`).
* `Dps p = Σ λ(p^j)² X^j` satisfies `Dps · P = 1 + X` with `P = 1 − (λ_p²−1)X + (λ_p²−1)X² − X³`
  (`Dps_mul_P`). Hence `eps = Dps⁻¹ = P · Σ(−1)^j X^j` (`eps_eq`) and `|coeff j eps| ≤ 4 + 2λ_p²`.
-/
import RamanujanTau.HafnerBridge.Main
import RamanujanTau.HeckeQExp

set_option autoImplicit false

namespace RamanujanTau.HafnerBridge2

open Finset PowerSeries
open RamanujanTau.HafnerBridge

lemma lam_def (n : ℕ) : lam n = ((RamanujanTau.tau n : ℤ) : ℝ) * (n : ℝ) ^ (-(11 / 2 : ℝ)) := rfl

lemma lam_zero : lam 0 = 0 := by
  rw [lam_def]; simp [RamanujanTau.tau_zero]

lemma lam_mul_coprime {m n : ℕ} (h : m.Coprime n) : lam (m * n) = lam m * lam n := by
  rw [lam_def, lam_def, lam_def, RamanujanTau.tau_mul_coprime h]
  push_cast
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

lemma lam_pow_eq (p r : ℕ) :
    lam (p ^ r) = ((RamanujanTau.tau (p ^ r) : ℤ) : ℝ) * ((p : ℝ) ^ (-(11 / 2 : ℝ))) ^ r := by
  rw [lam_def]
  congr 1
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
    ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm]

lemma lam_hecke {p : ℕ} (hp : p.Prime) (r : ℕ) :
    lam (p ^ (r + 2)) = lam p * lam (p ^ (r + 1)) - lam (p ^ r) := by
  have hrec := RamanujanTau.tau_hecke_recurrence hp (r := r + 1) (by omega)
  simp only [show r + 1 + 1 = r + 2 by ring, show r + 1 - 1 = r by omega] at hrec
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set s : ℝ := (p : ℝ) ^ (-(11 / 2 : ℝ)) with hs
  have hs2 : (p : ℝ) ^ 11 * s ^ 2 = 1 := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_add hp0]
    norm_num
  have h1 : lam p = ((RamanujanTau.tau p : ℤ) : ℝ) * s := by
    have := lam_pow_eq p 1; rw [pow_one, pow_one] at this; exact this
  rw [lam_pow_eq, lam_pow_eq, lam_pow_eq, h1, hrec]
  push_cast
  linear_combination (-(((RamanujanTau.tau (p ^ r) : ℤ) : ℝ)) * s ^ r) * hs2

lemma lam_sq_eq_bb {n : ℕ} (hn : 1 ≤ n) : lam n ^ 2 = RamanujanTau.GoodSecondTerm.bb n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [lam_def, RamanujanTau.GoodSecondTerm.bb, mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ _),
    ← Real.rpow_mul hn0.le]
  rw [show (-(11 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -((11 : ℕ) : ℝ) by norm_num, Real.rpow_neg hn0.le,
    Real.rpow_natCast]
  rfl

/-! ### The local power series -/

/-- `D_p(X) = Σ_j λ(p^j)² X^j`. -/
noncomputable def Dps (p : ℕ) : PowerSeries ℝ := PowerSeries.mk fun j => lam (p ^ j) ^ 2

/-- `U_{p,a}(X) = Σ_j λ(p^{j+a}) λ(p^j) X^j`. -/
noncomputable def Ups (p a : ℕ) : PowerSeries ℝ := PowerSeries.mk fun j => lam (p ^ (j + a)) * lam (p ^ j)

/-- `e_p = D_p⁻¹`. -/
noncomputable def eps (p : ℕ) : PowerSeries ℝ := (Dps p)⁻¹

/-- `g_{p,a} = U_{p,a} · D_p⁻¹`, the local factor of `λ(p^a ·)λ(·)` over `λ(·)²`. -/
noncomputable def gps (p a : ℕ) : PowerSeries ℝ := Ups p a * eps p

lemma lam_one' : lam 1 = 1 := RamanujanTau.HafnerBridge.lam_one

lemma constantCoeff_Dps (p : ℕ) : constantCoeff (Dps p) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Dps, coeff_mk, pow_zero, lam_one', one_pow]

lemma eps_mul_Dps (p : ℕ) : eps p * Dps p = 1 :=
  PowerSeries.inv_mul_cancel _ (by rw [constantCoeff_Dps]; norm_num)

lemma gps_mul_Dps (p a : ℕ) : gps p a * Dps p = Ups p a := by
  rw [gps, mul_assoc, eps_mul_Dps, mul_one]

/-- `P = 1 − bX + bX² − X³` with `b = λ_p² − 1`. -/
noncomputable def Pps (p : ℕ) : PowerSeries ℝ :=
  1 - C (lam p ^ 2 - 1) * X + C (lam p ^ 2 - 1) * X ^ 2 - X ^ 3

lemma coeff_mul_Xpow (f : PowerSeries ℝ) (i M : ℕ) :
    coeff M (f * X ^ i) = if i ≤ M then coeff (M - i) f else 0 := coeff_mul_X_pow' f i M

lemma Dps_mul_P {p : ℕ} (hp : p.Prime) : Dps p * Pps p = 1 + X := by
  ext M
  have e : Dps p * Pps p = Dps p - C (lam p ^ 2 - 1) * (Dps p * X ^ 1) +
      C (lam p ^ 2 - 1) * (Dps p * X ^ 2) - Dps p * X ^ 3 := by
    unfold Pps; ring
  rw [map_add (coeff M), coeff_one, coeff_X]
  rw [e, map_sub, map_add, map_sub, coeff_C_mul, coeff_C_mul, coeff_mul_Xpow, coeff_mul_Xpow,
    coeff_mul_Xpow]
  generalize hb : lam p ^ 2 - 1 = b
  simp only [Dps, coeff_mk, coeff_one, coeff_X]
  rcases M with _ | _ | _ | M
  · simp [lam_one']
  · simp [lam_one']; rw [← hb]; ring
  · have h2 := lam_hecke hp 0
    simp only [zero_add, pow_zero, pow_one, lam_one'] at h2
    norm_num
    rw [h2, lam_one', ← hb]; ring
  · have h1 := lam_hecke hp M
    have h2 := lam_hecke hp (M + 1)
    rw [show M + 1 + 2 = M + 3 by ring, show M + 1 + 1 = M + 2 by ring] at h2
    simp only [show (1 : ℕ) ≤ M + 1 + 1 + 1 by omega, show (2 : ℕ) ≤ M + 1 + 1 + 1 by omega,
      show (3 : ℕ) ≤ M + 1 + 1 + 1 by omega, if_true, show M + 1 + 1 + 1 ≠ 0 by omega,
      show M + 1 + 1 + 1 ≠ 1 by omega, if_false, show M + 1 + 1 + 1 - 1 = M + 2 by omega,
      show M + 1 + 1 + 1 - 2 = M + 1 by omega, show M + 1 + 1 + 1 - 3 = M by omega,
      show M + 1 + 1 + 1 = M + 3 by omega]
    rw [h2, h1, ← hb]; ring

/-- `Σ (−1)^j X^j = (1+X)⁻¹`. -/
noncomputable def Alt : PowerSeries ℝ := PowerSeries.mk fun j => (-1 : ℝ) ^ j

lemma one_add_X_mul_Alt : (1 + X) * Alt = 1 := by
  ext M
  rw [add_mul, one_mul, map_add, mul_comm X Alt, ← pow_one (X : PowerSeries ℝ), coeff_mul_Xpow]
  simp only [Alt, coeff_mk, coeff_one]
  rcases M with _ | M
  · simp
  · simp only [show 1 ≤ M + 1 by omega, if_true, show M + 1 - 1 = M by omega, pow_succ,
      show M + 1 ≠ 0 by omega, if_false]
    ring

lemma eps_eq {p : ℕ} (hp : p.Prime) : eps p = Pps p * Alt := by
  calc eps p = eps p * ((1 + X) * Alt) := by rw [one_add_X_mul_Alt, mul_one]
    _ = (eps p * Dps p) * Pps p * Alt := by rw [← Dps_mul_P hp]; ring
    _ = Pps p * Alt := by rw [eps_mul_Dps, one_mul]

lemma abs_coeff_Alt_mul_Xpow (i M : ℕ) : |coeff M (Alt * X ^ i)| ≤ 1 := by
  rw [coeff_mul_Xpow]
  split_ifs
  · simp [Alt, coeff_mk]
  · simp

/-- `|e_j| ≤ 4 + 2λ_p²`. -/
lemma abs_coeff_eps_le {p : ℕ} (hp : p.Prime) (j : ℕ) : |coeff j (eps p)| ≤ 4 + 2 * lam p ^ 2 := by
  rw [eps_eq hp]
  have e : Pps p * Alt = Alt * X ^ 0 - C (lam p ^ 2 - 1) * (Alt * X ^ 1) +
      C (lam p ^ 2 - 1) * (Alt * X ^ 2) - Alt * X ^ 3 := by unfold Pps; ring
  rw [e, map_sub, map_add, map_sub, coeff_C_mul, coeff_C_mul]
  have a0 := abs_coeff_Alt_mul_Xpow 0 j
  have a1 := abs_coeff_Alt_mul_Xpow 1 j
  have a2 := abs_coeff_Alt_mul_Xpow 2 j
  have a3 := abs_coeff_Alt_mul_Xpow 3 j
  have hb : |lam p ^ 2 - 1| ≤ lam p ^ 2 + 1 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (lam p)]
  calc _ ≤ |coeff j (Alt * X ^ 0)| + |lam p ^ 2 - 1| * |coeff j (Alt * X ^ 1)| +
        |lam p ^ 2 - 1| * |coeff j (Alt * X ^ 2)| + |coeff j (Alt * X ^ 3)| := by
        refine (abs_sub _ _).trans ?_
        refine add_le_add ?_ le_rfl
        refine (abs_add_le _ _).trans ?_
        refine add_le_add ?_ (by rw [abs_mul])
        refine (abs_sub _ _).trans ?_
        exact add_le_add le_rfl (by rw [abs_mul])
    _ ≤ 1 + (lam p ^ 2 + 1) * 1 + (lam p ^ 2 + 1) * 1 + 1 := by gcongr
    _ = 4 + 2 * lam p ^ 2 := by ring

end RamanujanTau.HafnerBridge2
