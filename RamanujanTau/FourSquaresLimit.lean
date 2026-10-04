/-
# Jacobi's four-square theorem, part 2: the limit `n → ∞`

From `S(n) = 1`: `((−q;q)_∞/(q;q)_∞)⁴ · (1 + 8 Σ_{k≥1} (−1)^k q^k/(1+q^k)²) = 1`.
Everything is compared modulo `X^N` through the quotient map `π`. For `n ≥ 2N` every finite Pochhammer
symbol in `T(n,k)` with `k < N` agrees with its infinite version, and the terms with `k ≥ N` vanish.
-/
import RamanujanTau.FourSquaresWZ
import RamanujanTau.MockTheta5JacobiTriple

set_option autoImplicit false

namespace FourSquares
open PowerSeries Finset MockTheta5.Bailey MockTheta5.JTP

/-! ## congruences modulo `X^N` -/

lemma coeff_eq_of_dvd {f g : PowerSeries ℤ} {K k : ℕ} (h : (X : PowerSeries ℤ) ^ K ∣ f - g) (hk : k < K) :
    coeff k f = coeff k g := by
  have := (PowerSeries.X_pow_dvd_iff.mp h) k hk
  rwa [map_sub, sub_eq_zero] at this

lemma eq_of_dvd_all {f g : PowerSeries ℤ} (h : ∀ N, (X : PowerSeries ℤ) ^ (N + 1) ∣ f - g) : f = g := by
  ext k; exact coeff_eq_of_dvd (h k) (Nat.lt_succ_self k)

/-- reduction modulo `X^N`. -/
noncomputable abbrev π (N : ℕ) : PowerSeries ℤ →+* PowerSeries ℤ ⧸ Ideal.span {(X : PowerSeries ℤ) ^ N} :=
  Ideal.Quotient.mk _

lemma π_eq_iff {N : ℕ} {f g : PowerSeries ℤ} : π N f = π N g ↔ (X : PowerSeries ℤ) ^ N ∣ f - g := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

lemma π_inverse {N : ℕ} {u : PowerSeries ℤ} (hu : IsUnit u) : π N (Ring.inverse u) = Ring.inverse (π N u) := by
  have h1 : π N u * π N (Ring.inverse u) = 1 := by rw [← map_mul, Ring.mul_inverse_cancel u hu, map_one]
  have hu' : IsUnit (π N u) := hu.map _
  calc π N (Ring.inverse u) = (Ring.inverse (π N u) * π N u) * π N (Ring.inverse u) := by
        rw [Ring.inverse_mul_cancel _ hu', one_mul]
    _ = Ring.inverse (π N u) * (π N u * π N (Ring.inverse u)) := by ring
    _ = Ring.inverse (π N u) := by rw [h1, mul_one]

lemma π_X_pow {N k : ℕ} (h : N ≤ k) : π N (X ^ k) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]; exact pow_dvd_pow X h

/-! ## `(−q;q)_∞` and the Lambert series -/

noncomputable def mfacInf : PowerSeries ℤ := mk fun k => coeff k (mfac (k + 1))

lemma X_pow_dvd_mfac_sub (N : ℕ) : ∀ M, N ≤ M → (X : PowerSeries ℤ) ^ (N + 1) ∣ mfac M - mfac N := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    rw [mfac_succ, show mfac M * (1 + X ^ (M + 1)) - mfac N = (mfac M - mfac N) + mfac M * X ^ (M + 1) by ring]
    exact dvd_add ih (Dvd.dvd.mul_left (pow_dvd_pow X (by omega)) _)

lemma π_mfac {N n : ℕ} (h : N ≤ n) : π N (mfac n) = π N mfacInf := by
  rw [π_eq_iff, PowerSeries.X_pow_dvd_iff]
  intro k hk
  rw [map_sub, mfacInf, coeff_mk, sub_eq_zero,
    coeff_eq_of_dvd (X_pow_dvd_mfac_sub k n (by omega)) (Nat.lt_succ_self k),
    coeff_eq_of_dvd (X_pow_dvd_mfac_sub k (k + 1) (by omega)) (Nat.lt_succ_self k)]

lemma π_qfac {N n : ℕ} (h : N ≤ n) : π N (qfac n) = π N qfacInf := by
  rw [π_eq_iff, PowerSeries.X_pow_dvd_iff]
  intro k hk
  rw [map_sub, coeff_qfacInf (show k + 1 ≤ n by omega), sub_self]

/-- the Lambert-type term `(−1)^k q^k/(1+q^k)²`. -/
noncomputable def tk (k : ℕ) : PowerSeries ℤ := (-1) ^ k * X ^ k * Ring.inverse ((1 + X ^ k) ^ 2)

/-- `Σ_{k≥1} (−1)^k q^k/(1+q^k)²`. -/
noncomputable def Lser : PowerSeries ℤ := mk fun m => coeff m (∑ i ∈ range m, tk (i + 1))

lemma π_Lser (N : ℕ) : π N Lser = π N (∑ i ∈ range N, tk (i + 1)) := by
  rw [π_eq_iff, PowerSeries.X_pow_dvd_iff]
  intro m hm
  rw [map_sub, Lser, coeff_mk, sub_eq_zero, map_sum, map_sum,
    show N = m + (N - m) by omega, sum_range_add]
  rw [sum_eq_zero (s := range (N - m)) fun i _ => by
    rw [tk, mul_comm ((-1 : PowerSeries ℤ) ^ (m + i + 1)), mul_assoc, coeff_X_pow_mul', if_neg (by omega)], add_zero]

/-! ## the limit -/

theorem limit_identity : mfacInf ^ 4 * Ring.inverse (qfacInf ^ 4) * (1 + 8 * Lser) = 1 := by
  refine eq_of_dvd_all fun N => ?_
  rw [← π_eq_iff, map_one]
  set n := N + 1 + (N + 1) with hn
  have hS := congrArg (π (N + 1)) (St_eq_one n)
  rw [St, Ct, map_one, map_add, map_sum, hn, sum_range_add] at hS
  rw [sum_eq_zero (s := range (N + 1)) (f := fun x => π (N + 1) (Tt (N + 1 + (N + 1)) (N + 1 + x + 1))) (fun i _ => by
    dsimp only; rw [Tt]; simp only [map_mul, π_X_pow (show N + 1 ≤ N + 1 + i + 1 by omega), mul_zero, zero_mul]),
    add_zero, ← hn] at hS
  have hP : ∀ m, N + 1 ≤ m → π (N + 1) (qfac m) = π (N + 1) qfacInf := fun m h => π_qfac h
  have hM : ∀ m, N + 1 ≤ m → π (N + 1) (mfac m) = π (N + 1) mfacInf := fun m h => π_mfac h
  have hC : π (N + 1) (mfac n ^ 4 * Ring.inverse (qfac n ^ 4))
      = π (N + 1) (mfacInf ^ 4 * Ring.inverse (qfacInf ^ 4)) := by
    simp (disch := unit_tac) only [map_mul, map_pow, π_inverse]
    rw [hM n (by omega), hP n (by omega), π_inverse ((isUnit_qfacInf).pow 4), map_pow]
  have hT : ∀ i ∈ range (N + 1), π (N + 1) (Tt n (i + 1))
      = π (N + 1) (mfacInf ^ 4 * Ring.inverse (qfacInf ^ 4)) * (8 * π (N + 1) (tk (i + 1))) := by
    intro i hi
    rw [mem_range] at hi
    rw [Tt, tk]
    simp (disch := unit_tac) only [map_mul, map_pow, π_inverse]
    rw [hM (n - (i + 1)) (by omega), hM (n + (i + 1)) (by omega), hM n (by omega), hP (n - (i + 1)) (by omega),
      hP (n + (i + 1)) (by omega), hP n (by omega), π_inverse ((isUnit_qfacInf).pow 4), map_pow,
      show π (N + 1) qfacInf * π (N + 1) qfacInf * π (N + 1) qfacInf ^ 2 = π (N + 1) qfacInf ^ 4 by ring]
    simp only [map_ofNat]
    ring
  rw [← hS, hC, sum_congr rfl hT, ← mul_sum]
  simp only [map_mul, map_add, map_one, π_Lser, map_sum, map_ofNat]
  rw [← mul_sum]
  ring

end FourSquares
