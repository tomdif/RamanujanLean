/-
# Dyson's crank moment `M₂(n) = 2n·p(n)`, Euler's `n·p(n) = Σ σ(k) p(n−k)`, and Andrews' `spt(n) = n·p(n) − ½N₂(n)`

Both moment identities are first-order computations in the dual numbers `ℤ[ε]`.
* **Euler**: `q ↦ (1+ε)q` (`rescale`) sends `(q;q)_∞` to `(q;q)_∞·(1 − ε Σ_d d q^d/(1−q^d))`, and sends `p(n)` to
  `p(n) + ε·n·p(n)`.
* **Dyson**: `(1−zqᵈ)(1−qᵈ/z) = (1−qᵈ)² + w·qᵈ` with `w = 2 − z − z⁻¹`, so the coefficients of the crank generating
  function are polynomials in `w`. The second-moment functional sends a polynomial `f(w)` to `−2f'(0)`
  (`mom2_kernel`), and `f'(0)` is read off by `w ↦ ε`: `∏((1−qᵈ)² + εqᵈ) = (q;q)²_∞(1 + ε Σ_d qᵈ/(1−qᵈ)²)`.
Both sums equal `Σ σ(k) qᵏ`.
-/
import RamanujanTau.SptMoment
import Mathlib.Algebra.DualNumber
import Mathlib.NumberTheory.ArithmeticFunction.Misc

set_option autoImplicit false

namespace Dyson
open PowerSeries Finset DualNumber
open MockTheta5.Bailey MockTheta5.JTP

/-! ## Agreement modulo `X^N` -/

section Trunc
variable {R : Type*} [CommRing R]

lemma coeff_eq_of_dvd {f g : PowerSeries R} {K k : ℕ} (h : (X : PowerSeries R) ^ K ∣ f - g) (hk : k < K) :
    coeff k f = coeff k g := by
  have := (PowerSeries.X_pow_dvd_iff.mp h) k hk
  rwa [map_sub, sub_eq_zero] at this

lemma dvd_mul_sub {N : ℕ} {f f' g g' : PowerSeries R} (hf : (X : PowerSeries R) ^ N ∣ f - f')
    (hg : (X : PowerSeries R) ^ N ∣ g - g') : (X : PowerSeries R) ^ N ∣ f * g - f' * g' := by
  rw [show f * g - f' * g' = (f - f') * g + f' * (g - g') by ring]
  exact dvd_add (dvd_mul_of_dvd_left hf _) (dvd_mul_of_dvd_right hg _)

lemma dvd_inv_sub {N : ℕ} {f f' : PowerSeries R} (hu : IsUnit f) (hu' : IsUnit f')
    (h : (X : PowerSeries R) ^ N ∣ f - f') : (X : PowerSeries R) ^ N ∣ Ring.inverse f - Ring.inverse f' := by
  have h1 := Ring.inverse_mul_cancel f hu
  have h2 := Ring.inverse_mul_cancel f' hu'
  rw [show Ring.inverse f - Ring.inverse f' = Ring.inverse f * Ring.inverse f' * -(f - f') by
    linear_combination (-Ring.inverse f) * h2 + Ring.inverse f' * h1]
  exact dvd_mul_of_dvd_right (dvd_neg.mpr h) _

lemma inverse_eq_of_mul {a b : R} (h : a * b = 1) : Ring.inverse a = b := by
  have ha : IsUnit a := ⟨⟨a, b, h, by rw [mul_comm]; exact h⟩, rfl⟩
  calc Ring.inverse a = Ring.inverse a * (a * b) := by rw [h, mul_one]
    _ = b := by rw [← mul_assoc, Ring.inverse_mul_cancel a ha, one_mul]

lemma dvd_map_sub {S : Type*} [CommRing S] (φ : R →+* S) {N : ℕ} {f g : PowerSeries R}
    (h : (X : PowerSeries R) ^ N ∣ f - g) : (X : PowerSeries S) ^ N ∣ map φ f - map φ g := by
  obtain ⟨c, hc⟩ := h
  exact ⟨map φ c, by rw [← map_sub, hc, map_mul, map_pow, map_X]⟩

lemma dvd_rescale_sub (a : R) {N : ℕ} {f g : PowerSeries R}
    (h : (X : PowerSeries R) ^ N ∣ f - g) : (X : PowerSeries R) ^ N ∣ rescale a f - rescale a g := by
  obtain ⟨c, hc⟩ := h
  exact ⟨C (a ^ N) * rescale a c, by rw [← map_sub, hc, map_mul, map_pow, rescale_X, mul_pow, ← map_pow]; ring⟩

end Trunc

lemma isUnit_of_constCoeff_one {R : Type*} [CommRing R] {f : PowerSeries R} (h : constantCoeff f = 1) :
    IsUnit f := by
  rw [PowerSeries.isUnit_iff_constantCoeff, h]; exact isUnit_one

/-! ## The divisor series -/

/-- `1/(1 − qᵈ)`. -/
noncomputable def Gd (d : ℕ) : PowerSeries ℤ := mk fun k => if d ∣ k then 1 else 0

/-- `qᵈ/(1 − qᵈ)²`, i.e. `Σ_m m q^{dm}`. -/
noncomputable def gd (d : ℕ) : PowerSeries ℤ := mk fun k => if d ∣ k then ((k / d : ℕ) : ℤ) else 0

/-- `Σ σ(k) qᵏ`. -/
noncomputable def sigS : PowerSeries ℤ := mk fun k => (ArithmeticFunction.sigma 1 k : ℤ)

lemma one_sub_mul_Gd {d : ℕ} (hd : 1 ≤ d) : (1 - X ^ d) * Gd d = 1 := by
  ext k
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', Gd, coeff_mk, coeff_one]
  by_cases hk : d ≤ k
  · rw [if_pos hk, coeff_mk, if_neg (show k ≠ 0 by omega)]
    have e := Nat.dvd_sub_iff_left hk (dvd_refl d)
    by_cases h : d ∣ k
    · simp only [if_pos h, if_pos (e.mpr h), sub_self]
    · simp only [if_neg h, if_neg (fun h' => h (e.mp h')), sub_self]
  · rw [if_neg hk, sub_zero]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · rw [if_neg (fun h => by have := Nat.le_of_dvd hk0 h; omega), if_neg (by omega)]

lemma one_sub_mul_gd {d : ℕ} (hd : 1 ≤ d) : (1 - X ^ d) * gd d = X ^ d * Gd d := by
  ext k
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_X_pow_mul', gd, Gd, coeff_mk]
  by_cases hk : d ≤ k
  · rw [if_pos hk, if_pos hk, coeff_mk, coeff_mk]
    have e := Nat.dvd_sub_iff_left hk (dvd_refl d)
    by_cases h : d ∣ k
    · simp only [if_pos h, if_pos (e.mpr h)]
      obtain ⟨j, rfl⟩ := h
      have hj : j ≠ 0 := by rintro rfl; rw [mul_zero] at hk; omega
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [show d * (i + 1) - d = d * i by rw [Nat.mul_succ]; omega, Nat.mul_div_cancel_left _ (by omega),
        Nat.mul_div_cancel_left _ (by omega)]
      push_cast; ring
    · simp only [if_neg h, if_neg (fun h' => h (e.mp h')), sub_zero]
  · rw [if_neg hk, if_neg hk, sub_zero]
    split_ifs with h
    · rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp
      · exact absurd (Nat.le_of_dvd hk0 h) hk
    · rfl

lemma sq_mul_gd {d : ℕ} (hd : 1 ≤ d) : (1 - X ^ d) ^ 2 * gd d = X ^ d := by
  rw [sq, mul_assoc, one_sub_mul_gd hd, mul_left_comm, one_sub_mul_Gd hd, mul_one]

/-- `Σ_{i<N} [i+1 ∣ k] f(i+1) = Σ_{d ∣ k} f(d)` once `1 ≤ k ≤ N`. -/
lemma sum_range_dvd (f : ℕ → ℤ) {k N : ℕ} (hk : 1 ≤ k) (hN : k ≤ N) :
    ∑ i ∈ range N, (if i + 1 ∣ k then f (i + 1) else 0) = ∑ d ∈ k.divisors, f d := by
  rw [Nat.divisors, sum_filter, sum_Ico_eq_sum_range, show k + 1 - 1 = k by omega]
  rw [show N = k + (N - k) by omega, sum_range_add]
  rw [sum_eq_zero (s := range (N - k)) (fun i _ => if_neg (fun h => by have := Nat.le_of_dvd hk h; omega)),
    add_zero]
  exact sum_congr rfl fun i _ => by rw [add_comm 1 i]

lemma coeff_sum_gd (N k : ℕ) (hk : k ≤ N) :
    coeff k (∑ i ∈ range N, gd (i + 1)) = coeff k sigS := by
  rw [map_sum, sigS, coeff_mk]
  simp only [gd, coeff_mk]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  rw [sum_range_dvd (fun d => ((k / d : ℕ) : ℤ)) hk0 hk, ArithmeticFunction.sigma_one_apply, Nat.cast_sum]
  exact Nat.sum_div_divisors k (fun d => (d : ℤ))

lemma coeff_dXGd {d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k) :
    coeff k ((d : PowerSeries ℤ) * X ^ d * Gd d) = if d ∣ k then (d : ℤ) else 0 := by
  rw [show (d : PowerSeries ℤ) * X ^ d * Gd d = X ^ d * (C (d : ℤ) * Gd d) by rw [map_natCast]; ring,
    coeff_X_pow_mul']
  by_cases hdk : d ≤ k
  · rw [if_pos hdk, coeff_C_mul, Gd, coeff_mk]
    have e := Nat.dvd_sub_iff_left hdk (dvd_refl d)
    by_cases h : d ∣ k
    · simp only [if_pos h, if_pos (e.mpr h), mul_one]
    · simp only [if_neg h, if_neg (fun h' => h (e.mp h')), mul_zero]
  · rw [if_neg hdk, if_neg (fun h => hdk (Nat.le_of_dvd hk h))]

lemma coeff_sum_dGd (N k : ℕ) (hk : k ≤ N) :
    coeff k (∑ i ∈ range N, ((i + 1 : ℕ) : PowerSeries ℤ) * X ^ (i + 1) * Gd (i + 1)) = coeff k sigS := by
  rw [map_sum, sigS, coeff_mk]
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [sum_eq_zero fun i _ => by
      rw [show ((i + 1 : ℕ) : PowerSeries ℤ) * X ^ (i + 1) * Gd (i + 1)
          = X ^ (i + 1) * (((i + 1 : ℕ) : PowerSeries ℤ) * Gd (i + 1)) by ring, coeff_X_pow_mul', if_neg (by omega)]]
    simp
  rw [sum_congr rfl fun i _ => coeff_dXGd (d := i + 1) (by omega) hk0, sum_range_dvd (fun d => (d : ℤ)) hk0 hk,
    ArithmeticFunction.sigma_one_apply, Nat.cast_sum]

/-! ## First-order expansions over `ℤ[ε]` -/

local notation "D" => DualNumber ℤ

/-- the inclusion `ℤ⟦q⟧ → ℤ[ε]⟦q⟧`. -/
noncomputable abbrev ι0 : PowerSeries ℤ →+* PowerSeries D := PowerSeries.map (Int.castRingHom D)

lemma Ceps_sq : (C (ε : D)) * C ε = 0 := by rw [← map_mul, eps_mul_eps, map_zero]

lemma ι0_X : ι0 (X : PowerSeries ℤ) = X := map_X _

lemma qfac_succ (N : ℕ) : qfac (N + 1) = qfac N * (1 - X ^ (N + 1)) := by
  rw [qfac, qfac, prod_range_succ]

lemma ι0_qfac (N : ℕ) : ι0 (qfac N) = ∏ i ∈ range N, (1 - X ^ (i + 1)) := by
  simp [qfac, map_prod]

/-- `∏_{d ≤ N} ((1−qᵈ)² + εqᵈ) = (q;q)²_N · (1 + ε Σ_{d≤N} qᵈ/(1−qᵈ)²)`. -/
lemma prod_eps_crank (N : ℕ) :
    ∏ i ∈ range N, ((1 - X ^ (i + 1)) ^ 2 + C (ε : D) * X ^ (i + 1))
      = ι0 (qfac N) ^ 2 * (1 + C ε * ι0 (∑ i ∈ range N, gd (i + 1))) := by
  induction N with
  | zero => simp [qfac]
  | succ N ih =>
    have h := congrArg ι0 (sq_mul_gd (d := N + 1) (by omega))
    simp only [map_mul, map_pow, map_sub, map_one, ι0_X] at h
    rw [prod_range_succ, ih, qfac_succ, sum_range_succ, map_mul, map_add]
    simp only [map_sub, map_one, map_pow, ι0_X]
    linear_combination (-(ι0 (qfac N)) ^ 2 * C (ε : D)) * h
      + (ι0 (qfac N)) ^ 2 * ι0 (∑ i ∈ range N, gd (i + 1)) * X ^ (N + 1) * Ceps_sq

lemma one_add_eps_pow (k : ℕ) : ((1 : D) + (ε : D)) ^ k = 1 + (k : D) * (ε : D) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]; push_cast
    linear_combination (k : D) * (eps_mul_eps (R := ℤ))

lemma rescale_factor (d : ℕ) :
    rescale ((1 : D) + ε) (ι0 (1 - X ^ d)) = 1 - X ^ d - (d : PowerSeries D) * C ε * X ^ d := by
  rw [map_sub, map_one, map_pow, ι0_X, map_sub, map_one, map_pow, rescale_X, mul_pow, ← map_pow, one_add_eps_pow,
    map_add, map_one, map_mul, map_natCast]
  ring

/-- `q ↦ (1+ε)q` on `(q;q)_N`: `(q;q)_N · (1 − ε Σ_{d≤N} d qᵈ/(1−qᵈ))`. -/
lemma rescale_qfac (N : ℕ) :
    rescale ((1 : D) + ε) (ι0 (qfac N))
      = ι0 (qfac N) * (1 - C ε * ι0 (∑ i ∈ range N, ((i + 1 : ℕ) : PowerSeries ℤ) * X ^ (i + 1) * Gd (i + 1))) := by
  induction N with
  | zero => simp [qfac]
  | succ N ih =>
    have h := congrArg ι0 (one_sub_mul_Gd (d := N + 1) (by omega))
    simp only [map_mul, map_sub, map_one, map_pow, ι0_X] at h
    rw [qfac_succ, map_mul, map_mul, ih, rescale_factor, sum_range_succ, map_add, map_mul, map_mul, map_pow, ι0_X,
      map_natCast]
    simp only [map_sub (ι0), map_one, map_pow, ι0_X]
    linear_combination (ι0 (qfac N) * C (ε : D) * ((N + 1 : ℕ) : PowerSeries D) * X ^ (N + 1)) * h
      + (ι0 (qfac N) * ι0 (∑ i ∈ range N, ((i + 1 : ℕ) : PowerSeries ℤ) * X ^ (i + 1) * Gd (i + 1))
          * ((N + 1 : ℕ) : PowerSeries D) * X ^ (N + 1)) * Ceps_sq


/-! ## Euler: `n·p(n) = Σ_k σ(k) p(n−k)` -/

lemma X_pow_dvd_qfacInf_sub (N : ℕ) : (X : PowerSeries ℤ) ^ N ∣ qfacInf - qfac N := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro k hk
  rw [map_sub, coeff_qfacInf (show k + 1 ≤ N by omega), sub_self]

lemma dvd_partitionGF_sub (N : ℕ) : (X : PowerSeries ℤ) ^ N ∣ partitionGF - Ring.inverse (qfac N) :=
  dvd_inv_sub isUnit_qfacInf (isUnit_qfac N) (X_pow_dvd_qfacInf_sub N)

lemma X_pow_dvd_sigS_sub_dGd (N : ℕ) :
    (X : PowerSeries ℤ) ^ N ∣ (∑ i ∈ range N, ((i + 1 : ℕ) : PowerSeries ℤ) * X ^ (i + 1) * Gd (i + 1)) - sigS := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro k hk
  rw [map_sub, coeff_sum_dGd N k hk.le, sub_self]

lemma X_pow_dvd_sigS_sub_gd (N : ℕ) :
    (X : PowerSeries ℤ) ^ N ∣ (∑ i ∈ range N, gd (i + 1)) - sigS := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro k hk
  rw [map_sub, coeff_sum_gd N k hk.le, sub_self]

lemma ι0_inv_mul (N : ℕ) : ι0 (qfac N) * ι0 (Ring.inverse (qfac N)) = 1 := by
  rw [← map_mul, Ring.mul_inverse_cancel _ (isUnit_qfac N), map_one]

lemma coeff_ι0 (n : ℕ) (F : PowerSeries ℤ) : coeff n (ι0 F) = ((coeff n F : ℤ) : D) := by
  rw [coeff_map]; rfl

/-- `snd` of `coeff n (F·(1 + c·ε·G))` is `c·coeff n (F·G)`. -/
lemma snd_coeff_eps (n : ℕ) (c : ℤ) (F G : PowerSeries ℤ) :
    TrivSqZeroExt.snd (coeff n (ι0 F * (1 + C ((c : D) * ε) * ι0 G))) = c * coeff n (F * G) := by
  rw [mul_add, mul_one, mul_left_comm, ← map_mul, map_add, coeff_C_mul, coeff_ι0, coeff_ι0]
  simp

/-- **Euler's identity** `n·p(n) = Σ_{k=1}^n σ(k)·p(n−k)`, as `n·p(n) = [qⁿ] P(q)·Σσ(k)qᵏ`. -/
theorem euler_sigma (n : ℕ) : (n : ℤ) * coeff n partitionGF = coeff n (partitionGF * sigS) := by
  set N := n + 1
  set TN := ∑ i ∈ range N, ((i + 1 : ℕ) : PowerSeries ℤ) * X ^ (i + 1) * Gd (i + 1)
  set R := rescale ((1 : D) + ε)
  have hPB : ι0 qfacInf * ι0 partitionGF = 1 := by
    rw [← map_mul, partitionGF, Ring.mul_inverse_cancel _ isUnit_qfacInf, map_one]
  have hRP : Ring.inverse (R (ι0 qfacInf)) = R (ι0 partitionGF) :=
    inverse_eq_of_mul (by rw [← map_mul, hPB, map_one])
  have hfin : (R (ι0 (qfac N))) * (ι0 (Ring.inverse (qfac N)) * (1 + C ε * ι0 TN)) = 1 := by
    rw [rescale_qfac]
    linear_combination ι0_inv_mul N - ι0 (qfac N) * ι0 (Ring.inverse (qfac N)) * ι0 TN ^ 2 * Ceps_sq
  have hfin' := inverse_eq_of_mul hfin
  have hu1 : IsUnit (R (ι0 qfacInf)) := ⟨⟨_, _, by rw [← map_mul, hPB, map_one], by
    rw [← map_mul, mul_comm, hPB, map_one]⟩, rfl⟩
  have hu2 : IsUnit (R (ι0 (qfac N))) := ⟨⟨_, _, hfin, by rw [mul_comm]; exact hfin⟩, rfl⟩
  have hd := dvd_inv_sub hu1 hu2 (dvd_rescale_sub _ (dvd_map_sub _ (X_pow_dvd_qfacInf_sub N)))
  rw [hRP, hfin'] at hd
  have hc := congrArg TrivSqZeroExt.snd (coeff_eq_of_dvd hd (show n < N by omega))
  rw [show C (ε : D) = C (((1 : ℤ) : D) * ε) by simp, snd_coeff_eps, coeff_rescale, coeff_ι0,
    one_add_eps_pow] at hc
  simp at hc
  rw [hc]
  exact coeff_eq_of_dvd (dvd_mul_sub (dvd_sub_comm.mp (dvd_partitionGF_sub N)) (X_pow_dvd_sigS_sub_dGd N))
    (show n < N by omega)


/-- Euler's identity with explicit sums: `n·p(n) = Σ_{i+j=n} p(i)·σ(j)`. -/
theorem euler_sigma_sum (n : ℕ) :
    (n : ℤ) * Fintype.card n.Partition
      = ∑ x ∈ antidiagonal n, (Fintype.card x.1.Partition : ℤ) * (ArithmeticFunction.sigma 1 x.2 : ℤ) := by
  rw [← coeff_partitionGF_eq_card, euler_sigma, coeff_mul]
  refine sum_congr rfl fun x _ => ?_
  rw [coeff_partitionGF_eq_card, sigS, coeff_mk]

/-! ## Dyson: `M₂(n) = 2n·p(n)` -/

section DysonCrank
open CrankProof
open LaurentPolynomial (T)

/-- `w = 2 − z − z⁻¹`. -/
noncomputable def Wz : LaurentPolynomial ℤ := 2 - T 1 - T (-1)

/-- `ℤ[w] → ℤ[z, z⁻¹]`, `w ↦ 2 − z − z⁻¹`. -/
noncomputable def ιW : Polynomial ℤ →+* LaurentPolynomial ℤ := Polynomial.eval₂RingHom (Int.castRingHom _) Wz

lemma evU_one_Wz : evU 1 Wz = 0 := by
  rw [Wz, map_sub, map_sub, evU_T1, evU_Tm1, map_ofNat]; norm_num

/-- the second moment of `f(2 − z − z⁻¹)` is `−2·f'(0)`. -/
lemma mom2_ιW (p : Polynomial ℤ) : mom2 (ιW p) = -2 * p.coeff 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, Polynomial.coeff_add]; ring
  | monomial n a =>
    rw [ιW, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, Polynomial.coeff_monomial]
    rcases n with _ | m
    · rw [pow_zero, mul_one, if_neg (by norm_num), mul_zero,
        show (Int.castRingHom (LaurentPolynomial ℤ)) a = LaurentPolynomial.C a * T 0 by simp, mom2_CT]
      ring
    · rw [pow_succ', mul_left_comm, Wz, mom2_kernel, ← Wz]
      have h : (CrankProof.ev1 ((Int.castRingHom (LaurentPolynomial ℤ)) a * Wz ^ m) : ℂ) = if m = 0 then a else 0 := by
        rw [← evU_one_ev1, map_mul, map_pow, evU_one_Wz]
        rcases m with _ | m <;> simp
      have h' : CrankProof.ev1 ((Int.castRingHom (LaurentPolynomial ℤ)) a * Wz ^ m) = if m = 0 then a else 0 := by
        exact_mod_cast (by rw [h]; all_goals (split_ifs <;> simp) : ((CrankProof.ev1 ((Int.castRingHom (LaurentPolynomial ℤ)) a * Wz ^ m) : ℤ) : ℂ)
          = ((if m = 0 then a else 0 : ℤ) : ℂ))
      rw [h']
      rcases m with _ | m <;> simp

/-- `f(ε)` has `ε`-part `f'(0)`. -/
lemma snd_aeval_eps (p : Polynomial ℤ) : TrivSqZeroExt.snd (Polynomial.aeval (ε : D) p) = p.coeff 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, TrivSqZeroExt.snd_add, hp, hq, Polynomial.coeff_add]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.coeff_monomial]
    rcases n with _ | _ | m
    · simp
    · simp
    · rw [pow_succ, pow_succ, mul_assoc (ε ^ m), eps_mul_eps, mul_zero, mul_zero, if_neg (by omega)]; simp

/-- `∏_{d≤N} ((1−qᵈ)² + w qᵈ)` over `ℤ[w]`. -/
noncomputable def AwN (N : ℕ) : PowerSeries (Polynomial ℤ) :=
  ∏ i ∈ range N, ((1 - X ^ (i + 1)) ^ 2 + C Polynomial.X * X ^ (i + 1))

noncomputable def qW (N : ℕ) : PowerSeries (Polynomial ℤ) := ∏ i ∈ range N, (1 - X ^ (i + 1))

lemma isUnit_AwN (N : ℕ) : IsUnit (AwN N) := by
  apply isUnit_of_constCoeff_one
  rw [AwN, map_prod]
  exact prod_eq_one fun i _ => by simp

/-- the truncated crank generating function, with coefficients in `ℤ[w]`. -/
noncomputable def CW (N : ℕ) : PowerSeries (Polynomial ℤ) := qW N * Ring.inverse (AwN N)

lemma map_ιW_AwN (N : ℕ) : map ιW (AwN N) = pochL (T 1) 1 N * pochL (T (-1)) 1 N := by
  rw [AwN, map_prod, pochL, pochL, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  have hT : (C (T 1 : LaurentPolynomial ℤ)) * C (T (-1)) = 1 := by
    rw [← map_mul, ← LaurentPolynomial.T_add]; simp
  have hW : ιW Polynomial.X = 2 - T 1 - T (-1) := by simp [ιW, Wz]
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_X, map_C, hW, map_ofNat]
  rw [add_comm 1 i]
  linear_combination (-(X : PowerSeries (LaurentPolynomial ℤ)) ^ (2 * (i + 1))) * hT

lemma map_ιW_qW (N : ℕ) : map ιW (qW N) = pochL 1 1 N := by
  rw [qW, map_prod, pochL]
  refine prod_congr rfl fun i _ => ?_
  simp [add_comm 1 i]

lemma pochL_succ (c : LaurentPolynomial ℤ) (s n : ℕ) :
    pochL c s (n + 1) = pochL c s n * (1 - C c * X ^ (s + n)) := by
  rw [pochL, prod_range_succ]; rfl

lemma X_pow_dvd_pochL_sub (c : LaurentPolynomial ℤ) (s N : ℕ) :
    ∀ M, N ≤ M → (X : PowerSeries (LaurentPolynomial ℤ)) ^ (s + N) ∣ pochL c s M - pochL c s N := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
      rw [pochL_succ, show pochL c s M * (1 - C c * X ^ (s + M)) - pochL c s N
          = (pochL c s M - pochL c s N) - pochL c s M * C c * X ^ (s + M) by ring]
      exact dvd_sub ih (Dvd.dvd.mul_left (pow_dvd_pow X (by omega)) _)

lemma X_pow_dvd_pochInfL_sub (c : LaurentPolynomial ℤ) (N : ℕ) :
    (X : PowerSeries (LaurentPolynomial ℤ)) ^ N ∣ pochInfL c 1 - pochL c 1 N := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro k hk
  rw [map_sub, pochInfL, coeff_mk, sub_eq_zero]
  exact (coeff_eq_of_dvd (X_pow_dvd_pochL_sub c 1 (k + 1) N (by omega)) (by omega)).symm

lemma coeff_CgfL_eq (n : ℕ) : coeff n CgfL = ιW (coeff n (CW (n + 1))) := by
  rw [← coeff_map, CW, map_mul, map_inverse _ (isUnit_AwN _), map_ιW_AwN, map_ιW_qW]
  refine coeff_eq_of_dvd (K := n + 1) ?_ (by omega)
  refine dvd_mul_sub (X_pow_dvd_pochInfL_sub 1 _) (dvd_inv_sub ?_ ?_ (dvd_mul_sub (X_pow_dvd_pochInfL_sub _ _)
    (X_pow_dvd_pochInfL_sub _ _)))
  · exact (isUnit_pochInfL _ le_rfl).mul (isUnit_pochInfL _ le_rfl)
  · exact (isUnit_pochL _ le_rfl _).mul (isUnit_pochL _ le_rfl _)

lemma inv_sq_one_add {Q Qi E : PowerSeries D} (hQ : Q * Qi = 1) (hE : E * E = 0) :
    Ring.inverse (Q ^ 2 * (1 + E)) = Qi ^ 2 * (1 - E) :=
  inverse_eq_of_mul (by linear_combination (Q * Qi + 1) * hQ - (Q * Qi) ^ 2 * hE)

/-- `ℤ[w] → ℤ[ε]`, `w ↦ ε`. -/
noncomputable def ae : Polynomial ℤ →+* D := (Polynomial.aeval (ε : D)).toRingHom

lemma ae_apply (p : Polynomial ℤ) : ae p = Polynomial.aeval (ε : D) p := rfl

lemma ae_X : ae Polynomial.X = ε := by rw [ae_apply, Polynomial.aeval_X]

set_option maxHeartbeats 2000000 in
lemma map_ae_CW (N : ℕ) :
    map ae (CW N) = ι0 (Ring.inverse (qfac N)) * (1 + C (((-1 : ℤ) : D) * ε) * ι0 (∑ i ∈ range N, gd (i + 1))) := by
  have hA : map ae (AwN N) = ∏ i ∈ range N, ((1 - X ^ (i + 1)) ^ 2 + C (ε : D) * X ^ (i + 1)) := by
    rw [AwN, map_prod]
    simp only [map_add, map_pow, map_sub, map_one, map_mul, map_X, map_C, ae_X]
  have hq : map ae (qW N) = ι0 (qfac N) := by
    rw [qW, map_prod, ι0_qfac]
    simp only [map_pow, map_sub, map_one, map_X]
  have hE : (C (ε : D) * ι0 (∑ i ∈ range N, gd (i + 1))) * (C (ε : D) * ι0 (∑ i ∈ range N, gd (i + 1))) = 0 := by
    rw [mul_mul_mul_comm, Ceps_sq, zero_mul]
  have hI := map_inverse (PowerSeries.map ae) (isUnit_AwN N)
  rw [CW, map_mul, hI, hA, hq, prod_eps_crank, inv_sq_one_add (ι0_inv_mul N) hE]
  simp only [Int.cast_neg, Int.cast_one, neg_one_mul, map_neg]
  linear_combination (ι0 (Ring.inverse (qfac N)) * (1 - C (ε : D) * ι0 (∑ i ∈ range N, gd (i + 1)))) * ι0_inv_mul N

lemma crankL_eq (n : ℕ) (hn : 2 ≤ n) : crankL n = coeff n CgfL := by
  rw [← sub_eq_zero]
  apply laurent_eq_zero_of_evU
  intro u
  rw [map_sub, evU_crankL, crank_generating_function u.ne_zero hn, ← coeff_map, map_CgfL, RankProof.Cgf, sub_self]

/-- **Dyson's identity** (1989): the second crank moment is `M₂(n) = Σ_λ crank(λ)² = 2n·p(n)`. -/
theorem crank_moment_two {n : ℕ} (hn : 2 ≤ n) :
    ∑ l : n.Partition, crank l ^ 2 = 2 * n * (Fintype.card n.Partition : ℤ) := by
  have h1 : ∑ l : n.Partition, crank l ^ 2 = mom2 (crankL n) := by
    rw [crankL, map_sum]; simp_rw [mom2_T]
  have h2 : (coeff n (CW (n + 1))).coeff 1 = -coeff n (Ring.inverse (qfac (n + 1)) * ∑ i ∈ range (n + 1), gd (i + 1)) := by
    rw [← snd_aeval_eps, ← ae_apply,
      ← coeff_map, map_ae_CW, snd_coeff_eps]; ring
  have h3 : coeff n (Ring.inverse (qfac (n + 1)) * ∑ i ∈ range (n + 1), gd (i + 1)) = coeff n (partitionGF * sigS) :=
    coeff_eq_of_dvd (dvd_mul_sub (dvd_sub_comm.mp (dvd_partitionGF_sub _)) (X_pow_dvd_sigS_sub_gd _)) (by omega)
  rw [h1, crankL_eq n hn, coeff_CgfL_eq, mom2_ιW, h2, h3, ← euler_sigma, coeff_partitionGF_eq_card]
  ring

/-- **Andrews' formula** `spt(n) = n·p(n) − ½N₂(n)`, i.e. `2·spt(n) = 2n·p(n) − N₂(n)`. -/
theorem spt_eq_np_sub_rank_moment {n : ℕ} (hn : 2 ≤ n) :
    2 * (spt n : ℤ) = 2 * n * (Fintype.card n.Partition : ℤ) - ∑ l : n.Partition, rank l ^ 2 := by
  rw [← crank_moment_sub_rank_moment hn, crank_moment_two hn]

end DysonCrank

end Dyson
