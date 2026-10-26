/-
# Analytic realizations of q-series on the unit disc

Tools for `Taylor.T`: locally uniform convergence of series by the M-test, Taylor series of polynomials, and the
holomorphic functions behind Ramanujan's third-order `f(q)` and `φ(−q)`, with `T f = f(q)` as formal series.
-/
import RamanujanTau.Taylor
import RamanujanTau.MockTheta3

set_option autoImplicit false

namespace Taylor
open Complex Filter Metric Function Set
open scoped Topology Nat

/-- **M-test on the disc**: a series of functions dominated on every closed disc `|z| ≤ r < 1` by a summable
sequence converges locally uniformly on the open disc. -/
lemma tlu_tsum_nat {f : ℕ → ℂ → ℂ}
    (hb : ∀ r : ℝ, 0 ≤ r → r < 1 → ∃ u : ℕ → ℝ, Summable u ∧ ∀ n z, ‖z‖ ≤ r → ‖f n z‖ ≤ u n) :
    TendstoLocallyUniformlyOn (fun N z => ∑ n ∈ Finset.range N, f n z) (fun z => ∑' n, f n z) atTop
      (ball 0 1) := by
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun x hx => ?_
  have hx1 : ‖x‖ < 1 := by simpa using hx
  set r := (‖x‖ + 1) / 2
  obtain ⟨u, hu, hfu⟩ := hb r (by positivity) (by simp only [r]; linarith)
  refine ⟨ball 0 r, mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (by simp only [mem_ball_zero_iff, r]; linarith)),
    tendstoUniformlyOn_tsum_nat hu fun n z hz => hfu n z ?_⟩
  exact (by simpa using hz : ‖z‖ < r).le

/-- `Σ r^{n²} Cⁿ < ∞` for `0 ≤ r < 1`. -/
lemma summable_sq_mul_pow {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (C : ℝ) (hC : 0 ≤ C) :
    Summable fun n : ℕ => r ^ (n ^ 2) * C ^ n := by
  rcases h0.eq_or_lt with rfl | h0
  · refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    have : n ≠ 0 := by simpa using hn
    simp [zero_pow (pow_ne_zero 2 this)]
  -- dominate by a geometric series once `r^n C ≤ 1/2`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, r ^ N * C ≤ 1 / 2 := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).mul_const C
    rw [zero_mul] at this
    exact (this.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
  refine (summable_nat_add_iff N).mp ?_
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (C ^ N * r ^ (N ^ 2)))
  have e : (n + N) ^ 2 = N ^ 2 + N * n + n * (n + N) := by ring
  calc r ^ ((n + N) ^ 2) * C ^ (n + N) = (C ^ N * r ^ (N ^ 2)) * (r ^ (N * n) * r ^ (n * (n + N)) * C ^ n) := by
        rw [e, pow_add, pow_add, pow_add]; ring
    _ ≤ (C ^ N * r ^ (N ^ 2)) * ((r ^ N * C) ^ n) := by
        gcongr
        rw [mul_pow, pow_mul]
        have : r ^ (n * (n + N)) ≤ 1 := pow_le_one₀ h0.le h1.le
        nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ (r ^ N) ^ n * C ^ n)]
    _ ≤ (C ^ N * r ^ (N ^ 2)) * (1 / 2) ^ n := by gcongr

/-- the Taylor series of a polynomial is the polynomial. -/
lemma T_poly (p : Polynomial ℤ) :
    T (fun z => (p.map (Int.castRingHom ℂ)).eval z) = MockTheta5.JTP.ψC (p : PowerSeries ℤ) := by
  ext n
  rw [coeff_T, RamanujanTau.DiscriminantBridge.iteratedDeriv_poly_zero, PowerSeries.coeff_map,
    Polynomial.coeff_coe, Polynomial.coeff_map]
  have : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

lemma hol_poly (p : Polynomial ℤ) : Hol (fun z => (p.map (Int.castRingHom ℂ)).eval z) :=
  (Polynomial.differentiable _).differentiableOn

lemma T_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (hf : ∀ i, Hol (f i)) :
    T (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, T (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using T_const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [T_add (hf a) (DifferentiableOn.fun_sum fun i _ => hf i), ih]

lemma inverse_eq_inv (u : PowerSeries ℂ) (hu : PowerSeries.constantCoeff u ≠ 0) : Ring.inverse u = u⁻¹ := by
  have h : u * u⁻¹ = 1 := PowerSeries.mul_inv_cancel u hu
  have hU : IsUnit u := IsUnit.of_mul_eq_one _ h
  calc Ring.inverse u = Ring.inverse u * (u * u⁻¹) := by rw [h, mul_one]
    _ = u⁻¹ := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hU, one_mul]

/-- **series of the shape `Σ sₙ q^{n²}/Pₙ(q)^k`.** The holomorphic sum has Taylor series the formal sum. -/
theorem T_series (s : ℕ → ℤ) (k : ℕ) (P : ℕ → Polynomial ℤ)
    (hc : ∀ n, PowerSeries.constantCoeff ((P n : Polynomial ℤ) : PowerSeries ℤ) = 1)
    (hP0 : ∀ n z, z ∈ ball (0 : ℂ) 1 → ((P n).map (Int.castRingHom ℂ)).eval z ≠ 0)
    (hPb : ∀ r : ℝ, 0 ≤ r → r < 1 → ∃ c > (0 : ℝ), ∀ n z, ‖z‖ ≤ r → c ^ n ≤ ‖((P n).map (Int.castRingHom ℂ)).eval z‖)
    (hs : ∀ n, ‖(s n : ℂ)‖ ≤ 1) :
    Hol (fun z => ∑' n, (s n : ℂ) * z ^ (n ^ 2) * (((P n).map (Int.castRingHom ℂ)).eval z)⁻¹ ^ k) ∧
    T (fun z => ∑' n, (s n : ℂ) * z ^ (n ^ 2) * (((P n).map (Int.castRingHom ℂ)).eval z)⁻¹ ^ k)
      = MockTheta5.JTP.ψC (PowerSeries.mk fun m => PowerSeries.coeff m (∑ n ∈ Finset.range (m + 1),
          PowerSeries.C (s n) * PowerSeries.X ^ (n ^ 2) * Ring.inverse ((P n : Polynomial ℤ) : PowerSeries ℤ) ^ k)) := by
  set ev : ℕ → ℂ → ℂ := fun n z => ((P n).map (Int.castRingHom ℂ)).eval z
  set term : ℕ → ℂ → ℂ := fun n z => (s n : ℂ) * z ^ (n ^ 2) * (ev n z)⁻¹ ^ k
  have hterm : ∀ n, Hol (term n) := fun n =>
    ((differentiableOn_const _).mul (differentiableOn_id.pow _)).mul (((hol_poly (P n)).inv (hP0 n)).pow k)
  have hT : TendstoLocallyUniformlyOn (fun N z => ∑ n ∈ Finset.range N, term n z) (fun z => ∑' n, term n z) atTop
      (ball 0 1) := by
    refine tlu_tsum_nat fun r h0 h1 => ?_
    obtain ⟨c, hc0, hcb⟩ := hPb r h0 h1
    refine ⟨fun n => r ^ (n ^ 2) * ((c⁻¹) ^ k) ^ n, summable_sq_mul_pow h0 h1 _ (by positivity), fun n z hz => ?_⟩
    simp only [term, norm_mul, norm_pow, norm_inv]
    have h1' : ‖z‖ ^ (n ^ 2) ≤ r ^ (n ^ 2) := pow_le_pow_left₀ (norm_nonneg _) hz _
    have h2 : ‖ev n z‖⁻¹ ≤ (c ^ n)⁻¹ := inv_anti₀ (by positivity) (hcb n z hz)
    have h3 : (‖ev n z‖⁻¹) ^ k ≤ ((c⁻¹) ^ k) ^ n := by
      calc (‖ev n z‖⁻¹) ^ k ≤ ((c ^ n)⁻¹) ^ k := pow_le_pow_left₀ (by positivity) h2 k
        _ = _ := by rw [← inv_pow, ← pow_mul, ← pow_mul, mul_comm]
    calc ‖(s n : ℂ)‖ * ‖z‖ ^ (n ^ 2) * ‖ev n z‖⁻¹ ^ k ≤ 1 * r ^ (n ^ 2) * ((c⁻¹) ^ k) ^ n := by gcongr; exact hs n
      _ = _ := by ring
  have hhol : Hol (fun z => ∑' n, term n z) :=
    Hol.of_tlu hT fun N => DifferentiableOn.fun_sum fun n _ => hterm n
  refine ⟨hhol, T_of_tlu hT (fun N => DifferentiableOn.fun_sum fun n _ => hterm n) fun m => ?_⟩
  -- Taylor series of each term
  have hTn : ∀ n, T (term n) = MockTheta5.JTP.ψC (PowerSeries.C (s n) * PowerSeries.X ^ (n ^ 2)
      * Ring.inverse ((P n : Polynomial ℤ) : PowerSeries ℤ) ^ k) := by
    intro n
    have hu : PowerSeries.constantCoeff (MockTheta5.JTP.ψC ((P n : Polynomial ℤ) : PowerSeries ℤ)) ≠ 0 := by
      rw [show MockTheta5.JTP.ψC = PowerSeries.map (Int.castRingHom ℂ) from rfl, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hc n]; simp
    have hU : IsUnit ((P n : Polynomial ℤ) : PowerSeries ℤ) := by
      rw [PowerSeries.isUnit_iff_constantCoeff, hc n]; exact isUnit_one
    have hA : Hol (fun z => (s n : ℂ) * z ^ (n ^ 2)) := (differentiableOn_const _).mul (differentiableOn_id.pow _)
    have hB : Hol (fun z => (ev n z)⁻¹) := (hol_poly (P n)).inv (hP0 n)
    have hBk : Hol (fun z => (ev n z)⁻¹ ^ k) := hB.pow k
    have e1 := T_mul hA hBk
    have e2 := T_mul (f := fun _ => (s n : ℂ)) (g := fun z => z ^ (n ^ 2)) (differentiableOn_const _)
      (differentiableOn_id.pow _)
    have e3 := T_pow hB k
    have e4 := T_inv (hol_poly (P n)) (hP0 n)
    have e5 := T_pow (f := fun z => z) differentiableOn_id (n ^ 2)
    show T (fun z => (fun z => (s n : ℂ) * z ^ (n ^ 2)) z * (fun z => (ev n z)⁻¹ ^ k) z) = _
    rw [e1]
    simp only at e2 e3 e5 ⊢
    rw [e2, e3, e4, T_poly, T_const, e5, T_id,
      map_mul, map_mul, map_pow, map_pow, CrankProof.map_inverse _ hU, inverse_eq_inv _ hu]
    simp [MockTheta5.JTP.ψC]
  filter_upwards [eventually_ge_atTop (m + 1)] with N hN
  rw [T_sum _ _ hterm, map_sum]
  simp only [hTn]
  rw [show MockTheta5.JTP.ψC = PowerSeries.map (Int.castRingHom ℂ) from rfl, PowerSeries.coeff_map]
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  rw [← map_sum (Int.castRingHom ℂ), ← map_sum (PowerSeries.coeff m)]
  congr 1
  rw [← Finset.sum_range_add_sum_Ico _ hN, map_add, add_eq_left, map_sum]
  refine Finset.sum_eq_zero fun n hn => ?_
  have : m < n ^ 2 := by
    have := (Finset.mem_Ico.mp hn).1; nlinarith
  rw [mul_comm (PowerSeries.C (s n)), mul_assoc, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

end Taylor
