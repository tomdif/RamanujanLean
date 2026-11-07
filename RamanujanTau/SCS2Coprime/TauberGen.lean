/-
# Item 4 (part 1): the Tauberian step for an arbitrary real sequence

For `c : ℕ → ℝ` with Laplace transform `Gc c` (`GboundsAB`), this is `SCSSharp.laplace_rieszK`,
`SCSSharp2.Rmean2_le21` and `SCSSharp2.Asum_bound_large21` with `a_n = τ(n)τ(n+h)` replaced by `c`:

* `laplace_rieszC`: `2π Σ c_n φ_k(e^{(n−x)/L}) = ∫ e^{xs/L} P_k(s) Gc(s/L) dy`, `s = L/x + iy`;
* `Rmean2C_le`: if `‖Gc c (1/x + iv)‖ ≤ K (|2vx|+3) x^{11901/1000}` for all `v`, then
  `2π |Σ c_n φ₂(e^{(n−x)/L})| ≤ e (48/σ₀) I₂ K x^{11901/1000}` with `L = xσ₀`;
* **`AsumC_bound`**: with `x = N+1`, from that pointwise input at `σ = 1/x`, a total bound
  `Σ_{n≤N} |c_n| ≤ A x¹²` and short-interval bounds `Σ_{N−D<n≤N} |c_n| ≤ A₂ x¹¹ (D + x^{1−1/21})`:
  `|Σ_{n≤N} c_n| ≤ (e·48·I₂·K + 2(13!·A + 3A₂)) x^{12−1/21}`.
-/
import RamanujanTau.SCS2Coprime.PointAB
import RamanujanTau.SCSSharp2.Asum21

set_option autoImplicit false

namespace RamanujanTau.SCS2Coprime

open MeasureTheory Complex Filter Finset
open RamanujanTau.RankinError RamanujanTau.SCSProof RamanujanTau.SCSSharp RamanujanTau.SCSSharp2
open scoped Real

variable (c : ℕ → ℝ)

/-- The term function on the line. -/
noncomputable def ktermC (k : ℕ) (x L : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  (c n : ℂ) * (((Real.exp ((n - x) / L) : ℝ) : ℂ) ^ (-((L / x : ℝ) + y * I)) *
    Pk k ((L / x : ℝ) + y * I))

lemma norm_ktermC (k : ℕ) {x L : ℝ} (hx : 0 < x) (hL : 0 < L) (n : ℕ) (y : ℝ) :
    ‖ktermC c k x L n y‖ = |c n| * Real.exp (-n * (1 / x)) * Real.exp 1 *
      ‖Pk k ((L / x : ℝ) + y * I)‖ := by
  unfold ktermC
  rw [norm_mul, norm_mul, cpow_exp_neg, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have hre : (-((L / x : ℝ) + y * I) * (((n - x) / L : ℝ) : ℂ)).re = -(L / x) * ((n - x) / L) := by
    simp [Complex.mul_re]
  rw [hre]
  have : -(L / x) * ((n - x) / L) = -n * (1 / x) + 1 := by field_simp; ring
  rw [this, Real.exp_add]; ring

lemma integral_ktermC {k : ℕ} (hk : 1 ≤ k) {x L : ℝ} (hx : 0 < x) (hL : 0 < L) (n : ℕ) :
    ∫ y, ktermC c k x L n y = (c n : ℂ) * (2 * π * (phi k (Real.exp ((n - x) / L)) : ℂ)) := by
  have hinv := mellinInv_Pk (k := k) hk (σ := L / x) (by positivity)
    (u := Real.exp ((n - x) / L)) (Real.exp_pos _)
  unfold mellinInv at hinv
  rw [Complex.real_smul] at hinv
  unfold ktermC
  rw [integral_const_mul]
  congr 1
  have h2π : (2 * π : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  rw [← hinv]
  push_cast
  field_simp
  congr 1; funext y; simp only [smul_eq_mul]; ring_nf

lemma integrable_ktermC {k : ℕ} (hk : 1 ≤ k) {x L : ℝ} (hx : 0 < x) (hL : 0 < L) (n : ℕ) :
    Integrable (ktermC c k x L n) := by
  have hP := integrable_Pk_line (k := k) hk (σ := L / x) (by positivity)
  have hmeas : AEStronglyMeasurable (ktermC c k x L n) := by
    refine Continuous.aestronglyMeasurable ?_
    unfold ktermC
    have hc1 := continuous_Pk_line k (σ := L / x) (by positivity)
    refine continuous_const.mul (Continuous.mul ?_ ?_)
    · exact Continuous.const_cpow (by fun_prop) (Or.inl (by
        exact_mod_cast (Real.exp_pos _).ne'))
    · push_cast at hc1 ⊢; exact hc1
  refine (hP.norm.const_mul (|c n| * Real.exp (-n * (1 / x)) * Real.exp 1)).mono' hmeas
    (Eventually.of_forall fun y => ?_)
  rw [norm_ktermC c k hx hL]

/-- **The exponential-Riesz formula** for an arbitrary real sequence. -/
theorem laplace_rieszC {k : ℕ} (hk : 1 ≤ k) {x L : ℝ} (hx : 0 < x) (hL : 0 < L)
    (hsum : Summable fun n : ℕ => |c n| * Real.exp (-n * (1 / x))) :
    (2 * π : ℂ) * ∑' n : ℕ, (c n : ℂ) * (phi k (Real.exp ((n - x) / L)) : ℂ) =
      ∫ y : ℝ, cexp (x * ((L / x : ℝ) + y * I) / L) * Pk k ((L / x : ℝ) + y * I) *
        Gc c (((L / x : ℝ) + y * I) / L) := by
  have hint := integrable_ktermC c hk hx hL
  have hsumI : Summable fun n => ∫ y, ‖ktermC c k x L n y‖ := by
    simp_rw [norm_ktermC c k hx hL, integral_const_mul]
    exact (hsum.mul_right (Real.exp 1)).mul_right _
  have key := integral_tsum_of_summable_integral_norm hint hsumI
  simp_rw [integral_ktermC c hk hx hL] at key
  rw [← tsum_mul_left]
  have e1 : ∀ n : ℕ, (2 * π : ℂ) * ((c n : ℂ) * (phi k (Real.exp ((n - x) / L)) : ℂ)) =
      (c n : ℂ) * (2 * π * (phi k (Real.exp ((n - x) / L)) : ℂ)) := fun n => by ring
  simp_rw [e1, key]
  congr 1
  funext y
  unfold ktermC Gc
  rw [← tsum_mul_left]
  congr 1
  funext n
  rw [cpow_exp_neg]
  have e : -(((L / x : ℝ) : ℂ) + y * I) * (((n - x) / L : ℝ) : ℂ) =
      x * (((L / x : ℝ) : ℂ) + y * I) / L + (-(n : ℂ) * ((((L / x : ℝ) : ℂ) + y * I) / L)) := by
    push_cast; field_simp; ring
  rw [e, Complex.exp_add]
  push_cast
  ring

/-- The quadratic exponential-Riesz mean of `c`. -/
noncomputable def Rmean2C (x L : ℝ) : ℝ := ∑' n : ℕ, c n * phi 2 (Real.exp ((n - x) / L))

set_option maxHeartbeats 2000000 in
/-- **Bound for the quadratic exponential-Riesz mean** from a pointwise bound on `Re W = 1/x`. -/
theorem Rmean2C_le (K : ℝ) (hK : 0 ≤ K) {x : ℝ} (hx : 1 ≤ x)
    (hsum : Summable fun n : ℕ => |c n| * Real.exp (-n * (1 / x)))
    (hpt : ∀ v : ℝ, ‖Gc c (((1 / x : ℝ) : ℂ) + v * I)‖ ≤
      K * (|2 * v / (1 / x)| + 3) * (1 / x) ^ (-(11901 / 1000 : ℝ)))
    {σ₀ : ℝ} (hσ0 : 0 < σ₀) :
    2 * π * |Rmean2C c x (x * σ₀)| ≤
      Real.exp 1 * (48 / σ₀) * I2 * (K * x ^ (11901 / 1000 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  set L := x * σ₀ with hLdef
  have hL : 0 < L := by positivity
  have hLx : L / x = σ₀ := by rw [hLdef]; field_simp
  have hR := laplace_rieszC c (k := 2) (by norm_num) hx0 hL hsum
  rw [hLx] at hR
  set Gm := K * x ^ (11901 / 1000 : ℝ)
  have hGm0 : 0 ≤ Gm := by positivity
  have hbound : ∀ y : ℝ, ‖cexp (x * ((σ₀ : ℂ) + y * I) / L) * Pk 2 ((σ₀ : ℂ) + y * I) *
      Gc c (((σ₀ : ℂ) + y * I) / L)‖ ≤
        Real.exp 1 * Gm * (48 / σ₀ * (1 + ‖y‖) ^ (-(2 : ℝ))) := by
    intro y
    rw [norm_mul, norm_mul, Complex.norm_exp]
    have hre : (x * ((σ₀ : ℂ) + y * I) / L).re = 1 := by
      rw [hLdef]; simp [Complex.div_re]; field_simp
    rw [hre]
    have hW : ((σ₀ : ℂ) + y * I) / L = ((1 / x : ℝ) : ℂ) + ((y / L : ℝ) : ℂ) * I := by
      have hσC : (σ₀ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
      have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
      rw [hLdef]; push_cast; field_simp
    rw [hW]
    have hG := hpt (y / L)
    have hθ : 2 * (y / L) / (1 / x) = 2 * y / σ₀ := by rw [hLdef]; field_simp
    have hxp : (1 / x) ^ (-(11901 / 1000 : ℝ)) = x ^ (11901 / 1000 : ℝ) := by
      rw [one_div, Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le, neg_neg]
    rw [hxp, hθ] at hG
    have hk := Pk2_mul_le hσ0 y
    calc Real.exp 1 * ‖Pk 2 ((σ₀ : ℂ) + y * I)‖ * ‖Gc c (((1 / x : ℝ) : ℂ) + ((y / L : ℝ) : ℂ) * I)‖
        ≤ Real.exp 1 * ‖Pk 2 ((σ₀ : ℂ) + y * I)‖ *
            (K * (|2 * y / σ₀| + 3) * x ^ (11901 / 1000 : ℝ)) := by gcongr
      _ = Real.exp 1 * Gm * (‖Pk 2 ((σ₀ : ℂ) + y * I)‖ * (|2 * y / σ₀| + 3)) := by ring
      _ ≤ _ := by gcongr
  have hint : Integrable fun y : ℝ => Real.exp 1 * Gm * (48 / σ₀ * (1 + ‖y‖) ^ (-(2 : ℝ))) :=
    (int2.const_mul _).const_mul _
  have hnorm := norm_integral_le_of_norm_le hint (Eventually.of_forall hbound)
  rw [← hR] at hnorm
  rw [integral_const_mul, integral_const_mul] at hnorm
  have hRe : ‖(2 * π : ℂ) * ∑' n : ℕ, (c n : ℂ) * (phi 2 (Real.exp ((n - x) / L)) : ℂ)‖ =
      2 * π * |Rmean2C c x L| := by
    unfold Rmean2C
    rw [norm_mul]
    have : (∑' n : ℕ, (c n : ℂ) * (phi 2 (Real.exp ((n - x) / L)) : ℂ)) =
        ((∑' n : ℕ, c n * phi 2 (Real.exp ((n - x) / L)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]; push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    congr 1
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  rw [hRe] at hnorm
  refine hnorm.trans (le_of_eq ?_)
  unfold I2
  ring

/-- `Rmean2C` as a finite sum. -/
lemma Rmean2C_eq (N : ℕ) {L : ℝ} (hL : 0 < L) :
    Rmean2C c ((N : ℝ) + 1) L = ∑ n ∈ range (N + 1), c n *
      (1 - Real.exp ((n - ((N : ℝ) + 1)) / L)) ^ 2 := by
  unfold Rmean2C
  rw [tsum_eq_sum (s := range (N + 1)) (fun n hn => ?_)]
  · refine sum_congr rfl fun n hn => ?_
    have : (n : ℝ) < N + 1 := by exact_mod_cast mem_range.1 hn
    rw [phi_of_le (Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) hL.le))]
  · have : (N : ℝ) + 1 ≤ n := by
      have := not_lt.1 (fun h => hn (mem_range.2 h)); exact_mod_cast this
    rw [phi2_of_ge (Real.one_le_exp (div_nonneg (by linarith) hL.le)), mul_zero]

/-- The sharp partial sum. -/
noncomputable def AsumC (N : ℕ) : ℝ := ∑ n ∈ range (N + 1), c n

set_option maxHeartbeats 4000000 in
/-- **Sharp sums from the pointwise bound** (generic `η = 1/21` chain). -/
theorem AsumC_bound (K A A₂ : ℝ) (hK : 0 ≤ K) (hA0 : 0 ≤ A) (hA20 : 0 ≤ A₂) (hc0 : c 0 = 0)
    (N : ℕ)
    (hsum : Summable fun n : ℕ => |c n| * Real.exp (-n * (1 / ((N : ℝ) + 1))))
    (hpt : ∀ v : ℝ, ‖Gc c (((1 / ((N : ℝ) + 1) : ℝ) : ℂ) + v * I)‖ ≤
      K * (|2 * v / (1 / ((N : ℝ) + 1))| + 3) * (1 / ((N : ℝ) + 1)) ^ (-(11901 / 1000 : ℝ)))
    (hA : ∑ n ∈ range (N + 1), |c n| ≤ A * ((N : ℝ) + 1) ^ 12)
    (hS : ∀ D : ℕ, ∑ n ∈ Ioc (N - D) N, |c n| ≤
      A₂ * ((N : ℝ) + 1) ^ 11 * (D + ((N : ℝ) + 1) ^ (1 - ηt))) :
    |AsumC c N| ≤ (Real.exp 1 * 48 * I2 * K + 2 * ((Nat.factorial 13 : ℝ) * A + 3 * A₂)) *
      ((N : ℝ) + 1) ^ (12 - ηt) := by
  set F : ℝ := (Nat.factorial 13 : ℝ)
  have hF : 0 < F := by positivity
  set x : ℝ := (N : ℝ) + 1 with hxdef
  have hx1 : 1 ≤ x := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hx0 : 0 < x := by linarith
  have hη := ηt_pos; have hη2 := ηt_le
  set L := x * x ^ (-(2 / 39 : ℝ)) with hLdef
  have hL : 0 < L := by positivity
  have hσ0 : 0 < x ^ (-(2 / 39 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  -- the smoothed sum
  have hRb : |Rmean2C c x L| ≤ Real.exp 1 * 48 * I2 * K * x ^ (12 - ηt) := by
    have hR := Rmean2C_le c K hK hx1 hsum hpt hσ0
    have hI2 := I2_nonneg
    have e : 48 / x ^ (-(2 / 39 : ℝ)) * x ^ (11901 / 1000 : ℝ) = 48 * x ^ (466139 / 39000 : ℝ) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hx0.le, neg_neg, mul_assoc, ← Real.rpow_add hx0]
      norm_num
    have hpow : x ^ (466139 / 39000 : ℝ) ≤ x ^ (12 - ηt) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by unfold ηt; norm_num)
    have h2π : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
    have hRn : 0 ≤ |Rmean2C c x L| := abs_nonneg _
    have hfin : Real.exp 1 * (48 / x ^ (-(2 / 39 : ℝ))) * I2 * (K * x ^ (11901 / 1000 : ℝ))
        ≤ Real.exp 1 * 48 * I2 * K * x ^ (12 - ηt) := by
      have : Real.exp 1 * (48 / x ^ (-(2 / 39 : ℝ))) * I2 * (K * x ^ (11901 / 1000 : ℝ))
          = Real.exp 1 * I2 * K * (48 / x ^ (-(2 / 39 : ℝ)) * x ^ (11901 / 1000 : ℝ)) := by ring
      rw [this, e]
      have h0 : 0 ≤ Real.exp 1 * I2 * K := by positivity
      calc Real.exp 1 * I2 * K * (48 * x ^ (466139 / 39000 : ℝ))
          ≤ Real.exp 1 * I2 * K * (48 * x ^ (12 - ηt)) := by gcongr
        _ = _ := by ring
    have := hR.trans hfin
    nlinarith
  rw [hxdef, Rmean2C_eq c N hL, ← hxdef] at hRb
  set u : ℕ → ℝ := fun n => Real.exp ((n - x) / L) with hu
  have hdec : AsumC c N = (∑ n ∈ range (N + 1), c n * (1 - u n) ^ 2) +
      ∑ n ∈ range (N + 1), c n * (u n * (2 - u n)) := by
    unfold AsumC; rw [← sum_add_distrib]; refine sum_congr rfl fun n _ => by ring
  set s := x ^ (1 / 273 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hx0 _
  set D : ℕ := ⌈x ^ (1 - ηt)⌉₊
  have hD1 : x ^ (1 - ηt) ≤ D := Nat.le_ceil _
  have hD2 : (D : ℝ) ≤ x ^ (1 - ηt) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  -- the far part
  have hfar : ∀ n ∈ (range (N + 1)).filter (fun n => n + D ≤ N), u n ≤ F / s ^ 13 := by
    intro n hn
    obtain ⟨-, hnD⟩ := mem_filter.1 hn
    have hnD' : (n : ℝ) + D ≤ N := by exact_mod_cast hnD
    have hkey : s ≤ (x - n) / L := by
      rw [le_div_iff₀ hL, hLdef, hs, mul_comm x, ← mul_assoc, ← Real.rpow_add hx0,
        ← Real.rpow_add_one hx0.ne']
      have : (1 / 273 : ℝ) + -(2 / 39) + 1 = 1 - ηt := by unfold ηt; norm_num
      rw [this]; linarith
    have hexp : s ^ 13 / F ≤ Real.exp ((x - n) / L) :=
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ hs0.le hkey 13) hF.le).trans
        (Real.pow_div_factorial_le_exp _ (le_trans hs0.le hkey) 13)
    calc u n = (Real.exp ((x - n) / L))⁻¹ := by
          simp only [hu]; rw [← Real.exp_neg]; ring_nf
      _ ≤ (s ^ 13 / F)⁻¹ := by gcongr
      _ = F / s ^ 13 := by rw [inv_div]
  have hu0 : ∀ n, 0 < u n := fun n => Real.exp_pos _
  have hfar_sum : ∑ n ∈ (range (N + 1)).filter (fun n => n + D ≤ N), |c n| * u n ≤
      F / s ^ 13 * (A * x ^ 12) := by
    calc ∑ n ∈ (range (N + 1)).filter (fun n => n + D ≤ N), |c n| * u n
        ≤ ∑ n ∈ (range (N + 1)).filter (fun n => n + D ≤ N), |c n| * (F / s ^ 13) :=
          sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hfar n hn) (abs_nonneg _)
      _ ≤ ∑ n ∈ range (N + 1), |c n| * (F / s ^ 13) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun n _ _ => mul_nonneg (abs_nonneg _) (by positivity))
      _ = F / s ^ 13 * ∑ n ∈ range (N + 1), |c n| := by rw [← sum_mul]; ring
      _ ≤ F / s ^ 13 * (A * x ^ 12) := by gcongr
  -- the near part
  have hnear_sub : (range (N + 1)).filter (fun n => ¬ n + D ≤ N) ⊆ insert 0 (Ioc (N - D) N) := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_filter.1 hn
    rw [mem_range] at h1
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_Ioc.2 ⟨by omega, by omega⟩)
  have hnear_sum : ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n + D ≤ N), |c n| * u n ≤
      A₂ * x ^ 11 * (D + x ^ (1 - ηt)) := by
    calc ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n + D ≤ N), |c n| * u n
        ≤ ∑ n ∈ (range (N + 1)).filter (fun n => ¬ n + D ≤ N), |c n| := by
          refine sum_le_sum fun n hn => ?_
          have hn' : (n : ℝ) < x := by
            have := mem_range.1 (mem_filter.1 hn).1; rw [hxdef]; exact_mod_cast this
          have : u n ≤ 1 :=
            Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) hL.le)
          have := abs_nonneg (c n)
          nlinarith
      _ ≤ ∑ n ∈ insert 0 (Ioc (N - D) N), |c n| :=
          sum_le_sum_of_subset_of_nonneg hnear_sub (fun n _ _ => abs_nonneg _)
      _ = |c 0| + ∑ n ∈ Ioc (N - D) N, |c n| := by rw [sum_insert (by simp)]
      _ ≤ A₂ * x ^ 11 * (D + x ^ (1 - ηt)) := by rw [hc0, abs_zero, zero_add]; exact hS D
  have herr : |∑ n ∈ range (N + 1), c n * (u n * (2 - u n))| ≤
      2 * (F / s ^ 13 * (A * x ^ 12) + A₂ * x ^ 11 * (D + x ^ (1 - ηt))) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have e : ∀ n ∈ range (N + 1), |c n * (u n * (2 - u n))| ≤ 2 * (|c n| * u n) := by
      intro n hn
      have hn' : (n : ℝ) < x := by
        have := mem_range.1 hn; rw [hxdef]; exact_mod_cast this
      have hu1 : u n ≤ 1 :=
        Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) hL.le)
      have := hu0 n
      rw [abs_mul, abs_of_nonneg (show 0 ≤ u n * (2 - u n) by nlinarith)]
      have ha := abs_nonneg (c n)
      nlinarith [mul_nonneg ha (sq_nonneg (u n))]
    refine (sum_le_sum e).trans ?_
    rw [← mul_sum, ← sum_filter_add_sum_filter_not (range (N + 1)) (fun n => n + D ≤ N)]
    gcongr
  -- numerics
  have hs13 : s ^ 13 = x ^ ηt := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; unfold ηt; norm_num
  have hx12 : F / s ^ 13 * (A * x ^ 12) = F * A * x ^ (12 - ηt) := by
    rw [hs13]
    have : x ^ (12 - ηt) = x ^ 12 / x ^ ηt := by
      rw [Real.rpow_sub hx0]; norm_cast
    rw [this]; field_simp
  have hx11 : A₂ * x ^ 11 * (D + x ^ (1 - ηt)) ≤ 3 * A₂ * x ^ (12 - ηt) := by
    have h1 : (1 : ℝ) ≤ x ^ (1 - ηt) := Real.one_le_rpow hx1 (by linarith)
    have hD3 : (D : ℝ) + x ^ (1 - ηt) ≤ 3 * x ^ (1 - ηt) := by linarith
    have e : x ^ 11 * x ^ (1 - ηt) = x ^ (12 - ηt) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx0]; norm_num; ring_nf
    calc A₂ * x ^ 11 * (D + x ^ (1 - ηt)) ≤ A₂ * x ^ 11 * (3 * x ^ (1 - ηt)) := by gcongr
      _ = 3 * A₂ * (x ^ 11 * x ^ (1 - ηt)) := by ring
      _ = _ := by rw [e]
  rw [hdec]
  calc |(∑ n ∈ range (N + 1), c n * (1 - u n) ^ 2) +
        ∑ n ∈ range (N + 1), c n * (u n * (2 - u n))|
      ≤ |∑ n ∈ range (N + 1), c n * (1 - u n) ^ 2| +
          |∑ n ∈ range (N + 1), c n * (u n * (2 - u n))| := abs_add_le _ _
    _ ≤ Real.exp 1 * 48 * I2 * K * x ^ (12 - ηt) +
          2 * (F * A * x ^ (12 - ηt) + 3 * A₂ * x ^ (12 - ηt)) := by
        gcongr
        refine herr.trans ?_
        rw [hx12]; gcongr
    _ = _ := by ring

end RamanujanTau.SCS2Coprime
