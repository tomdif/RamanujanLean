import RamanujanTau.ThetaLift.HermiteBounds

/-!
# The integral in `v`

The integral of the Hermite term against `v^(λ-3/2)` is an exponential. It vanishes when `x` and `g` have
opposite signs, which is what makes the lift holomorphic.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Polynomial MeasureTheory Set
open scoped Real

noncomputable section

/-- The real Appell expansion. -/
lemma ev_appell (n : ℕ) (s t : ℝ) :
    ev (hermite n) (s + t) = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * t ^ (n - k) * ev (hermite k) s := by
  have h := hermite_appell n (s : ℂ) (t : ℂ)
  have hc : ∀ (m : ℕ) (r : ℝ), aeval (r : ℂ) (hermite m) = ((ev (hermite m) r : ℝ) : ℂ) := by
    intro m r
    unfold ev
    exact Polynomial.aeval_algHom_apply (Complex.ofRealAm.restrictScalars ℤ) r (hermite m)
  have e : (s : ℂ) + t = ((s + t : ℝ) : ℂ) := by push_cast; rfl
  rw [e, hc] at h
  simp only [hc] at h
  exact_mod_cast h

/-- The `v`-integrand. -/
def vTerm (lam : ℕ) (ε g m y v : ℝ) : ℝ :=
  v ^ ((lam : ℝ) - 3 / 2) * Real.exp (-(6 * π * g ^ 2 * y ^ 2 / v) - π * m ^ 2 * v / 6) *
    (√(3 / (π * v)) ^ lam *
      ev (hermite lam) ((ε * m + 6 * g * y / v) / √(3 / (π * v))))

/-- The parts of `vTerm`. -/
def vPart (n : ℕ) (ε α c v : ℝ) : ℝ :=
  v ^ (((n : ℝ) - 3) / 2) *
    (Real.exp (-(c ^ 2 / (2 * (α * v))) - α * v / 2) * ev (hermite n) (ε * √(α * v)))

lemma integrable_vPart (n : ℕ) {ε α c : ℝ} (hε : ε = 1 ∨ ε = -1) (hα : 0 < α) (hc : 0 < c) :
    IntegrableOn (vPart n ε α c) (Ioi 0) := by
  obtain ⟨C, hC0, hC⟩ := ev_gauss_bound (hermite n)
  have hβ : 0 < c ^ 2 / (2 * α) := by positivity
  have hγ : 0 < 7 * α / 16 := by positivity
  have hI := (integrableOn_rpow_exp (((n : ℝ) - 3) / 2) hβ hγ).const_mul C
  refine Integrable.mono' hI ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro v hv
    have hv' : v ≠ 0 := (mem_Ioi.mp hv).ne'
    apply ContinuousAt.continuousWithinAt
    have hP : Continuous (ev (hermite n)) :=
      continuous_iff_continuousAt.mpr fun x => (hasDerivAt_ev _ x).continuousAt
    unfold vPart
    refine ContinuousAt.mul ?_ (ContinuousAt.mul ?_ ?_)
    · exact Real.continuousAt_rpow_const _ _ (Or.inl hv')
    · fun_prop (disch := simp [hv', hα.ne'])
    · exact hP.continuousAt.comp (by fun_prop)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv' : 0 < v := hv
    have hb := hC (ε * √(α * v))
    have hsq : (ε * √(α * v)) ^ 2 = α * v := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      rcases hε with rfl | rfl <;> norm_num
    rw [hsq] at hb
    unfold vPart
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_eq_abs]
    have hp : 0 ≤ v ^ (((n : ℝ) - 3) / 2) := by positivity
    calc _ ≤ v ^ (((n : ℝ) - 3) / 2) * (Real.exp (-(c ^ 2 / (2 * (α * v))) - α * v / 2) *
          (C * Real.exp (α * v / 16))) := by gcongr
      _ = C * (v ^ (((n : ℝ) - 3) / 2) * Real.exp (-(c ^ 2 / (2 * α) / v) - 7 * α / 16 * v)) := by
        have e : -(c ^ 2 / (2 * α) / v) - 7 * α / 16 * v =
            -(c ^ 2 / (2 * (α * v))) - α * v / 2 + α * v / 16 := by
          field_simp
          ring
        rw [e, Real.exp_add]
        ring

/-- The power of `v` in a part. -/
lemma power_part (n k : ℕ) {A g y v : ℝ} (hA : 0 < A) (hy : 0 < y) (hv : 0 < v) :
    v ^ (((n + k : ℕ) : ℝ) - 3 / 2) * ((A * v ^ (-(1 / 2 : ℝ))) ^ (n + k) *
        (6 * g * y / A * v ^ (-(1 / 2 : ℝ))) ^ k) =
      y ^ (n + k) * ((6 * g) ^ k * (A / y) ^ n * v ^ (((n : ℝ) - 3) / 2)) := by
  have hs : ∀ m : ℕ, (v ^ (-(1 / 2 : ℝ))) ^ m = v ^ (-((m : ℝ) / 2)) := by
    intro m
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv.le]
    congr 1
    ring
  have h1 : (A * v ^ (-(1 / 2 : ℝ))) ^ (n + k) * (6 * g * y / A * v ^ (-(1 / 2 : ℝ))) ^ k =
      A ^ n * (6 * g * y) ^ k * (v ^ (-(1 / 2 : ℝ))) ^ (n + 2 * k) := by
    rw [mul_pow, mul_pow, div_pow, pow_add A, show n + 2 * k = (n + k) + k by ring,
      pow_add (v ^ (-(1 / 2 : ℝ))) (n + k) k]
    field_simp
  rw [h1, hs]
  have h2 : v ^ (((n + k : ℕ) : ℝ) - 3 / 2) * v ^ (-(((n + 2 * k : ℕ) : ℝ) / 2)) =
      v ^ (((n : ℝ) - 3) / 2) := by
    rw [← Real.rpow_add hv]
    congr 1
    push_cast
    ring
  calc _ = A ^ n * (6 * g * y) ^ k * (v ^ (((n + k : ℕ) : ℝ) - 3 / 2) *
        v ^ (-(((n + 2 * k : ℕ) : ℝ) / 2))) := by ring
    _ = _ := by
      rw [h2, div_pow, mul_pow (6 * g) y k, pow_add y]
      field_simp

/-- `vTerm` as a finite sum of parts. -/
lemma vTerm_eq (lam : ℕ) {ε g m y v : ℝ} (hε : ε = 1 ∨ ε = -1) (hg : 0 < g) (hm : 0 < m) (hy : 0 < y)
    (hv : 0 < v) :
    vTerm lam ε g m y v = y ^ lam * ∑ n ∈ Finset.range (lam + 1),
      (lam.choose n : ℝ) * (6 * g) ^ (lam - n) * (√(3 / π) / y) ^ n *
        vPart n ε (π * m ^ 2 / 3) (2 * π * y * g * m) v := by
  have hπ := Real.pi_pos
  set A := √(3 / π) with hA
  have hApos : 0 < A := Real.sqrt_pos.mpr (by positivity)
  set q := v ^ (-(1 / 2 : ℝ)) with hq
  have hqpos : 0 < q := by positivity
  have hq2 : q * q * v = 1 := by
    rw [hq, ← Real.rpow_add hv]
    have : (-(1 / 2 : ℝ) + -(1 / 2 : ℝ)) = -1 := by norm_num
    rw [this, Real.rpow_neg_one]
    field_simp
  have hr : √(3 / (π * v)) = A * q := by
    have h1 : 3 / (π * v) = 3 / π * v⁻¹ := by field_simp
    rw [h1, Real.sqrt_mul (by positivity), ← hA, Real.sqrt_inv, hq, Real.sqrt_eq_rpow v,
      Real.rpow_neg hv.le]
  have hα : √(π * m ^ 2 / 3 * v) = m / (A * q) := by
    have h1 : π * m ^ 2 / 3 * v = m ^ 2 * (3 / (π * v))⁻¹ := by field_simp
    rw [← hr, h1, Real.sqrt_mul (by positivity), Real.sqrt_sq hm.le, Real.sqrt_inv]
    exact (div_eq_mul_inv _ _).symm
  have harg : (ε * m + 6 * g * y / v) / (A * q) = ε * (m / (A * q)) + 6 * g * y / A * q := by
    have hv1 : 1 / v = q * q := by
      field_simp
      linarith
    have : 6 * g * y / v = 6 * g * y * (q * q) := by
      rw [← hv1]
      ring
    rw [this]
    field_simp
  have hexp : ∀ n : ℕ, Real.exp (-(6 * π * g ^ 2 * y ^ 2 / v) - π * m ^ 2 * v / 6) =
      Real.exp (-((2 * π * y * g * m) ^ 2 / (2 * (π * m ^ 2 / 3 * v))) - π * m ^ 2 / 3 * v / 2) := by
    intro _
    congr 1
    field_simp
    ring
  unfold vTerm
  rw [hr, harg, ev_appell, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨k, rfl⟩ : ∃ k, lam = n + k := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  have hsub : n + k - n = k := by omega
  have hp := power_part n k (g := g) hApos hy hv
  unfold vPart
  rw [hsub, hexp n, hα]
  calc _ = ((n + k).choose n : ℝ) * (Real.exp (-((2 * π * y * g * m) ^ 2 / (2 * (π * m ^ 2 / 3 * v))) -
          π * m ^ 2 / 3 * v / 2) * ev (hermite n) (ε * (m / (A * q)))) *
        (v ^ (((n + k : ℕ) : ℝ) - 3 / 2) * ((A * q) ^ (n + k) * (6 * g * y / A * q) ^ k)) := by
        push_cast
        ring
    _ = _ := by
      rw [hp]
      ring

/-- **The integral in `v`.** -/
theorem vTerm_integral (lam : ℕ) {ε g m y : ℝ} (hε : ε = 1 ∨ ε = -1) (hg : 0 < g) (hm : 0 < m)
    (hy : 0 < y) :
    ∫ v in Ioi (0 : ℝ), vTerm lam ε g m y v =
      (1 + ε) ^ lam * (6 * g) ^ lam * y ^ lam * ((√6 * y * g)⁻¹ * Real.exp (-(2 * π * y * g * m))) := by
  have hπ := Real.pi_pos
  have hα : 0 < π * m ^ 2 / 3 := by positivity
  have hc : 0 < 2 * π * y * g * m := by positivity
  have hcongr : ∫ v in Ioi (0 : ℝ), vTerm lam ε g m y v = ∫ v in Ioi (0 : ℝ), y ^ lam *
      ∑ n ∈ Finset.range (lam + 1), (lam.choose n : ℝ) * (6 * g) ^ (lam - n) * (√(3 / π) / y) ^ n *
        vPart n ε (π * m ^ 2 / 3) (2 * π * y * g * m) v :=
    setIntegral_congr_fun measurableSet_Ioi fun v hv => vTerm_eq lam hε hg hm hy hv
  rw [hcongr, integral_const_mul, integral_finsetSum]
  · simp only [integral_const_mul]
    have hk := kernel_sum lam ε hε hg hm hy
    have hval : (π * m ^ 2 / 3) ^ ((3 : ℝ) / 2) * (2 / (π * m ^ 2 / 3)) *
        (√(π / (1 / 2)) / 2) * (2 * π * y * g * m)⁻¹ = (√6 * y * g)⁻¹ := by
      have hg' := hg
      have hA3 : (π * m ^ 2 / 3) ^ ((3 : ℝ) / 2) = (π * m ^ 2 / 3) * √(π * m ^ 2 / 3) := by
        rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hα,
          Real.rpow_one]
      have hsα : √(π * m ^ 2 / 3) = √(π / 3) * m := by
        rw [show π * m ^ 2 / 3 = π / 3 * m ^ 2 by ring, Real.sqrt_mul (by positivity),
          Real.sqrt_sq hm.le]
      set a := √(π / 3) with ha
      set b := √(π / (1 / 2)) with hb
      set d := √6 with hd
      have ha0 : 0 < a := Real.sqrt_pos.mpr (by positivity)
      have hb0 : 0 < b := Real.sqrt_pos.mpr (by positivity)
      have hd0 : 0 < d := Real.sqrt_pos.mpr (by norm_num)
      have ha2 : a ^ 2 = π / 3 := Real.sq_sqrt (by positivity)
      have hb2 : b ^ 2 = π / (1 / 2) := Real.sq_sqrt (by positivity)
      have hd2 : d ^ 2 = 6 := Real.sq_sqrt (by norm_num)
      have habd : a * b * d = 2 * π := by
        have h1 : (a * b * d) ^ 2 = (2 * π) ^ 2 := by
          rw [mul_pow, mul_pow, ha2, hb2, hd2]
          field_simp
          norm_num
        exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num)).mp h1
      rw [hA3, hsα]
      field_simp
      nlinarith [habd]
    have hk' : ∑ n ∈ Finset.range (lam + 1), (lam.choose n : ℝ) * (6 * g) ^ (lam - n) *
        (√(3 / π) / y) ^ n * ∫ v in Ioi (0 : ℝ), vPart n ε (π * m ^ 2 / 3) (2 * π * y * g * m) v =
        (1 + ε) ^ lam * (6 * g) ^ lam * (((π * m ^ 2 / 3) ^ ((3 : ℝ) / 2) * (2 / (π * m ^ 2 / 3)) *
          (√(π / (1 / 2)) / 2) * (2 * π * y * g * m)⁻¹) * Real.exp (-(2 * π * y * g * m))) := hk
    rw [hk', hval]
    ring
  · intro n _
    exact (integrable_vPart n hε hα hc).const_mul _

end

end RamanujanTau.ThetaLift
