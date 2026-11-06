/-
# Averaged mean value of a real Dirichlet polynomial

For real coefficients `c`, `P(t) = ∑_{n≤N} cₙ n^{-it}` and `G(u) = ∫₀ᵘ |P|²`:

    |∫_a^b G(u) du − (b²−a²)/2 · ∑ cₙ²| ≤ ∑_{m≠n} |c_m c_n| · 2/(log n − log m)².

Averaging the primitive over `u` turns the off-diagonal factor `sin(λu)/λ` (size up to `u`) into
`(cos λa − cos λb)/λ²`, which is `O(1/λ²)`. This is the only cancellation used.
-/
import RamanujanTau.MeanSquare.Poly

set_option autoImplicit false

namespace RamanujanTau.ZetaCritical

open Complex MeasureTheory Set Filter Topology Finset
open RamanujanTau.MeanSquare (dpoly ex normSq_dpoly continuous_dpoly)

/-- `|P(t)|² = ∑_{m,n} c_m c_n cos((log n − log m) t)` for real coefficients. -/
lemma normSq_dpoly_real (c : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    ‖dpoly (fun n => (c n : ℂ)) N t‖ ^ 2 = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      c m * c n * Real.cos ((Real.log n - Real.log m) * t) := by
  have h := congrArg Complex.re (normSq_dpoly (fun n => (c n : ℂ)) N t)
  rw [Complex.ofReal_re] at h
  rw [h, Complex.re_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [Complex.re_sum]
  refine sum_congr rfl fun n _ => ?_
  simp only [Complex.conj_ofReal, ex]
  rw [← Complex.ofReal_mul, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- The primitive `S(λ,u) = ∫₀ᵘ cos(λt) dt`. -/
noncomputable def Sc (l u : ℝ) : ℝ := ∫ t in (0 : ℝ)..u, Real.cos (l * t)

lemma continuous_Sc (l : ℝ) : Continuous (Sc l) := by
  unfold Sc
  exact intervalIntegral.continuous_primitive
    (fun _ _ => (by fun_prop : Continuous fun t : ℝ => Real.cos (l * t)).intervalIntegrable _ _) 0

lemma Sc_zero (u : ℝ) : Sc 0 u = u := by simp [Sc]

lemma Sc_ne {l : ℝ} (hl : l ≠ 0) (u : ℝ) : Sc l u = Real.sin (l * u) / l := by
  unfold Sc
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hl, integral_cos]
  simp only [mul_zero, Real.sin_zero, sub_zero, smul_eq_mul]
  field_simp

/-- `∫_a^b S(0,u) du = (b²−a²)/2`. -/
lemma int_Sc_zero (a b : ℝ) : ∫ u in a..b, Sc 0 u = (b ^ 2 - a ^ 2) / 2 := by
  simp only [Sc_zero]; exact integral_id

/-- `|∫_a^b S(λ,u) du| ≤ 2/λ²` for `λ ≠ 0`. -/
lemma abs_int_Sc_le {l : ℝ} (hl : l ≠ 0) (a b : ℝ) : |∫ u in a..b, Sc l u| ≤ 2 / l ^ 2 := by
  have e : ∫ u in a..b, Sc l u = (Real.cos (l * a) - Real.cos (l * b)) / l ^ 2 := by
    simp only [Sc_ne hl]
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hl, integral_sin]
    simp only [smul_eq_mul]
    field_simp
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < l ^ 2)]
  gcongr
  have h1 := Real.abs_cos_le_one (l * a)
  have h2 := Real.abs_cos_le_one (l * b)
  calc |Real.cos (l * a) - Real.cos (l * b)| ≤ |Real.cos (l * a)| + |Real.cos (l * b)| :=
        abs_sub _ _
    _ ≤ 2 := by linarith

/-- The primitive of `|P|²` as a double sum of `S`. -/
lemma primitive_eq (c : ℕ → ℝ) (N : ℕ) (u : ℝ) :
    ∫ t in (0 : ℝ)..u, ‖dpoly (fun n => (c n : ℂ)) N t‖ ^ 2 =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m * c n * Sc (Real.log n - Real.log m) u := by
  simp_rw [normSq_dpoly_real]
  have hc : ∀ l : ℝ, IntervalIntegrable (fun t : ℝ => Real.cos (l * t)) volume 0 u :=
    fun l => (by fun_prop : Continuous fun t : ℝ => Real.cos (l * t)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum (μ := volume) (fun m _ => ?_)]
  · refine sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_finsetSum (fun n _ => (hc _).const_mul _)]
    refine sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_const_mul]; rfl
  · refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_finsetSum _ fun n _ => continuous_const.mul (by fun_prop)

/-- The primitive is continuous. -/
lemma continuous_primitive_P (c : ℕ → ℝ) (N : ℕ) :
    Continuous fun u => ∫ t in (0 : ℝ)..u, ‖dpoly (fun n => (c n : ℂ)) N t‖ ^ 2 :=
  intervalIntegral.continuous_primitive (μ := volume)
    (fun _ _ => ((continuous_dpoly _ N).norm.pow 2).intervalIntegrable _ _) 0

/-- **Averaged mean value.** -/
theorem avg_mv (c : ℕ → ℝ) (N : ℕ) (a b : ℝ) :
    |(∫ u in a..b, ∫ t in (0 : ℝ)..u, ‖dpoly (fun n => (c n : ℂ)) N t‖ ^ 2) -
        (b ^ 2 - a ^ 2) / 2 * ∑ n ∈ Icc 1 N, c n ^ 2| ≤
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (if n = m then 0 else |c m * c n| * (2 / (Real.log n - Real.log m) ^ 2)) := by
  set S := Finset.Icc 1 N with hS
  simp_rw [primitive_eq]
  have hi : ∀ l : ℝ, IntervalIntegrable (Sc l) volume a b :=
    fun l => (continuous_Sc l).intervalIntegrable _ _
  have hI : ∫ u in a..b, ∑ m ∈ S, ∑ n ∈ S, c m * c n * Sc (Real.log n - Real.log m) u =
      ∑ m ∈ S, ∑ n ∈ S, c m * c n * ∫ u in a..b, Sc (Real.log n - Real.log m) u := by
    rw [intervalIntegral.integral_finsetSum (μ := volume) (fun m _ => ?_)]
    · refine sum_congr rfl fun m _ => ?_
      rw [intervalIntegral.integral_finsetSum (fun n _ => (hi _).const_mul _)]
      refine sum_congr rfl fun n _ => ?_
      rw [intervalIntegral.integral_const_mul]
    · refine Continuous.intervalIntegrable ?_ _ _
      exact continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_Sc _)
  rw [hI]
  set F : ℕ → ℕ → ℝ := fun m n => c m * c n * ∫ u in a..b, Sc (Real.log n - Real.log m) u
    with hF
  have hdiag : ∀ m ∈ S, F m m = (b ^ 2 - a ^ 2) / 2 * c m ^ 2 := by
    intro m _
    simp only [hF, sub_self, int_Sc_zero]; ring
  have hsplit : ∀ m ∈ S, ∑ n ∈ S, F m n = F m m + ∑ n ∈ S, (if n = m then 0 else F m n) := by
    intro m hm
    rw [← sum_erase_add S _ hm, add_comm]
    congr 1
    rw [← sum_erase_add S _ hm]
    simp only [if_true, add_zero]
    refine sum_congr rfl fun n hn => ?_
    rw [if_neg (ne_of_mem_erase hn)]
  have hdiff : ∑ m ∈ S, ∑ n ∈ S, F m n - (b ^ 2 - a ^ 2) / 2 * ∑ n ∈ S, c n ^ 2 =
      ∑ m ∈ S, ∑ n ∈ S, (if n = m then 0 else F m n) := by
    rw [sum_congr rfl hsplit, sum_add_distrib, sum_congr rfl hdiag, ← mul_sum]; ring
  rw [hdiff]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
  by_cases hnm : n = m
  · simp [hnm]
  · simp only [hnm, if_false, hF]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.1 hm).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.1 hn).1
    have hl : Real.log n - Real.log m ≠ 0 := by
      intro h
      have : Real.log n = Real.log m := by linarith
      have := Real.log_injOn_pos (Set.mem_Ioi.2 hn0) (Set.mem_Ioi.2 hm0) this
      exact hnm (by exact_mod_cast this)
    rw [abs_mul]
    gcongr
    exact abs_int_Sc_le hl a b

end RamanujanTau.ZetaCritical
