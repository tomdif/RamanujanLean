/-
# The partition generating function on the unit disc

`F(q) = 1/(q;q)_∞` is holomorphic on `|q| < 1` and `F(q) = Σ p(n) qⁿ` there, with `p(n) = #(Nat.Partition n)`.
Proof: `F` has a Taylor expansion on the disc. Leibniz on `(q;q)_∞ · F = 1` gives its coefficients the same
recurrence as the formal inverse `1/(q;q)_∞`, whose coefficients are `p(n)`.
-/
import RamanujanTau.Realize
import RamanujanTau.MockTheta5PartitionCount

set_option autoImplicit false

namespace HardyRamanujan
open Complex Metric Realize Filter
open scoped Nat Topology

/-- `p(n)`, the number of partitions of `n`. -/
abbrev p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- `(q;q)_∞`. -/
noncomputable abbrev Pq (q : ℂ) : ℂ := Pfun 1 1 q

lemma Pq_ne_zero {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) : Pq q ≠ 0 := by
  rw [mem_ball_zero_iff] at hq
  have hs : Summable fun n : ℕ => ‖q‖ ^ (n + 1) :=
    (summable_geometric_of_lt_one (norm_nonneg _) hq).comp_injective (add_left_injective 1)
  refine tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -q ^ (1 + 1 * n)) (fun i => ?_) ?_
  · intro h
    have h1 : q ^ (1 + 1 * i) = 1 := by linear_combination -h
    have := congrArg norm h1
    rw [norm_pow, norm_one] at this
    have hlt : ‖q‖ ^ (1 + 1 * i) < 1 := pow_lt_one₀ (norm_nonneg _) hq (by omega)
    linarith
  · refine hs.congr fun n => ?_
    simp [norm_pow, add_comm]

/-- `F(q) = 1/(q;q)_∞`. -/
noncomputable def F (q : ℂ) : ℂ := (Pq q)⁻¹

/-- `[qⁱ](q;q)_∞`. -/
noncomputable abbrev a (i : ℕ) : ℂ := ((PowerSeries.coeff i (RankProof.Pinf 1 1) : ℤ) : ℂ)

lemma Pq_realizes : Realizes Pq (RankProof.Pinf 1 1) := realizes_Pinf 1 1 le_rfl le_rfl

lemma F_diff : DifferentiableOn ℂ F (ball 0 1) :=
  Pq_realizes.diff.inv fun _ hq => Pq_ne_zero hq

lemma contDiffAt_of_ball {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1)) (n : ℕ) :
    ContDiffAt ℂ n f 0 :=
  ((hf.analyticAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))).contDiffAt).of_le le_top

/-- the formal recurrence: `Σ_{i ≤ n} [qⁱ](q;q)_∞ · p(n − i) = [n = 0]`. -/
lemma formal_rec (n : ℕ) : ∑ i ∈ Finset.range (n + 1),
    a i * (p (n - i) : ℂ) = if n = 0 then 1 else 0 := by
  have h : RankProof.Pinf 1 1 * MockTheta5.JTP.partitionGF = 1 := by
    rw [RankProof.Pinf_one_one, MockTheta5.JTP.partitionGF, Ring.mul_inverse_cancel _ MockTheta5.JTP.isUnit_qfacInf]
  have hc := congrArg (PowerSeries.coeff n) h
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
    PowerSeries.coeff i (RankProof.Pinf 1 1) * PowerSeries.coeff j MockTheta5.JTP.partitionGF)] at hc
  simp only [MockTheta5.JTP.coeff_partitionGF_eq_card, PowerSeries.coeff_one] at hc
  have := congrArg (fun x : ℤ => (x : ℂ)) hc
  push_cast at this
  rw [this]
  try (split_ifs <;> simp)

/-- the analytic recurrence for `b_k = F^{(k)}(0)/k!`. -/
lemma analytic_rec (n : ℕ) : ∑ i ∈ Finset.range (n + 1),
    a i * (iteratedDeriv (n - i) F 0 / (n - i)!) =
      if n = 0 then 1 else 0 := by
  have h1 : (fun q => Pq q * F q) =ᶠ[𝓝 0] fun _ => (1 : ℂ) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (one_pos : (0 : ℝ) < 1))] with q hq
    exact mul_inv_cancel₀ (Pq_ne_zero hq)
  have hL := iteratedDeriv_fun_mul (contDiffAt_of_ball Pq_realizes.diff n) (contDiffAt_of_ball F_diff n)
    (𝕜 := ℂ) (x := 0)
  rw [h1.iteratedDeriv_eq, iteratedDeriv_const] at hL
  have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have key : ∑ i ∈ Finset.range (n + 1), a i *
      (iteratedDeriv (n - i) F 0 / (n - i)!) = (n ! : ℂ)⁻¹ * ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℂ) * iteratedDeriv i Pq 0 * iteratedDeriv (n - i) F 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [Pq_realizes.iteratedDeriv_zero i]
    have hi' : (((n - i)! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (n - i).factorial_ne_zero
    have hch : (n.choose i : ℂ) * (i ! : ℂ) * ((n - i)! : ℂ) = n ! := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega : i ≤ n)
    field_simp
    linear_combination (-(iteratedDeriv (n - i) F 0 * a i)) * hch
  rw [key, ← hL]
  split_ifs with h0
  · subst h0; simp
  · simp

lemma iteratedDeriv_F (n : ℕ) : iteratedDeriv n F 0 / n ! = p n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have ha := analytic_rec n
    have hf := formal_rec n
    rw [Finset.sum_range_succ'] at ha hf
    have hc0 : a 0 = 1 := by
      simp only [a, RankProof.Pinf_one_one, MockTheta5.JTP.coeff_zero_qfacInf, Int.cast_one]
    have hrest : ∑ i ∈ Finset.range n, a (i + 1) *
        (iteratedDeriv (n - (i + 1)) F 0 / (n - (i + 1))!) = ∑ i ∈ Finset.range n,
        a (i + 1) * (p (n - (i + 1)) : ℂ) :=
      Finset.sum_congr rfl fun i hi => by rw [ih _ (by rw [Finset.mem_range] at hi; omega)]
    rw [hrest] at ha
    simp only [hc0, Nat.sub_zero, one_mul] at ha hf
    linear_combination ha - hf

/-- **`F(q) = Σ p(n) qⁿ`** on the unit disc. -/
theorem hasSum_F {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) : HasSum (fun n => (p n : ℂ) * q ^ n) (F q) := by
  have H := Complex.hasSum_taylorSeries_on_ball F_diff hq
  convert H using 1
  funext n
  rw [sub_zero, smul_eq_mul, smul_eq_mul, ← iteratedDeriv_F n]
  have : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

end HardyRamanujan
