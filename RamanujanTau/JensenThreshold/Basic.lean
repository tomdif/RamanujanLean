/-
# Jensen polynomials of the partition function: definitions and the two root-counting certificates

* `jensen d n = Σ_{j=0}^{d} C(d,j) p(n+j) X^j ∈ ℝ[X]`, with `p(m) = #(Nat.Partition m)`.
* `Hyperbolic P` : all roots of `P` are real, counted with multiplicity (`card P.roots = natDegree P`).
* `hyperbolic_of_alternating` : `d + 1` increasing points with alternating signs force `d` distinct real roots.
* `laguerre_of_hyperbolic` : a real-rooted `P` of degree `d` satisfies Laguerre's inequality
  `(d−1)·P'(x)² ≥ d·P(x)·P''(x)` for every real `x`. A single rational `x₀` violating it certifies that `P`
  is not hyperbolic.
* `scaled_eval`, `scaled_eval_derivative`, `scaled_eval_derivative2` : the values at `x = −u/v`, times `vᵈ`,
  `vᵈ⁻¹`, `vᵈ⁻²`, are integer sums, so both certificates reduce to integer arithmetic.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace JensenThreshold
open Polynomial

/-- `p(m) = #(Nat.Partition m)` (definitionally `HardyRamanujan.p`). -/
abbrev pc (m : ℕ) : ℕ := Fintype.card (Nat.Partition m)

/-- The degree-`d` shift-`n` Jensen polynomial of the partition function. -/
noncomputable def jensen (d n : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) * (pc (n + j) : ℝ)) * X ^ j

/-- All roots real (with multiplicity). -/
def Hyperbolic (P : ℝ[X]) : Prop := Multiset.card P.roots = P.natDegree

/-- The (named) tail statement: `J^{d,n}` is hyperbolic for every `n ≥ n₀`. -/
def JensenTail (d n₀ : ℕ) : Prop := ∀ n, n₀ ≤ n → Hyperbolic (jensen d n)

lemma pc_pos (m : ℕ) : 0 < pc m := Fintype.card_pos

lemma natDegree_jensen_le (d n : ℕ) : (jensen d n).natDegree ≤ d := by
  unfold jensen
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_C_mul_X_pow_le _ _).trans (by simp at hj; omega)

lemma coeff_jensen (d n k : ℕ) :
    (jensen d n).coeff k = if k < d + 1 then (d.choose k : ℝ) * pc (n + k) else 0 := by
  unfold jensen
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single k]
  · by_cases hk : k < d + 1
    · simp [hk]
    · simp [hk, Nat.choose_eq_zero_of_lt (by omega : d < k)]
  · intro b _ hb; simp [Ne.symm hb]
  · intro hk; simp only [Finset.mem_range] at hk; simp [hk, Nat.choose_eq_zero_of_lt (by omega : d < k)]

lemma natDegree_jensen (d n : ℕ) : (jensen d n).natDegree = d := by
  apply le_antisymm (natDegree_jensen_le d n)
  apply le_natDegree_of_ne_zero
  rw [coeff_jensen, if_pos (by omega), Nat.choose_self, Nat.cast_one, one_mul]
  exact_mod_cast (pc_pos _).ne'

lemma eval_jensen (d n : ℕ) (x : ℝ) :
    (jensen d n).eval x = ∑ j ∈ Finset.range (d + 1), (d.choose j : ℝ) * pc (n + j) * x ^ j := by
  simp [jensen, eval_finsetSum]

lemma eval_derivative_jensen (d n : ℕ) (x : ℝ) :
    (derivative (jensen d n)).eval x =
      ∑ j ∈ Finset.range (d + 1), (d.choose j : ℝ) * pc (n + j) * j * x ^ (j - 1) := by
  simp only [jensen, derivative_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [derivative_C_mul_X_pow, eval_C_mul, eval_X_pow]

lemma eval_derivative2_jensen (d n : ℕ) (x : ℝ) :
    (derivative (derivative (jensen d n))).eval x =
      ∑ j ∈ Finset.range (d + 1), (d.choose j : ℝ) * pc (n + j) * j * ((j - 1 : ℕ) : ℝ) * x ^ (j - 1 - 1) := by
  simp only [jensen, derivative_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [derivative_C_mul_X_pow, derivative_C_mul_X_pow, eval_C_mul, eval_X_pow]

/-! ## Scaled evaluation at `x = −u/v` -/

lemma pow_div_scale {u v : ℝ} (hv : v ≠ 0) {j e : ℕ} :
    v ^ (j + e) * (-(u / v)) ^ j = (-u) ^ j * v ^ e := by
  rw [show -(u / v) = (-u) / v by ring, div_pow, pow_add]; field_simp

lemma scaled_eval (d n u v : ℕ) (hv : 0 < v) :
    (v : ℝ) ^ d * (jensen d n).eval (-((u : ℝ) / v)) =
      ∑ j ∈ Finset.range (d + 1), (d.choose j : ℝ) * pc (n + j) * (-(u : ℝ)) ^ j * (v : ℝ) ^ (d - j) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [eval_jensen, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  have := pow_div_scale (u := u) hv' (j := j) (e := d - j)
  rw [show j + (d - j) = d by omega] at this
  calc (v : ℝ) ^ d * ((d.choose j : ℝ) * pc (n + j) * (-((u : ℝ) / v)) ^ j)
      = (d.choose j : ℝ) * pc (n + j) * ((v : ℝ) ^ d * (-((u : ℝ) / v)) ^ j) := by ring
    _ = _ := by rw [this]; ring

lemma scaled_eval_derivative (d n u v : ℕ) (hv : 0 < v) :
    (v : ℝ) ^ (d - 1) * (derivative (jensen d n)).eval (-((u : ℝ) / v)) =
      ∑ j ∈ Finset.range (d + 1),
        (d.choose j : ℝ) * pc (n + j) * j * (-(u : ℝ)) ^ (j - 1) * (v : ℝ) ^ (d - j) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [eval_derivative_jensen, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  have := pow_div_scale (u := u) hv' (j := j - 1) (e := d - j)
  rw [show j - 1 + (d - j) = d - 1 by omega] at this
  calc (v : ℝ) ^ (d - 1) * ((d.choose j : ℝ) * pc (n + j) * j * (-((u : ℝ) / v)) ^ (j - 1))
      = (d.choose j : ℝ) * pc (n + j) * j * ((v : ℝ) ^ (d - 1) * (-((u : ℝ) / v)) ^ (j - 1)) := by ring
    _ = _ := by rw [this]; ring

lemma scaled_eval_derivative2 (d n u v : ℕ) (hv : 0 < v) :
    (v : ℝ) ^ (d - 2) * (derivative (derivative (jensen d n))).eval (-((u : ℝ) / v)) =
      ∑ j ∈ Finset.range (d + 1),
        (d.choose j : ℝ) * pc (n + j) * j * ((j - 1 : ℕ) : ℝ) * (-(u : ℝ)) ^ (j - 2) * (v : ℝ) ^ (d - j) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [eval_derivative2_jensen, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · interval_cases j <;> simp
  have := pow_div_scale (u := u) hv' (j := j - 2) (e := d - j)
  rw [show j - 2 + (d - j) = d - 2 by omega] at this
  rw [show j - 1 - 1 = j - 2 by omega]
  calc (v : ℝ) ^ (d - 2) * ((d.choose j : ℝ) * pc (n + j) * j * ((j - 1 : ℕ) : ℝ) * (-((u : ℝ) / v)) ^ (j - 2))
      = (d.choose j : ℝ) * pc (n + j) * j * ((j - 1 : ℕ) : ℝ) *
          ((v : ℝ) ^ (d - 2) * (-((u : ℝ) / v)) ^ (j - 2)) := by ring
    _ = _ := by rw [this]; ring

/-! ## Sign alternation ⟹ hyperbolic -/

lemma le_of_strict_chain {d : ℕ} {x : ℕ → ℝ} (h : ∀ i < d, x i < x (i + 1)) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ d) : x i ≤ x j := by
  induction j with
  | zero => obtain rfl : i = 0 := by omega
            exact le_rfl
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · exact (ih (by omega) (by omega)).trans (h j (by omega)).le

theorem hyperbolic_of_alternating (P : ℝ[X]) (d : ℕ) (hdeg : P.natDegree ≤ d) (x : ℕ → ℝ)
    (hmono : ∀ i < d, x i < x (i + 1)) (hsign : ∀ i < d, P.eval (x i) * P.eval (x (i + 1)) < 0) :
    Hyperbolic P := by
  have hroot : ∀ i : Fin d, ∃ r ∈ Set.Ioo (x i) (x (i + 1)), P.eval r = 0 := by
    intro i
    have hs := hsign i i.2
    have hab := (hmono i i.2).le
    have hc : ContinuousOn (fun t => P.eval t) (Set.Icc (x i) (x (i + 1))) :=
      P.continuous.continuousOn
    rcases lt_or_gt_of_ne (show P.eval (x i) ≠ 0 by intro h0; rw [h0, zero_mul] at hs; exact lt_irrefl _ hs)
      with hneg | hpos
    · have hp : 0 < P.eval (x (i + 1)) := by nlinarith
      obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo hab hc ⟨hneg, hp⟩
      exact ⟨r, hr, hr0⟩
    · have hn : P.eval (x (i + 1)) < 0 := by nlinarith
      obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo' hab hc ⟨hn, hpos⟩
      exact ⟨r, hr, hr0⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact le_antisymm (card_roots' P) (by omega)
  choose r hr hr0 using hroot
  have hP0 : P ≠ 0 := by
    rintro rfl
    have := hsign 0 hd; simp at this
  have hrmono : StrictMono r := by
    intro i j hij
    have h1 := (hr i).2
    have h2 := (hr j).1
    have hij' : (i : ℕ) < j := hij
    have : x (i + 1) ≤ x j := le_of_strict_chain hmono (by omega) j.2.le
    linarith
  have hsub : Finset.univ.image r ⊆ P.roots.toFinset := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    rw [Multiset.mem_toFinset, mem_roots hP0]
    exact hr0 i
  have hcard : d ≤ Multiset.card P.roots := by
    calc d = (Finset.univ.image r).card := by
            rw [Finset.card_image_of_injective _ hrmono.injective]; simp
      _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
  exact le_antisymm (card_roots' P) (hdeg.trans hcard)

/-! ## Laguerre's inequality for real-rooted polynomials -/

lemma laguerre_prod (s : Multiset ℝ) (x : ℝ) :
    ((Multiset.card s : ℝ) - 1) * ((derivative (s.map fun a => X - C a).prod).eval x) ^ 2 ≥
      (Multiset.card s : ℝ) * (s.map fun a => X - C a).prod.eval x *
        (derivative (derivative (s.map fun a => X - C a).prod)).eval x := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one,
      derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, derivative_one,
      zero_mul, zero_add, eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_one] at ih ⊢
    set Q := (s.map fun a => X - C a).prod
    set q := Q.eval x
    set q1 := (derivative Q).eval x
    set q2 := (derivative (derivative Q)).eval x
    set e := (Multiset.card s : ℝ)
    set y := x - a
    rcases Multiset.empty_or_exists_mem s with hs | ⟨b, hb⟩
    · subst hs
      simp [Q, q, q1, q2, e]
    have he : 1 ≤ e := by
      have : 1 ≤ Multiset.card s := Multiset.card_pos_iff_exists_mem.mpr ⟨b, hb⟩
      simp only [e]; exact_mod_cast this
    have gap : 0 ≤ (e - 1) * q1 ^ 2 - e * q * q2 := by linarith
    have key : e * ((e + 1 - 1) * (q + y * q1) ^ 2 - (e + 1) * (y * q) * (q1 + (q1 + y * q2))) =
        (e * q - y * q1) ^ 2 + (e + 1) * y ^ 2 * ((e - 1) * q1 ^ 2 - e * q * q2) := by ring
    have h0 : 0 ≤ (e * q - y * q1) ^ 2 + (e + 1) * y ^ 2 * ((e - 1) * q1 ^ 2 - e * q * q2) := by
      have : 0 ≤ (e + 1) * y ^ 2 := by positivity
      nlinarith [sq_nonneg (e * q - y * q1), mul_nonneg this gap]
    have : 0 ≤ (e + 1 - 1) * (q + y * q1) ^ 2 - (e + 1) * (y * q) * (q1 + (q1 + y * q2)) := by
      by_contra hneg
      push Not at hneg
      have : e * ((e + 1 - 1) * (q + y * q1) ^ 2 - (e + 1) * (y * q) * (q1 + (q1 + y * q2))) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) hneg
      linarith
    linarith

theorem laguerre_of_hyperbolic (P : ℝ[X]) (h : Hyperbolic P) (x : ℝ) :
    ((P.natDegree : ℝ) - 1) * ((derivative P).eval x) ^ 2 ≥
      (P.natDegree : ℝ) * P.eval x * (derivative (derivative P)).eval x := by
  have hP := C_leadingCoeff_mul_prod_multiset_X_sub_C h
  have hl := laguerre_prod P.roots x
  rw [h] at hl
  set Q := (P.roots.map fun a => X - C a).prod
  set c := P.leadingCoeff
  have h0 : P.eval x = c * Q.eval x := by
    conv_lhs => rw [← hP]
    simp
  have h1 : (derivative P).eval x = c * (derivative Q).eval x := by
    conv_lhs => rw [← hP]
    simp
  have h2 : (derivative (derivative P)).eval x = c * (derivative (derivative Q)).eval x := by
    conv_lhs => rw [← hP]
    simp
  rw [h0, h1, h2]
  have hc : 0 ≤ c ^ 2 := sq_nonneg c
  nlinarith [mul_le_mul_of_nonneg_left hl hc]

/-- A Laguerre violation at one point certifies non-hyperbolicity. -/
theorem not_hyperbolic_of_laguerre (P : ℝ[X]) (x : ℝ)
    (hx : ((P.natDegree : ℝ) - 1) * ((derivative P).eval x) ^ 2 <
      (P.natDegree : ℝ) * P.eval x * (derivative (derivative P)).eval x) : ¬ Hyperbolic P :=
  fun h => absurd (laguerre_of_hyperbolic P h x) (not_le.mpr hx)

end JensenThreshold
