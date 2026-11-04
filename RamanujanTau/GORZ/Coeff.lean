/-
# Coefficientwise convergence of the renormalized Jensen polynomials to the Hermite polynomial

`Jhat d n = (Mmain(n) δ^d)⁻¹ · J^{d,n}(e^{−A}(δX − 1)) ∈ ℝ[X]`. **`tendsto_coeff_Jhat`** : for every `i`,
`coeff_i (Jhat d n) → coeff_i (H d)` as `n → ∞`, where `H d = H_d(X/2)` (physicists' Hermite). This is the
GORZ Theorem 1 statement for `p(n)` in its polynomial form.
-/
import RamanujanTau.GORZ.Limit

set_option autoImplicit false

namespace GORZ

open Real Finset Filter Topology Polynomial JensenThreshold JensenThreshold.Tail Rademacher

/-- the renormalized Jensen polynomial `Ĵ^{d,n}(X) = J^{d,n}(e^{−A}(δX−1)) / (Mmain(n) δ^d)`. -/
noncomputable def Jhat (d n : ℕ) : ℝ[X] :=
  C ((Mmain n * δv (uk 1 n) ^ d)⁻¹) *
    (jensen d n).comp (C (Real.exp (-(Av (uk 1 n)))) * (C (δv (uk 1 n)) * X - 1))

noncomputable def Gpoly (d n : ℕ) : ℝ[X] :=
  ∑ k ∈ range (d + 1), C ((d.choose k : ℝ) * gamv n k) * (X ^ (d - k) * (C (δv (uk 1 n)) * X - 1) ^ k)

lemma Gpoly_eval (d n : ℕ) (x : ℝ) : (Gpoly d n).eval x = Gn d n x := by
  simp only [Gpoly, Gn, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
  refine sum_congr rfl fun k _ => ?_
  ring

lemma Jhat_eval (d : ℕ) {n : ℕ} (hn : 2 ≤ n) (hU : 12 ≤ uk 1 n) (x : ℝ) : (Jhat d n).eval x = Gn d n x := by
  have hδ := δ_pos hU
  have hU1 : 1 < uk 1 n := by linarith
  have hM : 0 < Mmain n := by rw [Mmain_eq_exp hU1]; have := Kc_pos; positivity
  simp only [Jhat, eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_one]
  rw [eval_jensen_eq' d hn hU x]
  field_simp

theorem Jhat_eq_Gpoly (d : ℕ) {n : ℕ} (hn : 2 ≤ n) (hU : 12 ≤ uk 1 n) : Jhat d n = Gpoly d n :=
  Polynomial.funext fun x => by rw [Jhat_eval d hn hU, Gpoly_eval]

lemma coeff_lin_pow (δ : ℝ) (k m : ℕ) :
    ((C δ * X - 1) ^ k).coeff m = (k.choose m : ℝ) * δ ^ m * (-1) ^ (k - m) := by
  rw [sub_eq_add_neg, add_pow, finsetSum_coeff]
  have e : ∀ j ∈ range (k + 1), (C δ * X) ^ j * (-1 : ℝ[X]) ^ (k - j) * (k.choose j : ℝ[X]) =
      C (δ ^ j * (-1) ^ (k - j) * (k.choose j : ℝ)) * X ^ j := by
    intro j _
    simp only [mul_pow, map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  rw [sum_congr rfl fun j hj => by rw [e j hj]]
  simp only [coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  split_ifs with h
  · ring
  · simp only [mem_range, not_lt] at h
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

lemma coeff_Gpoly (d n i : ℕ) : (Gpoly d n).coeff i = ∑ k ∈ range (d + 1), (d.choose k : ℝ) * gamv n k *
    (if d - k ≤ i then (k.choose (i - (d - k)) : ℝ) * δv (uk 1 n) ^ (i - (d - k)) * (-1) ^ (k - (i - (d - k)))
      else 0) := by
  rw [Gpoly, finsetSum_coeff]
  refine sum_congr rfl fun k _ => ?_
  rw [coeff_C_mul, coeff_X_pow_mul']
  congr 1
  split_ifs
  · rw [coeff_lin_pow]
  · rfl

lemma coeff_H (d i : ℕ) : (H d).coeff i =
    ∑ k ∈ range (d + 1), if i = d - k then (d.choose k : ℝ) * cH k else 0 := by
  rw [H, finsetSum_coeff]
  refine sum_congr rfl fun k _ => ?_
  rw [coeff_C_mul_X_pow]

/-- **Coefficientwise convergence** `Ĵ^{d,n} → H_d(X/2)` (GORZ Theorem 1, partition case). (Milestone 2c.) -/
theorem tendsto_coeff_Jhat (d i : ℕ) :
    Tendsto (fun n : ℕ => (Jhat d n).coeff i) atTop (𝓝 ((H d).coeff i)) := by
  have hev : ∀ᶠ n : ℕ in atTop, (Gpoly d n).coeff i = (Jhat d n).coeff i := by
    filter_upwards [eventually_ge_atTop 2, ev_U12] with n hn hU
    rw [Jhat_eq_Gpoly d hn hU]
  refine Tendsto.congr' hev ?_
  simp only [coeff_Gpoly, coeff_H]
  refine tendsto_finsetSum _ fun k _ => ?_
  have hlim := (tendsto_gam k).const_mul (d.choose k : ℝ)
  split_ifs with h1 h2 h2
  · -- i = d − k
    have hm : i - (d - k) = 0 := by omega
    simp only [hm, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero]
    have h3 : (d.choose k : ℝ) * cH k = (d.choose k : ℝ) * cH k * (-1) ^ k := by
      rw [mul_assoc, mul_comm (cH k), neg_one_pow_mul_cH]
    rw [h3]
    exact (hlim.mul_const ((-1 : ℝ) ^ k)).congr fun n => by ring
  · -- d − k < i: the δ-power kills the term
    have hm : 0 < i - (d - k) := by omega
    have hδm := (tendsto_δ.pow (i - (d - k))).const_mul ((k.choose (i - (d - k)) : ℝ))
    have := (hlim.mul (hδm.mul_const ((-1 : ℝ) ^ (k - (i - (d - k))))))
    rw [zero_pow hm.ne', mul_zero, zero_mul, mul_zero] at this
    exact this
  · omega
  · exact tendsto_const_nhds.congr fun n => by simp

end GORZ
