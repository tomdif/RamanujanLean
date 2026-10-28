import Mathlib

/-!
# Coefficient bounds for power series over a nonarchimedean normed field

`GB ρ F`: every coefficient of `F ∈ K⟦X⟧` has norm `≤ ρ`. Closed under sums, products (bounds
multiply), finite sums and products (bound `1`), `expand`, `rescale` by elements of norm `1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VLayer
open PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- every coefficient has norm `≤ ρ`. -/
def GB (ρ : ℝ) (F : PowerSeries K) : Prop := ∀ n, ‖coeff n F‖ ≤ ρ

lemma GB.mono {ρ ρ' : ℝ} {F : PowerSeries K} (h : GB ρ F) (hρ : ρ ≤ ρ') : GB ρ' F :=
  fun n => (h n).trans hρ

lemma GB_zero {ρ : ℝ} (hρ : 0 ≤ ρ) : GB ρ (0 : PowerSeries K) := fun n => by simpa using hρ

lemma GB_one {ρ : ℝ} (hρ : 1 ≤ ρ) : GB ρ (1 : PowerSeries K) := fun n => by
  rw [coeff_one]; split_ifs <;> simp <;> linarith

lemma GB_C {ρ : ℝ} {a : K} (ha : ‖a‖ ≤ ρ) (hρ : 0 ≤ ρ) : GB ρ (C a : PowerSeries K) := fun n => by
  rw [coeff_C]; split_ifs <;> simpa

lemma GB.add {ρ : ℝ} {F G : PowerSeries K} (hF : GB ρ F) (hG : GB ρ G) : GB ρ (F + G) := fun n => by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hF n) (hG n))

lemma GB.neg {ρ : ℝ} {F : PowerSeries K} (hF : GB ρ F) : GB ρ (-F) := fun n => by
  rw [map_neg, norm_neg]; exact hF n

lemma GB.sub {ρ : ℝ} {F G : PowerSeries K} (hF : GB ρ F) (hG : GB ρ G) : GB ρ (F - G) := by
  rw [sub_eq_add_neg]; exact hF.add hG.neg

lemma GB.mul {ρ ρ' : ℝ} {F G : PowerSeries K} (hF : GB ρ F) (hG : GB ρ' G) (hρ : 0 ≤ ρ)
    (hρ' : 0 ≤ ρ') : GB (ρ * ρ') (F * G) := fun n => by
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hρ hρ') fun x _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hF _) (hG _) (norm_nonneg _) hρ

lemma GB.mul_one {ρ : ℝ} {F G : PowerSeries K} (hF : GB 1 F) (hG : GB ρ G) (hρ : 0 ≤ ρ) :
    GB ρ (F * G) := by
  simpa using hF.mul hG zero_le_one hρ

lemma GB_sum {ι : Type*} {ρ : ℝ} (hρ : 0 ≤ ρ) (s : Finset ι) (f : ι → PowerSeries K)
    (h : ∀ i ∈ s, GB ρ (f i)) : GB ρ (∑ i ∈ s, f i) := fun n => by
  rw [map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hρ fun i hi => h i hi n

lemma GB_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries K) (h : ∀ i ∈ s, GB 1 (f i)) :
    GB 1 (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GB_one (K := K) le_rfl
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul_one
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) zero_le_one

lemma GB_pow {F : PowerSeries K} (hF : GB 1 F) (n : ℕ) : GB 1 (F ^ n) := by
  simpa using GB_prod (Finset.range n) (fun _ => F) fun _ _ => hF

/-- `∏ (1 + h_i) ≡ 1` when every `h_i` is small. -/
lemma GB_prod_sub_one {ι : Type*} {ρ : ℝ} (hρ : 0 ≤ ρ) (s : Finset ι) (f : ι → PowerSeries K)
    (h1 : ∀ i ∈ s, GB 1 (f i)) (h : ∀ i ∈ s, GB ρ (f i - 1)) : GB ρ (∏ i ∈ s, f i - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GB_zero (K := K) hρ
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have e : f a * ∏ i ∈ s, f i - 1 = (f a - 1) * ∏ i ∈ s, f i + (∏ i ∈ s, f i - 1) := by ring
    rw [e]
    refine GB.add ?_ (ih (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    have := (h a (Finset.mem_insert_self a s)).mul
      (GB_prod s f fun i hi => h1 i (Finset.mem_insert_of_mem hi)) hρ zero_le_one
    simpa using this

lemma GB_expand {ρ : ℝ} (hρ : 0 ≤ ρ) {p : ℕ} (hp : p ≠ 0) {F : PowerSeries K} (hF : GB ρ F) :
    GB ρ (expand p hp F) := fun n => by
  rw [coeff_expand]; split_ifs
  · exact hF _
  · simpa using hρ

lemma GB_rescale {ρ : ℝ} {a : K} (ha : ‖a‖ = 1) {F : PowerSeries K} (hF : GB ρ F) :
    GB ρ (rescale a F) := fun n => by
  rw [coeff_rescale, norm_mul, norm_pow, ha, one_pow, one_mul]; exact hF n

end VLayer
