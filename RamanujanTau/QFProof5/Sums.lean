/-
# Elementary finite-sum bounds used by the local mass estimates (unconditional)

* `sum_c_le`: `Σ_{k≤N} (k+1)(k+2)/2 · r^k ≤ 8` for `0 ≤ r ≤ 1/2`;
* `sum_sq_le`: `Σ_{k≤N} (k+1)² r^k ≤ 16`;
* `sum_sq_shift_le`: `Σ_{a≤N} (a+1)² r^{a−e} ≤ 16 (e+1)³` (truncated subtraction);
* `conv1_le`: `Σ_{i≤N} Σ_{a≤i} F(a) G(i−a) ≤ (Σ_{a≤N} F)(Σ_{k≤N} G)` for `F, G ≥ 0`;
* `poly_le_geom`: `(e+1)^12 ≤ (100/3)^12 (3/2)^e`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.QFProof5

open Finset

lemma Icc_zero_eq_range (N : ℕ) : Icc 0 N = range (N + 1) := by
  ext; simp only [mem_Icc, mem_range]; omega

lemma c_eq_choose (k : ℕ) : ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 = (((k + 2).choose 2 : ℕ) : ℝ) := by
  rw [Nat.cast_choose_two]; push_cast; ring

lemma sum_c_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (N : ℕ) :
    ∑ k ∈ Icc 0 N, ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 * r ^ k ≤ 8 := by
  have hr1 : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; linarith
  have hs := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hr1
  have h1 : ∑ k ∈ Icc 0 N, ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 * r ^ k ≤ 1 / (1 - r) ^ (2 + 1) := by
    have := sum_le_hasSum (Icc 0 N) (fun i _ => by positivity) hs
    refine le_trans (le_of_eq ?_) this
    refine sum_congr rfl fun k _ => ?_
    rw [c_eq_choose]
  refine h1.trans ?_
  have h2 : (1 / 2 : ℝ) ≤ 1 - r := by linarith
  have h3 : (1 / 2 : ℝ) ^ 3 ≤ (1 - r) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
  rw [div_le_iff₀ (by positivity)]
  norm_num at h3 ⊢
  linarith

lemma sum_sq_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (N : ℕ) :
    ∑ k ∈ Icc 0 N, ((k : ℝ) + 1) ^ 2 * r ^ k ≤ 16 := by
  have h := sum_c_le hr0 hr N
  have : ∑ k ∈ Icc 0 N, ((k : ℝ) + 1) ^ 2 * r ^ k ≤
      2 * ∑ k ∈ Icc 0 N, ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 * r ^ k := by
    rw [mul_sum]
    refine sum_le_sum fun k _ => ?_
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hrk : 0 ≤ r ^ k := pow_nonneg hr0 k
    nlinarith
  linarith

/-- `Σ_{a<M} φ(a−e) ≤ e φ(0) + Σ_{a<M} φ(a)` for `φ ≥ 0`. -/
lemma sum_shift_le (φ : ℕ → ℝ) (hφ : ∀ k, 0 ≤ φ k) (e M : ℕ) :
    ∑ a ∈ range M, φ (a - e) ≤ e * φ 0 + ∑ a ∈ range M, φ a := by
  have hS : 0 ≤ ∑ a ∈ range M, φ a := sum_nonneg fun _ _ => hφ _
  rcases le_or_gt M e with hMe | hMe
  · have : ∑ a ∈ range M, φ (a - e) = M * φ 0 := by
      rw [sum_congr rfl fun a ha => by rw [show a - e = 0 by have := mem_range.1 ha; omega]]
      simp
    rw [this]
    have : (M : ℝ) ≤ e := by exact_mod_cast hMe
    nlinarith [hφ 0]
  · rw [← sum_range_add_sum_Ico _ hMe.le, sum_Ico_eq_sum_range]
    have h1 : ∑ a ∈ range e, φ (a - e) = e * φ 0 := by
      rw [sum_congr rfl fun a ha => by rw [show a - e = 0 by have := mem_range.1 ha; omega]]
      simp
    have h2 : ∑ k ∈ range (M - e), φ (e + k - e) ≤ ∑ a ∈ range M, φ a := by
      rw [sum_congr rfl fun k _ => by rw [show e + k - e = k by omega]]
      exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) fun _ _ _ => hφ _
    linarith

lemma sum_sq_shift_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (e N : ℕ) :
    ∑ a ∈ Icc 0 N, ((a : ℝ) + 1) ^ 2 * r ^ (a - e) ≤ 16 * ((e : ℝ) + 1) ^ 3 := by
  have he : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hpt : ∀ a : ℕ, ((a : ℝ) + 1) ^ 2 * r ^ (a - e) ≤
      ((e : ℝ) + 1) ^ 2 * ((((a - e : ℕ) : ℝ) + 1) ^ 2 * r ^ (a - e)) := by
    intro a
    have h1 : (a : ℝ) + 1 ≤ ((e : ℝ) + 1) * (((a - e : ℕ) : ℝ) + 1) := by
      rcases le_or_gt a e with hae | hae
      · rw [show a - e = 0 by omega]; push_cast
        have : (a : ℝ) ≤ e := by exact_mod_cast hae
        linarith
      · rw [Nat.cast_sub hae.le]
        have : (e : ℝ) < a := by exact_mod_cast hae
        nlinarith
    have h0 : (0 : ℝ) ≤ (a : ℝ) + 1 := by positivity
    have h2 : ((a : ℝ) + 1) ^ 2 ≤ ((e : ℝ) + 1) ^ 2 * (((a - e : ℕ) : ℝ) + 1) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ h0 h1 2
    have hrk : 0 ≤ r ^ (a - e) := pow_nonneg hr0 _
    nlinarith
  have hφ : ∀ k : ℕ, (0 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 * r ^ k := fun k => by positivity
  have hsh := sum_shift_le (fun k => ((k : ℝ) + 1) ^ 2 * r ^ k) hφ e (N + 1)
  have hs := sum_sq_le hr0 hr N
  rw [Icc_zero_eq_range] at hs ⊢
  calc ∑ a ∈ range (N + 1), ((a : ℝ) + 1) ^ 2 * r ^ (a - e)
      ≤ ∑ a ∈ range (N + 1), ((e : ℝ) + 1) ^ 2 * ((((a - e : ℕ) : ℝ) + 1) ^ 2 * r ^ (a - e)) :=
        sum_le_sum fun a _ => hpt a
    _ = ((e : ℝ) + 1) ^ 2 * ∑ a ∈ range (N + 1), ((((a - e : ℕ) : ℝ) + 1) ^ 2 * r ^ (a - e)) := by
        rw [mul_sum]
    _ ≤ ((e : ℝ) + 1) ^ 2 * (e * 1 + 16) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        simp only [Nat.cast_zero, zero_add, one_pow, pow_zero, mul_one] at hsh
        linarith
    _ ≤ 16 * ((e : ℝ) + 1) ^ 3 := by nlinarith [sq_nonneg ((e : ℝ) + 1)]

/-- One-variable convolution bound. -/
lemma conv1_le (F G : ℕ → ℝ) (hF : ∀ k, 0 ≤ F k) (hG : ∀ k, 0 ≤ G k) (N : ℕ) :
    ∑ i ∈ Icc 0 N, ∑ a ∈ Icc 0 i, F a * G (i - a) ≤
      (∑ a ∈ Icc 0 N, F a) * ∑ k ∈ Icc 0 N, G k := by
  rw [sum_comm' (t' := Icc 0 N) (s' := fun a => Icc a N) (by
    intro i a; simp only [mem_Icc]; omega)]
  rw [sum_mul]
  refine sum_le_sum fun a ha => ?_
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (hF a)
  have hinj : Set.InjOn (fun i => i - a) (Icc a N : Set ℕ) := by
    intro x hx y hy hxy
    simp only [coe_Icc, Set.mem_Icc] at hx hy
    simp only at hxy
    omega
  rw [← sum_image (f := G) (fun x hx y hy h => hinj hx hy h)]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => hG _
  intro k hk
  simp only [mem_image, mem_Icc] at hk ⊢
  obtain ⟨i, hi, rfl⟩ := hk
  omega

/-- `(e+1)^12 ≤ (100/3)^12 (3/2)^e`. -/
lemma poly_le_geom (e : ℕ) : ((e : ℝ) + 1) ^ 12 ≤ (100 / 3 : ℝ) ^ 12 * (3 / 2 : ℝ) ^ e := by
  have h1 : 1 + (e : ℝ) * (3 / 100) ≤ (1 + 3 / 100) ^ e := one_add_mul_le_pow (by norm_num) e
  have h2 : (e : ℝ) + 1 ≤ 100 / 3 * (103 / 100 : ℝ) ^ e := by
    have : (1 + 3 / 100 : ℝ) = 103 / 100 := by norm_num
    rw [this] at h1
    nlinarith
  have h3 : ((e : ℝ) + 1) ^ 12 ≤ (100 / 3 * (103 / 100 : ℝ) ^ e) ^ 12 :=
    pow_le_pow_left₀ (by positivity) h2 12
  refine h3.trans ?_
  rw [mul_pow, ← pow_mul, mul_comm e 12, pow_mul]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by norm_num) e) (by positivity)

end RamanujanTau.QFProof5
