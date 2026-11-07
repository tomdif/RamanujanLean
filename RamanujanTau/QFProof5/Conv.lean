/-
# Weighted convolution bound for the local factors `γK` (under `[DeligneBound]`)

For a generic kernel `K p n e` and a weight `w ≥ 0`:

* `conv2_le`: two-variable convolution `Σ_{i,j≤N} Σ_{a≤i,b≤j} H(a,b)G(i−a)G(j−b) ≤ (ΣH)(ΣG)²`;
* `wmass_le`: `Σ_{i,j≤N} w^{i+j}|γK K p e i j| ≤ (Σ_{a,b≤N} w^{a+b}|K p (a+b) e|) (Σ_{k≤N} w^k|Fi(p^k)|)²`;
* `sumFi_le`: `Σ_{k≤N} w^k|Fi(p^k)| ≤ 8` when `w/p ≤ 1/2`;
* `split_low`: `Σ_{i,j≤N} g ≤ g(0,0)+g(1,0)+g(0,1) + w^{−2} Σ w^{i+j} g` for `w ≥ 1`.
-/
import RamanujanTau.QFProof5.Basic

set_option autoImplicit false

namespace RamanujanTau.QFProof5

open Finset RamanujanTau.QFProof RamanujanTau.QFProof2 RamanujanTau.QFProof3 RamanujanTau.QFProof4
open RamanujanTau.SelbergCoeffs (alpha abs_alpha_le_one)

lemma conv2_le (H : ℕ → ℕ → ℝ) (G : ℕ → ℝ) (hH : ∀ a b, 0 ≤ H a b) (hG : ∀ k, 0 ≤ G k) (N : ℕ) :
    ∑ i ∈ Icc 0 N, ∑ j ∈ Icc 0 N, ∑ a ∈ Icc 0 i, ∑ b ∈ Icc 0 j, H a b * G (i - a) * G (j - b) ≤
      (∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, H a b) * (∑ k ∈ Icc 0 N, G k) ^ 2 := by
  set SG := ∑ k ∈ Icc 0 N, G k with hSGdef
  have hSG : 0 ≤ SG := sum_nonneg fun _ _ => hG _
  have step1 : ∀ i, ∑ j ∈ Icc 0 N, ∑ a ∈ Icc 0 i, ∑ b ∈ Icc 0 j, H a b * G (i - a) * G (j - b) =
      ∑ a ∈ Icc 0 i, G (i - a) * ∑ j ∈ Icc 0 N, ∑ b ∈ Icc 0 j, H a b * G (j - b) := by
    intro i
    rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun b _ => ?_
    ring
  have step2 : ∀ a, ∑ j ∈ Icc 0 N, ∑ b ∈ Icc 0 j, H a b * G (j - b) ≤ (∑ b ∈ Icc 0 N, H a b) * SG :=
    fun a => conv1_le (H a) G (hH a) hG N
  calc _ = ∑ i ∈ Icc 0 N, ∑ a ∈ Icc 0 i, G (i - a) * ∑ j ∈ Icc 0 N, ∑ b ∈ Icc 0 j, H a b * G (j - b) :=
        sum_congr rfl fun i _ => step1 i
    _ ≤ ∑ i ∈ Icc 0 N, ∑ a ∈ Icc 0 i, (∑ b ∈ Icc 0 N, H a b) * SG * G (i - a) := by
        refine sum_le_sum fun i _ => sum_le_sum fun a _ => ?_
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (step2 a) (hG _)
    _ = SG * ∑ i ∈ Icc 0 N, ∑ a ∈ Icc 0 i, (∑ b ∈ Icc 0 N, H a b) * G (i - a) := by
        rw [mul_sum]; refine sum_congr rfl fun i _ => ?_
        rw [mul_sum]; refine sum_congr rfl fun a _ => ?_
        ring
    _ ≤ SG * ((∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, H a b) * SG) :=
        mul_le_mul_of_nonneg_left (conv1_le _ G (fun a => sum_nonneg fun b _ => hH a b) hG N) hSG
    _ = _ := by ring

lemma abs_sum2_le (s t : Finset ℕ) (f : ℕ → ℕ → ℝ) :
    |∑ a ∈ s, ∑ b ∈ t, f a b| ≤ ∑ a ∈ s, ∑ b ∈ t, |f a b| :=
  (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun _ _ => abs_sum_le_sum_abs _ _)

lemma γK_symm (K : ℕ → ℕ → ℕ → ℝ) (p e i j : ℕ) : γK K p e i j = γK K p e j i := by
  unfold γK
  rw [sum_comm]
  refine sum_congr rfl fun b _ => sum_congr rfl fun a _ => ?_
  rw [add_comm b a]; ring

section Deligne

variable [DeligneBound]

lemma pt_le (K : ℕ → ℕ → ℕ → ℝ) (p : ℕ) {w : ℝ} (hw : 0 ≤ w) (e i j : ℕ) :
    w ^ (i + j) * |γK K p e i j| ≤ ∑ a ∈ Icc 0 i, ∑ b ∈ Icc 0 j,
      (w ^ (a + b) * |K p (a + b) e|) * (w ^ (i - a) * |Fi (p ^ (i - a))|) *
        (w ^ (j - b) * |Fi (p ^ (j - b))|) := by
  unfold γK
  refine (mul_le_mul_of_nonneg_left (abs_sum2_le _ _ _) (pow_nonneg hw _)).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun a ha => ?_
  rw [mul_sum]
  refine sum_le_sum fun b hb => ?_
  have hai : a ≤ i := (mem_Icc.1 ha).2
  have hbj : b ≤ j := (mem_Icc.1 hb).2
  have hwp : w ^ (i + j) = w ^ (a + b) * w ^ (i - a) * w ^ (j - b) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [hwp, abs_mul, abs_mul, abs_mul, abs_mul]
  have h1 := abs_alpha_le_one (p ^ a)
  have h2 := abs_alpha_le_one (p ^ b)
  have hA : |alpha (p ^ a)| * |alpha (p ^ b)| ≤ 1 := by
    have := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num); simpa using this
  have hR : 0 ≤ |K p (a + b) e| * |Fi (p ^ (i - a))| * |Fi (p ^ (j - b))| := by positivity
  have hW : 0 ≤ w ^ (a + b) * w ^ (i - a) * w ^ (j - b) := by positivity
  calc w ^ (a + b) * w ^ (i - a) * w ^ (j - b) *
        (|alpha (p ^ a)| * |alpha (p ^ b)| * |K p (a + b) e| * |Fi (p ^ (i - a))| * |Fi (p ^ (j - b))|)
      = w ^ (a + b) * w ^ (i - a) * w ^ (j - b) *
        ((|alpha (p ^ a)| * |alpha (p ^ b)|) * (|K p (a + b) e| * |Fi (p ^ (i - a))| * |Fi (p ^ (j - b))|)) := by
        ring
    _ ≤ w ^ (a + b) * w ^ (i - a) * w ^ (j - b) *
        (1 * (|K p (a + b) e| * |Fi (p ^ (i - a))| * |Fi (p ^ (j - b))|)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA hR) hW
    _ = _ := by ring

/-- **Weighted local mass bound.** -/
theorem wmass_le (K : ℕ → ℕ → ℕ → ℝ) (p : ℕ) {w : ℝ} (hw : 0 ≤ w) (e N : ℕ) :
    ∑ i ∈ Icc 0 N, ∑ j ∈ Icc 0 N, w ^ (i + j) * |γK K p e i j| ≤
      (∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, w ^ (a + b) * |K p (a + b) e|) *
        (∑ k ∈ Icc 0 N, w ^ k * |Fi (p ^ k)|) ^ 2 := by
  refine (sum_le_sum fun i _ => sum_le_sum fun j _ => pt_le K p hw e i j).trans ?_
  exact conv2_le (fun a b => w ^ (a + b) * |K p (a + b) e|) (fun k => w ^ k * |Fi (p ^ k)|)
    (fun a b => by positivity) (fun k => by positivity) N

lemma sumFi_le {p : ℕ} (hp : p.Prime) {w : ℝ} (hw : 0 ≤ w) (hwX : w * Xp p ≤ 1 / 2) (N : ℕ) :
    ∑ k ∈ Icc 0 N, w ^ k * |Fi (p ^ k)| ≤ 8 := by
  have hX := Xp_pos hp
  refine le_trans (sum_le_sum fun k _ => ?_) (sum_c_le (by positivity) hwX N)
  calc w ^ k * |Fi (p ^ k)| ≤ w ^ k * (((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 * Xp p ^ k) :=
        mul_le_mul_of_nonneg_left (abs_Fi_le hp k) (pow_nonneg hw _)
    _ = _ := by rw [mul_pow]; ring

end Deligne

lemma sum2_ite_le (s t : Finset ℕ) (a b : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    ∑ i ∈ s, ∑ j ∈ t, (if i = a ∧ j = b then c else 0) ≤ c := by
  simp only [ite_and]
  have h : ∀ i ∈ s, ∑ j ∈ t, (if i = a then (if j = b then c else 0) else 0) =
      if i = a then ∑ j ∈ t, (if j = b then c else 0) else 0 := by
    intro i _; split_ifs <;> simp
  rw [sum_congr rfl h, sum_ite_eq' s a (fun _ => ∑ j ∈ t, if j = b then c else 0)]
  split_ifs
  · rw [sum_ite_eq' t b (fun _ => c)]; split_ifs <;> linarith
  · exact hc

/-- Splitting off the three lowest terms with a weight `w ≥ 1`. -/
lemma split_low (g : ℕ → ℕ → ℝ) (hg : ∀ i j, 0 ≤ g i j) {w : ℝ} (hw : 1 ≤ w) (N : ℕ) :
    ∑ i ∈ Icc 0 N, ∑ j ∈ Icc 0 N, g i j ≤
      g 0 0 + g 1 0 + g 0 1 + (w ^ 2)⁻¹ * ∑ i ∈ Icc 0 N, ∑ j ∈ Icc 0 N, w ^ (i + j) * g i j := by
  have hw0 : 0 < w := by linarith
  have hpt : ∀ i j, g i j ≤ (if i = 0 ∧ j = 0 then g 0 0 else 0) + (if i = 1 ∧ j = 0 then g 1 0 else 0) +
      (if i = 0 ∧ j = 1 then g 0 1 else 0) + (w ^ 2)⁻¹ * (w ^ (i + j) * g i j) := by
    intro i j
    have hr : 0 ≤ (w ^ 2)⁻¹ * (w ^ (i + j) * g i j) := by have := hg i j; positivity
    by_cases h00 : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h00
      rw [if_pos ⟨rfl, rfl⟩, if_neg (by omega), if_neg (by omega)]; linarith
    by_cases h10 : i = 1 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h10
      rw [if_neg h00, if_pos ⟨rfl, rfl⟩, if_neg (by omega)]; linarith
    by_cases h01 : i = 0 ∧ j = 1
    · obtain ⟨rfl, rfl⟩ := h01
      rw [if_neg h00, if_neg h10, if_pos ⟨rfl, rfl⟩]; linarith
    rw [if_neg h00, if_neg h10, if_neg h01]
    have h2 : 2 ≤ i + j := by omega
    have : w ^ 2 ≤ w ^ (i + j) := pow_le_pow_right₀ hw h2
    rw [← mul_assoc, zero_add, zero_add, zero_add]
    have hgw : g i j ≤ (w ^ 2)⁻¹ * w ^ (i + j) * g i j := by
      have h1 : 1 ≤ (w ^ 2)⁻¹ * w ^ (i + j) := by
        rw [inv_mul_eq_div, one_le_div (by positivity)]; exact this
      nlinarith [hg i j]
    exact hgw
  calc ∑ i ∈ Icc 0 N, ∑ j ∈ Icc 0 N, g i j
      ≤ ∑ i ∈ Icc 0 N, ∑ j ∈ Icc 0 N, ((if i = 0 ∧ j = 0 then g 0 0 else 0) +
          (if i = 1 ∧ j = 0 then g 1 0 else 0) + (if i = 0 ∧ j = 1 then g 0 1 else 0) +
          (w ^ 2)⁻¹ * (w ^ (i + j) * g i j)) := sum_le_sum fun i _ => sum_le_sum fun j _ => hpt i j
    _ = ∑ i ∈ Icc 0 N, ∑ j ∈ Icc 0 N, (if i = 0 ∧ j = 0 then g 0 0 else 0) +
        ∑ i ∈ Icc 0 N, ∑ j ∈ Icc 0 N, (if i = 1 ∧ j = 0 then g 1 0 else 0) +
        ∑ i ∈ Icc 0 N, ∑ j ∈ Icc 0 N, (if i = 0 ∧ j = 1 then g 0 1 else 0) +
        (w ^ 2)⁻¹ * ∑ i ∈ Icc 0 N, ∑ j ∈ Icc 0 N, w ^ (i + j) * g i j := by
        simp only [sum_add_distrib, mul_sum]
    _ ≤ _ := by
        have := sum2_ite_le (Icc 0 N) (Icc 0 N) 0 0 (hg 0 0)
        have := sum2_ite_le (Icc 0 N) (Icc 0 N) 1 0 (hg 1 0)
        have := sum2_ite_le (Icc 0 N) (Icc 0 N) 0 1 (hg 0 1)
        linarith

end RamanujanTau.QFProof5
