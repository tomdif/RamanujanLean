/-
# `SvStripD` step 1: generic complex local masses (unconditional)

The twisted local factor of `Γ^z` at a prime has the shape

    γ(e; i, j) = Σ_{a≤i, b≤j} A₁(a) A₂(b) L(a+b, e) F₁(i−a) F₂(j−b)

with complex local sequences.  Here everything is generic: we only assume, for some `0 < X ≤ 3/5`,

    ‖A₁(a)‖, ‖A₂(b)‖ ≤ 1,   ‖F_i(k)‖ ≤ c_k X^k  (c_k = (k+1)(k+2)/2),
    ‖L(n,e)‖ ≤ κ (n+1)² X^{n−e},   L(n,e) = 0 for n < e.

(For the twisted kernel, `X = ‖p^{−s}‖ = p^{−1+t}`, `t = |Im z|`.)  Results, uniform in the
truncation `N` (`TC e N = Σ_{i,j≤N} ‖γ(e;i,j)‖`):

* `TC_le_gen`:  `TC e N ≤ B κ (e+1)^6`;
* `TC_zero_split`: `TC 0 N ≤ ‖γ(0;0,0)‖ + ‖γ(0;1,0)‖ + ‖γ(0;0,1)‖ + (9/4) B κ X²`;
* `TC_one_split`:  `TC 1 N ≤ ‖γ(1;0,0)‖ + ‖γ(1;1,0)‖ + ‖γ(1;0,1)‖ + (9/4) B κ X`;

with `B = 27² · 54² = 2125764`.  The lowest terms carry the first-order cancellation and are
computed for the concrete twisted data in `Local.lean`.  Level 1.
-/
import RamanujanTau.QFProof5.Local

set_option autoImplicit false

namespace RamanujanTau.SvStripD

open Finset
open RamanujanTau.QFProof5 (conv1_le conv2_le split_low sum_shift_le Icc_zero_eq_range c_eq_choose sq_add_le
  sum_mul_self_le)

/-! ### Geometric sums for `r ≤ 2/3` -/

/-- `c_k = (k+1)(k+2)/2`. -/
noncomputable def ck (k : ℕ) : ℝ := ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2

lemma ck_nonneg (k : ℕ) : 0 ≤ ck k := by unfold ck; positivity

lemma sum_ck_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 2 / 3) (N : ℕ) :
    ∑ k ∈ Icc 0 N, ck k * r ^ k ≤ 27 := by
  have hr1 : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; linarith
  have hs := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hr1
  have h1 : ∑ k ∈ Icc 0 N, ck k * r ^ k ≤ 1 / (1 - r) ^ (2 + 1) := by
    have := sum_le_hasSum (Icc 0 N) (fun i _ => by positivity) hs
    refine le_trans (le_of_eq ?_) this
    refine sum_congr rfl fun k _ => ?_
    rw [ck, c_eq_choose]
  refine h1.trans ?_
  have h2 : (1 / 3 : ℝ) ≤ 1 - r := by linarith
  have h3 : (1 / 3 : ℝ) ^ 3 ≤ (1 - r) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
  rw [div_le_iff₀ (by positivity)]
  norm_num at h3 ⊢
  linarith

lemma sum_sq_le' {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 2 / 3) (N : ℕ) :
    ∑ k ∈ Icc 0 N, ((k : ℝ) + 1) ^ 2 * r ^ k ≤ 54 := by
  have h := sum_ck_le hr0 hr N
  have : ∑ k ∈ Icc 0 N, ((k : ℝ) + 1) ^ 2 * r ^ k ≤ 2 * ∑ k ∈ Icc 0 N, ck k * r ^ k := by
    rw [mul_sum]
    refine sum_le_sum fun k _ => ?_
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hrk : 0 ≤ r ^ k := pow_nonneg hr0 k
    unfold ck; nlinarith
  linarith

lemma sum_sq_shift_le' {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 2 / 3) (e N : ℕ) :
    ∑ a ∈ Icc 0 N, ((a : ℝ) + 1) ^ 2 * r ^ (a - e) ≤ 54 * ((e : ℝ) + 1) ^ 3 := by
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
  have hs := sum_sq_le' hr0 hr N
  rw [Icc_zero_eq_range] at hs ⊢
  calc ∑ a ∈ range (N + 1), ((a : ℝ) + 1) ^ 2 * r ^ (a - e)
      ≤ ∑ a ∈ range (N + 1), ((e : ℝ) + 1) ^ 2 * ((((a - e : ℕ) : ℝ) + 1) ^ 2 * r ^ (a - e)) :=
        sum_le_sum fun a _ => hpt a
    _ = ((e : ℝ) + 1) ^ 2 * ∑ a ∈ range (N + 1), ((((a - e : ℕ) : ℝ) + 1) ^ 2 * r ^ (a - e)) := by
        rw [mul_sum]
    _ ≤ ((e : ℝ) + 1) ^ 2 * (e * 1 + 54) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        simp only [Nat.cast_zero, zero_add, one_pow, pow_zero, mul_one] at hsh
        linarith
    _ ≤ 54 * ((e : ℝ) + 1) ^ 3 := by nlinarith [sq_nonneg ((e : ℝ) + 1)]

/-! ### The generic local factor -/

/-- `γ(e;i,j) = Σ_{a≤i,b≤j} A₁(a)A₂(b)L(a+b,e)F₁(i−a)F₂(j−b)`. -/
noncomputable def γC (A₁ A₂ F₁ F₂ : ℕ → ℂ) (L : ℕ → ℕ → ℂ) (e i j : ℕ) : ℂ :=
  ∑ a ∈ Icc 0 i, ∑ b ∈ Icc 0 j, A₁ a * A₂ b * L (a + b) e * F₁ (i - a) * F₂ (j - b)

/-- The local mass `TC e N = Σ_{i,j≤N} ‖γ(e;i,j)‖`. -/
noncomputable def TC (A₁ A₂ F₁ F₂ : ℕ → ℂ) (L : ℕ → ℕ → ℂ) (e N : ℕ) : ℝ :=
  ∑ i ∈ Icc 0 N, ∑ j ∈ Icc 0 N, ‖γC A₁ A₂ F₁ F₂ L e i j‖

lemma TC_nonneg (A₁ A₂ F₁ F₂ : ℕ → ℂ) (L : ℕ → ℕ → ℂ) (e N : ℕ) : 0 ≤ TC A₁ A₂ F₁ F₂ L e N :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _

lemma γC_00 (A₁ A₂ F₁ F₂ : ℕ → ℂ) (L : ℕ → ℕ → ℂ) (e : ℕ) :
    γC A₁ A₂ F₁ F₂ L e 0 0 = A₁ 0 * A₂ 0 * L 0 e * F₁ 0 * F₂ 0 := by
  simp [γC]

lemma Icc01 : Icc 0 1 = ({0, 1} : Finset ℕ) := by
  ext x; simp only [mem_Icc, mem_insert, mem_singleton]; omega

lemma γC_10 (A₁ A₂ F₁ F₂ : ℕ → ℂ) (L : ℕ → ℕ → ℂ) (e : ℕ) :
    γC A₁ A₂ F₁ F₂ L e 1 0 =
      A₁ 0 * A₂ 0 * L 0 e * F₁ 1 * F₂ 0 + A₁ 1 * A₂ 0 * L 1 e * F₁ 0 * F₂ 0 := by
  unfold γC
  rw [Icc01, sum_pair (by norm_num)]
  simp

lemma γC_01 (A₁ A₂ F₁ F₂ : ℕ → ℂ) (L : ℕ → ℕ → ℂ) (e : ℕ) :
    γC A₁ A₂ F₁ F₂ L e 0 1 =
      A₁ 0 * A₂ 0 * L 0 e * F₁ 0 * F₂ 1 + A₁ 0 * A₂ 1 * L 1 e * F₁ 0 * F₂ 0 := by
  unfold γC
  rw [Icc01]
  simp

lemma w_ge {X : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 2 / 3) : 1 ≤ 2 / 3 / X := by
  rw [le_div_iff₀ hX0]; linarith

lemma w_X {X : ℝ} (hX0 : 0 < X) : 2 / 3 / X * X = 2 / 3 := by field_simp

lemma inv_w_sq {X : ℝ} (hX0 : 0 < X) : ((2 / 3 / X) ^ 2)⁻¹ = 9 / 4 * X ^ 2 := by field_simp; ring

section Bounds

variable {A₁ A₂ F₁ F₂ : ℕ → ℂ} {L : ℕ → ℕ → ℂ} {X κ : ℝ}

lemma norm_sum2_le (s t : Finset ℕ) (f : ℕ → ℕ → ℂ) :
    ‖∑ a ∈ s, ∑ b ∈ t, f a b‖ ≤ ∑ a ∈ s, ∑ b ∈ t, ‖f a b‖ :=
  (norm_sum_le _ _).trans (sum_le_sum fun _ _ => norm_sum_le _ _)

/-- Pointwise weighted bound (`G(k) = c_k (wX)^k`). -/
lemma ptC_le (hX : 0 ≤ X) (hA₁ : ∀ a, ‖A₁ a‖ ≤ 1) (hA₂ : ∀ a, ‖A₂ a‖ ≤ 1)
    (hF₁ : ∀ k, ‖F₁ k‖ ≤ ck k * X ^ k) (hF₂ : ∀ k, ‖F₂ k‖ ≤ ck k * X ^ k)
    {w : ℝ} (hw : 0 ≤ w) (e i j : ℕ) :
    w ^ (i + j) * ‖γC A₁ A₂ F₁ F₂ L e i j‖ ≤ ∑ a ∈ Icc 0 i, ∑ b ∈ Icc 0 j,
      (w ^ (a + b) * ‖L (a + b) e‖) * (ck (i - a) * (w * X) ^ (i - a)) *
        (ck (j - b) * (w * X) ^ (j - b)) := by
  unfold γC
  refine (mul_le_mul_of_nonneg_left (norm_sum2_le _ _ _) (pow_nonneg hw _)).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun a ha => ?_
  rw [mul_sum]
  refine sum_le_sum fun b hb => ?_
  have hai : a ≤ i := (mem_Icc.1 ha).2
  have hbj : b ≤ j := (mem_Icc.1 hb).2
  have hwp : w ^ (i + j) = w ^ (a + b) * w ^ (i - a) * w ^ (j - b) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [hwp, norm_mul, norm_mul, norm_mul, norm_mul]
  have hA : ‖A₁ a‖ * ‖A₂ b‖ ≤ 1 := by
    have := mul_le_mul (hA₁ a) (hA₂ b) (norm_nonneg _) (by norm_num); simpa using this
  have h1 := hF₁ (i - a)
  have h2 := hF₂ (j - b)
  have hL0 := norm_nonneg (L (a + b) e)
  have hW : 0 ≤ w ^ (a + b) * w ^ (i - a) * w ^ (j - b) := by positivity
  have hc1 := ck_nonneg (i - a)
  have hc2 := ck_nonneg (j - b)
  calc w ^ (a + b) * w ^ (i - a) * w ^ (j - b) *
        (‖A₁ a‖ * ‖A₂ b‖ * ‖L (a + b) e‖ * ‖F₁ (i - a)‖ * ‖F₂ (j - b)‖)
      = w ^ (a + b) * w ^ (i - a) * w ^ (j - b) *
        ((‖A₁ a‖ * ‖A₂ b‖) * (‖L (a + b) e‖ * ‖F₁ (i - a)‖ * ‖F₂ (j - b)‖)) := by ring
    _ ≤ w ^ (a + b) * w ^ (i - a) * w ^ (j - b) *
        (1 * (‖L (a + b) e‖ * (ck (i - a) * X ^ (i - a)) * (ck (j - b) * X ^ (j - b)))) := by
        gcongr
    _ = _ := by rw [mul_pow, mul_pow]; ring

/-- **Weighted local mass**: `Σ w^{i+j}‖γ‖ ≤ 27² Σ_{a,b} w^{a+b}‖L(a+b,e)‖` for `wX ≤ 2/3`. -/
theorem wmassC_le (hX : 0 ≤ X) (hA₁ : ∀ a, ‖A₁ a‖ ≤ 1) (hA₂ : ∀ a, ‖A₂ a‖ ≤ 1)
    (hF₁ : ∀ k, ‖F₁ k‖ ≤ ck k * X ^ k) (hF₂ : ∀ k, ‖F₂ k‖ ≤ ck k * X ^ k)
    {w : ℝ} (hw : 0 ≤ w) (hwX : w * X ≤ 2 / 3) (e N : ℕ) :
    ∑ i ∈ Icc 0 N, ∑ j ∈ Icc 0 N, w ^ (i + j) * ‖γC A₁ A₂ F₁ F₂ L e i j‖ ≤
      729 * ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, w ^ (a + b) * ‖L (a + b) e‖ := by
  have hG := sum_ck_le (by positivity) hwX N
  refine (sum_le_sum fun i _ => sum_le_sum fun j _ =>
    ptC_le hX hA₁ hA₂ hF₁ hF₂ hw e i j).trans ?_
  refine (conv2_le (fun a b => w ^ (a + b) * ‖L (a + b) e‖) (fun k => ck k * (w * X) ^ k)
    (fun a b => by positivity) (fun k => by have := ck_nonneg k; positivity) N).trans ?_
  have hS0 : 0 ≤ ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, w ^ (a + b) * ‖L (a + b) e‖ :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity
  have hG0 : 0 ≤ ∑ k ∈ Icc 0 N, ck k * (w * X) ^ k :=
    sum_nonneg fun k _ => by have := ck_nonneg k; positivity
  have : (∑ k ∈ Icc 0 N, ck k * (w * X) ^ k) ^ 2 ≤ 729 := by nlinarith
  calc _ ≤ (∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, w ^ (a + b) * ‖L (a + b) e‖) * 729 :=
        mul_le_mul_of_nonneg_left this hS0
    _ = _ := by ring

/-! ### Kernel sums -/

variable (hX0 : 0 < X) (hκ : 0 ≤ κ)
  (hL : ∀ n e, ‖L n e‖ ≤ κ * (((n : ℝ) + 1) ^ 2 * X ^ (n - e)))
  (hL0 : ∀ n e, n < e → L n e = 0)
include hX0 hκ hL

lemma ksum0C {w : ℝ} (hw : 0 ≤ w) (hwX : w * X ≤ 2 / 3) (N : ℕ) :
    ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, w ^ (a + b) * ‖L (a + b) 0‖ ≤ 2916 * κ := by
  set F : ℕ → ℝ := fun k => ((k : ℝ) + 1) ^ 2 * (w * X) ^ k
  have hpt : ∀ a b : ℕ, w ^ (a + b) * ‖L (a + b) 0‖ ≤ κ * (F a * F b) := by
    intro a b
    have h1 := hL (a + b) 0
    rw [Nat.sub_zero] at h1
    calc w ^ (a + b) * ‖L (a + b) 0‖
        ≤ w ^ (a + b) * (κ * ((((a + b : ℕ) : ℝ) + 1) ^ 2 * X ^ (a + b))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = κ * ((((a + b : ℕ) : ℝ) + 1) ^ 2 * (w * X) ^ (a + b)) := by rw [mul_pow]; ring
      _ ≤ κ * ((((a : ℝ) + 1) ^ 2 * ((b : ℝ) + 1) ^ 2) * (w * X) ^ (a + b)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (sq_add_le a b) (by positivity)) hκ
      _ = κ * (F a * F b) := by simp only [F]; rw [pow_add]; ring
  calc _ ≤ ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, κ * (F a * F b) :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => hpt a b
    _ = κ * ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, F a * F b := by simp only [mul_sum]
    _ ≤ κ * 54 ^ 2 := mul_le_mul_of_nonneg_left
        (sum_mul_self_le F (fun k => by positivity) N (sum_sq_le' (by positivity) hwX N)) hκ
    _ = 2916 * κ := by ring

include hL0 in
lemma ksum1C {w : ℝ} (hw : 0 ≤ w) (hwX : w * X ≤ 2 / 3) (N : ℕ) :
    ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, w ^ (a + b) * ‖L (a + b) 1‖ ≤ 2916 * κ / X := by
  set F : ℕ → ℝ := fun k => ((k : ℝ) + 1) ^ 2 * (w * X) ^ k
  have hpt : ∀ a b : ℕ, w ^ (a + b) * ‖L (a + b) 1‖ ≤ κ / X * (F a * F b) := by
    intro a b
    have hF : 0 ≤ κ / X * (F a * F b) := by positivity
    rcases Nat.eq_zero_or_pos (a + b) with h0 | hpos
    · rw [h0, hL0 0 1 one_pos, norm_zero, mul_zero]; exact hF
    have h1 := hL (a + b) 1
    have hXn : X ^ (a + b - 1) = X ^ (a + b) / X := by
      obtain ⟨m, hm⟩ : ∃ m, a + b = m + 1 := ⟨a + b - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel, pow_succ]; field_simp
    rw [hXn] at h1
    calc w ^ (a + b) * ‖L (a + b) 1‖
        ≤ w ^ (a + b) * (κ * ((((a + b : ℕ) : ℝ) + 1) ^ 2 * (X ^ (a + b) / X))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = κ / X * ((((a + b : ℕ) : ℝ) + 1) ^ 2 * (w * X) ^ (a + b)) := by
          rw [mul_pow]; field_simp
      _ ≤ κ / X * ((((a : ℝ) + 1) ^ 2 * ((b : ℝ) + 1) ^ 2) * (w * X) ^ (a + b)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (sq_add_le a b) (by positivity))
            (by positivity)
      _ = κ / X * (F a * F b) := by simp only [F]; rw [pow_add]; ring
  calc _ ≤ ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, κ / X * (F a * F b) :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => hpt a b
    _ = κ / X * ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, F a * F b := by simp only [mul_sum]
    _ ≤ κ / X * 54 ^ 2 := mul_le_mul_of_nonneg_left
        (sum_mul_self_le F (fun k => by positivity) N (sum_sq_le' (by positivity) hwX N))
        (by positivity)
    _ = 2916 * κ / X := by ring

include hL0 in
lemma ksumGC (hX1 : X ≤ 2 / 3) (e N : ℕ) :
    ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, (1 : ℝ) ^ (a + b) * ‖L (a + b) e‖ ≤ 2916 * κ * ((e : ℝ) + 1) ^ 6 := by
  have hX1' : X ≤ 1 := by linarith
  set F : ℕ → ℝ := fun k => ((k : ℝ) + 1) ^ 2 * X ^ (k - e)
  have hpt : ∀ a b : ℕ, (1 : ℝ) ^ (a + b) * ‖L (a + b) e‖ ≤ κ * (F a * F b) := by
    intro a b
    rw [one_pow, one_mul]
    have hF : 0 ≤ κ * (F a * F b) := by positivity
    rcases lt_or_ge (a + b) e with hlt | hge
    · rw [hL0 _ _ hlt, norm_zero]; exact hF
    have h1 := hL (a + b) e
    have hXn : X ^ (a + b - e) ≤ X ^ (a - e) * X ^ (b - e) := by
      rw [← pow_add]; exact pow_le_pow_of_le_one hX0.le hX1' (by omega)
    calc ‖L (a + b) e‖ ≤ κ * ((((a + b : ℕ) : ℝ) + 1) ^ 2 * X ^ (a + b - e)) := h1
      _ ≤ κ * ((((a : ℝ) + 1) ^ 2 * ((b : ℝ) + 1) ^ 2) * (X ^ (a - e) * X ^ (b - e))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (sq_add_le a b) hXn (by positivity) (by positivity)) hκ
      _ = κ * (F a * F b) := by simp only [F]; ring
  have hS := sum_sq_shift_le' hX0.le hX1 e N
  calc _ ≤ ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, κ * (F a * F b) :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => hpt a b
    _ = κ * ∑ a ∈ Icc 0 N, ∑ b ∈ Icc 0 N, F a * F b := by simp only [mul_sum]
    _ ≤ κ * (54 * ((e : ℝ) + 1) ^ 3) ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_mul_self_le F (fun k => by positivity) N hS) hκ
    _ = 2916 * κ * ((e : ℝ) + 1) ^ 6 := by ring

/-! ### The local mass bounds -/

variable (hA₁ : ∀ a, ‖A₁ a‖ ≤ 1) (hA₂ : ∀ a, ‖A₂ a‖ ≤ 1)
  (hF₁ : ∀ k, ‖F₁ k‖ ≤ ck k * X ^ k) (hF₂ : ∀ k, ‖F₂ k‖ ≤ ck k * X ^ k)
include hA₁ hA₂ hF₁ hF₂

include hL0 in
/-- **Generic bound** (`L3`-type): `TC e N ≤ 2125764 κ (e+1)^6`. -/
theorem TC_le_gen (hX1 : X ≤ 2 / 3) (e N : ℕ) :
    TC A₁ A₂ F₁ F₂ L e N ≤ 2125764 * κ * ((e : ℝ) + 1) ^ 6 := by
  have h := wmassC_le (L := L) hX0.le hA₁ hA₂ hF₁ hF₂ zero_le_one (by linarith) e N
  have hk := ksumGC hX0 hκ hL hL0 hX1 e N
  simp only [one_pow, one_mul] at h hk
  unfold TC
  nlinarith

/-- **`e = 0` split** (`L1`-type): `TC 0 N ≤ low terms + (9/4)·2125764 κ X²`. -/
theorem TC_zero_split (hX1 : X ≤ 2 / 3) (N : ℕ) :
    TC A₁ A₂ F₁ F₂ L 0 N ≤ ‖γC A₁ A₂ F₁ F₂ L 0 0 0‖ + ‖γC A₁ A₂ F₁ F₂ L 0 1 0‖ +
      ‖γC A₁ A₂ F₁ F₂ L 0 0 1‖ + 4782969 * κ * X ^ 2 := by
  have hw1 := w_ge hX0 hX1
  have hs := split_low (fun i j => ‖γC A₁ A₂ F₁ F₂ L 0 i j‖) (fun _ _ => norm_nonneg _) hw1 N
  have hm := wmassC_le (L := L) hX0.le hA₁ hA₂ hF₁ hF₂ (by linarith) (w_X hX0).le 0 N
  have hk := ksum0C hX0 hκ hL (by linarith) (w_X hX0).le N
  rw [inv_w_sq hX0] at hs
  unfold TC
  have hX2 : 0 ≤ 9 / 4 * X ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left (hm.trans (mul_le_mul_of_nonneg_left hk (by norm_num))) hX2
  nlinarith

include hL0 in
/-- **`e = 1` split** (`L2`-type): `TC 1 N ≤ low terms + (9/4)·2125764 κ X`. -/
theorem TC_one_split (hX1 : X ≤ 2 / 3) (N : ℕ) :
    TC A₁ A₂ F₁ F₂ L 1 N ≤ ‖γC A₁ A₂ F₁ F₂ L 1 0 0‖ + ‖γC A₁ A₂ F₁ F₂ L 1 1 0‖ +
      ‖γC A₁ A₂ F₁ F₂ L 1 0 1‖ + 4782969 * κ * X := by
  have hw1 := w_ge hX0 hX1
  have hs := split_low (fun i j => ‖γC A₁ A₂ F₁ F₂ L 1 i j‖) (fun _ _ => norm_nonneg _) hw1 N
  have hm := wmassC_le (L := L) hX0.le hA₁ hA₂ hF₁ hF₂ (by linarith) (w_X hX0).le 1 N
  have hk := ksum1C hX0 hκ hL hL0 (by linarith) (w_X hX0).le N
  rw [inv_w_sq hX0] at hs
  unfold TC
  have hX2 : 0 ≤ 9 / 4 * X ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left (hm.trans (mul_le_mul_of_nonneg_left hk (by norm_num))) hX2
  have e : 9 / 4 * X ^ 2 * (729 * (2916 * κ / X)) = 4782969 * κ * X := by field_simp; ring
  nlinarith

end Bounds

end RamanujanTau.SvStripD
