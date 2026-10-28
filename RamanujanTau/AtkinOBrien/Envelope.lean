/-
# Atkin–O'Brien for ℓ ∈ {13,17,19,23}: the envelope inequalities

For a prime `p ≥ 13` (so `p > 11`) put `s = (p+1)/2` and define the Katz-index envelopes
  `α(i) = ⌈(p i − 2)/(p+1)⌉`, `β(i) = ⌈(p i − 2 − s)/(p+1)⌉`,
and the matrix bounds
  `u(i,j) = ⌈(p i − j)/(p+1)⌉ − 1`  (for `U`, Katz/Wan/Vonk), `d(i,j) = ⌈(p i − j − s)/(p+1)⌉ − 1` (for `D`).
These are the inequalities that make the envelopes stable: for all `i, j`,
* `U` contracts `β` (offset 2) into `α` (offset 1), and preserves offset 1;
* `D` contracts `α` (offset 2) into `β` (offset 1), and preserves offset 1;
* `α(i), β(i) ≥ 2` for `i ≥ 2` (so the leading digit after a step lives in `S_{p−1}`).
See `docs/ATKIN_OBRIEN_PROOF.md`, Step 2.
-/
import Mathlib

set_option autoImplicit false

namespace AtkinOBrien

variable (p : ℕ)

noncomputable def s : ℚ := ((p : ℚ) + 1) / 2
noncomputable def α (i : ℕ) : ℤ := ⌈((p : ℚ) * i - 2) / (p + 1)⌉
noncomputable def β (i : ℕ) : ℤ := ⌈((p : ℚ) * i - 2 - s p) / (p + 1)⌉
noncomputable def u (i j : ℕ) : ℤ := ⌈((p : ℚ) * i - j) / (p + 1)⌉ - 1
noncomputable def d (i j : ℕ) : ℤ := ⌈((p : ℚ) * i - j - s p) / (p + 1)⌉ - 1

variable {p}

lemma ceil_mono_sub {x y : ℚ} (h : y ≤ x) : ⌈y⌉ ≤ ⌈x⌉ := Int.ceil_mono h

/-- if an integer exceeds `x − 1` then it is at least `⌈x⌉ − 1`. -/
lemma ge_ceil_sub_one {n : ℤ} {x : ℚ} (h : x - 1 < n) : ⌈x⌉ - 1 ≤ n := by
  have : ⌈x⌉ ≤ n + 1 := Int.ceil_le.mpr (by push_cast; linarith)
  linarith

lemma pos_p1 (hp : 13 ≤ p) : (0 : ℚ) < p + 1 := by positivity

/-- the generic `j ≥ 3` estimate: `γ(j) − c + m(i,j) > γ'(i) − 1`. -/
lemma key_large (hp : 13 ≤ p) (i j : ℕ) (hj : 3 ≤ j) (a b c : ℚ) (hc : c ≤ 2)
    (hab : b ≤ (p + 1) / 2) :
    ((p : ℚ) * i - 2 - a) / (p + 1) - 1 <
      ((p : ℚ) * j - 2 - b) / (p + 1) - c + (((p : ℚ) * i - j - a) / (p + 1) - 1) := by
  have hp' : (13 : ℚ) ≤ p := by exact_mod_cast hp
  have hj' : (3 : ℚ) ≤ j := by exact_mod_cast hj
  have hpos : (0 : ℚ) < p + 1 := by linarith
  rw [← sub_pos]
  have : ((p : ℚ) * j - 2 - b) / (p + 1) - c + (((p : ℚ) * i - j - a) / (p + 1) - 1) -
      (((p : ℚ) * i - 2 - a) / (p + 1) - 1) = (((p : ℚ) - 1) * j - b) / (p + 1) - c := by
    field_simp; ring
  rw [this, sub_pos, lt_div_iff₀ hpos]
  have h3 : ((p : ℚ) - 1) * 3 ≤ ((p : ℚ) - 1) * j := mul_le_mul_of_nonneg_left hj' (by linarith)
  nlinarith

/-- **U: β-envelope with offset `c ≤ 2` ↦ α-envelope with offset 1** (the `j`-minimum is ≥ `α(i) − 1`). -/
theorem U_step (hp : 13 ≤ p) (c : ℤ) (hc2 : c ≤ 2) (i j : ℕ) :
    α p i - 1 ≤ max 0 (β p j - c) + u p i j := by
  have hpos := pos_p1 hp
  rcases Nat.lt_or_ge j 3 with hj | hj
  · -- small j: u(i,j) ≥ u(i,2) = α(i) − 1
    have : α p i - 1 ≤ u p i j := by
      unfold α u
      have : ((p : ℚ) * i - 2) / (p + 1) ≤ ((p : ℚ) * i - j) / (p + 1) := by
        apply div_le_div_of_nonneg_right _ hpos.le
        have : (j : ℚ) ≤ 2 := by exact_mod_cast (by omega : j ≤ 2)
        linarith
      linarith [Int.ceil_mono this]
    linarith [le_max_left 0 (β p j - c)]
  · have h := key_large hp i j hj 0 (s p) (c : ℚ) (by exact_mod_cast hc2) (by unfold s; linarith)
    have hb : ((p : ℚ) * j - 2 - s p) / (p + 1) ≤ β p j := Int.le_ceil _
    have hu : ((p : ℚ) * i - j - 0) / (p + 1) - 1 ≤ u p i j := by
      unfold u; simp only [sub_zero]; push_cast; linarith [Int.le_ceil (((p : ℚ) * i - j) / (p + 1))]
    have : ((p : ℚ) * i - 2 - 0) / (p + 1) - 1 < ((max 0 (β p j - c) + u p i j : ℤ) : ℚ) := by
      push_cast
      have := le_max_right (0 : ℤ) (β p j - c)
      have : ((β p j - c : ℤ) : ℚ) ≤ ((max 0 (β p j - c) : ℤ) : ℚ) := by exact_mod_cast this
      push_cast at this
      linarith
    have := ge_ceil_sub_one this
    simp only [sub_zero] at this
    unfold α; exact this

/-- **D: α-envelope with offset `c ≤ 2` ↦ β-envelope with offset 1**. -/
theorem D_step (hp : 13 ≤ p) (c : ℤ) (hc2 : c ≤ 2) (i j : ℕ) :
    β p i - 1 ≤ max 0 (α p j - c) + d p i j := by
  have hpos := pos_p1 hp
  rcases Nat.lt_or_ge j 3 with hj | hj
  · have : β p i - 1 ≤ d p i j := by
      unfold β d
      have : ((p : ℚ) * i - 2 - s p) / (p + 1) ≤ ((p : ℚ) * i - j - s p) / (p + 1) := by
        apply div_le_div_of_nonneg_right _ hpos.le
        have : (j : ℚ) ≤ 2 := by exact_mod_cast (by omega : j ≤ 2)
        linarith
      linarith [Int.ceil_mono this]
    linarith [le_max_left 0 (α p j - c)]
  · have hs0 : 0 ≤ s p := by unfold s; positivity
    have h := key_large hp i j hj (s p) 0 (c : ℚ) (by exact_mod_cast hc2) (by linarith)
    have hb : ((p : ℚ) * j - 2 - 0) / (p + 1) ≤ α p j := by
      unfold α; simp only [sub_zero]; exact Int.le_ceil _
    have hu : ((p : ℚ) * i - j - s p) / (p + 1) - 1 ≤ d p i j := by
      unfold d; push_cast; linarith [Int.le_ceil (((p : ℚ) * i - j - s p) / (p + 1))]
    have : ((p : ℚ) * i - 2 - s p) / (p + 1) - 1 < ((max 0 (α p j - c) + d p i j : ℤ) : ℚ) := by
      push_cast
      have := le_max_right (0 : ℤ) (α p j - c)
      have : ((α p j - c : ℤ) : ℚ) ≤ ((max 0 (α p j - c) : ℤ) : ℚ) := by exact_mod_cast this
      push_cast at this
      linarith
    exact ge_ceil_sub_one this

/-- the envelopes are `≥ 2` from index 2 on. -/
theorem envelopes_ge_two (hp : 13 ≤ p) (i : ℕ) (hi : 2 ≤ i) : 2 ≤ α p i ∧ 2 ≤ β p i := by
  have hp' : (13 : ℚ) ≤ p := by exact_mod_cast hp
  have hi' : (2 : ℚ) ≤ i := by exact_mod_cast hi
  have hpos : (0 : ℚ) < p + 1 := by linarith
  have h1 : (1 : ℚ) < ((p : ℚ) * i - 2 - s p) / (p + 1) := by
    rw [lt_div_iff₀ hpos]; unfold s; nlinarith
  have h2 : ((p : ℚ) * i - 2 - s p) / (p + 1) ≤ ((p : ℚ) * i - 2) / (p + 1) := by
    apply div_le_div_of_nonneg_right _ hpos.le; unfold s; linarith
  constructor
  · have : (1 : ℤ) < α p i := Int.lt_ceil.mpr (by push_cast; linarith)
    omega
  · have : (1 : ℤ) < β p i := Int.lt_ceil.mpr (by push_cast; linarith)
    omega

end AtkinOBrien
