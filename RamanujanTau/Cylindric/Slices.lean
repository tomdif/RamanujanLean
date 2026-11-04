import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Normalized height slices for cylindric partitions

Conjugating each row turns a cylindric partition with entries at most `N`
into `N` componentwise decreasing height vectors. Each vector decomposes
uniquely into a normalized vector (one zero coordinate) and a common offset.
`shift_le_iff` identifies the exact transition cost between normalized slices.

These lemmas justify the local offset step of `scripts/cylindric_positivity.py`.
The full infinite generating-function identity and Warnaar positivity are not
proved in this module. This module is not yet in the public root import graph.
-/

namespace Cylindric

variable {ι : Type*} [Fintype ι]

def shift (u : ι → ℕ) (k : ℕ) : ι → ℕ := fun i => u i + k

def Normalized (u : ι → ℕ) : Prop := ∃ i, u i = 0

/-- The row-height form of the outgoing cylinder inequalities. -/
def Admissible (next : ι → ι) (c u : ι → ℕ) : Prop :=
  ∀ i, u (next i) ≤ u i + c i

omit [Fintype ι] in
/-- Adding or removing a common offset preserves every cylinder inequality. -/
theorem admissible_shift_iff (next : ι → ι) (c u : ι → ℕ) (k : ℕ) :
    Admissible next c (shift u k) ↔ Admissible next c u := by
  simp only [Admissible, shift]
  constructor <;> intro h i <;> have := h i <;> omega

/-- Every nonempty finite height vector has a normalized representative. -/
theorem exists_normalized_shift [Nonempty ι] (h : ι → ℕ) :
    ∃ u k, Normalized u ∧ shift u k = h := by
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image Finset.univ h Finset.univ_nonempty
  refine ⟨fun j => h j - h i, h i, ⟨i, by simp⟩, ?_⟩
  funext j
  have hj := hmin j (Finset.mem_univ j)
  simp only [shift]
  omega

omit [Fintype ι] in
/-- Neither the normalized slice nor its common offset is arbitrary. -/
theorem normalized_shift_unique (u v : ι → ℕ) (k l : ℕ)
    (hu : Normalized u) (hv : Normalized v) (heq : shift u k = shift v l) :
    u = v ∧ k = l := by
  obtain ⟨i, hi⟩ := hu
  obtain ⟨j, hj⟩ := hv
  have ei := congrFun heq i
  have ej := congrFun heq j
  simp only [shift, hi, hj, zero_add] at ei ej
  have hkl : k = l := by omega
  refine ⟨?_, hkl⟩
  funext t
  have et := congrFun heq t
  simp only [shift] at et
  omega

/-- Minimal additional offset needed when the next normalized slice is `v`. -/
def jump (u v : ι → ℕ) : ℕ := Finset.univ.sup fun i => v i - u i

/-- Exact local transition, including necessity at a zero coordinate of `u`. -/
theorem shift_le_iff (u v : ι → ℕ) (k l : ℕ) (hu : Normalized u) :
    (∀ i, shift v l i ≤ shift u k i) ↔ l + jump u v ≤ k := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := hu
    have hz := h i
    simp only [shift, hi, zero_add] at hz
    have hcost : jump u v ≤ k - l := by
      apply Finset.sup_le
      intro j _
      have hj := h j
      simp only [shift] at hj
      omega
    omega
  · intro h i
    have hi : v i - u i ≤ jump u v := by
      exact Finset.le_sup (f := fun j => v j - u j) (Finset.mem_univ i)
    simp only [shift]
    omega

/-- Offsets for a transition are precisely its cost plus a nonnegative slack. -/
theorem shift_le_iff_exists_slack (u v : ι → ℕ) (k l : ℕ) (hu : Normalized u) :
    (∀ i, shift v l i ≤ shift u k i) ↔ ∃ slack, k = l + jump u v + slack := by
  rw [shift_le_iff u v k l hu]
  constructor
  · intro h
    exact ⟨k - (l + jump u v), by omega⟩
  · rintro ⟨slack, h⟩
    omega

/-- The offset contributes exactly `rank * k` boxes to the slice volume. -/
theorem shift_volume (u : ι → ℕ) (k : ℕ) :
    ∑ i, shift u k i = (∑ i, u i) + Fintype.card ι * k := by
  simp [shift, Finset.sum_add_distrib]

end Cylindric
