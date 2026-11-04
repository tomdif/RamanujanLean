/-
# The higher-order Turán inequality as a Lipschitz condition on the Turán defect

For a positive sequence `α` put

* `tdef α n = 1 − α(n)α(n+2)/α(n+1)²`  (the **Turán defect**; Turán's inequality is `tdef ≥ 0`), and
* `lam α n = 1/√(tdef α n)`.

With `A = tdef α n`, `B = tdef α (n+1)` one has the exact identity (**`hot_eq`**)

  `hot α n = α(n+1)² α(n+2)² · (4AB − (A + B − AB)²)`,

because `α(n)α(n+3)/(α(n+1)α(n+2)) = (1−A)(1−B)`.  For `0 < A, B < 1` the bracket factors as
`(AB − (√A−√B)²)(2√(AB) + 1 − (1−A)(1−B))` with positive second factor, so (**`hot_nonneg_iff_lip`**)

  `hot α n ≥ 0  ⟺  |lam α (n+1) − lam α n| ≤ 1`.

So, given strict Turán inequalities, the higher-order Turán inequalities say exactly that `n ↦ 1/√(Turán defect)`
is 1-Lipschitz.  A convenient sufficient pair (**`lip_of_mono`**): `B ≤ A` and `A ≤ B (1 + √A)²`.
-/
import RamanujanTau.GORZXiD3.Cubic

set_option autoImplicit false

namespace GORZXiD3

open Real

/-- Turán defect `1 − α(n)α(n+2)/α(n+1)²`. -/
noncomputable def tdef (α : ℕ → ℝ) (n : ℕ) : ℝ := 1 - α n * α (n + 2) / α (n + 1) ^ 2

/-- `1/√(Turán defect)`. -/
noncomputable def lam (α : ℕ → ℝ) (n : ℕ) : ℝ := 1 / Real.sqrt (tdef α n)

lemma hot_eq {α : ℕ → ℝ} {n : ℕ} (h1 : α (n + 1) ≠ 0) (h2 : α (n + 2) ≠ 0) :
    hot α n = α (n + 1) ^ 2 * α (n + 2) ^ 2 *
      (4 * tdef α n * tdef α (n + 1) -
        (tdef α n + tdef α (n + 1) - tdef α n * tdef α (n + 1)) ^ 2) := by
  unfold hot tdef
  rw [show n + 1 + 1 = n + 2 by ring, show n + 1 + 2 = n + 3 by ring]
  field_simp
  ring

lemma tdef_lt_one {α : ℕ → ℝ} (hα : ∀ n, 0 < α n) (n : ℕ) : tdef α n < 1 := by
  unfold tdef
  have := hα n; have := hα (n + 1); have := hα (n + 2)
  have : 0 < α n * α (n + 2) / α (n + 1) ^ 2 := by positivity
  linarith

/-- the bracket, in terms of `s = √A`, `t = √B`. -/
lemma bracket_factor (s t : ℝ) :
    4 * s ^ 2 * t ^ 2 - (s ^ 2 + t ^ 2 - s ^ 2 * t ^ 2) ^ 2 =
      (s ^ 2 * t ^ 2 - (s - t) ^ 2) * (2 * s * t + (1 - (1 - s ^ 2) * (1 - t ^ 2))) := by ring

/-- `|1/t − 1/s| ≤ 1 ⟺ |s − t| ≤ st` for `s, t > 0`. -/
lemma lip_iff {s t : ℝ} (hs : 0 < s) (ht : 0 < t) : |1 / t - 1 / s| ≤ 1 ↔ (s - t) ^ 2 ≤ s ^ 2 * t ^ 2 := by
  have e : 1 / t - 1 / s = (s - t) / (s * t) := by field_simp
  have hst : 0 < s * t := mul_pos hs ht
  rw [e, abs_div, abs_of_pos hst, div_le_one hst, ← sq_le_sq₀ (abs_nonneg _) hst.le, sq_abs, mul_pow]

/-- **HOT ⟺ Lipschitz form**, for a positive sequence with strict Turán inequalities at `n`, `n+1`. -/
theorem hot_nonneg_iff_lip {α : ℕ → ℝ} (hα : ∀ n, 0 < α n) {n : ℕ} (hA : 0 < tdef α n)
    (hB : 0 < tdef α (n + 1)) : 0 ≤ hot α n ↔ |lam α (n + 1) - lam α n| ≤ 1 := by
  have hA1 := tdef_lt_one hα n
  have hB1 := tdef_lt_one hα (n + 1)
  set s := Real.sqrt (tdef α n)
  set t := Real.sqrt (tdef α (n + 1))
  have hs : 0 < s := Real.sqrt_pos.2 hA
  have ht : 0 < t := Real.sqrt_pos.2 hB
  have hs2 : s ^ 2 = tdef α n := Real.sq_sqrt hA.le
  have ht2 : t ^ 2 = tdef α (n + 1) := Real.sq_sqrt hB.le
  have hpos : 0 < 2 * s * t + (1 - (1 - s ^ 2) * (1 - t ^ 2)) := by
    have : 0 < (1 - s ^ 2) * (1 - t ^ 2) := by rw [hs2, ht2]; exact mul_pos (by linarith) (by linarith)
    have : (1 - s ^ 2) * (1 - t ^ 2) < 1 := by
      rw [hs2, ht2]; nlinarith
    have : 0 < s * t := mul_pos hs ht
    linarith
  have hc : 0 < α (n + 1) ^ 2 * α (n + 2) ^ 2 := by have := hα (n + 1); have := hα (n + 2); positivity
  rw [hot_eq (hα _).ne' (hα _).ne', ← hs2, ← ht2]
  show _ ↔ |1 / t - 1 / s| ≤ 1
  rw [lip_iff hs ht, mul_nonneg_iff_of_pos_left hc]
  have key := bracket_factor s t
  rw [key, mul_nonneg_iff_of_pos_right hpos]
  constructor <;> intro h <;> linarith

/-- sufficient pair: the defect is nonincreasing and does not collapse faster than `(1+√A)^{-2}`. -/
lemma lip_of_mono {A B : ℝ} (hB : 0 < B) (hBA : B ≤ A) (hc : A ≤ B * (1 + Real.sqrt A) ^ 2) :
    |1 / Real.sqrt B - 1 / Real.sqrt A| ≤ 1 := by
  have hA : 0 < A := lt_of_lt_of_le hB hBA
  have hs : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have ht : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  have hst : Real.sqrt B ≤ Real.sqrt A := Real.sqrt_le_sqrt hBA
  have h2 : Real.sqrt A ≤ Real.sqrt B * (1 + Real.sqrt A) := by
    have := Real.sqrt_le_sqrt hc
    rwa [Real.sqrt_mul hB.le, Real.sqrt_sq (by positivity)] at this
  rw [abs_le]
  constructor
  · have : 1 / Real.sqrt A ≤ 1 / Real.sqrt B := one_div_le_one_div_of_le ht hst
    linarith
  · rw [div_sub_div _ _ ht.ne' hs.ne', div_le_one (mul_pos ht hs)]
    nlinarith

end GORZXiD3
