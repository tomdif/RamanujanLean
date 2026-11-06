/-
# `SCS2Coprime/` checkpoint 3: the two-sided shifted-convolution bound (all `a, b ≥ 1`)

Build: `nice -n 10 lake build RamanujanTau.SCS2Coprime.Main3`. See `docs/SCS2.md` §8.

* **`scs2_general`**: for all `a, b ≥ 1`, `ℓ ≠ 0`, `N`,
  `|Σ_{m,n≤N, am−bn=ℓ} λ(m)λ(n)| ≤ C N^{1−1/21} |ℓ|^{1/21} (ab)¹²`
  (coprimality is **not** needed: `Ψ_{a,b}` is `Γ₀(ab)`-invariant for all `a, b`);
* `scs2_gcd`: the same with `(a, b, ℓ)` replaced by `(a/g, b/g, ℓ/g)`, `g = gcd(a,b)`
  (via the committed `SCS2.shiftSum2_mul_left`; the sum vanishes unless `g ∣ ℓ`);
* **`scs2_range`**: for `0 ≤ θ ≤ 1` and `|ℓ| ≤ N^{1−θ}`: `|S| ≤ C N^{1−θ/21} (ab)¹²`.
-/
import RamanujanTau.SCS2Coprime.FinalAB

set_option autoImplicit false

namespace RamanujanTau.SCS2Coprime

open Finset
open RamanujanTau.SubconvexityCond RamanujanTau.HeckeAFE

/-- `S(a, b; −ℓ) = S(b, a; ℓ)`. -/
lemma shiftSum2_neg (a b : ℕ) (ℓ : ℤ) (N : ℕ) :
    shiftSum2 a b (-ℓ) N = shiftSum2 b a ℓ N := by
  unfold shiftSum2
  rw [sum_comm]
  refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
  by_cases h : (a : ℤ) * n - b * m = -ℓ
  · rw [if_pos h, if_pos (by linarith)]; ring
  · rw [if_neg h, if_neg (by intro h'; apply h; linarith)]

/-- **The two-sided shifted-convolution bound**, all `a, b ≥ 1`, `ℓ ≠ 0`. -/
theorem scs2_general : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℕ) (ℓ : ℤ) (N : ℕ), 1 ≤ a → 1 ≤ b → ℓ ≠ 0 →
    |shiftSum2 a b ℓ N| ≤
      C * (N : ℝ) ^ (1 - 1 / 21 : ℝ) * |(ℓ : ℝ)| ^ (1 / 21 : ℝ) * ((a * b : ℕ) : ℝ) ^ 12 := by
  obtain ⟨C, hC0, hC⟩ := shiftSum2_bound_pos
  refine ⟨C, hC0, fun a b ℓ N ha hb hℓ => ?_⟩
  set h := ℓ.natAbs with hh
  have hh1 : 1 ≤ h := Int.natAbs_pos.2 hℓ
  have habs : |(ℓ : ℝ)| = (h : ℝ) := by rw [hh, Nat.cast_natAbs, Int.cast_abs]
  rw [habs]
  rcases le_or_gt 0 ℓ with hl | hl
  · have e : ℓ = (h : ℤ) := by rw [hh]; omega
    rw [e]
    have := hC ⟨a, ha⟩ ⟨b, hb⟩ h N hh1
    simpa [mul_comm] using this
  · have e : ℓ = -(h : ℤ) := by rw [hh]; omega
    rw [e, shiftSum2_neg]
    have := hC ⟨b, hb⟩ ⟨a, ha⟩ h N hh1
    have e2 : ((a * b : ℕ) : ℝ) = (b : ℝ) * a := by push_cast; ring
    rw [e2]
    simpa using this

/-- **gcd-refined form**: with `g = gcd(a,b)`, `a = g a'`, `b = g b'`, `ℓ = g ℓ'`. -/
theorem scs2_gcd : ∃ C : ℝ, 0 ≤ C ∧ ∀ (g a b : ℕ) (ℓ : ℤ) (N : ℕ), 1 ≤ g → 1 ≤ a → 1 ≤ b →
    ℓ ≠ 0 → |shiftSum2 (g * a) (g * b) (g * ℓ) N| ≤
      C * (N : ℝ) ^ (1 - 1 / 21 : ℝ) * |(ℓ : ℝ)| ^ (1 / 21 : ℝ) * ((a * b : ℕ) : ℝ) ^ 12 := by
  obtain ⟨C, hC0, hC⟩ := scs2_general
  refine ⟨C, hC0, fun g a b ℓ N hg ha hb hℓ => ?_⟩
  rw [RamanujanTau.SCS2.shiftSum2_mul_left g a b hg ℓ N]
  exact hC a b ℓ N ha hb hℓ

/-- **Restricted range**: `|ℓ| ≤ N^{1−θ}` gives the power saving `N^{1−θ/21}`. -/
theorem scs2_range : ∃ C : ℝ, 0 ≤ C ∧ ∀ (θ : ℝ), 0 ≤ θ → θ ≤ 1 →
    ∀ (a b : ℕ) (ℓ : ℤ) (N : ℕ), 1 ≤ a → 1 ≤ b → ℓ ≠ 0 →
      |(ℓ : ℝ)| ≤ (N : ℝ) ^ (1 - θ) →
      |shiftSum2 a b ℓ N| ≤ C * (N : ℝ) ^ (1 - θ / 21) * ((a * b : ℕ) : ℝ) ^ 12 := by
  obtain ⟨C, hC0, hC⟩ := scs2_general
  refine ⟨C, hC0, fun θ hθ0 hθ1 a b ℓ N ha hb hℓ hR => ?_⟩
  have hab : 0 ≤ ((a * b : ℕ) : ℝ) ^ 12 := by positivity
  have hℓ1 : (1 : ℝ) ≤ |(ℓ : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hℓ
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  rcases eq_or_lt_of_le hN0 with hN | hN
  · -- `N = 0` forces `|ℓ| ≤ 0^{1−θ} ≤ 1`, and the sum is empty
    have hN' : N = 0 := by exact_mod_cast hN.symm
    have : shiftSum2 a b ℓ N = 0 := by rw [hN']; simp [shiftSum2]
    rw [this, abs_zero]; positivity
  refine (hC a b ℓ N ha hb hℓ).trans ?_
  have hp : |(ℓ : ℝ)| ^ (1 / 21 : ℝ) ≤ ((N : ℝ) ^ (1 - θ)) ^ (1 / 21 : ℝ) :=
    Real.rpow_le_rpow (abs_nonneg _) hR (by norm_num)
  have e : (N : ℝ) ^ (1 - 1 / 21 : ℝ) * ((N : ℝ) ^ (1 - θ)) ^ (1 / 21 : ℝ) =
      (N : ℝ) ^ (1 - θ / 21) := by
    rw [← Real.rpow_mul hN0, ← Real.rpow_add hN]; ring_nf
  calc C * (N : ℝ) ^ (1 - 1 / 21 : ℝ) * |(ℓ : ℝ)| ^ (1 / 21 : ℝ) * ((a * b : ℕ) : ℝ) ^ 12
      ≤ C * (N : ℝ) ^ (1 - 1 / 21 : ℝ) * ((N : ℝ) ^ (1 - θ)) ^ (1 / 21 : ℝ) *
          ((a * b : ℕ) : ℝ) ^ 12 := by gcongr
    _ = C * (N : ℝ) ^ (1 - θ / 21) * ((a * b : ℕ) : ℝ) ^ 12 := by
        rw [mul_assoc C, e]

end RamanujanTau.SCS2Coprime

-- item 2 (Hölder on `Γ₀(ab)\(ℍ×ℍ)`)
#print axioms RamanujanTau.SCS2Coprime.tsum_coset
#print axioms RamanujanTau.SCS2Coprime.lintegral_SQ_le
#print axioms RamanujanTau.SCS2Coprime.norm_QAB_le
-- item 3 (`Q_eq`, pointwise bound)
#print axioms RamanujanTau.SCS2Coprime.Q_eqAB
#print axioms RamanujanTau.SCS2Coprime.main_term_leAB
#print axioms RamanujanTau.SCS2Coprime.GAB_eq
#print axioms RamanujanTau.SCS2Coprime.cR_laplace
#print axioms RamanujanTau.SCS2Coprime.pointwise_parAB
#print axioms RamanujanTau.SCS2Coprime.pointwise_Gc
-- item 4 (Tauberian, Rankin along the progression, Abel)
#print axioms RamanujanTau.SCS2Coprime.laplace_rieszC
#print axioms RamanujanTau.SCS2Coprime.AsumC_bound
#print axioms RamanujanTau.SCS2Coprime.short_cR
#print axioms RamanujanTau.SCS2Coprime.sum_cR_cs
#print axioms RamanujanTau.SCS2Coprime.AsumAB_bound
#print axioms RamanujanTau.SCS2Coprime.shiftSum2_eq
#print axioms RamanujanTau.SCS2Coprime.shiftSum2_bound_pos
-- headlines
#print axioms RamanujanTau.SCS2Coprime.scs2_general
#print axioms RamanujanTau.SCS2Coprime.scs2_gcd
#print axioms RamanujanTau.SCS2Coprime.scs2_range
