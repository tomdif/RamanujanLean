/-
# Amplification: from `|α^r + β^r| ≪ p^{r/2}` (all large `r`) to `|α|, |β| ≤ √p`

Pure complex analysis, independent of finite fields.  If `αβ = p` and
`|α^r + β^r| ≤ C p^{r/2}` for all `r ≥ r₀` (any `C`, any `r₀`), then `|α| = |β| = √p`,
so `|α + β| ≤ 2√p`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.KloostermanL

/-- If `‖α‖‖β‖ = s²` and `‖α^r+β^r‖ ≤ C s^r` for all `r ≥ r₀`, then `‖α‖ ≤ s`. -/
theorem norm_le_of_powSum_bound {α β : ℂ} {s C : ℝ} (hs : 0 < s) (hαβ : ‖α‖ * ‖β‖ = s ^ 2)
    (r₀ : ℕ) (hb : ∀ r, r₀ ≤ r → ‖α ^ r + β ^ r‖ ≤ C * s ^ r) : ‖α‖ ≤ s := by
  by_contra h
  rw [not_le] at h
  have hβ : ‖β‖ ≤ s := by
    by_contra h2
    rw [not_le] at h2
    nlinarith [norm_nonneg α, norm_nonneg β, mul_lt_mul'' h h2 hs.le hs.le]
  set t := ‖α‖ / s with ht_def
  have ht : 1 < t := (one_lt_div hs).2 h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C + 1) ht
  set m := n + r₀ with hm
  have key := hb m (by omega)
  have h1 : ‖α‖ ^ m - ‖β‖ ^ m ≤ C * s ^ m := by
    have := norm_sub_norm_le (α ^ m) (-(β ^ m))
    rw [norm_neg, sub_neg_eq_add, norm_pow, norm_pow] at this
    linarith
  have h2 : ‖β‖ ^ m ≤ s ^ m := pow_le_pow_left₀ (norm_nonneg _) hβ _
  have h3 : ‖α‖ ^ m = t ^ m * s ^ m := by
    rw [← mul_pow, ht_def, div_mul_cancel₀ _ hs.ne']
  have h4 : t ^ n ≤ t ^ m := pow_le_pow_right₀ ht.le (by omega)
  have hsp : 0 < s ^ m := pow_pos hs _
  nlinarith

/-- **Amplification.** `αβ = p > 0` and `‖α^r+β^r‖ ≤ C (√p)^r` for all `r ≥ r₀` imply
`‖α‖ ≤ √p`, `‖β‖ ≤ √p` and `‖α + β‖ ≤ 2√p`. -/
theorem norm_add_le_two_sqrt_of_powSum_bound {α β : ℂ} {p C : ℝ} (hp : 0 < p)
    (hαβ : α * β = p) (r₀ : ℕ) (hb : ∀ r, r₀ ≤ r → ‖α ^ r + β ^ r‖ ≤ C * Real.sqrt p ^ r) :
    ‖α‖ ≤ Real.sqrt p ∧ ‖β‖ ≤ Real.sqrt p ∧ ‖α + β‖ ≤ 2 * Real.sqrt p := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  have hn : ‖α‖ * ‖β‖ = Real.sqrt p ^ 2 := by
    rw [← norm_mul, hαβ, Real.sq_sqrt hp.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hp]
  have hA := norm_le_of_powSum_bound hs hn r₀ hb
  have hB := norm_le_of_powSum_bound (α := β) (β := α) hs (by rw [mul_comm]; exact hn) r₀
    (fun r hr => by rw [add_comm]; exact hb r hr)
  exact ⟨hA, hB, (norm_add_le _ _).trans (by linarith)⟩

end RamanujanTau.KloostermanL
