/-
# Uniform `Γ`-ratio bounds in vertical strips

From `Stirling.norm_Gamma_ratio_le_of_le/ge`:

* `norm_Gamma_ratio_unif`: for `1 ≤ Re z, Re w ≤ R` and `|Im z| = |Im w| = |t|`,
  `‖Γ(z)‖ ≤ C_R (1+|t|)^{Re z − Re w} ‖Γ(w)‖` with `C_R` independent of `z, w`;
* `inv_Gamma_eq_prod`: `Γ(z)⁻¹ = (∏_{i<N} (z+i)) Γ(z+N)⁻¹` for **all** `z` (Mathlib's
  `Γ(−n) = 0` convention makes this an identity of entire functions).
-/
import RamanujanTau.Stirling.GammaRatio

set_option autoImplicit false

namespace RamanujanTau.RankinLandau

open Complex Real Finset RamanujanTau.Stirling

lemma norm_Gamma_conj (z : ℂ) : ‖Complex.Gamma ((starRingEnd ℂ) z)‖ = ‖Complex.Gamma z‖ := by
  rw [Complex.Gamma_conj, Complex.norm_conj]

/-- `‖Γ(z)‖` depends only on `Re z` and `|Im z|`. -/
lemma norm_Gamma_eq_of_abs_im (z : ℂ) :
    ‖Complex.Gamma z‖ = ‖Complex.Gamma ((z.re : ℂ) + |z.im| * I)‖ := by
  rcases le_or_gt 0 z.im with h | h
  · rw [abs_of_nonneg h, Complex.re_add_im]
  · rw [abs_of_neg h, ← norm_Gamma_conj]
    congr 2
    apply Complex.ext <;> simp

/-- **Uniform ratio bound.** -/
theorem norm_Gamma_ratio_unif {R : ℝ} (hR : 1 ≤ R) : ∃ C : ℝ, 0 < C ∧
    ∀ α β t : ℝ, 1 ≤ α → α ≤ R → 1 ≤ β → β ≤ R →
      ‖Complex.Gamma (α + t * I)‖ ≤ C * (1 + |t|) ^ (α - β) * ‖Complex.Gamma (β + t * I)‖ := by
  set n : ℕ := ⌈R⌉₊ with hn
  have hnR : R ≤ n := Nat.le_ceil R
  set C : ℝ := ((n + 1).factorial : ℝ) * Real.exp 10 * R ^ R * 2 ^ R + Real.exp 10 * 2 ^ R
    with hC
  have hRR : 1 ≤ R ^ R := Real.one_le_rpow hR (by linarith)
  have h2R : 1 ≤ (2 : ℝ) ^ R := Real.one_le_rpow (by norm_num) (by linarith)
  have hC1 : 0 ≤ ((n + 1).factorial : ℝ) * Real.exp 10 * R ^ R * 2 ^ R := by positivity
  refine ⟨C, by positivity, fun α β t hα1 hαR hβ1 hβR => ?_⟩
  have ht : (0 : ℝ) < 1 + |t| := by positivity
  rcases le_total β α with hβα | hαβ
  · have h := norm_Gamma_ratio_le_of_le hβ1 hβα n (by linarith) t
    have hb : ‖(β : ℂ) + t * I‖ ≤ R * (1 + |t|) := by
      calc ‖(β : ℂ) + t * I‖ ≤ ‖(β : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = β + |t| := by simp [abs_of_nonneg (by linarith : (0:ℝ) ≤ β)]
        _ ≤ R * (1 + |t|) := by nlinarith [abs_nonneg t]
    have hpow : ‖(β : ℂ) + t * I‖ ^ (α - β) ≤ R ^ R * (1 + |t|) ^ (α - β) := by
      calc ‖(β : ℂ) + t * I‖ ^ (α - β) ≤ (R * (1 + |t|)) ^ (α - β) :=
            Real.rpow_le_rpow (norm_nonneg _) hb (by linarith)
        _ = R ^ (α - β) * (1 + |t|) ^ (α - β) := Real.mul_rpow (by linarith) ht.le
        _ ≤ R ^ R * (1 + |t|) ^ (α - β) :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hR (by linarith))
              (by positivity)
    calc ‖Complex.Gamma (α + t * I)‖
        ≤ ((n + 1).factorial : ℝ) * Real.exp 10 * ‖(β : ℂ) + t * I‖ ^ (α - β) *
          ‖Complex.Gamma (β + t * I)‖ := h
      _ ≤ ((n + 1).factorial : ℝ) * Real.exp 10 * (R ^ R * (1 + |t|) ^ (α - β)) *
          ‖Complex.Gamma (β + t * I)‖ := by gcongr
      _ ≤ C * (1 + |t|) ^ (α - β) * ‖Complex.Gamma (β + t * I)‖ := by
          have : ((n + 1).factorial : ℝ) * Real.exp 10 * R ^ R ≤ C := by
            have := mul_le_mul_of_nonneg_left h2R
              (by positivity : (0:ℝ) ≤ ((n + 1).factorial : ℝ) * Real.exp 10 * R ^ R)
            rw [hC]; nlinarith [Real.exp_pos 10]
          have h0 : 0 ≤ (1 + |t|) ^ (α - β) * ‖Complex.Gamma (β + t * I)‖ := by positivity
          nlinarith
  · have h := norm_Gamma_ratio_le_of_ge hα1 hαβ t
    have hb : (1 + |t|) / 2 ≤ ‖(α : ℂ) + t * I‖ := by
      have h1 : |t| ≤ ‖(α : ℂ) + t * I‖ := by
        have := Complex.abs_im_le_norm ((α : ℂ) + t * I); simpa using this
      have h2 : α ≤ ‖(α : ℂ) + t * I‖ := by
        have := Complex.abs_re_le_norm ((α : ℂ) + t * I)
        simp at this; linarith [le_abs_self α]
      linarith
    have hpow : ‖(α : ℂ) + t * I‖ ^ (α - β) ≤ 2 ^ R * (1 + |t|) ^ (α - β) := by
      calc ‖(α : ℂ) + t * I‖ ^ (α - β) ≤ ((1 + |t|) / 2) ^ (α - β) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hb (by linarith)
        _ = (2 : ℝ) ^ (β - α) * (1 + |t|) ^ (α - β) := by
            rw [Real.div_rpow ht.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
            ring_nf
        _ ≤ 2 ^ R * (1 + |t|) ^ (α - β) := by
            gcongr
            · norm_num
            · linarith
    calc ‖Complex.Gamma (α + t * I)‖
        ≤ Real.exp 10 * ‖(α : ℂ) + t * I‖ ^ (α - β) * ‖Complex.Gamma (β + t * I)‖ := h
      _ ≤ Real.exp 10 * (2 ^ R * (1 + |t|) ^ (α - β)) * ‖Complex.Gamma (β + t * I)‖ := by
          gcongr
      _ ≤ C * (1 + |t|) ^ (α - β) * ‖Complex.Gamma (β + t * I)‖ := by
          have : Real.exp 10 * 2 ^ R ≤ C := by rw [hC]; linarith
          have h0 : 0 ≤ (1 + |t|) ^ (α - β) * ‖Complex.Gamma (β + t * I)‖ := by positivity
          nlinarith

/-- The same, for complex arguments with `|Im z| = |Im w|`. -/
theorem norm_Gamma_ratio_unif' {R : ℝ} (hR : 1 ≤ R) : ∃ C : ℝ, 0 < C ∧
    ∀ z w : ℂ, 1 ≤ z.re → z.re ≤ R → 1 ≤ w.re → w.re ≤ R → |z.im| = |w.im| →
      ‖Complex.Gamma z‖ ≤ C * (1 + |w.im|) ^ (z.re - w.re) * ‖Complex.Gamma w‖ := by
  obtain ⟨C, hC0, hC⟩ := norm_Gamma_ratio_unif hR
  refine ⟨C, hC0, fun z w hz1 hzR hw1 hwR him => ?_⟩
  have := hC z.re w.re |w.im| hz1 hzR hw1 hwR
  rw [abs_abs] at this
  rw [norm_Gamma_eq_of_abs_im z, norm_Gamma_eq_of_abs_im w, him]
  exact this

lemma inv_Gamma_eq_mul (w : ℂ) : (Complex.Gamma w)⁻¹ = w * (Complex.Gamma (w + 1))⁻¹ := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [Complex.Gamma_zero]
  · rw [Complex.Gamma_add_one w hw, mul_inv, ← mul_assoc, mul_inv_cancel₀ hw, one_mul]

/-- `Γ(z)⁻¹ = (∏_{i<N} (z+i)) Γ(z+N)⁻¹` for all `z`. -/
lemma inv_Gamma_eq_prod (z : ℂ) (N : ℕ) :
    (Complex.Gamma z)⁻¹ = (∏ i ∈ range N, (z + i)) * (Complex.Gamma (z + N))⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, inv_Gamma_eq_mul (z + N), prod_range_succ]
    push_cast
    ring_nf

lemma norm_prod_add_le (z : ℂ) (N : ℕ) {R : ℝ} (hR1 : 1 ≤ R) (hR : |z.re| + N ≤ R) :
    ‖∏ i ∈ range N, (z + i)‖ ≤ (R * (1 + |z.im|)) ^ N := by
  rw [norm_prod]
  calc ∏ i ∈ range N, ‖z + i‖ ≤ ∏ _i ∈ range N, R * (1 + |z.im|) := by
        refine prod_le_prod (fun _ _ => norm_nonneg _) (fun i hi => ?_)
        have hi' : (i : ℝ) ≤ N := by exact_mod_cast (mem_range.1 hi).le
        calc ‖z + i‖ ≤ |z.re + i| + |z.im| := by
              have := Complex.norm_le_abs_re_add_abs_im (z + i); simpa using this
          _ ≤ |z.re| + N + |z.im| := by
              have := abs_add_le z.re (i : ℝ)
              rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) i)] at this; linarith
          _ ≤ R + R * |z.im| := by
              nlinarith [abs_nonneg z.im]
          _ = R * (1 + |z.im|) := by ring
    _ = (R * (1 + |z.im|)) ^ N := by rw [prod_const, card_range]

end RamanujanTau.RankinLandau

#print axioms RamanujanTau.RankinLandau.norm_Gamma_ratio_unif'
#print axioms RamanujanTau.RankinLandau.inv_Gamma_eq_prod
