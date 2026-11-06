/-
# The cancellation input: `J(x) = Σ_{m≤x} (fR(m)/m) log(x/m) ≪ (1 + log x)^{1/2}`

`fR` = coefficients of `R(s)^{−1/2}` (`SelbergDelange3.fR`, unconditional).  The trivial bound is
`(log x)^{3/2}`; the saving of a full `log x` is the Selberg–Delange cancellation of
`selberg_sum_fR`.  This is the **only** analytic (cancellation) input of the `Q⁰`, `Q¹` bounds.
-/
import RamanujanTau.SelbergDelange3.Selberg

set_option autoImplicit false

namespace RamanujanTau.QFProof

open Finset
open RamanujanTau.SelbergDelange2 (Isum)
open RamanujanTau.SelbergDelange3 (fR selberg_sum_fR)

lemma sqrt4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num

lemma Isum_le_trivial {x X : ℝ} (hx : 1 ≤ x) (hxX : x ≤ X) :
    |Isum fR x| ≤ ∑ n ∈ Ioc 0 ⌊X⌋₊, |fR n| / n * Real.log X := by
  have hx0 : 0 < x := by linarith
  unfold Isum
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hsub : Ioc 0 ⌊x⌋₊ ⊆ Ioc 0 ⌊X⌋₊ := Ioc_subset_Ioc_right (Nat.floor_le_floor hxX)
  refine le_trans (sum_le_sum fun n hn => ?_)
    (sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => ?_)
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.1 hn).1
    have hnx : (n : ℝ) ≤ x := (Nat.cast_le.2 (mem_Ioc.1 hn).2).trans (Nat.floor_le hx0.le)
    have h1 : 1 ≤ x / n := by rw [le_div_iff₀ hn0]; linarith
    have hl0 : 0 ≤ Real.log (x / n) := Real.log_nonneg h1
    have hl : Real.log (x / n) ≤ Real.log X := by
      refine Real.log_le_log (by positivity) ?_
      calc x / n ≤ x := div_le_self hx0.le (by exact_mod_cast (mem_Ioc.1 hn).1)
        _ ≤ X := hxX
    rw [abs_mul, abs_div, Nat.abs_cast, abs_of_nonneg hl0]
    gcongr
  · have := Real.log_nonneg (hx.trans hxX); positivity

/-- **`J(x) ≪ (1 + log x)^{1/2}`** for all `x ≥ 1` (level 1). -/
theorem J_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x → |Isum fR x| ≤ K * (1 + Real.log x) ^ (1 / 2 : ℝ) := by
  obtain ⟨C₁, K₃, X₂, c₀, h⟩ := selberg_sum_fR
  set X : ℝ := max X₂ (Real.exp (2 * |c₀| + 2)) with hX
  have hX1 : 1 ≤ X := le_trans (Real.one_le_exp (by positivity)) (le_max_right _ _)
  set K0 : ℝ := ∑ n ∈ Ioc 0 ⌊X⌋₊, |fR n| / n * Real.log X with hK0
  have hK00 : 0 ≤ K0 := sum_nonneg fun n _ => by
    have := Real.log_nonneg hX1; positivity
  refine ⟨K0 + 4 * |C₁| + 3 * |K₃|, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set t := Real.log x with ht
  have ht0 : 0 ≤ t := Real.log_nonneg hx
  have hP1 : 1 ≤ (1 + t) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hP0 : 0 ≤ (1 + t) ^ (1 / 2 : ℝ) := by linarith
  have hA : 0 ≤ 4 * |C₁| + 3 * |K₃| := by positivity
  rcases lt_or_ge x X with hlt | hge
  · have hb := Isum_le_trivial hx hlt.le
    rw [← hK0] at hb
    nlinarith
  · have hx2 : X₂ ≤ x := le_trans (le_max_left _ _) hge
    have hta : 2 * |c₀| + 2 ≤ t := by
      rw [ht, Real.le_log_iff_exp_le hx0]; exact le_trans (le_max_right _ _) hge
    have hc := le_abs_self c₀
    have hc' := neg_abs_le c₀
    have hpos : 0 < t - c₀ := by linarith
    have ht1 : 1 ≤ t := by linarith [abs_nonneg c₀]
    have h2 := (h x hx2).2
    rw [← ht] at h2
    -- main term
    have hm : |2 * C₁ * (t - c₀) ^ (1 / 2 : ℝ)| ≤ 4 * |C₁| * (1 + t) ^ (1 / 2 : ℝ) := by
      have hr : (t - c₀) ^ (1 / 2 : ℝ) ≤ 2 * (1 + t) ^ (1 / 2 : ℝ) := by
        calc (t - c₀) ^ (1 / 2 : ℝ) ≤ (4 * (1 + t)) ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow hpos.le (by linarith) (by norm_num)
          _ = 2 * (1 + t) ^ (1 / 2 : ℝ) := by
              rw [Real.mul_rpow (by norm_num) (by linarith), sqrt4]
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
      have : |(2 : ℝ)| = 2 := by norm_num
      rw [this]
      nlinarith [abs_nonneg C₁]
    -- error term
    have he : K₃ * (1 + Real.log (1 + t)) * t ^ (-(1 / 2 : ℝ)) ≤ 3 * |K₃| * (1 + t) ^ (1 / 2 : ℝ) := by
      have hl := Real.log_le_rpow_div (x := 1 + t) (by linarith) (ε := 1 / 2) (by norm_num)
      have hl0 : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
      have h3 : 1 + Real.log (1 + t) ≤ 3 * (1 + t) ^ (1 / 2 : ℝ) := by
        have : Real.log (1 + t) ≤ 2 * (1 + t) ^ (1 / 2 : ℝ) := by
          calc Real.log (1 + t) ≤ (1 + t) ^ (1 / 2 : ℝ) / (1 / 2) := hl
            _ = 2 * (1 + t) ^ (1 / 2 : ℝ) := by ring
        linarith
      have h4 : t ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)
      have h5 : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht0 _
      calc K₃ * (1 + Real.log (1 + t)) * t ^ (-(1 / 2 : ℝ))
          ≤ |K₃| * (1 + Real.log (1 + t)) * t ^ (-(1 / 2 : ℝ)) := by
            gcongr; exact le_abs_self K₃
        _ ≤ |K₃| * (3 * (1 + t) ^ (1 / 2 : ℝ)) * 1 := by gcongr
        _ = 3 * |K₃| * (1 + t) ^ (1 / 2 : ℝ) := by ring
    have htri : |Isum fR x| ≤ |Isum fR x - 2 * C₁ * (t - c₀) ^ (1 / 2 : ℝ)| +
        |2 * C₁ * (t - c₀) ^ (1 / 2 : ℝ)| := by
      have := abs_add_le (Isum fR x - 2 * C₁ * (t - c₀) ^ (1 / 2 : ℝ)) (2 * C₁ * (t - c₀) ^ (1 / 2 : ℝ))
      simpa using this
    nlinarith

end RamanujanTau.QFProof
