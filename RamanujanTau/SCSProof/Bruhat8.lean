/-
# Bruhat decomposition, part 8: Weil summed over the moduli

`norm_tsum_Iγ_le`: for `h ≥ 1` and `0 < δ ≤ 1/2` there is `C = C(δ)` (independent of all
parameters) with `‖Σ_γ I(γ)‖ ≤ C h ε³ Y^{−3/2−2δ}`.
-/
import RamanujanTau.SCSProof.Bruhat7

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex
open RamanujanTau.TauBound
open scoped ENNReal Real

lemma kloosterman_zero_mod (m n : ℤ) : kloosterman m n 0 = 0 := by
  simp [kloosterman]

/-- `Σ_{m ≤ K+1} m^{1/2+δ}/m ≤ (K+2)^{1/2+δ} (1 + log (K+1))`. -/
lemma sum_rpow_div_le (δ : ℝ) (hδ : 0 < δ) (K : ℕ) :
    ∑ m ∈ Finset.range (K + 2), (if m = 0 then 0 else (m : ℝ) ^ (1 / 2 + δ) / m) ≤
      ((K : ℝ) + 2) ^ (1 / 2 + δ) * (1 + Real.log (K + 1)) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.succ_ne_zero, if_false, if_true, add_zero]
  have hterm : ∀ m ∈ Finset.range (K + 1), ((m + 1 : ℕ) : ℝ) ^ (1 / 2 + δ) / ((m + 1 : ℕ) : ℝ) ≤
      ((K : ℝ) + 2) ^ (1 / 2 + δ) * (1 / ((m + 1 : ℕ) : ℝ)) := by
    intro m hm
    have hm' : m < K + 1 := Finset.mem_range.1 hm
    rw [div_eq_mul_one_div]
    gcongr
    push_cast
    have : (m : ℝ) < K + 1 := by exact_mod_cast hm'
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  gcongr
  have hh := harmonic_le_one_add_log (K + 1)
  have e : (harmonic (K + 1) : ℝ) = ∑ m ∈ Finset.range (K + 1), 1 / ((m + 1 : ℕ) : ℝ) := by
    simp [harmonic]
  rw [← e]
  push_cast at hh ⊢
  linarith

/-- **`‖P‖²`-bound (Weil).** -/
theorem norm_tsum_Iγ_le (δ : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : Par, 1 ≤ P.h →
      ‖∑' γ, Iγ P γ‖ ≤ C * P.h * P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by
  obtain ⟨A, hA0, hA⟩ := norm_kloosterman_hh_le δ hδ
  refine ⟨32 + 128 * A * 25 * (1 + 1 / δ), by positivity, fun P hh => ?_⟩
  have hY := P.hY; have hY1 := P.hY1; have hε := P.hε
  have hhR : (1 : ℝ) ≤ P.h := by exact_mod_cast hh
  have h1 := norm_tsum_Iγ_le_gK P
  -- the `∫⁻ ‖ft‖` term
  have hX : (∫⁻ q, ‖ft P q‖ₑ).toReal ≤ 16 * P.ε ^ 3 / P.Y := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (lintegral_ft_le P)
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  -- `Y^{-1} ≤ Y^{-3/2-2δ}`
  have hYpow : P.Y ^ (-(1 : ℝ)) ≤ P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) :=
    Real.rpow_le_rpow_of_exponent_ge hY hY1 (by linarith)
  have hYinv : 1 / P.Y = P.Y ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one, one_div]
  -- the Kloosterman terms
  have hg : ∀ m ∈ Finset.range (K2 P + 2), gK P m ≤
      (A * P.h * (64 * P.ε ^ 3 / P.Y)) * (if m = 0 then 0 else (m : ℝ) ^ (1 / 2 + δ) / m) := by
    intro m _
    unfold gK
    split_ifs with hm0
    · subst hm0; simp [kloosterman_zero_mod]
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 hm0
      have hk := hA P.h m hh hm1
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
      calc ‖kloosterman P.h P.h m‖ * (64 * P.ε ^ 3 / (m * P.Y))
          ≤ (A * P.h * (m : ℝ) ^ (1 / 2 + δ)) * (64 * P.ε ^ 3 / (m * P.Y)) := by gcongr
        _ = _ := by field_simp
  have hsum := Finset.sum_le_sum hg
  rw [← Finset.mul_sum] at hsum
  have hS := sum_rpow_div_le δ hδ (K2 P)
  -- `K₂ + 2 ≤ 5/Y`
  have hK : (K2 P : ℝ) + 2 ≤ 5 / P.Y := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 / P.Y by positivity)
    have h3 : 3 ≤ 3 / P.Y := by rw [le_div_iff₀ hY]; linarith
    unfold K2
    have : (5 : ℝ) / P.Y = 2 / P.Y + 3 / P.Y := by ring
    linarith
  have hK1 : (1 : ℝ) ≤ 5 / P.Y := by rw [le_div_iff₀ hY]; linarith
  have hlog : Real.log ((K2 P : ℝ) + 1) ≤ (5 / P.Y) ^ δ / δ := by
    refine (Real.log_le_rpow_div (by positivity) hδ).trans ?_
    gcongr; linarith
  have hpow1 : ((K2 P : ℝ) + 2) ^ (1 / 2 + δ) ≤ (5 / P.Y) ^ (1 / 2 + δ) := by
    gcongr
  have hS' : ((K2 P : ℝ) + 2) ^ (1 / 2 + δ) * (1 + Real.log (K2 P + 1)) ≤
      25 * (1 + 1 / δ) * P.Y ^ (-(1 / 2 : ℝ) - 2 * δ) := by
    have e1 : (5 / P.Y) ^ (1 / 2 + δ) * (5 / P.Y) ^ δ = (5 / P.Y) ^ (1 / 2 + 2 * δ) := by
      rw [← Real.rpow_add (by positivity)]; ring_nf
    have e2 : (5 / P.Y) ^ (1 / 2 + 2 * δ) = (5 : ℝ) ^ (1 / 2 + 2 * δ) * P.Y ^ (-(1 / 2 : ℝ) - 2 * δ) := by
      rw [Real.div_rpow (by norm_num) hY.le, div_eq_mul_inv, ← Real.rpow_neg hY.le]
      ring_nf
    have h5 : (5 : ℝ) ^ (1 / 2 + 2 * δ) ≤ 25 := by
      calc (5 : ℝ) ^ (1 / 2 + 2 * δ) ≤ (5 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 25 := by norm_num
    have hpowδ : 1 ≤ (5 / P.Y) ^ δ := Real.one_le_rpow hK1 hδ.le
    have hYp : 0 < P.Y ^ (-(1 / 2 : ℝ) - 2 * δ) := Real.rpow_pos_of_pos hY _
    calc ((K2 P : ℝ) + 2) ^ (1 / 2 + δ) * (1 + Real.log (K2 P + 1))
        ≤ (5 / P.Y) ^ (1 / 2 + δ) * ((5 / P.Y) ^ δ * (1 + 1 / δ)) := by
          gcongr
          · have := Real.log_nonneg (show (1 : ℝ) ≤ K2 P + 1 by
              have : (0 : ℝ) ≤ K2 P := Nat.cast_nonneg _
              linarith)
            linarith
          · calc 1 + Real.log ((K2 P : ℝ) + 1) ≤ 1 + (5 / P.Y) ^ δ / δ := by linarith
              _ ≤ (5 / P.Y) ^ δ + (5 / P.Y) ^ δ / δ := by linarith
              _ = (5 / P.Y) ^ δ * (1 + 1 / δ) := by ring
      _ = (5 / P.Y) ^ (1 / 2 + 2 * δ) * (1 + 1 / δ) := by rw [← e1]; ring
      _ ≤ 25 * P.Y ^ (-(1 / 2 : ℝ) - 2 * δ) * (1 + 1 / δ) := by
          rw [e2]; gcongr
      _ = 25 * (1 + 1 / δ) * P.Y ^ (-(1 / 2 : ℝ) - 2 * δ) := by ring
  have hYsplit : 1 / P.Y * P.Y ^ (-(1 / 2 : ℝ) - 2 * δ) = P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by
    rw [hYinv, ← Real.rpow_add hY]; ring_nf
  have hYp3 : 0 ≤ P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := (Real.rpow_pos_of_pos hY _).le
  have hfin : 2 * ∑ m ∈ Finset.range (K2 P + 2), gK P m ≤
      128 * A * 25 * (1 + 1 / δ) * P.h * P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by
    have hcoef : 0 ≤ A * P.h * (64 * P.ε ^ 3 / P.Y) := by positivity
    calc 2 * ∑ m ∈ Finset.range (K2 P + 2), gK P m
        ≤ 2 * ((A * P.h * (64 * P.ε ^ 3 / P.Y)) * (((K2 P : ℝ) + 2) ^ (1 / 2 + δ) *
            (1 + Real.log (K2 P + 1)))) := by
          gcongr; exact hsum.trans (mul_le_mul_of_nonneg_left hS hcoef)
      _ ≤ 2 * ((A * P.h * (64 * P.ε ^ 3 / P.Y)) * (25 * (1 + 1 / δ) *
            P.Y ^ (-(1 / 2 : ℝ) - 2 * δ))) := by gcongr
      _ = 128 * A * 25 * (1 + 1 / δ) * P.h * P.ε ^ 3 *
            (1 / P.Y * P.Y ^ (-(1 / 2 : ℝ) - 2 * δ)) := by ring
      _ = _ := by rw [hYsplit]
  have hfirst : 2 * (∫⁻ q, ‖ft P q‖ₑ).toReal ≤ 32 * P.h * P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by
    have : 2 * (16 * P.ε ^ 3 / P.Y) = 32 * P.ε ^ 3 * P.Y ^ (-(1 : ℝ)) := by rw [← hYinv]; ring
    calc 2 * (∫⁻ q, ‖ft P q‖ₑ).toReal ≤ 2 * (16 * P.ε ^ 3 / P.Y) := by linarith
      _ = 32 * P.ε ^ 3 * P.Y ^ (-(1 : ℝ)) := this
      _ ≤ 32 * P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by gcongr
      _ ≤ 32 * P.h * P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by
          have : 0 ≤ P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) := by positivity
          nlinarith
  calc ‖∑' γ, Iγ P γ‖ ≤ _ := h1
    _ ≤ 32 * P.h * P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) +
          128 * A * 25 * (1 + 1 / δ) * P.h * P.ε ^ 3 * P.Y ^ (-(3 / 2 : ℝ) - 2 * δ) :=
        add_le_add hfirst hfin
    _ = _ := by ring

end RamanujanTau.SCSProof
