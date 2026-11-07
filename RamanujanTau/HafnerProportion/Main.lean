/-
# Selberg–Hafner positive proportion for `L(Δ,s)`: headlines

See `docs/HAFNER_PROPORTION.md`.

Level 1 (axiom-clean, unconditional):
* `selberg_zeros` — abstract Selberg method: (H1) `∫J ≥ aTh`, (H2) `∫J² ≤ BTh²`,
  (H3) `∫I² ≤ (a²/16)Th²` give `≥ 5a²T/(16Bh)` distinct zeros of `Z` in `[T, 2T+h]`;
* `mollified_first_moment` — `∫_a^c |L(Δ,6+iu)||M(6+iu)|² du ≥ (c−a)/2 − T/8` for every
  mollifier with `b(1) = 1`, `|b(n)| ≤ βn^η`, `y^{2+2η} ≤ T^{1/4}`, `0 ≤ a ≤ c ≤ 3T`;
* `selberg_H1` — hence Selberg's (H1) with `a = 1/4`, for all `0 < h ≤ T/8`;
* `selberg_H2` — (H2) from the mollified second moment `∫_T^{3T}|LM²|² ≤ BT`;
* `norm_tauL_line` — `|ZH t| = |L(Δ,6+it)|` for the normalised Hardy function.

Level 2 (conditional on the named hypothesis `SelbergHyp` = mollified second moment + Selberg's
key lemma `∫_T^{2T} I² ≤ (D/√K) T h²`, `h = K/log T`):
* `tauL_critical_zeros_T_log_T_of_selberg` — `N₀(T) ≫ T log T`;
* `tauL_positive_proportion_of_selberg` — `N₀(3T) ≥ c · N(3T)` (with RvM).
-/
import RamanujanTau.HafnerProportion.Proportion

set_option autoImplicit false

namespace RamanujanTau.HafnerProportion

open Complex MeasureTheory Set
open RamanujanTau.HeckeL RamanujanTau.ZeroCount
open scoped Real

/-- Abstract Selberg method. -/
example {Z w : ℝ → ℝ} (hZ : Continuous Z) (hw : Continuous w)
    (hw0 : ∀ t, 0 ≤ w t) {T h a B : ℝ} (hT : 0 < T) (hh : 0 < h) (ha : 0 < a) (hB : 0 < B)
    (H1 : a * T * h ≤ ∫ t in Icc T (2 * T), selJ Z w h t)
    (H2 : ∫ t in Icc T (2 * T), selJ Z w h t ^ 2 ≤ B * T * h ^ 2)
    (H3 : ∫ t in Icc T (2 * T), selI Z w h t ^ 2 ≤ a ^ 2 / 16 * T * h ^ 2) :
    ∃ F : Finset ℝ, (∀ γ ∈ F, γ ∈ Icc T (2 * T + h) ∧ Z γ = 0) ∧
      5 * a ^ 2 / (16 * B) * T / h ≤ F.card :=
  selberg_zeros hZ hw hw0 hT hh ha hB H1 H2 H3

/-- Selberg's (H1) for `L(Δ,s)`, unconditional. -/
example {β η : ℝ} (hβ : 0 ≤ β) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ (b : ℕ → ℂ) (y : ℕ), 1 ≤ y → b 1 = 1 →
      (∀ n : ℕ, ‖b n‖ ≤ β * (n : ℝ) ^ η) → (y : ℝ) ^ (2 + 2 * η) ≤ T ^ (1 / 4 : ℝ) →
      ∀ h : ℝ, 0 < h → h ≤ T / 8 →
        1 / 4 * T * h ≤ ∫ t in Icc T (2 * T), selJ ZH (wM b y) h t :=
  selberg_H1 hβ hη0 hη1

/-- Hafner: `N₀(T) ≫ T log T`, conditional on `SelbergHyp`. -/
example (H : SelbergHyp) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ γ ∈ S, T ≤ γ ∧ γ ≤ 3 * T ∧ tauL (6 + γ * I) = 0) ∧ c * T * Real.log T ≤ S.card :=
  tauL_critical_zeros_T_log_T_of_selberg H

/-- Hafner: a positive proportion of zeros on `Re s = 6`, conditional on `SelbergHyp`. -/
example (H : SelbergHyp) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ γ ∈ S, 0 < γ ∧ γ ≤ 3 * T ∧ tauL (6 + γ * I) = 0) ∧
        c * (zeroCount (3 * T) : ℝ) ≤ S.card :=
  tauL_positive_proportion_of_selberg H

end RamanujanTau.HafnerProportion

#print axioms RamanujanTau.HafnerProportion.selberg_zeros
#print axioms RamanujanTau.HafnerProportion.selberg_measure
#print axioms RamanujanTau.HafnerProportion.zeros_of_measure
#print axioms RamanujanTau.HafnerProportion.exists_zero_of_abs_lt
#print axioms RamanujanTau.HafnerProportion.double_lower
#print axioms RamanujanTau.HafnerProportion.double_upper
#print axioms RamanujanTau.HafnerProportion.sq_integral_le
#print axioms RamanujanTau.HafnerProportion.norm_tauL_line
#print axioms RamanujanTau.HafnerProportion.norm_tauL_sub_one_le_all
#print axioms RamanujanTau.HafnerProportion.norm_Mc_sub_one_le
#print axioms RamanujanTau.HafnerProportion.mollified_first_moment
#print axioms RamanujanTau.HafnerProportion.selberg_H1
#print axioms RamanujanTau.HafnerProportion.selberg_H2
#print axioms RamanujanTau.HafnerProportion.tauL_critical_zeros_T_log_T_of_selberg
#print axioms RamanujanTau.HafnerProportion.tauL_positive_proportion_of_selberg
