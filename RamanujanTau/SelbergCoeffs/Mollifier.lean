/-
# Selberg's mollifier for `L(Δ,s)` and the coefficient clauses of `SelbergHyp`

Selberg's choice (Titchmarsh §10.9, Hafner 1983 §2):

    b(n) = α(n) (1 − log n / log y)   for 1 ≤ n ≤ y,    b(n) = 0 otherwise,

with `α` the coefficients of `L(Δ,s)^{−1/2}` (`Global.alpha`) and `y = ⌊T^θ⌋`.

* `bSel_one`: `b(1) = 1`;
* `norm_bSel_le_one [DeligneBound]`: `|b(n)| ≤ 1` (so `β = 1, η = 0`);
* `norm_bSel_le_sqrt`: `|b(n)| ≤ n^{1/2}` unconditionally (`β = 1, η = 1/2`);
* `SelbergMollHyp`: (MV2) and (SK) **for this specific mollifier**, `y = ⌊T^θ⌋`, `0 < θ ≤ 1/12`;
* `selbergHyp_of_moll` (Deligne) and `selbergHyp_of_moll_uncond` (no Deligne):
  `SelbergMollHyp → HafnerProportion.SelbergHyp`; hence the positive proportion
  `tauL_positive_proportion_of_moll`.
-/
import RamanujanTau.SelbergCoeffs.Global
import RamanujanTau.HafnerProportion.Main

set_option autoImplicit false

namespace RamanujanTau.SelbergCoeffs

open Complex RamanujanTau.HafnerProportion RamanujanTau.HeckeL RamanujanTau.ZeroCount
open scoped Real

noncomputable section

/-- **Selberg's mollifier coefficients** `b(n) = α(n)(1 − log n/log y)`, `1 ≤ n ≤ y`. -/
def bSel (y : ℕ) (n : ℕ) : ℂ :=
  if 1 ≤ n ∧ n ≤ y then ((alpha n * (1 - Real.log n / Real.log y) : ℝ) : ℂ) else 0

theorem bSel_one {y : ℕ} (hy : 1 ≤ y) : bSel y 1 = 1 := by
  simp [bSel, hy, alpha_one]

lemma abs_smooth_le {y n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ y) :
    |1 - Real.log n / Real.log y| ≤ 1 := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast h1
  have hny : (n : ℝ) ≤ y := by exact_mod_cast h2
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg hn
  have hl1 : Real.log n ≤ Real.log y := Real.log_le_log (by linarith) hny
  have hr0 : 0 ≤ Real.log n / Real.log y := div_nonneg hl0 (hl0.trans hl1)
  have hr1 : Real.log n / Real.log y ≤ 1 := div_le_one_of_le₀ hl1 (hl0.trans hl1)
  rw [abs_le]; constructor <;> linarith

lemma norm_bSel_le_abs_alpha (y n : ℕ) : ‖bSel y n‖ ≤ |alpha n| := by
  unfold bSel
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    calc |alpha n| * |1 - Real.log n / Real.log y| ≤ |alpha n| * 1 :=
          mul_le_mul_of_nonneg_left (abs_smooth_le h.1 h.2) (abs_nonneg _)
      _ = |alpha n| := mul_one _
  · simp

/-- **Under Deligne, `|b(n)| ≤ 1 = 1 · n^0`.** -/
theorem norm_bSel_le_one [DeligneBound] (y n : ℕ) : ‖bSel y n‖ ≤ 1 * (n : ℝ) ^ (0 : ℝ) := by
  rw [Real.rpow_zero, one_mul]
  exact (norm_bSel_le_abs_alpha y n).trans (abs_alpha_le_one n)

/-- **Unconditionally, `|b(n)| ≤ 1 · n^{1/2}`.** -/
theorem norm_bSel_le_sqrt (y n : ℕ) : ‖bSel y n‖ ≤ 1 * (n : ℝ) ^ (1 / 2 : ℝ) := by
  rw [one_mul]
  exact (norm_bSel_le_abs_alpha y n).trans (abs_alpha_le_sqrt n)

/-- **(MV2) and (SK) for Selberg's mollifier** `bSel ⌊T^θ⌋`, some fixed `0 < θ ≤ 1/12`.
This is the analytic content left open (milestones 2 and 4 of `HAFNER_PROPORTION.md`). -/
def SelbergMollHyp : Prop :=
  ∃ θ B D : ℝ, 0 < θ ∧ θ ≤ 1 / 12 ∧ 0 < B ∧ 0 ≤ D ∧
    ∀ K : ℝ, 1 ≤ K → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (∫ u in T..(3 * T), ‖tauL (6 + u * I) * Mc (bSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊ (6 + u * I) ^ 2‖ ^ 2)
          ≤ B * T ∧
      (∫ t in Set.Icc T (2 * T), selI ZH (wM (bSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊) (K / Real.log T) t ^ 2) ≤
          D / Real.sqrt K * T * (K / Real.log T) ^ 2

lemma floor_window {θ e T : ℝ} (hθ : 0 < θ) (he : 0 ≤ e) (hθe : e * θ ≤ 1 / 4) (hT : 1 ≤ T) :
    1 ≤ ⌊T ^ θ⌋₊ ∧ ((⌊T ^ θ⌋₊ : ℕ) : ℝ) ^ e ≤ T ^ (1 / 4 : ℝ) := by
  have h1 : 1 ≤ T ^ θ := Real.one_le_rpow hT hθ.le
  refine ⟨Nat.one_le_floor_iff _ |>.mpr h1, ?_⟩
  have hf : ((⌊T ^ θ⌋₊ : ℕ) : ℝ) ≤ T ^ θ := Nat.floor_le (by linarith)
  calc ((⌊T ^ θ⌋₊ : ℕ) : ℝ) ^ e ≤ (T ^ θ) ^ e := Real.rpow_le_rpow (by positivity) hf he
    _ = T ^ (θ * e) := by rw [← Real.rpow_mul (by linarith)]
    _ ≤ T ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)

/-- **Under Deligne, Selberg's mollifier meets every size condition of `SelbergHyp`** (with
`β = 1, η = 0`), so (MV2)+(SK) for it give `SelbergHyp`. -/
theorem selbergHyp_of_moll [DeligneBound] (H : SelbergMollHyp) : SelbergHyp := by
  obtain ⟨θ, B, D, hθ, hθ1, hB, hD, hK⟩ := H
  refine ⟨1, 0, B, D, zero_le_one, le_rfl, zero_le_one, hB, hD, fun K hK1 => ?_⟩
  obtain ⟨T₀, hT₀⟩ := hK K hK1
  refine ⟨max T₀ 1, fun T hT => ?_⟩
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  obtain ⟨hMV, hSK⟩ := hT₀ T (le_trans (le_max_left _ _) hT)
  obtain ⟨hy, hwin⟩ := floor_window (e := 2 + 2 * 0) hθ (by norm_num) (by linarith) hT1
  exact ⟨bSel ⌊T ^ θ⌋₊, ⌊T ^ θ⌋₊, hy, bSel_one hy, norm_bSel_le_one _, hwin, hMV, hSK⟩

/-- **Without Deligne**: Selberg's mollifier still meets the size conditions, with `η = 1/2`. -/
theorem selbergHyp_of_moll_uncond (H : SelbergMollHyp) : SelbergHyp := by
  obtain ⟨θ, B, D, hθ, hθ1, hB, hD, hK⟩ := H
  refine ⟨1, 1 / 2, B, D, zero_le_one, by norm_num, by norm_num, hB, hD, fun K hK1 => ?_⟩
  obtain ⟨T₀, hT₀⟩ := hK K hK1
  refine ⟨max T₀ 1, fun T hT => ?_⟩
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  obtain ⟨hMV, hSK⟩ := hT₀ T (le_trans (le_max_left _ _) hT)
  obtain ⟨hy, hwin⟩ := floor_window (e := 2 + 2 * (1 / 2)) hθ (by norm_num) (by linarith) hT1
  exact ⟨bSel ⌊T ^ θ⌋₊, ⌊T ^ θ⌋₊, hy, bSel_one hy, norm_bSel_le_sqrt _, hwin, hMV, hSK⟩

/-- **Positive proportion from (MV2)+(SK) for Selberg's mollifier** (no Deligne needed for the
coefficient clauses). -/
theorem tauL_positive_proportion_of_moll (H : SelbergMollHyp) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ γ ∈ S, 0 < γ ∧ γ ≤ 3 * T ∧ tauL (6 + γ * I) = 0) ∧
        c * (zeroCount (3 * T) : ℝ) ≤ S.card :=
  tauL_positive_proportion_of_selberg (selbergHyp_of_moll_uncond H)

end

end RamanujanTau.SelbergCoeffs
