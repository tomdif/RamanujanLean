/-
# `Andrews66.Hb C 1` at every cusp, and Andrews' `O(√n log n)` unconditionally

The sharp cusp bounds `f_odd_bound'`, `phi_odd_bound'`, `aA_cusp_bound'` (all `≪ |z|^{−1}`) are assembled exactly as
in `HbFull`:
* `K` odd: `f`;
* `K ≡ 2 (4)`: `f + b = 2φ(−q)`, `−q` at the odd cusp `(h+K/2)/2 mod K/2`, `z/2`;
* `K ≡ 0 (4)`: `f − b = −4(ψ(−q)+1 − 1)`.

`HbSharp_holds : Andrews66.Hb Csharp 1`, hence (`Andrews66.andrews_1966_printed_isBigO_of_Hb`)
`andrews_1966_sqrt_log_unconditional : α(n) − andrewsPrinted(n) = O(√n (1 + log n))`.
-/
import RamanujanTau.MockCusp.SharpPsi
import RamanujanTau.MockCusp.HbFull
import RamanujanTau.Andrews66.OmegaB

set_option autoImplicit false

namespace MockCusp
open Complex Filter Metric Set
open scoped Topology Real

noncomputable section

/-- the constants of the three cusp classes. -/
def CoddS : ℝ := 36 * (1 + HardyRamanujan.C0) * CstO (4 * √(3 / π))
def CphiS : ℝ := 36 * (1 + HardyRamanujan.C0) * CstO (4 * √(24 / π))
def CpsiS : ℝ := 18 * (1 + HardyRamanujan.C0) * CstP (16 * √(3 / (2 * π)))

lemma CoddS_nonneg : 0 ≤ CoddS := by
  unfold CoddS CstO; have := HardyRamanujan.C0_nonneg; positivity
lemma CphiS_nonneg : 0 ≤ CphiS := by
  unfold CphiS CstO; have := HardyRamanujan.C0_nonneg; positivity
lemma CpsiS_nonneg : 0 ≤ CpsiS := by
  unfold CpsiS CstP; have := HardyRamanujan.C0_nonneg; positivity

/-- **`K ≡ 2 (mod 4)`, `D = 1`**. -/
theorem Hb_two_mod_four' {K' : ℕ} (hK' : Odd K') {h : ℕ} (hcop : Nat.Coprime h (2 * K')) {z : ℂ}
    (hz : 0 < z.re) (hR : ((2 * K' : ℕ) : ℝ) / 2 ≤ (1 / z).re) :
    ‖Andrews66.fA (Rademacher.qp h (2 * K') z) - Andrews66.epsK (2 * K') * Andrews66.bE (Rademacher.qp h (2 * K') z)‖
      ≤ 4 * CphiS * ‖z‖ ^ (-(1 : ℝ)) := by
  have hK0 : 0 < 2 * K' := by have := hK'.pos; omega
  have hq := Rademacher.qp_mem hK0 hz (h' := h)
  have heps : Andrews66.epsK (2 * K') = -1 := by
    rw [Andrews66.epsK, if_pos (even_two_mul K'), Nat.mul_div_cancel_left _ two_pos, hK'.neg_one_pow]
  have hho := odd_of_coprime_even hcop (even_two_mul K')
  obtain ⟨h'', hh''⟩ : ∃ h'' : ℕ, h + K' = 2 * h'' := by
    obtain ⟨a, ha⟩ := hho; obtain ⟨b, hb⟩ := hK'; exact ⟨a + b + 1, by omega⟩
  have hcop'' : Nat.Coprime h'' K' := by
    have h1 : Nat.Coprime h K' := Nat.Coprime.coprime_dvd_right ⟨2, by ring⟩ hcop
    have h2 : Nat.Coprime (h + K') K' := Nat.coprime_add_self_left.mpr h1
    rw [hh''] at h2
    exact Nat.Coprime.coprime_mul_left h2
  have hK'c : (K' : ℂ) ≠ 0 := by exact_mod_cast hK'.pos.ne'
  have hQ : Rademacher.qp h'' K' (z / 2) = -Rademacher.qp h (2 * K') z := by
    have e : (h'' : ℂ) = ((h : ℂ) + K') / 2 := by
      have : ((h + K' : ℕ) : ℂ) = ((2 * h'' : ℕ) : ℂ) := by rw [hh'']
      push_cast at this; linear_combination -this / 2
    rw [Rademacher.qp, Rademacher.qp, show (2 * π * I * ((((h'' : ℤ) : ℂ) + I * (z / 2)) / K')) =
      2 * π * I * ((((h : ℤ) : ℂ) + I * z) / ((2 * K' : ℕ) : ℂ)) + π * I by
        push_cast; rw [e]; field_simp; ring, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hz2 : 0 < (z / 2).re := by simp; linarith
  have hR2 : (K' : ℝ) / 2 ≤ (1 / (z / 2)).re := by
    rw [show 1 / (z / 2) = ((2 : ℝ) : ℂ) * (1 / z) by push_cast; field_simp, Complex.re_ofReal_mul]
    push_cast at hR; have : (0 : ℝ) ≤ K' := by positivity
    linarith
  have hφ := phi_odd_bound' hK' hcop'' hz2 hR2
  rw [hQ, ← gA_eq_Rd] at hφ
  rw [heps, ← bA_eq_bE hq]
  have hW := MockTheta3.Radial.watson_disc hq
  rw [show Andrews66.fA (Rademacher.qp h (2 * K') z) - -1 * MockTheta3.Radial.bA (Rademacher.qp h (2 * K') z) =
    2 * MockTheta3.Radial.gA (Rademacher.qp h (2 * K') z) by
      rw [← hW]; simp [Andrews66.fA]]
  rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr fun h0 => by rw [h0] at hz; simp at hz
  rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp] at hφ
  have hr : (‖z‖ / 2) ^ (-(1 : ℝ)) = 2 * ‖z‖ ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one, Real.rpow_neg_one]; field_simp
  rw [hr] at hφ
  have hC := CphiS_nonneg
  calc 2 * ‖MockTheta3.Radial.gA (Rademacher.qp h (2 * K') z)‖
      ≤ 2 * (36 * (1 + HardyRamanujan.C0) * CstO (4 * √(24 / π)) * (2 * ‖z‖ ^ (-(1 : ℝ)))) := by gcongr
    _ = 4 * CphiS * ‖z‖ ^ (-(1 : ℝ)) := by unfold CphiS; ring

/-- **`K ≡ 0 (mod 4)`, `D = 1`**. -/
theorem Hb_zero_mod_four' {T : ℕ} (hT : 0 < T) {h : ℕ} (hcop : Nat.Coprime h (4 * T)) {z : ℂ}
    (hz : 0 < z.re) (hR : ((4 * T : ℕ) : ℝ) / 2 ≤ (1 / z).re) :
    ‖Andrews66.fA (Rademacher.qp h (4 * T) z) - Andrews66.epsK (4 * T) * Andrews66.bE (Rademacher.qp h (4 * T) z)‖
      ≤ (4 * CpsiS + 4) * ‖z‖ ^ (-(1 : ℝ)) := by
  have hK0 : 0 < 4 * T := by omega
  have hq := Rademacher.qp_mem hK0 hz (h' := h)
  have heps : Andrews66.epsK (4 * T) = 1 := by
    rw [Andrews66.epsK, if_pos ⟨2 * T, by ring⟩, show 4 * T / 2 = 2 * T by omega, pow_mul]; norm_num
  have hb := aA_cusp_bound' hT rfl hcop hz hR
  rw [heps, one_mul, ← bA_eq_bE hq]
  have hW := watson_disc2 hq
  rw [show Andrews66.fA (Rademacher.qp h (4 * T) z) - MockTheta3.Radial.bA (Rademacher.qp h (4 * T) z) =
    -4 * (aA (Rademacher.qp h (4 * T) z) - 1) by rw [← hW]; simp [Andrews66.fA]]
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr fun h0 => by rw [h0] at hz; simp at hz
  have hz1 : ‖z‖ ≤ 1 := by
    have h1 : (1 / z).re ≤ 1 / ‖z‖ := by
      rw [one_div, inv_re, Complex.normSq_eq_norm_sq, div_le_div_iff₀ (by positivity) hzn]
      nlinarith [Complex.re_le_norm z]
    have := hR.trans h1
    rw [le_div_iff₀ hzn] at this
    push_cast at this
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  have hone : 1 ≤ ‖z‖ ^ (-(1 : ℝ)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hzn hz1 (by norm_num)
  rw [norm_mul, show ‖(-4 : ℂ)‖ = 4 by simp]
  have h2 := norm_sub_le (aA (Rademacher.qp h (4 * T) z)) 1
  rw [norm_one] at h2
  have hb' : ‖aA (Rademacher.qp h (4 * T) z)‖ ≤ CpsiS * ‖z‖ ^ (-(1 : ℝ)) := by
    unfold CpsiS; exact hb
  nlinarith

/-- the constant of the sharp bound. -/
def Csharp : ℝ := max (max (4 * CphiS) (4 * CpsiS + 4)) CoddS

lemma Csharp_nonneg : 0 ≤ Csharp := le_max_of_le_right CoddS_nonneg

/-- **`Andrews66.Hb Csharp 1`**: `‖f(q) − ε_K b(q)‖ ≤ Csharp ‖z‖^{−1}` at every cusp. -/
theorem HbSharp_holds : Andrews66.Hb Csharp 1 := by
  intro K hK h hcop z hz hR
  have hzp : 0 ≤ ‖z‖ ^ (-(1 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  have h1 : 4 * CphiS ≤ Csharp := (le_max_left _ _).trans (le_max_left _ _)
  have h2 : 4 * CpsiS + 4 ≤ Csharp := (le_max_right _ _).trans (le_max_left _ _)
  have h3 : CoddS ≤ Csharp := le_max_right _ _
  by_cases hKe : Even K
  · obtain ⟨m, rfl⟩ := hKe
    rcases Nat.even_or_odd m with ⟨T, rfl⟩ | hm
    · have hT : 0 < T := by omega
      have e : T + T + (T + T) = 4 * T := by ring
      rw [e] at hcop hR ⊢
      exact (Hb_zero_mod_four' hT hcop hz hR).trans (mul_le_mul_of_nonneg_right h2 hzp)
    · have e : m + m = 2 * m := by ring
      rw [e] at hcop hR ⊢
      exact (Hb_two_mod_four' hm hcop hz hR).trans (mul_le_mul_of_nonneg_right h1 hzp)
  · have hKo : Odd K := Nat.not_even_iff_odd.mp hKe
    rw [Andrews66.epsK, if_neg hKe, zero_mul, sub_zero]
    refine (f_odd_bound' hKo hcop hz hR).trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_right h3 hzp))
    unfold CoddS; ring

/-- **Andrews 1966, with his sharp error, unconditionally**: `α(n) − andrewsPrinted(n) = O(√n (1 + log n))`. -/
theorem andrews_1966_sqrt_log_unconditional :
    (fun n : ℕ => (Dragonette.α n : ℂ) - Andrews66.andrewsPrinted n) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log n)) :=
  Andrews66.andrews_1966_printed_isBigO_of_Hb HbSharp_holds Csharp_nonneg le_rfl

/-- the same with Andrews' main sum over `k ≤ √n/2` (`Andrews66.andrewsMain`). -/
theorem andrews_1966_sqrt_log_main_unconditional :
    (fun n : ℕ => (Dragonette.α n : ℂ) - Andrews66.andrewsMain n) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log n)) :=
  Andrews66.andrews_1966_sqrt_log_of_Hb HbSharp_holds Csharp_nonneg le_rfl

end

end MockCusp
