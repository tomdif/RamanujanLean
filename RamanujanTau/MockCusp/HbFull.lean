/-
# `Andrews66.Hb` at every cusp, and Andrews' 1966 theorem unconditionally

* `Hb_two_mod_four`: `K ≡ 2 (mod 4)`, `ε_K = −1`. `f + b = 2φ(−q)` (`watson_disc`, `bA_eq_bE`), and
  `−q = e^{2πi(h''+iz/2)/(K/2)}` with `h'' = (h+K/2)/2` is a point near an *odd*-order root of unity, where
  `phi_odd_bound` applies.
* `Hb_zero_mod_four`: `K ≡ 0 (mod 4)`, `ε_K = +1`. `f − b = −4ψ(−q)` (`watson_disc2`, `bA_eq_bE`) and
  `aA_cusp_bound`.
* `HbEven_holds`, `Hb_holds`: `Andrews66.Hb Cb (3/2)` with an explicit `Cb`.
* `andrews_1966_unconditional`: Andrews' asymptotic for `α(n)` (the coefficients of `f(q)`), with his printed main
  term over `k ≤ √n`, and error `A₁ N²(1 + log N) + A₂ N`, `N = ⌊√n⌋`, i.e. `O(n log n)`.
-/
import RamanujanTau.MockCusp.PsiCusp
import RamanujanTau.MockCusp.Hb
import RamanujanTau.Andrews66.Printed

set_option autoImplicit false

namespace MockCusp
open Complex Filter Metric Set
open scoped Topology Real

noncomputable section

lemma rpow_half_le {x : ℝ} (hx : 0 < x) : (x / 2) ^ (-(3 / 2 : ℝ)) ≤ 3 * x ^ (-(3 / 2 : ℝ)) := by
  rw [Real.div_rpow hx.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
  gcongr
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
  have : √2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

lemma odd_of_coprime_even {h K : ℕ} (hcop : Nat.Coprime h K) (hK : Even K) : Odd h := by
  obtain ⟨m, rfl⟩ := hK
  exact Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right ⟨m, by ring⟩ hcop)

/-- **`K ≡ 2 (mod 4)`**. -/
theorem Hb_two_mod_four {K' : ℕ} (hK' : Odd K') {h : ℕ} (hcop : Nat.Coprime h (2 * K')) {z : ℂ}
    (hz : 0 < z.re) (hR : ((2 * K' : ℕ) : ℝ) / 2 ≤ (1 / z).re) :
    ‖Andrews66.fA (Rademacher.qp h (2 * K') z) - Andrews66.epsK (2 * K') * Andrews66.bE (Rademacher.qp h (2 * K') z)‖
      ≤ 2592 * (1 + HardyRamanujan.C0) * ‖z‖ ^ (-(3 / 2 : ℝ)) := by
  have hK0 : 0 < 2 * K' := by have := hK'.pos; omega
  have hq := Rademacher.qp_mem hK0 hz (h' := h)
  have heps : Andrews66.epsK (2 * K') = -1 := by
    rw [Andrews66.epsK, if_pos (even_two_mul K'), Nat.mul_div_cancel_left _ two_pos, hK'.neg_one_pow]
  have hho := odd_of_coprime_even hcop (even_two_mul K')
  -- `h'' = (h + K')/2`
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
  have hφ := phi_odd_bound hK' hcop'' hz2 hR2
  rw [hQ, ← gA_eq_Rd] at hφ
  rw [heps, ← bA_eq_bE hq]
  have hW := MockTheta3.Radial.watson_disc hq
  rw [show Andrews66.fA (Rademacher.qp h (2 * K') z) - -1 * MockTheta3.Radial.bA (Rademacher.qp h (2 * K') z) =
    2 * MockTheta3.Radial.gA (Rademacher.qp h (2 * K') z) by
      rw [← hW]; simp [Andrews66.fA]]
  rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr fun h0 => by rw [h0] at hz; simp at hz
  have hr := rpow_half_le hzn
  rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp] at hφ
  have hC := HardyRamanujan.C0_nonneg
  calc 2 * ‖MockTheta3.Radial.gA (Rademacher.qp h (2 * K') z)‖
      ≤ 2 * (432 * (1 + HardyRamanujan.C0) * (‖z‖ / 2) ^ (-(3 / 2 : ℝ))) := by gcongr
    _ ≤ 2 * (432 * (1 + HardyRamanujan.C0) * (3 * ‖z‖ ^ (-(3 / 2 : ℝ)))) := by gcongr
    _ = 2592 * (1 + HardyRamanujan.C0) * ‖z‖ ^ (-(3 / 2 : ℝ)) := by ring

/-- **`K ≡ 0 (mod 4)`**. -/
theorem Hb_zero_mod_four {T : ℕ} (hT : 0 < T) {h : ℕ} (hcop : Nat.Coprime h (4 * T)) {z : ℂ}
    (hz : 0 < z.re) (hR : ((4 * T : ℕ) : ℝ) / 2 ≤ (1 / z).re) :
    ‖Andrews66.fA (Rademacher.qp h (4 * T) z) - Andrews66.epsK (4 * T) * Andrews66.bE (Rademacher.qp h (4 * T) z)‖
      ≤ (864 * (1 + HardyRamanujan.C0) + 4) * ‖z‖ ^ (-(3 / 2 : ℝ)) := by
  have hK0 : 0 < 4 * T := by omega
  have hq := Rademacher.qp_mem hK0 hz (h' := h)
  have heps : Andrews66.epsK (4 * T) = 1 := by
    rw [Andrews66.epsK, if_pos ⟨2 * T, by ring⟩, show 4 * T / 2 = 2 * T by omega, pow_mul]; norm_num
  have hb := aA_cusp_bound hT rfl hcop hz hR
  rw [heps, one_mul, ← bA_eq_bE hq]
  have hW := watson_disc2 hq
  rw [show Andrews66.fA (Rademacher.qp h (4 * T) z) - MockTheta3.Radial.bA (Rademacher.qp h (4 * T) z) =
    -4 * (aA (Rademacher.qp h (4 * T) z) - 1) by rw [← hW]; simp [Andrews66.fA]]
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr fun h0 => by rw [h0] at hz; simp at hz
  -- `‖z‖ ≤ 1`, so `1 ≤ ‖z‖^{−3/2}`
  have hz1 : ‖z‖ ≤ 1 := by
    have h1 : (1 / z).re ≤ 1 / ‖z‖ := by
      rw [one_div, inv_re, Complex.normSq_eq_norm_sq, div_le_div_iff₀ (by positivity) hzn]
      nlinarith [Complex.re_le_norm z]
    have := hR.trans h1
    rw [le_div_iff₀ hzn] at this
    push_cast at this
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  have hone : 1 ≤ ‖z‖ ^ (-(3 / 2 : ℝ)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hzn hz1 (by norm_num)
  rw [norm_mul, show ‖(-4 : ℂ)‖ = 4 by simp]
  have h2 := norm_sub_le (aA (Rademacher.qp h (4 * T) z)) 1
  rw [norm_one] at h2
  nlinarith

/-- the constant of the even cusps. -/
def Ceven : ℝ := 2592 * (1 + HardyRamanujan.C0) + 4

/-- **the even half of `Hb`**, unconditionally. -/
theorem HbEven_holds : HbEven Ceven (3 / 2) := by
  intro K hK hKe h hcop z hz hR
  have hC := HardyRamanujan.C0_nonneg
  have hzp : 0 ≤ ‖z‖ ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  obtain ⟨m, rfl⟩ := hKe
  rcases Nat.even_or_odd m with ⟨T, rfl⟩ | hm
  · have hT : 0 < T := by omega
    have e : T + T + (T + T) = 4 * T := by ring
    rw [e] at hcop hR ⊢
    refine (Hb_zero_mod_four hT hcop hz hR).trans ?_
    unfold Ceven
    gcongr; linarith
  · have e : m + m = 2 * m := by ring
    rw [e] at hcop hR ⊢
    refine (Hb_two_mod_four hm hcop hz hR).trans ?_
    unfold Ceven
    gcongr; linarith

/-- **`Andrews66.Hb` holds** (all cusps). -/
theorem Hb_holds : Andrews66.Hb (max Ceven Codd) (3 / 2) := Hb_of_even HbEven_holds

lemma Cb_nonneg : 0 ≤ max Ceven Codd := le_max_of_le_right Codd_nonneg

/-- **Andrews 1966, unconditionally** (with Andrews' printed main term over `k ≤ √n`; error `O(N²(1+log N))`,
`N = ⌊√n⌋`). -/
theorem andrews_1966_unconditional :
    ∃ A₁ A₂ : ℝ, ∀ n : ℕ, 1 ≤ n →
      ‖(Dragonette.α n : ℂ) - Andrews66.andrewsPrinted n‖ ≤
        A₁ * ((Nat.sqrt n : ℝ) ^ (2 : ℝ) * (1 + Real.log (Nat.sqrt n))) + A₂ * Nat.sqrt n := by
  obtain ⟨A₁, A₂, hA⟩ := Andrews66.andrews_1966_printed_of_Hb Hb_holds Cb_nonneg (by norm_num)
  refine ⟨A₁, A₂, fun n hn => ?_⟩
  have := hA n hn
  rwa [show (2 * (3 / 2 : ℝ) - 1) = 2 by norm_num] at this

/-- the same, as a `BigO`: `α(n) − (Andrews' main sum over k ≤ √n/2) = O(n (1 + log n))`. -/
theorem andrews_1966_isBigO_unconditional :
    (fun n : ℕ => (Dragonette.α n : ℂ) - Andrews66.andrewsMain n) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ) * (1 + Real.log n)) := by
  have := Andrews66.andrews_1966_isBigO_of_Hb Hb_holds Cb_nonneg (by norm_num)
  rwa [show ((3 / 2 : ℝ) - 1 / 2) = 1 by norm_num] at this

end

end MockCusp
