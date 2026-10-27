/-
# An explicit Lehmer-type error bound from Rademacher's series

With `U = u₁(n) = π√((2/3)(n − 1/24))` and `K = (π/12)^{3/2}·2π·4/√π`:

  `|p(n) − M(n)| ≤ K e^{U/2}`,   `M(n) = K e^U (U − 1)/(2U³)`   (`p_sub_main_le`, `n ≥ 2`).

The proof needs no error constants from the proof of Rademacher's formula, only its limit. Since
`|A_k| ≤ k` (each `|ω_{h,k}| = 1`) and `(u cosh u − sinh u)/u³ ≤ cosh(u)/3`, the `k`-th term is at most
`(K/3) e^{U/2} k^{−3/2}` for `k ≥ 2`, and `Σ_{k≥2} k^{−3/2} ≤ 2`. The first term is
`K(U cosh U − sinh U)/U³ = M(n) + K e^{−U}(U+1)/(2U³)`.
-/
import RamanujanTau.Rademacher.Closed
import RamanujanTau.Rademacher.DedekindOmega

set_option autoImplicit false

namespace Rademacher
open Real Filter
open scoped Topology

noncomputable section

/-! ### `0 ≤ u cosh u − sinh u ≤ u³ cosh u / 3` -/

lemma hasDerivAt_G (u : ℝ) : HasDerivAt (fun u => u * cosh u - sinh u) (u * sinh u) u := by
  have := ((hasDerivAt_id u).mul (hasDerivAt_cosh u)).sub (hasDerivAt_sinh u)
  convert this using 1; simp

lemma G_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ u * cosh u - sinh u := by
  have hmono : MonotoneOn (fun u => u * cosh u - sinh u) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_id.mul continuous_cosh).sub continuous_sinh |>.continuousOn
    · exact fun x _ => (hasDerivAt_G x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      rw [(hasDerivAt_G x).deriv]
      exact mul_nonneg hx.le (sinh_nonneg_iff.mpr hx.le)
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
  simpa using this

lemma hasDerivAt_H (u : ℝ) :
    HasDerivAt (fun u => u ^ 3 * cosh u / 3 - (u * cosh u - sinh u))
      (u * (u * cosh u - sinh u) + u ^ 3 * sinh u / 3) u := by
  have h1 := (((hasDerivAt_pow 3 u).mul (hasDerivAt_cosh u)).div_const 3).sub (hasDerivAt_G u)
  convert h1 using 1; push_cast; ring

lemma G_le {u : ℝ} (hu : 0 ≤ u) : u * cosh u - sinh u ≤ u ^ 3 * cosh u / 3 := by
  have hmono : MonotoneOn (fun u => u ^ 3 * cosh u / 3 - (u * cosh u - sinh u)) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (((continuous_pow 3).mul continuous_cosh).div_const 3).sub
        ((continuous_id.mul continuous_cosh).sub continuous_sinh) |>.continuousOn
    · exact fun x _ => (hasDerivAt_H x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      rw [(hasDerivAt_H x).deriv]
      have := G_nonneg hx.le
      have := sinh_nonneg_iff.mpr hx.le
      positivity
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
  simp at this
  linarith

lemma cosh_le_exp {x : ℝ} (hx : 0 ≤ x) : cosh x ≤ exp x := by
  rw [cosh_eq]
  have : exp (-x) ≤ exp x := exp_le_exp.mpr (by linarith)
  linarith

/-! ### `|A_k(n)| ≤ k` and `A_1(n) = 1` -/

lemma norm_Ak_le (k n : ℕ) (hk : 0 < k) : ‖Ak k n‖ ≤ k := by
  unfold Ak
  refine (norm_sum_le _ _).trans ?_
  have : ∀ h ∈ (Finset.range k).filter (fun h => Nat.Coprime h k),
      ‖omega h k * Complex.exp (-(2 * π * Complex.I * n * h / k))‖ = 1 := by
    intro h hh
    rw [norm_mul, (omega_spec hk (Finset.mem_filter.mp hh).2).1, one_mul, Complex.norm_exp]
    have : (-(2 * π * Complex.I * n * h / k)).re = 0 := by
      rw [show (2 * π * Complex.I * n * h / k : ℂ) = ((2 * π * n * h / k : ℝ) : ℂ) * Complex.I by push_cast; ring]
      simp
    rw [this, Real.exp_zero]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range k).le

lemma Ak_one (n : ℕ) : Ak 1 n = 1 := by
  rw [Ak, show (Finset.range 1).filter (fun h => Nat.Coprime h 1) = {0} by decide, Finset.sum_singleton,
    omega_zero_one]
  simp

/-! ### the terms -/

/-- `K = (π/12)^{3/2}·2π·4/√π`. -/
def Kc : ℝ := (π / 12) ^ (3 / 2 : ℝ) * (2 * π) * 4 / √π

lemma Kc_pos : 0 < Kc := by unfold Kc; have := pi_pos; positivity

lemma uk_eq {k n : ℕ} (hk : 0 < k) : uk k n = uk 1 n / k := by
  unfold uk; rw [Nat.cast_one, div_one]; field_simp

lemma uk_pos {k n : ℕ} (hk : 0 < k) (hn : 1 ≤ n) : 0 < uk k n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  unfold uk
  have : 0 < (2 / 3) * ((n : ℝ) - 1 / 24) := by nlinarith
  have := pi_pos
  positivity

lemma radTerm_eq {k n : ℕ} (hk : 0 < k) (hn : 1 ≤ n) :
    radTerm k n = Kc * (k : ℝ) ^ (-(5 / 2 : ℝ)) * ((uk k n * cosh (uk k n) - sinh (uk k n)) / uk k n ^ 3) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hu := uk_pos hk hn
  have hsp : 0 < √π := Real.sqrt_pos.mpr pi_pos
  rw [radTerm, Kc, div_mul_eq_div_div, Real.div_rpow (by have := pi_pos; positivity) (by positivity)]
  have h52 : (k : ℝ) ^ (-(5 / 2 : ℝ)) = 1 / ((k : ℝ) ^ (3 / 2 : ℝ) * k) := by
    rw [Real.rpow_neg hkr.le, show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hkr, Real.rpow_one]
    ring
  rw [h52]
  have : (0 : ℝ) < (k : ℝ) ^ (3 / 2 : ℝ) := by positivity
  field_simp

lemma radTerm_nonneg {k n : ℕ} (hk : 0 < k) (hn : 1 ≤ n) : 0 ≤ radTerm k n := by
  rw [radTerm_eq hk hn]
  have := G_nonneg (uk_pos hk hn).le
  have := Kc_pos
  have := uk_pos hk hn
  positivity

/-- `k · radTerm(k) ≤ (K/3) e^{U/2} k^{−3/2}` for `k ≥ 2`. -/
lemma k_radTerm_le {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n) :
    k * radTerm k n ≤ Kc / 3 * exp (uk 1 n / 2) * (k : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hk0 : 0 < k := by omega
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hu := uk_pos hk0 hn
  have hU := uk_pos one_pos hn
  rw [radTerm_eq hk0 hn]
  have hG := G_le hu.le
  have h1 : (uk k n * cosh (uk k n) - sinh (uk k n)) / uk k n ^ 3 ≤ cosh (uk k n) / 3 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have h2 : cosh (uk k n) ≤ exp (uk 1 n / 2) := by
    refine (cosh_le_cosh.mpr ?_).trans (cosh_le_exp (by positivity))
    rw [abs_of_pos hu, abs_of_pos (by positivity), uk_eq hk0]
    exact div_le_div_of_nonneg_left hU.le (by norm_num) hkr
  have h3 : (k : ℝ) * (k : ℝ) ^ (-(5 / 2 : ℝ)) = (k : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [show (-(3 / 2 : ℝ)) = 1 + (-(5 / 2 : ℝ)) by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
  have hK := Kc_pos
  have hkp : 0 < (k : ℝ) ^ (-(5 / 2 : ℝ)) := by positivity
  calc (k : ℝ) * (Kc * (k : ℝ) ^ (-(5 / 2 : ℝ)) * ((uk k n * cosh (uk k n) - sinh (uk k n)) / uk k n ^ 3))
      ≤ (k : ℝ) * (Kc * (k : ℝ) ^ (-(5 / 2 : ℝ)) * (exp (uk 1 n / 2) / 3)) := by
        have h4 : (uk k n * cosh (uk k n) - sinh (uk k n)) / uk k n ^ 3 ≤ exp (uk 1 n / 2) / 3 := by linarith
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 (by positivity)) (by positivity)
    _ = Kc / 3 * exp (uk 1 n / 2) * ((k : ℝ) * (k : ℝ) ^ (-(5 / 2 : ℝ))) := by ring
    _ = _ := by rw [h3]

/-- `k^{−3/2} ≤ 2(1/√(k−1) − 1/√k)`. -/
lemma rpow_le_tele {k : ℕ} (hk : 2 ≤ k) :
    (k : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 2 * (1 / √((k - 1 : ℕ) : ℝ) - 1 / √(k : ℝ)) := by
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set x := √(k : ℝ) with hx
  set y := √((k - 1 : ℕ) : ℝ) with hy
  have hx2 : x ^ 2 = k := Real.sq_sqrt (by linarith)
  have hy2 : y ^ 2 = k - 1 := by
    rw [hy, Real.sq_sqrt (by positivity)]; push_cast [Nat.cast_sub (by omega : 1 ≤ k)]; ring
  have hxp : 0 < x := Real.sqrt_pos.mpr (by linarith)
  have h1 : (1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k - 1)
  have hyp : 0 < y := Real.sqrt_pos.mpr (by linarith)
  have hyx : y ≤ x := by nlinarith
  have hpow : (k : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / x ^ 3 := by
    rw [Real.rpow_neg (by linarith), hx, ← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]
    norm_num
  rw [hpow]
  have key : 1 / x ^ 3 ≤ 2 / ((x + y) * x * y) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hxp hyp]
  have : 2 / ((x + y) * x * y) = 2 * (1 / y - 1 / x) := by
    field_simp
    nlinarith
  linarith

lemma sum_rpow_le (N : ℕ) : ∑ k ∈ Finset.range N, ((k + 2 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 2 := by
  have : ∀ N : ℕ, ∑ k ∈ Finset.range N, ((k + 2 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 2 * (1 - 1 / √((N + 1 : ℕ) : ℝ)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have := rpow_le_tele (k := N + 2) (by omega)
      rw [show N + 2 - 1 = N + 1 by omega] at this
      have e : ((N + 1 + 1 : ℕ) : ℝ) = ((N + 2 : ℕ) : ℝ) := by push_cast; ring
      rw [e]
      linarith
  refine (this N).trans ?_
  have : 0 ≤ 1 / √((N + 1 : ℕ) : ℝ) := by positivity
  linarith

/-! ### the bound -/

/-- the main term `M(n) = K e^U (U − 1)/(2U³)`. -/
def Mmain (n : ℕ) : ℝ := Kc * exp (uk 1 n) * (uk 1 n - 1) / (2 * uk 1 n ^ 3)

lemma sum_Icc_eq (N : ℕ) (f : ℕ → ℂ) : ∑ k ∈ Finset.Icc 1 (N + 1), f k = f 1 + ∑ k ∈ Finset.range N, f (k + 2) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, show N + 1 + 1 - 1 = N + 1 by omega,
    Finset.sum_range_succ']
  simp only [add_comm 1]
  rw [add_comm]

theorem p_sub_radTerm_le (n : ℕ) (hn : 1 ≤ n) :
    |(HardyRamanujan.p n : ℝ) - radTerm 1 n| ≤ 2 * Kc / 3 * exp (uk 1 n / 2) := by
  have hT := rademacher n hn
  have hlim : Tendsto (fun N : ℕ => ‖∑ k ∈ Finset.Icc 1 (N + 1), Ak k n * (radTerm k n : ℂ) - radTerm 1 n‖)
      atTop (𝓝 ‖(HardyRamanujan.p n : ℂ) - radTerm 1 n‖) :=
    ((hT.comp (tendsto_add_atTop_nat 1)).sub_const _).norm
  have hbd : ∀ N : ℕ, ‖∑ k ∈ Finset.Icc 1 (N + 1), Ak k n * (radTerm k n : ℂ) - radTerm 1 n‖ ≤
      2 * Kc / 3 * exp (uk 1 n / 2) := by
    intro N
    rw [sum_Icc_eq, Ak_one, one_mul, add_sub_cancel_left]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ k ∈ Finset.range N, ‖Ak (k + 2) n * (radTerm (k + 2) n : ℂ)‖ ≤
        Kc / 3 * exp (uk 1 n / 2) * ((k + 2 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
      intro k _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (radTerm_nonneg (by omega) hn)]
      refine (mul_le_mul_of_nonneg_right (norm_Ak_le _ _ (by omega)) (radTerm_nonneg (by omega) hn)).trans ?_
      exact k_radTerm_le (by omega) hn
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have := sum_rpow_le N
    have : 0 ≤ Kc / 3 * exp (uk 1 n / 2) := by have := Kc_pos; positivity
    nlinarith
  have := le_of_tendsto' hlim hbd
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
  exact this

lemma radTerm_one_eq (n : ℕ) (hn : 1 ≤ n) :
    radTerm 1 n = Mmain n + Kc * exp (-uk 1 n) * (uk 1 n + 1) / (2 * uk 1 n ^ 3) := by
  have hu := uk_pos one_pos hn
  rw [radTerm_eq one_pos hn, Nat.cast_one, Real.one_rpow, mul_one, Mmain, cosh_eq, sinh_eq]
  field_simp
  ring

/-- **the explicit error bound** `|p(n) − M(n)| ≤ K e^{U/2}` (`n ≥ 2`). -/
theorem p_sub_main_le (n : ℕ) (hn : 2 ≤ n) :
    |(HardyRamanujan.p n : ℝ) - Mmain n| ≤ Kc * exp (uk 1 n / 2) := by
  have hn1 : 1 ≤ n := by omega
  have hU := uk_pos one_pos hn1
  have hU3 : 3 ≤ uk 1 n := by
    have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h9 : 9 ≤ uk 1 n ^ 2 := by
      rw [uk, Nat.cast_one, div_one, mul_pow, Real.sq_sqrt (by nlinarith)]
      have := pi_gt_three
      nlinarith
    nlinarith
  have h1 := p_sub_radTerm_le n hn1
  rw [radTerm_one_eq n hn1] at h1
  have hK := Kc_pos
  have hsmall : Kc * exp (-uk 1 n) * (uk 1 n + 1) / (2 * uk 1 n ^ 3) ≤ Kc / 3 * exp (uk 1 n / 2) := by
    have he : exp (-uk 1 n) ≤ exp (uk 1 n / 2) := exp_le_exp.mpr (by linarith)
    have hr : (uk 1 n + 1) / (2 * uk 1 n ^ 3) ≤ 1 / 3 := by
      have h9 : 9 ≤ uk 1 n ^ 2 := by nlinarith
      have h27 : 27 ≤ uk 1 n ^ 3 := by nlinarith
      rw [div_le_iff₀ (by positivity)]; nlinarith
    calc Kc * exp (-uk 1 n) * (uk 1 n + 1) / (2 * uk 1 n ^ 3)
        = Kc * exp (-uk 1 n) * ((uk 1 n + 1) / (2 * uk 1 n ^ 3)) := by ring
      _ ≤ Kc * exp (uk 1 n / 2) * (1 / 3) := by gcongr
      _ = _ := by ring
  have hpos : 0 ≤ Kc * exp (-uk 1 n) * (uk 1 n + 1) / (2 * uk 1 n ^ 3) := by positivity
  rw [abs_le] at h1 ⊢
  constructor <;> nlinarith

end

end Rademacher
