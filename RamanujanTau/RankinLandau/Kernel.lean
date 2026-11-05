/-
# The dual kernel of the weight-`(m+1)` Rankin–Selberg functional equation

With `γₘ(s) = 2π^{−s}Γ(s)Γ(s+m)(4π)^{−s−m}` (`RankinErrorGeneral.gamM`) and the Riesz factor
`P_j(s) = j!/(s(s+1)⋯(s+j))`, the functional equation `ζ(2s)D(s) = Δ(s) ζ(2−2s)D(1−s)`,
`Δ(s) = γₘ(1−s)/γₘ(s)`, produces the kernel factor

    Q_j(s) = P_j(s) Δ(s) = R_j(s) γₘ(1−s),
    R_j(s) = j! π^s (4π)^{s+m}/2 · Γ(s+j+1)⁻¹ Γ(s+m)⁻¹          (entire),

and `Q_j` is holomorphic on `Re s < 1`. The dual kernels are

    J_j^{(σ)}(y) = (1/2π) ∫ y^{σ+it+j} Q_j(σ+it) dt.

`Qk_bound`: on `A₀ ≤ Re s ≤ 1/2`, `‖Q_j(s)‖ ≤ K (1+|Im s|)^{1−4A₀−j}` (the exponent
`1 − 4σ − j` is the degree-4 count `(1/2−σ)·4 − (j+1)`), from the uniform `Γ`-ratio bound.
No phase information is used.
-/
import RamanujanTau.RankinLandau.GammaUnif
import RamanujanTau.RankinErrorGeneral.Gamma

set_option autoImplicit false

namespace RamanujanTau.RankinLandau

open Complex Real MeasureTheory Set Filter Topology Finset
open RamanujanTau.RankinErrorGeneral

/-- `R_j(s) = j! π^s (4π)^{s+m}/2 · Γ(s+j+1)⁻¹ Γ(s+m)⁻¹ = P_j(s) γₘ(s)⁻¹`. -/
noncomputable def Rk (m j : ℕ) (s : ℂ) : ℂ :=
  (j.factorial : ℂ) * ((π : ℂ) ^ s * ((4 * π : ℝ) : ℂ) ^ (s + m) / 2) *
    (Complex.Gamma (s + j + 1))⁻¹ * (Complex.Gamma (s + m))⁻¹

/-- The kernel factor `Q_j(s) = R_j(s) γₘ(1−s)`. -/
noncomputable def Qk (m j : ℕ) (s : ℂ) : ℂ := Rk m j s * gamM m (1 - s)

/-- The dual kernel on the line `Re s = σ`. -/
noncomputable def Jc (m j : ℕ) (σ y : ℝ) : ℂ :=
  ((1 / (2 * π) : ℝ) : ℂ) * ∫ t : ℝ, (y : ℂ) ^ ((σ : ℂ) + t * I + j) * Qk m j (σ + t * I)

lemma Rk_succ_mul (m j : ℕ) (s : ℂ) :
    Rk m (j + 1) s * (s + (j + 1 : ℕ)) = ((j : ℂ) + 1) * Rk m j s := by
  unfold Rk
  have e := inv_Gamma_eq_mul (s + j + 1)
  rw [show s + ((j + 1 : ℕ) : ℂ) + 1 = s + j + 1 + 1 by push_cast; ring]
  rw [e, Nat.factorial_succ]
  push_cast
  ring

lemma Qk_succ_mul (m j : ℕ) (s : ℂ) :
    Qk m (j + 1) s * (s + (j + 1 : ℕ)) = ((j : ℂ) + 1) * Qk m j s := by
  unfold Qk
  rw [mul_right_comm, Rk_succ_mul]; ring

lemma differentiable_Rk (m j : ℕ) : Differentiable ℂ (Rk m j) := by
  intro s
  have h3 : DifferentiableAt ℂ (fun s => (Complex.Gamma (s + j + 1))⁻¹) s := by
    have := (Complex.differentiable_one_div_Gamma (s + j + 1)).comp s
      ((differentiableAt_id.add_const (j : ℂ)).add_const 1)
    simpa [Function.comp_def] using this
  have h4 : DifferentiableAt ℂ (fun s => (Complex.Gamma (s + m))⁻¹) s := by
    have := (Complex.differentiable_one_div_Gamma (s + m)).comp s
      (differentiableAt_id.add_const (m : ℂ))
    simpa [Function.comp_def] using this
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h4pi : ((4 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (4 * π : ℝ) ≠ 0)
  unfold Rk
  exact (((differentiableAt_const _).mul (((differentiableAt_id.const_cpow (Or.inl hpi)).mul
    ((differentiableAt_id.add_const _).const_cpow (Or.inl h4pi))).div_const 2)).mul h3).mul h4

lemma differentiableAt_Gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z := by
  refine Complex.differentiableAt_Gamma z (fun n h => ?_)
  rw [h] at hz; simp at hz; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]

lemma differentiableOn_Qk (m j : ℕ) : DifferentiableOn ℂ (Qk m j) {s : ℂ | s.re < 1} := by
  intro s hs
  simp only [mem_setOf_eq] at hs
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h4pi : ((4 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (4 * π : ℝ) ≠ 0)
  have g1 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (1 - s)) s := by
    have := (differentiableAt_Gamma_of_re_pos (z := 1 - s) (by simp; linarith)).comp s
      ((differentiableAt_const 1).sub differentiableAt_id)
    simpa [Function.comp_def] using this
  have g2 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (1 - s + m)) s := by
    have := (differentiableAt_Gamma_of_re_pos (z := 1 - s + m)
      (by simp; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])).comp s
      (((differentiableAt_const 1).sub differentiableAt_id).add_const (m : ℂ))
    simpa [Function.comp_def] using this
  have hG : DifferentiableAt ℂ (fun s => gamM m (1 - s)) s := by
    unfold gamM
    refine ((((differentiableAt_const 2).mul ?_).mul g1).mul g2).mul ?_
    · exact ((differentiableAt_const 1).sub differentiableAt_id).neg.const_cpow (Or.inl hpi)
    · exact (((differentiableAt_const 1).sub differentiableAt_id).neg.sub_const _).const_cpow
        (Or.inl h4pi)
  exact ((differentiable_Rk m j s).mul hG).differentiableWithinAt

/-! ### The modulus of `Q_j` in vertical strips -/

lemma one_add_abs_le_three_norm_one_sub {s : ℂ} (hs : s.re ≤ 1 / 2) :
    1 + |s.im| ≤ 3 * ‖1 - s‖ := by
  have h1 : |s.im| ≤ ‖1 - s‖ := by
    have := Complex.abs_im_le_norm (1 - s); simpa using this
  have h2 : 1 / 2 ≤ ‖1 - s‖ := by
    have := Complex.abs_re_le_norm (1 - s); simp at this
    have : 1 - s.re ≤ |1 - s.re| := le_abs_self _
    linarith
  linarith

/-- **The phase-free strip bound.** -/
theorem Qk_bound (m j : ℕ) (hm : 1 ≤ m) {A₀ : ℝ} (hA : A₀ ≤ 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, A₀ ≤ s.re → s.re ≤ 1 / 2 →
      ‖Qk m j s‖ ≤ K * (1 + |s.im|) ^ (1 - 4 * A₀ - j) := by
  set N : ℕ := ⌈1 - A₀⌉₊ with hN
  have hNA : 1 - A₀ ≤ N := Nat.le_ceil _
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  set R₁ : ℝ := 2 - A₀ + m + j + N + 2 with hR₁
  have hR₁1 : 1 ≤ R₁ := by rw [hR₁]; linarith
  obtain ⟨C, hC0, hC⟩ := norm_Gamma_ratio_unif' hR₁1
  set R₂ : ℝ := |A₀| + j + m + N + 2 with hR₂
  have hR₂1 : 1 ≤ R₂ := by rw [hR₂]; linarith [abs_nonneg A₀]
  set K : ℝ := (j.factorial : ℝ) * C ^ 2 * R₂ ^ (2 * N) * 3 with hK
  refine ⟨K, by positivity, fun s h1 h2 => ?_⟩
  set σ : ℝ := s.re with hσ
  set t : ℝ := s.im with ht
  have ht0 : (0 : ℝ) < 1 + |t| := by positivity
  have hs1 : 1 - s ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hΓ1 : Complex.Gamma (1 - s) = Complex.Gamma (2 - s) / (1 - s) := by
    rw [eq_div_iff hs1, show (2 : ℂ) - s = 1 - s + 1 by ring, Complex.Gamma_add_one _ hs1]
    ring
  have hw₁re : (s + j + 1 + N).re = σ + j + 1 + N := by simp [hσ]
  have hw₂re : (s + m + N).re = σ + m + N := by simp [hσ]
  have hw₁im : (s + j + 1 + N).im = t := by simp [ht]
  have hw₂im : (s + m + N).im = t := by simp [ht]
  have hσabs : |σ| ≤ |A₀| + 1 / 2 := by
    rcases le_total 0 σ with h | h
    · rw [abs_of_nonneg h]; linarith [abs_nonneg A₀]
    · rw [abs_of_nonpos h]; linarith [neg_abs_le A₀]
  -- the two `Γ`-ratios
  have r1 : ‖Complex.Gamma (2 - s)‖ * ‖Complex.Gamma (s + j + 1 + N)‖⁻¹ ≤
      C * (1 + |t|) ^ (1 - 2 * σ - j - N) := by
    have hpos : 0 < ‖Complex.Gamma (s + j + 1 + N)‖ := norm_pos_iff.2
      (Complex.Gamma_ne_zero_of_re_pos (by rw [hw₁re]; linarith))
    have := hC (2 - s) (s + j + 1 + N) (by simp [← hσ]; linarith) (by simp [← hσ]; rw [hR₁]; linarith)
      (by rw [hw₁re]; linarith) (by rw [hw₁re, hR₁]; linarith)
      (by rw [hw₁im]; simp [ht])
    rw [hw₁im, hw₁re, show (2 - s).re = 2 - σ by simp [hσ],
      show 2 - σ - (σ + j + 1 + N) = 1 - 2 * σ - j - N by ring] at this
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]; exact this
  have r2 : ‖Complex.Gamma (1 - s + m)‖ * ‖Complex.Gamma (s + m + N)‖⁻¹ ≤
      C * (1 + |t|) ^ (1 - 2 * σ - N) := by
    have hpos : 0 < ‖Complex.Gamma (s + m + N)‖ := norm_pos_iff.2
      (Complex.Gamma_ne_zero_of_re_pos (by rw [hw₂re]; linarith))
    have := hC (1 - s + m) (s + m + N) (by simp [← hσ]; linarith) (by simp [← hσ]; rw [hR₁]; linarith)
      (by rw [hw₂re]; linarith) (by rw [hw₂re, hR₁]; linarith)
      (by rw [hw₂im]; simp [ht])
    rw [hw₂im, hw₂re, show (1 - s + m).re = 1 - σ + m by simp [hσ],
      show 1 - σ + m - (σ + m + N) = 1 - 2 * σ - N by ring] at this
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]; exact this
  -- the two products
  have p1 : ‖∏ i ∈ range N, (s + j + 1 + i)‖ ≤ (R₂ * (1 + |t|)) ^ N := by
    have := norm_prod_add_le (s + j + 1) N hR₂1 (by
      have : |(s + j + 1).re| ≤ |σ| + j + 1 := by
        simp only [add_re, natCast_re, one_re, ← hσ]
        calc |σ + j + 1| ≤ |σ + j| + |(1:ℝ)| := abs_add_le _ _
          _ ≤ |σ| + j + 1 := by
              have := abs_add_le σ (j:ℝ); rw [abs_of_nonneg hj0] at this; rw [abs_one]; linarith
      rw [hR₂]; linarith)
    simpa [ht] using this
  have p2 : ‖∏ i ∈ range N, (s + m + i)‖ ≤ (R₂ * (1 + |t|)) ^ N := by
    have := norm_prod_add_le (s + m) N hR₂1 (by
      have : |(s + m).re| ≤ |σ| + m := by
        simp only [add_re, natCast_re, ← hσ]
        calc |σ + m| ≤ |σ| + |(m:ℝ)| := abs_add_le _ _
          _ = |σ| + m := by rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) m)]
      rw [hR₂]; linarith)
    simpa [ht] using this
  -- the exponential constants
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h4pi : (0 : ℝ) < 4 * π := by positivity
  have c1 : π ^ σ * (4 * π) ^ (σ + m) / 2 * (2 * π ^ (σ - 1) * (4 * π) ^ (σ - 1 - m)) ≤ 1 := by
    have ea : π ^ σ * π ^ (σ - 1) = π ^ (2 * σ - 1) := by
      rw [← Real.rpow_add hpi]; congr 1; ring
    have eb : (4 * π) ^ (σ + m) * (4 * π) ^ (σ - 1 - m) = (4 * π) ^ (2 * σ - 1) := by
      rw [← Real.rpow_add h4pi]; congr 1; ring
    have e : π ^ σ * (4 * π) ^ (σ + m) / 2 * (2 * π ^ (σ - 1) * (4 * π) ^ (σ - 1 - m)) =
        π ^ (2 * σ - 1) * (4 * π) ^ (2 * σ - 1) := by
      rw [← ea, ← eb]; ring
    rw [e]
    have hpi1 : 1 ≤ π := by linarith [Real.pi_gt_three]
    exact mul_le_one₀ (Real.rpow_le_one_of_one_le_of_nonpos hpi1 (by linarith))
      (by positivity) (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith))
  have d1 : ‖1 - s‖⁻¹ ≤ 3 * (1 + |t|) ^ (-1 : ℝ) := by
    have := one_add_abs_le_three_norm_one_sub h2
    rw [Real.rpow_neg_one, ← ht] at *
    have hpos : 0 < ‖1 - s‖ := norm_pos_iff.2 hs1
    rw [inv_le_iff_one_le_mul₀ hpos]
    calc (1 : ℝ) = (1 + |t|) * (1 + |t|)⁻¹ := (mul_inv_cancel₀ ht0.ne').symm
      _ ≤ (3 * ‖1 - s‖) * (1 + |t|)⁻¹ := by gcongr
      _ = 3 * (1 + |t|)⁻¹ * ‖1 - s‖ := by ring
  -- the norm identity
  have hnorm : ‖Qk m j s‖ = (j.factorial : ℝ) *
      (π ^ σ * (4 * π) ^ (σ + m) / 2 * (2 * π ^ (σ - 1) * (4 * π) ^ (σ - 1 - m))) *
      (‖Complex.Gamma (2 - s)‖ * ‖Complex.Gamma (s + j + 1 + N)‖⁻¹) *
      (‖Complex.Gamma (1 - s + m)‖ * ‖Complex.Gamma (s + m + N)‖⁻¹) *
      ‖∏ i ∈ range N, (s + j + 1 + i)‖ * ‖∏ i ∈ range N, (s + m + i)‖ * ‖1 - s‖⁻¹ := by
    unfold Qk Rk gamM
    rw [inv_Gamma_eq_prod (s + j + 1) N, inv_Gamma_eq_prod (s + m) N, hΓ1]
    simp only [norm_mul, norm_div, norm_inv, Complex.norm_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hpi, Complex.norm_cpow_eq_rpow_re_of_pos h4pi,
      Complex.norm_ofNat]
    simp only [add_re, sub_re, neg_re, one_re, natCast_re, ← hσ]
    ring
  -- assemble
  have hfac : (0 : ℝ) ≤ (j.factorial : ℝ) := by positivity
  have hE : (1 + |t|) ^ (1 - 4 * σ - j) ≤ (1 + |t|) ^ (1 - 4 * A₀ - j) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (by linarith)
  have hNpow : ((R₂ * (1 + |t|)) ^ N) * ((R₂ * (1 + |t|)) ^ N) =
      R₂ ^ (2 * N) * (1 + |t|) ^ ((2 * N : ℕ) : ℝ) := by
    rw [Real.rpow_natCast, ← pow_add, ← mul_pow, two_mul]
  rw [hnorm]
  calc (j.factorial : ℝ) *
      (π ^ σ * (4 * π) ^ (σ + m) / 2 * (2 * π ^ (σ - 1) * (4 * π) ^ (σ - 1 - m))) *
      (‖Complex.Gamma (2 - s)‖ * ‖Complex.Gamma (s + j + 1 + N)‖⁻¹) *
      (‖Complex.Gamma (1 - s + m)‖ * ‖Complex.Gamma (s + m + N)‖⁻¹) *
      ‖∏ i ∈ range N, (s + j + 1 + i)‖ * ‖∏ i ∈ range N, (s + m + i)‖ * ‖1 - s‖⁻¹
      ≤ (j.factorial : ℝ) * 1 * (C * (1 + |t|) ^ (1 - 2 * σ - j - N)) *
        (C * (1 + |t|) ^ (1 - 2 * σ - N)) * (R₂ * (1 + |t|)) ^ N * (R₂ * (1 + |t|)) ^ N *
        (3 * (1 + |t|) ^ (-1 : ℝ)) := by
        gcongr
    _ = ((j.factorial : ℝ) * C * C * 3) * ((R₂ * (1 + |t|)) ^ N * (R₂ * (1 + |t|)) ^ N) *
          ((1 + |t|) ^ (1 - 2 * σ - j - N) * (1 + |t|) ^ (1 - 2 * σ - N) * (1 + |t|) ^ (-1 : ℝ)) := by
        ring
    _ = K * ((1 + |t|) ^ (1 - 2 * σ - j - N) * (1 + |t|) ^ (1 - 2 * σ - N) *
          (1 + |t|) ^ ((2 * N : ℕ) : ℝ) * (1 + |t|) ^ (-1 : ℝ)) := by
        rw [hNpow, hK]; ring
    _ = K * (1 + |t|) ^ (1 - 4 * σ - j) := by
        rw [← Real.rpow_add ht0, ← Real.rpow_add ht0, ← Real.rpow_add ht0]
        congr 2; push_cast; ring
    _ ≤ K * (1 + |t|) ^ (1 - 4 * A₀ - j) := by gcongr

end RamanujanTau.RankinLandau

#print axioms RamanujanTau.RankinLandau.Qk_succ_mul
#print axioms RamanujanTau.RankinLandau.differentiableOn_Qk
#print axioms RamanujanTau.RankinLandau.Qk_bound
