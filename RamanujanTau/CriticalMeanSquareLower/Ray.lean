/-
# Lower bound for the ray integral of `|Δ|²`

`CriticalMeanSquare.weighted_parseval` turns the weighted critical-line mean square of `Λ(Δ,·)` into
`2π ∫ e^{12u} |Δ(i e^{u+iβ})|² du`, an integral of `|Δ|²` along the ray `τ = −w + iκw`
(`κ = cot β`, `w > 0`).

Here we show this ray integral is `≫ κ^{-12} log(1/κ)`.  The argument avoids Ford circles:
on each unit block `w ∈ [N, N+1]` the ray moves vertically by only `κ`, so `|Δ(−w+iκw)|²` is
compared with the horizontal values `|Δ(−w+iκN)|²` (a Cauchy-estimate Lipschitz bound,
`exists_Dc_lip`), whose integral over a period is `Σ τ(n)² e^{-4πnκN} ≫ (κN)^{-12}` by
Parseval on horizontal lines and the Rankin lower bound `Σ_{n≤N} τ(n)² ≫ N¹²`.  Each block then
contributes `≫ κ^{-12}/N − O(κ^{-12}/N³)`, and summing `N₁ ≤ N < 1/κ` gives the logarithm.
-/
import RamanujanTau.CriticalMeanSquare.Parseval
import RamanujanTau.RankinSelberg.Main

set_option autoImplicit false

namespace RamanujanTau.CriticalMeanSquareLower

open Complex MeasureTheory Set Filter Topology
open UpperHalfPlane hiding I
open RamanujanTau.HeckeL RamanujanTau.HardyZeros RamanujanTau.HardyCountHafner
  RamanujanTau.CriticalMeanSquare
open scoped Real

/-- The point `x + iy`. -/
noncomputable def pt (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * I

@[simp] lemma pt_im (x y : ℝ) : (pt x y).im = y := by simp [pt]
@[simp] lemma pt_re (x y : ℝ) : (pt x y).re = x := by simp [pt]

lemma continuousOn_Dc : ContinuousOn Dc {z : ℂ | 0 < z.im} := Dc_differentiableOn.continuousOn

/-- Horizontal mean `H(y) = ∫₀¹ |Δ(x+iy)|² dx`. -/
noncomputable def Hh (y : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, ‖Dc (pt x y)‖ ^ 2

lemma Dc_pt_eq {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Dc (pt x y) = RankinSelberg.Δf (RankinSelberg.hp hy x) := by
  have h : 0 < (pt x y).im := by simpa using hy
  rw [Dc_of_im_pos h]; rfl

lemma hasSum_Hh {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => ((tau n : ℝ)) ^ 2 * Real.exp (-2 * π * y) ^ (2 * n)) (Hh y) := by
  have h := RankinSelberg.hasSum_tau_sq hy
  have e : Hh y = ∫ x in (0 : ℝ)..1, ‖RankinSelberg.Δf (RankinSelberg.hp hy x)‖ ^ 2 := by
    unfold Hh
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    show ‖Dc (pt x y)‖ ^ 2 = _
    rw [Dc_pt_eq hy]
  rw [e]; exact h

/-- **Horizontal lower bound**: `H(y) ≥ k / y¹²` for `0 < y ≤ 1`. -/
theorem exists_Hh_lower : ∃ k : ℝ, 0 < k ∧ ∀ y : ℝ, 0 < y → y ≤ 1 → k / y ^ 12 ≤ Hh y := by
  obtain ⟨k, hk0, hk⟩ := RankinSelberg.exists_sum_tau_sq_ge
  refine ⟨k * Real.exp (-4 * π) / 2 ^ 12, by positivity, fun y hy hy1 => ?_⟩
  set N : ℕ := ⌊1 / y⌋₊ with hNdef
  have hy1' : (1 : ℝ) ≤ 1 / y := by rw [le_div_iff₀ hy]; linarith
  have hN1 : 1 ≤ N := Nat.le_floor (by simpa using hy1')
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNy : (N : ℝ) * y ≤ 1 := by
    have := Nat.floor_le (show 0 ≤ 1 / y by positivity)
    calc (N : ℝ) * y ≤ (1 / y) * y := by gcongr
      _ = 1 := by field_simp
  have hN2 : 1 ≤ 2 * y * N := by
    have h1 := Nat.lt_floor_add_one (1 / y)
    rw [← hNdef] at h1
    have h2 : 1 < y * (N + 1) := by
      rw [div_lt_iff₀ hy] at h1; linarith
    nlinarith
  -- partial sum
  set r : ℝ := Real.exp (-2 * π * y)
  have hpart := sum_le_hasSum (Finset.Icc 1 N) (fun n _ => by positivity) (hasSum_Hh hy)
  have hterm : ∀ n ∈ Finset.Icc 1 N, ((tau n : ℝ)) ^ 2 * Real.exp (-4 * π) ≤
      ((tau n : ℝ)) ^ 2 * r ^ (2 * n) := by
    intro n hn
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    gcongr
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    have hny : (n : ℝ) * y ≤ 1 := by nlinarith
    have := mul_le_mul_of_nonneg_left hny Real.pi_pos.le
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul] at hsum
  have hkN := hk N hN1
  have hpow : (1 / y) ^ 12 ≤ (2 : ℝ) ^ 12 * (N : ℝ) ^ 12 := by
    rw [← mul_pow]; gcongr
    rw [div_le_iff₀ hy]; linarith
  have hE : 0 < Real.exp (-4 * π) := Real.exp_pos _
  calc k * Real.exp (-4 * π) / 2 ^ 12 / y ^ 12
      = k * Real.exp (-4 * π) / 2 ^ 12 * (1 / y) ^ 12 := by rw [div_pow]; ring
    _ ≤ k * Real.exp (-4 * π) / 2 ^ 12 * ((2 : ℝ) ^ 12 * (N : ℝ) ^ 12) := by gcongr
    _ = k * (N : ℝ) ^ 12 * Real.exp (-4 * π) := by ring
    _ ≤ (∑ n ∈ Finset.Icc 1 N, ((tau n : ℝ)) ^ 2) * Real.exp (-4 * π) := by gcongr
    _ ≤ _ := hsum.trans hpart

/-- Shifting and reflecting a period. -/
lemma integral_period (y a : ℝ) :
    ∫ w in a..a + 1, ‖Dc (pt (-w) y)‖ ^ 2 = Hh y := by
  have h := intervalIntegral.integral_comp_neg (a := a) (b := a + 1)
    (fun x : ℝ => ‖Dc (pt x y)‖ ^ 2)
  simp only at h
  rw [h]
  have hper : Function.Periodic (fun x : ℝ => ‖Dc (pt x y)‖ ^ 2) 1 := by
    intro x
    simp only
    rw [show pt (x + 1) y = pt x y + 1 by simp [pt]; ring, Dc_add_one]
  have := hper.intervalIntegral_add_eq (-(a + 1)) 0
  rw [show -a = -(a + 1) + 1 by ring, this, zero_add]
  rfl

/-- **Vertical Lipschitz bound** (Cauchy estimate): for `y₀ ≤ y₁, y₂`,
`|Δ(x+iy₁) − Δ(x+iy₂)| ≤ A |y₁ − y₂| / y₀⁷`. -/
theorem exists_Dc_lip : ∃ A : ℝ, 0 ≤ A ∧ ∀ x y₁ y₂ y₀ : ℝ, 0 < y₀ → y₀ ≤ y₁ → y₀ ≤ y₂ →
    ‖Dc (pt x y₁) - Dc (pt x y₂)‖ ≤ A * |y₁ - y₂| / y₀ ^ 7 := by
  obtain ⟨M, hM0, hM⟩ := exists_Delta_bound_exp
  have hMb : ∀ z : ℂ, 0 < z.im → ‖Dc z‖ ≤ M / z.im ^ 6 := by
    intro z hz
    rw [Dc_of_im_pos hz]
    have h := hM ⟨z, hz⟩
    have hy6 : 0 < z.im ^ 6 := by positivity
    have he : 1 ≤ Real.exp (π * z.im) := Real.one_le_exp (by positivity)
    rw [le_div_iff₀ hy6]
    have h0 : 0 ≤ ‖Δf ⟨z, hz⟩‖ * z.im ^ 6 := by positivity
    have : (⟨z, hz⟩ : ℍ).im = z.im := rfl
    rw [this] at h
    nlinarith
  refine ⟨2 ^ 7 * M, by positivity, fun x y₁ y₂ y₀ hy₀ h1 h2 => ?_⟩
  set R : ℝ := y₀ / 2 with hR
  have hR0 : 0 < R := by positivity
  -- derivative bound on `Im ≥ y₀`
  have hder : ∀ z : ℂ, y₀ ≤ z.im → ‖deriv Dc z‖ ≤ 2 ^ 7 * M / y₀ ^ 7 := by
    intro z hz
    have hsub : closure (Metric.ball z R) ⊆ {w : ℂ | 0 < w.im} := by
      rw [closure_ball z hR0.ne']
      intro w hw
      have hd : |w.im - z.im| ≤ R := by
        have := Complex.abs_im_le_norm (w - z)
        rw [Complex.sub_im] at this
        exact this.trans (by simpa [dist_eq_norm] using hw)
      show 0 < w.im
      have := neg_abs_le (w.im - z.im)
      rw [hR] at hd; linarith
    have hd : DiffContOnCl ℂ Dc (Metric.ball z R) :=
      (Dc_differentiableOn.mono hsub).diffContOnCl
    have hsph : ∀ w ∈ Metric.sphere z R, ‖Dc w‖ ≤ M / R ^ 6 := by
      intro w hw
      have hd' : |w.im - z.im| ≤ R := by
        have := Complex.abs_im_le_norm (w - z)
        rw [Complex.sub_im] at this
        exact this.trans (mem_sphere_iff_norm.mp hw).le
      have hwim : R ≤ w.im := by
        have := neg_abs_le (w.im - z.im)
        rw [hR] at hd' ⊢; linarith
      have hw0 : 0 < w.im := by linarith
      refine (hMb w hw0).trans ?_
      gcongr
    have := norm_deriv_le_of_forall_mem_sphere_norm_le hR0 hd hsph
    refine this.trans (le_of_eq ?_)
    rw [hR]; field_simp
  -- mean value theorem along the vertical line
  set φ : ℝ → ℂ := fun y => Dc (pt x y) with hφ
  have hφd : ∀ y ∈ Ici y₀, HasDerivWithinAt φ (deriv Dc (pt x y) * I) (Ici y₀) y := by
    intro y hy
    have hy' : 0 < (pt x y).im := by simp; exact lt_of_lt_of_le hy₀ hy
    have hDa : DifferentiableAt ℂ Dc (pt x y) :=
      Dc_differentiableOn.differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hy')
    have hg : HasDerivAt (fun y : ℝ => pt x y) I y := by
      have := ((hasDerivAt_id (y : ℂ)).comp_ofReal (z := y)).mul_const I
      simp only [id, one_mul] at this
      have h2 := this.const_add (x : ℂ)
      exact h2
    exact (hDa.hasDerivAt.comp y hg).hasDerivWithinAt
  have hbd : ∀ y ∈ Ici y₀, ‖deriv Dc (pt x y) * I‖ ≤ 2 ^ 7 * M / y₀ ^ 7 := by
    intro y hy
    rw [norm_mul, Complex.norm_I, mul_one]
    exact hder _ (by simpa using hy)
  have := (convex_Ici y₀).norm_image_sub_le_of_norm_hasDerivWithin_le hφd hbd
    (show y₂ ∈ Ici y₀ from h2) (show y₁ ∈ Ici y₀ from h1)
  simp only [hφ, Real.norm_eq_abs] at this
  calc ‖Dc (pt x y₁) - Dc (pt x y₂)‖ ≤ 2 ^ 7 * M / y₀ ^ 7 * |y₁ - y₂| := this
    _ = 2 ^ 7 * M * |y₁ - y₂| / y₀ ^ 7 := by ring

end RamanujanTau.CriticalMeanSquareLower
