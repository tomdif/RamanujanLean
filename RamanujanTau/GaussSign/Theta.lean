import Mathlib

/-!
# Theta asymptotics at rational cusps

`tendsto_sqrt_cosKernel`: `√y · cosKernel a y → [a = 0]` as `y → 0⁺` (from the functional equation
`evenKernel a x = x^{-1/2} cosKernel a (1/x)` and the decay of `evenKernel a x − [a = 0]`).

`tendsto_theta_quad`: for `N ≥ 1`, `a ∈ ℤ`,
`√y · θ(2a/N + iy) → N⁻¹ Σ_{r mod N} e(a r²/N)` as `y → 0⁺`
(the quadratic phase is `N`-periodic; expand it by the finite Fourier inversion on `ZMod N`).

`theta_pert`: `‖θ(u + iv) − θ(u' + iv)‖ ≤ 2|u − u'|/v · evenKernel 0 (v/2)`.
-/

set_option autoImplicit false

namespace RamanujanTau.GaussSign
open Complex Filter Topology Finset HurwitzZeta ZMod
open scoped Real

noncomputable section

/-- `√y · cosKernel a y → [a = 0]` as `y → 0⁺`. -/
theorem tendsto_sqrt_cosKernel (a : UnitAddCircle) :
    Tendsto (fun y : ℝ => Real.sqrt y * cosKernel a y) (𝓝[>] 0)
      (𝓝 (if a = 0 then 1 else 0)) := by
  obtain ⟨p, hp, hO⟩ := isBigO_atTop_evenKernel_sub a
  have h1 : Tendsto (fun x : ℝ => evenKernel a x - (if a = 0 then 1 else 0)) atTop (𝓝 0) := by
    refine hO.trans_tendsto ?_
    have : Tendsto (fun x : ℝ => -p * x) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith)
    exact Real.tendsto_exp_atBot.comp this
  have h2 : Tendsto (fun x : ℝ => evenKernel a x) atTop (𝓝 (if a = 0 then 1 else 0)) := by
    simpa using h1.add_const (if a = 0 then (1 : ℝ) else 0)
  refine (h2.comp tendsto_inv_nhdsGT_zero).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
  simp only [Function.comp_apply]
  rw [evenKernel_functional_equation, Real.inv_rpow hy.le]
  simp only [one_div, inv_inv, Real.sqrt_eq_rpow]

/-- `θ(τ)` as a sum. -/
lemma hasSum_theta {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ => cexp (π * I * (n : ℂ) ^ 2 * τ)) (jacobiTheta τ) := by
  rw [jacobiTheta_eq_jacobiTheta₂]
  refine (hasSum_jacobiTheta₂_term 0 hτ).congr_fun fun n => ?_
  simp [jacobiTheta₂_term]

lemma stdAddChar_intCast (N : ℕ) [NeZero N] (m : ℤ) :
    (stdAddChar (m : ZMod N) : ℂ) = cexp (2 * π * I * m / N) := by
  rw [stdAddChar_apply, toCircle_intCast]

/-- **Theta at the rational point `2a/N`.** -/
theorem tendsto_theta_quad (N : ℕ) [NeZero N] (a : ℤ) :
    Tendsto (fun y : ℝ => (Real.sqrt y : ℂ) * jacobiTheta (2 * a / N + I * y)) (𝓝[>] 0)
      (𝓝 ((N : ℂ)⁻¹ * ∑ r : ZMod N, (stdAddChar ((a : ZMod N) * r ^ 2) : ℂ))) := by
  set Φ : ZMod N → ℂ := fun r => stdAddChar ((a : ZMod N) * r ^ 2) with hΦ
  have hN : (N : ℂ) ≠ 0 := NeZero.ne _
  -- expansion
  have hexp : ∀ y : ℝ, 0 < y → jacobiTheta (2 * a / N + I * y) =
      (N : ℂ)⁻¹ * ∑ j : ZMod N, 𝓕 Φ j * (cosKernel ((j.val : ℝ) / N : ℝ) y : ℂ) := by
    intro y hy
    have hτ : 0 < (2 * (a : ℂ) / N + I * y).im := by simpa using hy
    refine ((hasSum_theta hτ).unique ?_)
    rw [Finset.mul_sum]
    have hs := hasSum_sum (s := (Finset.univ : Finset (ZMod N))) fun j _ =>
      ((hasSum_int_cosKernel ((j.val : ℝ) / N) hy).mul_left (𝓕 Φ j)).mul_left (N : ℂ)⁻¹
    convert hs using 1
    funext n
    have hinv : Φ (n : ZMod N) = (N : ℂ)⁻¹ * ∑ j : ZMod N, (stdAddChar (j * (n : ZMod N)) : ℂ) * 𝓕 Φ j := by
      have := congr_fun (((𝓕 : (ZMod N → ℂ) ≃ₗ[ℂ] (ZMod N → ℂ))).symm_apply_apply Φ) (n : ZMod N)
      rw [← this, invDFT_apply]; simp [smul_eq_mul]
    have hterm : cexp (π * I * (n : ℂ) ^ 2 * (2 * a / N + I * y)) =
        Φ (n : ZMod N) * (rexp (-π * n ^ 2 * y) : ℂ) := by
      rw [hΦ]; simp only
      rw [show ((a : ZMod N) * (n : ZMod N) ^ 2) = ((a * n ^ 2 : ℤ) : ZMod N) by push_cast; ring,
        stdAddChar_intCast, ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring_nf
      rw [I_sq]; ring
    rw [hterm, hinv, mul_assoc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show j * (n : ZMod N) = ((j.val * n : ℤ) : ZMod N) by push_cast; simp, stdAddChar_intCast]
    have : cexp (2 * π * I * ((j.val * n : ℤ) : ℂ) / N) = cexp (2 * π * I * ((((j.val : ℝ) / N : ℝ)) : ℂ) * n) := by
      congr 1; push_cast; ring
    rw [this]; ring
  have hz : ∀ j : ZMod N, (((j.val : ℝ) / N : ℝ) : UnitAddCircle) = 0 ↔ j = 0 := by
    intro j
    have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    rw [AddCircle.coe_eq_zero_iff_of_mem_Ico]
    · rw [div_eq_zero_iff, Nat.cast_eq_zero, ZMod.val_eq_zero]
      simp [NeZero.ne N]
    · refine ⟨by positivity, ?_⟩
      rw [div_lt_one hNr]; exact_mod_cast ZMod.val_lt j
  have hlim : Tendsto (fun y : ℝ => (N : ℂ)⁻¹ * ∑ j : ZMod N,
      𝓕 Φ j * ((Real.sqrt y * cosKernel ((j.val : ℝ) / N : ℝ) y : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 ((N : ℂ)⁻¹ * ∑ j : ZMod N, 𝓕 Φ j *
        ((if (((j.val : ℝ) / N : ℝ) : UnitAddCircle) = 0 then 1 else 0 : ℝ) : ℂ))) := by
    refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul ?_)
    exact (tendsto_sqrt_cosKernel _).ofReal
  have hval : (N : ℂ)⁻¹ * ∑ j : ZMod N, 𝓕 Φ j *
      ((if (((j.val : ℝ) / N : ℝ) : UnitAddCircle) = 0 then 1 else 0 : ℝ) : ℂ) =
      (N : ℂ)⁻¹ * ∑ r : ZMod N, Φ r := by
    rw [← dft_apply_zero Φ]
    congr 1
    rw [Finset.sum_eq_single (0 : ZMod N)]
    · rw [if_pos ((hz 0).mpr rfl)]; simp
    · intro j _ hj; rw [if_neg (fun h => hj ((hz j).mp h))]; simp
    · simp
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
  rw [hexp y hy, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast; ring

/-- `x e^{-x} ≤ 2 e^{-x/2}`. -/
lemma mul_exp_neg_le (X : ℝ) : X * rexp (-X) ≤ 2 * rexp (-(X / 2)) := by
  have h1 : X / 2 + 1 ≤ rexp (X / 2) := Real.add_one_le_exp _
  have h2 : rexp (-X) = rexp (-(X / 2)) * rexp (-(X / 2)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : rexp (X / 2) * rexp (-(X / 2)) = 1 := by rw [← Real.exp_add]; simp
  have hp : 0 < rexp (-(X / 2)) := Real.exp_pos _
  rw [h2]
  nlinarith

/-- **Perturbing the real part of `τ`.** -/
theorem theta_pert (u u' v : ℝ) (hv : 0 < v) :
    ‖jacobiTheta (u + I * v) - jacobiTheta (u' + I * v)‖ ≤
      2 * |u - u'| / v * evenKernel ((0 : ℝ) : UnitAddCircle) (v / 2) := by
  have hτ : ∀ w : ℝ, 0 < ((w : ℂ) + I * v).im := fun w => by simpa using hv
  have h1 := (hasSum_theta (hτ u)).sub (hasSum_theta (hτ u'))
  have hg := (hasSum_int_evenKernel 0 (by positivity : 0 < v / 2)).mul_left (2 * |u - u'| / v)
  refine h1.norm_le_of_bounded hg fun n => ?_
  have hsplit : ∀ w : ℝ, cexp (π * I * (n : ℂ) ^ 2 * (w + I * v)) =
      (rexp (-π * n ^ 2 * v) : ℂ) * cexp (I * ((π * n ^ 2 * w : ℝ) : ℂ)) := by
    intro w
    rw [ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring_nf; rw [I_sq]; ring
  rw [hsplit, hsplit, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hd : cexp (I * ((π * n ^ 2 * u : ℝ) : ℂ)) - cexp (I * ((π * n ^ 2 * u' : ℝ) : ℂ)) =
      cexp (I * ((π * n ^ 2 * u' : ℝ) : ℂ)) * (cexp (I * ((π * n ^ 2 * (u - u') : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [hd, norm_mul, norm_exp_I_mul_ofReal, one_mul]
  have hb := Real.norm_exp_I_mul_ofReal_sub_one_le (x := π * n ^ 2 * (u - u'))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ π * (n : ℝ) ^ 2)] at hb
  have hX := mul_exp_neg_le (π * n ^ 2 * v)
  have hE : 0 ≤ rexp (-π * n ^ 2 * v) := (Real.exp_pos _).le
  calc rexp (-π * n ^ 2 * v) * ‖cexp (I * ((π * n ^ 2 * (u - u') : ℝ) : ℂ)) - 1‖
      ≤ rexp (-π * n ^ 2 * v) * (π * n ^ 2 * |u - u'|) := mul_le_mul_of_nonneg_left hb hE
    _ = |u - u'| / v * ((π * n ^ 2 * v) * rexp (-(π * n ^ 2 * v))) := by
        field_simp
    _ ≤ |u - u'| / v * (2 * rexp (-(π * n ^ 2 * v / 2))) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = 2 * |u - u'| / v * rexp (-π * ((n : ℝ) + 0) ^ 2 * (v / 2)) := by
        rw [add_zero]; ring_nf

end

end RamanujanTau.GaussSign
