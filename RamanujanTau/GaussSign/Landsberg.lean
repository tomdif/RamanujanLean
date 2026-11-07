import RamanujanTau.GaussSign.Theta

/-!
# The theta-function proof of Gauss's evaluation `Σ_{r mod N} e(r²/N)`

Approach `τ = 2/N + it` vertically (`t → 0⁺`). On one side `√t θ(τ) → N⁻¹ Σ_r e(r²/N)`
(`tendsto_theta_quad`). On the other, `θ(τ) = (−iτ)^{−1/2} θ(−1/τ)` and
`−1/τ = u + iv` with `u = −(N/2)/(1+st²)`, `v = st/(1+st²)`, `s = N²/4`, which is the cusp
`−N/2` up to a real-part error `|u + N/2| = (N/2) t v` (`theta_pert` controls it); at `−N/2`,
`√v θ(−N/2 + iv) → ¼ Σ_{r mod 4} e(−N r²/4)`. Comparing the two limits gives
`gaussQuad_limit`, and evaluating the principal square root gives `gaussQuad_eval`.
-/

set_option autoImplicit false

namespace RamanujanTau.GaussSign
open Complex Filter Topology Finset HurwitzZeta ZMod
open scoped Real

noncomputable section

section limit
variable (N : ℕ) [NeZero N]

/-- **The limit identity** (no parity hypothesis). -/
theorem gaussQuad_limit :
    (N : ℂ)⁻¹ * ∑ r : ZMod N, (stdAddChar (((1 : ℤ) : ZMod N) * r ^ 2) : ℂ) =
      1 / (-I * (2 * ((1 : ℤ) : ℂ) / N + I * ((0 : ℝ) : ℂ))) ^ (1 / 2 : ℂ) *
        (((Real.sqrt ((1 + (N : ℝ) ^ 2 / 4 * 0 ^ 2) / ((N : ℝ) ^ 2 / 4)) : ℝ) : ℂ) *
          (((4 : ℕ) : ℂ)⁻¹ * ∑ r : ZMod 4, (stdAddChar (((-(N : ℤ) : ℤ) : ZMod 4) * r ^ 2) : ℂ))
          + 0) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set s : ℝ := (N : ℝ) ^ 2 / 4 with hs
  have hs0 : 0 < s := by positivity
  let τ : ℝ → ℂ := fun t => 2 * ((1 : ℤ) : ℂ) / N + I * t
  let v : ℝ → ℝ := fun t => s * t / (1 + s * t ^ 2)
  let uu : ℝ → ℝ := fun t => -((N : ℝ) / 2) / (1 + s * t ^ 2)
  let rr : ℝ → ℝ := fun t => (1 + s * t ^ 2) / s
  let A : ℝ → ℂ := fun t => 1 / (-I * τ t) ^ (1 / 2 : ℂ)
  let σ : ℝ → ℂ := fun t => 2 * (((-(N : ℤ)) : ℤ) : ℂ) / ((4 : ℕ) : ℂ) + I * (v t)
  have hDpos : ∀ t : ℝ, 0 < 1 + s * t ^ 2 := fun t => by positivity
  have hvpos : ∀ t : ℝ, 0 < t → 0 < v t := fun t ht => div_pos (by positivity) (hDpos t)
  -- algebraic facts
  have hinv : ∀ t : ℝ, 0 < t → -1 / τ t = (uu t : ℂ) + I * (v t) := by
    intro t ht
    have hτ0 : τ t ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp [τ] at this
      linarith
    rw [div_eq_iff hτ0]
    have hD : ((1 + s * t ^ 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hDpos t).ne'
    simp only [uu, v, τ, ofReal_div, ofReal_neg]
    rw [hs]
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
    have hD' : (1 + (N : ℂ) ^ 2 / 4 * (t : ℂ) ^ 2) ≠ 0 := by
      have := hD; push_cast [hs] at this; exact this
    push_cast
    field_simp
    have h4 : (4 + (N : ℂ) ^ 2 * (t : ℂ) ^ 2) ≠ 0 := by
      intro h; apply hD'; linear_combination h / 4
    rw [eq_div_iff h4]
    linear_combination (-2 * (N : ℂ) ^ 2 * (t : ℂ) ^ 2) * I_sq
  -- functional equation
  have hfe : ∀ t : ℝ, 0 < t → jacobiTheta (τ t) = A t * jacobiTheta ((uu t : ℂ) + I * (v t)) := by
    intro t ht
    rw [← hinv t ht, jacobiTheta_eq_jacobiTheta₂, jacobiTheta_eq_jacobiTheta₂,
      jacobiTheta₂_functional_equation 0 (τ t)]
    simp [A]
  have hrv : ∀ t : ℝ, t = rr t * v t := by
    intro t; simp only [rr, v]; field_simp [(hDpos t).ne']
  have huv : ∀ t : ℝ, 0 ≤ t → |uu t - (-(N : ℝ) / 2)| = (N : ℝ) / 2 * t * v t := by
    intro t ht
    have : uu t - (-(N : ℝ) / 2) = (N : ℝ) / 2 * t * v t := by
      simp only [uu, v]; field_simp [(hDpos t).ne']; ring
    rw [this, abs_of_nonneg (by have := hvpos; positivity)]
  have hσ : ∀ t : ℝ, σ t = ((-(N : ℝ) / 2 : ℝ) : ℂ) + I * (v t) := by
    intro t; simp only [σ]; push_cast; ring
  -- limits
  have hcont_v : Continuous v := by
    simp only [v]; exact Continuous.div (by fun_prop) (by fun_prop) fun t => (hDpos t).ne'
  have hv : Tendsto v (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (hcont_v.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa [v] using this
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t) using hvpos t ht
  have hv2 : Tendsto (fun t => v t / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := ((hcont_v.div_const 2).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa [v] using this
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact half_pos (hvpos t ht)
  have hcont_rr : Continuous rr := by simp only [rr]; fun_prop
  have hR : Tendsto (fun t => ((Real.sqrt (rr t) : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 ((Real.sqrt (rr 0) : ℝ) : ℂ)) :=
    (((Real.continuous_sqrt.comp hcont_rr).tendsto 0).ofReal).mono_left nhdsWithin_le_nhds
  have hR2 : Tendsto (fun t => Real.sqrt (2 * rr t)) (𝓝[>] 0) (𝓝 (Real.sqrt (2 * rr 0))) :=
    ((Real.continuous_sqrt.comp (hcont_rr.const_mul 2)).tendsto 0).mono_left nhdsWithin_le_nhds
  have hslit : -I * τ 0 ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right; simp [τ]; exact NeZero.ne N
  have hA : Tendsto A (𝓝[>] 0) (𝓝 (A 0)) := by
    have hc : ContinuousAt (fun t : ℝ => (-I * τ t) ^ (1 / 2 : ℂ)) 0 :=
      ContinuousAt.comp (x := (0 : ℝ)) (f := fun t : ℝ => -I * τ t) (g := fun z : ℂ => z ^ (1 / 2 : ℂ))
        (continuousAt_cpow_const hslit) (by simp only [τ]; fun_prop)
    have hne : (-I * τ 0) ^ (1 / 2 : ℂ) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff, not_and_or]; left
      intro h; rw [h] at hslit; exact slitPlane_ne_zero hslit rfl
    exact (tendsto_const_nhds.div hc.tendsto hne).mono_left nhdsWithin_le_nhds
  have hB : Tendsto (fun t => ((Real.sqrt (v t) : ℝ) : ℂ) * jacobiTheta (σ t)) (𝓝[>] 0)
      (𝓝 (((4 : ℕ) : ℂ)⁻¹ * ∑ r : ZMod 4, (stdAddChar (((-(N : ℤ) : ℤ) : ZMod 4) * r ^ 2) : ℂ))) :=
    (tendsto_theta_quad 4 (-(N : ℤ))).comp hv
  have hE : Tendsto (fun t => Real.sqrt (v t / 2) * evenKernel ((0 : ℝ) : UnitAddCircle) (v t / 2))
      (𝓝[>] 0) (𝓝 1) := by
    have := (tendsto_sqrt_cosKernel 0).comp hv2
    have e0 : ((0 : ℝ) : UnitAddCircle) = 0 := by simp
    rw [e0, evenKernel_eq_cosKernel_of_zero]
    simpa only [Function.comp_def, eq_self_iff_true, if_true] using this
  have hDlim : Tendsto (fun t => ((Real.sqrt t : ℝ) : ℂ) *
      (jacobiTheta ((uu t : ℂ) + I * (v t)) - jacobiTheta (σ t))) (𝓝[>] 0) (𝓝 0) := by
    have hbd : Tendsto (fun t => (N : ℝ) * t * (Real.sqrt (2 * rr t) *
        (Real.sqrt (v t / 2) * evenKernel ((0 : ℝ) : UnitAddCircle) (v t / 2)))) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun t : ℝ => (N : ℝ) * t) (𝓝[>] 0) (𝓝 0) := by
        have h := ((continuous_const_mul (N : ℝ)).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
        simpa using h
      simpa using h0.mul (hR2.mul hE)
    refine squeeze_zero_norm' ?_ hbd
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [hσ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hp := theta_pert (uu t) (-(N : ℝ) / 2) (v t) (hvpos t ht)
    rw [huv t ht.le] at hp
    have hvt := hvpos t ht
    have hsq : Real.sqrt t = Real.sqrt (2 * rr t) * Real.sqrt (v t / 2) := by
      rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 2 * rr t by have := hDpos t; simp only [rr]; positivity)]
      congr 1; rw [show 2 * rr t * (v t / 2) = rr t * v t by ring]; exact hrv t
    calc Real.sqrt t * ‖jacobiTheta ((uu t : ℂ) + I * (v t)) -
          jacobiTheta (((-(N : ℝ) / 2 : ℝ) : ℂ) + I * (v t))‖
        ≤ Real.sqrt t * (2 * ((N : ℝ) / 2 * t * v t) / v t *
            evenKernel ((0 : ℝ) : UnitAddCircle) (v t / 2)) :=
          mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg _)
      _ = _ := by rw [hsq]; field_simp
  -- assemble
  have hmain : Tendsto (fun t => ((Real.sqrt t : ℝ) : ℂ) * jacobiTheta (τ t)) (𝓝[>] 0)
      (𝓝 (A 0 * (((Real.sqrt (rr 0)) : ℝ) * (((4 : ℕ) : ℂ)⁻¹ *
        ∑ r : ZMod 4, (stdAddChar (((-(N : ℤ) : ℤ) : ZMod 4) * r ^ 2) : ℂ)) + 0))) := by
    refine (hA.mul ((hR.mul hB).add hDlim)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [hfe t ht]
    have hsq : Real.sqrt t = Real.sqrt (rr t) * Real.sqrt (v t) := by
      rw [← Real.sqrt_mul (show (0 : ℝ) ≤ rr t by have := hDpos t; simp only [rr]; positivity), ← hrv t]
    rw [hsq]; push_cast; ring
  have hL1 := tendsto_theta_quad N 1
  exact tendsto_nhds_unique hL1 hmain

end limit

/-- The principal square root of `−2i/N`. -/
lemma sqrt_neg_two_I_div (N : ℕ) [NeZero N] :
    (-I * (2 * ((1 : ℤ) : ℂ) / N + I * ((0 : ℝ) : ℂ))) ^ (1 / 2 : ℂ) =
      ((Real.sqrt (2 / N) * (Real.sqrt 2 / 2) : ℝ) : ℂ) * (1 - I) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hr : (0 : ℝ) < 2 / N := by positivity
  have hx : -I * (2 * ((1 : ℤ) : ℂ) / N + I * ((0 : ℝ) : ℂ)) = ((2 / N : ℝ) : ℂ) * (-I) := by
    push_cast; ring
  rw [hx, cpow_def_of_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hr.ne') (neg_ne_zero.mpr I_ne_zero)),
    log_ofReal_mul hr (neg_ne_zero.mpr I_ne_zero), log_neg_I]
  have e1 : ((Real.log (2 / N) : ℂ) + -(π / 2) * I) * (1 / 2) =
      ((Real.log (2 / N) / 2 : ℝ) : ℂ) + ((-(π / 4) : ℝ) : ℂ) * I := by push_cast; ring
  rw [e1, Complex.exp_add, ← ofReal_exp, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have e2 : Real.exp (Real.log (2 / N) / 2) = Real.sqrt (2 / N) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr]; ring_nf
  rw [e2]; push_cast; ring

lemma sum_zmod4 (f : ZMod 4 → ℂ) : ∑ r : ZMod 4, f r = f 0 + f 1 + f 2 + f 3 := by
  rw [show (Finset.univ : Finset (ZMod 4)) = {0, 1, 2, 3} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- **Gauss's evaluation of the quadratic Gauss sum**, for every odd `N`:
`Σ_{r mod N} e(r²/N) = √N` if `N ≡ 1 (mod 4)` and `= i√N` if `N ≡ 3 (mod 4)`. -/
theorem gaussQuad_eval (N : ℕ) [NeZero N] (hodd : Odd N) :
    ∑ r : ZMod N, (stdAddChar (r ^ 2) : ℂ) =
      if N % 4 = 1 then ((Real.sqrt N : ℝ) : ℂ) else I * ((Real.sqrt N : ℝ) : ℂ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h := gaussQuad_limit N
  rw [sqrt_neg_two_I_div] at h
  simp only [Int.cast_one, one_mul] at h
  set G := ∑ r : ZMod N, (stdAddChar (r ^ 2) : ℂ)
  set ρ : ℝ := Real.sqrt (2 / N) * (Real.sqrt 2 / 2)
  set c : ℂ := stdAddChar (((-(N : ℤ) : ℤ) : ZMod 4))
  have h4 : ∑ r : ZMod 4, (stdAddChar (((-(N : ℤ) : ℤ) : ZMod 4) * r ^ 2) : ℂ) = 2 + 2 * c := by
    rw [sum_zmod4]
    have e2 : (2 : ZMod 4) ^ 2 = 0 := by decide
    have e3 : (3 : ZMod 4) ^ 2 = 1 := by decide
    rw [e2, e3]; simp only [zero_pow two_ne_zero, mul_zero, one_pow, mul_one, AddChar.map_zero_eq_one]
    ring
  have hsq : Real.sqrt ((1 + (N : ℝ) ^ 2 / 4 * 0 ^ 2) / ((N : ℝ) ^ 2 / 4)) = 2 / N := by
    rw [show (1 + (N : ℝ) ^ 2 / 4 * 0 ^ 2) / ((N : ℝ) ^ 2 / 4) = (2 / N) ^ 2 by field_simp; ring,
      Real.sqrt_sq (by positivity)]
  rw [h4, hsq] at h
  have hρ : (ρ : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = 1 := by
    have : ρ * Real.sqrt N = 1 := by
      simp only [ρ]
      have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      rw [Real.sqrt_div (by norm_num)]
      have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNr
      field_simp
      linarith
    exact_mod_cast this
  have hρ0 : (ρ : ℂ) ≠ 0 := by intro h0; rw [h0, zero_mul] at hρ; exact zero_ne_one hρ
  have hI : (1 - I) ≠ 0 := by
    intro h0; have := congrArg Complex.im h0; simp at this
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  -- `G · ρ (1 − i) = 1 + c`
  have hG : G * ((ρ : ℂ) * (1 - I)) = 1 + c := by
    have e : G = (N : ℂ) * ((N : ℂ)⁻¹ * G) := by field_simp
    rw [e, h]; push_cast; field_simp; ring
  have hcN : c = cexp (2 * π * I * ((-(N : ℤ) : ℤ) : ℂ) / ((4 : ℕ) : ℂ)) := stdAddChar_intCast 4 _
  obtain ⟨m, hm⟩ := hodd
  rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · -- `N = 4j + 1`
    have hmod : N % 4 = 1 := by omega
    rw [if_pos hmod]
    have hc : c = -I := by
      rw [hcN, show (2 * π * I * ((-(N : ℤ) : ℤ) : ℂ) / ((4 : ℕ) : ℂ)) =
        ((-j : ℤ) : ℂ) * (2 * π * I) + -(π / 2 * I) by rw [hm, hj]; push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_neg,
        Complex.exp_pi_div_two_mul_I, Complex.inv_I]
    rw [hc] at hG
    have hGρ : G * ρ = 1 := mul_right_cancel₀ hI (by linear_combination hG)
    linear_combination (((Real.sqrt N : ℝ) : ℂ)) * hGρ - G * hρ
  · -- `N = 4j + 3`
    have hmod : ¬ N % 4 = 1 := by omega
    rw [if_neg hmod]
    have hc : c = I := by
      rw [hcN, show (2 * π * I * ((-(N : ℤ) : ℤ) : ℂ) / ((4 : ℕ) : ℂ)) =
        ((-j - 1 : ℤ) : ℂ) * (2 * π * I) + π / 2 * I by rw [hm, hj]; push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_pi_div_two_mul_I]
    rw [hc] at hG
    have hGρ : G * ρ = I := mul_right_cancel₀ hI (by linear_combination hG + I_sq)
    linear_combination (((Real.sqrt N : ℝ) : ℂ)) * hGρ - G * hρ

end

end RamanujanTau.GaussSign
