/-
# Ω± for `A(x) = ∑_{n≤x} a_f(n)` (real coefficients) at every exponent `β < (k−1)/2 + 1/10`

Suppose `ε A(x) ≥ −c x^β` for `x ≥ X₀` (`ε = ±1`), with `0 < β < (k−1)/2 + 1/10`.

1. `g(t) = 1_{t ≥ 1}(ε A(t) + c' t^β) ≥ 0` (`c' = |c| + ∑_{n≤X₀}|a(n)|`), and its Mellin transform is
   `ε L(s)/s + c'/(s−β)`, holomorphic on `Re s > β`.
2. Landau (`landau_mellin`): `∫ g(t) t^{−σ−1} < ∞` for all `σ > β`, hence
   `∫₁^∞ |A(t)| t^{−σ−1} dt < ∞` for all `σ > β`, and `∫ A t^{−w−1} = L(w)/w` on `Re w > β`.
3. With the unconditional `|A(x)| ≤ C x^θ`, `θ = (k−1)/2 + 2/5 + η` (`cuspForm_partial_sum_sharp`):
   `|h_σ|² ≤ C |h_{σ₁}|` pointwise whenever `2σ ≥ σ₁ + θ`, so for `σ = α + δ`,
   `α = (2k−1)/4`, `∫ |h_σ|² ≤ C ‖h_{σ₁}‖₁` **uniformly in `δ`** (choose `β < σ₁ < 2α − θ`).
4. Plancherel + `block_lower` (`TauOmegaPartial`): `∫ |h_σ|² ≥ K₂/(4δ) → ∞`. Contradiction.
-/
import RamanujanTau.TauOmegaPM.Landau
import RamanujanTau.TauOmegaPartial.Omega
import RamanujanTau.TauPartialSumsSharp.Main

set_option autoImplicit false

namespace RamanujanTau.TauOmegaPM

open Complex MeasureTheory Set Filter Topology Asymptotics
open RamanujanTau.HeckeConvexGeneral RamanujanTau.TauOmegaPartial
open scoped MatrixGroups FourierTransform Real

variable {k : ℕ}

/-! ### Generic helpers -/

/-- A polynomial bound on `[1,∞)` gives Mellin convergence on `Re s > θ`. -/
lemma mc_of_bound {ψ : ℝ → ℂ} (h0 : ∀ t < 1, ψ t = 0) (hψ : Measurable ψ) {K θ : ℝ}
    (hb : ∀ t, 1 ≤ t → ‖ψ t‖ ≤ K * t ^ θ) :
    ∀ s : ℂ, θ < s.re → MellinConvergent ψ (-s) := by
  intro s hs
  unfold MellinConvergent
  set p : ℝ := θ - s.re - 1 with hp
  have hp1 : p < -1 := by rw [hp]; linarith
  have hI : IntegrableOn (fun t : ℝ => K * t ^ p) (Ici 1) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (integrableOn_Ioi_rpow_of_lt hp1 zero_lt_one).const_mul K
  have hI' : Integrable ((Ici (1 : ℝ)).indicator (fun t : ℝ => K * t ^ p)) :=
    (integrable_indicator_iff measurableSet_Ici).2 hI
  refine (hI'.integrableOn (s := Ioi 0)).mono' (aesm_integrand hψ (-s) _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_integrand ht0]
  rcases lt_or_ge t 1 with h1 | h1
  · rw [h0 t h1, norm_zero, mul_zero]
    exact Set.indicator_nonneg (fun t (ht : 1 ≤ t) => by
      have : 0 ≤ ‖ψ t‖ := norm_nonneg _
      have h := hb t ht
      have : 0 ≤ K * t ^ θ := le_trans (norm_nonneg _) h
      have htp : 0 < t ^ θ := Real.rpow_pos_of_pos (by linarith) _
      have hK : 0 ≤ K := by
        by_contra hK; push Not at hK; nlinarith
      positivity) t
  · rw [Set.indicator_of_mem (show t ∈ Ici (1 : ℝ) from h1)]
    have e : t ^ ((-s).re - 1) * t ^ θ = t ^ p := by
      rw [← Real.rpow_add ht0, hp]; congr 1; simp; ring
    calc t ^ ((-s).re - 1) * ‖ψ t‖ ≤ t ^ ((-s).re - 1) * (K * t ^ θ) := by
          gcongr; exact hb t h1
      _ = K * t ^ p := by rw [← e]; ring

private theorem rexp_neg_deriv_aux' :
    ∀ x ∈ univ, HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) univ x :=
  fun x _ ↦ mul_neg_one (Real.exp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

private theorem rexp_neg_image_aux' : Real.exp ∘ Neg.neg '' univ = Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ, Real.range_exp]

private theorem rexp_neg_injOn_aux' : univ.InjOn (Real.exp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

/-- Mellin convergence at `−σ` is integrability of `u ↦ e^{σu} ψ(e^{−u})`. -/
lemma integrable_of_mc {ψ : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent ψ (-((σ : ℝ) : ℂ))) :
    Integrable (fun u : ℝ => Real.exp (σ * u) • ψ (Real.exp (-u))) := by
  rw [MellinConvergent, ← rexp_neg_image_aux', integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ rexp_neg_deriv_aux' rexp_neg_injOn_aux'] at hf
  rw [integrableOn_univ] at hf
  refine hf.congr (Eventually.of_forall fun u => ?_)
  simp only [Function.comp_apply, abs_neg, abs_of_pos (Real.exp_pos _)]
  rw [Complex.ofReal_exp, ← smul_assoc, smul_eq_mul]
  rw [show ((Real.exp (σ * u) : ℝ) • ψ (Real.exp (-u))) =
    ((Real.exp (σ * u) : ℝ) : ℂ) • ψ (Real.exp (-u)) from rfl]
  congr 1
  rw [Complex.ofReal_exp, Complex.ofReal_neg, ← Complex.exp_log (show (Complex.exp (-(u : ℂ))) ≠ 0
    from Complex.exp_ne_zero _)]
  rw [Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_nonneg)]
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_nonneg)]
  rw [Complex.real_smul, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

/-! ### The cusp-form specifics -/

lemma A_real (f : CuspForm 𝒮ℒ (k : ℤ)) (hreal : ∀ n, (coef f n).im = 0) (x : ℝ) :
    A f x = (((A f x).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · simp [A, Complex.im_sum, hreal]

/-- The Mellin identity on the whole half-plane of convergence. -/
lemma mellin_A_eq_of_conv (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {β : ℝ} (hβ : 0 ≤ β)
    (hc : ∀ s : ℂ, β < s.re → MellinConvergent (A f) (-s)) :
    ∀ w : ℂ, β < w.re → mellin (A f) (-w) = fL f w / w := by
  refine mellin_eq_of_eventually (fun t ht => A_of_lt_one f ht) (measurable_A f) hc ?_
    (σ0 := ((k : ℝ) + 1) / 2) (fun s hs => mellin_A_eq_of_large f hk hs)
  refine (fL_entire f hk).differentiableOn.div differentiableOn_id fun w hw h => ?_
  have hw' : β < w.re := hw
  rw [h] at hw'; simp at hw'; linarith

lemma fourier_hfun_of_conv (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {β : ℝ} (hβ : 0 ≤ β)
    (hc : ∀ s : ℂ, β < s.re → MellinConvergent (A f) (-s)) {σ : ℝ} (hσ : β < σ) (ξ : ℝ) :
    𝓕 (hfun f σ) ξ = Fs f σ ξ := by
  set w : ℂ := (σ : ℂ) - 2 * π * ξ * I with hw
  have hre : (-w).re = -σ := by simp [hw]
  have him : (-w).im = 2 * π * ξ := by simp [hw]
  have h := mellin_eq_fourier (A f) (s := -w)
  rw [hre, him] at h
  have e1 : (2 * π * ξ) / (2 * π) = ξ := by field_simp
  rw [e1] at h
  have e2 : (fun u : ℝ => Real.exp (-(-σ) * u) • A f (Real.exp (-u))) = hfun f σ := by
    funext u; simp [hfun]
  rw [e2] at h
  rw [← h, Fs]
  exact mellin_A_eq_of_conv f hk hβ hc w (by rw [hw]; simpa using hσ)

/-- **Step 1 (Landau)**: a one-sided bound `ε A(x) ≥ −c x^β` forces
`∫₁^∞ |A(t)| t^{−σ−1} dt < ∞` for every `σ > β`. -/
theorem conv_of_one_sided (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k)
    (hreal : ∀ n, (coef f n).im = 0) {β θ C : ℝ} (hβ0 : 0 < β) (hβθ : β < θ)
    (hCA : ∀ x : ℝ, 1 ≤ x → ‖A f x‖ ≤ C * x ^ θ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    {c X0 : ℝ} (h : ∀ x ≥ X0, -c * x ^ β ≤ ε * (A f x).re) :
    ∀ s : ℂ, β < s.re → MellinConvergent (A f) (-s) := by
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : 1 ≤ k := by omega
  have hε2 : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hεabs : ∀ y : ℝ, -|y| ≤ ε * y := by
    intro y; rcases hε with h | h <;> rw [h]
    · simp [neg_abs_le]
    · simp [le_abs_self]
  -- the nonnegative function
  set X1 : ℝ := max X0 1 with hX1
  set S0 : ℝ := ∑ n ∈ Finset.Icc 1 ⌊X1⌋₊, ‖coef f n‖ with hS0
  have hS00 : 0 ≤ S0 := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set c' : ℝ := |c| + S0 with hc'
  have hc'0 : 0 ≤ c' := by positivity
  set g : ℝ → ℝ := (Ici (1 : ℝ)).indicator (fun t => ε * (A f t).re + c' * t ^ β) with hg
  have hg1 : ∀ t < 1, g t = 0 := fun t ht =>
    Set.indicator_of_notMem (show t ∉ Ici (1 : ℝ) from fun h' => by simp at h'; linarith) _
  have hge : ∀ t, 1 ≤ t → g t = ε * (A f t).re + c' * t ^ β := fun t ht =>
    Set.indicator_of_mem (show t ∈ Ici (1 : ℝ) from ht) _
  have hg0 : ∀ t, 0 ≤ g t := by
    intro t
    rcases lt_or_ge t 1 with h1 | h1
    · rw [hg1 t h1]
    rw [hge t h1]
    have htb : 1 ≤ t ^ β := Real.one_le_rpow h1 hβ0.le
    have hcb : 0 ≤ |c| * t ^ β := by positivity
    rcases le_or_gt X1 t with h2 | h2
    · have := h t (le_trans (le_max_left _ _) h2)
      have : -|c| * t ^ β ≤ -c * t ^ β := by nlinarith [le_abs_self c]
      rw [hc']; nlinarith
    · have hA : |(A f t).re| ≤ S0 := by
        refine (Complex.abs_re_le_norm _).trans ?_
        exact norm_A_le f h2.le
      have := hεabs (A f t).re
      rw [hc']; nlinarith
  have hgm : Measurable g := by
    refine Measurable.indicator ?_ measurableSet_Ici
    exact (measurable_const.mul (Complex.measurable_re.comp (measurable_A f))).add
      (measurable_const.mul (measurable_id.pow_const β))
  set ψ : ℝ → ℂ := fun t => (g t : ℂ) with hψ
  have hψ0 : ∀ t < 1, ψ t = 0 := fun t ht => by simp [hψ, hg1 t ht]
  have hψm : Measurable ψ := Complex.measurable_ofReal.comp hgm
  -- the power piece
  set φ2 : ℝ → ℂ := (Ici (1 : ℝ)).indicator (fun t => ((t ^ β : ℝ) : ℂ)) with hφ2
  have hφ20 : ∀ t < 1, φ2 t = 0 := fun t ht =>
    Set.indicator_of_notMem (show t ∉ Ici (1 : ℝ) from fun h' => by simp at h'; linarith) _
  have hφ2m : Measurable φ2 :=
    (Complex.measurable_ofReal.comp (measurable_id.pow_const β)).indicator measurableSet_Ici
  have hφ2c : ∀ s : ℂ, β < s.re → MellinConvergent φ2 (-s) := by
    refine mc_of_bound hφ20 hφ2m (K := 1) fun t ht => ?_
    rw [hφ2, Set.indicator_of_mem (show t ∈ Ici (1 : ℝ) from ht), Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), one_mul]
  have hφ2mel : ∀ s : ℂ, β < s.re → mellin φ2 (-s) = 1 / (s - β) := by
    intro s hs
    rw [mellin, hφ2]
    have e : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (-s - 1) •
        (Ici (1 : ℝ)).indicator (fun t => ((t ^ β : ℝ) : ℂ)) t =
        ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ ((β : ℂ) - s - 1) := by
      have e1 : (fun t : ℝ => (t : ℂ) ^ (-s - 1) •
          (Ici (1 : ℝ)).indicator (fun t => ((t ^ β : ℝ) : ℂ)) t) =
          (Ici (1 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ (-s - 1) • ((t ^ β : ℝ) : ℂ)) := by
        funext t
        by_cases ht : t ∈ Ici (1 : ℝ)
        · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
        · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
      rw [e1, setIntegral_indicator measurableSet_Ici]
      have e2 : Ioi (0 : ℝ) ∩ Ici 1 = Ici 1 := by
        ext t; simp only [mem_inter_iff, mem_Ioi, mem_Ici]; constructor
        · exact fun h => h.2
        · exact fun h => ⟨by linarith, h⟩
      rw [e2, integral_Ici_eq_integral_Ioi]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
      rw [smul_eq_mul, Complex.ofReal_cpow ht0.le, ← Complex.cpow_add _ _
        (ofReal_ne_zero.2 ht0.ne')]
      congr 1; ring
    rw [e, integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one]
    have hsb : s - (β : ℂ) ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    rw [show (β : ℂ) - s - 1 + 1 = -(s - β) by ring, Complex.ofReal_one, Complex.one_cpow]
    field_simp
  -- decomposition `g = ε A + c' φ₂`
  have hdec : ∀ t, ψ t = ε * A f t + c' * φ2 t := by
    intro t
    rcases lt_or_ge t 1 with h1 | h1
    · rw [hψ0 t h1, A_of_lt_one f h1, hφ20 t h1]; ring
    · simp only [hψ, hge t h1, hφ2, Set.indicator_of_mem (show t ∈ Ici (1 : ℝ) from h1)]
      conv_rhs => rw [A_real f hreal t]
      push_cast; ring
  have hAdec : ∀ t, A f t = ε * (ψ t - c' * φ2 t) := by
    intro t; rw [hdec t]
    have : (ε : ℂ) * ε = 1 := by exact_mod_cast hε2
    linear_combination (-(A f t)) * this
  -- convergence far right
  have hAc : ∀ s : ℂ, θ < s.re → MellinConvergent (A f) (-s) :=
    mc_of_bound (fun t ht => A_of_lt_one f ht) (measurable_A f) hCA
  have hψb : ∀ t, 1 ≤ t → ‖ψ t‖ ≤ (|C| + c') * t ^ θ := by
    intro t ht
    have htθ : t ^ β ≤ t ^ θ := Real.rpow_le_rpow_of_exponent_le ht hβθ.le
    have hA := hCA t ht
    rw [hdec t, hφ2, Set.indicator_of_mem (show t ∈ Ici (1 : ℝ) from ht)]
    calc ‖(ε : ℂ) * A f t + c' * ((t ^ β : ℝ) : ℂ)‖ ≤ ‖(ε : ℂ) * A f t‖ + ‖(c' : ℂ) * ((t ^ β : ℝ) : ℂ)‖ :=
          norm_add_le _ _
      _ = ‖A f t‖ + c' * t ^ β := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg hc'0, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
          rcases hε with h | h <;> rw [h] <;> simp
      _ ≤ |C| * t ^ θ + c' * t ^ θ := by
          gcongr
          exact hA.trans (mul_le_mul_of_nonneg_right (le_abs_self C)
            (Real.rpow_nonneg (by linarith) _))
      _ = (|C| + c') * t ^ θ := by ring
  set σ0 : ℝ := max θ (((k : ℝ) + 1) / 2) + 1 with hσ0
  have hψc0 : MellinConvergent ψ (-((σ0 : ℝ) : ℂ)) :=
    mc_of_bound hψ0 hψm hψb _ (by simp [hσ0]; linarith [le_max_left θ (((k : ℝ) + 1) / 2)])
  -- the analytic continuation
  set F : ℂ → ℂ := fun s => ε * (fL f s / s) + c' * (1 / (s - β)) with hF
  have hFd : DifferentiableOn ℂ F {s | β < s.re} := by
    intro s hs
    have hs' : β < s.re := hs
    have hs0 : s ≠ 0 := by intro h0; rw [h0] at hs'; simp at hs'; linarith
    have hsb : s - (β : ℂ) ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    refine DifferentiableAt.differentiableWithinAt ?_
    refine ((differentiableAt_const _).mul (((fL_entire f hk1) s).div differentiableAt_id hs0)).add
      ((differentiableAt_const _).mul ((differentiableAt_const _).div
        (differentiableAt_id.sub (differentiableAt_const _)) hsb))
  have hFG : ∀ s : ℂ, σ0 < s.re → mellin ψ (-s) = F s := by
    intro s hs
    have hsθ : θ < s.re := by linarith [le_max_left θ (((k : ℝ) + 1) / 2)]
    have hsk : ((k : ℝ) + 1) / 2 < s.re := by linarith [le_max_right θ (((k : ℝ) + 1) / 2)]
    have hsβ : β < s.re := by linarith
    have h1 := hAc s hsθ
    have h2 := hφ2c s hsβ
    have e : mellin ψ (-s) = ε * mellin (A f) (-s) + c' * mellin φ2 (-s) := by
      unfold mellin
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
      · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        simp only [smul_eq_mul]; rw [hdec t]; ring
      · exact h1.const_mul _
      · exact h2.const_mul _
    rw [e, mellin_A_eq_of_large f hk1 hsk, hφ2mel s hsβ]
  -- Landau
  have hland := landau_mellin hg0 hg1 hgm hψc0 hFd hFG
  have hψc : ∀ s : ℂ, β < s.re → MellinConvergent ψ (-s) := fun s hs =>
    mc_mono hψ0 hψm (hland s.re hs) (by simp)
  have hAconv : ∀ s : ℂ, β < s.re → MellinConvergent (A f) (-s) := by
    intro s hs
    have := ((hψc s hs).sub ((hφ2c s hs).const_mul (c' : ℂ))).const_mul (ε : ℂ)
    unfold MellinConvergent
    refine IntegrableOn.congr_fun (s := Ioi (0 : ℝ)) (μ := volume) this (fun t _ => ?_)
      measurableSet_Ioi
    simp only [smul_eq_mul, Pi.sub_apply]; rw [hAdec t]; ring
  exact hAconv

/-- **Step 2 (Plancherel)**: convergence of `∫ |A| t^{−σ−1}` for `σ > β`, together with
`|A(x)| ≤ C x^θ` and `β + θ < 2α`, `α = (2k−1)/4`, is impossible. -/
theorem false_of_conv (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) {β θ C : ℝ} (hβ0 : 0 < β)
    (hCA : ∀ x : ℝ, 1 ≤ x → ‖A f x‖ ≤ C * x ^ θ)
    (hβθ : β < θ) (hβθ2 : β + θ < 2 * (((k : ℝ) - 1) / 2 + 1 / 4))
    (hAconv : ∀ s : ℂ, β < s.re → MellinConvergent (A f) (-s)) : False := by
  have hk : 12 ≤ k := by
    by_contra h; exact hf (eq_zero_of_lt_twelve f (by omega))
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : 1 ≤ k := by omega
  -- `L¹` on the log scale
  set α : ℝ := ((k : ℝ) - 1) / 2 + 1 / 4 with hα
  set σ1 : ℝ := (β + (2 * α - θ)) / 2 with hσ1
  have hσ1β : β < σ1 := by rw [hσ1]; linarith
  have hσ1θ : σ1 + θ ≤ 2 * α := by rw [hσ1]; linarith
  have hI1 : Integrable (hfun f σ1) := by
    have := integrable_of_mc (hAconv _ (by simpa using hσ1β))
    exact this
  set I1 : ℝ := ∫ u, ‖hfun f σ1 u‖ with hI1def
  have hI10 : 0 ≤ I1 := integral_nonneg fun _ => norm_nonneg _
  set C' : ℝ := |C| with hC'
  have hC'0 : 0 ≤ C' := abs_nonneg _
  -- pointwise `L²`–`L¹` domination
  have hdom : ∀ σ : ℝ, α ≤ σ → ∀ u : ℝ, ‖hfun f σ u‖ ^ 2 ≤ C' * ‖hfun f σ1 u‖ := by
    intro σ hσ u
    rcases lt_or_ge 0 u with hu | hu
    · have h0 : ∀ σ', hfun f σ' u = 0 := fun σ' => by
        rw [hfun, A_of_lt_one f ((Real.exp_lt_exp.2 (by linarith : -u < 0)).trans_eq
          Real.exp_zero), smul_zero]
      rw [h0, h0]; simp
    have hx : 1 ≤ Real.exp (-u) := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by linarith)
    have hn : ∀ σ', ‖hfun f σ' u‖ = Real.exp (σ' * u) * ‖A f (Real.exp (-u))‖ := fun σ' => by
      rw [hfun, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hA := hCA _ hx
    have hAθ : ‖A f (Real.exp (-u))‖ ≤ C' * Real.exp (-u * θ) := by
      rw [← Real.exp_mul] at hA
      exact hA.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
    rw [hn, hn]
    set a := ‖A f (Real.exp (-u))‖ with ha
    have ha0 : 0 ≤ a := norm_nonneg _
    have hexp : Real.exp (σ * u) ^ 2 * Real.exp (-u * θ) ≤ Real.exp (σ1 * u) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.2
      push_cast
      nlinarith
    calc (Real.exp (σ * u) * a) ^ 2 = Real.exp (σ * u) ^ 2 * a * a := by ring
      _ ≤ Real.exp (σ * u) ^ 2 * a * (C' * Real.exp (-u * θ)) := by gcongr
      _ = C' * a * (Real.exp (σ * u) ^ 2 * Real.exp (-u * θ)) := by ring
      _ ≤ C' * a * Real.exp (σ1 * u) := by gcongr
      _ = C' * (Real.exp (σ1 * u) * a) := by ring
  -- the Ω-assembly of `TauOmegaPartial`
  obtain ⟨m, hm, hlow, hm0⟩ := exists_first_coef f hf hk1
  obtain ⟨K1, hK1, Ξ0, hΞ0, hblock⟩ := block_lower f hk hm hlow hm0
  set K2 : ℝ := K1 / (4 * Ξ0) with hK2
  have hK20 : 0 < K2 := by positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (1 / 16) (K2 / (8 * (C' * I1 + 1))) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 16 := by rw [hδ]; exact min_le_left _ _
  have hδ2 : δ ≤ K2 / (8 * (C' * I1 + 1)) := by rw [hδ]; exact min_le_right _ _
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = α + δ := ⟨_, rfl⟩
  have hσα : α ≤ σ := by linarith
  have hσβ : β < σ := by
    have : β < α := by linarith
    linarith
  have hi : Integrable (hfun f σ) := integrable_of_mc (hAconv _ (by simpa using hσβ))
  have hm2 : Integrable (fun u => ‖hfun f σ u‖ ^ 2) :=
    (hI1.norm.const_mul C').mono' ((measurable_hfun f σ).aestronglyMeasurable.norm.pow 2)
      (Eventually.of_forall fun u => by
        rw [Real.norm_of_nonneg (by positivity)]; exact hdom σ hσα u)
  have hmem : MemLp (hfun f σ) 2 :=
    (memLp_two_iff_integrable_sq_norm (measurable_hfun f σ).aestronglyMeasurable).2 hm2
  have hup : ∫ u, ‖hfun f σ u‖ ^ 2 ≤ C' * I1 := by
    rw [hI1def, ← integral_const_mul]
    exact integral_mono hm2 (hI1.norm.const_mul C') (hdom σ hσα)
  obtain ⟨hF2, hpl⟩ := plancherel_of_integrable hi hmem
  have hFeq : 𝓕 (hfun f σ) = Fs f σ := by
    funext ξ; exact fourier_hfun_of_conv f hk1 hβ0.le hAconv hσβ ξ
  rw [hFeq] at hF2 hpl
  have hσ0' : 0 < σ := by linarith
  have hFc := continuous_Fs f hk1 hσ0'
  have hFi : Integrable (fun ξ => ‖Fs f σ ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hFc.aestronglyMeasurable).1 hF2
  set J : ℕ := ⌈1 / (4 * δ)⌉₊ with hJ
  set a : ℕ → ℝ := fun j => 2 ^ j * Ξ0 with ha
  have hsum : ∑ j ∈ Finset.range J, ∫ ξ in a j..a (j + 1), ‖Fs f σ ξ‖ ^ 2 =
      ∫ ξ in a 0..a J, ‖Fs f σ ξ‖ ^ 2 :=
    intervalIntegral.sum_integral_adjacent_intervals fun j _ =>
      (hFc.norm.pow 2).intervalIntegrable _ _
  have hle : ∫ ξ in a 0..a J, ‖Fs f σ ξ‖ ^ 2 ≤ ∫ ξ, ‖Fs f σ ξ‖ ^ 2 := by
    have h0J : a 0 ≤ a J := by
      simp only [ha, pow_zero, one_mul]
      exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
    rw [intervalIntegral.integral_of_le h0J]
    exact setIntegral_le_integral hFi (Eventually.of_forall fun _ => by positivity)
  have hblocks : ∀ j ∈ Finset.range J, K2 ≤ ∫ ξ in a j..a (j + 1), ‖Fs f σ ξ‖ ^ 2 := by
    intro j hj
    have hjJ : j < J := Finset.mem_range.1 hj
    have haj : Ξ0 ≤ a j := by
      simp only [ha]; exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
    have hb := hblock δ hδ0 hδ1 (a j) haj
    rw [← hα, ← hσ] at hb
    have hnext : a (j + 1) = 2 * a j := by simp only [ha]; rw [pow_succ]; ring
    rw [hnext]
    have hw := dyadic_weight hΞ0 hδ0 hδ1 hjJ
    have : K2 ≤ K1 * (2 * a j) ^ (-(4 * δ)) := by
      rw [hK2, div_eq_mul_one_div]
      simp only [ha]
      exact mul_le_mul_of_nonneg_left hw hK1.le
    exact this.trans hb
  have hlow' : (J : ℝ) * K2 ≤ ∫ ξ, ‖Fs f σ ξ‖ ^ 2 := by
    have := Finset.sum_le_sum hblocks
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hsum] at this
    exact this.trans hle
  have hJge : 1 / (4 * δ) ≤ (J : ℝ) := Nat.le_ceil _
  rw [hpl] at hlow'
  have hmain : K2 / (4 * δ) ≤ C' * I1 := by
    have : K2 / (4 * δ) ≤ (J : ℝ) * K2 := by
      rw [div_eq_mul_one_div, mul_comm]; exact mul_le_mul_of_nonneg_right hJge hK20.le
    linarith
  have hbig : 2 * (C' * I1 + 1) ≤ K2 / (4 * δ) := by
    have hpos : 0 < 8 * (C' * I1 + 1) := by positivity
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hδ2 (show 0 ≤ 8 * (C' * I1 + 1) by positivity)
    rw [mul_div_cancel₀ _ hpos.ne'] at this
    nlinarith
  nlinarith


/-- **The one-sided bound is impossible** below the exponent `(k−1)/2 + 1/10`. -/
theorem no_one_sided (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (hreal : ∀ n, (coef f n).im = 0)
    {β : ℝ} (hβ0 : 0 < β) (hβ : β < ((k : ℝ) - 1) / 2 + 1 / 10) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    {c X0 : ℝ} (h : ∀ x ≥ X0, -c * x ^ β ≤ ε * (A f x).re) : False := by
  have hk : 12 ≤ k := by
    by_contra h; exact hf (eq_zero_of_lt_twelve f (by omega))
  set η : ℝ := (((k : ℝ) - 1) / 2 + 1 / 10 - β) / 4 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  set θ : ℝ := ((k : ℝ) - 1) / 2 + 2 / 5 + η with hθ
  obtain ⟨C, hC⟩ := TauPartialSumsSharp.cuspForm_partial_sum_sharp f hη0
  have hCA : ∀ x : ℝ, 1 ≤ x → ‖A f x‖ ≤ C * x ^ θ := fun x hx => hC x hx
  have hβθ : β < θ := by rw [hθ]; linarith
  exact false_of_conv f hf hβ0 hCA hβθ (by rw [hθ, hη]; linarith)
    (conv_of_one_sided f hk hreal hβ0 hβθ hCA hε h)

end RamanujanTau.TauOmegaPM
