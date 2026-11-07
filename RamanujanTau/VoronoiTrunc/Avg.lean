/-
# The iterated average `It_h^r`: linearity, sup bounds, and an `L²` bound

`It h 0 g = g`, `It h (j+1) g x = ∫₀^h (It h j g)(x+s) ds` (defined in `Dual.lean`).

* `It_add`, `It_const_mul`, `It_finset_sum`, `It_const`;
* `norm_It_le`: `‖It_h^j f(x)‖ ≤ h^j B` if `‖f‖ ≤ B` on `[x, x+jh]`;
* `norm_It_sub_le`: `‖It_h^j f(x) − h^j f(x)‖ ≤ h^j ε` if `‖f(y) − f(x)‖ ≤ ε` on `[x, x+jh]`;
* `integral_norm_It_sq_le`: `∫_a^b ‖It_h^j f‖² ≤ h^{2j} ∫_a^{b+jh} ‖f‖²`.
-/
import RamanujanTau.VoronoiTrunc.Dual

set_option autoImplicit false

namespace RamanujanTau.VoronoiTrunc

open Complex Real MeasureTheory Set Filter Topology

variable {h : ℝ}

lemma It_zero (g : ℝ → ℂ) : It h 0 g = g := rfl
lemma It_succ (j : ℕ) (g : ℝ → ℂ) (x : ℝ) :
    It h (j + 1) g x = ∫ s in (0 : ℝ)..h, It h j g (x + s) := rfl

lemma It_add : ∀ (j : ℕ) (f g : ℝ → ℂ), Continuous f → Continuous g →
    It h j (fun y => f y + g y) = fun x => It h j f x + It h j g x := by
  intro j
  induction j with
  | zero => intro f g _ _; rfl
  | succ j ih =>
    intro f g hf hg
    funext x
    rw [It_succ, It_succ, It_succ, ih f g hf hg]
    exact intervalIntegral.integral_add
      (((continuous_It h j f hf).comp (continuous_const.add continuous_id)).intervalIntegrable _ _)
      (((continuous_It h j g hg).comp (continuous_const.add continuous_id)).intervalIntegrable _ _)

lemma It_const_mul : ∀ (j : ℕ) (c : ℂ) (f : ℝ → ℂ),
    It h j (fun y => c * f y) = fun x => c * It h j f x := by
  intro j
  induction j with
  | zero => intro c f; rfl
  | succ j ih =>
    intro c f
    funext x
    rw [It_succ, It_succ, ih c f]
    exact intervalIntegral.integral_const_mul _ _

lemma It_finset_sum {ι : Type*} (j : ℕ) (s : Finset ι) (f : ι → ℝ → ℂ) (hf : ∀ i, Continuous (f i)) :
    It h j (fun y => ∑ i ∈ s, f i y) = fun x => ∑ i ∈ s, It h j (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := It_const_mul (h := h) j 0 (fun _ => 0)
    simpa using this
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    rw [It_add j (f a) (fun y => ∑ i ∈ s, f i y) (hf a)
      (continuous_finsetSum _ fun i _ => hf i), ih]

lemma It_const : ∀ (j : ℕ) (c : ℂ) (x : ℝ), It h j (fun _ => c) x = (h : ℂ) ^ j * c := by
  intro j
  induction j with
  | zero => intro c x; simp [It]
  | succ j ih =>
    intro c x
    rw [It_succ]
    simp_rw [ih c]
    rw [intervalIntegral.integral_const]
    simp [Complex.real_smul]; ring

lemma norm_It_le (hh : 0 ≤ h) : ∀ (j : ℕ) (f : ℝ → ℂ) (x B : ℝ),
    (∀ y ∈ Icc x (x + j * h), ‖f y‖ ≤ B) → ‖It h j f x‖ ≤ h ^ j * B := by
  intro j
  induction j with
  | zero => intro f x B hB; simpa using hB x ⟨le_rfl, by simp⟩
  | succ j ih =>
    intro f x B hB
    rw [It_succ]
    have hb : ∀ s ∈ Set.uIoc (0 : ℝ) h, ‖It h j f (x + s)‖ ≤ h ^ j * B := by
      intro s hs
      rw [uIoc_of_le hh] at hs
      refine ih f (x + s) B (fun y hy => hB y ⟨by linarith [hy.1, hs.1], ?_⟩)
      have := hy.2; push_cast at this ⊢; nlinarith [hs.2]
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [sub_zero, abs_of_nonneg hh] at this
    calc _ ≤ h ^ j * B * h := this
      _ = h ^ (j + 1) * B := by ring

lemma norm_It_sub_le (hh : 0 ≤ h) (j : ℕ) {f : ℝ → ℂ} (hf : Continuous f) (x ε : ℝ)
    (hε : ∀ y ∈ Icc x (x + j * h), ‖f y - f x‖ ≤ ε) :
    ‖It h j f x - (h : ℂ) ^ j * f x‖ ≤ h ^ j * ε := by
  have e : It h j f x - (h : ℂ) ^ j * f x = It h j (fun y => f y + (-1 : ℂ) * f x) x := by
    rw [It_add j f (fun _ => (-1 : ℂ) * f x) hf continuous_const]
    simp only
    rw [It_const]; ring
  rw [e]
  refine norm_It_le hh j _ x ε (fun y hy => ?_)
  have := hε y hy
  rwa [show f y + (-1 : ℂ) * f x = f y - f x by ring]

/-- Cauchy–Schwarz on an interval. -/
lemma sq_integral_le {φ : ℝ → ℝ} (hφ : Continuous φ) (hh : 0 ≤ h) :
    (∫ s in (0 : ℝ)..h, φ s) ^ 2 ≤ h * ∫ s in (0 : ℝ)..h, φ s ^ 2 := by
  rcases hh.eq_or_lt with rfl | hpos
  · simp
  set I := ∫ s in (0 : ℝ)..h, φ s
  set m := I / h
  have hnn : 0 ≤ ∫ s in (0 : ℝ)..h, (φ s - m) ^ 2 :=
    intervalIntegral.integral_nonneg hh (fun s _ => sq_nonneg _)
  have e : ∫ s in (0 : ℝ)..h, (φ s - m) ^ 2 = (∫ s in (0 : ℝ)..h, φ s ^ 2) - 2 * m * I + m ^ 2 * h := by
    have h1 : ∀ s, (φ s - m) ^ 2 = φ s ^ 2 - 2 * m * φ s + m ^ 2 := fun s => by ring
    simp_rw [h1]
    have c1 : Continuous fun s => φ s ^ 2 - 2 * m * φ s := (hφ.pow 2).sub (continuous_const.mul hφ)
    rw [intervalIntegral.integral_add (c1.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_sub (f := fun s => φ s ^ 2) (g := fun s => 2 * m * φ s)
        ((hφ.pow 2).intervalIntegrable _ _) ((continuous_const.mul hφ).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp; ring
  rw [e] at hnn
  have hI : I = m * h := by simp only [m]; field_simp
  rw [hI] at hnn ⊢
  nlinarith


lemma integrable_prod_of_continuous {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F))
    (a b c d : ℝ) :
    Integrable (Function.uncurry F) ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
  rw [Measure.prod_restrict]
  have := hF.continuousOn.integrableOn_compact (μ := volume) (isCompact_Icc (a := a) (b := b) |>.prod
    (isCompact_Icc (a := c) (b := d)))
  rw [Measure.volume_eq_prod] at this
  exact this.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- **`L²` bound for the iterated average**: `∫_a^b ‖It_h^j f‖² ≤ h^{2j} ∫_a^{b+jh} ‖f‖²`. -/
theorem integral_norm_It_sq_le (hh : 0 ≤ h) : ∀ (j : ℕ) (f : ℝ → ℂ), Continuous f →
    ∀ a b : ℝ, a ≤ b →
      ∫ x in a..b, ‖It h j f x‖ ^ 2 ≤ h ^ (2 * j) * ∫ x in a..(b + j * h), ‖f x‖ ^ 2 := by
  intro j
  induction j with
  | zero => intro f _ a b _; simp [It]
  | succ j ih =>
    intro f hf a b hab
    set G := It h j f with hG
    have hGc : Continuous G := continuous_It h j f hf
    have hφ : Continuous fun p : ℝ × ℝ => ‖G (p.2 + p.1)‖ ^ 2 :=
      ((hGc.comp (continuous_snd.add continuous_fst)).norm).pow 2
    -- pointwise Cauchy–Schwarz
    have hpt : ∀ x, ‖It h (j + 1) f x‖ ^ 2 ≤ h * ∫ s in (0 : ℝ)..h, ‖G (x + s)‖ ^ 2 := by
      intro x
      rw [It_succ]
      have hc : Continuous fun s => ‖G (x + s)‖ := (hGc.comp (continuous_const.add continuous_id)).norm
      have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun s => G (x + s)) hh
      have h2 := sq_integral_le hc hh
      calc ‖∫ s in (0 : ℝ)..h, G (x + s)‖ ^ 2 ≤ (∫ s in (0 : ℝ)..h, ‖G (x + s)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ _ := h2
    have hcL : Continuous fun x => ‖It h (j + 1) f x‖ ^ 2 := ((continuous_It h (j + 1) f hf).norm).pow 2
    have hcR : Continuous fun x => h * ∫ s in (0 : ℝ)..h, ‖G (x + s)‖ ^ 2 := by
      refine continuous_const.mul ?_
      have : Continuous (Function.uncurry fun x s : ℝ => ‖G (x + s)‖ ^ 2) :=
        ((hGc.comp (continuous_fst.add continuous_snd)).norm).pow 2
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' this 0 h
    have step1 : ∫ x in a..b, ‖It h (j + 1) f x‖ ^ 2 ≤
        ∫ x in a..b, h * ∫ s in (0 : ℝ)..h, ‖G (x + s)‖ ^ 2 :=
      intervalIntegral.integral_mono_on hab (hcL.intervalIntegrable _ _) (hcR.intervalIntegrable _ _)
        (fun x _ => hpt x)
    -- swap the integrals
    have hswap : ∫ x in a..b, ∫ s in (0 : ℝ)..h, ‖G (x + s)‖ ^ 2 =
        ∫ s in (0 : ℝ)..h, ∫ x in a..b, ‖G (x + s)‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le hab]
      have hint := integrable_prod_of_continuous (F := fun s x => ‖G (x + s)‖ ^ 2) hφ 0 h a b
      rw [← uIoc_of_le hh] at hint
      have := intervalIntegral_integral_swap (a := 0) (b := h) (μ := volume.restrict (Ioc a b))
        (f := fun s x => ‖G (x + s)‖ ^ 2) hint
      simp only at this
      rw [← this]
      congr 1; funext s
      rw [intervalIntegral.integral_of_le hab]
    have hshift : ∀ s ∈ Set.uIcc (0 : ℝ) h, ∫ x in a..b, ‖G (x + s)‖ ^ 2 ≤ ∫ x in a..(b + h), ‖G x‖ ^ 2 := by
      intro s hs
      rw [uIcc_of_le hh] at hs
      rw [intervalIntegral.integral_comp_add_right (fun x => ‖G x‖ ^ 2) s]
      have hGsq : Continuous fun x => ‖G x‖ ^ 2 := (hGc.norm).pow 2
      exact intervalIntegral.integral_mono_interval (by linarith [hs.1]) (by linarith)
        (by linarith [hs.2]) (Eventually.of_forall fun x => sq_nonneg _) (hGsq.intervalIntegrable _ _)
    have step2 : ∫ s in (0 : ℝ)..h, ∫ x in a..b, ‖G (x + s)‖ ^ 2 ≤ h * ∫ x in a..(b + h), ‖G x‖ ^ 2 := by
      have hc2 : Continuous fun s => ∫ x in a..b, ‖G (x + s)‖ ^ 2 := by
        have : Continuous (Function.uncurry fun s x : ℝ => ‖G (x + s)‖ ^ 2) := hφ
        exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' this a b
      have := intervalIntegral.integral_mono_on (μ := volume) hh (hc2.intervalIntegrable _ _)
        ((continuous_const (y := ∫ x in a..(b + h), ‖G x‖ ^ 2)).intervalIntegrable _ _)
        (fun s hs => hshift s (by rwa [uIcc_of_le hh]))
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
      exact this
    have step3 := ih f hf a (b + h) (by linarith)
    rw [intervalIntegral.integral_const_mul, hswap] at step1
    have hb : b + h + j * h = b + ((j + 1 : ℕ) : ℝ) * h := by push_cast; ring
    rw [hb] at step3
    calc ∫ x in a..b, ‖It h (j + 1) f x‖ ^ 2 ≤ h * (h * ∫ x in a..(b + h), ‖G x‖ ^ 2) :=
          step1.trans (mul_le_mul_of_nonneg_left step2 hh)
      _ ≤ h * (h * (h ^ (2 * j) * ∫ x in a..(b + ((j + 1 : ℕ) : ℝ) * h), ‖f x‖ ^ 2)) := by
          gcongr
      _ = h ^ (2 * (j + 1)) * ∫ x in a..(b + ((j + 1 : ℕ) : ℝ) * h), ‖f x‖ ^ 2 := by ring

end RamanujanTau.VoronoiTrunc
