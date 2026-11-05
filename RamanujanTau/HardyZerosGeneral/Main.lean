/-
# Hardy's theorem for every level-one cusp form with real coefficients

Let `f ∈ S_k(SL₂(ℤ))`, `f ≠ 0`, with real Fourier coefficients.  Then `L(f,s)` has infinitely
many zeros on the critical line `Re s = k/2`.  See `docs/HARDY_ZEROS_GENERAL.md`.

* Odd `k`: `f = 0` (`eq_zero_of_odd`, evaluate at `−1 ∈ SL₂(ℤ)`); `k < 12`: `f = 0`.
* `k ≡ 0 mod 4`: root number `i^k = 1`; `Z(t) = Λ(f,k/2+it)` is real and even.
* `k ≡ 2 mod 4`: root number `i^k = −1`; `Z(t) = i·Y(t)` with `Y` real and odd.  The odd case of
  Hardy's argument (`hardy_abstract_odd`) uses odd finite-difference orders `m`.
* `∫ Z(t) e^{αt} dt = 2π e^{i(k/2)α} f(i e^{iα})` (`integral_Zc_exp`) and
  `f(i e^{i(π/2−β)}) = O(β^N)` (`Fc_rot_decay`, cusp `−1`).
-/
import RamanujanTau.HardyZerosGeneral.Cusp
import RamanujanTau.HardyZerosGeneral.Abstract
import RamanujanTau.HeckeConvexGeneral.Main

set_option autoImplicit false

namespace RamanujanTau.HardyZerosGeneral

open Complex ModularForm MeasureTheory Set Filter
open UpperHalfPlane hiding I
open RamanujanTau.HeckeConvexGeneral
open scoped MatrixGroups Real ComplexConjugate

variable {k : ℕ}

/-- Level-one cusp forms of odd weight vanish. -/
lemma eq_zero_of_odd (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : Odd k) : f = 0 := by
  ext z
  have hf := SlashInvariantForm.slash_action_eqn'' f
    (show (-1 : GL (Fin 2) ℝ) ∈ 𝒮ℒ from ⟨-1, by ext; simp⟩) z
  have hko : Odd (k : ℤ) := by exact_mod_cast hk
  rw [neg_smul, one_smul, denom_neg, denom_one, hko.neg_one_zpow] at hf
  have h2 : (2 : ℂ) * f z = 0 := by linear_combination hf
  simpa using (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- **Hardy's argument for `Z_f = Y · c`** with `Y` real of parity `σ = ±1` and `‖c‖ = 1`. -/
theorem Zc_zeros_of_rep (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) (c : ℂ) (hc : ‖c‖ = 1)
    (Y : ℝ → ℝ) (hY : ∀ t, Zc f t = (Y t : ℂ) * c) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hpar : ∀ t, Y (-t) = σ * Y t) : ∀ T : ℝ, ∃ t > T, Zc f t = 0 := by
  have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  have hYc : Continuous Y := by
    have : Y = fun t => (Zc f t / c).re := by
      funext t; rw [hY, mul_div_cancel_right₀ _ hc0, ofReal_re]
    rw [this]; exact continuous_re.comp ((continuous_Zc f (by omega)).div_const c)
  have hnorm : ∀ t, |Y t| = ‖Zc f t‖ := by
    intro t; rw [hY, norm_mul, hc, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hint : ∀ a, 0 ≤ a → a < π / 2 → Integrable (fun t => Y t * Real.exp (a * t)) := by
    intro a ha0 ha
    refine (integrable_heckeLambda_line f hk ha).mono'
      ((hYc.mul (by fun_prop)).aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), hnorm]
    change ‖Zc f t‖ * _ ≤ ‖Zc f t‖ * (1 + |t|) * Real.exp (a * |t|)
    have h1 : ‖Zc f t‖ ≤ ‖Zc f t‖ * (1 + |t|) := le_mul_of_one_le_right (norm_nonneg _)
      (by linarith [abs_nonneg t])
    have h2 : Real.exp (a * t) ≤ Real.exp (a * |t|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self t) ha0)
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
  have habs : ∀ α : ℝ, |α| < π / 2 →
      |∫ t, Y t * Real.exp (α * t)| = 2 * π * ‖Fc f (cexp (α * I) * I)‖ := by
    intro α hα
    have h := integral_Zc_exp f hk hα
    have hc' : (∫ t : ℝ, Zc f t * cexp (α * t)) =
        ((∫ t, Y t * Real.exp (α * t) : ℝ) : ℂ) * c := by
      calc (∫ t : ℝ, Zc f t * cexp (α * t))
          = ∫ t : ℝ, ((Y t * Real.exp (α * t) : ℝ) : ℂ) * c := by
            refine integral_congr_ae (Eventually.of_forall fun t => ?_)
            simp only [hY, Complex.ofReal_mul, Complex.ofReal_exp]; ring
        _ = (∫ t : ℝ, ((Y t * Real.exp (α * t) : ℝ) : ℂ)) * c := integral_mul_const _ _
        _ = _ := by congr 1; exact integral_ofReal
    rw [hc'] at h
    have := congrArg norm h
    rw [norm_mul, hc, mul_one, Complex.norm_real, Real.norm_eq_abs] at this
    have e : ((((k : ℝ) / 2 : ℝ) : ℂ) * ((α : ℂ) * I)).re = 0 := by simp
    rw [this, norm_mul, norm_mul, norm_mul, Complex.norm_exp, e, Real.exp_zero, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  have hdec : ∀ N : ℕ, ∃ C β₀ : ℝ, 0 < β₀ ∧ ∀ β, 0 < β → β ≤ β₀ →
      |∫ t, Y t * Real.exp ((π / 2 - β) * t)| ≤ C * β ^ N := by
    intro N
    obtain ⟨C, β₀, hβ₀, hβ₀1, hC⟩ := Fc_rot_decay f N
    refine ⟨2 * π * C, β₀, hβ₀, fun β hβ hββ₀ => ?_⟩
    have hα : |π / 2 - β| < π / 2 := by
      rw [abs_lt]; constructor <;> linarith [Real.pi_gt_three]
    rw [habs _ hα]
    have := hC β hβ hββ₀
    calc 2 * π * ‖Fc f (cexp (((π / 2 - β : ℝ) : ℂ) * I) * I)‖ ≤ 2 * π * (C * β ^ N) := by
          gcongr
      _ = 2 * π * C * β ^ N := by ring
  intro T
  obtain ⟨t, ht, h0⟩ := hardy_abstract_parity Y hYc σ hσ hpar hint hdec T
  exact ⟨t, ht, by rw [hY, h0, ofReal_zero, zero_mul]⟩

/-- **Hardy's theorem for `Λ(f,s)`**: arbitrarily large zeros `k/2 + it` of the completed
L-function, for `f ≠ 0` with real coefficients. -/
theorem heckeLambda_infinitely_many_critical_zeros (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, (coef f n).im = 0) :
    ∀ T : ℝ, ∃ t > T, heckeLambda f ((k : ℂ) / 2 + t * I) = 0 := by
  have hk12 : 12 ≤ k := by
    by_contra h
    exact hf (eq_zero_of_lt_twelve f (by omega))
  have hk1 : 1 ≤ k := by omega
  have hsc : ∀ t : ℝ, (k : ℂ) / 2 + t * I = sc k t := by intro t; simp [sc]
  have hev : Even k := by
    rcases Nat.even_or_odd k with h | h
    · exact h
    · exact absurd (eq_zero_of_odd f h) hf
  obtain ⟨j, hj⟩ := hev
  have hIk : I ^ k = (-1) ^ j := by
    rw [hj, ← two_mul, pow_mul, I_sq]
  suffices H : ∀ T : ℝ, ∃ t > T, Zc f t = 0 by
    intro T
    obtain ⟨t, ht, h0⟩ := H T
    exact ⟨t, ht, by rw [hsc]; exact h0⟩
  rcases Nat.even_or_odd j with hj2 | hj2
  · -- `k ≡ 0 mod 4`: `Z` real and even
    have h1 : I ^ k = 1 := by rw [hIk, hj2.neg_one_pow]
    refine Zc_zeros_of_rep f hk12 1 (by simp) (fun t => (Zc f t).re) (fun t => ?_) 1
      (Or.inl rfl) (fun t => ?_)
    · have hc := Zc_conj f hk1 hreal t
      rw [h1, one_mul] at hc
      rw [mul_one]; exact (Complex.conj_eq_iff_re.mp hc).symm
    · simp only [Zc_neg f hk1, h1, one_mul]
  · -- `k ≡ 2 mod 4`: `Z = i·Y` with `Y` real and odd
    have h1 : I ^ k = -1 := by rw [hIk, hj2.neg_one_pow]
    refine Zc_zeros_of_rep f hk12 I (by simp) (fun t => (Zc f t).im) (fun t => ?_) (-1)
      (Or.inr rfl) (fun t => ?_)
    · have hc := Zc_conj f hk1 hreal t
      rw [h1, neg_one_mul] at hc
      have hre : (Zc f t).re = 0 := by
        have := congrArg Complex.re hc
        simp only [Complex.conj_re, Complex.neg_re] at this
        linarith
      apply Complex.ext <;> simp [hre]
    · simp only [Zc_neg f hk1, h1, neg_one_mul, Complex.neg_im]

/-- **Hardy's theorem for level-one cusp forms**: if `f ∈ S_k(SL₂(ℤ))` is nonzero with real
Fourier coefficients, then `L(f,s)` (the entire continuation `fL f` of `∑ a_f(n) n^{−s}`) has
zeros `k/2 + it` with `t` arbitrarily large. -/
theorem fL_infinitely_many_critical_zeros (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, (coef f n).im = 0) :
    ∀ T : ℝ, ∃ t > T, fL f ((k : ℂ) / 2 + t * I) = 0 := by
  intro T
  obtain ⟨t, ht, h0⟩ := heckeLambda_infinitely_many_critical_zeros f hf hreal T
  exact ⟨t, ht, by rw [fL, h0, mul_zero]⟩

/-- **The set of ordinates of critical zeros of `L(f,s)` is infinite.** -/
theorem fL_critical_zeros_infinite (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, (coef f n).im = 0) :
    Set.Infinite {t : ℝ | fL f ((k : ℂ) / 2 + t * I) = 0} := by
  refine Set.infinite_of_not_bddAbove fun ⟨T, hT⟩ => ?_
  obtain ⟨t, ht, h0⟩ := fL_infinitely_many_critical_zeros f hf hreal T
  exact absurd (hT h0) (not_le.mpr ht)

/-- **Infinitely many zeros of `L(f,s)` on `Re s = k/2`**, as a set of complex numbers. -/
theorem fL_zeros_on_critical_line_infinite (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0)
    (hreal : ∀ n, (coef f n).im = 0) :
    Set.Infinite {s : ℂ | s.re = (k : ℝ) / 2 ∧ fL f s = 0} := by
  have hinj : Set.InjOn (fun t : ℝ => (k : ℂ) / 2 + t * I)
      {t : ℝ | fL f ((k : ℂ) / 2 + t * I) = 0} := by
    intro a _ b _ h
    have := congrArg Complex.im h
    simpa using this
  refine Set.infinite_of_injOn_mapsTo hinj (fun t ht => ?_)
    (fL_critical_zeros_infinite f hf hreal)
  refine ⟨?_, ht⟩
  simp

/-! ### The case `f = Δ` -/

lemma discriminant_ne_zero' :
    (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) ≠ 0 := by
  intro h
  have := congrArg (fun g : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ) => g UpperHalfPlane.I) h
  exact ModularForm.discriminant_ne_zero UpperHalfPlane.I (by simpa using this)

/-- **Hardy's theorem for `L(Δ,s)`, recovered from the general theorem**: zeros `6 + it` of
`fL Δ` with `t` arbitrarily large. -/
theorem fL_discriminant_infinitely_many_critical_zeros :
    ∀ T : ℝ, ∃ t > T,
      fL (k := 12) (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) (6 + t * I) = 0 := by
  intro T
  obtain ⟨t, ht, h0⟩ := fL_infinitely_many_critical_zeros (k := 12) _ discriminant_ne_zero'
    (fun n => by rw [coef_discriminant]; simp [RamanujanTau.tauC]) T
  refine ⟨t, ht, ?_⟩
  have e : ((12 : ℕ) : ℂ) / 2 = 6 := by norm_num
  rwa [e] at h0

end RamanujanTau.HardyZerosGeneral

#print axioms RamanujanTau.HardyZerosGeneral.hardy_abstract_parity
#print axioms RamanujanTau.HardyZerosGeneral.hardy_abstract_odd
#print axioms RamanujanTau.HardyZerosGeneral.integral_Zc_exp
#print axioms RamanujanTau.HardyZerosGeneral.Fc_rot_decay
#print axioms RamanujanTau.HardyZerosGeneral.eq_zero_of_odd
#print axioms RamanujanTau.HardyZerosGeneral.heckeLambda_infinitely_many_critical_zeros
#print axioms RamanujanTau.HardyZerosGeneral.fL_infinitely_many_critical_zeros
#print axioms RamanujanTau.HardyZerosGeneral.fL_critical_zeros_infinite
#print axioms RamanujanTau.HardyZerosGeneral.fL_zeros_on_critical_line_infinite
#print axioms RamanujanTau.HardyZerosGeneral.fL_discriminant_infinitely_many_critical_zeros
