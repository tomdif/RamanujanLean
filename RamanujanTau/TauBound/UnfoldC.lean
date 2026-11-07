/-
# Unfolding the `c`-th layer of the Poincaré series

`unfold_c`: for `c ≥ 1`, `y > 0`,
`∑_{d ∈ ℤ} ∫₀¹ e(-n w) T(c,d,w) du = c^{-12} S(1,n;c) K(n,c;y)`   (`w = u + iy`),
proved by `d = d₀ + c t`, `∑_t ∫₀¹ g(u + t) du = ∫_ℝ g` (Mathlib
`Integrable.hasSum_intervalIntegral_comp_add_int`) and translation invariance.
-/
import RamanujanTau.TauBound.Poincare

set_option autoImplicit false

namespace RamanujanTau.TauBound

open Complex MeasureTheory
open scoped Real

/-- The `kInt` integrand. -/
noncomputable def kIntegrand (n c : ℕ) (y : ℝ) (x : ℝ) : ℂ :=
  ((x : ℂ) + y * I) ^ (-12 : ℤ) * ee (-1 / ((c : ℂ) ^ 2 * ((x : ℂ) + y * I))) *
    ee (-(n : ℂ) * ((x : ℂ) + y * I))

lemma kInt_eq (n c : ℕ) (y : ℝ) : kInt n c y = ∫ x, kIntegrand n c y x := rfl

lemma w_ne_zero {y : ℝ} (hy : 0 < y) (x : ℝ) : (x : ℂ) + y * I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this; linarith

lemma continuous_ee : Continuous ee := by
  unfold ee; fun_prop

lemma continuous_kIntegrand (n c : ℕ) (hc : c ≠ 0) {y : ℝ} (hy : 0 < y) :
    Continuous (kIntegrand n c y) := by
  unfold kIntegrand
  have hw : Continuous fun x : ℝ => (x : ℂ) + y * I := by fun_prop
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  refine Continuous.mul (Continuous.mul ?_ ?_) ?_
  · exact hw.zpow₀ _ (fun x => Or.inl (w_ne_zero hy x))
  · refine continuous_ee.comp (continuous_const.div (continuous_const.mul hw) fun x => ?_)
    exact mul_ne_zero (pow_ne_zero _ hc') (w_ne_zero hy x)
  · exact continuous_ee.comp (continuous_const.mul hw)

lemma integrable_kIntegrand (n c : ℕ) (hc : c ≠ 0) {y : ℝ} (hy : 0 < y) :
    Integrable (kIntegrand n c y) := by
  have hb := (integrable_bracket (r := 0) (by norm_num) hy).const_mul
    (expConst 0 * Real.exp (2 * π * n * y) * (2 * π * y / (c : ℝ) ^ 2) ^ (-(0 : ℝ)))
  refine hb.mono' (continuous_kIntegrand n c hc hy).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  exact norm_integrand_le le_rfl n c hc hy x

lemma ee_add (a b : ℂ) : ee (a + b) = ee a * ee b := by
  unfold ee; rw [← Complex.exp_add]; ring_nf

lemma ee_intCast (k : ℤ) : ee k = 1 := by
  unfold ee
  rw [show 2 * π * I * (k : ℂ) = k * (2 * π * I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-- Pointwise identity for a coprime `d`. -/
lemma term_eq (n c : ℕ) (hc : c ≠ 0) {y : ℝ} (hy : 0 < y) (d : ℤ) (hd : Int.gcd c d = 1)
    (u : ℝ) :
    ee (-(n : ℂ) * ((u : ℂ) + y * I)) * poincareTerm c d ((u : ℂ) + y * I) =
      (c : ℂ) ^ (-12 : ℤ) * ee (((((d : ZMod c)⁻¹).val : ℂ) + n * d) / c) *
        kIntegrand n c y (u + d / c) := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  set W : ℂ := (((u + d / c : ℝ)) : ℂ) + y * I with hW
  have hW0 : W ≠ 0 := w_ne_zero hy _
  have hcw : (c : ℂ) * ((u : ℂ) + y * I) + d = c * W := by
    rw [hW]; push_cast; field_simp; ring
  unfold poincareTerm kIntegrand
  rw [if_pos hd, hcw, mul_zpow, ← hW]
  set a : ℂ := (((d : ZMod c)⁻¹).val : ℂ)
  have e1 : ee (-(n : ℂ) * ((u : ℂ) + y * I)) * ee (a / c - 1 / (c * (c * W))) =
      ee ((a + n * d) / c) * (ee (-1 / ((c : ℂ) ^ 2 * W)) * ee (-(n : ℂ) * W)) := by
    rw [← ee_add, ← ee_add, ← ee_add]
    congr 1
    have hwW : (u : ℂ) + y * I = W - d / c := by rw [hW]; push_cast; ring
    rw [hwW]; field_simp; ring
  calc ee (-(n : ℂ) * ((u : ℂ) + y * I)) * ((c : ℂ) ^ (-12 : ℤ) * W ^ (-12 : ℤ) *
        ee (a / c - 1 / (c * (c * W))))
      = (c : ℂ) ^ (-12 : ℤ) * W ^ (-12 : ℤ) *
          (ee (-(n : ℂ) * ((u : ℂ) + y * I)) * ee (a / c - 1 / (c * (c * W)))) := by ring
    _ = _ := by rw [e1]; ring

/-- Kloosterman symmetry `S(n,1;c) = S(1,n;c)`. -/
lemma kloosterman_symm (m n : ℤ) (c : ℕ) : kloosterman m n c = kloosterman n m c := by
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · subst h0; simp [kloosterman]
  haveI : NeZero c := ⟨hpos.ne'⟩
  rw [kloosterman_eq_kl, kloosterman_eq_kl]
  unfold kl
  refine Fintype.sum_equiv (Equiv.inv _) _ _ (fun u => ?_)
  simp only [Equiv.inv_apply, inv_inv]
  congr 1; ring

/-- `d̄ mod c` as a complex number. -/
noncomputable def abar (c : ℕ) (d : ℤ) : ℂ := (((d : ZMod c)⁻¹).val : ℂ)

/-- The `(c,d)` coefficient integral. -/
noncomputable def coefTerm (n c : ℕ) (y : ℝ) (d : ℤ) : ℂ :=
  ∫ u in (0 : ℝ)..1, ee (-(n : ℂ) * ((u : ℂ) + y * I)) * poincareTerm c d ((u : ℂ) + y * I)

lemma gcd_shift (c : ℕ) (d0 t : ℤ) : Int.gcd c (d0 + c * t) = Int.gcd c d0 := by
  rw [Int.gcd_comm, Int.gcd_comm (c : ℤ) d0]
  simp

lemma coefTerm_shift (n c : ℕ) (hc : c ≠ 0) {y : ℝ} (hy : 0 < y) (d0 : ℕ)
    (hd0 : Nat.Coprime d0 c) (t : ℤ) :
    coefTerm n c y (d0 + c * t) = (c : ℂ) ^ (-12 : ℤ) *
      ee ((abar c d0 + n * d0) / c) *
      ∫ u in (0 : ℝ)..1, kIntegrand n c y (u + t + d0 / c) := by
  have hgcd : Int.gcd c ((d0 : ℤ) + c * t) = 1 := by
    rw [gcd_shift, Int.gcd_natCast_natCast, Nat.gcd_comm]; exact hd0
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  unfold coefTerm
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  rw [term_eq n c hc hy _ hgcd u]
  have hz : (((d0 : ℤ) + c * t : ℤ) : ZMod c) = ((d0 : ℤ) : ZMod c) := by simp
  rw [hz]
  change (c : ℂ) ^ (-12 : ℤ) * ee ((abar c d0 + n * (((d0 : ℤ) + c * t : ℤ) : ℂ)) / c) * _ = _
  have he : ee ((abar c d0 + n * (((d0 : ℤ) + c * t : ℤ) : ℂ)) / c) =
      ee ((abar c d0 + n * d0) / c) := by
    rw [show (abar c d0 + n * (((d0 : ℤ) + c * t : ℤ) : ℂ)) / c =
      (abar c d0 + n * d0) / c + ((n * t : ℤ) : ℂ) by
        push_cast; field_simp; ring]
    rw [ee_add, ee_intCast, mul_one]
  rw [he]
  congr 2
  push_cast; field_simp; ring

lemma coefTerm_noncop (n c : ℕ) (y : ℝ) (d : ℤ) (hd : Int.gcd c d ≠ 1) :
    coefTerm n c y d = 0 := by
  simp only [coefTerm, poincareTerm, if_neg hd, mul_zero, intervalIntegral.integral_zero]

/-- **Unfolding of the `c`-th layer.** -/
theorem unfold_c (n c : ℕ) (hc : c ≠ 0) {y : ℝ} (hy : 0 < y) :
    HasSum (coefTerm n c y) ((c : ℂ) ^ (-12 : ℤ) * kloosterman 1 n c * kInt n c y) := by
  classical
  have hcpos : (0 : ℤ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc
  set φ : ℕ → ℂ := fun d0 => ee ((abar c d0 + n * d0) / c)
  set A : ℕ → ℂ := fun d0 => if Nat.Coprime d0 c then
    (c : ℂ) ^ (-12 : ℤ) * φ d0 * kInt n c y else 0
  set F : ℕ → ℤ → ℂ := fun d0 d => if d % c = d0 then coefTerm n c y d else 0
  have hF : ∀ d0 ∈ Finset.range c, HasSum (F d0) (A d0) := by
    intro d0 hd0
    have hd0' : (d0 : ℤ) < c := by exact_mod_cast Finset.mem_range.mp hd0
    have hinj : Function.Injective (fun t : ℤ => (d0 : ℤ) + c * t) := by
      intro a b h; simp only at h
      have : (c : ℤ) * a = c * b := by linarith
      exact mul_left_cancel₀ hcpos.ne' this
    have hmod : ∀ t : ℤ, ((d0 : ℤ) + c * t) % c = d0 := by
      intro t
      rw [Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by positivity) hd0'
    refine (hinj.hasSum_iff (fun d hd => ?_)).mp ?_
    · simp only [F]
      rw [if_neg]
      intro hdc
      apply hd
      refine ⟨d / c, ?_⟩
      simp only
      have := Int.emod_add_mul_ediv d c
      rw [hdc] at this; linarith
    · simp only [F, Function.comp_def, hmod, if_true]
      by_cases hcop : Nat.Coprime d0 c
      · simp only [A, if_pos hcop]
        simp_rw [coefTerm_shift n c hc hy d0 hcop]
        refine HasSum.mul_left _ ?_
        have hint := (integrable_kIntegrand n c hc hy).comp_add_right ((d0 : ℝ) / c)
        have := hint.hasSum_intervalIntegral_comp_add_int
        rw [integral_add_right_eq_self (fun x => kIntegrand n c y x) ((d0 : ℝ) / c)] at this
        exact this
      · simp only [A, if_neg hcop]
        have : ∀ t : ℤ, coefTerm n c y ((d0 : ℤ) + c * t) = 0 := by
          intro t
          apply coefTerm_noncop
          rw [gcd_shift, Int.gcd_natCast_natCast, Nat.gcd_comm]; exact hcop
        simp_rw [this]; exact hasSum_zero
  have hsum := hasSum_sum hF
  have hpt : (fun d => ∑ d0 ∈ Finset.range c, F d0 d) = coefTerm n c y := by
    funext d
    have h0 : 0 ≤ d % c := Int.emod_nonneg _ hcpos.ne'
    have h1 : d % c < c := Int.emod_lt_of_pos _ hcpos
    rw [Finset.sum_eq_single (d % c).toNat]
    · simp only [F, Int.toNat_of_nonneg h0, if_true]
    · intro b _ hb
      simp only [F]
      rw [if_neg]
      intro h; apply hb; rw [h]; simp
    · intro h; exfalso; apply h
      rw [Finset.mem_range]; omega
  rw [hpt] at hsum
  convert hsum using 1
  simp only [A]
  rw [← Finset.sum_filter, kloosterman_symm, kloosterman, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun d0 _ => ?_)
  simp only [φ]
  simp only [abar, Int.cast_natCast]
  congr 1; push_cast; ring_nf

end RamanujanTau.TauBound
