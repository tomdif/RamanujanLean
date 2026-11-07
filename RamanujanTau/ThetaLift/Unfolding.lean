import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Unfolding

Let `H` act on `α` with a fundamental domain `F`, and let `St` be an exact fundamental domain of a
subgroup `A`. For an `A`-invariant function `f` integrable on `St`, the integral of `f` over `St` is
the integral over `F` of the sum of `f` over `A\H`.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open MeasureTheory Set
open scoped ENNReal Pointwise

noncomputable section

variable {α H : Type*} [Group H] [MulAction H α] {St : Set α} {A : Subgroup H}

/-- Every point has exactly one `A`-translate in `St`. -/
def ExactDomain (A : Subgroup H) (St : Set α) : Prop := ∀ x : α, ∃! a : A, ((a : H)⁻¹ • x) ∈ St

/-- The decomposition of `H` into left cosets of `A`. -/
def cosetEquiv (A : Subgroup H) : (H ⧸ A) × A ≃ H where
  toFun p := p.1.out * (p.2 : H)
  invFun g := ((g : H ⧸ A), ⟨(g : H ⧸ A).out⁻¹ * g, by
    rw [← QuotientGroup.eq]
    simp⟩)
  left_inv p := by
    obtain ⟨r, a⟩ := p
    have h : ((r.out * (a : H) : H) : H ⧸ A) = r := by
      rw [QuotientGroup.mk_mul_of_mem _ a.2, QuotientGroup.out_eq']
    ext
    · simp [h]
    · simp [h]
  right_inv g := by simp

/-- The sum over the fibre of `A` for the indicator of `St` gives the value of `f`. -/
lemma hasSum_indicator_fiber {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (hSt : ExactDomain A St) {f : α → E}
    (hf : ∀ (a : A) (x : α), f ((a : H)⁻¹ • x) = f x) (x : α) :
    HasSum (fun a : A => St.indicator f ((a : H)⁻¹ • x)) (f x) := by
  classical
  obtain ⟨a₀, ha₀, huniq⟩ := hSt x
  have h := hasSum_single (f := fun a : A => St.indicator f ((a : H)⁻¹ • x)) a₀ (fun a ha => by
    have : ((a : H)⁻¹ • x) ∉ St := fun hmem => ha (huniq a hmem)
    simp [indicator_of_notMem this])
  simp only [indicator_of_mem ha₀, hf] at h
  exact h

lemma smul_cosetEquiv_inv (p : (H ⧸ A) × A) (x : α) :
    (cosetEquiv A p)⁻¹ • x = (p.2 : H)⁻¹ • (p.1.out⁻¹ • x) := by
  change (p.1.out * (p.2 : H))⁻¹ • x = _
  rw [mul_inv_rev, mul_smul]

variable [MeasurableSpace α] {μ : Measure α} [Countable H] [MeasurableConstSMul H α]
  [SMulInvariantMeasure H α μ] {F : Set α}

/-- **Unfolding for nonnegative functions.** -/
theorem unfold_lintegral (hF : IsFundamentalDomain H F μ) (hSt : ExactDomain A St)
    (hStm : MeasurableSet St) {f : α → ℝ≥0∞} (hfm : Measurable f)
    (hf : ∀ (a : A) (x : α), f ((a : H)⁻¹ • x) = f x) :
    ∫⁻ x in St, f x ∂μ = ∫⁻ x in F, ∑' r : H ⧸ A, f (r.out⁻¹ • x) ∂μ := by
  have hsw := lintegral_tsum (μ := μ.restrict F) (f := fun (g : H) x => St.indicator f (g⁻¹ • x))
    fun g => ((hfm.indicator hStm).comp (measurable_const_smul g⁻¹)).aemeasurable
  rw [← lintegral_indicator hStm, hF.lintegral_eq_tsum', ← hsw]
  refine lintegral_congr fun x => ?_
  rw [← (cosetEquiv A).tsum_eq]
  simp only [smul_cosetEquiv_inv]
  exact (ENNReal.tsum_prod (f := fun (r : H ⧸ A) (a : A) =>
    St.indicator f ((a : H)⁻¹ • (r.out⁻¹ • x)))).trans
      (tsum_congr fun r => (hasSum_indicator_fiber hSt hf (r.out⁻¹ • x)).tsum_eq)

/-- **Unfolding.** -/
theorem unfold_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hF : IsFundamentalDomain H F μ) (hSt : ExactDomain A St) (hStm : MeasurableSet St)
    {f : α → E} (hfi : IntegrableOn f St μ)
    (hf : ∀ (a : A) (x : α), f ((a : H)⁻¹ • x) = f x) :
    (∀ᵐ x ∂μ.restrict F, Summable fun r : H ⧸ A => f (r.out⁻¹ • x)) ∧
      ∫ x in St, f x ∂μ = ∫ x in F, ∑' r : H ⧸ A, f (r.out⁻¹ • x) ∂μ := by
  have hint : Integrable (St.indicator f) μ := hfi.integrable_indicator hStm
  set t := St.indicator f with ht
  have hcomp : ∀ g : H, AEStronglyMeasurable (fun x => t (g⁻¹ • x)) (μ.restrict F) := fun g =>
    ((hint.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_smul g⁻¹ μ))).restrict
  have hfin : ∑' g : H, ∫⁻ x in F, ‖t (g⁻¹ • x)‖ₑ ∂μ ≠ ⊤ := by
    rw [← hF.lintegral_eq_tsum' fun x => ‖t x‖ₑ]
    exact hint.2.ne
  have hae : ∀ᵐ x ∂μ.restrict F, Summable fun g : H => t (g⁻¹ • x) := by
    have hmeas : ∀ g : H, AEMeasurable (fun x => ‖t (g⁻¹ • x)‖ₑ) (μ.restrict F) := fun g =>
      (hcomp g).enorm
    have hlt : ∀ᵐ x ∂μ.restrict F, ∑' g : H, ‖t (g⁻¹ • x)‖ₑ < ⊤ := by
      refine ae_lt_top' (AEMeasurable.tsum hmeas) ?_
      rwa [lintegral_tsum hmeas]
    filter_upwards [hlt] with x hx
    refine Summable.of_norm ?_
    have := ENNReal.summable_toReal hx.ne
    refine this.congr fun g => ?_
    simp [toReal_enorm]
  have hsumr : ∀ x, Summable (fun g : H => t (g⁻¹ • x)) →
      Summable (fun r : H ⧸ A => f (r.out⁻¹ • x)) ∧
        ∑' g : H, t (g⁻¹ • x) = ∑' r : H ⧸ A, f (r.out⁻¹ • x) := by
    intro x hx
    have hp : Summable fun p : (H ⧸ A) × A => t ((p.2 : H)⁻¹ • (p.1.out⁻¹ • x)) := by
      have := ((cosetEquiv A).summable_iff (f := fun g : H => t (g⁻¹ • x))).mpr hx
      refine this.congr fun p => ?_
      simp only [Function.comp, smul_cosetEquiv_inv]
    have hfib : ∀ r : H ⧸ A, ∑' a : A, t ((a : H)⁻¹ • (r.out⁻¹ • x)) = f (r.out⁻¹ • x) := fun r =>
      (hasSum_indicator_fiber hSt hf (r.out⁻¹ • x)).tsum_eq
    refine ⟨hp.prod.congr hfib, ?_⟩
    rw [← (cosetEquiv A).tsum_eq]
    simp only [smul_cosetEquiv_inv]
    rw [hp.tsum_prod' fun r => hp.prod_factor r]
    exact tsum_congr hfib
  refine ⟨hae.mono fun x hx => (hsumr x hx).1, ?_⟩
  have hdecomp : ∫ x in St, f x ∂μ = ∫ x, t x ∂μ := (integral_indicator hStm).symm
  rw [hdecomp, hF.integral_eq_tsum' t hint, ← integral_tsum hcomp hfin]
  refine integral_congr_ae (hae.mono fun x hx => (hsumr x hx).2)

end

end RamanujanTau.ThetaLift
