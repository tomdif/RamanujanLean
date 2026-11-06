/-
# Item 2: the Hölder step for `Ψ_{a,b}` on `Γ₀(q)\(ℍ×ℍ)`, `q = ab`

No fundamental domain is used.  With `P_q(p) = Σ_{h ∈ Γ₀(q)} ft(h p)` and the finite set of right
cosets `x ∈ Γ₀(q)\SL₂(ℤ)` with representatives `x.out`:

* `tsum_coset`: `Σ_{γ ∈ SL₂(ℤ)} g(γ) = Σ_x Σ_{h ∈ Γ₀(q)} g(h·x.out)` (absolutely summable `g`);
* pointwise, `Σ_γ ft(γp) conj P_q(γp) = Σ_x |P_q(x.out p)|²` and
  `Σ_γ Ψ(γp) conj ft(γp) = Σ_x Ψ(x.out p) conj P_q(x.out p)` (invariance of `Ψ_{a,b}` and `P_q`);
* unfolding over `SL₂(ℤ)` (`SCSProof.integral_unfold2`) then gives
  `∫_{U×ℍ} Σ_x |P_q(x.out p)|² ≤ 2‖Σ_{h∈Γ₀(q)} I(h)‖` (`lintegral_SQ_le`), and
* **`norm_QAB_le`**: `‖∫ Ψ_{a,b} conj ft‖ ≤ ½ √(c² · q⁴ · 8R) · √(2‖Σ_{h∈Γ₀(q)} I(h)‖)`,
  `c = M (ab)^{−6} R⁶`, using Cauchy–Schwarz over the `≤ q⁴` cosets and Hölder on `U × ℍ`.
-/
import RamanujanTau.SCS2Coprime.Index
import RamanujanTau.SCS2Coprime.CoeffAB
import RamanujanTau.SCSSharp.NormQ

set_option autoImplicit false

namespace RamanujanTau.SCS2Coprime

open MeasureTheory Set Complex CongruenceSubgroup
open UpperHalfPlane hiding I
open RamanujanTau.SCSProof RamanujanTau.SCSSharp
open RamanujanTau.EisensteinReal.Horo (Uset)
open scoped MatrixGroups ENNReal Real ComplexConjugate

section coset

variable (H : Subgroup SL(2, ℤ))

/-- `RCos H × H ≃ SL₂(ℤ)`, `(x, h) ↦ h · x.out`. -/
noncomputable def cosetEquiv' : RCos H × H ≃ SL(2, ℤ) :=
  (Equiv.prodComm _ _).trans (cosetEquiv H)

lemma tsum_coset (g : SL(2, ℤ) → ℂ) (hg : Summable g) :
    ∑' γ, g γ = ∑' x : RCos H, ∑' h : H, g ((h : SL(2, ℤ)) * x.out) := by
  rw [← (cosetEquiv' H).tsum_eq]
  exact (hg.comp_injective (cosetEquiv' H).injective).tsum_prod

lemma finite_RCos_Gamma0 (q : ℕ) (hq : 1 ≤ q) : Finite (RCos (Gamma0 q)) := by
  haveI : NeZero q := ⟨by omega⟩
  have e : Nat.card (RCos (Gamma0 q)) = (Gamma0 q).index := by
    rw [Subgroup.index]
    exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)
  exact Nat.finite_of_card_ne_zero (by rw [e]; exact Subgroup.FiniteIndex.index_ne_zero)

end coset

variable (P : Par)

/-- `Σ_γ ‖ft(γp)‖ ≤ N₀` for every `p`. -/
lemma tsum_enorm_ft_le_N0 (p : ℍ × ℍ) : ∑' γ : SL(2, ℤ), ‖ft P (dsmul γ p)‖ₑ ≤ N0 P := by
  by_cases h : ∀ γ : SL(2, ℤ), ft P (dsmul γ p) = 0
  · simp [h]
  push Not at h
  obtain ⟨γ₀, h0⟩ := h
  have key := tsum_enorm_ft_le P (dsmul γ₀ p)
  have hre : ∑' γ : SL(2, ℤ), ‖ft P (dsmul γ (dsmul γ₀ p))‖ₑ =
      ∑' γ : SL(2, ℤ), ‖ft P (dsmul γ p)‖ₑ := by
    simp_rw [← dsmul_mul]
    exact (Equiv.mulRight γ₀).tsum_eq (fun δ => ‖ft P (dsmul δ p)‖ₑ)
  rw [hre] at key
  have hne : ‖ft P (dsmul γ₀ p)‖ₑ ≠ 0 := enorm_ne_zero.2 h0
  have hnt : ‖ft P (dsmul γ₀ p)‖ₑ ≠ ∞ := enorm_ne_top
  rw [mul_comm (N0 P : ℝ≥0∞)] at key
  exact (ENNReal.mul_le_mul_iff_right hne hnt).1 key

lemma summable_norm_ft_dsmul (p : ℍ × ℍ) :
    Summable fun γ : SL(2, ℤ) => ‖ft P (dsmul γ p)‖ := by
  have hfin : ∑' γ : SL(2, ℤ), ‖ft P (dsmul γ p)‖ₑ ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (tsum_enorm_ft_le_N0 P p)
  exact (ENNReal.summable_toReal hfin).congr fun γ => by simp

lemma tsum_norm_ft_le (p : ℍ × ℍ) : ∑' γ : SL(2, ℤ), ‖ft P (dsmul γ p)‖ ≤ N0 P := by
  have h := tsum_enorm_ft_le_N0 P p
  have e : ∑' γ : SL(2, ℤ), ‖ft P (dsmul γ p)‖ₑ =
      ENNReal.ofReal (∑' γ : SL(2, ℤ), ‖ft P (dsmul γ p)‖) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (summable_norm_ft_dsmul P p)]
    simp_rw [ofReal_norm_eq_enorm]
  rw [e, ← ENNReal.ofReal_natCast] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

/-- The incomplete Poincaré series over `Γ₀(q)`. -/
noncomputable def PtQ (q : ℕ) (p : ℍ × ℍ) : ℂ := ∑' h : Gamma0 q, ft P (dsmul h p)

lemma PtQ_smul (q : ℕ) (h : Gamma0 q) (p : ℍ × ℍ) : PtQ P q (dsmul h p) = PtQ P q p := by
  unfold PtQ
  simp_rw [← dsmul_mul]
  exact (Equiv.mulRight h).tsum_eq (fun δ : Gamma0 q => ft P (dsmul (δ : SL(2, ℤ)) p))

lemma measurable_PtQ (q : ℕ) : Measurable (PtQ P q) := by
  unfold PtQ
  exact Measurable.tsum fun h => measurable_ft_dsmul P h

lemma norm_PtQ_le (q : ℕ) (p : ℍ × ℍ) : ‖PtQ P q p‖ ≤ N0 P := by
  unfold PtQ
  have hs : Summable fun h : Gamma0 q => ‖ft P (dsmul (h : SL(2, ℤ)) p)‖ :=
    (summable_norm_ft_dsmul P p).comp_injective Subtype.val_injective
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  refine le_trans ?_ (tsum_norm_ft_le P p)
  exact Summable.tsum_subtype_le (fun γ : SL(2, ℤ) => ‖ft P (dsmul γ p)‖) _
    (fun _ => norm_nonneg _) (summable_norm_ft_dsmul P p)

lemma Dh_le_of_PtQ (q : ℕ) (p : ℍ × ℍ) (hp : PtQ P q p ≠ 0) : Dh p.1 p.2 ≤ Rθ P := by
  by_contra hD
  apply hp
  unfold PtQ
  have : ∀ h : Gamma0 q, ft P (dsmul h p) = 0 := by
    intro h
    by_contra hne
    have := Dh_le_of_ft P _ hne
    simp only [dsmul] at this
    rw [Dh_smul] at this
    exact hD this
  simp [this]

/-! ### The norm square -/

/-- `S_q(p) = Σ_x |P_q(x.out p)|²`. -/
noncomputable def SQ (q : ℕ) (p : ℍ × ℍ) : ℝ :=
  ∑' x : RCos (Gamma0 q), ‖PtQ P q (dsmul x.out p)‖ ^ 2

lemma SQ_nonneg (q : ℕ) (p : ℍ × ℍ) : 0 ≤ SQ P q p := tsum_nonneg fun _ => by positivity

lemma measurable_SQ (q : ℕ) (hq : 1 ≤ q) : Measurable (SQ P q) := by
  haveI := finite_RCos_Gamma0 q hq
  haveI := Fintype.ofFinite (RCos (Gamma0 q))
  have e : SQ P q = fun p => ∑ x : RCos (Gamma0 q), ‖PtQ P q (dsmul x.out p)‖ ^ 2 := by
    funext p; unfold SQ; rw [tsum_fintype]
  rw [e]
  exact Finset.measurable_sum _ fun x _ =>
    ((measurable_PtQ P q).comp (measurable_dsmul _)).norm.pow_const 2

lemma summable_ft_PtQ (q : ℕ) (p : ℍ × ℍ) :
    Summable fun γ : SL(2, ℤ) => ft P (dsmul γ p) * conj (PtQ P q (dsmul γ p)) := by
  refine Summable.of_norm_bounded ((summable_norm_ft_dsmul P p).mul_right (N0 P : ℝ)) fun γ => ?_
  rw [norm_mul, Complex.norm_conj]
  gcongr
  exact norm_PtQ_le P q _

lemma tsum_ft_PtQ (q : ℕ) (p : ℍ × ℍ) :
    ∑' γ : SL(2, ℤ), ft P (dsmul γ p) * conj (PtQ P q (dsmul γ p)) = ((SQ P q p : ℝ) : ℂ) := by
  rw [tsum_coset (Gamma0 q) _ (summable_ft_PtQ P q p)]
  unfold SQ
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun x => ?_
  simp_rw [dsmul_mul, PtQ_smul]
  rw [tsum_mul_right]
  change PtQ P q (dsmul x.out p) * conj (PtQ P q (dsmul x.out p)) = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma integral_ft_PtQ (q : ℕ) :
    ∫ p, ft P p * conj (PtQ P q p) = ∑' h : Gamma0 q, Iγ P h := by
  unfold PtQ Iγ
  have hmeas : ∀ h : Gamma0 q, AEStronglyMeasurable
      (fun p => ft P p * conj (ft P (dsmul h p))) volume := fun h =>
    ((measurable_ft P).mul (Complex.continuous_conj.measurable.comp
      (measurable_ft_dsmul P h))).aestronglyMeasurable
  have hfin : ∑' h : Gamma0 q, ∫⁻ p, ‖ft P p * conj (ft P (dsmul h p))‖ₑ ≠ ∞ := by
    simp_rw [enorm_mul, RCLike.enorm_conj]
    exact ne_top_of_le_ne_top (tsum_Ip_ne_top P)
      (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (Ip P))
  rw [← integral_tsum hmeas hfin]
  congr 1; funext p
  rw [Complex.conj_tsum, tsum_mul_left]

lemma enorm_ft_PtQ_le (q : ℕ) (p : ℍ × ℍ) :
    ‖ft P p * conj (PtQ P q p)‖ₑ ≤ N0 P * ‖ft P p‖ₑ := by
  rw [enorm_mul, RCLike.enorm_conj, mul_comm]
  gcongr
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (norm_PtQ_le P q p)

/-- **`‖P_q‖²` on `Γ₀(q)\(ℍ×ℍ)`**: `(∫⁻_{U×ℍ} S_q).toReal ≤ 2 ‖Σ_{h ∈ Γ₀(q)} I(h)‖`. -/
theorem lintegral_SQ_le (q : ℕ) (hq : 1 ≤ q) :
    (∫⁻ p, indU p * ENNReal.ofReal (SQ P q p)).toReal ≤ 2 * ‖∑' h : Gamma0 q, Iγ P h‖ := by
  have hg : Measurable fun p => ft P p * conj (PtQ P q p) :=
    (measurable_ft P).mul (Complex.continuous_conj.measurable.comp (measurable_PtQ P q))
  have hgi : ∫⁻ p, ‖ft P p * conj (PtQ P q p)‖ₑ ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := (N0 P : ℝ≥0∞) * ∫⁻ p, ‖ft P p‖ₑ)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (lintegral_ft_ne_top P)) ?_
    rw [← lintegral_const_mul _ (measurable_ft P).enorm]
    exact lintegral_mono fun p => enorm_ft_PtQ_le P q p
  have h := integral_unfold2 _ hg hgi
  simp only at h
  simp_rw [tsum_ft_PtQ P q, integral_ft_PtQ P q] at h
  have hpt : ∀ p : ℍ × ℍ, indUC p * ((SQ P q p : ℝ) : ℂ) =
      (((indU p * ENNReal.ofReal (SQ P q p)).toReal : ℝ) : ℂ) := by
    intro p
    unfold indUC indU
    by_cases hU : p.1 ∈ Uset
    · rw [indicator_of_mem hU, indicator_of_mem hU]
      simp only [Pi.one_apply, one_mul]
      rw [ENNReal.toReal_ofReal (SQ_nonneg P q p)]
    · rw [indicator_of_notMem hU, indicator_of_notMem hU]; simp
  simp_rw [hpt] at h
  rw [integral_complex_ofReal] at h
  have hfin : ∀ᵐ p ∂(volume : Measure (ℍ × ℍ)), indU p * ENNReal.ofReal (SQ P q p) < ∞ := by
    refine Filter.Eventually.of_forall fun p => ?_
    unfold indU
    by_cases hU : p.1 ∈ Uset
    · rw [indicator_of_mem hU]; simp
    · rw [indicator_of_notMem hU]; simp
  have hm : AEMeasurable (fun p => indU p * ENNReal.ofReal (SQ P q p)) volume :=
    (measurable_indU.mul (ENNReal.measurable_ofReal.comp (measurable_SQ P q hq))).aemeasurable
  rw [integral_toReal hm hfin] at h
  have := congrArg norm h
  rw [Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg, norm_mul] at this
  rw [this]; simp

end RamanujanTau.SCS2Coprime
