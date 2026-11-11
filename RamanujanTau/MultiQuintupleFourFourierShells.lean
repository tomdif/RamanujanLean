import RamanujanTau.MultiQuintupleFourFourier

/-! Persistent four-factor vanishing forces cancellation on every actual dual shell. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 1000000

noncomputable def fourDualBranchTerm (p : ℕ) (v : Fin 4 → ℕ) (R : ℕ) (a : ℂ)
    (b : Fin 4 → Bool) (x : ZMod p × (Fin 4 → ℤ)) : ℂ :=
  (fourBranchWeight b : ℂ)*
    fourCongruenceGaussianPhase p (fun i => 3*(v i : ℤ)) (fourBranchResidue v R b)
      (fourBranchShift p v b) x.1 *
      fourSeparatedDualGaussian a (fourBranchShift p v b)
        (fourCongruenceModulation p (fun i => 3*(v i : ℤ)) x.1) x.2

theorem summable_fourDualBranchTerm (p : ℕ) [NeZero p] (v : Fin 4 → ℕ) (R : ℕ)
    {a : ℂ} (ha : 0<a.re) (b : Fin 4 → Bool) :
    Summable (fourDualBranchTerm p v R a b) := by
  have hs (h : ZMod p) := (summable_fourSeparatedDualGaussian ha (fourBranchShift p v b)
    (fourCongruenceModulation p (fun i => 3*(v i : ℤ)) h)).mul_left
      ((fourBranchWeight b : ℂ)*fourCongruenceGaussianPhase p (fun i => 3*(v i : ℤ))
        (fourBranchResidue v R b) (fourBranchShift p v b) h)
  exact summable_finite_outer (fourDualBranchTerm p v R a b) hs

theorem summable_fourRawGaussian (p : ℕ) [NeZero p] (v : Fin 4 → ℕ) (R : ℕ)
    (H : ℤ) (hv : (∑ i, (v i : ℤ)*(v i : ℤ))=(p : ℤ)*H)
    {a : ℂ} (ha : 0<a.re) :
    Summable (fun x => fourRawAmplitude p (fun i => (v i : ℤ)) R x *
      fourDualNormGaussian p a (fourDualPoint p (fun i => (v i : ℤ)) x)) := by
  classical
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hs := summable_sum (s := Finset.univ)
    (fun b _ => summable_fourDualBranchTerm p v R ha b)
  apply hs.congr
  intro x
  exact four_sum_poisson_branches p v R H hv a ha0 x

theorem four_progression_gaussian_eq_fourier (p : ℕ) [NeZero p] (v : Fin 4 → ℕ) (R : ℕ)
    (H : ℤ) (hv : (∑ i, (v i : ℤ)*(v i : ℤ))=(p : ℤ)*H)
    (t : ℝ) (ht : 0<t) :
    fourWatsonProgressionGaussian p v R t =
      (1/(p : ℂ))*(1/(t : ℂ)^(1/2 : ℂ))^4 *
        ∑' x, fourRawAmplitude p (fun i => (v i : ℤ)) R x *
          fourDualNormGaussian p (t : ℂ) (fourDualPoint p (fun i => (v i : ℤ)) x) := by
  classical
  have htC : 0<(t : ℂ).re := by simpa using ht
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  rw [four_progression_gaussian_poisson p v R t ht]
  have he (b : Fin 4 → Bool) :
      (∑ h : ZMod p, (fourBranchWeight b : ℂ)*
        fourCongruenceGaussianPhase p (fun i => 3*(v i : ℤ)) (fourBranchResidue v R b)
          (fourBranchShift p v b) h *
          ∑' z, fourSeparatedDualGaussian (t : ℂ) (fourBranchShift p v b)
            (fourCongruenceModulation p (fun i => 3*(v i : ℤ)) h) z) =
      ∑' x, fourDualBranchTerm p v R (t : ℂ) b x := by
    rw [(summable_fourDualBranchTerm p v R htC b).tsum_prod,tsum_fintype]
    simp only [fourDualBranchTerm,tsum_mul_left]
  simp_rw [he]
  rw [← Summable.tsum_finsetSum (fun b _ => summable_fourDualBranchTerm p v R htC b)]
  congr 1
  apply tsum_congr
  intro x
  exact four_sum_poisson_branches p v R H hv _ ht0 x

theorem four_persistent_vanishing_fourier_gaussian {p R : ℕ} [Fact p.Prime]
    {v : Fin 4 → ℕ} (hp2 : p ≠ 2) (hc : fourCanonical p v) (hR : R<p)
    (hz : PersistentFourVanishing p v R)
    (H : ℤ) (hv : (∑ i, (v i : ℤ)*(v i : ℤ))=(p : ℤ)*H)
    (t : ℝ) (ht : 0<t) :
    (∑' x, fourRawAmplitude p (fun i => (v i : ℤ)) R x *
      fourDualNormGaussian p (t : ℂ) (fourDualPoint p (fun i => (v i : ℤ)) x))=0 := by
  have hh := four_persistent_vanishing_primal_gaussian hp2 hc hR hz t
  rw [four_progression_gaussian_eq_fourier p v R H hv t ht] at hh
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  have hfactor : (1/(p : ℂ))*(1/(t : ℂ)^(1/2 : ℂ))^4 ≠ 0 := by
    exact mul_ne_zero (one_div_ne_zero hpC)
      (pow_ne_zero _ (one_div_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl htC))))
  exact (mul_eq_zero.mp hh).resolve_left hfactor

def fourNormDegree (p : ℕ) (v : Fin 4 → ℤ) (x : ZMod p × (Fin 4 → ℤ)) : ℕ :=
  (∑ i, fourDualPoint p v x i*fourDualPoint p v x i : ℤ).toNat

theorem fourDualNormGaussian_reparameterize (p : ℕ) [NeZero p] (v : Fin 4 → ℤ)
    (s : ℝ) (hs : 0<s) (x : ZMod p × (Fin 4 → ℤ)) :
    fourDualNormGaussian p ((Real.pi/((p : ℝ)^2*s) : ℝ) : ℂ) (fourDualPoint p v x) =
      (Real.exp (-s*(fourNormDegree p v x : ℝ)) : ℂ) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [fourDualNormGaussian,Complex.ofReal_exp]
  congr 1
  have hn : ((fourNormDegree p v x : ℕ) : ℤ)=
      ∑ i, fourDualPoint p v x i*fourDualPoint p v x i :=
    Int.toNat_of_nonneg (Finset.sum_nonneg (fun i _ => mul_self_nonneg _))
  have hnC := congrArg (fun z : ℤ => (z : ℂ)) hn
  push_cast at hnC ⊢
  rw [hnC]
  field_simp

theorem four_persistent_vanishing_fourier_shells {p R : ℕ} [Fact p.Prime]
    {v : Fin 4 → ℕ} (hp2 : p ≠ 2) (hc : fourCanonical p v) (hR : R<p)
    (hz : PersistentFourVanishing p v R)
    (H : ℤ) (hv : (∑ i, (v i : ℤ)*(v i : ℤ))=(p : ℤ)*H) :
    ∀ d : ℕ, (∑' x : (fourNormDegree p (fun i => (v i : ℤ))) ⁻¹' {d},
      fourRawAmplitude p (fun i => (v i : ℤ)) R x)=0 := by
  apply gaussian_fiber_sums_zero
  · intro s hs
    have ht : 0<Real.pi/((p : ℝ)^2*s) := div_pos Real.pi_pos
      (mul_pos (sq_pos_of_ne_zero (by exact_mod_cast (NeZero.ne p))) hs)
    have hh := summable_fourRawGaussian p v R H hv
      (a := ((Real.pi/((p : ℝ)^2*s) : ℝ) : ℂ)) ht
    simpa only [fourDualNormGaussian_reparameterize p _ s hs] using hh
  · intro s hs
    have ht : 0<Real.pi/((p : ℝ)^2*s) := div_pos Real.pi_pos
      (mul_pos (sq_pos_of_ne_zero (by exact_mod_cast (NeZero.ne p))) hs)
    simpa only [fourDualNormGaussian_reparameterize p _ s hs] using
      four_persistent_vanishing_fourier_gaussian hp2 hc hR hz H hv _ ht

end Ramanujan.MultiQuintuple
