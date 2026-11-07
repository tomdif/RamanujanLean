/-
# Coefficient vanishing forces cancellation on every actual Fourier shell
-/
import RamanujanTau.MultiQuintupleWatsonFourierAmplitude
import RamanujanTau.MultiQuintupleGaussianUniqueness

namespace Ramanujan.MultiQuintuple
open scoped BigOperators

noncomputable def watsonDualBranchTerm (p i j k R : ℕ) (a : ℂ)
    (b : TripleBranchBits) (x : ZMod p × TernaryIntPoint) : ℂ :=
  (tripleBranchWeight b : ℂ)*
    congruenceGaussianPhase p (3*i) (3*j) (3*k) (watsonBranchResidue i j k R b)
      (watsonBranchShift p i j k b) x.1 *
        separatedDualGaussian a (watsonBranchShift p i j k b)
          (congruenceModulation p (3*i) (3*j) (3*k) x.1) x.2

theorem summable_watsonDualBranchTerm (p i j k R : ℕ) [NeZero p]
    {a : ℂ} (ha : 0 < a.re) (b : TripleBranchBits) :
    Summable (watsonDualBranchTerm p i j k R a b) := by
  have hs (h : ZMod p) := (summable_separatedDualGaussian ha
    (watsonBranchShift p i j k b) (congruenceModulation p (3*i) (3*j) (3*k) h)).mul_left
      ((tripleBranchWeight b : ℂ)*congruenceGaussianPhase p (3*i) (3*j) (3*k)
        (watsonBranchResidue i j k R b) (watsonBranchShift p i j k b) h)
  exact summable_finite_outer _ hs

theorem summable_rawFourierGaussian (p i j k R : ℕ) [NeZero p]
    (hv : (p : ℤ) ∣ ternaryIntNorm (((i : ℤ),(j : ℤ)),(k : ℤ)))
    {a : ℂ} (ha : 0 < a.re) :
    Summable (fun x => rawFourierAmplitude p (((i : ℤ),(j : ℤ)),(k : ℤ)) R x *
      dualNormGaussian p a (fourierDualPoint p (((i : ℤ),(j : ℤ)),(k : ℤ)) x)) := by
  classical
  obtain ⟨H,hv⟩ := hv
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hs := summable_sum (s := Finset.univ)
    (fun b _ => summable_watsonDualBranchTerm p i j k R ha b)
  apply hs.congr
  intro x
  exact sum_watson_poisson_branch_terms p i j k R H hv a ha0 x

theorem watsonProgressionGaussian_eq_fourier (p i j k R : ℕ) [NeZero p]
    (hv : (p : ℤ) ∣ ternaryIntNorm (((i : ℤ),(j : ℤ)),(k : ℤ)))
    (t : ℝ) (ht : 0 < t) :
    watsonProgressionGaussian p i j k R t =
      (1/(p : ℂ))*(1/(t : ℂ)^(1/2 : ℂ))^3 *
        ∑' x, rawFourierAmplitude p (((i : ℤ),(j : ℤ)),(k : ℤ)) R x *
          dualNormGaussian p (t : ℂ) (fourierDualPoint p (((i : ℤ),(j : ℤ)),(k : ℤ)) x) := by
  classical
  obtain ⟨H,hv⟩ := hv
  have htC : 0 < (t : ℂ).re := by simpa using ht
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  rw [watsonProgressionGaussian_poisson p i j k R t ht]
  have he (b : TripleBranchBits) :
      (∑ h : ZMod p, (tripleBranchWeight b : ℂ)*
        congruenceGaussianPhase p (3*i) (3*j) (3*k) (watsonBranchResidue i j k R b)
          (watsonBranchShift p i j k b) h *
            ∑' y, separatedDualGaussian (t : ℂ) (watsonBranchShift p i j k b)
              (congruenceModulation p (3*i) (3*j) (3*k) h) y) =
      ∑' x, watsonDualBranchTerm p i j k R (t : ℂ) b x := by
    rw [(summable_watsonDualBranchTerm p i j k R htC b).tsum_prod,tsum_fintype]
    simp only [watsonDualBranchTerm,tsum_mul_left]
  simp_rw [he]
  rw [← Summable.tsum_finsetSum (fun b _ => summable_watsonDualBranchTerm p i j k R htC b)]
  congr 1
  apply tsum_congr
  intro x
  exact sum_watson_poisson_branch_terms p i j k R H hv _ ht0 x

theorem persistent_vanishing_fourier_gaussian {p i j k R : ℕ} [NeZero p]
    (ha : AdmissibleSparseTriple p i j k) (hR : R < p)
    (hzero : PersistentTripleVanishing p i j k R) (t : ℝ) (ht : 0 < t) :
    (∑' x, rawFourierAmplitude p (((i : ℤ),(j : ℤ)),(k : ℤ)) R x *
      dualNormGaussian p (t : ℂ) (fourierDualPoint p (((i : ℤ),(j : ℤ)),(k : ℤ)) x))=0 := by
  letI : Fact p.Prime := ⟨ha.1⟩
  have hh := persistent_vanishing_primal_gaussian ha hR hzero t
  rw [watsonProgressionGaussian_eq_fourier p i j k R ha.2.2.2.2.2.2 t ht] at hh
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast ha.1.ne_zero
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  have hc : (1/(p : ℂ))*(1/(t : ℂ)^(1/2 : ℂ))^3 ≠ 0 := by
    apply mul_ne_zero (one_div_ne_zero hpC)
    exact pow_ne_zero _ (one_div_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl htC)))
  exact (mul_eq_zero.mp hh).resolve_left hc

def fourierNormDegree (p : ℕ) (v : TernaryIntPoint) (x : ZMod p × TernaryIntPoint) : ℕ :=
  (ternaryIntNorm (fourierDualPoint p v x)).toNat

theorem dualNormGaussian_reparameterize (p : ℕ) [NeZero p] (v : TernaryIntPoint)
    (s : ℝ) (hs : 0 < s) (x : ZMod p × TernaryIntPoint) :
    dualNormGaussian p ((Real.pi/((p : ℝ)^2*s) : ℝ) : ℂ) (fourierDualPoint p v x) =
      (Real.exp (-s*(fourierNormDegree p v x : ℝ)) : ℂ) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [dualNormGaussian,Complex.ofReal_exp]
  congr 1
  have hn : ((fourierNormDegree p v x : ℕ) : ℤ)=ternaryIntNorm (fourierDualPoint p v x) :=
    Int.toNat_of_nonneg (ternaryIntNorm_nonneg _)
  have hnC := congrArg (fun z : ℤ => (z : ℂ)) hn
  push_cast at hnC ⊢
  rw [hnC]
  field_simp

theorem persistent_vanishing_fourier_shells {p i j k R : ℕ} [NeZero p]
    (ha : AdmissibleSparseTriple p i j k) (hR : R < p)
    (hzero : PersistentTripleVanishing p i j k R) :
    ∀ d : ℕ, (∑' x : (fourierNormDegree p (((i : ℤ),(j : ℤ)),(k : ℤ))) ⁻¹' {d},
      rawFourierAmplitude p (((i : ℤ),(j : ℤ)),(k : ℤ)) R x)=0 := by
  letI : Fact p.Prime := ⟨ha.1⟩
  apply gaussian_fiber_sums_zero
  · intro s hs
    have ht : 0 < Real.pi/((p : ℝ)^2*s) := div_pos Real.pi_pos (mul_pos (sq_pos_of_ne_zero
      (by exact_mod_cast ha.1.ne_zero)) hs)
    have hh := summable_rawFourierGaussian p i j k R ha.2.2.2.2.2.2
      (a := ((Real.pi/((p : ℝ)^2*s) : ℝ) : ℂ)) ht
    simpa only [dualNormGaussian_reparameterize p _ s hs] using hh
  · intro s hs
    have ht : 0 < Real.pi/((p : ℝ)^2*s) := div_pos Real.pi_pos (mul_pos (sq_pos_of_ne_zero
      (by exact_mod_cast ha.1.ne_zero)) hs)
    simpa only [dualNormGaussian_reparameterize p _ s hs] using
      persistent_vanishing_fourier_gaussian ha hR hzero _ ht

end Ramanujan.MultiQuintuple
