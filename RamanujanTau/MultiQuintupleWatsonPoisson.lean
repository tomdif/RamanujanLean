/-
# Applying congruence Poisson summation to the actual Watson branches
-/
import RamanujanTau.MultiQuintuplePrimalGaussian
import RamanujanTau.MultiQuintupleCongruencePoisson

namespace Ramanujan.MultiQuintuple
open scoped BigOperators

def assembleWatsonPoint (b : TripleBranchBits) (x : TernaryIntPoint) : TripleQuintBranchIndex :=
  (((b.1.1,x.1.1),(b.1.2,x.1.2)),(b.2,x.2))

def watsonBranchIndexEquiv : TripleBranchBits × TernaryIntPoint ≃ TripleQuintBranchIndex where
  toFun x := assembleWatsonPoint x.1 x.2
  invFun x := (pointBranchBits x,((pointN1 x,pointN2 x),pointN3 x))
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

noncomputable def watsonBranchShift (p i j k : ℕ) (b : TripleBranchBits) : TernaryComplexPoint :=
  ((((i : ℂ)/p+(branchSign b.1.1 : ℂ)/6),((j : ℂ)/p+(branchSign b.1.2 : ℂ)/6)),
    (k : ℂ)/p+(branchSign b.2 : ℂ)/6)

def watsonBranchResidue (i j k R : ℕ) (b : TripleBranchBits) : ℤ :=
  (R : ℤ)-(i : ℤ)*(if b.1.1 then 1 else 0)-(j : ℤ)*(if b.1.2 then 1 else 0)-
    (k : ℤ)*(if b.2 then 1 else 0)

theorem assembled_watson_residue (p i j k R : ℕ) (b : TripleBranchBits) (x : TernaryIntPoint) :
    InThetaResidueFiber p i j k R (assembleWatsonPoint b x) ↔
      (p : ℤ) ∣ 3*(i : ℤ)*x.1.1+3*(j : ℤ)*x.1.2+3*(k : ℤ)*x.2-watsonBranchResidue i j k R b := by
  have he : pointLinearResidue i j k (assembleWatsonPoint b x)-(R : ℤ) =
      3*(i : ℤ)*x.1.1+3*(j : ℤ)*x.1.2+3*(k : ℤ)*x.2-watsonBranchResidue i j k R b := by
    rcases b with ⟨⟨b1,b2⟩,b3⟩
    cases b1 <;> cases b2 <;> cases b3 <;>
      simp [pointLinearResidue,tripleLinearResidue,assembleWatsonPoint,pointB1,pointB2,pointB3,
      pointN1,pointN2,pointN3,watsonBranchResidue] <;> ring
  rw [← he]
  constructor
  · rintro ⟨q,hq⟩
    exact ⟨q,by omega⟩
  · rintro ⟨q,hq⟩
    exact ⟨q,by omega⟩

theorem assembled_watson_gaussian (p i j k : ℕ) (hp : p ≠ 0)
    (a : ℂ) (b : TripleBranchBits) (x : TernaryIntPoint) :
    Complex.exp (-Real.pi*a*(pointThetaNorm p i j k (assembleWatsonPoint b x) : ℂ)/(36*(p : ℂ)^2)) =
      separatedGaussian a (watsonBranchShift p i j k b) 0 x := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  unfold separatedGaussian shiftedGaussian watsonBranchShift
  simp only [Prod.fst_zero,Prod.snd_zero,mul_zero,zero_mul,add_zero]
  repeat rw [← Complex.exp_add]
  congr 1
  simp only [pointThetaNorm,pointCoord1,pointCoord2,pointCoord3,assembleWatsonPoint,
    pointB1,pointB2,pointB3,pointN1,pointN2,pointN3,
    quintLatticeCoord_eq_cosetBase_add_period,ternaryNorm]
  push_cast
  field_simp
  ring

theorem summable_finite_outer {ι κ : Type*} [Fintype ι] (f : ι × κ → ℂ)
    (hf : ∀ i, Summable (fun k => f (i,k))) : Summable f := by
  apply summable_norm_iff.mp
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  exact ⟨fun i => (hf i).norm,(hasSum_fintype _).summable⟩

noncomputable def watsonBranchGaussianTerm (p i j k R : ℕ) (a : ℂ)
    (b : TripleBranchBits) (x : TernaryIntPoint) : ℂ := by
  classical
  exact (tripleBranchWeight b : ℂ) *
    if (p : ℤ) ∣ 3*(i : ℤ)*x.1.1+3*(j : ℤ)*x.1.2+3*(k : ℤ)*x.2-watsonBranchResidue i j k R b
      then separatedGaussian a (watsonBranchShift p i j k b) 0 x else 0

theorem summable_watsonBranchGaussianTerm (p i j k R : ℕ) {a : ℂ} (ha : 0 < a.re)
    (b : TripleBranchBits) : Summable (watsonBranchGaussianTerm p i j k R a b) := by
  classical
  have hs := (summable_separatedGaussian ha (watsonBranchShift p i j k b) 0).indicator
    {x | (p : ℤ) ∣ 3*(i : ℤ)*x.1.1+3*(j : ℤ)*x.1.2+3*(k : ℤ)*x.2-watsonBranchResidue i j k R b}
  simpa only [watsonBranchGaussianTerm,Set.indicator_apply,Set.mem_setOf_eq] using
    hs.mul_left (tripleBranchWeight b : ℂ)

theorem watsonProgressionGaussian_eq_branches (p i j k R : ℕ) (hp : p ≠ 0)
    (t : ℝ) (ht : 0 < t) :
    watsonProgressionGaussian p i j k R t =
      ∑ b : TripleBranchBits, ∑' x : TernaryIntPoint, watsonBranchGaussianTerm p i j k R (t : ℂ) b x := by
  classical
  unfold watsonProgressionGaussian
  rw [← watsonBranchIndexEquiv.tsum_eq]
  have he : (fun x : TripleBranchBits × TernaryIntPoint =>
      if InThetaResidueFiber p i j k R (watsonBranchIndexEquiv x) then
        (pointBranchWeight (watsonBranchIndexEquiv x) : ℂ)*Complex.exp
          (-Real.pi*(t : ℂ)*(pointThetaNorm p i j k (watsonBranchIndexEquiv x) : ℂ)/(36*(p : ℂ)^2)) else 0) =
      (fun x : TripleBranchBits × TernaryIntPoint => watsonBranchGaussianTerm p i j k R (t : ℂ) x.1 x.2) := by
    funext x
    change (if InThetaResidueFiber p i j k R (assembleWatsonPoint x.1 x.2) then
      (pointBranchWeight (assembleWatsonPoint x.1 x.2) : ℂ)*Complex.exp
        (-Real.pi*(t : ℂ)*(pointThetaNorm p i j k (assembleWatsonPoint x.1 x.2) : ℂ)/(36*(p : ℂ)^2)) else 0) = _
    simp only [assembled_watson_residue,assembled_watson_gaussian p i j k hp,
      watsonBranchGaussianTerm,mul_ite,mul_zero]
    rfl
  have hsb (b : TripleBranchBits) := summable_watsonBranchGaussianTerm p i j k R
    (by simpa using ht : 0 < (t : ℂ).re) b
  have hs := summable_finite_outer
    (fun x : TripleBranchBits × TernaryIntPoint => watsonBranchGaussianTerm p i j k R (t : ℂ) x.1 x.2) hsb
  rw [he,hs.tsum_prod,tsum_fintype]

/-- The exact Gaussian identity for the product is transported through
Poisson summation, including all eight branch signs and residue phases. -/
theorem watsonProgressionGaussian_poisson (p i j k R : ℕ) [NeZero p]
    (t : ℝ) (ht : 0 < t) :
    watsonProgressionGaussian p i j k R t =
      (1/(p : ℂ))*(1/(t : ℂ)^(1/2 : ℂ))^3 *
      ∑ b : TripleBranchBits, ∑ h : ZMod p, (tripleBranchWeight b : ℂ)*
        congruenceGaussianPhase p (3*i) (3*j) (3*k) (watsonBranchResidue i j k R b)
          (watsonBranchShift p i j k b) h *
            ∑' y : TernaryIntPoint,
              separatedDualGaussian (t : ℂ) (watsonBranchShift p i j k b)
                (congruenceModulation p (3*i) (3*j) (3*k) h) y := by
  classical
  rw [watsonProgressionGaussian_eq_branches p i j k R (NeZero.ne p) t ht]
  simp only [watsonBranchGaussianTerm,tsum_mul_left]
  simp_rw [congruence_gaussian_poisson p (3*(i : ℤ)) (3*(j : ℤ)) (3*(k : ℤ))
    _ (by simpa using ht : 0 < (t : ℂ).re)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro h _
  ring

end Ramanujan.MultiQuintuple
