import RamanujanTau.MultiQuintupleFourGaussian
import RamanujanTau.MultiQuintupleFourFortyOne
import RamanujanTau.MultiQuintupleFourPlaneCoordinates
import RamanujanTau.MultiQuintuplePrimalGaussian

/-! Actual four-factor coefficient vanishings imply the primal Gaussian identity. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000

def fourCanonical (p : ℕ) (v : Fin 4 → ℕ) : Prop := ∀ i, 0<v i ∧ 2*v i<p

noncomputable def fourProduct (p : ℕ) (v : Fin 4 → ℕ) : PowerSeries ℤ :=
  quintupleSpecialized p (v 0)*quintupleSpecialized p (v 1)*
    quintupleSpecialized p (v 2)*quintupleSpecialized p (v 3)

def PersistentFourVanishing (p : ℕ) (v : Fin 4 → ℕ) (R : ℕ) : Prop :=
  ∀ N : ℕ, coeff (p*N+R) (fourProduct p v)=0

def quadIntegers (x : QuadQuintBranchIndex) : Fin 4 → ℤ :=
  ![quadN1 x,quadN2 x,quadN3 x,quadN4 x]

noncomputable def fourNaturalDegree (p : ℕ) (v : Fin 4 → ℕ) (x : QuadQuintBranchIndex) : ℕ :=
  ∑ i, quintExpHalf (quadBits x i) p (v i) (quadIntegers x i)

theorem four_exp_eq_degree {p : ℕ} {v : Fin 4 → ℕ} (hv : fourCanonical p v)
    (x : QuadQuintBranchIndex) :
    quadExp2 p (v 0) (v 1) (v 2) (v 3) x=2*(fourNaturalDegree p v x : ℤ) := by
  have hsum : quadExp2 p (v 0) (v 1) (v 2) (v 3) x =
      ∑ i : Fin 4, quintExp2 (quadBits x i) p (v i) (quadIntegers x i) := by
    simp [quadExp2,pointTripleExp2,tripleQuintExp2,quadBits,quadIntegers,
      quadN1,quadN2,quadN3,quadN4,quadB4,pointB1,pointB2,pointB3,
      pointN1,pointN2,pointN3,Fin.sum_univ_succ]
    ring
  rw [hsum,fourNaturalDegree,Nat.cast_sum,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ =>
    quintExp2_eq_two_mul_quintExpHalf _ _ _ _ (hv i).1 (hv i).2)

theorem four_degree_eq_iff {p : ℕ} {v : Fin 4 → ℕ} (hv : fourCanonical p v)
    (x : QuadQuintBranchIndex) (K : ℕ) :
    fourNaturalDegree p v x=K ↔ quadExp2 p (v 0) (v 1) (v 2) (v 3) x=2*(K : ℤ) := by
  rw [four_exp_eq_degree hv x]
  omega

theorem four_degree_fiber_weight_eq_coefficient {p : ℕ} {v : Fin 4 → ℕ}
    (hv : fourCanonical p v) (K : ℕ) :
    (∑' x : (fourNaturalDegree p v) ⁻¹' {K}, (quadWeight x : ℂ)) =
      ((coeff K (fourProduct p v) : ℤ) : ℂ) := by
  classical
  rw [tsum_subtype ((fourNaturalDegree p v) ⁻¹' {K})
    (fun x : QuadQuintBranchIndex => (quadWeight x : ℂ))]
  rw [tsum_eq_sum (s := quadBox K) (fun x hx => ?_)]
  · rw [fourProduct,coeff_quad_eq_finiteBox p (v 0) (v 1) (v 2) (v 3) K
      (hv 0).1 (hv 0).2 (hv 1).1 (hv 1).2 (hv 2).1 (hv 2).2 (hv 3).1 (hv 3).2]
    push_cast
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Set.indicator_apply,Set.mem_preimage,Set.mem_singleton_iff,quadContribution]
    by_cases hd : fourNaturalDegree p v x=K
    · simp [hd,(four_degree_eq_iff hv x K).mp hd]
    · simp [hd,((four_degree_eq_iff hv x K).not).mp hd]
  · simp only [Set.indicator_apply,Set.mem_preimage,Set.mem_singleton_iff]
    split_ifs with hd
    · exact False.elim (hx (mem_quadBox_of_exp p (v 0) (v 1) (v 2) (v 3) K x
        (hv 0).1 (hv 0).2 (hv 1).1 (hv 1).2 (hv 2).1 (hv 2).2 (hv 3).1 (hv 3).2
        ((four_degree_eq_iff hv x K).mp hd)))
    · rfl

theorem four_persistent_vanishing_weighted_sum {p R : ℕ} {v : Fin 4 → ℕ}
    (hv : fourCanonical p v) (hz : PersistentFourVanishing p v R) (g : ℕ → ℂ) :
    (∑' x : QuadQuintBranchIndex, if fourNaturalDegree p v x % p=R then
      (quadWeight x : ℂ)*g (fourNaturalDegree p v x) else 0)=0 := by
  classical
  apply tsum_zero_of_fiber_sums_zero _ (fourNaturalDegree p v)
  intro K
  have hf : ∀ x : (fourNaturalDegree p v) ⁻¹' {K}, fourNaturalDegree p v x=K :=
    fun x => x.property
  simp only [hf]
  by_cases hK : K%p=R
  · simp only [hK,if_true]
    rw [tsum_mul_right,four_degree_fiber_weight_eq_coefficient hv K]
    have hd : K=p*(K/p)+R := by have := Nat.mod_add_div K p; omega
    rw [hd,hz (K/p)]
    simp
  · simp [hK]

theorem four_degree_mod_iff_residue {p R : ℕ} [Fact p.Prime] {v : Fin 4 → ℕ}
    (hp2 : p ≠ 2) (hv : fourCanonical p v) (hR : R<p) (x : QuadQuintBranchIndex) :
    fourNaturalDegree p v x%p=R ↔
      (p : ℤ) ∣ quadResidue (v 0) (v 1) (v 2) (v 3) x-(R : ℤ) := by
  have hp : p.Prime := Fact.out
  have htwo : (2 : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 2 p).not.mpr
      (fun h => hp2 (Nat.dvd_prime (by decide : Nat.Prime 2) |>.mp h |>.resolve_left hp.ne_one))
  obtain ⟨u,hu⟩ := quadExp2_residue p (v 0) (v 1) (v 2) (v 3) x
  rw [four_exp_eq_degree hv x] at hu
  have hu' := congrArg (fun z : ℤ => (z : ZMod p)) hu
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat,ZMod.natCast_self,
    zero_mul,add_zero] at hu'
  have hdegree := mul_left_cancel₀ htwo hu'
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,Int.cast_natCast,sub_eq_zero,
    ← hdegree,ZMod.natCast_eq_natCast_iff]
  simp [Nat.ModEq,Nat.mod_eq_of_lt hR]

def fourThetaNorm (p : ℕ) (v : Fin 4 → ℕ) (x : QuadQuintBranchIndex) : ℤ :=
  ∑ i, (quintLatticeCoord (quadBits x i) p (v i) (quadIntegers x i))^2

def fourThetaOffset (p : ℕ) (v : Fin 4 → ℕ) : ℤ := ∑ i, (6*(v i : ℤ)-p)^2

theorem four_theta_norm_eq_degree {p : ℕ} {v : Fin 4 → ℕ}
    (hv : fourCanonical p v) (x : QuadQuintBranchIndex) :
    fourThetaNorm p v x=24*(p : ℤ)*(fourNaturalDegree p v x : ℤ)+fourThetaOffset p v := by
  simp only [fourThetaNorm,fourThetaOffset,fourNaturalDegree,Nat.cast_sum]
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := quintExp2_square_completion (quadBits x i) p (v i) (quadIntegers x i)
  rw [quintExp2_eq_two_mul_quintExpHalf _ _ _ _ (hv i).1 (hv i).2] at h
  linear_combination h.symm

noncomputable def fourWatsonProgressionGaussian (p : ℕ) (v : Fin 4 → ℕ) (R : ℕ) (t : ℝ) : ℂ := by
  classical
  exact ∑' x : QuadQuintBranchIndex,
    if (p : ℤ) ∣ quadResidue (v 0) (v 1) (v 2) (v 3) x-(R : ℤ) then
      (quadWeight x : ℂ)*Complex.exp (-Real.pi*(t : ℂ)*(fourThetaNorm p v x : ℂ)/(36*(p : ℂ)^2))
    else 0

theorem four_persistent_vanishing_primal_gaussian {p R : ℕ} [Fact p.Prime] {v : Fin 4 → ℕ}
    (hp2 : p ≠ 2) (hv : fourCanonical p v) (hR : R<p)
    (hz : PersistentFourVanishing p v R) (t : ℝ) :
    fourWatsonProgressionGaussian p v R t=0 := by
  classical
  have hh := four_persistent_vanishing_weighted_sum hv hz (fun K =>
    Complex.exp (-Real.pi*(t : ℂ)*((24*(p : ℤ)*K+fourThetaOffset p v : ℤ) : ℂ)/(36*(p : ℂ)^2)))
  convert hh using 1
  apply tsum_congr
  intro x
  simp only [four_degree_mod_iff_residue hp2 hv hR]
  split_ifs
  · rw [four_theta_norm_eq_degree hv x]
  · rfl

end Ramanujan.MultiQuintuple
