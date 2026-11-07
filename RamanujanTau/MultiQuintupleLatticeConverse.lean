/-
# Short projective roots from congruence-lattice preservation

The primitive-normal arguments from MultiQuintupleThetaArithmetic only need
preservation of the integral congruence lattice. This file establishes that
generalization, so the dual construction can use the arithmetic extraction
without first supplying a coherent involution of Watson branch points.
-/
import RamanujanTau.MultiQuintupleDualLattice

namespace Ramanujan.MultiQuintuple

structure CongruenceLatticeInvolution (p i j k : ℕ)
    extends RationalTernaryOrthogonalInvolution where
  maps_lattice : ∀ x : TernaryIntIndex, InThetaIndexLattice p i j k x →
    ∃ y : TernaryIntIndex, InThetaIndexLattice p i j k y ∧
      linear (ternaryIntIndexToRat x) = ternaryIntIndexToRat y

def CongruenceLatticeInvolution.ofProjective
    (p i j k : ℕ) (hp : p ≠ 0) (T : RationalTernaryOrthogonalInvolution)
    (hN : ∀ w ∈ projectiveDualLattice p (((i : ℤ),(j : ℤ)),(k : ℤ)),
      ∃ z ∈ projectiveDualLattice p (((i : ℤ),(j : ℤ)),(k : ℤ)),
        T.linear (ternaryIntIndexToRat w) = ternaryIntIndexToRat z) :
    CongruenceLatticeInvolution p i j k where
  toRationalTernaryOrthogonalInvolution := T
  maps_lattice := by
    intro x hx
    have hx' : x ∈ congruenceLattice p (((i : ℤ),(j : ℤ)),(k : ℤ)) := by
      simpa [congruenceLattice, InThetaIndexLattice, affineIndexDot,
        ternaryIntDot, ternaryDot] using hx
    obtain ⟨y,hy,hmap⟩ := T.preserves_congruence_of_projective p hp _ hN x hx'
    refine ⟨y,?_,hmap⟩
    simpa [congruenceLattice, InThetaIndexLattice, affineIndexDot,
      ternaryIntDot, ternaryDot] using hy

theorem CongruenceLatticeInvolution.exists_householder_or_neg_householder
    {p i j k : ℕ} (T : CongruenceLatticeInvolution p i j k) :
    (∃ w : TernaryRatPoint, w ≠ 0 ∧
      IsThetaAntiFixed T.toRationalTernaryOrthogonalInvolution w ∧
      ∀ x, T.linear x = ternaryRatHouseholder w x) ∨
    (∃ w : TernaryRatPoint, w ≠ 0 ∧
      IsThetaFixed T.toRationalTernaryOrthogonalInvolution w ∧
      ∀ x, T.linear x = -ternaryRatHouseholder w x) :=
  T.toRationalTernaryOrthogonalInvolution.exists_householder_or_neg_householder

theorem CongruenceLatticeInvolution.exists_integral_householder_or_neg_householder
    {p i j k : ℕ} (T : CongruenceLatticeInvolution p i j k) :
    (∃ W : TernaryIntIndex, W ≠ 0 ∧
      ∀ x, T.linear x =
        ternaryRatHouseholder (ternaryIntIndexToRat W) x) ∨
    (∃ W : TernaryIntIndex, W ≠ 0 ∧
      ∀ x, T.linear x =
        -ternaryRatHouseholder (ternaryIntIndexToRat W) x) := by
  rcases T.exists_householder_or_neg_householder with hpositive | hnegative
  · obtain ⟨w, hw, hwanti, hT⟩ := hpositive
    obtain ⟨W, hW, hscale⟩ :=
      exists_integral_normal_for_ternaryRatHouseholder w hw
    exact Or.inl ⟨W, hW, fun x => (hT x).trans (hscale x)⟩
  · obtain ⟨w, hw, hwfixed, hT⟩ := hnegative
    obtain ⟨W, hW, hscale⟩ :=
      exists_integral_normal_for_ternaryRatHouseholder w hw
    exact Or.inr ⟨W, hW, fun x =>
      (hT x).trans (congrArg Neg.neg (hscale x))⟩

theorem CongruenceLatticeInvolution.exists_primitive_integral_householder_or_neg
    {p i j k : ℕ} (T : CongruenceLatticeInvolution p i j k) :
    (∃ w : TernaryIntIndex, w ≠ 0 ∧
      ∃ b1 b2 b3 : ℤ,
        b1 * w.1.1 ^ 2 + b2 * w.1.2 ^ 2 + b3 * w.2 ^ 2 = 1 ∧
        ∀ x, T.linear x =
          ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
    (∃ w : TernaryIntIndex, w ≠ 0 ∧
      ∃ b1 b2 b3 : ℤ,
        b1 * w.1.1 ^ 2 + b2 * w.1.2 ^ 2 + b3 * w.2 ^ 2 = 1 ∧
        ∀ x, T.linear x =
          -ternaryRatHouseholder (ternaryIntIndexToRat w) x) := by
  rcases T.exists_integral_householder_or_neg_householder with
    hpositive | hnegative
  · obtain ⟨W, hW, hT⟩ := hpositive
    obtain ⟨g, hg, w, hscale, b1, b2, b3, hsquare⟩ :=
      exists_primitive_ternary_rescaling_with_square_bezout W hW
    have hw : w ≠ 0 := by
      intro hwzero
      apply hW
      rw [hscale, hwzero]
      simp [ternaryIntScale]
    have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    have hnormal : ∀ x,
        ternaryRatHouseholder (ternaryIntIndexToRat W) x =
          ternaryRatHouseholder (ternaryIntIndexToRat w) x := by
      intro x
      rw [hscale, ternaryIntIndexToRat_scale]
      exact ternaryRatHouseholder_smul_normal (g : ℚ) hgq
        (ternaryIntIndexToRat w)
        (by
          intro hzero
          apply hw
          apply ternaryIntIndexToRat_injective
          simpa using hzero) x
    exact Or.inl ⟨w, hw, b1, b2, b3, hsquare,
      fun x => (hT x).trans (hnormal x)⟩
  · obtain ⟨W, hW, hT⟩ := hnegative
    obtain ⟨g, hg, w, hscale, b1, b2, b3, hsquare⟩ :=
      exists_primitive_ternary_rescaling_with_square_bezout W hW
    have hw : w ≠ 0 := by
      intro hwzero
      apply hW
      rw [hscale, hwzero]
      simp [ternaryIntScale]
    have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    have hnormal : ∀ x,
        ternaryRatHouseholder (ternaryIntIndexToRat W) x =
          ternaryRatHouseholder (ternaryIntIndexToRat w) x := by
      intro x
      rw [hscale, ternaryIntIndexToRat_scale]
      exact ternaryRatHouseholder_smul_normal (g : ℚ) hgq
        (ternaryIntIndexToRat w)
        (by
          intro hzero
          apply hw
          apply ternaryIntIndexToRat_injective
          simpa using hzero) x
    exact Or.inr ⟨w, hw, b1, b2, b3, hsquare,
      fun x => (hT x).trans (congrArg Neg.neg (hnormal x))⟩

theorem CongruenceLatticeInvolution.exists_integral_images_of_p_basis
    {p i j k : ℕ} (T : CongruenceLatticeInvolution p i j k)
    :
    (∃ y1 : TernaryIntIndex,
      T.linear (ternaryIntIndexToRat (ternaryIntScale p thetaIndexBasis1)) =
        ternaryIntIndexToRat y1) ∧
    (∃ y2 : TernaryIntIndex,
      T.linear (ternaryIntIndexToRat (ternaryIntScale p thetaIndexBasis2)) =
        ternaryIntIndexToRat y2) ∧
    (∃ y3 : TernaryIntIndex,
      T.linear (ternaryIntIndexToRat (ternaryIntScale p thetaIndexBasis3)) =
        ternaryIntIndexToRat y3) := by
  obtain ⟨y1, hy1, hmap1⟩ := T.maps_lattice
    (ternaryIntScale p thetaIndexBasis1) (p_basis1_mem_thetaIndexLattice p i j k)
  obtain ⟨y2, hy2, hmap2⟩ := T.maps_lattice
    (ternaryIntScale p thetaIndexBasis2) (p_basis2_mem_thetaIndexLattice p i j k)
  obtain ⟨y3, hy3, hmap3⟩ := T.maps_lattice
    (ternaryIntScale p thetaIndexBasis3) (p_basis3_mem_thetaIndexLattice p i j k)
  exact ⟨⟨y1, hmap1⟩, ⟨y2, hmap2⟩, ⟨y3, hmap3⟩⟩

theorem CongruenceLatticeInvolution.primitive_householder_norm_cases
    {p i j k : ℕ} (T : CongruenceLatticeInvolution p i j k)
    (hadmissible : AdmissibleSparseTriple p i j k)
    (w : TernaryIntIndex) (hw : w ≠ 0) (b1 b2 b3 : ℤ)
    (hprimitive :
      b1 * w.1.1 ^ 2 + b2 * w.1.2 ^ 2 + b3 * w.2 ^ 2 = 1)
    (hT : (∀ x, T.linear x =
        ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
      (∀ x, T.linear x =
        -ternaryRatHouseholder (ternaryIntIndexToRat w) x)) :
    ternaryNorm w.1.1 w.1.2 w.2 = 1 ∨
      ternaryNorm w.1.1 w.1.2 w.2 = 2 ∨
      ternaryNorm w.1.1 w.1.2 w.2 = p ∨
      ternaryNorm w.1.1 w.1.2 w.2 = 2 * p := by
  obtain ⟨⟨y1, hmap1⟩, ⟨y2, hmap2⟩, ⟨y3, hmap3⟩⟩ :=
    T.exists_integral_images_of_p_basis
  obtain ⟨z1, z2, z3, hh1, hh2, hh3⟩ :
      ∃ z1 z2 z3 : TernaryIntIndex,
        ternaryRatHouseholder (ternaryIntIndexToRat w)
            (ternaryIntIndexToRat (ternaryIntScale p thetaIndexBasis1)) =
          ternaryIntIndexToRat z1 ∧
        ternaryRatHouseholder (ternaryIntIndexToRat w)
            (ternaryIntIndexToRat (ternaryIntScale p thetaIndexBasis2)) =
          ternaryIntIndexToRat z2 ∧
        ternaryRatHouseholder (ternaryIntIndexToRat w)
            (ternaryIntIndexToRat (ternaryIntScale p thetaIndexBasis3)) =
          ternaryIntIndexToRat z3 := by
    rcases hT with hpositive | hnegative
    · exact ⟨y1, y2, y3,
        (hpositive _).symm.trans hmap1,
        (hpositive _).symm.trans hmap2,
        (hpositive _).symm.trans hmap3⟩
    · have hneg1 := congrArg Neg.neg ((hnegative _).symm.trans hmap1)
      have hneg2 := congrArg Neg.neg ((hnegative _).symm.trans hmap2)
      have hneg3 := congrArg Neg.neg ((hnegative _).symm.trans hmap3)
      exact ⟨-y1, -y2, -y3,
        by simpa [ternaryIntIndexToRat] using hneg1,
        by simpa [ternaryIntIndexToRat] using hneg2,
        by simpa [ternaryIntIndexToRat] using hneg3⟩
  have hdiv1 := householder_integral_p_basis1_norm_dvd p w z1 hw hh1
  have hdiv2 := householder_integral_p_basis2_norm_dvd p w z2 hw hh2
  have hdiv3 := householder_integral_p_basis3_norm_dvd p w z3 hw hh3
  have hcast_ne : ternaryIntIndexToRat w ≠ 0 := by
    intro hzero
    apply hw
    apply ternaryIntIndexToRat_injective
    simpa using hzero
  have hnormpos : 0 < ternaryNorm w.1.1 w.1.2 w.2 := by
    have hqpos := ternaryRatNorm_pos hcast_ne
    rw [ternaryRatNorm_intIndexToRat] at hqpos
    exact_mod_cast hqpos
  let n : ℕ := (ternaryNorm w.1.1 w.1.2 w.2).toNat
  have hnormn : ternaryNorm w.1.1 w.1.2 w.2 = (n : ℤ) := by
    exact (Int.toNat_of_nonneg (le_of_lt hnormpos)).symm
  have hn_dvd : n ∣ 2 * p := by
    apply primitive_reflection_norm_dvd_two_mul p n
      w.1.1 w.1.2 w.2 b1 b2 b3 hprimitive
    · simpa [hnormn] using hdiv1
    · simpa [hnormn] using hdiv2
    · simpa [hnormn] using hdiv3
  rcases hadmissible with ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩
  rcases eq_one_or_two_or_prime_or_two_prime_of_dvd hp hn_dvd with
    hn | hn | hn | hn
  · exact Or.inl (by rw [hnormn, hn]; norm_num)
  · exact Or.inr (Or.inl (by rw [hnormn, hn]; norm_num))
  · exact Or.inr (Or.inr (Or.inl (by rw [hnormn, hn])))
  · exact Or.inr (Or.inr (Or.inr (by
      calc
        ternaryNorm w.1.1 w.1.2 w.2 = (n : ℤ) := hnormn
        _ = ((2 * p : ℕ) : ℤ) := by exact_mod_cast hn
        _ = 2 * (p : ℤ) := by push_cast; rfl)))

set_option maxHeartbeats 1000000 in
theorem CongruenceLatticeInvolution.primitive_householder_norm_ne_one_two
    {p i j k : ℕ} (T : CongruenceLatticeInvolution p i j k)
    (hadmissible : AdmissibleSparseTriple p i j k)
    (w : TernaryIntIndex)
    (hT : (∀ x, T.linear x =
        ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
      (∀ x, T.linear x =
        -ternaryRatHouseholder (ternaryIntIndexToRat w) x)) :
    ternaryNorm w.1.1 w.1.2 w.2 ≠ 1 ∧
      ternaryNorm w.1.1 w.1.2 w.2 ≠ 2 := by
  rcases hadmissible with ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩
  have hj : 0 < j := by omega
  have hk : 0 < k := by omega
  have hip : i < p := by omega
  have hjp : j < p := by omega
  have hkp : k < p := by omega
  have hp2 : 2 < p := by omega
  have hnot12prod : ¬(p : ℤ) ∣ 2 * (i : ℤ) * (j : ℤ) :=
    prime_not_dvd_two_mul_of_lt hp hi hj hip hjp hp2
  have hnot13prod : ¬(p : ℤ) ∣ 2 * (i : ℤ) * (k : ℤ) :=
    prime_not_dvd_two_mul_of_lt hp hi hk hip hkp hp2
  have hnot23prod : ¬(p : ℤ) ∣ 2 * (j : ℤ) * (k : ℤ) :=
    prime_not_dvd_two_mul_of_lt hp hj hk hjp hkp hp2
  have hnot12diff : ¬(p : ℤ) ∣ (j : ℤ) ^ 2 - (i : ℤ) ^ 2 :=
    prime_not_dvd_square_sub_square_of_canonical hp hi hij (by omega)
  have hik : i < k := by omega
  have hnot13diff : ¬(p : ℤ) ∣ (k : ℤ) ^ 2 - (i : ℤ) ^ 2 :=
    prime_not_dvd_square_sub_square_of_canonical hp hi hik hpk
  have hnot23diff : ¬(p : ℤ) ∣ (k : ℤ) ^ 2 - (j : ℤ) ^ 2 :=
    prime_not_dvd_square_sub_square_of_canonical hp hj hjk hpk
  let d12 : TernaryIntIndex := (((j : ℤ), -(i : ℤ)), 0)
  let d13 : TernaryIntIndex := (((k : ℤ), 0), -(i : ℤ))
  let d23 : TernaryIntIndex := ((0, (k : ℤ)), -(j : ℤ))
  have hd12 : InThetaIndexLattice p i j k d12 := by
    refine ⟨0, ?_⟩
    simp [d12, affineIndexDot]
    ring
  have hd13 : InThetaIndexLattice p i j k d13 := by
    refine ⟨0, ?_⟩
    simp [d13, affineIndexDot]
    ring
  have hd23 : InThetaIndexLattice p i j k d23 := by
    refine ⟨0, ?_⟩
    simp [d23, affineIndexDot]
    ring
  obtain ⟨z12, ⟨q12, hq12⟩, hmap12⟩ :=
    T.maps_lattice d12 hd12
  obtain ⟨z13, ⟨q13, hq13⟩, hmap13⟩ :=
    T.maps_lattice d13 hd13
  obtain ⟨z23, ⟨q23, hq23⟩, hmap23⟩ :=
    T.maps_lattice d23 hd23
  have hdot12 :
      (i : ℚ) * (T.linear (ternaryIntIndexToRat d12)).1.1 +
          (j : ℚ) * (T.linear (ternaryIntIndexToRat d12)).1.2 +
          (k : ℚ) * (T.linear (ternaryIntIndexToRat d12)).2 =
        (p : ℚ) * (q12 : ℚ) := by
    rw [hmap12]
    simp only [ternaryIntIndexToRat]
    exact_mod_cast hq12
  have hdot13 :
      (i : ℚ) * (T.linear (ternaryIntIndexToRat d13)).1.1 +
          (j : ℚ) * (T.linear (ternaryIntIndexToRat d13)).1.2 +
          (k : ℚ) * (T.linear (ternaryIntIndexToRat d13)).2 =
        (p : ℚ) * (q13 : ℚ) := by
    rw [hmap13]
    simp only [ternaryIntIndexToRat]
    exact_mod_cast hq13
  have hdot23 :
      (i : ℚ) * (T.linear (ternaryIntIndexToRat d23)).1.1 +
          (j : ℚ) * (T.linear (ternaryIntIndexToRat d23)).1.2 +
          (k : ℚ) * (T.linear (ternaryIntIndexToRat d23)).2 =
        (p : ℚ) * (q23 : ℚ) := by
    rw [hmap23]
    simp only [ternaryIntIndexToRat]
    exact_mod_cast hq23
  rcases w with ⟨⟨w1, w2⟩, w3⟩
  have hsmall_impossible :
      ternaryNorm w1 w2 w3 = 1 ∨ ternaryNorm w1 w2 w3 = 2 → False := by
    intro hsmall
    have hsquares : w1 ^ 2 + w2 ^ 2 + w3 ^ 2 ≤ 2 := by
      rcases hsmall with hnorm | hnorm <;>
        simp only [ternaryNorm] at hnorm <;> omega
    have hw1lo : -2 < w1 := by nlinarith [sq_nonneg w2, sq_nonneg w3]
    have hw1hi : w1 < 2 := by nlinarith [sq_nonneg w2, sq_nonneg w3]
    have hw2lo : -2 < w2 := by nlinarith [sq_nonneg w1, sq_nonneg w3]
    have hw2hi : w2 < 2 := by nlinarith [sq_nonneg w1, sq_nonneg w3]
    have hw3lo : -2 < w3 := by nlinarith [sq_nonneg w1, sq_nonneg w2]
    have hw3hi : w3 < 2 := by nlinarith [sq_nonneg w1, sq_nonneg w2]
    have hsupport :
        (w2 = 0 ∧ w3 = 0 ∧ ternaryNorm w1 w2 w3 = 1) ∨
        (w1 = 0 ∧ w3 = 0 ∧ ternaryNorm w1 w2 w3 = 1) ∨
        (w1 = 0 ∧ w2 = 0 ∧ ternaryNorm w1 w2 w3 = 1) ∨
        (w3 = 0 ∧ ternaryNorm w1 w2 w3 = 2) ∨
        (w2 = 0 ∧ ternaryNorm w1 w2 w3 = 2) ∨
        (w1 = 0 ∧ ternaryNorm w1 w2 w3 = 2) := by
      interval_cases w1 <;> interval_cases w2 <;> interval_cases w3
      all_goals norm_num [ternaryNorm] at hsmall
      all_goals norm_num [ternaryNorm]
    obtain ⟨r12, r13, r23, hHdot12, hHdot13, hHdot23⟩ :
        ∃ r12 r13 r23 : ℤ,
          (i : ℚ) * (ternaryRatHouseholder
              (ternaryIntIndexToRat ((w1, w2), w3))
              (ternaryIntIndexToRat d12)).1.1 +
              (j : ℚ) * (ternaryRatHouseholder
                (ternaryIntIndexToRat ((w1, w2), w3))
                (ternaryIntIndexToRat d12)).1.2 +
              (k : ℚ) * (ternaryRatHouseholder
                (ternaryIntIndexToRat ((w1, w2), w3))
                (ternaryIntIndexToRat d12)).2 = (p : ℚ) * r12 ∧
          (i : ℚ) * (ternaryRatHouseholder
              (ternaryIntIndexToRat ((w1, w2), w3))
              (ternaryIntIndexToRat d13)).1.1 +
              (j : ℚ) * (ternaryRatHouseholder
                (ternaryIntIndexToRat ((w1, w2), w3))
                (ternaryIntIndexToRat d13)).1.2 +
              (k : ℚ) * (ternaryRatHouseholder
                (ternaryIntIndexToRat ((w1, w2), w3))
                (ternaryIntIndexToRat d13)).2 = (p : ℚ) * r13 ∧
          (i : ℚ) * (ternaryRatHouseholder
              (ternaryIntIndexToRat ((w1, w2), w3))
              (ternaryIntIndexToRat d23)).1.1 +
              (j : ℚ) * (ternaryRatHouseholder
                (ternaryIntIndexToRat ((w1, w2), w3))
                (ternaryIntIndexToRat d23)).1.2 +
              (k : ℚ) * (ternaryRatHouseholder
                (ternaryIntIndexToRat ((w1, w2), w3))
                (ternaryIntIndexToRat d23)).2 = (p : ℚ) * r23 := by
      rcases hT with hpositive | hnegative
      · exact ⟨q12, q13, q23,
          by simpa only [hpositive] using hdot12,
          by simpa only [hpositive] using hdot13,
          by simpa only [hpositive] using hdot23⟩
      · rw [hnegative] at hdot12 hdot13 hdot23
        refine ⟨-q12, -q13, -q23, ?_, ?_, ?_⟩ <;>
          simp at hdot12 hdot13 hdot23 ⊢ <;> nlinarith
    rcases hsupport with haxis1 | haxis2 | haxis3 | hpair12 | hpair13 | hpair23
    · rcases haxis1 with ⟨rfl, rfl, hnorm⟩
      interval_cases w1 <;> norm_num [ternaryNorm] at hnorm <;>
        norm_num [d12, ternaryRatHouseholder, ternaryIntIndexToRat,
          ternaryRatDot, ternaryRatNorm] at hHdot12 <;>
        apply hnot12prod <;>
        apply int_dvd_of_rat_eq_mul_or_neg (p : ℤ)
          (2 * (i : ℤ) * (j : ℤ)) r12 <;>
        first
        | left; push_cast; nlinarith only [hHdot12]
        | right; push_cast; nlinarith only [hHdot12]
    · rcases haxis2 with ⟨rfl, rfl, hnorm⟩
      interval_cases w2 <;> norm_num [ternaryNorm] at hnorm <;>
        norm_num [d12, ternaryRatHouseholder, ternaryIntIndexToRat,
          ternaryRatDot, ternaryRatNorm] at hHdot12 <;>
        apply hnot12prod <;>
        apply int_dvd_of_rat_eq_mul_or_neg (p : ℤ)
          (2 * (i : ℤ) * (j : ℤ)) r12 <;>
        left <;> push_cast <;> nlinarith only [hHdot12]
    · rcases haxis3 with ⟨rfl, rfl, hnorm⟩
      interval_cases w3 <;> norm_num [ternaryNorm] at hnorm <;>
        norm_num [d13, ternaryRatHouseholder, ternaryIntIndexToRat,
          ternaryRatDot, ternaryRatNorm] at hHdot13 <;>
        apply hnot13prod <;>
        apply int_dvd_of_rat_eq_mul_or_neg (p : ℤ)
          (2 * (i : ℤ) * (k : ℤ)) r13 <;>
        left <;> push_cast <;> nlinarith only [hHdot13]
    · rcases hpair12 with ⟨rfl, hnorm⟩
      interval_cases w1 <;> interval_cases w2 <;>
        norm_num [ternaryNorm] at hnorm <;>
        norm_num [d12, ternaryRatHouseholder, ternaryIntIndexToRat,
          ternaryRatDot, ternaryRatNorm] at hHdot12 <;>
        apply hnot12diff <;>
        apply int_dvd_of_rat_eq_mul_or_neg (p : ℤ)
          ((j : ℤ) ^ 2 - (i : ℤ) ^ 2) r12 <;>
        first
        | left; push_cast; nlinarith only [hHdot12]
        | right; push_cast; nlinarith only [hHdot12]
    · rcases hpair13 with ⟨rfl, hnorm⟩
      interval_cases w1 <;> interval_cases w3 <;>
        norm_num [ternaryNorm] at hnorm <;>
        norm_num [d13, ternaryRatHouseholder, ternaryIntIndexToRat,
          ternaryRatDot, ternaryRatNorm] at hHdot13 <;>
        apply hnot13diff <;>
        apply int_dvd_of_rat_eq_mul_or_neg (p : ℤ)
          ((k : ℤ) ^ 2 - (i : ℤ) ^ 2) r13 <;>
        first
        | left; push_cast; nlinarith only [hHdot13]
        | right; push_cast; nlinarith only [hHdot13]
    · rcases hpair23 with ⟨rfl, hnorm⟩
      interval_cases w2 <;> interval_cases w3 <;>
        norm_num [ternaryNorm] at hnorm <;>
        norm_num [d23, ternaryRatHouseholder, ternaryIntIndexToRat,
          ternaryRatDot, ternaryRatNorm] at hHdot23 <;>
        apply hnot23diff <;>
        apply int_dvd_of_rat_eq_mul_or_neg (p : ℤ)
          ((k : ℤ) ^ 2 - (j : ℤ) ^ 2) r23 <;>
        first
        | left; push_cast; nlinarith only [hHdot23]
        | right; push_cast; nlinarith only [hHdot23]
  constructor
  · intro hnorm
    exact hsmall_impossible (Or.inl hnorm)
  · intro hnorm
    exact hsmall_impossible (Or.inr hnorm)

theorem CongruenceLatticeInvolution.primitive_householder_norm_eq_prime_or_two_prime
    {p i j k : ℕ} (T : CongruenceLatticeInvolution p i j k)
    (hadmissible : AdmissibleSparseTriple p i j k)
    (w : TernaryIntIndex) (hw : w ≠ 0) (b1 b2 b3 : ℤ)
    (hprimitive :
      b1 * w.1.1 ^ 2 + b2 * w.1.2 ^ 2 + b3 * w.2 ^ 2 = 1)
    (hT : (∀ x, T.linear x =
        ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
      (∀ x, T.linear x =
        -ternaryRatHouseholder (ternaryIntIndexToRat w) x)) :
    ternaryNorm w.1.1 w.1.2 w.2 = p ∨
      ternaryNorm w.1.1 w.1.2 w.2 = 2 * p := by
  have hcases := T.primitive_householder_norm_cases
    hadmissible w hw b1 b2 b3 hprimitive hT
  have hsmall := T.primitive_householder_norm_ne_one_two
    hadmissible w hT
  rcases hcases with hnorm | hnorm | hnorm | hnorm
  · exact (hsmall.1 hnorm).elim
  · exact (hsmall.2 hnorm).elim
  · exact Or.inl hnorm
  · exact Or.inr hnorm

theorem CongruenceLatticeInvolution.short_normal_dot_dvd_on_thetaIndexLattice
    {p i j k : ℕ} (T : CongruenceLatticeInvolution p i j k)
    (hadmissible : AdmissibleSparseTriple p i j k)
    (w : TernaryIntIndex) (hw : w ≠ 0) (b1 b2 b3 e : ℤ)
    (hprimitive :
      b1 * w.1.1 ^ 2 + b2 * w.1.2 ^ 2 + b3 * w.2 ^ 2 = 1)
    (hnorm : ternaryNorm w.1.1 w.1.2 w.2 = e * (p : ℤ))
    (hT : (∀ x, T.linear x =
        ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
      (∀ x, T.linear x =
        -ternaryRatHouseholder (ternaryIntIndexToRat w) x))
    (x : TernaryIntIndex) (hx : InThetaIndexLattice p i j k x) :
    (p : ℤ) ∣ ternaryDot w.1.1 w.1.2 w.2 x.1.1 x.1.2 x.2 := by
  obtain ⟨y, hy, hmap⟩ :=
    T.maps_lattice x hx
  obtain ⟨z, hhouse⟩ : ∃ z : TernaryIntIndex,
      ternaryRatHouseholder (ternaryIntIndexToRat w)
          (ternaryIntIndexToRat x) = ternaryIntIndexToRat z := by
    rcases hT with hpositive | hnegative
    · exact ⟨y, (hpositive _).symm.trans hmap⟩
    · have hneg := congrArg Neg.neg ((hnegative _).symm.trans hmap)
      exact ⟨-y, by simpa [ternaryIntIndexToRat] using hneg⟩
  have hdiv := householder_integral_image_norm_dvd_two_dot
    w x z hw b1 b2 b3 hprimitive hhouse
  obtain ⟨q, hq⟩ := hdiv
  have hpdiv : (p : ℤ) ∣
      2 * ternaryDot w.1.1 w.1.2 w.2 x.1.1 x.1.2 x.2 := by
    refine ⟨e * q, ?_⟩
    calc
      2 * ternaryDot w.1.1 w.1.2 w.2 x.1.1 x.1.2 x.2 =
          ternaryNorm w.1.1 w.1.2 w.2 * q := hq
      _ = (p : ℤ) * (e * q) := by rw [hnorm]; ring
  rcases hadmissible with ⟨hp, hp3, hi, hij, hjk, hpk, hisotropic⟩
  have hpoddNat : Odd p := hp.odd_of_ne_two (by omega)
  have hpodd : Odd (p : ℤ) := by exact_mod_cast hpoddNat
  exact int_dvd_of_dvd_two_mul_of_odd (p : ℤ)
    (ternaryDot w.1.1 w.1.2 w.2 x.1.1 x.1.2 x.2) hpodd hpdiv

theorem CongruenceLatticeInvolution.primitive_short_normal_projective_lift
    {p i j k : ℕ} (T : CongruenceLatticeInvolution p i j k)
    (hadmissible : AdmissibleSparseTriple p i j k)
    (w : TernaryIntIndex) (hw : w ≠ 0) (b1 b2 b3 : ℤ)
    (hprimitive :
      b1 * w.1.1 ^ 2 + b2 * w.1.2 ^ 2 + b3 * w.2 ^ 2 = 1)
    (hnorm : ternaryNorm w.1.1 w.1.2 w.2 = p ∨
      ternaryNorm w.1.1 w.1.2 w.2 = 2 * p)
    (hT : (∀ x, T.linear x =
        ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
      (∀ x, T.linear x =
        -ternaryRatHouseholder (ternaryIntIndexToRat w) x)) :
    ∃ e lambda a1 a2 a3 : ℤ,
      (e = 1 ∨ e = 2) ∧
      ternaryNorm w.1.1 w.1.2 w.2 = e * p ∧
      w.1.1 = lambda * i + p * a1 ∧
      w.1.2 = lambda * j + p * a2 ∧
      w.2 = lambda * k + p * a3 := by
  obtain ⟨e, he, hnorme⟩ : ∃ e : ℤ, (e = 1 ∨ e = 2) ∧
      ternaryNorm w.1.1 w.1.2 w.2 = e * p := by
    rcases hnorm with hnorm | hnorm
    · exact ⟨1, Or.inl rfl, by simpa using hnorm⟩
    · exact ⟨2, Or.inr rfl, by simpa using hnorm⟩
  obtain ⟨bp, bv, hunit3⟩ :=
    admissibleSparseTriple_exists_three_i_bezout hadmissible
  have hunit : bp * (p : ℤ) + (3 * bv) * (i : ℤ) = 1 := by
    linear_combination hunit3
  have hkernel : ∀ x1 x2 x3 : ℤ,
      (p : ℤ) ∣ ternaryDot i j k x1 x2 x3 →
        (p : ℤ) ∣ ternaryDot w.1.1 w.1.2 w.2 x1 x2 x3 := by
    intro x1 x2 x3 hx
    let x : TernaryIntIndex := ((x1, x2), x3)
    have hxL : InThetaIndexLattice p i j k x := by
      obtain ⟨q, hq⟩ := hx
      refine ⟨q, ?_⟩
      simpa [x, affineIndexDot, ternaryDot] using hq
    simpa [x] using T.short_normal_dot_dvd_on_thetaIndexLattice
      hadmissible w hw b1 b2 b3 e hprimitive hnorme hT x hxL
  obtain ⟨lambda, a1, a2, a3, hw1, hw2, hw3⟩ :=
    congruence_kernel_forces_projective_lift (p : ℤ)
      i j k w.1.1 w.1.2 w.2 bp (3 * bv) hunit hkernel
  exact ⟨e, lambda, a1, a2, a3, he, hnorme, hw1, hw2, hw3⟩

theorem CongruenceLatticeInvolution.exists_primitive_short_projective_householder
    {p i j k : ℕ} (T : CongruenceLatticeInvolution p i j k)
    (hadmissible : AdmissibleSparseTriple p i j k) :
    ∃ w : TernaryIntIndex, w ≠ 0 ∧
      ∃ b1 b2 b3 e lambda a1 a2 a3 : ℤ,
        b1 * w.1.1 ^ 2 + b2 * w.1.2 ^ 2 + b3 * w.2 ^ 2 = 1 ∧
        (e = 1 ∨ e = 2) ∧
        ternaryNorm w.1.1 w.1.2 w.2 = e * p ∧
        w.1.1 = lambda * i + p * a1 ∧
        w.1.2 = lambda * j + p * a2 ∧
        w.2 = lambda * k + p * a3 ∧
        ((∀ x, T.linear x =
            ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
          (∀ x, T.linear x =
            -ternaryRatHouseholder (ternaryIntIndexToRat w) x)) := by
  rcases T.exists_primitive_integral_householder_or_neg with
    hpositive | hnegative
  · obtain ⟨w, hw, b1, b2, b3, hprimitive, hT⟩ := hpositive
    have hsign :
        (∀ x, T.linear x =
          ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
        (∀ x, T.linear x =
          -ternaryRatHouseholder (ternaryIntIndexToRat w) x) := Or.inl hT
    have hnorm := T.primitive_householder_norm_eq_prime_or_two_prime
      hadmissible w hw b1 b2 b3 hprimitive hsign
    obtain ⟨e, lambda, a1, a2, a3, he, hroot, hw1, hw2, hw3⟩ :=
      T.primitive_short_normal_projective_lift hadmissible
        w hw b1 b2 b3 hprimitive hnorm hsign
    exact ⟨w, hw, b1, b2, b3, e, lambda, a1, a2, a3,
      hprimitive, he, hroot, hw1, hw2, hw3, hsign⟩
  · obtain ⟨w, hw, b1, b2, b3, hprimitive, hT⟩ := hnegative
    have hsign :
        (∀ x, T.linear x =
          ternaryRatHouseholder (ternaryIntIndexToRat w) x) ∨
        (∀ x, T.linear x =
          -ternaryRatHouseholder (ternaryIntIndexToRat w) x) := Or.inr hT
    have hnorm := T.primitive_householder_norm_eq_prime_or_two_prime
      hadmissible w hw b1 b2 b3 hprimitive hsign
    obtain ⟨e, lambda, a1, a2, a3, he, hroot, hw1, hw2, hw3⟩ :=
      T.primitive_short_normal_projective_lift hadmissible
        w hw b1 b2 b3 hprimitive hnorm hsign
    exact ⟨w, hw, b1, b2, b3, e, lambda, a1, a2, a3,
      hprimitive, he, hroot, hw1, hw2, hw3, hsign⟩

end Ramanujan.MultiQuintuple
