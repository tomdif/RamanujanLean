import RamanujanTau.MultiQuintupleFourPrimePlaneLattices

/-! Integer orthogonal involutions on equal-length rank-two bases have exactly
six signed-permutation blocks. -/
namespace Ramanujan.MultiQuintuple
set_option maxHeartbeats 2000000

def fourPairVector (u w : Fin 4 → ℤ) (a : Fin 2 → ℤ) : Fin 4 → ℤ := a 0 • u+a 1 • w

theorem fourVectorNorm_combination (u w : Fin 4 → ℤ) (a b : ℤ) :
    fourVectorNorm (a • u+b • w)=
      a*a*fourVectorNorm u+2*a*b*fourDot u w+b*b*fourVectorNorm w := by
  simp [fourVectorNorm,fourDot]
  ring

theorem four_signed_symmetric_norm_one (a b d : ℤ)
    (hab : a*a+b*b=1) (hbd : b*b+d*d=1) :
    ∃ i : Fin 6, fourPrimePlaneInvolution i 1 0=![a,b] ∧
      fourPrimePlaneInvolution i 0 1=![b,d] := by
  have ha : -1 ≤ a ∧ a ≤ 1 := by constructor <;> nlinarith [sq_nonneg b]
  have hb : -1 ≤ b ∧ b ≤ 1 := by constructor <;> nlinarith [sq_nonneg a]
  have hd : -1 ≤ d ∧ d ≤ 1 := by constructor <;> nlinarith [sq_nonneg b]
  rcases ha with ⟨ha0,ha1⟩
  rcases hb with ⟨hb0,hb1⟩
  rcases hd with ⟨hd0,hd1⟩
  interval_cases a <;> interval_cases b <;> interval_cases d <;> norm_num at hab <;> norm_num at hbd
  all_goals decide +kernel

/-- Integrality, equal basis lengths, orthogonality, and involutivity force
one of the six concrete plane blocks. -/
theorem four_involution_pair_block (u w : Fin 4 → ℤ) (q : ℤ) (hq : 0<q)
    (hu : fourVectorNorm u=q) (hw : fourVectorNorm w=q) (huw : fourDot u w=0)
    (T : FourOrthogonalInvolution)
    (hTu : ∃ a b : ℤ, T.linear (fourIntToRat u)=fourIntToRat (a • u+b • w))
    (hTw : ∃ c d : ℤ, T.linear (fourIntToRat w)=fourIntToRat (c • u+d • w)) :
    ∃ i : Fin 6,
      T.linear (fourIntToRat u)=fourIntToRat (fourPairVector u w (fourPrimePlaneInvolution i 1 0)) ∧
      T.linear (fourIntToRat w)=fourIntToRat (fourPairVector u w (fourPrimePlaneInvolution i 0 1)) := by
  obtain ⟨a,b,ha⟩ := hTu
  obtain ⟨c,d,hc⟩ := hTw
  have hn1 := four_involution_integer_norm T u (a • u+b • w) ha
  have hn2 := four_involution_integer_norm T w (c • u+d • w) hc
  rw [fourVectorNorm_combination,hu,hw,huw] at hn1 hn2
  have hab : a*a+b*b=1 := by
    apply mul_left_cancel₀ (ne_of_gt hq)
    linear_combination hn1
  have hcd : c*c+d*d=1 := by
    apply mul_left_cancel₀ (ne_of_gt hq)
    linear_combination hn2
  have hs := four_involution_self_adjoint T (fourIntToRat u) (fourIntToRat w)
  rw [ha,hc,fourDot_intToRat,fourDot_intToRat] at hs
  have hsi : fourDot (a • u+b • w) w=fourDot u (c • u+d • w) := by exact_mod_cast hs
  rw [fourDot_add_left,fourDot_add_right,fourDot_smul_left,fourDot_smul_left,
    fourDot_smul_right,fourDot_smul_right] at hsi
  change fourDot u u=q at hu
  change fourDot w w=q at hw
  have hbc : b=c := by
    apply mul_right_cancel₀ (ne_of_gt hq)
    simpa only [hu,hw,huw,mul_zero,zero_add,add_zero] using hsi
  subst c
  obtain ⟨i,hi,hj⟩ := four_signed_symmetric_norm_one a b d hab hcd
  refine ⟨i,?_,?_⟩
  · rw [hi]
    exact ha
  · rw [hj]
    exact hc

/-- A residue-lattice symmetry has one of six blocks on each of the fixed
short plane and its long orthogonal complement. -/
theorem fourPrime_lattice_blocks {p : ℕ} [Fact p.Prime] (m n : ℤ)
    (hp : (p : ℤ)=m*m+n*n) (hp9 : 9<p) (h3 : (3 : ZMod p) ≠ 0) (hm : (m : ZMod p) ≠ 0)
    (T : FourOrthogonalInvolution)
    (hL : ∀ x ∈ fourResidueModule p (fourPrimeV m n),
      ∃ y ∈ fourResidueModule p (fourPrimeV m n), T.linear (fourIntToRat x)=fourIntToRat y) :
    ∃ a b : Fin 6,
      T.linear (fourIntToRat (fourPrimeV m n))=
        fourIntToRat (fourPairVector (fourPrimeV m n) (fourPrimeJ m n) (fourPrimePlaneInvolution a 1 0)) ∧
      T.linear (fourIntToRat (fourPrimeJ m n))=
        fourIntToRat (fourPairVector (fourPrimeV m n) (fourPrimeJ m n) (fourPrimePlaneInvolution a 0 1)) ∧
      T.linear (fourIntToRat fourPrimeU)=
        fourIntToRat (fourPairVector fourPrimeU fourPrimeW (fourPrimePlaneInvolution b 1 0)) ∧
      T.linear (fourIntToRat fourPrimeW)=
        fourIntToRat (fourPairVector fourPrimeU fourPrimeW (fourPrimePlaneInvolution b 0 1)) := by
  have hpq : 0<3*(p : ℤ) := by have := (Fact.out : p.Prime).pos; positivity
  have hv : fourVectorNorm (fourPrimeV m n)=3*(p : ℤ) := by rw [fourPrime_long_norm,hp]
  have hj : fourVectorNorm (fourPrimeJ m n)=3*(p : ℤ) := by
    rw [fourPrimeJ,fourPrime_long_norm,hp]
    ring
  have hvj : fourDot (fourPrimeV m n) (fourPrimeJ m n)=0 := by
    simp [fourPrimeV,fourPrimeJ,fourDot]
    ring
  obtain ⟨a,ha,hj'⟩ := four_involution_pair_block (fourPrimeV m n) (fourPrimeJ m n)
    (3*(p : ℤ)) hpq hv hj hvj T
    (fourPrime_long_images_integral m n hp hp9 h3 hm T hL _ (Or.inl rfl))
    (fourPrime_long_images_integral m n hp hp9 h3 hm T hL _ (Or.inr rfl))
  have hs (x : Fin 4 → ℤ) (hx : x=fourPrimeU ∨ x=fourPrimeW) :
      ∃ c d : ℤ, T.linear (fourIntToRat x)=fourIntToRat (c • fourPrimeU+d • fourPrimeW) := by
    rcases fourPrime_fixed_images m n hp hp9 hm T hL x hx with h | h | h | h
    · exact ⟨1,0,by simpa using h⟩
    · exact ⟨-1,0,by simpa using h⟩
    · exact ⟨0,1,by simpa using h⟩
    · exact ⟨0,-1,by simpa using h⟩
  obtain ⟨b,hb,hb'⟩ := four_involution_pair_block fourPrimeU fourPrimeW 3 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) T
    (hs _ (Or.inl rfl)) (hs _ (Or.inr rfl))
  exact ⟨a,b,ha,hj',hb,hb'⟩

end Ramanujan.MultiQuintuple
