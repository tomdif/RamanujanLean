import RamanujanTau.MultiQuintupleFourPlaneBlocks

/-! The two lattice blocks reverse the certified integer characters. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 3000000

theorem fourIntToRat_injective : Function.Injective fourIntToRat := by
  intro x y h
  funext i
  have hi := congrFun h i
  change (x i : ℚ)=(y i : ℚ) at hi
  exact_mod_cast hi

theorem fourPairVector_plane_linear (u w : Fin 4 → ℤ) (a : Fin 6) (x y : ℤ) :
    fourPairVector u w (fourPrimePlaneInvolution a x y)=
      x • fourPairVector u w (fourPrimePlaneInvolution a 1 0)+
        y • fourPairVector u w (fourPrimePlaneInvolution a 0 1) := by
  fin_cases a <;> simp [fourPairVector,fourPrimePlaneInvolution] <;> module

theorem four_block_pair_map (T : FourOrthogonalInvolution) (u w : Fin 4 → ℤ) (a : Fin 6)
    (hu : T.linear (fourIntToRat u)=fourIntToRat (fourPairVector u w (fourPrimePlaneInvolution a 1 0)))
    (hw : T.linear (fourIntToRat w)=fourIntToRat (fourPairVector u w (fourPrimePlaneInvolution a 0 1)))
    (x y : ℤ) :
    T.linear (fourIntToRat (x • u+y • w))=
      fourIntToRat (fourPairVector u w (fourPrimePlaneInvolution a x y)) := by
  rw [fourPairVector_plane_linear]
  simp only [fourIntToRat_add,fourIntToRat_int_smul,map_add,map_smul,hu,hw]

theorem fourPrime_numerator_split (m n : ℤ) (z : Fin 4 → ℤ) :
    fourPrimeNumerator m n z=
      (z 0 • fourPrimeV m n+z 1 • fourPrimeJ m n)+
        (m*m+n*n) • (z 2 • fourPrimeU+z 3 • fourPrimeW) := by
  ext i
  fin_cases i <;> dsimp [fourPrimeNumerator,fourPrimeV,fourPrimeJ,fourPrimeU,fourPrimeW] <;> ring

theorem fourPrime_numerator_blocks (m n : ℤ) (T : FourOrthogonalInvolution) (a b : Fin 6)
    (hv : T.linear (fourIntToRat (fourPrimeV m n))=
      fourIntToRat (fourPairVector (fourPrimeV m n) (fourPrimeJ m n) (fourPrimePlaneInvolution a 1 0)))
    (hj : T.linear (fourIntToRat (fourPrimeJ m n))=
      fourIntToRat (fourPairVector (fourPrimeV m n) (fourPrimeJ m n) (fourPrimePlaneInvolution a 0 1)))
    (hu : T.linear (fourIntToRat fourPrimeU)=
      fourIntToRat (fourPairVector fourPrimeU fourPrimeW (fourPrimePlaneInvolution b 1 0)))
    (hw : T.linear (fourIntToRat fourPrimeW)=
      fourIntToRat (fourPairVector fourPrimeU fourPrimeW (fourPrimePlaneInvolution b 0 1)))
    (z : Fin 4 → ℤ) :
    T.linear (fourIntToRat (fourPrimeNumerator m n z))=
      fourIntToRat (fourPrimeNumerator m n (fourPrimeImage a b z)) := by
  rw [fourPrime_numerator_split m n z,fourIntToRat_add,fourIntToRat_int_smul,map_add,map_smul,
    four_block_pair_map T _ _ a hv hj,four_block_pair_map T _ _ b hu hw,
    ← fourIntToRat_int_smul,← fourIntToRat_add,fourPrime_numerator_split]
  rfl

theorem fourPrime_character_abs_le (m n : ℤ) (z : Fin 4 → ℤ) : |fourPrimeCharacter m n z| ≤ 1 := by
  unfold fourPrimeCharacter
  rw [Finset.abs_prod]
  apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
  intro i _
  unfold fourPrimeTrit
  split_ifs <;> norm_num

theorem four_signed_character_cast_injective (a b : ℤ) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (he : (a : ZMod 3)=(b : ZMod 3)) : a=b := by
  have hd : (3 : ℤ) ∣ a-b := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp (by
    push_cast
    rw [he,sub_self])
  have hmod := Int.emod_eq_zero_of_dvd hd
  rw [abs_le] at ha hb
  omega

/-- Character reversal on the actual supported short Fourier vectors forces
compatibility with the finite integer certificates for the lattice blocks. -/
theorem fourPrime_blocks_compatible {p : ℕ} [Fact p.Prime] (m n : ℤ)
    (hp : (p : ℤ)=m*m+n*n) (hp100 : 100<p) (hp3 : (p : ZMod 3) ≠ 0)
    (h3 : (3 : ZMod p) ≠ 0) (hm : (m : ZMod p) ≠ 0) (T : FourOrthogonalInvolution)
    (hshort : ∀ x : FourShortIndex p (fourPrimeV m n),
      ∃ y : FourShortIndex p (fourPrimeV m n),
        T.linear (fourIntToRat (fourDualPoint p (fourPrimeV m n) x.val))=
          fourIntToRat (fourDualPoint p (fourPrimeV m n) y.val) ∧
        fourCubicCharacter y.val.2= -fourCubicCharacter x.val.2)
    (a b : Fin 6)
    (hv : T.linear (fourIntToRat (fourPrimeV m n))=
      fourIntToRat (fourPairVector (fourPrimeV m n) (fourPrimeJ m n) (fourPrimePlaneInvolution a 1 0)))
    (hj : T.linear (fourIntToRat (fourPrimeJ m n))=
      fourIntToRat (fourPairVector (fourPrimeV m n) (fourPrimeJ m n) (fourPrimePlaneInvolution a 0 1)))
    (hu : T.linear (fourIntToRat fourPrimeU)=
      fourIntToRat (fourPairVector fourPrimeU fourPrimeW (fourPrimePlaneInvolution b 1 0)))
    (hw : T.linear (fourIntToRat fourPrimeW)=
      fourIntToRat (fourPairVector fourPrimeU fourPrimeW (fourPrimePlaneInvolution b 0 1))) :
    FourPrimeCompatible m n a b := by
  have hp3' : ((m*m+n*n : ℤ) : ZMod 3) ≠ 0 := by rw [← hp]; simpa only [Int.cast_natCast] using hp3
  have hp100' : 100<m*m+n*n := by rw [← hp]; exact_mod_cast hp100
  intro j
  let z := (fourPrimeData m n).points j
  have hd := (fourPrime_generator_data m n hp3').1 j
  have hz : FourPrimeIntegral m n z := fourPrime_character_integral m n z hd.2.2.1
  obtain ⟨lift,hlift⟩ := fourPrime_point_projective m n hp h3 hm z hz
  obtain ⟨hc,hpos,hbound⟩ := fourPrime_generator_short m n hp100' hp3' j
  obtain ⟨x,hx⟩ := four_projective_short_lift h3 hp3 lift
    (by rw [hlift]; exact hc) (by rw [hlift]; exact hpos) (by rw [hlift,hp]; exact hbound)
  have hpoint := hx.trans hlift
  obtain ⟨y,hy,hchar⟩ := hshort x
  rw [hpoint] at hy
  have hn := fourPrime_numerator_blocks m n T a b hv hj hu hw z
  have hnum : fourPrimeNumerator m n z=(3 : ℤ) • fourPrimePoint m n z := by
    funext i
    exact (fourPrime_three_point m n z hz i).symm
  rw [hnum,fourIntToRat_int_smul,map_smul,hy,← fourIntToRat_int_smul] at hn
  have hi := (fourIntToRat_injective hn).symm
  have hint : FourPrimeIntegral m n (fourPrimeImage a b z) := by
    intro i
    exact ⟨fourDualPoint p (fourPrimeV m n) y.val i,congrFun hi i⟩
  have himage : fourPrimePoint m n (fourPrimeImage a b z)=fourDualPoint p (fourPrimeV m n) y.val := by
    funext i
    apply mul_left_cancel₀ (by decide : (3 : ℤ) ≠ 0)
    rw [fourPrime_three_point m n _ hint]
    exact congrFun hi i
  apply four_signed_character_cast_injective _ _ (fourPrime_character_abs_le _ _ _)
    (by simpa only [abs_neg] using fourPrime_character_abs_le m n z)
  rw [fourPrime_point_character m n _ hint,himage,fourDualPoint_character p hp3,hchar,
    ← fourDualPoint_character p hp3 (fourPrimeV m n) x.val,hpoint,
    ← fourPrime_point_character m n z hz,Int.cast_neg]

end Ramanujan.MultiQuintuple
