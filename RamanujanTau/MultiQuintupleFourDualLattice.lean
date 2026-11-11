import RamanujanTau.MultiQuintupleFourPairingIsometry

/-! Every integral projective-lattice vector has a Fourier index. In four
dimensions the cubic character is unchanged by the Fourier parametrization. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators

/-- Invert the Fourier parametrization on the integral projective lattice. -/
theorem fourDualPoint_surjective_of_projective {p : ℕ} [Fact p.Prime]
    (h3 : (3 : ZMod p) ≠ 0) {v : Fin 4 → ℤ} (x : FourProjectiveLift p v) :
    ∃ a : ZMod p × (Fin 4 → ℤ), fourDualPoint p v a=x.point := by
  let h : ZMod p := -(x.scalar : ZMod p)/3
  let z : Fin 4 → ℤ := fun i => (x.point i+3*(h.val : ℤ)*v i)/p
  have hd : ∀ i, (p : ℤ) ∣ x.point i+3*(h.val : ℤ)*v i := by
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    have hx := congrArg (fun a : ℤ => (a : ZMod p)) (congrFun x.point_eq i)
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Int.cast_add,Int.cast_mul,
      Int.cast_natCast,ZMod.natCast_self,zero_mul,add_zero] at hx
    push_cast
    rw [hx,ZMod.natCast_zmod_val]
    dsimp [h]
    field_simp
    ring
  refine ⟨(h,z),?_⟩
  funext i
  have he := Int.ediv_mul_cancel (hd i)
  change (p : ℤ)*((x.point i+3*(h.val : ℤ)*v i)/p)-3*(h.val : ℤ)*v i=x.point i
  linear_combination he

private theorem four_cubic_fourth_power : ∀ a : ZMod 3, a ≠ 0 → a^4=1 := by
  decide +kernel

/-- The fourth power removes the scaling character of the modulus. -/
theorem fourDualPoint_character (p : ℕ) (hp3 : (p : ZMod 3) ≠ 0)
    (v : Fin 4 → ℤ) (x : ZMod p × (Fin 4 → ℤ)) :
    fourCubicCharacter (fourDualPoint p v x)=fourCubicCharacter x.2 := by
  calc
    fourCubicCharacter (fourDualPoint p v x)=∏ i, (p : ZMod 3)*(x.2 i : ZMod 3) := by
      unfold fourCubicCharacter
      apply Finset.prod_congr rfl
      intro i _
      simp [fourDualPoint,show (3 : ZMod 3)=0 by decide]
    _=(p : ZMod 3)^4*fourCubicCharacter x.2 := by
      simp [Finset.prod_mul_distrib,fourCubicCharacter]
    _=fourCubicCharacter x.2 := by rw [four_cubic_fourth_power _ hp3,one_mul]

/-- A supported, positive, short projective-lattice vector is an actual short
Fourier vector. This supplies the index needed to apply analytic necessity. -/
theorem four_projective_short_lift {p : ℕ} [Fact p.Prime]
    (h3 : (3 : ZMod p) ≠ 0) (hp3 : (p : ZMod 3) ≠ 0)
    {v : Fin 4 → ℤ} (x : FourProjectiveLift p v)
    (hc : fourCubicCharacter x.point ≠ 0) (hpos : 0<fourVectorNorm x.point)
    (hshort : 2*fourVectorNorm x.point<(p : ℤ)^2) :
    ∃ a : FourShortIndex p v, fourDualPoint p v a.val=x.point := by
  obtain ⟨a,ha⟩ := fourDualPoint_surjective_of_projective h3 x
  have hn : fourDualNorm p v a=fourVectorNorm x.point := by
    rw [← fourFourierLift_norm]
    change fourVectorNorm (fourDualPoint p v a)=fourVectorNorm x.point
    rw [ha]
  have hs : fourCubicCharacter a.2 ≠ 0 := by
    rw [← fourDualPoint_character p hp3 v a,ha]
    exact hc
  exact ⟨⟨a,hs,by rw [hn]; exact hpos,by rw [hn]; exact hshort⟩,ha⟩

end Ramanujan.MultiQuintuple
