import RamanujanTau.MultiQuintupleFourPrimeShortGenerators

/-! Supported short Fourier vectors span the prime-family lattice integrally
and the full rational space. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 2000000

/-- An explicit integral lift of a vector on the projective residue line. -/
def fourProjectiveLiftOfCast {p : ℕ} [Fact p.Prime] (v w : Fin 4 → ℤ)
    (a : ZMod p) (hw : ∀ i, (w i : ZMod p)=a*(v i : ZMod p)) : FourProjectiveLift p v where
  point := w
  scalar := a.val
  remainder i := (w i-(a.val : ℤ)*v i)/p
  point_eq := by
    funext i
    have hd : (p : ℤ) ∣ w i-(a.val : ℤ)*v i := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
      push_cast
      rw [ZMod.natCast_zmod_val,hw]
      ring
    have he := Int.mul_ediv_cancel' hd
    change w i=(a.val : ℤ)*v i+(p : ℤ)*((w i-(a.val : ℤ)*v i)/p)
    omega

theorem fourPrime_point_projective {p : ℕ} [Fact p.Prime] (m n : ℤ)
    (hp : (p : ℤ)=m*m+n*n) (h3 : (3 : ZMod p) ≠ 0) (hm : (m : ZMod p) ≠ 0)
    (z : Fin 4 → ℤ) (hz : FourPrimeIntegral m n z) :
    ∃ x : FourProjectiveLift p (fourPrimeV m n), x.point=fourPrimePoint m n z := by
  have hpp : (m : ZMod p)*(m : ZMod p)+(n : ZMod p)*(n : ZMod p)=0 := by
    have h := congrArg (fun a : ℤ => (a : ZMod p)) hp
    simpa only [Int.cast_natCast,ZMod.natCast_self,Int.cast_add,Int.cast_mul] using h.symm
  let X : ZMod p := (m : ZMod p)*z 0-(n : ZMod p)*z 1
  let Y : ZMod p := (n : ZMod p)*z 0+(m : ZMod p)*z 1
  have hline : (m : ZMod p)*Y=(n : ZMod p)*X := by
    dsimp [X,Y]
    linear_combination (z 1 : ZMod p)*hpp
  have hcoords : ∀ i, (m : ZMod p)*(fourPrimeNumerator m n z i : ZMod p)=
      X*(fourPrimeV m n i : ZMod p) := by
    intro i
    fin_cases i <;> simp [fourPrimeNumerator,fourPrimeV,hpp] <;> dsimp [X,Y] at hline ⊢
    · linear_combination -hline
    · linear_combination hline
    · ring
    · linear_combination hline
  let a : ZMod p := X/(3*(m : ZMod p))
  have hw : ∀ i, (fourPrimePoint m n z i : ZMod p)=a*(fourPrimeV m n i : ZMod p) := by
    intro i
    have hthree := congrArg (fun a : ℤ => (a : ZMod p)) (fourPrime_three_point m n z hz i)
    push_cast at hthree
    apply mul_left_cancel₀ (mul_ne_zero h3 hm)
    calc
      (3*(m : ZMod p))*(fourPrimePoint m n z i : ZMod p)=
          (m : ZMod p)*(3*(fourPrimePoint m n z i : ZMod p)) := by ring
      _=(m : ZMod p)*(fourPrimeNumerator m n z i : ZMod p) := by rw [hthree]
      _=X*(fourPrimeV m n i : ZMod p) := hcoords i
      _=(3*(m : ZMod p))*(a*(fourPrimeV m n i : ZMod p)) := by
        dsimp [a]
        field_simp
  exact ⟨fourProjectiveLiftOfCast (fourPrimeV m n) (fourPrimePoint m n z) a hw,rfl⟩

def fourShortPointSet (p : ℕ) (v : Fin 4 → ℤ) : Set (Fin 4 → ℤ) :=
  Set.range (fun x : FourShortIndex p v => fourDualPoint p v x.val)

/-- The supported short vectors generate every integral projective lift. -/
theorem fourPrime_projective_mem_short_span {p : ℕ} [Fact p.Prime] (m n : ℤ)
    (hp : (p : ℤ)=m*m+n*n) (hp100 : 100<p) (hp3 : (p : ZMod 3) ≠ 0)
    (h3 : (3 : ZMod p) ≠ 0) (hm : (m : ZMod p) ≠ 0)
    (x : FourProjectiveLift p (fourPrimeV m n)) :
    x.point ∈ Submodule.span ℤ (fourShortPointSet p (fourPrimeV m n)) := by
  have hp3' : ((m*m+n*n : ℤ) : ZMod 3) ≠ 0 := by
    rw [← hp]
    simpa only [Int.cast_natCast] using hp3
  have hp100' : 100<m*m+n*n := by rw [← hp]; exact_mod_cast hp100
  have hmem : ∀ j : Fin 12, fourPrimePoint m n ((fourPrimeData m n).points j) ∈
      Submodule.span ℤ (fourShortPointSet p (fourPrimeV m n)) := by
    intro j
    have hd := (fourPrime_generator_data m n hp3').1 j
    obtain ⟨y,hy⟩ := fourPrime_point_projective m n hp h3 hm _
      (fourPrime_character_integral m n _ hd.2.2.1)
    obtain ⟨hc,hpos,hshort⟩ := fourPrime_generator_short m n hp100' hp3' j
    obtain ⟨a,ha⟩ := four_projective_short_lift h3 hp3 y
      (by rw [hy]; exact hc) (by rw [hy]; exact hpos) (by rw [hy,hp]; exact hshort)
    exact Submodule.subset_span ⟨a,ha.trans hy⟩
  obtain ⟨c,hc⟩ := fourPrime_projective_integer_generation m n hp hp3' x
  rw [hc]
  exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hmem j))

theorem fourIntToRat_add (x y : Fin 4 → ℤ) :
    fourIntToRat (x+y)=fourIntToRat x+fourIntToRat y := by
  ext i
  simp [fourIntToRat]

theorem fourIntToRat_int_smul (c : ℤ) (x : Fin 4 → ℤ) :
    fourIntToRat (c • x)=(c : ℚ) • fourIntToRat x := by
  ext i
  simp [fourIntToRat]

/-- Pass from integral generation to rational span without assuming saturation. -/
theorem four_short_span_cast {p : ℕ} {v z : Fin 4 → ℤ}
    (hz : z ∈ Submodule.span ℤ (fourShortPointSet p v)) :
    fourIntToRat z ∈ Submodule.span ℚ
      (Set.range (fun x : FourShortIndex p v => fourIntToRat (fourDualPoint p v x.val))) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i,rfl⟩ := hx
      exact Submodule.subset_span ⟨i,rfl⟩
  | zero =>
      have hz0 : fourIntToRat (0 : Fin 4 → ℤ)=(0 : FourRatPoint) := by
        ext i
        simp [fourIntToRat]
      rw [hz0]
      exact Submodule.zero_mem _
  | add x y hx hy ix iy =>
      simpa only [fourIntToRat_add] using Submodule.add_mem _ ix iy
  | smul c x hx ix =>
      simpa only [fourIntToRat_int_smul] using Submodule.smul_mem _ (c : ℚ) ix

/-- The strict p²/2 Fourier shell spans all four rational dimensions for every
prime in the family above 100. The finite certificates are fully lifted. -/
theorem fourPrime_short_span {p : ℕ} [Fact p.Prime] (m n : ℤ)
    (hp : (p : ℤ)=m*m+n*n) (hp100 : 100<p) (hp3 : (p : ZMod 3) ≠ 0)
    (h3 : (3 : ZMod p) ≠ 0) (hm : (m : ZMod p) ≠ 0) :
    Submodule.span ℚ (Set.range (fun x : FourShortIndex p (fourPrimeV m n) =>
      fourIntToRat (fourDualPoint p (fourPrimeV m n) x.val)))=⊤ := by
  classical
  let P := Submodule.span ℚ (Set.range (fun x : FourShortIndex p (fourPrimeV m n) =>
    fourIntToRat (fourDualPoint p (fourPrimeV m n) x.val)))
  have hsingle : ∀ i : Fin 4, Pi.single i (1 : ℚ) ∈ P := by
    intro i
    let x : FourProjectiveLift p (fourPrimeV m n) :=
      ⟨(p : ℤ) • Pi.single i 1,0,Pi.single i 1,by simp⟩
    have hh := four_short_span_cast (fourPrime_projective_mem_short_span m n hp hp100 hp3 h3 hm x)
    have he : fourIntToRat x.point=(p : ℚ) • Pi.single i (1 : ℚ) := by
      ext k
      by_cases hk : k=i <;> simp [x,fourIntToRat,hk]
    rw [he] at hh
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    simpa only [smul_smul,inv_mul_cancel₀ hpq,one_smul] using P.smul_mem (p : ℚ)⁻¹ hh
  apply top_unique
  intro z _
  have he : z=∑ i : Fin 4, z i • Pi.single i (1 : ℚ) := by
    ext k
    simp [Finset.sum_apply,Pi.single_apply]
  rw [he]
  exact P.sum_mem (fun i _ => P.smul_mem _ (hsingle i))

end Ramanujan.MultiQuintuple
