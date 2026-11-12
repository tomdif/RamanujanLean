import RamanujanTau.MultiQuintupleFourPrimeCertificateLift

/-! Supported short integer generators for the entire prime-family lattice. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem fourPrimeTrit_ne_zero_iff (a : ℤ) :
    fourPrimeTrit a ≠ 0 ↔ a%9=3 ∨ a%9=6 := by
  unfold fourPrimeTrit
  split_ifs <;> simp_all

theorem fourPrime_character_integral (m n : ℤ) (z : Fin 4 → ℤ)
    (hz : fourPrimeCharacter m n z ≠ 0) : FourPrimeIntegral m n z := by
  intro i
  have hi := (Finset.prod_ne_zero_iff.mp hz) i (Finset.mem_univ i)
  rcases (fourPrimeTrit_ne_zero_iff _).mp hi with hi | hi
  all_goals exact Int.dvd_of_emod_eq_zero (by omega)

theorem fourPrimeTrit_cast (a : ℤ) (ha : (3 : ℤ) ∣ a) :
    (fourPrimeTrit a : ZMod 3)=((a/3 : ℤ) : ZMod 3) := by
  obtain ⟨q,rfl⟩ := ha
  have hq : ((q%3 : ℤ) : ZMod 3)=(q : ZMod 3) := ZMod.intCast_mod q 3
  have hlo : 0 ≤ q%3 := Int.emod_nonneg q (by decide)
  have hhi : q%3<3 := Int.emod_lt_of_pos q (by decide)
  interval_cases h : q%3
  all_goals
    have h9 : (3*q)%9=3*(q%3) := by omega
    simpa [fourPrimeTrit,h9,h] using hq

theorem fourPrime_point_character (m n : ℤ) (z : Fin 4 → ℤ)
    (hz : FourPrimeIntegral m n z) :
    (fourPrimeCharacter m n z : ZMod 3)=fourCubicCharacter (fourPrimePoint m n z) := by
  simp only [fourPrimeCharacter,Int.cast_prod,fourCubicCharacter,fourPrimePoint]
  apply Finset.prod_congr rfl
  intro i _
  exact fourPrimeTrit_cast _ (hz i)

theorem fourPrime_point_supported (m n : ℤ) (z : Fin 4 → ℤ)
    (hz : fourPrimeCharacter m n z ≠ 0) : fourCubicCharacter (fourPrimePoint m n z) ≠ 0 := by
  rw [← fourPrime_point_character m n z (fourPrime_character_integral m n z hz)]
  simp only [fourPrimeCharacter,Int.cast_prod] at hz ⊢
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have ht := (Finset.prod_ne_zero_iff.mp hz) i hi
  unfold fourPrimeTrit at ht ⊢
  split_ifs at * <;> norm_num at *

theorem fourPrime_point_norm (m n : ℤ) (z : Fin 4 → ℤ)
    (hz : FourPrimeIntegral m n z) :
    3*fourVectorNorm (fourPrimePoint m n z)=
      (m*m+n*n)*(z 0*z 0+z 1*z 1+(m*m+n*n)*(z 2*z 2+z 3*z 3)) := by
  have he : fourPrimeNumerator m n z=(3 : ℤ) • fourPrimePoint m n z := by
    funext i
    exact (fourPrime_three_point m n z hz i).symm
  apply mul_left_cancel₀ (by decide : (3 : ℤ) ≠ 0)
  calc
    3*(3*fourVectorNorm (fourPrimePoint m n z))=fourPrimeNorm (fourPrimeNumerator m n z) := by
      rw [he]
      simp [fourPrimeNorm,fourVectorNorm,fourDot,Fin.sum_univ_succ]
      ring
    _=3*((m*m+n*n)*(z 0*z 0+z 1*z 1+(m*m+n*n)*(z 2*z 2+z 3*z 3))) := by
      rw [fourPrime_numerator_norm]
      ring

theorem fourPrime_point_positive (m n : ℤ) (z : Fin 4 → ℤ)
    (hz : fourPrimeCharacter m n z ≠ 0) : 0<fourVectorNorm (fourPrimePoint m n z) := by
  have hs := fourPrime_point_supported m n z hz
  have hn := fourVectorNorm_nonneg (fourPrimePoint m n z)
  have hne : fourVectorNorm (fourPrimePoint m n z) ≠ 0 := by
    intro h
    have he := (fourVectorNorm_eq_zero_iff _).mp h
    simp [he,fourCubicCharacter] at hs
  omega

theorem fourPrime_generator_short (m n : ℤ)
    (hp100 : 100<m*m+n*n) (hp3 : ((m*m+n*n : ℤ) : ZMod 3) ≠ 0) (j : Fin 12) :
    fourCubicCharacter (fourPrimePoint m n ((fourPrimeData m n).points j)) ≠ 0 ∧
    0<fourVectorNorm (fourPrimePoint m n ((fourPrimeData m n).points j)) ∧
    2*fourVectorNorm (fourPrimePoint m n ((fourPrimeData m n).points j))<(m*m+n*n)^2 := by
  obtain ⟨haxis,hbound,hchar,h0,h1⟩ := (fourPrime_generator_data m n hp3).1 j
  refine ⟨fourPrime_point_supported m n _ hchar,fourPrime_point_positive m n _ hchar,?_⟩
  have hn := fourPrime_point_norm m n _ (fourPrime_character_integral m n _ hchar)
  have hd : 3*fourVectorNorm (fourPrimePoint m n ((fourPrimeData m n).points j))=
      (m*m+n*n)*(m*m+n*n+(fourPrimeData m n).points j 0*(fourPrimeData m n).points j 0+
        (fourPrimeData m n).points j 1*(fourPrimeData m n).points j 1) := by
    rcases haxis with ⟨h2,h3⟩ | ⟨h2,h3⟩ <;> rw [h2,h3] at hn <;> nlinarith [hn]
  simpa only [pow_two] using fourPrime_supported_point_short (m*m+n*n)
    ((fourPrimeData m n).points j 0) ((fourPrimeData m n).points j 1) _ hp100 hbound hd

/-- A left inverse gives explicit integral coefficients for every vector. -/
theorem four_integer_coefficients {ι : Type*} [Fintype ι]
    (a : ι → Fin 4 → ℤ) (b : Fin 4 → ι → ℤ)
    (hinverse : ∀ i k, ∑ j, b i j*a j k=if i=k then 1 else 0) (q : Fin 4 → ℤ) :
    q=∑ j, (∑ i, q i*b i j) • a j := by
  funext k
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  symm
  calc
    ∑ j, (∑ i, q i*b i j)*a j k=∑ i, q i*(∑ j, b i j*a j k) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp [Finset.mul_sum,mul_assoc]
    _=q k := by simp [hinverse]

/-- Every integral projective-lattice vector is an integer linear combination
of the twelve certified points, uniformly in the integer parameters. -/
theorem fourPrime_projective_integer_generation {p : ℕ} (m n : ℤ)
    (hp : (p : ℤ)=m*m+n*n) (hp3 : ((m*m+n*n : ℤ) : ZMod 3) ≠ 0)
    (x : FourProjectiveLift p (fourPrimeV m n)) :
    ∃ c : Fin 12 → ℤ, x.point=∑ j, c j • fourPrimePoint m n ((fourPrimeData m n).points j) := by
  obtain ⟨q,hq⟩ := fourPrime_projective_basis_preimage m n hp hp3 x
  have hd := fourPrime_generator_data m n hp3
  have he := four_integer_coefficients (fun j => fourPrimeCoordinates m n ((fourPrimeData m n).points j))
    (fourPrimeData m n).inverse hd.2 q
  have hb := congrArg (fourPrimeBasisMap m n) he
  rw [hq] at hb
  simp only [map_sum,map_smul] at hb
  refine ⟨fun j => ∑ i, q i*(fourPrimeData m n).inverse i j,?_⟩
  rw [hb]
  apply Finset.sum_congr rfl
  intro j _
  rw [← fourPrime_point_eq_basis m n hp3 _ (fourPrime_character_integral m n _ (hd.1 j).2.2.1)]

end Ramanujan.MultiQuintuple
