import RamanujanTau.MultiQuintupleFourPhaseCompression
import RamanujanTau.MultiQuintuplePhaseVacancy

/-! The projective norm identity for the actual four-factor Fourier phases. -/
namespace Ramanujan.MultiQuintuple
open scoped BigOperators
set_option maxHeartbeats 1000000

def fourDualNorm (p : ℕ) (v : Fin 4 → ℤ) (x : ZMod p × (Fin 4 → ℤ)) : ℤ :=
  ∑ i, fourDualPoint p v x i*fourDualPoint p v x i

theorem fourDualNorm_factor (p : ℕ) (v : Fin 4 → ℤ) (H : ℤ)
    (hv : (∑ i, v i*v i)=(p : ℤ)*H) (x : ZMod p × (Fin 4 → ℤ)) :
    fourDualNorm p v x = (p : ℤ)*((p : ℤ)*(∑ i, x.2 i*x.2 i)-
      6*(x.1.val : ℤ)*(∑ i, v i*x.2 i)+9*(x.1.val : ℤ)^2*H) := by
  calc
    _ = (p : ℤ)^2*(∑ i, x.2 i*x.2 i)-6*(p : ℤ)*(x.1.val : ℤ)*(∑ i, v i*x.2 i)+
        9*(x.1.val : ℤ)^2*(∑ i, v i*v i) := by
      simp only [fourDualNorm,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [fourDualPoint]
      ring
    _ = _ := by rw [hv]; ring

theorem fourDualNorm_quotient (p : ℕ) [NeZero p] (v : Fin 4 → ℤ) (H : ℤ)
    (hv : (∑ i, v i*v i)=(p : ℤ)*H) (x : ZMod p × (Fin 4 → ℤ)) :
    fourDualNorm p v x/p = (p : ℤ)*(∑ i, x.2 i*x.2 i)-
      6*(x.1.val : ℤ)*(∑ i, v i*x.2 i)+9*(x.1.val : ℤ)^2*H := by
  rw [fourDualNorm_factor p v H hv x,
    Int.mul_ediv_cancel_left _ (by exact_mod_cast (NeZero.ne p))]

theorem four_compressed_phase_mod_prime {p : ℕ} [Fact p.Prime]
    (h3 : (3 : ZMod p) ≠ 0) (v : Fin 4 → ℤ) (R : ℤ)
    (x : ZMod p × (Fin 4 → ℤ)) (b : Fin 4 → Bool)
    (hb : ∀ i, (x.2 i : ZMod 3)=dualCubicSign (b i)) :
    ((fourCompressedNumerator p v R x b/3 : ℤ) : ZMod p) =
      2*((∑ i, v i*fourDualPoint p v x i)/p : ℤ)+
        (((2*R-(∑ i, v i) : ℤ) : ZMod p)/3)*(-3*x.1) := by
  have hd := Int.mul_ediv_cancel' (four_compressed_numerator_dvd p v R x b hb)
  have he := congrArg (fun z : ℤ => (z : ZMod p)) hd
  have hw : (∑ i, (fourDualPoint p v x i : ZMod p)) =
      -3*x.1*(∑ i, (v i : ZMod p)) := by
    simp only [fourDualPoint,Int.cast_sub,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat,
      ZMod.natCast_self,ZMod.natCast_zmod_val,zero_mul,zero_sub,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [fourCompressedNumerator,fourRawPhase,Int.cast_add,Int.cast_sub,
    Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,Int.cast_sum,
    ZMod.natCast_self,zero_mul,add_zero,ZMod.natCast_zmod_val,hw] at he
  push_cast
  apply (mul_left_cancel₀ h3)
  calc
    _ = 6*((∑ i, v i*fourDualPoint p v x i)/p : ℤ)+
        3*x.1*(∑ i, (v i : ZMod p))-6*x.1*(R : ZMod p) := by
      simp only [fourCompressedNumerator,fourRawPhase]
      linear_combination he
    _ = _ := by field_simp; ring

theorem four_phase_projective_norm {p : ℕ} [Fact p.Prime]
    (h3 : (3 : ZMod p) ≠ 0) (v : Fin 4 → ℤ) (R H : ℤ)
    (hv : (∑ i, v i*v i)=(p : ℤ)*H)
    (x : ZMod p × (Fin 4 → ℤ)) (b : Fin 4 → Bool)
    (hb : ∀ i, (x.2 i : ZMod 3)=dualCubicSign (b i)) :
    (-3*x.1)*((fourCompressedNumerator p v R x b/3 : ℤ) : ZMod p)-
      ((H : ZMod p)+((2*R-(∑ i, v i) : ℤ) : ZMod p)/3)*(-3*x.1)^2 =
        ((fourDualNorm p v x/p : ℤ) : ZMod p) := by
  rw [four_compressed_phase_mod_prime h3 v R x b hb,
    fourDualPoint_pairing p v H hv,fourDualNorm_quotient p v H hv]
  push_cast
  simp only [ZMod.natCast_self,ZMod.natCast_zmod_val,zero_mul,zero_sub]
  ring

theorem four_short_norm_quotient_nonzero {p : ℕ} [Fact p.Prime]
    (v : Fin 4 → ℤ) (H : ℤ) (hv : (∑ i, v i*v i)=(p : ℤ)*H)
    (x : ZMod p × (Fin 4 → ℤ)) (hpos : 0<fourDualNorm p v x)
    (hshort : 2*fourDualNorm p v x<(p : ℤ)^2) :
    ((fourDualNorm p v x/p : ℤ) : ZMod p) ≠ 0 := by
  intro hz
  have hd : (p : ℤ) ∣ fourDualNorm p v x := ⟨_,fourDualNorm_factor p v H hv x⟩
  have he := Int.mul_ediv_cancel' hd
  have hq := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz
  obtain ⟨a,ha⟩ := hq
  have hp2 : (p : ℤ)^2 ∣ fourDualNorm p v x := by
    refine ⟨a,?_⟩
    rw [← he,ha]
    ring
  have hle := Int.le_of_dvd hpos hp2
  linarith

end Ramanujan.MultiQuintuple
