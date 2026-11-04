import RamanujanTau.MultiQuintupleFourBinaryAlgebra

/-!
# Infinite four-factor vanishing for `p=2m²+n²`

This family has indices `2m,4m,n,3n`, with `3 | m` and `5 | n`.
The two zero progressions come from complementary plane reflections.
-/
namespace Ramanujan.MultiQuintuple
open PowerSeries
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def fourBinaryK (m n : ℤ) (r : Bool) (z : QuadIntPoint) : ℤ :=
  fourBinaryNum m n r z/(2*m^2+n^2)

def fourBinaryPartner (m n : ℤ) (r : Bool) (x : QuadQuintBranchIndex) :
    QuadQuintBranchIndex :=
  quadAssemble (fourBinaryBits r (quadBits x)) (fun i =>
    (fourBinaryRaw m n r (quadZ x) (fourBinaryK m n r (quadZ x)) i-
      5*(if fourBinaryBits r (quadBits x) i then 1 else 0))/15)

lemma fourBinaryK_spec (m n : ℤ) (r : Bool) (z : QuadIntPoint)
    (hd : 2*m^2+n^2 ∣ fourBinaryNum m n r z) :
    (2*m^2+n^2)*fourBinaryK m n r z=fourBinaryNum m n r z := by
  simpa [fourBinaryK,mul_comm] using Int.ediv_mul_cancel hd

lemma fourBinary_raw_branch_dvd (m n : ℤ) (r : Bool) (x : QuadQuintBranchIndex)
    (k : ℤ) (h3 : (3 : ℤ) ∣ m) (h5 : (5 : ℤ) ∣ n)
    (hp15 : IsUnit (2*(m : ZMod 15)^2+(n : ZMod 15)^2))
    (hk : (2*m^2+n^2)*k=fourBinaryNum m n r (quadZ x)) (i : Fin 4) :
    (15 : ℤ) ∣ fourBinaryRaw m n r (quadZ x) k i-
      5*(if fourBinaryBits r (quadBits x) i then 1 else 0) := by
  have hm : ∃ a : ZMod 15, (m : ZMod 15)=3*a := by
    obtain ⟨a,ha⟩ := h3
    exact ⟨(a : ZMod 15),by
      simpa only [Int.cast_mul,Int.cast_ofNat] using congrArg (fun z : ℤ => (z : ZMod 15)) ha⟩
  have hn : ∃ b : ZMod 15, (n : ZMod 15)=5*b := by
    obtain ⟨b,hb⟩ := h5
    exact ⟨(b : ZMod 15),by
      simpa only [Int.cast_mul,Int.cast_ofNat] using congrArg (fun z : ℤ => (z : ZMod 15)) hb⟩
  have hk15 : (2*(m : ZMod 15)^2+(n : ZMod 15)^2)*(k : ZMod 15)=
      fourBinaryNum (m : ZMod 15) (n : ZMod 15) r (fun i => (quadZ x i : ZMod 15)) := by
    simpa only [Int.cast_mul,Int.cast_add,Int.cast_pow,Int.cast_ofNat,fourBinaryNum_cast] using
      congrArg (fun t : ℤ => (t : ZMod 15)) hk
  have hd : (15 : ℤ) ∣ fourBinaryRaw m n r (quadZ x) k i-
      5*fourBinaryRule r (quadZ x) i := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 15).mp
    have hh := fourBinary_raw_mod_fifteen (m : ZMod 15) (n : ZMod 15) r hm hn hp15
      (fun j => (quadZ x j : ZMod 15)) (k : ZMod 15) hk15 i
    simpa only [Int.cast_sub,Int.cast_mul,Int.cast_ofNat,fourBinaryRaw_cast,
      fourBinaryRule_cast,sub_eq_zero] using hh
  have hb := fourBinary_rule_branch r x i
  convert dvd_add hd hb using 1
  ring

lemma fourBinary_partner_coords (m n : ℤ) (r : Bool) (x : QuadQuintBranchIndex)
    (h3 : (3 : ℤ) ∣ m) (h5 : (5 : ℤ) ∣ n)
    (hp15 : IsUnit (2*(m : ZMod 15)^2+(n : ZMod 15)^2))
    (hd : 2*m^2+n^2 ∣ fourBinaryNum m n r (quadZ x)) :
    ∀ i, 5*quadZ (fourBinaryPartner m n r x) i=
      fourBinaryRaw m n r (quadZ x) (fourBinaryK m n r (quadZ x)) i := by
  intro i
  have hh := Int.ediv_mul_cancel (fourBinary_raw_branch_dvd m n r x _ h3 h5 hp15
    (fourBinaryK_spec m n r _ hd) i)
  simp only [fourBinaryPartner,quadZ_assemble]
  linarith

lemma fourBinary_partner_energy (m n : ℤ) (r : Bool) (x : QuadQuintBranchIndex)
    (h3 : (3 : ℤ) ∣ m) (h5 : (5 : ℤ) ∣ n)
    (hp15 : IsUnit (2*(m : ZMod 15)^2+(n : ZMod 15)^2))
    (hd : 2*m^2+n^2 ∣ fourBinaryNum m n r (quadZ x)) :
    fourEnergy (2*m^2+n^2) (fourBinaryV m n) (quadZ (fourBinaryPartner m n r x))=
      fourEnergy (2*m^2+n^2) (fourBinaryV m n) (quadZ x) := by
  have hz := funext (fourBinary_partner_coords m n r x h3 h5 hp15 hd)
  have he := fourBinary_energy_raw m n r (quadZ x) _ (fourBinaryK_spec m n r _ hd)
  rw [← hz,fourEnergyFive_scale] at he
  omega

lemma fourBinary_partner_involutive (m n : ℤ) (r : Bool) (x : QuadQuintBranchIndex)
    (hp : 2*m^2+n^2 ≠ 0) (h3 : (3 : ℤ) ∣ m) (h5 : (5 : ℤ) ∣ n)
    (hp15 : IsUnit (2*(m : ZMod 15)^2+(n : ZMod 15)^2))
    (hd : 2*m^2+n^2 ∣ fourBinaryNum m n r (quadZ x)) :
    fourBinaryPartner m n r (fourBinaryPartner m n r x)=x := by
  have hk := fourBinaryK_spec m n r _ hd
  have hz := fourBinary_partner_coords m n r x h3 h5 hp15 hd
  have hnum := fourBinary_num_next m n r _ _ _ hk hz
  have hd' : 2*m^2+n^2 ∣ fourBinaryNum m n r (quadZ (fourBinaryPartner m n r x)) :=
    ⟨_,hnum⟩
  have hnext : fourBinaryK m n r (quadZ (fourBinaryPartner m n r x))=
      -fourBinaryK m n r (quadZ x) := by
    simp only [fourBinaryK] at hnum ⊢
    rw [hnum]
    exact Int.mul_ediv_cancel_left _ hp
  have hz' := fourBinary_partner_coords m n r (fourBinaryPartner m n r x) h3 h5 hp15 hd'
  simp only [hnext] at hz'
  have hback := fourBinary_raw_involutive m n r _ _ _ hz
  apply quadZ_injective
  funext i
  have hi := hz' i
  rw [hback i] at hi
  omega



lemma fourBinary_num_dvd_of_exp (p m n R N : ℕ) (r : Bool)
    (hp : p=2*m^2+n^2) (hp6 : Nat.Coprime 6 p) (hpm : Nat.Coprime m p)
    (hR : (p : ℤ) ∣ fourBinaryResidue (m : ℤ) (n : ℤ) (R : ℤ) r)
    (x : QuadQuintBranchIndex)
    (hx : quadExp2 p (2*m) (4*m) n (3*n) x=2*((p*N+R : ℕ) : ℤ)) :
    2*(m : ℤ)^2+(n : ℤ)^2 ∣ fourBinaryNum (m : ℤ) (n : ℤ) r (quadZ x) := by
  have he := quadExp2_energy p (2*m) (4*m) n (3*n) x
  rw [hx] at he
  simp only [fourEnergy,fourDot,fourSum,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
    Nat.cast_mul,Nat.cast_ofNat] at he
  have hem := congrArg (fun t : ℤ => (t : ZMod p)) he
  push_cast at hem
  simp only [ZMod.natCast_self,zero_mul,zero_add] at hem
  have hz : fourDot (fourBinaryV (m : ZMod p) (n : ZMod p))
      (fun i => (quadZ x i : ZMod p))=(R : ZMod p) := by
    apply ((ZMod.isUnit_iff_coprime 6 p).mpr hp6).mul_left_cancel
    dsimp [fourDot,fourBinaryV]
    linear_combination -hem
  have hnorm : 2*(m : ZMod p)^2+(n : ZMod p)^2=0 := by
    simpa using (congrArg (fun t : ℕ => (t : ZMod p)) hp).symm
  have ha : fourBinaryResidue (m : ZMod p) (n : ZMod p) (R : ZMod p) r=0 := by
    simpa only [fourBinaryResidue_cast,Int.cast_natCast] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hR
  have hm : IsUnit (m : ZMod p) := (ZMod.isUnit_iff_coprime m p).mpr hpm
  have hznum := fourBinary_num_zero (m : ZMod p) (n : ZMod p) (R : ZMod p) r _ hm hnorm hz ha
  have hd : (p : ℤ) ∣ fourBinaryNum (m : ℤ) (n : ℤ) r (quadZ x) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa only [fourBinaryNum_cast,Int.cast_natCast] using hznum
  simpa only [hp,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hd

/-- Actual infinite-product cancellation in a quadratic norm family different from `m²+n²`. -/
theorem coeff_fourBinary_zero (p m n R N : ℕ) (r : Bool)
    (hp : p=2*m^2+n^2) (hmpos : 0<m) (hnpos : 0<n)
    (hm8 : 8*m<p) (hn6 : 6*n<p) (h3 : 3 ∣ m) (h5 : 5 ∣ n)
    (hcop : Nat.Coprime (30*m) p)
    (hR : (p : ℤ) ∣ fourBinaryResidue (m : ℤ) (n : ℤ) (R : ℤ) r) :
    coeff (p*N+R) (quintupleSpecialized p (2*m) * quintupleSpecialized p (4*m) *
      quintupleSpecialized p n * quintupleSpecialized p (3*n))=0 := by
  have hp0 : 2*(m : ℤ)^2+(n : ℤ)^2 ≠ 0 := by positivity
  have hp6 : Nat.Coprime 6 p := hcop.coprime_dvd_left ⟨5*m,by ring⟩
  have hpm : Nat.Coprime m p := hcop.coprime_dvd_left ⟨30,by ring⟩
  have hp15 : Nat.Coprime p 15 := (hcop.coprime_dvd_left ⟨2*m,by ring⟩).symm
  have hu : IsUnit (2*((m : ℤ) : ZMod 15)^2+((n : ℤ) : ZMod 15)^2) := by
    have h := (ZMod.isUnit_iff_coprime p 15).mpr hp15
    simpa only [hp,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Int.cast_natCast] using h
  have hm3 : (3 : ℤ) ∣ (m : ℤ) := by exact_mod_cast h3
  have hn5 : (5 : ℤ) ∣ (n : ℤ) := by exact_mod_cast h5
  have hd := fourBinary_num_dvd_of_exp p m n R N r hp hp6 hpm hR
  have hpint : (p : ℤ)=2*(m : ℤ)^2+(n : ℤ)^2 := by exact_mod_cast hp
  have hv : (![((2*m : ℕ) : ℤ),((4*m : ℕ) : ℤ),(n : ℤ),((3*n : ℕ) : ℤ)] : QuadIntPoint)=
      fourBinaryV (m : ℤ) (n : ℤ) := by simp [fourBinaryV]
  apply coeff_quad_eq_zero_of_expInvolution p (2*m) (4*m) n (3*n) (p*N+R)
    (fourBinaryPartner (m : ℤ) (n : ℤ) r)
    (by omega) (by omega) (by omega) (by omega) hnpos (by omega) (by omega) (by omega)
  · intro x hx
    exact fourBinary_bits_weight r x _
  · intro x hx
    have he := fourBinary_partner_energy (m : ℤ) (n : ℤ) r x hm3 hn5 hu (hd x hx)
    have he1 := quadExp2_energy p (2*m) (4*m) n (3*n) x
    have he2 := quadExp2_energy p (2*m) (4*m) n (3*n) (fourBinaryPartner (m : ℤ) (n : ℤ) r x)
    rw [hpint,hv] at he1 he2
    omega
  · intro x hx
    exact fourBinary_partner_involutive (m : ℤ) (n : ℤ) r x hp0 hm3 hn5 hu (hd x hx)

/-- A concrete example outside the previous sum-of-two-squares family. -/
theorem coeff_fourBinary_43 (R N : ℕ) (hR : R=19 ∨ R=32) :
    coeff (43*N+R) (quintupleSpecialized 43 6 * quintupleSpecialized 43 12 *
      quintupleSpecialized 43 5 * quintupleSpecialized 43 15)=0 := by
  rcases hR with rfl | rfl
  · exact coeff_fourBinary_zero 43 3 5 19 N true (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [fourBinaryResidue])
  · exact coeff_fourBinary_zero 43 3 5 32 N false (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [fourBinaryResidue])

/-- The new base modulus cannot have the shape required by the earlier family. -/
theorem fortyThree_not_sum_two_squares : ¬ ∃ m n : ℕ, 43=m^2+n^2 := by
  rintro ⟨m,n,h⟩
  have hm : m ≤ 6 := by nlinarith
  have hn : n ≤ 6 := by nlinarith
  interval_cases m <;> interval_cases n <;> norm_num at h

end Ramanujan.MultiQuintuple
