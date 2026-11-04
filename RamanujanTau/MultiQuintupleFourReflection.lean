import RamanujanTau.MultiQuintupleFourReflectionAlgebra

/-!
# Four congruence families of four-factor vanishing

The sixteen reflections give sufficient vanishing criteria when one of
`m`, `n`, `m-n`, or `m+n` is divisible by nine. These are actual infinite-product
coefficient theorems. A universal converse is not asserted.
-/
namespace Ramanujan.MultiQuintuple
open PowerSeries
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def fourReflectionK (m n : ℤ) (b : Fin 4) (z : QuadIntPoint) : ℤ :=
  fourLongNum m n b z/(m^2+n^2)

def fourReflectionPartner (m n : ℤ) (a b : Fin 4) (x : QuadQuintBranchIndex) :
    QuadQuintBranchIndex :=
  quadAssemble (fourPlaneBits (fourReflectionBranch a) (quadBits x)) (fun i =>
    (fourReflectionRaw m n a b (quadZ x) (fourReflectionK m n b (quadZ x)) i-
      3*(if fourPlaneBits (fourReflectionBranch a) (quadBits x) i then 1 else 0))/9)

lemma fourReflectionK_spec (m n : ℤ) (b : Fin 4) (z : QuadIntPoint)
    (hd : m^2+n^2 ∣ fourLongNum m n b z) :
    (m^2+n^2)*fourReflectionK m n b z=fourLongNum m n b z := by
  simpa [fourReflectionK,mul_comm] using Int.ediv_mul_cancel hd

lemma fourReflection_raw_branch_dvd (m n : ℤ) (a b : Fin 4) (x : QuadQuintBranchIndex)
    (k : ℤ) (h9 : (9 : ℤ) ∣ fourReflectionCondition m n a b)
    (hp9 : IsUnit ((m : ZMod 9)^2+(n : ZMod 9)^2))
    (hk : (m^2+n^2)*k=fourLongNum m n b (quadZ x)) (i : Fin 4) :
    (9 : ℤ) ∣ fourReflectionRaw m n a b (quadZ x) k i-
      3*(if fourPlaneBits (fourReflectionBranch a) (quadBits x) i then 1 else 0) := by
  have hs : fourReflectionCondition (m : ZMod 9) (n : ZMod 9) a b=0 := by
    simpa only [fourReflectionCondition_cast] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mpr h9
  have hk9 : ((m : ZMod 9)^2+(n : ZMod 9)^2)*(k : ZMod 9)=
      fourLongNum (m : ZMod 9) (n : ZMod 9) b (fun i => (quadZ x i : ZMod 9)) := by
    simpa only [Int.cast_mul,Int.cast_add,Int.cast_pow,fourLongNum_cast] using
      congrArg (fun t : ℤ => (t : ZMod 9)) hk
  have hd : (9 : ℤ) ∣ fourReflectionRaw m n a b (quadZ x) k i-
      3*fourPlaneZRule (fourReflectionBranch a) (quadZ x) i := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mp
    have hh := fourReflection_raw_mod_nine (m : ZMod 9) (n : ZMod 9) a b hp9 hs
      (fun j => (quadZ x j : ZMod 9)) (k : ZMod 9) hk9 i
    simpa only [Int.cast_sub,Int.cast_mul,Int.cast_ofNat,fourReflectionRaw_cast,
      fourPlaneZRule_cast,sub_eq_zero] using hh
  have hb := fourPlane_rule_branch (fourReflectionBranch a) x i
  convert dvd_add hd hb using 1
  ring

lemma fourReflection_partner_coords (m n : ℤ) (a b : Fin 4) (x : QuadQuintBranchIndex)
    (h9 : (9 : ℤ) ∣ fourReflectionCondition m n a b)
    (hp9 : IsUnit ((m : ZMod 9)^2+(n : ZMod 9)^2))
    (hd : m^2+n^2 ∣ fourLongNum m n b (quadZ x)) :
    ∀ i, 3*quadZ (fourReflectionPartner m n a b x) i=
      fourReflectionRaw m n a b (quadZ x) (fourReflectionK m n b (quadZ x)) i := by
  intro i
  have hh := Int.ediv_mul_cancel (fourReflection_raw_branch_dvd m n a b x _ h9 hp9
    (fourReflectionK_spec m n b _ hd) i)
  simp only [fourReflectionPartner,quadZ_assemble]
  linarith

lemma fourReflection_partner_energy (m n : ℤ) (a b : Fin 4) (x : QuadQuintBranchIndex)
    (h9 : (9 : ℤ) ∣ fourReflectionCondition m n a b)
    (hp9 : IsUnit ((m : ZMod 9)^2+(n : ZMod 9)^2))
    (hd : m^2+n^2 ∣ fourLongNum m n b (quadZ x)) :
    fourEnergy (m^2+n^2) (fourV m n) (quadZ (fourReflectionPartner m n a b x))=
      fourEnergy (m^2+n^2) (fourV m n) (quadZ x) := by
  have hz := funext (fourReflection_partner_coords m n a b x h9 hp9 hd)
  have he := fourReflection_energy_raw m n a b (quadZ x) _ (fourReflectionK_spec m n b _ hd)
  rw [← hz,fourEnergyTriple_scale] at he
  omega

lemma fourReflection_partner_involutive (m n : ℤ) (a b : Fin 4) (x : QuadQuintBranchIndex)
    (hp : m^2+n^2 ≠ 0) (h9 : (9 : ℤ) ∣ fourReflectionCondition m n a b)
    (hp9 : IsUnit ((m : ZMod 9)^2+(n : ZMod 9)^2))
    (hd : m^2+n^2 ∣ fourLongNum m n b (quadZ x)) :
    fourReflectionPartner m n a b (fourReflectionPartner m n a b x)=x := by
  have hk := fourReflectionK_spec m n b _ hd
  have hz := fourReflection_partner_coords m n a b x h9 hp9 hd
  have hnum := fourReflection_num_next m n a b _ _ _ hk hz
  have hd' : m^2+n^2 ∣ fourLongNum m n b (quadZ (fourReflectionPartner m n a b x)) :=
    ⟨_,hnum⟩
  have hnext : fourReflectionK m n b (quadZ (fourReflectionPartner m n a b x))=
      -fourReflectionK m n b (quadZ x) := by
    simp only [fourReflectionK] at hnum ⊢
    rw [hnum]
    exact Int.mul_ediv_cancel_left _ hp
  have hz' := fourReflection_partner_coords m n a b (fourReflectionPartner m n a b x) h9 hp9 hd'
  simp only [hnext] at hz'
  have hback := fourReflection_raw_involutive m n a b _ _ _ hz
  apply quadZ_injective
  funext i
  have hi := hz' i
  rw [hback i] at hi
  omega

lemma fourReflection_num_dvd_of_exp (p m n R N : ℕ) (b : Fin 4)
    (hp : p=m^2+n^2) (hnm : n<m) (hp6 : Nat.Coprime 6 p) (hpn : Nat.Coprime n p)
    (hR : (p : ℤ) ∣ fourReflectionResidue (m : ℤ) (n : ℤ) (R : ℤ) b)
    (x : QuadQuintBranchIndex)
    (hx : quadExp2 p (m-n) n m (m+n) x=2*((p*N+R : ℕ) : ℤ)) :
    (m : ℤ)^2+(n : ℤ)^2 ∣ fourLongNum (m : ℤ) (n : ℤ) b (quadZ x) := by
  have he := quadExp2_energy p (m-n) n m (m+n) x
  rw [hx] at he
  simp only [fourEnergy,fourDot,fourSum,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
    Nat.cast_sub (Nat.le_of_lt hnm),Nat.cast_add] at he
  have hem := congrArg (fun t : ℤ => (t : ZMod p)) he
  push_cast at hem
  simp only [ZMod.natCast_self,zero_mul,zero_add] at hem
  have hz : fourDot (fourV (m : ZMod p) (n : ZMod p))
      (fun i => (quadZ x i : ZMod p))=(R : ZMod p) := by
    apply ((ZMod.isUnit_iff_coprime 6 p).mpr hp6).mul_left_cancel
    simp only [fourDot,fourV,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
    linear_combination -hem
  have hnorm : (m : ZMod p)^2+(n : ZMod p)^2=0 := by
    simpa using (congrArg (fun t : ℕ => (t : ZMod p)) hp).symm
  have ha : fourReflectionResidue (m : ZMod p) (n : ZMod p) (R : ZMod p) b=0 := by
    simpa only [fourReflectionResidue_cast,Int.cast_natCast] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hR
  have hn : IsUnit (n : ZMod p) := (ZMod.isUnit_iff_coprime n p).mpr hpn
  have hznum := fourReflection_num_zero (m : ZMod p) (n : ZMod p) (R : ZMod p) b _ hn hnorm hz ha
  have hd : (p : ℤ) ∣ fourLongNum (m : ℤ) (n : ℤ) b (quadZ x) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa only [fourLongNum_cast,Int.cast_natCast] using hznum
  simpa only [hp,Nat.cast_add,Nat.cast_pow] using hd

/-- A sufficient actual-coefficient theorem for each of the sixteen reflections. -/
theorem coeff_fourReflection_eq_zero (p m n R N : ℕ) (a b : Fin 4)
    (hp : p=m^2+n^2) (hnpos : 0<n) (hnm : n<m) (hbound : 2*(m+n)<p)
    (hp6 : Nat.Coprime 6 p) (hpn : Nat.Coprime n p)
    (h9 : (9 : ℤ) ∣ fourReflectionCondition (m : ℤ) (n : ℤ) a b)
    (hR : (p : ℤ) ∣ fourReflectionResidue (m : ℤ) (n : ℤ) (R : ℤ) b) :
    coeff (p*N+R) (quintupleSpecialized p (m-n) * quintupleSpecialized p n *
      quintupleSpecialized p m * quintupleSpecialized p (m+n))=0 := by
  have hmpos : 0<m := lt_trans hnpos hnm
  have hp0 : (m : ℤ)^2+(n : ℤ)^2 ≠ 0 := by positivity
  have hp3 : Nat.Coprime 3 p := hp6.coprime_dvd_left (by decide)
  have hp9 : Nat.Coprime p 9 := by simpa using hp3.symm.pow_right 2
  have hpunit : IsUnit (((m : ℤ) : ZMod 9)^2+((n : ℤ) : ZMod 9)^2) := by
    have hu := (ZMod.isUnit_iff_coprime p 9).mpr hp9
    simpa only [hp,Nat.cast_add,Nat.cast_pow,Int.cast_natCast] using hu
  have hd := fourReflection_num_dvd_of_exp p m n R N b hp hnm hp6 hpn hR
  have hpint : (p : ℤ)=(m : ℤ)^2+(n : ℤ)^2 := by exact_mod_cast hp
  have hv : (![((m-n : ℕ) : ℤ),(n : ℤ),(m : ℤ),((m+n : ℕ) : ℤ)] : QuadIntPoint)=
      fourV (m : ℤ) (n : ℤ) := by
    simp [fourV,Nat.cast_sub (Nat.le_of_lt hnm)]
  apply coeff_quad_eq_zero_of_expInvolution p (m-n) n m (m+n) (p*N+R)
    (fourReflectionPartner (m : ℤ) (n : ℤ) a b)
    (by omega) (by omega) hnpos (by omega) hmpos (by omega) (by omega) hbound
  · intro x hx
    exact fourPlane_bits_weight (fourReflectionBranch a) x _
  · intro x hx
    have he := fourReflection_partner_energy (m : ℤ) (n : ℤ) a b x h9 hpunit (hd x hx)
    have he1 := quadExp2_energy p (m-n) n m (m+n) x
    have he2 := quadExp2_energy p (m-n) n m (m+n) (fourReflectionPartner (m : ℤ) (n : ℤ) a b x)
    rw [hpint,hv] at he1 he2
    omega
  · intro x hx
    exact fourReflection_partner_involutive (m : ℤ) (n : ℤ) a b x hp0 h9 hpunit (hd x hx)



lemma fourReflection_condition_exists (m n : ℤ) (b : Fin 4)
    (h9 : (9 : ℤ) ∣ m ∨ (9 : ℤ) ∣ n ∨ (9 : ℤ) ∣ m-n ∨ (9 : ℤ) ∣ m+n) :
    ∃ a : Fin 4, (9 : ℤ) ∣ fourReflectionCondition m n a b := by
  rcases h9 with h | h | h | h
  · fin_cases b
    · exact ⟨2, by simpa [fourReflectionCondition] using h⟩
    · exact ⟨3, by simpa [fourReflectionCondition] using h⟩
    · exact ⟨1, by simpa [fourReflectionCondition] using h⟩
    · exact ⟨0, by simpa [fourReflectionCondition] using h⟩
  · fin_cases b
    · exact ⟨3, by simpa [fourReflectionCondition] using h⟩
    · exact ⟨2, by simpa [fourReflectionCondition] using h⟩
    · exact ⟨0, by simpa [fourReflectionCondition] using h⟩
    · exact ⟨1, by simpa [fourReflectionCondition] using h⟩
  · fin_cases b
    · exact ⟨1, by simpa [fourReflectionCondition] using h⟩
    · exact ⟨0, by simpa [fourReflectionCondition] using h⟩
    · exact ⟨3, by simpa [fourReflectionCondition] using h⟩
    · exact ⟨2, by simpa [fourReflectionCondition] using h⟩
  · fin_cases b
    · exact ⟨0, by simpa [fourReflectionCondition] using h⟩
    · exact ⟨1, by simpa [fourReflectionCondition] using h⟩
    · exact ⟨2, by simpa [fourReflectionCondition] using h⟩
    · exact ⟨3, by simpa [fourReflectionCondition] using h⟩

/-- Any one of four congruences supplies all four long-direction residue criteria. -/
theorem coeff_fourReflection_family_zero (p m n R N : ℕ) (b : Fin 4)
    (hp : p=m^2+n^2) (hnpos : 0<n) (hnm : n<m) (hbound : 2*(m+n)<p)
    (hp6 : Nat.Coprime 6 p) (hpn : Nat.Coprime n p)
    (h9 : (9 : ℤ) ∣ (m : ℤ) ∨ (9 : ℤ) ∣ (n : ℤ) ∨
      (9 : ℤ) ∣ (m : ℤ)-(n : ℤ) ∨ (9 : ℤ) ∣ (m : ℤ)+(n : ℤ))
    (hR : (p : ℤ) ∣ fourReflectionResidue (m : ℤ) (n : ℤ) (R : ℤ) b) :
    coeff (p*N+R) (quintupleSpecialized p (m-n) * quintupleSpecialized p n *
      quintupleSpecialized p m * quintupleSpecialized p (m+n))=0 := by
  obtain ⟨a,ha⟩ := fourReflection_condition_exists (m : ℤ) (n : ℤ) b h9
  exact coeff_fourReflection_eq_zero p m n R N a b hp hnpos hnm hbound hp6 hpn ha hR

/-- Prime-modulus version with automatic coprimality modulo `p`. -/
theorem coeff_fourReflection_prime_zero (p m n R N : ℕ) (b : Fin 4)
    (hprime : p.Prime) (hp : p=m^2+n^2) (hnpos : 0<n) (hnm : n<m)
    (hbound : 2*(m+n)<p)
    (h9 : (9 : ℤ) ∣ (m : ℤ) ∨ (9 : ℤ) ∣ (n : ℤ) ∨
      (9 : ℤ) ∣ (m : ℤ)-(n : ℤ) ∨ (9 : ℤ) ∣ (m : ℤ)+(n : ℤ))
    (hR : (p : ℤ) ∣ fourReflectionResidue (m : ℤ) (n : ℤ) (R : ℤ) b) :
    coeff (p*N+R) (quintupleSpecialized p (m-n) * quintupleSpecialized p n *
      quintupleSpecialized p m * quintupleSpecialized p (m+n))=0 := by
  apply coeff_fourReflection_family_zero p m n R N b hp hnpos hnm hbound _ _ h9 hR
  · exact (hprime.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))).symm
  · exact (hprime.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt hnpos (by omega))).symm

/-- All four zero progressions at 97 are now actual infinite-product theorems. -/
theorem coeff_fourReflection_97 (R N : ℕ) (hR : R=9 ∨ R=13 ∨ R=55 ∨ R=64) :
    coeff (97*N+R) (quintupleSpecialized 97 5 * quintupleSpecialized 97 4 *
      quintupleSpecialized 97 9 * quintupleSpecialized 97 13)=0 := by
  rcases hR with rfl | rfl | rfl | rfl
  · exact coeff_fourReflection_family_zero 97 9 4 _ N 3
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [fourReflectionResidue])
  · exact coeff_fourReflection_family_zero 97 9 4 _ N 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [fourReflectionResidue])
  · exact coeff_fourReflection_family_zero 97 9 4 _ N 0
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [fourReflectionResidue])
  · exact coeff_fourReflection_family_zero 97 9 4 _ N 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [fourReflectionResidue])

end Ramanujan.MultiQuintuple
