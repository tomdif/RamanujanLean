import RamanujanTau.MultiQuintupleFourPlaneAlgebra

/-!
# Two-parameter four-factor cancellation

For `p = m² + n²`, the four factors have indices `m-n,n,m,m+n`.
Four explicit residue polynomials give sufficient conditions for an entire
coefficient progression to vanish. This is not a converse classification.
-/
namespace Ramanujan.MultiQuintuple
open PowerSeries
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def fourPlaneK (m n : ℤ) (r : Fin 4) (z : QuadIntPoint) : ℤ :=
  fourPlaneNum m n r z / (m^2+n^2)

def fourPlanePartner (m n : ℤ) (r : Fin 4) (x : QuadQuintBranchIndex) :
    QuadQuintBranchIndex :=
  quadAssemble (fourPlaneBits r (quadBits x)) (fun i =>
    (fourPlaneRaw m n r (quadZ x) (fourPlaneK m n r (quadZ x)) i-
      3*(if fourPlaneBits r (quadBits x) i then 1 else 0))/9)

lemma fourPlaneK_spec (m n : ℤ) (r : Fin 4) (z : QuadIntPoint)
    (hd : m^2+n^2 ∣ fourPlaneNum m n r z) :
    (m^2+n^2)*fourPlaneK m n r z=fourPlaneNum m n r z := by
  simpa [fourPlaneK,mul_comm] using Int.ediv_mul_cancel hd

lemma fourPlane_raw_branch_dvd (m n : ℤ) (r : Fin 4) (x : QuadQuintBranchIndex)
    (k : ℤ) (h9 : (9 : ℤ) ∣ m+n) (hn : IsUnit (n : ZMod 9))
    (hk : (m^2+n^2)*k=fourPlaneNum m n r (quadZ x)) (i : Fin 4) :
    (9 : ℤ) ∣ fourPlaneRaw m n r (quadZ x) k i-
      3*(if fourPlaneBits r (quadBits x) i then 1 else 0) := by
  have hs : (m : ZMod 9)+(n : ZMod 9)=0 := by
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (m+n) 9).mpr h9
  have hk9 : ((m : ZMod 9)^2+(n : ZMod 9)^2)*(k : ZMod 9)=
      fourPlaneNum (m : ZMod 9) (n : ZMod 9) r (fun i => (quadZ x i : ZMod 9)) := by
    simpa only [Int.cast_mul,Int.cast_add,Int.cast_pow,fourPlaneNum_cast] using
      congrArg (fun t : ℤ => (t : ZMod 9)) hk
  have hm := fourPlane_raw_mod_nine (m : ZMod 9) (n : ZMod 9) hn hs r _ (k : ZMod 9) hk9 i
  have hd : (9 : ℤ) ∣ fourPlaneRaw m n r (quadZ x) k i-3*fourPlaneZRule r (quadZ x) i := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mp
    simpa only [Int.cast_sub,Int.cast_mul,Int.cast_ofNat,fourPlaneRaw_cast,
      fourPlaneZRule_cast,sub_eq_zero] using hm
  have hb := fourPlane_rule_branch r x i
  convert dvd_add hd hb using 1 <;> ring

lemma quadZ_assemble (b : Fin 4 → Bool) (z : QuadIntPoint) (i : Fin 4) :
    quadZ (quadAssemble b z) i=3*z i+(if b i then 1 else 0) := by
  fin_cases i <;> rfl

lemma fourPlane_partner_coords (m n : ℤ) (r : Fin 4) (x : QuadQuintBranchIndex)
    (h9 : (9 : ℤ) ∣ m+n) (hn : IsUnit (n : ZMod 9))
    (hd : m^2+n^2 ∣ fourPlaneNum m n r (quadZ x)) :
    ∀ i, 3*quadZ (fourPlanePartner m n r x) i=
      fourPlaneRaw m n r (quadZ x) (fourPlaneK m n r (quadZ x)) i := by
  intro i
  have hh := Int.ediv_mul_cancel
    (fourPlane_raw_branch_dvd m n r x _ h9 hn (fourPlaneK_spec m n r _ hd) i)
  simp only [fourPlanePartner,quadZ_assemble]
  linarith

lemma fourPlane_partner_energy (m n : ℤ) (r : Fin 4) (x : QuadQuintBranchIndex)
    (h9 : (9 : ℤ) ∣ m+n) (hn : IsUnit (n : ZMod 9))
    (hd : m^2+n^2 ∣ fourPlaneNum m n r (quadZ x)) :
    fourEnergy (m^2+n^2) (fourV m n) (quadZ (fourPlanePartner m n r x))=
      fourEnergy (m^2+n^2) (fourV m n) (quadZ x) := by
  have hz := funext (fourPlane_partner_coords m n r x h9 hn hd)
  have he := fourPlane_energy_raw m n r (quadZ x) _ (fourPlaneK_spec m n r _ hd)
  rw [← hz,fourEnergyTriple_scale] at he
  omega

lemma fourPlane_partner_involutive (m n : ℤ) (r : Fin 4) (x : QuadQuintBranchIndex)
    (hp : m^2+n^2 ≠ 0) (h9 : (9 : ℤ) ∣ m+n) (hn : IsUnit (n : ZMod 9))
    (hd : m^2+n^2 ∣ fourPlaneNum m n r (quadZ x)) :
    fourPlanePartner m n r (fourPlanePartner m n r x)=x := by
  have hk := fourPlaneK_spec m n r _ hd
  have hz := fourPlane_partner_coords m n r x h9 hn hd
  have hnum := fourPlane_num_next m n r _ _ _ hk hz
  have hd' : m^2+n^2 ∣ fourPlaneNum m n r (quadZ (fourPlanePartner m n r x)) :=
    ⟨_,hnum⟩
  have hnext : fourPlaneK m n r (quadZ (fourPlanePartner m n r x))=
      fourPlaneNextK r (fourPlaneK m n r (quadZ x)) := by
    simp only [fourPlaneK] at hnum ⊢
    rw [hnum]
    exact Int.mul_ediv_cancel_left _ hp
  have hz' := fourPlane_partner_coords m n r (fourPlanePartner m n r x) h9 hn hd'
  simp only [hnext] at hz'
  have hback := fourPlane_raw_involutive m n r _ _ _ hz
  apply quadZ_injective
  funext i
  have hi := hz' i
  rw [hback i] at hi
  omega


lemma fourPlane_num_dvd_of_exp (p m n R N : ℕ) (r : Fin 4)
    (hp : p=m^2+n^2) (hnm : n<m) (hp6 : Nat.Coprime 6 p) (hpn : Nat.Coprime n p)
    (hR : (p : ℤ) ∣ fourPlaneResidueNum (m : ℤ) (n : ℤ) (R : ℤ) r)
    (x : QuadQuintBranchIndex)
    (hx : quadExp2 p (m-n) n m (m+n) x=2*((p*N+R : ℕ) : ℤ)) :
    (m : ℤ)^2+(n : ℤ)^2 ∣ fourPlaneNum (m : ℤ) (n : ℤ) r (quadZ x) := by
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
  have ha : fourPlaneResidueNum (m : ZMod p) (n : ZMod p) (R : ZMod p) r=0 := by
    simpa only [fourPlaneResidueNum_cast,Int.cast_natCast] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hR
  have hn : IsUnit (n : ZMod p) := (ZMod.isUnit_iff_coprime n p).mpr hpn
  have hznum := fourPlane_num_zero (m : ZMod p) (n : ZMod p) (R : ZMod p) r _ hn hnorm hz ha
  have hd : (p : ℤ) ∣ fourPlaneNum (m : ℤ) (n : ℤ) r (quadZ x) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa only [fourPlaneNum_cast,Int.cast_natCast] using hznum
  simpa only [hp,Nat.cast_add,Nat.cast_pow] using hd

/-- An unconditional sufficient theorem for all four progressions in the two-parameter family. -/
theorem coeff_fourPlane_eq_zero (p m n R N : ℕ) (r : Fin 4)
    (hp : p=m^2+n^2) (hnpos : 0<n) (hnm : n<m) (hbound : 2*(m+n)<p)
    (h9 : 9 ∣ m+n) (hn9 : Nat.Coprime n 9)
    (hp6 : Nat.Coprime 6 p) (hpn : Nat.Coprime n p)
    (hR : (p : ℤ) ∣ fourPlaneResidueNum (m : ℤ) (n : ℤ) (R : ℤ) r) :
    coeff (p*N+R) (quintupleSpecialized p (m-n) * quintupleSpecialized p n *
      quintupleSpecialized p m * quintupleSpecialized p (m+n))=0 := by
  have hmpos : 0<m := lt_trans hnpos hnm
  have hp0 : (m : ℤ)^2+(n : ℤ)^2 ≠ 0 := by positivity
  have hs : (9 : ℤ) ∣ (m : ℤ)+(n : ℤ) := by exact_mod_cast h9
  have hnunit : IsUnit ((n : ℤ) : ZMod 9) := by
    simpa using (ZMod.isUnit_iff_coprime n 9).mpr hn9
  have hd := fourPlane_num_dvd_of_exp p m n R N r hp hnm hp6 hpn hR
  have hpint : (p : ℤ)=(m : ℤ)^2+(n : ℤ)^2 := by exact_mod_cast hp
  have hv : (![((m-n : ℕ) : ℤ),(n : ℤ),(m : ℤ),((m+n : ℕ) : ℤ)] : QuadIntPoint)=
      fourV (m : ℤ) (n : ℤ) := by
    simp [fourV,Nat.cast_sub (Nat.le_of_lt hnm)]
  apply coeff_quad_eq_zero_of_expInvolution p (m-n) n m (m+n) (p*N+R)
    (fourPlanePartner (m : ℤ) (n : ℤ) r)
    (by omega) (by omega) hnpos (by omega) hmpos (by omega) (by omega) hbound
  · intro x hx
    exact fourPlane_bits_weight r x _
  · intro x hx
    have he := fourPlane_partner_energy (m : ℤ) (n : ℤ) r x hs hnunit (hd x hx)
    have he1 := quadExp2_energy p (m-n) n m (m+n) x
    have he2 := quadExp2_energy p (m-n) n m (m+n) (fourPlanePartner (m : ℤ) (n : ℤ) r x)
    rw [hpint,hv] at he1 he2
    omega
  · intro x hx
    exact fourPlane_partner_involutive (m : ℤ) (n : ℤ) r x hp0 hs hnunit (hd x hx)

/-- For prime moduli, the two coprimality conditions modulo `p` are automatic. -/
theorem coeff_fourPlane_prime_eq_zero (p m n R N : ℕ) (r : Fin 4)
    (hprime : p.Prime) (hp : p=m^2+n^2) (hnpos : 0<n) (hnm : n<m)
    (hbound : 2*(m+n)<p) (h9 : 9 ∣ m+n) (hn9 : Nat.Coprime n 9)
    (hR : (p : ℤ) ∣ fourPlaneResidueNum (m : ℤ) (n : ℤ) (R : ℤ) r) :
    coeff (p*N+R) (quintupleSpecialized p (m-n) * quintupleSpecialized p n *
      quintupleSpecialized p m * quintupleSpecialized p (m+n))=0 := by
  apply coeff_fourPlane_eq_zero p m n R N r hp hnpos hnm hbound h9 hn9 _ _ hR
  · exact (hprime.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))).symm
  · exact (hprime.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt hnpos (by omega))).symm

/-- The modulus-53 example is now an infinite coefficient theorem. -/
theorem coeff_fourPlane_53 (R N : ℕ) (hR : R=29 ∨ R=31 ∨ R=36 ∨ R=38) :
    coeff (53*N+R) (quintupleSpecialized 53 5 * quintupleSpecialized 53 2 *
      quintupleSpecialized 53 7 * quintupleSpecialized 53 9)=0 := by
  rcases hR with rfl | rfl | rfl | rfl
  · exact coeff_fourPlane_eq_zero 53 7 2 _ N 0 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [fourPlaneResidueNum])
  · exact coeff_fourPlane_eq_zero 53 7 2 _ N 1 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [fourPlaneResidueNum])
  · exact coeff_fourPlane_eq_zero 53 7 2 _ N 2 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [fourPlaneResidueNum])
  · exact coeff_fourPlane_eq_zero 53 7 2 _ N 3 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [fourPlaneResidueNum])

end Ramanujan.MultiQuintuple
