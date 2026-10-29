import RamanujanTau.TheoremA.BinaryFiltration
import RamanujanTau.TheoremA.ThetaCycle

/-!
# The weight-six theta-cycle theorem for the integral level-six model

The proved Hasse divisibility criterion supplies all minimum-weight step
and drop laws. For a nonzero series represented at weight p−3, U_p f = 0
therefore forces theta⁴ f to have a homogeneous representative of degree six.
No filtration hypothesis is left in this theorem. BinaryOrdinarity applies
the proved full weight-six obstruction. The newform sign identification
and half-integral correspondence remain separate obligations.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA

variable {F : Type*} [Field F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]

theorem BinaryRep.theta_pow (hp5 : 5 ≤ p) {n : ℕ} {f : PowerSeries F}
    (hf : BinaryRep f n) (i : ℕ) :
    BinaryRep ((TheoremA.theta ^ i) f) (n + i * ((p - 1) / 2 + 1)) := by
  induction i with
  | zero => simpa using hf
  | succ i ih =>
    have h := ih.theta hp5
    rw [pow_succ', Module.End.mul_apply]
    convert h using 1
    ring

omit hp in
lemma theta_pow_halfWeight_class (n i : ℕ) :
    (n + i * ((p - 1) / 2 + 1)) % ((p - 1) / 2) =
      (n + i) % ((p - 1) / 2) := by
  simp [Nat.mul_add, Nat.add_mod]

/-- Minimum half-weight in the class that theta^i must occupy. -/
noncomputable def binaryCycleHalfWeight (p n : ℕ) (f : PowerSeries F) (i : ℕ) : ℕ :=
  binaryHalfFiltration p (n + i) ((theta ^ i) f)

theorem binaryCycleHalfWeight_rep (hp5 : 5 ≤ p) {n : ℕ} {f : PowerSeries F}
    (hf : BinaryRep f n) (i : ℕ) :
    BinaryRep ((theta ^ i) f) (binaryCycleHalfWeight p n f i) :=
  (binaryHalfFiltration_spec (theta_pow_halfWeight_class (p := p) n i) (hf.theta_pow hp5 i)).2

theorem binaryCycleHalfWeight_step (hp5 : 5 ≤ p) {n : ℕ} {f : PowerSeries F}
    (hf : BinaryRep f n) (i : ℕ) :
    ∃ d : ℕ, binaryCycleHalfWeight p n f i + (p - 1) / 2 + 1 =
      binaryCycleHalfWeight p n f (i + 1) + ((p - 1) / 2) * d := by
  have h := binaryHalfFiltration_theta_step hp5
    (theta_pow_halfWeight_class (p := p) n i) (hf.theta_pow hp5 i)
  simpa only [binaryCycleHalfWeight, Nat.add_assoc, pow_succ', Module.End.mul_apply] using h

theorem binaryCycleHalfWeight_no_drop (hp5 : 5 ≤ p) {n : ℕ} {f : PowerSeries F}
    (hf : BinaryRep f n) (i : ℕ) (hfi : (theta ^ i) f ≠ 0)
    (hk : ¬ (p : ℤ) ∣ (2 * binaryCycleHalfWeight p n f i : ℕ)) :
    binaryCycleHalfWeight p n f (i + 1) = binaryCycleHalfWeight p n f i + (p - 1) / 2 + 1 := by
  have hkF : (2 * binaryCycleHalfWeight p n f i : F) ≠ 0 := by
    intro h
    have hd : p ∣ 2 * binaryCycleHalfWeight p n f i :=
      (CharP.cast_eq_zero_iff F p _).mp (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using h)
    exact hk (Int.natCast_dvd_natCast.mpr hd)
  have h := binaryHalfFiltration_theta_eq hp5
    (theta_pow_halfWeight_class (p := p) n i) (hf.theta_pow hp5 i) hfi hkF
  simpa only [binaryCycleHalfWeight, Nat.add_assoc, pow_succ', Module.End.mul_apply] using h

omit hp [CharP F p] in
theorem binaryCycleHalfWeight_zero {n : ℕ} {f : PowerSeries F}
    (hf : BinaryRep f n) (hn : n < (p - 1) / 2) :
    binaryCycleHalfWeight p n f 0 = n := by
  simpa only [binaryCycleHalfWeight, Nat.add_zero, pow_zero, Module.End.one_apply] using
    binaryHalfFiltration_eq_of_lt (p := p) hf hn

theorem binaryCycleHalfWeight_closed (hp5 : 5 ≤ p) (n : ℕ) (f : PowerSeries F)
    (hu : BoylanWebb.U p f = 0) :
    binaryCycleHalfWeight p n f (p - 1) = binaryCycleHalfWeight p n f 0 := by
  have hcycle := (U_eq_zero_iff_theta_cycle f).mp hu
  simp only [binaryCycleHalfWeight, hcycle, Nat.add_zero, pow_zero, Module.End.one_apply]
  apply binaryHalfFiltration_class_congr
  have hd := hasse_degree_even hp5
  rw [← hd]
  simp [Nat.add_mod]

theorem theta_pow_ne_zero_of_closed_cycle (f : PowerSeries F) (hf : f ≠ 0)
    (hu : BoylanWebb.U p f = 0) {i : ℕ} (hi : i ≤ p - 1) : (theta ^ i) f ≠ 0 := by
  intro hzero
  have h := congrArg (fun g : PowerSeries F => (theta ^ (p - 1 - i)) g) hzero
  dsimp only at h
  rw [← Module.End.mul_apply, ← pow_add, Nat.sub_add_cancel hi,
    (U_eq_zero_iff_theta_cycle f).mp hu, map_zero] at h
  exact hf h

/-- The fourth theta iterate reaches minimum weight six, without assumed filtration laws. -/
theorem binaryCycle_weight_six (hp13 : 13 ≤ p) (f : PowerSeries F)
    (hf : BinaryRep f ((p - 3) / 2)) (hf0 : f ≠ 0) (hu : BoylanWebb.U p f = 0) :
    binaryCycleHalfWeight p ((p - 3) / 2) f 4 = 3 := by
  have hp5 : 5 ≤ p := by omega
  have hperiod := hasse_degree_even hp5
  have hstartDegree : 2 * ((p - 3) / 2) = p - 3 := by omega
  have hstartLt : (p - 3) / 2 < (p - 1) / 2 := by omega
  choose d hd using binaryCycleHalfWeight_step hp5 hf
  have hw6 := theta_cycle_weight_six p hp13
    (fun i => (2 * binaryCycleHalfWeight p ((p - 3) / 2) f i : ℕ))
    (fun i => (d i : ℤ))
    (fun _ _ => by positivity) (fun _ _ => by positivity)
    (fun i _ => by
      have h := hd i
      have hz : (binaryCycleHalfWeight p ((p - 3) / 2) f i : ℤ) + ((p - 1) / 2 : ℕ) + 1 =
          (binaryCycleHalfWeight p ((p - 3) / 2) f (i + 1) : ℤ) + ((p - 1) / 2 : ℕ) * d i := by
        exact_mod_cast h
      have hpz : (2 : ℤ) * ((p - 1) / 2 : ℕ) = (p : ℤ) - 1 := by
        calc
          _ = ((2 * ((p - 1) / 2) : ℕ) : ℤ) := by push_cast; rfl
          _ = ((p - 1 : ℕ) : ℤ) := by rw [hperiod]
          _ = _ := by rw [Nat.cast_sub (by omega), Nat.cast_one]
      push_cast
      nlinarith)
    (fun i hi hnd => by
      have he := binaryCycleHalfWeight_no_drop hp5 hf i
        (theta_pow_ne_zero_of_closed_cycle f hf0 hu (by omega)) hnd
      have h := hd i
      rw [he] at h
      have hz : d i = 0 := by nlinarith
      simp [hz])
    (by
      dsimp only
      rw [binaryCycleHalfWeight_zero hf hstartLt, hstartDegree,
        Nat.cast_sub (by omega), Nat.cast_ofNat])
    (by dsimp only; rw [binaryCycleHalfWeight_closed hp5 _ f hu])
  dsimp only at hw6
  omega

/-- A nonzero weight-(p−3) series killed by U_p has a weight-six representative after theta⁴. -/
theorem theta_four_binaryRep (hp13 : 13 ≤ p) (f : PowerSeries F)
    (hf : BinaryRep f ((p - 3) / 2)) (hf0 : f ≠ 0) (hu : BoylanWebb.U p f = 0) :
    BinaryRep ((theta ^ 4) f) 3 := by
  have h := binaryCycleHalfWeight_rep (by omega : 5 ≤ p) hf 4
  rwa [binaryCycle_weight_six hp13 f hf hf0 hu] at h

end RamanujanTau.TheoremA
