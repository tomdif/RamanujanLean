import RamanujanTau.FiniteArithmetic.Cert29
import RamanujanTau.FiniteArithmetic.PartitionCycle
import RamanujanTau.FiniteArithmetic.Evaluate

/-!
# A certified infinite partition recurrence modulo 29

The finite list certificate identifies the genuine partition operator on its
odd orbit. The resulting two-step recurrence is unconditional modulo 29.
It does not identify the experimental normalized error operator `Theta`, and
does not establish sharpness modulo `29^m` for general `m`.
-/

set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.Partition29
open PowerSeries BoylanWebb

theorem two_step (b : ℕ) (hb : 1 ≤ b) :
    Ψ 29 (L 29 (b + 2)) = C 3 * Ψ 29 (L 29 b) :=
  partition_cycle_two_step 29 (Ψ 29 Cert29.f) (Ψ 29 Cert29.g) 8 3 (by decide)
    Cert29.seed Cert29.even_step Cert29.odd_step b hb

/-- The recurrence is about actual cardinalities of integer partitions. -/
theorem partition_count (b : ℕ) (hb : 1 ≤ b) (n : ℕ) (hn : 24 ∣ 29 ^ b * n + 1) :
    (Fintype.card (Nat.Partition ((29 ^ (b + 2) * n + 1) / 24)) : ZMod 29) =
      3 * (Fintype.card (Nat.Partition ((29 ^ b * n + 1) / 24)) : ZMod 29) :=
  count_of 29 (by decide) 3
    (partition_of_two_step 29 (by decide) 3 two_step) b hb n hn

lemma valid_index (b n t : ℕ) (hn : 24 ∣ 29 ^ b * n + 1) :
    24 ∣ 29 ^ (b + 2 * t) * n + 1 := by
  have ht : 29 ^ (2 * t) % 24 = 1 := by
    rw [pow_mul, Nat.pow_mod]
    norm_num
  have hm : Nat.ModEq 24 (29 ^ (2 * t)) 1 := ht
  have h := ((hm.mul_left (29 ^ b)).mul_right n).add_right 1
  have h' : Nat.ModEq 24 (29 ^ (b + 2 * t) * n + 1) (29 ^ b * n + 1) := by
    simpa only [pow_add, mul_one] using h
  exact (h'.dvd_iff (dvd_refl 24)).mpr hn

/-- Evaluation along an infinite structured family reduces to one initial
partition residue and a scalar power. This does not compute the initial
residue for an arbitrary `b,n`; that is a separate input cost. -/
theorem partition_count_iterate (b : ℕ) (hb : 1 ≤ b) (n : ℕ)
    (hn : 24 ∣ 29 ^ b * n + 1) (t : ℕ) :
    (Fintype.card (Nat.Partition ((29 ^ (b + 2 * t) * n + 1) / 24)) : ZMod 29) =
      (3 : ZMod 29) ^ t * (Fintype.card (Nat.Partition ((29 ^ b * n + 1) / 24)) : ZMod 29) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show b + 2 * (t + 1) = (b + 2 * t) + 2 by omega,
      partition_count _ (by omega) n (valid_index b n t hn), ih, pow_succ']
    ring

private lemma coeff_expand_mul_small (n : ℕ) (hn : n < 29) (F G : PowerSeries ℤ) :
    coeff n (RankProof.Ea 29 (by decide) F * G) = coeff 0 F * coeff n G := by
  rw [coeff_mul, Finset.sum_eq_single (0, n)]
  · simp [RankProof.coeff_Ea]
  · intro ij hij hne
    have hij' := Finset.mem_antidiagonal.mp hij
    have hi : ij.1 ≠ 0 := by
      intro hi
      apply hne
      ext <;> simp_all
    have hnd : ¬ 29 ∣ ij.1 := by
      intro hd
      exact hi (Nat.eq_zero_of_dvd_of_lt hd (by omega))
    simp [RankProof.coeff_Ea, hnd]
  · simp

/-- The initial residue is itself proved from the certified generating series. -/
theorem initial_residue : (Fintype.card (Nat.Partition 23) : ZMod 29) = 8 := by
  have hL : coeff 2 (L 29 1) = pZ 23 := by
    rw [(L_eq_partition 29 (by decide) 0).2,
      coeff_expand_mul_small 2 (by decide), MockTheta5.JTP.coeff_zero_qfacInf,
      one_mul, Pser, coeff_mk]
    norm_num [eB, ek]
  have hf : coeff 2 (Ψ 29 Cert29.f) = 1 :=
    (Cg_coeff Cert29.cg_LF (by decide : 2 ≤ 1073)).trans (by decide +kernel)
  have h := congrArg (coeff 2)
    (partition_cycle_values 29 (Ψ 29 Cert29.f) (Ψ 29 Cert29.g) 8 3 (by decide)
      Cert29.seed Cert29.even_step Cert29.odd_step 0).1
  rw [coeff_map, hL, show (23 : ℤ) = (23 : ℕ) from rfl, pZ_natCast] at h
  rw [coeff_C_mul, pow_zero, mul_one, hf, mul_one] at h
  change ((Fintype.card (Nat.Partition 23) : ℤ) : ZMod 29) = 8 at h
  rw [Int.cast_natCast] at h
  exact h

/-- A completely specified infinite family, including its initial residue. -/
theorem explicit_family (t : ℕ) :
    (Fintype.card (Nat.Partition ((29 ^ (1 + 2 * t) * 19 + 1) / 24)) : ZMod 29) =
      (3 : ZMod 29) ^ t * 8 := by
  have h := partition_count_iterate 1 le_rfl 19 (by decide) t
  change _ = (3 : ZMod 29) ^ t * (Fintype.card (Nat.Partition 23) : ZMod 29) at h
  rw [initial_residue] at h
  exact h

/-- Evaluate the explicit family without constructing its enormous index. -/
def residue (t : ℕ) : ZMod 29 :=
  (matrixPower (fun (_ _ : Fin 1) => (3 : ZMod 29)) t) 0 0 * 8

theorem residue_correct (t : ℕ) :
    residue t = (Fintype.card (Nat.Partition ((29 ^ (1 + 2 * t) * 19 + 1) / 24)) : ZMod 29) := by
  rw [explicit_family, residue, matrixPower_eq]
  congr 1
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_one, ih, pow_succ]


end RamanujanTau.FiniteArithmetic.Partition29
