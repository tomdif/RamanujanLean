import RamanujanTau.FiniteArithmetic.AllPowers29

/-! At any precision, two initial partition residues determine the entire
infinite family. Computing those initial residues is a separate cost. -/
set_option autoImplicit false
namespace RamanujanTau.FiniteArithmetic.Evaluate29Powers

def start (m : ℕ) : ℕ := 2 * m - 1

def index (m t : ℕ) : ℕ := (29 ^ (start m + 2 * t) * 19 + 1) / 24

noncomputable def count (m t : ℕ) : ZMod (29 ^ m) :=
  Fintype.card (Nat.Partition (index m t))

lemma valid (m : ℕ) (hm : 1 ≤ m) : 24 ∣ 29 ^ start m * 19 + 1 := by
  rw [show start m = 1 + 2 * (m - 1) by unfold start; omega]
  exact Partition29.valid_index 1 19 (m - 1) (by decide)

/-- The first residue is invertible even at composite modulus 29^m. -/
theorem initial_isUnit (m : ℕ) (hm : 1 ≤ m) : IsUnit (count m 0) := by
  let a := Fintype.card (Nat.Partition (index m 0))
  have ha : (a : ZMod 29) = 3 ^ (m - 1) * 8 := by
    have hi : index m 0 = (29 ^ (1 + 2 * (m - 1)) * 19 + 1) / 24 := by
      simp only [index, Nat.mul_zero, Nat.add_zero,
        show start m = 1 + 2 * (m - 1) by unfold start; omega]
    change (Fintype.card (Nat.Partition (index m 0)) : ZMod 29) = _
    rw [hi]
    exact Partition29.explicit_family (m - 1)
  have hunit : IsUnit (a : ZMod 29) := by
    rw [isUnit_iff_ne_zero, ha]
    exact mul_ne_zero (pow_ne_zero _ (by decide)) (by decide)
  have hc := (ZMod.isUnit_iff_coprime a 29).mp hunit
  exact (ZMod.isUnit_iff_coprime a (29 ^ m)).mpr (hc.pow_right m)

/-- A concrete specification of the multiplier, using only two finite counts. -/
noncomputable def multiplier (m : ℕ) : ZMod (29 ^ m) := count m 1 * (count m 0)⁻¹

theorem count_eq (m : ℕ) (hm : 1 ≤ m) (t : ℕ) :
    count m t = multiplier m ^ t * count m 0 := by
  obtain ⟨k, hk⟩ := AllPowers29.partition_residues_iterate m hm
  have h (j : ℕ) : count m j = k ^ j * count m 0 := by
    simpa only [count, index, Nat.mul_zero, Nat.add_zero] using
      hk (start m) le_rfl 19 (valid m hm) j
  have hk' : multiplier m = k := by
    rw [multiplier, h 1, pow_one, mul_assoc, ZMod.mul_inv_of_unit _ (initial_isUnit m hm), mul_one]
  rw [hk']
  exact h t

/-- Binary matrix powering from two supplied residues. This function does not
construct the partition index or recompute either initial partition count. -/
def evaluate (m : ℕ) (a b : ZMod (29 ^ m)) (t : ℕ) : ZMod (29 ^ m) :=
  matrixPower (fun _ _ : Fin 1 => b * a⁻¹) t 0 0 * a

theorem evaluate_eq (m : ℕ) (a b : ZMod (29 ^ m)) (t : ℕ) :
    evaluate m a b t = (b * a⁻¹) ^ t * a := by
  rw [evaluate, matrixPower_eq]
  congr 1
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_one, ih, pow_succ]

/-- The executable recurrence is correct for every m and every future iterate,
when its two inputs are the actual initial partition residues. -/
theorem evaluate_correct (m : ℕ) (hm : 1 ≤ m) (t : ℕ) :
    evaluate m (count m 0) (count m 1) t = count m t := by
  rw [evaluate_eq, count_eq m hm t]
  rfl

end RamanujanTau.FiniteArithmetic.Evaluate29Powers
