import RamanujanTau.ColoredPartitionEntropy
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Bosonic occupation numbers and colored partitions

The model has `k` species, positive integral mode energies, and nonnegative
integer occupation numbers of finite support. Mode zero is explicitly absent.
Its exact energy shells are equivalent to actual colored partitions.

The finite shell Hilbert spaces have an occupation-number orthonormal basis.
For 24 species we specify the vacuum offset `-1`, then identify the charge-shell
dimensions with the coefficients of `1/Δ` and transfer the proved entropy limit.

This is a mathematical occupation-basis model. The vacuum offset is an input;
string duality, a full oscillator representation, and a gravitational area law
are not supplied by this construction.
-/

set_option autoImplicit false
noncomputable section

namespace BosonicOccupation

open Finset Filter
open scoped Real Topology

/-- A species has finitely many occupied positive modes; each multiplicity is unrestricted. -/
@[ext]
structure Occupation (k : ℕ) where
  modes : Fin k → (ℕ →₀ ℕ)
  zero_mode : ∀ i, modes i 0 = 0

def modeEnergy (f : ℕ →₀ ℕ) : ℕ := f.sum fun m a => m * a

def energy {k : ℕ} (o : Occupation k) : ℕ := ∑ i, modeEnergy (o.modes i)

/-- Occupation-basis states at a fixed, unshifted total energy. -/
def State (k n : ℕ) := {o : Occupation k // energy o = n}

lemma modeEnergy_eq_multiset_sum (f : ℕ →₀ ℕ) :
    modeEnergy f = f.toMultiset.sum := by
  rw [Finsupp.sum_toMultiset]
  unfold modeEnergy
  apply Finsupp.sum_congr
  intro m _
  simp [Nat.mul_comm]

lemma partition_zero_count {n : ℕ} (p : Nat.Partition n) : p.parts.toFinsupp 0 = 0 := by
  simp only [Multiset.toFinsupp_apply]
  apply Multiset.count_eq_zero.mpr
  intro h
  exact (Nat.lt_irrefl 0) (p.parts_pos h)

/-- Read occupation numbers as the multiplicities of the parts, separately for each color. -/
def fromPartition {k n : ℕ} (p : ColoredPartitions.Partition k n) : State k n :=
  ⟨⟨fun i => (p.2 i).parts.toFinsupp, fun i => partition_zero_count (p.2 i)⟩, by
    change ∑ i, modeEnergy ((p.2 i).parts.toFinsupp) = n
    calc
      ∑ i, modeEnergy ((p.2 i).parts.toFinsupp) = ∑ i, p.1.1 i := by
        apply sum_congr rfl
        intro i _
        rw [modeEnergy_eq_multiset_sum, Multiset.toFinsupp_toMultiset, (p.2 i).parts_sum]
      _ = n := ColoredPartitions.sizes_sum p.1⟩

lemma occupied_mode_pos {k : ℕ} (o : Occupation k) (i : Fin k) {m : ℕ}
    (hm : m ∈ (o.modes i).toMultiset) : 0 < m := by
  have hmem := (Finsupp.mem_toMultiset _ _).mp hm
  have hne := Finsupp.mem_support_iff.mp hmem
  by_contra h
  have hm0 : m = 0 := by omega
  exact hne (hm0 ▸ o.zero_mode i)

/-- Reconstruct the partitions from their independent mode multiplicities. -/
def toPartition {k n : ℕ} (s : State k n) : ColoredPartitions.Partition k n := by
  let v : ColoredPartitions.Sizes k n :=
    ⟨Finsupp.equivFunOnFinite.symm (fun i => modeEnergy (s.1.modes i)), by
      simp only [mem_finsuppAntidiag, Finsupp.coe_equivFunOnFinite_symm,
        subset_univ, and_true]
      exact s.2⟩
  exact ⟨v, fun i =>
    { parts := (s.1.modes i).toMultiset
      parts_pos := occupied_mode_pos s.1 i
      parts_sum := (modeEnergy_eq_multiset_sum _).symm }⟩

private lemma colored_ext {k n : ℕ} (p q : ColoredPartitions.Partition k n)
    (h : ∀ i, (p.2 i).parts = (q.2 i).parts) : p = q := by
  have hv : p.1 = q.1 := by
    apply Subtype.ext
    ext i
    calc
      p.1.1 i = (p.2 i).parts.sum := (p.2 i).parts_sum.symm
      _ = (q.2 i).parts.sum := congrArg Multiset.sum (h i)
      _ = q.1.1 i := (q.2 i).parts_sum
  rcases p with ⟨vp, pp⟩
  rcases q with ⟨vq, pq⟩
  change vp = vq at hv
  cases hv
  have hp : pp = pq := by
    funext i
    exact Nat.Partition.ext (h i)
  exact congrArg (Sigma.mk vp) hp

theorem fromPartition_toPartition {k n : ℕ} (s : State k n) :
    fromPartition (toPartition s) = s := by
  apply Subtype.ext
  apply Occupation.ext
  funext i
  change Multiset.toFinsupp (Finsupp.toMultiset (s.1.modes i)) = s.1.modes i
  exact Finsupp.toMultiset_toFinsupp _

theorem toPartition_fromPartition {k n : ℕ} (p : ColoredPartitions.Partition k n) :
    toPartition (fromPartition p) = p := by
  apply colored_ext
  intro i
  change Finsupp.toMultiset (Multiset.toFinsupp (p.2 i).parts) = (p.2 i).parts
  exact Multiset.toFinsupp_toMultiset _

/-- An explicit equivalence of energy-shell occupation states and colored partitions. -/
def stateEquivPartition (k n : ℕ) : State k n ≃ ColoredPartitions.Partition k n where
  toFun := toPartition
  invFun := fromPartition
  left_inv := fromPartition_toPartition
  right_inv := toPartition_fromPartition

instance (k n : ℕ) : Fintype (State k n) :=
  Fintype.ofEquiv (ColoredPartitions.Partition k n) (stateEquivPartition k n).symm

theorem state_card (k n : ℕ) : Fintype.card (State k n) = ColoredPartitions.count k n :=
  Fintype.card_congr (stateEquivPartition k n)

/-- Every occupied mode's contribution is bounded by the total energy. -/
theorem mode_contribution_le_energy {k : ℕ} (o : Occupation k) (i : Fin k) (m : ℕ) :
    m * o.modes i m ≤ energy o := by
  have hm : m * o.modes i m ≤ modeEnergy (o.modes i) := by
    by_cases h : o.modes i m = 0
    · simp [h]
    · exact single_le_sum (f := fun j => j * o.modes i j) (fun _ _ => Nat.zero_le _)
        (Finsupp.mem_support_iff.mpr h)
  exact hm.trans (single_le_sum (f := fun j => modeEnergy (o.modes j))
    (fun _ _ => Nat.zero_le _) (mem_univ i))

/-- The finite mode cutoff follows from the energy constraint; it is not assumed. -/
theorem state_zero_above_energy {k n : ℕ} (s : State k n) (i : Fin k) {m : ℕ}
    (hm : n < m) : s.1.modes i m = 0 := by
  have h := mode_contribution_le_energy s.1 i m
  rw [s.2] at h
  by_contra hne
  have hpos : 1 ≤ s.1.modes i m := Nat.one_le_iff_ne_zero.mpr hne
  have : m ≤ m * s.1.modes i m := by nlinarith
  omega

theorem state_occupation_bound {k n : ℕ} (s : State k n) (i : Fin k) {m : ℕ}
    (hm : 0 < m) : s.1.modes i m ≤ n / m := by
  apply (Nat.le_div_iff_mul_le hm).mpr
  simpa [Nat.mul_comm, s.2] using mode_contribution_le_energy s.1 i m

def vacuum (k : ℕ) : Occupation k := ⟨fun _ => 0, by simp⟩

@[simp] theorem energy_vacuum (k : ℕ) : energy (vacuum k) = 0 := by
  simp [energy, vacuum, modeEnergy]

theorem zero_energy_unique {k : ℕ} (s : State k 0) : s.1 = vacuum k := by
  apply Occupation.ext
  funext i
  ext m
  by_cases hm : m = 0
  · simpa [hm, vacuum] using s.1.zero_mode i
  · exact state_zero_above_energy s i (Nat.pos_of_ne_zero hm)

/-- The finite Hilbert space with its occupation-number coordinates. -/
abbrev ShellSpace (k n : ℕ) := EuclideanSpace ℂ (State k n)

def occupationBasis (k n : ℕ) : OrthonormalBasis (State k n) ℂ (ShellSpace k n) :=
  EuclideanSpace.basisFun (State k n) ℂ

theorem shell_finrank (k n : ℕ) :
    Module.finrank ℂ (ShellSpace k n) = ColoredPartitions.count k n := by
  rw [finrank_euclideanSpace, state_card]

/-- The formal graded dimension series of the finite energy shells. -/
def shellSeries (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (Module.finrank ℂ (ShellSpace k n) : ℤ)

theorem shellSeries_eq (k : ℕ) : shellSeries k = ColoredPartitions.series k := by
  ext n
  simp only [shellSeries, PowerSeries.coeff_mk, shell_finrank, ColoredPartitions.coeff_series]

theorem discriminant_mul_shellSeries :
    UpperHalfPlane.qExpansion 1 RamanujanTau.DiscriminantBridge.Δmod *
      PowerSeries.map (Int.castRingHom ℂ) (shellSeries 24) = PowerSeries.X := by
  rw [shellSeries_eq]
  exact ColoredPartitions.qExpansion_discriminant_mul_series

/-- The vacuum energy offset `-1` is specified as part of the 24-species model. -/
def charge (o : Occupation 24) : ℤ := (energy o : ℤ) - 1

@[simp] theorem charge_vacuum : charge (vacuum 24) = -1 := by
  simp [charge]

theorem charge_eq_iff (o : Occupation 24) (n : ℕ) :
    charge o = (n : ℤ) ↔ energy o = n + 1 := by
  unfold charge
  omega

def ChargeState (n : ℕ) := {o : Occupation 24 // charge o = (n : ℤ)}

def chargeStateEquivEnergy (n : ℕ) : ChargeState n ≃ State 24 (n + 1) :=
  Equiv.subtypeEquivRight fun o => charge_eq_iff o n

instance (n : ℕ) : Fintype (ChargeState n) :=
  Fintype.ofEquiv (State 24 (n + 1)) (chargeStateEquivEnergy n).symm

abbrev ChargeSpace (n : ℕ) := EuclideanSpace ℂ (ChargeState n)

theorem charge_finrank (n : ℕ) :
    Module.finrank ℂ (ChargeSpace n) = ColoredPartitions.degeneracy n := by
  rw [finrank_euclideanSpace, Fintype.card_congr (chargeStateEquivEnergy n), state_card]
  rfl

/-- Exact identification of the graded charge-shell dimension with the reciprocal-discriminant coefficients. -/
theorem charge_finrank_eq_coeff (n : ℕ) :
    (Module.finrank ℂ (ChargeSpace n) : ℤ) =
      PowerSeries.coeff (n + 1) (ColoredPartitions.series 24) := by
  rw [charge_finrank, ColoredPartitions.coeff_shifted_series]

/-- Entropy growth of the explicitly constructed finite shell Hilbert spaces. -/
theorem charge_entropy :
    Tendsto (fun n : ℕ => Real.log (Module.finrank ℂ (ChargeSpace n) : ℝ) / √n)
      atTop (𝓝 (4 * π)) := by
  simpa only [charge_finrank] using ColoredPartitions.degeneracy_entropy

theorem charge_cardy_ratio :
    Tendsto (fun n : ℕ => Real.log (Module.finrank ℂ (ChargeSpace n) : ℝ) /
      Cardy.leadingEntropy 2 n) atTop (𝓝 1) := by
  simpa only [charge_finrank] using ColoredPartitions.degeneracy_cardy_ratio

end BosonicOccupation
