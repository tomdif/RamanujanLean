import RamanujanTau.MockTheta5PartitionCount
import RamanujanTau.TauModular
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Colored partitions as an actual finite counting model

A `k`-colored partition of `n` consists of one ordinary partition per color,
with total size `n`. Its count is the coefficient of the `k`th power of the
ordinary partition generating series. At `k = 24` this gives the regular
power series `q / Δ`; the pole in `1 / Δ` is accounted for by shifting indices.
No physical identification of these finite types is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace ColoredPartitions

open Finset PowerSeries
open scoped BigOperators

abbrev Sizes (k n : ℕ) :=
  ↥(finsuppAntidiag (univ : Finset (Fin k)) n)

/-- An ordered tuple of ordinary partitions, with sizes summing to `n`. -/
def Partition (k n : ℕ) := Σ v : Sizes k n, ∀ i : Fin k, Nat.Partition (v.1 i)

instance (k n : ℕ) : Fintype (Partition k n) := by
  unfold Partition
  infer_instance

def count (k n : ℕ) : ℕ := Fintype.card (Partition k n)

def series (k : ℕ) : PowerSeries ℤ := MockTheta5.JTP.partitionGF ^ k

lemma sizes_sum {k n : ℕ} (v : Sizes k n) : ∑ i, v.1 i = n :=
  (mem_finsuppAntidiag.mp v.2).1

lemma sizes_le {k n : ℕ} (v : Sizes k n) (i : Fin k) : v.1 i ≤ n := by
  exact (single_le_sum (fun j _ => Nat.zero_le (v.1 j)) (mem_univ i)).trans_eq (sizes_sum v)

/-- The finite convolution formula, derived from cardinalities of sigma and pi types. -/
theorem count_eq_sum (k n : ℕ) :
    count k n = ∑ v ∈ finsuppAntidiag (univ : Finset (Fin k)) n,
      ∏ i, Fintype.card (Nat.Partition (v i)) := by
  change Fintype.card (Σ v : Sizes k n, ∀ i : Fin k, Nat.Partition (v.1 i)) = _
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_pi]
  exact sum_coe_sort _ (fun v : Fin k →₀ ℕ => ∏ i : Fin k, Fintype.card (Nat.Partition (v i)))

/-- Exact coefficient-to-count bridge for every number of colors. -/
theorem coeff_series (k n : ℕ) : coeff n (series k) = (count k n : ℤ) := by
  unfold series
  rw [show MockTheta5.JTP.partitionGF ^ k =
    ∏ _i : Fin k, MockTheta5.JTP.partitionGF by simp, PowerSeries.coeff_prod]
  simp only [MockTheta5.JTP.coeff_partitionGF_eq_card, count_eq_sum, Nat.cast_sum,
    Nat.cast_prod]

/-- A positive number of colors supplies at least one colored partition of every size. -/
theorem count_pos {k : ℕ} (hk : 0 < k) (n : ℕ) : 0 < count k n := by
  let i : Fin k := ⟨0, hk⟩
  let v : Sizes k n := ⟨Finsupp.single i n, by simp⟩
  haveI : Nonempty (Partition k n) := ⟨⟨v, fun j => Nat.Partition.indiscrete _⟩⟩
  exact Fintype.card_pos

/-- A simple polynomial bound on the number of size tuples. -/
theorem sizes_card_le (k n : ℕ) : Fintype.card (Sizes k n) ≤ (n + 1) ^ k := by
  let f : Sizes k n → (Fin k → Fin (n + 1)) :=
    fun v i => ⟨v.1 i, Nat.lt_succ_of_le (sizes_le v i)⟩
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    ext i
    exact congrArg Fin.val (congrFun h i)
  simpa using Fintype.card_le_of_injective f hf

/-- Adding fixed extra ones is an injection between ordinary partition types. -/
def addOnes {n : ℕ} (r : ℕ) (p : Nat.Partition n) : Nat.Partition (n + r) where
  parts := p.parts + Multiset.replicate r 1
  parts_pos := by
    intro i hi
    rcases Multiset.mem_add.mp hi with hi | hi
    · exact p.parts_pos hi
    · have : i = 1 := (Multiset.mem_replicate.mp hi).2
      omega
  parts_sum := by simp [p.parts_sum]

lemma addOnes_injective (n r : ℕ) : Function.Injective (@addOnes n r) := by
  intro p q h
  apply Nat.Partition.ext
  exact add_right_cancel (congrArg Nat.Partition.parts h)

theorem ordinary_count_mono {m n : ℕ} (h : m ≤ n) :
    Fintype.card (Nat.Partition m) ≤ Fintype.card (Nat.Partition n) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  exact Fintype.card_le_of_injective (addOnes r) (addOnes_injective m r)

/-- A balanced tuple gives a lower bound that preserves the leading exponential rate. -/
theorem balanced_lower {k : ℕ} (hk : 0 < k) (n : ℕ) :
    Fintype.card (Nat.Partition (n / k)) ^ k ≤ count k n := by
  classical
  let i₀ : Fin k := ⟨0, hk⟩
  let v : Fin k →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun i => n / k + if i = i₀ then n % k else 0)
  have hv : v ∈ finsuppAntidiag (univ : Finset (Fin k)) n := by
    simp only [mem_finsuppAntidiag, subset_univ, and_true]
    simp only [v, Finsupp.coe_equivFunOnFinite_symm, sum_add_distrib]
    simp [Nat.div_add_mod]
  calc
    Fintype.card (Nat.Partition (n / k)) ^ k =
        ∏ _i : Fin k, Fintype.card (Nat.Partition (n / k)) := by simp
    _ ≤ ∏ i : Fin k, Fintype.card (Nat.Partition (v i)) := by
      apply prod_le_prod (fun _ _ => Nat.zero_le _)
      intro i _
      apply ordinary_count_mono
      simp [v]
    _ ≤ count k n := by
      rw [count_eq_sum]
      exact single_le_sum (f := fun w : Fin k →₀ ℕ =>
        ∏ i : Fin k, Fintype.card (Nat.Partition (w i))) (fun _ _ => Nat.zero_le _) hv

/-- The power series with the colored counts is the unit inverse of the Euler product power. -/
theorem euler_power_mul_series (k : ℕ) :
    MockTheta5.JTP.qfacInf ^ k * series k = 1 := by
  rw [series, ← mul_pow, MockTheta5.JTP.partitionGF,
    Ring.mul_inverse_cancel _ MockTheta5.JTP.isUnit_qfacInf, one_pow]

/-- The regular series for 24 colors equals `q/Δ`, expressed without inverting `q`. -/
theorem discriminant_mul_series :
    (X * MockTheta5.JTP.qfacInf ^ 24) * series 24 = X := by
  rw [mul_assoc, euler_power_mul_series, mul_one]

/-- The same identity for the q-expansion of the actual analytic modular discriminant. -/
theorem qExpansion_discriminant_mul_series :
    UpperHalfPlane.qExpansion 1 RamanujanTau.DiscriminantBridge.Δmod *
      PowerSeries.map (Int.castRingHom ℂ) (series 24) = X := by
  rw [RamanujanTau.TauModular.qExpansion_discriminant_eq, ← map_mul,
    discriminant_mul_series, PowerSeries.map_X]

/-- Coefficients of `q⁻¹ series 24`, i.e. `1/Δ`, indexed by nonnegative charge. -/
def degeneracy (n : ℕ) : ℕ := count 24 (n + 1)

theorem coeff_shifted_series (n : ℕ) :
    coeff (n + 1) (series 24) = (degeneracy n : ℤ) := coeff_series _ _

end ColoredPartitions
