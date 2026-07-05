/-
# The partition-count bridge: `coeff n (1/(q;q)_∞)` **is** the number of partitions of `n`

Our `partitionGF = Ring.inverse (q;q)_∞` is the formal generating function `1/(q;q)_∞`. Mathlib defines
`Nat.Partition.genFun` combinatorially (`coeff n = #{partitions of n}`) as the product
`∏' i, (1 + ∑' j, X^{(i+1)(j+1)})` — but leaves connecting it to `1/(q;q)_∞` as a stated TODO. We close it:

  * `HasProd (fun n ↦ 1 − X^{n+1}) (q;q)_∞`         (the partial products `(q;q)_N` converge to `(q;q)_∞`),
  * each `genFun` factor `1 + ∑' j, X^{(i+1)(j+1)} = ∑' i, (X^{i+1})^i` is the inverse of `1 − X^{i+1}`,
  so `genFun 1 · (q;q)_∞ = 1`, hence `partitionGF = genFun (fun _ _ ↦ 1)` and

  **`coeff_partitionGF_eq_card`:**  `coeff n partitionGF = #(Nat.Partition n)`.

Consequently the congruences read as statements about the honest partition count:
`five_dvd_partition_card`, `seven_dvd_partition_card`.  No `sorry`.
-/
import RamanujanTau.MockTheta5PartitionCongruence7
import Mathlib.Combinatorics.Enumerative.Partition.GenFun

namespace MockTheta5.JTP
open PowerSeries Filter Topology MockTheta5.Bailey
open scoped PowerSeries.WithPiTopology

/-- The partial products `(q;q)_N = ∏_{i<N}(1−X^{i+1})` converge to `(q;q)_∞`. -/
lemma tendsto_qfac : Tendsto (fun N => qfac N) atTop (𝓝 qfacInf) := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  exact tendsto_atTop_of_eventually_const (i₀ := d + 1) (fun N hN => (coeff_qfacInf hN).symm)

/-- `(q;q)_∞` is the infinite product `∏(1−X^{n+1})` in the `X`-adic sense. -/
lemma hasProd_qfacInf : HasProd (fun n => (1 : PowerSeries ℤ) - X ^ (n + 1)) qfacInf := by
  have hm := PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ
  have h1 : (∏' n, ((1 : PowerSeries ℤ) - X ^ (n + 1))) = qfacInf :=
    tendsto_nhds_unique hm.hasProd.tendsto_prod_nat tendsto_qfac
  rw [← h1]; exact hm.hasProd

/-- Each `genFun` factor times `(1 − X^{n+1})` is `1` (geometric series). -/
lemma genFun_factor_mul (n : ℕ) :
    ((1 : PowerSeries ℤ) + ∑' j, (1 : ℤ) • X ^ ((n + 1) * (j + 1))) * (1 - X ^ (n + 1)) = 1 := by
  have hcc : (X ^ (n + 1) : PowerSeries ℤ).constantCoeff = 0 := by rw [map_pow]; simp
  have hgeo : ((1 : PowerSeries ℤ) + ∑' j, (1 : ℤ) • X ^ ((n + 1) * (j + 1)))
      = ∑' i, (X ^ (n + 1) : PowerSeries ℤ) ^ i := by
    rw [(PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero hcc).tsum_eq_zero_add,
        pow_zero]
    refine congrArg (1 + ·) (tsum_congr (fun j => ?_))
    rw [one_smul, ← pow_mul]
  rw [hgeo]
  exact PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hcc

/-- **`genFun 1 · (q;q)_∞ = 1`.** -/
lemma genFun_one_mul_qfacInf : (Nat.Partition.genFun (fun _ _ => (1 : ℤ))) * qfacInf = 1 := by
  have hcomb := (Nat.Partition.hasProd_genFun (fun _ _ => (1 : ℤ))).mul hasProd_qfacInf
  rw [← hcomb.tprod_eq]
  exact (tprod_congr genFun_factor_mul).trans tprod_one

/-- `partitionGF = 1/(q;q)_∞` **is** Mathlib's combinatorial partition generating function. -/
lemma partitionGF_eq_genFun : partitionGF = Nat.Partition.genFun (fun _ _ => (1 : ℤ)) := by
  rw [partitionGF]
  symm
  calc Nat.Partition.genFun (fun _ _ => (1 : ℤ))
      = Nat.Partition.genFun (fun _ _ => (1 : ℤ)) * (qfacInf * Ring.inverse qfacInf) := by
        rw [Ring.mul_inverse_cancel _ isUnit_qfacInf, mul_one]
    _ = (Nat.Partition.genFun (fun _ _ => (1 : ℤ)) * qfacInf) * Ring.inverse qfacInf := by ring
    _ = Ring.inverse qfacInf := by rw [genFun_one_mul_qfacInf, one_mul]

/-- **The partition-count bridge:** `coeff n (1/(q;q)_∞) = #{partitions of n}`. -/
theorem coeff_partitionGF_eq_card (n : ℕ) :
    coeff n partitionGF = (Fintype.card (Nat.Partition n) : ℤ) := by
  rw [partitionGF_eq_genFun, Nat.Partition.coeff_genFun]
  have hone : ∀ p : Nat.Partition n, p.parts.toFinsupp.prod (fun _ _ => (1 : ℤ)) = 1 :=
    fun p => by simp only [Finsupp.prod, Finset.prod_const_one]
  simp only [hone, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- **Ramanujan's congruence for the partition count:** `5 ∣ p(5n+4)`. -/
theorem five_dvd_partition_card (n : ℕ) : 5 ∣ Fintype.card (Nat.Partition (5 * n + 4)) := by
  have h := five_dvd_coeff_partitionGF n
  rw [coeff_partitionGF_eq_card] at h
  exact_mod_cast h

/-- **Ramanujan's congruence for the partition count:** `7 ∣ p(7n+5)`. -/
theorem seven_dvd_partition_card (n : ℕ) : 7 ∣ Fintype.card (Nat.Partition (7 * n + 5)) := by
  have h := seven_dvd_coeff_partitionGF n
  rw [coeff_partitionGF_eq_card] at h
  exact_mod_cast h

end MockTheta5.JTP
