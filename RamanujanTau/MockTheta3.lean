/-
# Ramanujan's third-order mock theta function `f(q)` and rank parity

Ramanujan's last letter to Hardy (12 January 1920) introduces
  `f(q) = Σ_{n≥0} q^{n²}/(−q;q)_n²`.
At `z = −1` the Durfee form of Dyson's rank generating function (`CrankProof.rank_durfee`) is `f(q)`, so
  `f(q) = Σ_n (N(0,2,n) − N(1,2,n)) qⁿ`:
the `qⁿ` coefficient of `f` is the number of partitions of `n` with even rank minus the number with odd rank.
-/
import RamanujanTau.RankGF

set_option autoImplicit false

namespace MockTheta3
open PowerSeries Finset CrankProof

/-- `(−q;q)_k = ∏_{i<k} (1 + q^{i+1})`. -/
noncomputable def negPoch (k : ℕ) : PowerSeries ℤ := ∏ i ∈ range k, (1 + X ^ (i + 1))

lemma isUnit_negPoch (k : ℕ) : IsUnit (negPoch k) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, negPoch, map_prod]
  simp

/-- **Ramanujan's third-order mock theta function** `f(q) = Σ_n q^{n²}/(−q;q)_n²`, coefficientwise. -/
noncomputable def f3 : PowerSeries ℤ :=
  mk fun n => coeff n (∑ k ∈ range (n + 1), X ^ (k ^ 2) * Ring.inverse (negPoch k) ^ 2)

lemma ψ_negPoch (k : ℕ) : MockTheta5.JTP.ψC (negPoch k) = poch (-1) 1 k := by
  simp [negPoch, poch, map_prod, sub_eq_add_neg, add_comm]

/-- **`f(q)` counts partitions by rank parity**: `[qⁿ] f = N(0,2,n) − N(1,2,n)`. -/
theorem f3_rank (n : ℕ) :
    coeff n f3 = ((univ.filter fun l : n.Partition => Even (rank l)).card : ℤ)
      - ((univ.filter fun l : n.Partition => ¬ Even (rank l)).card : ℤ) := by
  apply Int.cast_injective (α := ℂ)
  have hD := rank_durfee (z := -1) (by norm_num) n
  have hsum : ∑ l : n.Partition, (-1 : ℂ) ^ rank l
      = ((univ.filter fun l : n.Partition => Even (rank l)).card : ℂ)
        - ((univ.filter fun l : n.Partition => ¬ Even (rank l)).card : ℂ) := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun l : n.Partition => Even (rank l))]
    rw [Finset.sum_congr rfl fun l hl => (Finset.mem_filter.mp hl).2.neg_one_zpow,
      Finset.sum_congr rfl fun l hl => (Int.not_even_iff_odd.mp (Finset.mem_filter.mp hl).2).neg_one_zpow]
    simp [sub_eq_add_neg]
  push_cast
  rw [← hsum, hD, Dser, coeff_mk, f3, coeff_mk]
  have hc : (Int.castRingHom ℂ) (coeff n (∑ k ∈ range (n + 1), X ^ (k ^ 2) * Ring.inverse (negPoch k) ^ 2))
      = coeff n (MockTheta5.JTP.ψC (∑ k ∈ range (n + 1), X ^ (k ^ 2) * Ring.inverse (negPoch k) ^ 2)) := by
    rw [PowerSeries.coeff_map]
  simp only [eq_intCast] at hc
  rw [hc]
  congr 1
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, map_pow, map_X, map_inverse _ (isUnit_negPoch k), ψ_negPoch]
  simp; ring

end MockTheta3
