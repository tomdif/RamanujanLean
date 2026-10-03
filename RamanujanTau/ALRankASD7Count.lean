/-
# Rank differences mod 7 from a class-pure decomposition

If `R(ζ;q) = Σ_t C(P_t(ζ)) · G_t` for every nontrivial 7th root of unity `ζ`, where each `G_t` is `ζ`-free and
supported on one class mod 7, and `P_t(ζ) = Σ_k v_{t,k} ζ^k`, then the discrete Fourier transform over the
seven roots turns `v_{t,a} = v_{t,b}` (for all `t` of class `c`) into `N(a,7,7n+c) = N(b,7,7n+c)`.
-/
import RamanujanTau.ALRank7Main

set_option autoImplicit false

namespace ALz
open HahnSeries Finset CrankProof

/-- the `ζ`-polynomial with coefficient vector `v`. -/
noncomputable def Pv (v : Fin 7 → ℂ) (z : ℂ) : ℂ := ∑ k : Fin 7, v k * z ^ (k : ℕ)

lemma geom7 (m : ℕ) : ∑ j : Fin 7, (ω7 ^ m) ^ (j : ℕ) = if m % 7 = 0 then 7 else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (ω7 ^ m) ^ j) 7]
  split_ifs with h
  · obtain ⟨r, hr⟩ := Nat.dvd_of_mod_eq_zero h
    rw [hr, pow_mul, ω7_pow7, one_pow]
    simp
  · have hp : IsPrimitiveRoot (ω7 ^ m) 7 := by
      have := ω7_prim.pow_of_coprime (m % 7) ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
        (by norm_num : Nat.Prime 7)).mpr (by omega))))
      rwa [← Nat.mod_add_div m 7, _root_.pow_add, pow_mul, ω7_pow7, one_pow, mul_one]
    exact hp.geom_sum_eq_zero (by norm_num)

/-- discrete Fourier inversion over the 7th roots of unity. -/
lemma fourier7 (v : Fin 7 → ℂ) (a : Fin 7) :
    ∑ j : Fin 7, (ω7 ^ (7 - (a : ℕ))) ^ (j : ℕ) * Pv v (ω7 ^ (j : ℕ)) = 7 * v a := by
  unfold Pv
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ k : Fin 7, ∑ j : Fin 7, (ω7 ^ (7 - (a : ℕ))) ^ (j : ℕ) * (v k * (ω7 ^ (j : ℕ)) ^ (k : ℕ)) =
      v k * ∑ j : Fin 7, (ω7 ^ (7 - (a : ℕ) + k)) ^ (j : ℕ) := by
    intro k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_mul, ← pow_mul, ← pow_mul, add_mul, _root_.pow_add]
    ring_nf
  simp_rw [this, geom7]
  rw [Finset.sum_eq_single a]
  · rw [if_pos (by omega)]; ring
  · intro k _ hk
    rw [if_neg, mul_zero]
    intro h
    exact hk (Fin.ext (by omega))
  · simp

/-- a 7th root of unity's power depends only on the exponent mod 7. -/
lemma root7_zpow {z : ℂ} (hz : z ^ 7 = 1) (r : ℤ) : z ^ r = z ^ (r % 7).toNat := by
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
  rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg r (by norm_num))]
  conv_lhs => rw [← Int.mul_ediv_add_emod r 7]
  rw [zpow_add₀ hz0, zpow_mul, show ((7 : ℤ)) = ((7 : ℕ) : ℤ) from rfl, zpow_natCast, hz, one_zpow, one_mul]

/-- `Σ_λ z^{rank λ} = P_N(z)` with `N_k` the rank counts mod 7. -/
lemma rank_sum_Pv {z : ℂ} (hz : z ^ 7 = 1) (m : ℕ) :
    ∑ l : m.Partition, z ^ rank l = Pv (fun k => (rankCount7 m k : ℂ)) z := by
  simp_rw [root7_zpow hz]
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := range 7) (g := fun l : m.Partition => (rank l % 7).toNat)
    (fun l _ => Finset.mem_coe.mpr (Finset.mem_range.mpr (show (rank l % 7).toNat < 7 by omega)))]
  rw [Pv, Fin.sum_univ_eq_sum_range (fun k => (rankCount7 m k : ℂ) * z ^ k) 7]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => z ^ k) (fun l hl => by rw [(Finset.mem_filter.mp hl).2]),
    Finset.sum_const, nsmul_eq_mul, rankCount7]

/-- **Rank equalities from a class-pure decomposition.** -/
theorem rank_eq_of_decomp {T : ℕ} (G : Fin T → L) (cl : Fin T → ℕ) (v : Fin T → Fin 7 → ℤ)
    (hG : ∀ t, InCls (cl t) (G t))
    (hdec : ∀ j : ℕ, 0 < j → j < 7 →
      ι1 (Dser (ω7 ^ j) (ω7 ^ j)⁻¹) = ∑ t, HahnSeries.C (Pv (fun k => (v t k : ℂ)) (ω7 ^ j)) * G t)
    {c : ℕ} (hc : c < 7) (a b : Fin 7) (hcond : ∀ t, cl t = c → v t a = v t b) (n : ℕ) :
    rankCount7 (7 * n + c) a = rankCount7 (7 * n + c) b := by
  set m := 7 * n + c with hm
  -- `S(ω^j)` in two ways
  have hS : ∀ j : Fin 7, ((ω7 ^ (7 - (a : ℕ))) ^ (j : ℕ) - (ω7 ^ (7 - (b : ℕ))) ^ (j : ℕ)) *
      Pv (fun k => (rankCount7 m k : ℂ)) (ω7 ^ (j : ℕ)) =
      ∑ t, ((ω7 ^ (7 - (a : ℕ))) ^ (j : ℕ) - (ω7 ^ (7 - (b : ℕ))) ^ (j : ℕ)) *
        Pv (fun k => (v t k : ℂ)) (ω7 ^ (j : ℕ)) * (G t).coeff (m : ℤ) := by
    intro j
    rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
    · simp [h0]
    have hz : (ω7 ^ (j : ℕ)) ^ 7 = 1 := by rw [← pow_mul, mul_comm, pow_mul, ω7_pow7, one_pow]
    rw [← rank_sum_Pv hz, rank_durfee (pow_ne_zero _ ω7_ne), ← ALz.ι1_coeff_nat, hdec j hpos j.isLt,
      coeff_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [C_mul_eq_smul, coeff_smul, smul_eq_mul]; ring
  have key := Finset.sum_congr rfl fun j (_ : j ∈ (univ : Finset (Fin 7))) => hS j
  rw [Finset.sum_comm] at key
  simp_rw [sub_mul] at key
  rw [Finset.sum_sub_distrib, fourier7, fourier7] at key
  have hz : ∀ t, ∑ j : Fin 7, ((ω7 ^ (7 - (a : ℕ))) ^ (j : ℕ) * Pv (fun k => (v t k : ℂ)) (ω7 ^ (j : ℕ)) *
      (G t).coeff (m : ℤ) - (ω7 ^ (7 - (b : ℕ))) ^ (j : ℕ) * Pv (fun k => (v t k : ℂ)) (ω7 ^ (j : ℕ)) *
      (G t).coeff (m : ℤ)) = 0 := by
    intro t
    simp_rw [← sub_mul]
    rw [← Finset.sum_mul]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, fourier7, fourier7]
    by_cases hct : cl t = c
    · rw [hcond t hct]; ring
    · have : (G t).coeff (m : ℤ) = 0 := by
        by_contra hne
        have := hG t (m : ℤ) hne
        apply hct
        omega
      rw [this, mul_zero]
  rw [Finset.sum_congr rfl fun t _ => hz t, Finset.sum_const_zero] at key
  have : (rankCount7 m a : ℂ) = rankCount7 m b := by linear_combination key / 7
  exact_mod_cast this

end ALz
