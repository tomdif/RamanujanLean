import RamanujanTau.HasseInv.Weierstrass

/-!
# A coefficient-level Cartier lemma

In characteristic `p`, for `φ = T + O(T²)`: `[T^{p−1}] (ψ(φ) · φ') = [T^{p−1}] ψ`.
-/

set_option autoImplicit false

namespace TateFormal
open MvPowerSeries FGL HasseInv

variable {R : Type*} [CommRing R]

local notation "R1" => MvPowerSeries Unit R
local notation "TT" => (X () : MvPowerSeries Unit R)

lemma natCast_R1' (k : ℕ) : ((k : R1) : PowerSeries R) = PowerSeries.C (k : R) := (map_natCast _ k).symm

theorem cartier (p : ℕ) [hp : Fact p.Prime] [CharP R p] (ψ φ : R1) (hφ0 : constantCoeff φ = 0)
    (hφ1 : PowerSeries.coeff 1 (φ : PowerSeries R) = 1) :
    PowerSeries.coeff (p - 1) (subst (fun _ : Unit => φ) ψ * pd () φ : PowerSeries R) =
      PowerSeries.coeff (p - 1) (ψ : PowerSeries R) := by
  have hS : HasSubst (fun _ : Unit => φ) := FGL.hs (fun _ => hφ0)
  -- `φ = T φ₁`
  obtain ⟨φ₁, hφ₁⟩ : (PowerSeries.X : PowerSeries R) ∣ φ := by
    rw [PowerSeries.X_dvd_iff]; exact hφ0
  have hcc1 : PowerSeries.constantCoeff φ₁ = 1 := by
    have := congrArg (PowerSeries.coeff 1) hφ₁
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
    rw [← this]; exact hφ1
  have hpd0 : PowerSeries.constantCoeff (pd () φ : PowerSeries R) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_pd', hφ1]; simp
  obtain ⟨ρ, hρ⟩ := exists_split (ψ : PowerSeries R) p
  have hsub : subst (fun _ : Unit => φ) ψ = ∑ n ∈ Finset.range p,
      MvPowerSeries.C (PowerSeries.coeff n (ψ : PowerSeries R)) * φ ^ n +
      φ ^ p * subst (fun _ : Unit => φ) (ρ : R1) := by
    conv_lhs => rw [show ψ = ((ψ : PowerSeries R) : R1) from rfl, hρ]
    rw [subst_add hS, subst_mul hS, subst_pow hS]
    erw [subst_X hS]
    congr 1
    rw [← coe_substAlgHom hS, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [coe_substAlgHom hS, subst_mul hS, subst_pow hS]
    erw [subst_X hS, subst_C]
  -- each monomial
  have hmono : ∀ n < p, PowerSeries.coeff (p - 1) (φ ^ n * pd () φ : PowerSeries R) =
      if n = p - 1 then 1 else 0 := by
    intro n hn
    split_ifs with hn1
    · subst hn1
      have hpow : (φ ^ (p - 1) : PowerSeries R) = PowerSeries.X ^ (p - 1) * φ₁ ^ (p - 1) := by
        rw [show (φ : PowerSeries R) = PowerSeries.X * φ₁ from hφ₁, mul_pow]
      rw [hpow, mul_assoc]
      have := PowerSeries.coeff_X_pow_mul (φ₁ ^ (p - 1) * pd () φ : PowerSeries R) (p - 1) 0
      rw [zero_add] at this
      rw [this, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, hcc1, hpd0]; simp
    · have h1 : pd () (φ ^ (n + 1)) = ((n : R1) + 1) * φ ^ n * pd () φ := pd_pow_succ φ n
      have h2 : PowerSeries.coeff (p - 1) (pd () (φ ^ (n + 1)) : PowerSeries R) = 0 := by
        rw [coeff_pd']
        have : ((p - 1 : ℕ) : R) + 1 = 0 := by
          rw [show ((p - 1 : ℕ) : R) + 1 = ((p - 1 + 1 : ℕ) : R) by push_cast; ring,
            Nat.sub_add_cancel hp.out.one_lt.le, CharP.cast_eq_zero]
        rw [this, mul_zero]
      rw [h1, mul_assoc, show ((n : R1) + 1 : PowerSeries R) = PowerSeries.C ((n + 1 : ℕ) : R) by
        rw [← natCast_R1']; push_cast; rfl, PowerSeries.coeff_C_mul] at h2
      refine natCast_mul_eq_zero p (k := n + 1) ?_ h2
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
  rw [hsub, add_mul, map_add, Finset.sum_mul, map_sum]
  have htail : PowerSeries.coeff (p - 1)
      (φ ^ p * subst (fun _ : Unit => φ) (ρ : R1) * pd () φ : PowerSeries R) = 0 := by
    have hpow : (φ ^ p : PowerSeries R) = PowerSeries.X ^ p * φ₁ ^ p := by
      rw [show (φ : PowerSeries R) = PowerSeries.X * φ₁ from hφ₁, mul_pow]
    rw [hpow, mul_assoc, mul_assoc, PowerSeries.coeff_X_pow_mul']
    rw [if_neg (by have := hp.out.one_lt; omega)]
  rw [htail, add_zero]
  have hterm : ∀ n ∈ Finset.range p, PowerSeries.coeff (p - 1)
      (MvPowerSeries.C (PowerSeries.coeff n (ψ : PowerSeries R)) * φ ^ n * pd () φ : PowerSeries R) =
      if n = p - 1 then PowerSeries.coeff n (ψ : PowerSeries R) else 0 := by
    intro n hn
    rw [mul_assoc]
    erw [PowerSeries.coeff_C_mul]
    rw [hmono n (Finset.mem_range.mp hn)]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range p) (p - 1)]
  rw [if_pos (Finset.mem_range.mpr (by have := hp.out.one_lt; omega))]

end TateFormal
