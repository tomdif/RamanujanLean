import RamanujanTau.FiniteArithmetic.Rank607Structure

/-! # The stabilization threshold at 607 modulo 607²

`b₆₀₇(2) = 3`: the map `X : Λ^odd(1, 2) → Λ^odd(3, 2)` is not a bijection.

Reason: `L(1)` does not lie in `Λ^odd(3, 2)`, so `Λ^odd(1, 2)` is strictly
larger than the finite module `Λ^odd(3, 2)`, and `X` maps the first onto the
second. The certificate is a linear functional on the 102 reconstruction
coordinates that vanishes on `L(3), …, L(51)` but not on `L(1)`. Coordinates
are well defined because the basis is triangular with unit leading terms.
-/
set_option autoImplicit false
set_option maxRecDepth 100000

namespace RamanujanTau.FiniteArithmetic.Rank607Threshold

open PowerSeries Rank607Program Rank607Series Rank607Final Rank607Structure Rank607Identities
  BLBound
open BoylanWebb (L)

/-! ### Certificate -/

def ph (k : ℕ) : R := (phiTable.getD k 0 : ℕ)

theorem phi_kill : ∀ j : Fin 25,
    ∑ k : Fin 102, ph k * crd (2 * (j : ℕ) + 3) k = 0 := by decide +kernel

theorem phi_L1 : ∑ k : Fin 102, ph k * crd 1 k ≠ 0 := by decide +kernel

attribute [local irreducible] coordAt phiTable

/-! ### The basis is triangular -/

/-- Power series `X^k G_k` with unit constant terms are independent. -/
theorem tri_indep {S : Type*} [CommRing S] (G : ℕ → PowerSeries S)
    (hG : ∀ k, IsUnit (constantCoeff (G k))) (n : ℕ) (c : ℕ → S)
    (h : ∑ k ∈ Finset.range n, C (c k) * (X ^ k * G k) = 0) : ∀ j < n, c j = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hc := congrArg (PowerSeries.coeff j) h
    rw [map_sum, map_zero, Finset.sum_eq_single j] at hc
    · rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply] at hc
      exact (hG j).mul_left_eq_zero.mp hc
    · intro k hk hkj
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
      split_ifs with hle
      · rw [ih k (lt_of_le_of_ne hle hkj) (lt_trans (lt_of_le_of_ne hle hkj) hj), zero_mul]
      · rw [mul_zero]
    · intro hj'
      exact absurd (Finset.mem_range.mpr hj) hj'

lemma unit_left {a b : PowerSeries R} (h : a * b = 1) : IsUnit a :=
  ⟨⟨a, b, h, by rw [mul_comm]; exact h⟩, rfl⟩

lemma unit_right {a b : PowerSeries R} (h : a * b = 1) : IsUnit b :=
  ⟨⟨b, a, by rw [mul_comm]; exact h, h⟩, rfl⟩

lemma unit_E4 : IsUnit (ModP.E4 R ^ 3) := unit_left vInv_spec

lemma unit_v : IsUnit vInv := unit_right vInv_spec

lemma unit_sigma : IsUnit (1 + sigmaPart : PowerSeries R) := unit_right E_sq_mul_sigma

lemma unit_W : IsUnit (W R) :=
  (MockTheta5.JTP.isUnit_qfacInf.pow 24).map (PowerSeries.map (Int.castRingHom R))

/-- The unit factor of the `k`-th basis series. -/
noncomputable def G (k : ℕ) : PowerSeries R :=
  (ModP.E4 R ^ 3) ^ 101 * (1 + sigmaPart) * (W R * vInv) ^ k

lemma B_eq (k : ℕ) : B k = X ^ k * G k := by
  show Bs vInv k = _
  rw [Bs, G, Dq_eq R]
  ring

lemma G_unit (k : ℕ) : IsUnit (constantCoeff (G k)) :=
  (((unit_E4.pow 101).mul unit_sigma).mul ((unit_W.mul unit_v).pow k)).map _

/-! ### `L(1)` is not in `Λ^odd(3, 2)` -/

theorem L1_not_mem : rd (L 607 1) ∉ Lam 607 2 3 := by
  intro hmem
  rw [← S_eq_Lam, S, Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨a, ha⟩ := hmem
  rw [sum_smul_L a (fun j : Fin 25 => 2 * (j : ℕ) + 3)
    (fun j => ⟨by dsimp only; omega, by dsimp only; have := j.isLt; omega⟩),
    L_coords 1 le_rfl (by norm_num)] at ha
  have hz : ∑ k ∈ Finset.range 102,
      C (∑ j, a j * crd (2 * (j : ℕ) + 3) k - crd 1 k) * (X ^ k * G k) = 0 := by
    simp_rw [← B_eq, map_sub, sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr ha
  have hk := tri_indep G G_unit 102 _ hz
  apply phi_L1
  have hc : ∀ k : Fin 102, crd 1 k = ∑ j, a j * crd (2 * (j : ℕ) + 3) k :=
    fun k => (sub_eq_zero.mp (hk k k.isLt)).symm
  simp_rw [hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  have := phi_kill j
  calc ∑ k : Fin 102, ph k * (a j * crd (2 * (j : ℕ) + 3) k)
      = a j * ∑ k : Fin 102, ph k * crd (2 * (j : ℕ) + 3) k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = 0 := by rw [this, mul_zero]

/-! ### The threshold -/

lemma not_bij_one : ¬ Set.BijOn (Xm 607 2) (Lam 607 2 1) (Lam 607 2 3) := by
  rintro ⟨hmaps, hinj, -⟩
  obtain ⟨-, hfin⟩ := chain_structure (ℓ := 607) (by norm_num) 2 (by norm_num) 1 (by norm_num)
  have hfin3 : (Lam 607 2 3 : Set (PowerSeries R)).Finite := by
    haveI := hfin
    exact Set.toFinite _
  have hfin1 : (Lam 607 2 1 : Set (PowerSeries R)).Finite :=
    Set.Finite.of_finite_image (hfin3.subset (Set.image_subset_iff.mpr hmaps)) hinj
  have hsub : (Lam 607 2 3 : Set (PowerSeries R)) ⊆ Lam 607 2 1 := by
    apply Submodule.span_mono
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨k, by omega, rfl⟩
  have hL1 : rd (L 607 1) ∈ Lam 607 2 1 := Submodule.subset_span ⟨0, le_rfl, rfl⟩
  have hss : (Lam 607 2 3 : Set (PowerSeries R)) ⊂ Lam 607 2 1 :=
    hsub.ssubset_of_not_subset fun h => L1_not_mem (h hL1)
  have hlt := Set.ncard_lt_ncard hss hfin1
  have hle := Set.ncard_le_ncard_of_injOn _ hmaps hinj hfin3
  omega

/-- **`b₆₀₇(2) = 3 = 2·2 - 1`.** -/
theorem bEll_607_two : bEll 607 2 = 3 := by
  have h3 : 3 ∈ bSet 607 2 := mem_bSet (ℓ := 607) (by norm_num) 2 (by norm_num) 1 (by norm_num)
  apply le_antisymm (Nat.sInf_le h3)
  obtain ⟨hodd, hbij⟩ := Nat.sInf_mem ⟨3, h3⟩
  by_contra hlt
  have h1 : sInf (bSet 607 2) = 1 := by
    obtain ⟨r, hr⟩ := hodd
    change ¬ 3 ≤ sInf (bSet 607 2) at hlt
    omega
  rw [h1] at hbij
  exact not_bij_one hbij

end RamanujanTau.FiniteArithmetic.Rank607Threshold
