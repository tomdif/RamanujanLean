import RamanujanTau.FiniteArithmetic.Rank607Structure

/-! # The stable module at 607 modulo 607

`Λ^odd(1, 1) ≅ (ℤ/607)²⁴`, so `rEll 607 1 = 24`.

The proof reduces the precision-two data modulo 607:
* `L(51) ≡ Σ t_j L(2j+3)` and `L(1) ≡ Σ rel1_j L(2j+3)`, coordinate by
  coordinate, so `L(3), …, L(49)` span the module, by `X`-stability;
* the coefficients `q²⁶ … q⁴⁹` of `L(3), …, L(49)` form a matrix with an
  explicit inverse modulo 607, so these 24 series are independent.
-/
set_option autoImplicit false
set_option maxRecDepth 100000

namespace RamanujanTau.FiniteArithmetic.Rank607One

open PowerSeries Rank607Program Rank607Series Rank607Final Rank607Structure BLBound
open BoylanWebb (L)

/-- Coefficients modulo 607. -/
abbrev R1 : Type := Rm 607 1

/-- Reduction from `ℤ/607²` to `ℤ/607`. -/
abbrev π : R →+* R1 := ZMod.castHom (by norm_num : 607 ^ 1 ∣ 607 ^ 2) R1

/-! ### Certificates -/

def r1 (j : ℕ) : R := (rel1Table.getD j 0 : ℕ)

/-- Coefficients `q^(i+26)` of `L(2j+3)` modulo 607, `i, j < 24`. -/
def A1 : Matrix (Fin 24) (Fin 24) R1 := fun i j => (entryAt i j : R1)

def K1 : Matrix (Fin 24) (Fin 24) R1 := fun i j => ((kTable.getD i []).getD j 0 : ℕ)

theorem inv_ok : K1 * A1 = 1 := by decide +kernel

theorem rel1_ok : ∀ k : Fin 102,
    (607 : R) * (crd 1 k - ∑ j : Fin 24, r1 j * crd (2 * (j : ℕ) + 3) k) = 0 := by
  decide +kernel

lemma pi_607 : π 607 = 0 := by decide

attribute [local irreducible] coordAt entryAt rel1Table kTable tTable

/-! ### Reduction -/

lemma red1 (f : PowerSeries ℤ) : redm 607 1 f = PowerSeries.map π (rd f) := by
  ext n
  simp [PowerSeries.coeff_map]

lemma map_smul_pi (c : R) (f : PowerSeries R) :
    PowerSeries.map π (c • f) = π c • PowerSeries.map π f := by
  rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, PowerSeries.map_C]

lemma diff_coords (b : ℕ) (h1 : 1 ≤ b) (h53 : b ≤ 53) (a : Fin 24 → R) :
    rd (L 607 b) - ∑ j : Fin 24, a j • V j =
      ∑ k ∈ Finset.range 102, C (crd b k - ∑ j : Fin 24, a j * crd (2 * (j : ℕ) + 3) k) * B k := by
  have h2 := sum_smul_L a (fun j : Fin 24 => 2 * (j : ℕ) + 3)
    (fun j => ⟨by dsimp only; omega, by dsimp only; have := j.isLt; omega⟩)
  rw [L_coords b h1 h53, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_sub, sub_mul]

/-- A coordinate relation that holds modulo 607 gives a relation of reduced series. -/
lemma map_rel (b : ℕ) (h1 : 1 ≤ b) (h53 : b ≤ 53) (a : Fin 24 → R)
    (h : ∀ k : Fin 102, (607 : R) * (crd b k - ∑ j : Fin 24, a j * crd (2 * (j : ℕ) + 3) k) = 0) :
    redm 607 1 (L 607 b) = ∑ j : Fin 24, π (a j) • redm 607 1 (L 607 (2 * (j : ℕ) + 3)) := by
  have hz : PowerSeries.map π (rd (L 607 b) - ∑ j : Fin 24, a j • V j) = 0 := by
    rw [diff_coords b h1 h53, map_sum]
    refine Finset.sum_eq_zero fun k hk => ?_
    obtain ⟨s, hs⟩ := dvd_of_mul_eq_zero (h ⟨k, Finset.mem_range.mp hk⟩)
    rw [map_mul, PowerSeries.map_C, hs, map_mul, pi_607, zero_mul, map_zero, zero_mul]
  rw [map_sub, map_sum, sub_eq_zero] at hz
  rw [red1, hz]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul_pi, red1]

/-! ### Span and independence -/

/-- `L(2j+3)` modulo 607. -/
noncomputable abbrev W (j : ℕ) : PowerSeries R1 := redm 607 1 (L 607 (2 * j + 3))

noncomputable def S1 : Submodule R1 (PowerSeries R1) :=
  Submodule.span R1 (Set.range fun j : Fin 24 => W j)

lemma W_mem (j : ℕ) (hj : j < 24) : W j ∈ S1 := Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩

lemma rel_mem (b : ℕ) (h1 : 1 ≤ b) (h53 : b ≤ 53) (a : Fin 24 → R)
    (h : ∀ k : Fin 102, (607 : R) * (crd b k - ∑ j : Fin 24, a j * crd (2 * (j : ℕ) + 3) k) = 0) :
    redm 607 1 (L 607 b) ∈ S1 := by
  rw [map_rel b h1 h53 a h]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (W_mem _ j.isLt)

lemma S1_stable : ∀ f ∈ S1, Xm 607 1 f ∈ S1 := by
  intro f hf
  have hle : S1 ≤ S1.comap (Xm 607 1) := by
    rw [S1, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    change Xm 607 1 (W j) ∈ S1
    have h := Xm_L (ℓ := 607) 1 ((j : ℕ) + 1)
    rw [show 2 * ((j : ℕ) + 1) + 1 = 2 * (j : ℕ) + 3 by ring] at h
    rw [h]
    by_cases hj : (j : ℕ) < 23
    · exact W_mem ((j : ℕ) + 1) (by omega)
    · have h24 : 2 * ((j : ℕ) + 1 + 1) + 1 = 51 := by omega
      rw [h24]
      exact rel_mem 51 (by norm_num) (by norm_num) (fun j => tv j) tor_ok
  exact hle hf

lemma L_mem1 (k : ℕ) : redm 607 1 (L 607 (2 * k + 1)) ∈ S1 := by
  induction k with
  | zero => exact rel_mem 1 le_rfl (by norm_num) (fun j => r1 j) rel1_ok
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact W_mem 0 (by norm_num)
    · rw [← Xm_L]
      exact S1_stable _ ih

theorem S1_eq_Lam : S1 = Lam 607 1 1 := by
  apply le_antisymm
  · rw [S1, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨(j : ℕ) + 1, by omega, by congr 2⟩
  · rw [Lam, Submodule.span_le]
    rintro _ ⟨k, -, rfl⟩
    exact L_mem1 k

lemma coeff_W (i j : Fin 24) : coeff ((i : ℕ) + 26) (W j) = A1 i j := by
  have h := entries_eq i j (by omega) (by omega)
  show coeff _ (redm 607 1 (L 607 (2 * (j : ℕ) + 3))) = _
  rw [red1, PowerSeries.coeff_map]
  change π (coeff ((i : ℕ) + 26) (rd (L 607 (2 * (j : ℕ) + 3)))) = _
  rw [h, map_natCast]
  rfl

theorem W_independent (x : Fin 24 → R1) (h : ∑ j, x j • W j = 0) : x = 0 := by
  have hA : A1.mulVec x = 0 := by
    funext i
    have hc := congrArg (coeff ((i : ℕ) + 26)) h
    rw [map_sum, map_zero] at hc
    simp only [coeff_smul, coeff_W, smul_eq_mul] at hc
    simpa [Matrix.mulVec, dotProduct, mul_comm] using hc
  rw [← Matrix.one_mulVec x, ← inv_ok, ← Matrix.mulVec_mulVec, hA, Matrix.mulVec_zero]

/-! ### The module and its rank -/

noncomputable def toSeries1 : (Fin 24 → R1) →ₗ[R1] PowerSeries R1 where
  toFun x := ∑ j, x j • W j
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [mul_smul, Finset.smul_sum]

lemma toSeries1_apply (x : Fin 24 → R1) : toSeries1 x = ∑ j, x j • W j := rfl

lemma toSeries1_mem (x : Fin 24 → R1) : toSeries1 x ∈ Lam 607 1 1 := by
  rw [← S1_eq_Lam, toSeries1_apply]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (W_mem _ j.isLt)

lemma toSeries1_injective : Function.Injective toSeries1 := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  exact W_independent x hx

lemma toSeries1_surj (f : PowerSeries R1) (hf : f ∈ Lam 607 1 1) : ∃ x, toSeries1 x = f := by
  rw [← S1_eq_Lam, S1, Submodule.mem_span_range_iff_exists_fun] at hf
  exact hf

attribute [local irreducible] toSeries1

/-- **`Λ^odd(1, 1) ≅ (ℤ/607)²⁴` at `ℓ = 607`.** -/
noncomputable def lamEquiv1 : (Fin 24 → R1) ≃ₗ[R1] Lam 607 1 1 :=
  LinearEquiv.ofBijective (LinearMap.codRestrict (Lam 607 1 1) toSeries1 toSeries1_mem)
    ⟨fun x y h => toSeries1_injective (by
      have h' := congrArg Subtype.val h
      rwa [LinearMap.codRestrict_apply, LinearMap.codRestrict_apply] at h'),
     fun f => (toSeries1_surj f.1 f.2).elim fun x hx => ⟨x, Subtype.ext hx⟩⟩

lemma det_ne_zero : A1.det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det inv_ok
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at h1
  have h10 : (1 : R1) ≠ 0 := by decide
  exact h10 h1.symm

/-- **`r₆₀₇(1) = 24`.** -/
theorem rEll_607_one : rEll 607 1 = 24 := by
  classical
  have hdet : Matrix.det (fun i j : Fin 24 => coeff ((i : ℕ) + 26) (W j)) ≠ 0 := by
    rw [show (fun i j : Fin 24 => coeff ((i : ℕ) + 26) (W j)) = A1 from
      funext fun i => funext fun j => coeff_W i j]
    exact det_ne_zero
  have hspan : Submodule.span R1 ((Finset.univ.image fun j : Fin 24 => W j : Finset _) :
      Set (PowerSeries R1)) = Lam 607 1 (2 * 1 - 1) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, ← S1_eq_Lam]
    rfl
  apply le_antisymm
  · have h : rEll 607 1 ≤ (Finset.univ.image fun j : Fin 24 => W j).card :=
      Nat.sInf_le ⟨_, rfl, hspan⟩
    exact h.trans (Finset.card_image_le.trans (by simp))
  · obtain ⟨s, hcard, hs⟩ := Nat.sInf_mem
      (s := {r | ∃ s : Finset (PowerSeries (Rm 607 1)), s.card = r ∧
        Submodule.span (Rm 607 1) (s : Set _) = Lam 607 1 (2 * 1 - 1)})
      ⟨_, _, rfl, hspan⟩
    have hc : 24 ≤ s.card := card_le_of_coeff_det_ne_zero (fun j : Fin 24 => W j)
      (fun i : Fin 24 => (i : ℕ) + 26) s (fun j => by
        rw [hs, show 2 * 1 - 1 = 1 from rfl, ← S1_eq_Lam]
        exact W_mem _ j.isLt) hdet
    simpa only [hcard, rEll] using hc

end RamanujanTau.FiniteArithmetic.Rank607One
