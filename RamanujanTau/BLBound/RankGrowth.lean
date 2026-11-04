import RamanujanTau.BLBound.Rank

/-!
# Rank growth with precision

Reduction of stable partition modules is surjective. Consequently their least
numbers of generators are nondecreasing with precision. Once the FKO bound is
attained at any precision, it is attained at every higher precision.

These statements concern the actual partition modules. No numerical rank claim
at prime 607 is assumed or established in this file.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.BLBound
open PowerSeries BoylanWebb

noncomputable section

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- The stable odd module is independent of the starting point in the proved range. -/
theorem Lam_stable_eq (h13 : 13 ≤ ℓ) {m k j : ℕ} (hm : 1 ≤ m)
    (hk : m ≤ k + 1) (hkj : k ≤ j) :
    Lam ℓ m (2 * k + 1) = Lam ℓ m (2 * j + 1) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hkj
  induction t with
  | zero => simp
  | succ t ih =>
    calc
      _ = Lam ℓ m (2 * (k + t) + 1) := ih (by omega)
      _ = Lam ℓ m (2 * (k + t + 1) + 1) := (chain_structure h13 m hm (k + t) (by omega)).1
      _ = _ := by congr 2

/-- Reduction on series, as a semilinear map between coefficient rings. -/
def precisionMap {m n : ℕ} (hmn : m ≤ n) :
    PowerSeries (Rm ℓ n) →ₛₗ[ZMod.castHom (pow_dvd_pow ℓ hmn) (Rm ℓ m)]
      PowerSeries (Rm ℓ m) where
  toFun := PowerSeries.map (ZMod.castHom (pow_dvd_pow ℓ hmn) (Rm ℓ m))
  map_add' := map_add _
  map_smul' c f := by
    simp only [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C]

lemma precisionMap_redm {m n : ℕ} (hmn : m ≤ n) (f : PowerSeries ℤ) :
    precisionMap (ℓ := ℓ) hmn (redm ℓ n f) = redm ℓ m f := by
  ext i
  simp [precisionMap, PowerSeries.coeff_map]

/-- Reduction sends a tail span onto the corresponding tail span at lower precision. -/
theorem precisionMap_Lam {m n : ℕ} (hmn : m ≤ n) (b : ℕ)
    [RingHomSurjective (ZMod.castHom (pow_dvd_pow ℓ hmn) (Rm ℓ m))] :
    (Lam ℓ n b).map (precisionMap (ℓ := ℓ) hmn) = Lam ℓ m b := by
  letI : RingHomSurjective (ZMod.castHom (pow_dvd_pow ℓ hmn) (Rm ℓ m)) :=
    ⟨ZMod.castHom_surjective _⟩
  rw [Lam, Submodule.map_span, Lam]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, precisionMap_redm hmn _⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨k, hk, rfl⟩, precisionMap_redm hmn _⟩

/-- **The number of generators of the stable partition module cannot decrease with precision.** -/
theorem rEll_mono (h13 : 13 ≤ ℓ) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    rEll ℓ m ≤ rEll ℓ n := by
  classical
  have hn : 1 ≤ n := by omega
  obtain ⟨s, -, hs⟩ := rank_Lam_le (ℓ := ℓ) h13 n hn (n - 1) (by omega)
  rw [show 2 * (n - 1) + 1 = 2 * n - 1 by omega] at hs
  obtain ⟨s, hcard, hspan⟩ := Nat.sInf_mem
    (s := {r | ∃ s : Finset (PowerSeries (Rm ℓ n)), s.card = r ∧
      Submodule.span (Rm ℓ n) (s : Set _) = Lam ℓ n (2 * n - 1)})
    ⟨_, s, rfl, hs⟩
  letI : RingHomSurjective (ZMod.castHom (pow_dvd_pow ℓ hmn) (Rm ℓ m)) :=
    ⟨ZMod.castHom_surjective _⟩
  let t := s.image (precisionMap (ℓ := ℓ) hmn)
  have ht : Submodule.span (Rm ℓ m) (t : Set _) = Lam ℓ m (2 * m - 1) := by
    rw [show (t : Set _) = precisionMap (ℓ := ℓ) hmn '' (s : Set _) by
      exact Finset.coe_image]
    rw [← Submodule.map_span, hspan, precisionMap_Lam (ℓ := ℓ) hmn]
    have h := Lam_stable_eq (ℓ := ℓ) h13 (m := m) (k := m - 1) (j := n - 1)
      hm (by omega) (by omega)
    simpa only [show 2 * (m - 1) + 1 = 2 * m - 1 by omega,
      show 2 * (n - 1) + 1 = 2 * n - 1 by omega] using h.symm
  have hmin : rEll ℓ m ≤ t.card := Nat.sInf_le ⟨t, rfl, ht⟩
  exact hmin.trans (Finset.card_image_le.trans (by simpa only [rEll] using hcard.le))

/-- **One finite-precision attainment of the FKO bound propagates to all higher precisions.** -/
theorem rEll_eq_bound_of_le (h13 : 13 ≤ ℓ) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (hattain : (ℓ + 12) / 24 ≤ rEll ℓ m) :
    rEll ℓ n = (ℓ + 12) / 24 := by
  exact le_antisymm (rEll_le h13 n (by omega)) (hattain.trans (rEll_mono h13 hm hmn))

end
end RamanujanTau.BLBound
