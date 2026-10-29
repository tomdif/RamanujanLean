import RamanujanTau.AtkinOBrienFinal.Lead

/-! Finite modular reduction of a Katz envelope, without a dimension-one or
cuspidality hypothesis. -/
set_option autoImplicit false
namespace RamanujanTau.FiniteArithmetic
open PowerSeries AtkinOBrien BoylanWebb AtkinOBrienFinal
variable {ℓ : ℕ} [Fact ℓ.Prime]

theorem envelope_reduction (hℓ : 5 ≤ ℓ) (γ : ℕ → ℤ)
    (hγ : ∀ i, 2 ≤ i → 2 ≤ γ i) (F : PS ℓ) (hF : Env ℓ hℓ 1 γ F) :
    ∃ g : PowerSeries ℤ, IntForm ((ℓ - 1 : ℕ) : ℤ) g ∧
      Ψ ℓ g = PowerSeries.map (PadicInt.toZMod (p := ℓ)) F := by
  obtain ⟨I₀, a₀, haK₀, hA₀, hab₀⟩ := hF 1
  set I := max I₀ 2 with hI
  set a := trunc I₀ a₀ with ha
  have haK : ∀ i, a i ∈ Kpiece ℓ hℓ i := trunc_mem hℓ haK₀
  have hA : Approx ℓ hℓ 1 I a F := approx_trunc hℓ hA₀ (le_max_left _ _)
  have hab : ∀ i, Dvd (ℓ : ℤ_[ℓ]) (max 0 (γ i - 1)).toNat (a i) := fun i => trunc_dvd i (hab₀ i)
  -- digits `i ≥ 2` vanish mod `ℓ`
  have hz : ∀ i, 2 ≤ i → MvPolynomial.map (PadicInt.toZMod (p := ℓ)) (a i) = 0 := by
    intro i hi
    obtain ⟨z, hz⟩ := Dvd_mono (a := 1) (by have := hγ i hi; omega) (hab i)
    rw [hz, pow_one, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_natCast,
      ZMod.natCast_self, map_zero, zero_mul]
  -- `F mod ℓ` is the sum of the first two digits
  set P₀ := MvPolynomial.map (PadicInt.toZMod (p := ℓ)) (a 0)
  set P₁ := MvPolynomial.map (PadicInt.toZMod (p := ℓ)) (a 1)
  have hFbar : PowerSeries.map (PadicInt.toZMod (p := ℓ)) F = ModP.ev (ZMod ℓ) P₀ + ModP.ev (ZMod ℓ) P₁ := by
    obtain ⟨g, hg⟩ := hA
    have e : F = ∑ i ∈ Finset.range I, ModP.ev ℤ_[ℓ] (a i) * Einv ℓ hℓ ^ i + (ℓ : ℤ_[ℓ]) ^ 1 • g := by
      rw [← hg]; abel
    rw [e, map_add, map_katzSum, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, map_pow,
      map_natCast, ZMod.natCast_self, zero_pow one_ne_zero, map_zero, zero_mul, add_zero,
      ← Finset.sum_range_add_sum_Ico _ (le_max_right I₀ 2 : 2 ≤ I)]
    rw [Finset.sum_eq_zero (s := Finset.Ico 2 I) (fun i hi => by
      rw [hz i (Finset.mem_Ico.mp hi).1, map_zero]), add_zero, Finset.sum_range_succ,
      Finset.sum_range_one]
  -- it is the reduction of a weight `ℓ − 1` integral form
  have hiso0 : ModP.Iso P₀ 0 := by
    have := iso_of_mem hℓ (i := 0) (P := P₀) ((Finset.coe_subset.mpr (MvPolynomial.support_map_subset _ _)).trans
      ((mem_Kpiece hℓ).mp (haK 0)))
    simpa using this
  have hiso1 : ModP.Iso P₁ (ℓ - 1) := by
    have := iso_of_mem hℓ (i := 1) (P := P₁) ((Finset.coe_subset.mpr (MvPolynomial.support_map_subset _ _)).trans
      ((mem_Kpiece hℓ).mp (haK 1)))
    simpa using this
  have hiso : ModP.Iso (P₀ * ModP.hasseBar ℓ hℓ + P₁) (ℓ - 1) := by
    refine MvPolynomial.IsWeightedHomogeneous.add ?_ hiso1
    exact ModP.iso_of_eq (hiso0.mul (ModP.iso_hasseBar hℓ)) (by simp)
  obtain ⟨g, hg, hgΨ⟩ := lift_iso ℓ (ℓ - 1) _ hiso
  have hgF : Ψ ℓ g = PowerSeries.map (PadicInt.toZMod (p := ℓ)) F := by
    rw [hgΨ, hFbar, map_add, map_mul, ModP.ev_hasseBar, mul_one]
  exact ⟨g, hg, hgF⟩

end RamanujanTau.FiniteArithmetic
