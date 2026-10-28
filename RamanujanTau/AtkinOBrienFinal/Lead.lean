import RamanujanTau.AtkinOBrienFinal.Katz
import RamanujanTau.BoylanWebb.Forms

/-!
# The leading digit (`hlead`): `dim S_{ℓ−1} = 1`

For `13 ≤ ℓ ≤ 24` (so `12 ≤ ℓ − 1 < 24`):
* `line`: by Sturm's bound (`BoylanWebb.sturm`, two coefficients), every integral form of weight `ℓ − 1`
  with constant term `≡ 0 (mod ℓ)` is `≡ c·f (mod ℓ)`, where `f` is any integral weight-`(ℓ−1)` form with
  `f ≡ 0` at the cusp and `a₁(f) ≢ 0`.
* `lead`: if `F ∈ A₁(γ)` (cuspidal, `v_i ≥ max(0, γ(i) − 1)`) and `γ(i) ≥ 2` for `i ≥ 2`
  (`AtkinOBrien.envelopes_ge_two`), then mod `ℓ` only the Katz digits `a₀ ∈ B₀ = ℤ_ℓ` and `a₁ ∈ B₁`
  survive, `F ≡ a₀Ā + a₁` is a cusp form of weight `ℓ − 1` mod `ℓ`, hence `F ≡ c·L (mod ℓ)` for any `L`
  with `L ≡ x·f`, `x ≠ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AtkinOBrienFinal
open PowerSeries AtkinOBrien BoylanWebb

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- **`dim S_{ℓ−1} = 1` mod `ℓ`** (Sturm). -/
theorem line (hℓ13 : 13 ≤ ℓ) (hℓ24 : ℓ ≤ 24) (f : PowerSeries ℤ) (hf : IntForm ((ℓ - 1 : ℕ) : ℤ) f)
    (hf0 : coeff 0 f = 0) (hf1 : coeff 1 (Ψ ℓ f) ≠ 0) (g : PowerSeries ℤ)
    (hg : IntForm ((ℓ - 1 : ℕ) : ℤ) g) (hg0 : coeff 0 (Ψ ℓ g) = 0) :
    ∃ c : ZMod ℓ, Ψ ℓ g = C c * Ψ ℓ f := by
  set c : ZMod ℓ := coeff 1 (Ψ ℓ g) / coeff 1 (Ψ ℓ f) with hc
  refine ⟨c, ?_⟩
  have hcast : ((((c.val : ℕ) : ℤ)) : ZMod ℓ) = c := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  set h := g - C ((c.val : ℕ) : ℤ) * f with hh
  have hhf : IntForm ((ℓ - 1 : ℕ) : ℤ) h := hg.sub (hf.C_mul _)
  have hΨ : Ψ ℓ h = Ψ ℓ g - C c * Ψ ℓ f := by
    rw [hh, map_sub, map_mul, PowerSeries.map_C]
    simp only [eq_intCast, hcast]
  have h0 : Ψ ℓ h = 0 := by
    refine sturm ℓ 2 _ (by omega) h hhf ?_
    have ht : (((ℓ - 1 : ℕ) : ℤ)).toNat / 12 + 1 = 2 := by
      rw [Int.toNat_natCast]; omega
    rw [ht, PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · rw [hΨ, map_sub, hg0, coeff_C_mul, coeff_map, hf0, map_zero, mul_zero, sub_zero]
    · rw [hΨ, map_sub, coeff_C_mul, hc, div_mul_cancel₀ _ hf1, sub_self]
  rw [hΨ, sub_eq_zero] at h0
  exact h0

/-- reduction `ℤ → ℤ_ℓ → 𝔽_ℓ` is `Ψ`. -/
lemma map_map_int (g : PowerSeries ℤ) :
    PowerSeries.map (PadicInt.toZMod (p := ℓ)) (PowerSeries.map (Int.castRingHom ℤ_[ℓ]) g) = Ψ ℓ g := by
  ext n
  simp only [coeff_map, eq_intCast, map_intCast]

/-- **`hlead`**: an element of `A₁(γ)` is `≡ c·L (mod ℓ)`. -/
theorem lead (hℓ : 5 ≤ ℓ) (hℓ13 : 13 ≤ ℓ) (hℓ24 : ℓ ≤ 24) (f : PowerSeries ℤ)
    (hf : IntForm ((ℓ - 1 : ℕ) : ℤ) f) (hf0 : coeff 0 f = 0) (hf1 : coeff 1 (Ψ ℓ f) ≠ 0)
    (Lb : PS ℓ) (x : ZMod ℓ) (hx : x ≠ 0)
    (hLb : PowerSeries.map (PadicInt.toZMod (p := ℓ)) Lb = C x * Ψ ℓ f)
    (γ : ℕ → ℤ) (hγ : ∀ i, 2 ≤ i → 2 ≤ γ i) (F : PS ℓ) (hF : F ∈ envSub hℓ 1 γ) :
    ∃ r : ℤ_[ℓ], ∃ y : PS ℓ, F = r • Lb + (ℓ : ℤ_[ℓ]) • y := by
  obtain ⟨hF0, hFe⟩ := hF
  obtain ⟨I₀, a₀, haK₀, hA₀, hab₀⟩ := hFe 1
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
  have hg0 : coeff 0 (Ψ ℓ g) = 0 := by rw [hgF, coeff_map, hF0, map_zero]
  obtain ⟨c, hc⟩ := line hℓ13 hℓ24 f hf hf0 hf1 g hg hg0
  -- conclude
  set r : ℤ_[ℓ] := (((c * x⁻¹).val : ℕ) : ℤ_[ℓ])
  have hr : PadicInt.toZMod r = c * x⁻¹ := by rw [map_natCast, ZMod.natCast_zmod_val]
  obtain ⟨y, hy⟩ := PS_dvd_of_map (F - r • Lb) (by
    rw [map_sub, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, hr, hLb, ← hgF, hc,
      ← mul_assoc, ← map_mul, mul_assoc, inv_mul_cancel₀ hx, mul_one, sub_self])
  exact ⟨r, y, by rw [← hy]; abel⟩

end AtkinOBrienFinal
