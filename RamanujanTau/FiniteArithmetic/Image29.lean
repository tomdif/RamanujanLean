import RamanujanTau.FiniteArithmetic.Cert29Image
import RamanujanTau.FiniteArithmetic.EnvelopeReduction
import RamanujanTau.AtkinOBrienFinal.Transfer

/-! The image of D on the entire first Katz envelope is a line modulo 29.
The ambient space of cusp forms has dimension two; no rank-one assumption
about that ambient space is used. -/
set_option autoImplicit false
namespace RamanujanTau.FiniteArithmetic.Image29
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal Cert29

lemma f_coeff (n : ℕ) (hn : n < 3) :
    coeff n (Ψ 29 f) = if n = 2 then 1 else 0 := by
  rw [Cg_coeff cg_LF (by omega)]
  interval_cases n <;> decide +kernel

lemma g_coeff (n : ℕ) (hn : n < 3) :
    coeff n (Ψ 29 g) = if n = 0 then 0 else if n = 1 then 3 else 1 := by
  rw [Cg_coeff cg_LG (by omega)]
  interval_cases n <;> decide +kernel

/-- A Sturm-certified spanning set of M₂₈ modulo 29. -/
theorem span (a : PowerSeries ℤ) (ha : IntForm 28 a) :
    ∃ c₀ c₁ c₂ : ZMod 29,
      Ψ 29 a = C c₀ + C c₁ * Ψ 29 g + C c₂ * Ψ 29 f := by
  obtain ⟨A, hA, hAbar⟩ := exists_hasse_lift 29 (by norm_num)
  let c₀ := coeff 0 (Ψ 29 a)
  let c₁ := coeff 1 (Ψ 29 a) / 3
  let c₂ := coeff 2 (Ψ 29 a) - c₁
  let lift : ZMod 29 → ℤ := fun c => c.val
  have hlift (c : ZMod 29) : (lift c : ZMod 29) = c := by
    exact ZMod.natCast_zmod_val c
  have hC (c : ZMod 29) : Ψ 29 (C (lift c)) = C c := by
    rw [PowerSeries.map_C]
    congr 1
    exact hlift c
  let r := a - C (lift c₀) * A - C (lift c₁) * g - C (lift c₂) * f
  have hr : IntForm 28 r := ((ha.sub (hA.C_mul _)).sub (form_g.C_mul _)).sub (form_f.C_mul _)
  have hbar : Ψ 29 r = Ψ 29 a - C c₀ - C c₁ * Ψ 29 g - C c₂ * Ψ 29 f := by
    simp only [r, map_sub, map_mul, hC, hAbar, mul_one]
  have hz : Ψ 29 r = 0 := by
    apply sturm 29 3 28 (by norm_num) r hr
    rw [PowerSeries.X_pow_dvd_iff]
    intro n hn
    have hn' : n < 3 := hn
    rw [hbar]
    simp only [map_sub, coeff_C_mul, coeff_C, f_coeff n hn', g_coeff n hn']
    interval_cases n <;> norm_num [c₀, c₁, c₂, div_mul_cancel₀ _ (by decide : (3 : ZMod 29) ≠ 0)]
  rw [hbar] at hz
  exact ⟨c₀, c₁, c₂, by linear_combination hz⟩

theorem D_image (a : PowerSeries ℤ) (ha : IntForm 28 a) :
    ∃ c : ZMod 29, U 29 (Ψ 29 (Dz ^ δ 29) * Ψ 29 a) = C c * Ψ 29 f := by
  obtain ⟨c₀, c₁, c₂, h⟩ := span a ha
  refine ⟨8 * c₀ + 3 * c₁ + 21 * c₂, ?_⟩
  rw [h]
  rw [show Ψ 29 (Dz ^ δ 29) * (C c₀ + C c₁ * Ψ 29 g + C c₂ * Ψ 29 f) =
    C c₀ * Ψ 29 (Dz ^ δ 29) + C c₁ * (Ψ 29 (Dz ^ δ 29) * Ψ 29 g) +
      C c₂ * (Ψ 29 (Dz ^ δ 29) * Ψ 29 f) by ring]
  rw [U_add, U_add, U_C_mul, U_C_mul, U_C_mul, Cert29.seed, Cert29.odd_step, Cert29Image.D_f]
  simp only [← mul_assoc, ← map_mul, ← add_mul, ← map_add]
  congr 2
  ring

lemma reduce_D (F : PS 29) :
    PowerSeries.map (PadicInt.toZMod (p := 29)) (Dlin 29 F) =
      U 29 (Ψ 29 (Dz ^ δ 29) * PowerSeries.map (PadicInt.toZMod (p := 29)) F) := by
  rw [Dlin_apply, map_U, map_mul, Φl, map_map_int, Ψ_Φ 29 (by decide)]

theorem envelope_image (F : PS 29) (hF : Env 29 (by norm_num) 1 (α 29) F) :
    ∃ c : ZMod 29, PowerSeries.map (PadicInt.toZMod (p := 29)) (Dlin 29 F) = C c * Ψ 29 f := by
  obtain ⟨a, ha, he⟩ := envelope_reduction (by norm_num : 5 ≤ 29) (α 29)
    (fun i hi => (envelopes_ge_two (by norm_num : 13 ≤ 29) i hi).1) F hF
  rw [reduce_D, ← he]
  exact D_image a ha

/-- The q² line inside M₂₈, characterized without any chosen operator matrix. -/
theorem double_cusp_line (a : PowerSeries ℤ) (ha : IntForm 28 a)
    (h₀ : coeff 0 (Ψ 29 a) = 0) (h₁ : coeff 1 (Ψ 29 a) = 0) :
    ∃ c : ZMod 29, Ψ 29 a = C c * Ψ 29 f := by
  obtain ⟨c₀, c₁, c₂, h⟩ := span a ha
  have e₀ := congrArg (coeff 0) h
  have e₁ := congrArg (coeff 1) h
  simp only [map_add, coeff_C_mul, f_coeff 0 (by decide), g_coeff 0 (by decide)] at e₀
  simp only [map_add, coeff_C_mul, f_coeff 1 (by decide), g_coeff 1 (by decide)] at e₁
  norm_num [h₀] at e₀
  norm_num [h₁] at e₁
  have hc₁ : c₁ = 0 := e₁.resolve_right (by decide)
  exact ⟨c₂, by simpa [e₀.symm, hc₁] using h⟩

end RamanujanTau.FiniteArithmetic.Image29
