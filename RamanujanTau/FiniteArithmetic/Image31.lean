import RamanujanTau.FiniteArithmetic.Cert31Image
import RamanujanTau.FiniteArithmetic.EnvelopeReduction
import RamanujanTau.AtkinOBrienFinal.Transfer

/-! The image of D on the entire first Katz envelope is a line modulo 31.
The ambient space of cusp forms has dimension two; no rank-one assumption
about that ambient space is used. -/
set_option autoImplicit false
namespace RamanujanTau.FiniteArithmetic.Image31
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal Cert31

lemma f_coeff (n : ℕ) (hn : n < 3) :
    coeff n (Ψ 31 f) = if n = 2 then 1 else 0 := by
  rw [Cg_coeff cg_LF (by omega)]
  interval_cases n <;> decide +kernel

lemma g_coeff (n : ℕ) (hn : n < 3) :
    coeff n (Ψ 31 g) = if n = 0 then 0 else if n = 1 then 29 else 2 := by
  rw [Cg_coeff cg_LG (by omega)]
  interval_cases n <;> decide +kernel

/-- A Sturm-certified spanning set of M₃₀ modulo 31. -/
theorem span (a : PowerSeries ℤ) (ha : IntForm 30 a) :
    ∃ c₀ c₁ c₂ : ZMod 31,
      Ψ 31 a = C c₀ + C c₁ * Ψ 31 g + C c₂ * Ψ 31 f := by
  obtain ⟨A, hA, hAbar⟩ := exists_hasse_lift 31 (by norm_num)
  let c₀ := coeff 0 (Ψ 31 a)
  let c₁ := coeff 1 (Ψ 31 a) / 29
  let c₂ := coeff 2 (Ψ 31 a) - 2 * c₁
  let lift : ZMod 31 → ℤ := fun c => c.val
  have hlift (c : ZMod 31) : (lift c : ZMod 31) = c := by
    exact ZMod.natCast_zmod_val c
  have hC (c : ZMod 31) : Ψ 31 (C (lift c)) = C c := by
    rw [PowerSeries.map_C]
    congr 1
    exact hlift c
  let r := a - C (lift c₀) * A - C (lift c₁) * g - C (lift c₂) * f
  have hr : IntForm 30 r := ((ha.sub (hA.C_mul _)).sub (form_g.C_mul _)).sub (form_f.C_mul _)
  have hbar : Ψ 31 r = Ψ 31 a - C c₀ - C c₁ * Ψ 31 g - C c₂ * Ψ 31 f := by
    simp only [r, map_sub, map_mul, hC, hAbar, mul_one]
  have hz : Ψ 31 r = 0 := by
    apply sturm 31 3 30 (by norm_num) r hr
    rw [PowerSeries.X_pow_dvd_iff]
    intro n hn
    have hn' : n < 3 := hn
    rw [hbar]
    simp only [map_sub, coeff_C_mul, coeff_C, f_coeff n hn', g_coeff n hn']
    interval_cases n <;> norm_num [c₀, c₁, c₂, div_mul_cancel₀ _ (by decide : (29 : ZMod 31) ≠ 0)]
    ring
  rw [hbar] at hz
  exact ⟨c₀, c₁, c₂, by linear_combination hz⟩

theorem D_image (a : PowerSeries ℤ) (ha : IntForm 30 a) :
    ∃ c : ZMod 31, U 31 (Ψ 31 (Dz ^ δ 31) * Ψ 31 a) = C c * Ψ 31 f := by
  obtain ⟨c₀, c₁, c₂, h⟩ := span a ha
  refine ⟨10 * c₀ + 30 * c₁ + 29 * c₂, ?_⟩
  rw [h]
  rw [show Ψ 31 (Dz ^ δ 31) * (C c₀ + C c₁ * Ψ 31 g + C c₂ * Ψ 31 f) =
    C c₀ * Ψ 31 (Dz ^ δ 31) + C c₁ * (Ψ 31 (Dz ^ δ 31) * Ψ 31 g) +
      C c₂ * (Ψ 31 (Dz ^ δ 31) * Ψ 31 f) by ring]
  rw [U_add, U_add, U_C_mul, U_C_mul, U_C_mul, Cert31.seed, Cert31.odd_step, Cert31Image.D_f]
  simp only [← mul_assoc, ← map_mul, ← add_mul, ← map_add]
  congr 2
  ring

lemma reduce_D (F : PS 31) :
    PowerSeries.map (PadicInt.toZMod (p := 31)) (Dlin 31 F) =
      U 31 (Ψ 31 (Dz ^ δ 31) * PowerSeries.map (PadicInt.toZMod (p := 31)) F) := by
  rw [Dlin_apply, map_U, map_mul, Φl, map_map_int, Ψ_Φ 31 (by decide)]

theorem envelope_image (F : PS 31) (hF : Env 31 (by norm_num) 1 (α 31) F) :
    ∃ c : ZMod 31, PowerSeries.map (PadicInt.toZMod (p := 31)) (Dlin 31 F) = C c * Ψ 31 f := by
  obtain ⟨a, ha, he⟩ := envelope_reduction (by norm_num : 5 ≤ 31) (α 31)
    (fun i hi => (envelopes_ge_two (by norm_num : 13 ≤ 31) i hi).1) F hF
  rw [reduce_D, ← he]
  exact D_image a ha

/-- The q² line inside M₃₀, characterized without any chosen operator matrix. -/
theorem double_cusp_line (a : PowerSeries ℤ) (ha : IntForm 30 a)
    (h₀ : coeff 0 (Ψ 31 a) = 0) (h₁ : coeff 1 (Ψ 31 a) = 0) :
    ∃ c : ZMod 31, Ψ 31 a = C c * Ψ 31 f := by
  obtain ⟨c₀, c₁, c₂, h⟩ := span a ha
  have e₀ := congrArg (coeff 0) h
  have e₁ := congrArg (coeff 1) h
  simp only [map_add, coeff_C_mul, f_coeff 0 (by decide), g_coeff 0 (by decide)] at e₀
  simp only [map_add, coeff_C_mul, f_coeff 1 (by decide), g_coeff 1 (by decide)] at e₁
  norm_num [h₀] at e₀
  norm_num [h₁] at e₁
  have hc₁ : c₁ = 0 := e₁.resolve_right (by decide)
  exact ⟨c₂, by simpa [e₀.symm, hc₁] using h⟩

end RamanujanTau.FiniteArithmetic.Image31
