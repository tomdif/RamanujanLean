import RamanujanTau.UBound.Final

/-!
# Specialization to `K = ℂ_ℓ`

`φC : ℤ_ℓ → ℂ_ℓ` (via `ℚ_ℓ`) is isometric, `‖ℓ‖ = ℓ⁻¹`, and `ℂ_ℓ` is complete, ultrametric and
algebraically closed (Mathlib). So the analytic side conditions of `UB_of_geom` are discharged and the
final theorem rests on: the non-canonical quotient family `Q` over `ℂ_ℓ` with `QuotHyp`, `GeomU`, `HQ`.
-/

set_option autoImplicit false

namespace UBound
open AtkinOBrienFinal DBound KatzForms UpContraction

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime]

/-- `ℤ_ℓ → ℂ_ℓ`. -/
noncomputable def φC (ℓ : ℕ) [Fact ℓ.Prime] : ℤ_[ℓ] →+* ℂ_[ℓ] :=
  (algebraMap ℚ_[ℓ] ℂ_[ℓ]).comp PadicInt.Coe.ringHom

lemma norm_algebraMap_Cp (x : ℚ_[ℓ]) : ‖algebraMap ℚ_[ℓ] ℂ_[ℓ] x‖ = ‖x‖ := by
  rw [IsScalarTower.algebraMap_apply ℚ_[ℓ] (PadicAlgCl ℓ) ℂ_[ℓ]]
  rw [← PadicComplex.coe_eq, PadicComplex.norm_extends, PadicAlgCl.norm_extends]

lemma norm_φC (x : ℤ_[ℓ]) : ‖φC ℓ x‖ ≤ 1 := by
  rw [φC, RingHom.comp_apply, norm_algebraMap_Cp]; exact x.2

lemma norm_ell_Cp : ‖(ℓ : ℂ_[ℓ])‖ = (ℓ : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[ℓ] ℂ_[ℓ]), norm_algebraMap_Cp, Padic.norm_p]

lemma ell_Cp_pos : 0 < ‖(ℓ : ℂ_[ℓ])‖ := by
  rw [norm_ell_Cp]; exact inv_pos.mpr (by exact_mod_cast hℓp.out.pos)

lemma ell_Cp_lt_one : ‖(ℓ : ℂ_[ℓ])‖ < 1 := by
  rw [norm_ell_Cp]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hℓp.out.one_lt)

/-- **(UB) over `ℂ_ℓ`**: `QuotHyp + GeomU ⟹ UB`, every prime `ℓ ≥ 5`. -/
theorem UB_of_geom_Cp (hℓ : 5 ≤ ℓ) (Q : WeierstrassCurve ℂ_[ℓ] → Fin ℓ → WeierstrassCurve ℂ_[ℓ])
    (hQ : QuotHyp ℓ (Eh (φC ℓ) hℓ) Q) (hG : GeomU hℓ (φC ℓ) Q) : UB ℓ hℓ :=
  UB_of_geom hℓ (φC ℓ) norm_φC ell_Cp_pos ell_Cp_lt_one Q hQ hG

/-- **The final theorem for `ℓ = 13`** on `QuotHyp + GeomU` (over `ℂ_13`) and `HQ`. -/
theorem atkin_obrien_13_Cp (Q : WeierstrassCurve ℂ_[13] → Fin 13 → WeierstrassCurve ℂ_[13])
    (hQ : QuotHyp 13 (Eh (φC 13) (by norm_num : 5 ≤ 13)) Q)
    (hG : GeomU (by norm_num : 5 ≤ 13) (φC 13) Q) (hHQ : HQ 13 (by norm_num)) :
    ∃ κ : ℤ_[13], (∃ d : ℤ_[13], κ = 6 + 13 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 13 ^ m * n + 1 →
        (13 : ℤ_[13]) ^ m ∣ (Fintype.card (Nat.Partition ((13 ^ (m + 2) * n + 1) / 24)) : ℤ_[13]) -
          κ * (Fintype.card (Nat.Partition ((13 ^ m * n + 1) / 24)) : ℤ_[13]) :=
  VLayer.atkin_obrien_13''' (UB_of_geom_Cp _ Q hQ hG) hHQ

/-- **The final theorem for `ℓ = 17`** on `QuotHyp + GeomU` (over `ℂ_17`) and `HQ`. -/
theorem atkin_obrien_17_Cp (Q : WeierstrassCurve ℂ_[17] → Fin 17 → WeierstrassCurve ℂ_[17])
    (hQ : QuotHyp 17 (Eh (φC 17) (by norm_num : 5 ≤ 17)) Q)
    (hG : GeomU (by norm_num : 5 ≤ 17) (φC 17) Q) (hHQ : HQ 17 (by norm_num)) :
    ∃ κ : ℤ_[17], (∃ d : ℤ_[17], κ = 6 + 17 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 17 ^ m * n + 1 →
        (17 : ℤ_[17]) ^ m ∣ (Fintype.card (Nat.Partition ((17 ^ (m + 2) * n + 1) / 24)) : ℤ_[17]) -
          κ * (Fintype.card (Nat.Partition ((17 ^ m * n + 1) / 24)) : ℤ_[17]) :=
  VLayer.atkin_obrien_17''' (UB_of_geom_Cp _ Q hQ hG) hHQ

/-- **The final theorem for `ℓ = 19`** on `QuotHyp + GeomU` (over `ℂ_19`) and `HQ`. -/
theorem atkin_obrien_19_Cp (Q : WeierstrassCurve ℂ_[19] → Fin 19 → WeierstrassCurve ℂ_[19])
    (hQ : QuotHyp 19 (Eh (φC 19) (by norm_num : 5 ≤ 19)) Q)
    (hG : GeomU (by norm_num : 5 ≤ 19) (φC 19) Q) (hHQ : HQ 19 (by norm_num)) :
    ∃ κ : ℤ_[19], (∃ d : ℤ_[19], κ = 10 + 19 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 19 ^ m * n + 1 →
        (19 : ℤ_[19]) ^ m ∣ (Fintype.card (Nat.Partition ((19 ^ (m + 2) * n + 1) / 24)) : ℤ_[19]) -
          κ * (Fintype.card (Nat.Partition ((19 ^ m * n + 1) / 24)) : ℤ_[19]) :=
  VLayer.atkin_obrien_19''' (UB_of_geom_Cp _ Q hQ hG) hHQ

/-- **The final theorem for `ℓ = 23`** on `QuotHyp + GeomU` (over `ℂ_23`) and `HQ`. -/
theorem atkin_obrien_23_Cp (Q : WeierstrassCurve ℂ_[23] → Fin 23 → WeierstrassCurve ℂ_[23])
    (hQ : QuotHyp 23 (Eh (φC 23) (by norm_num : 5 ≤ 23)) Q)
    (hG : GeomU (by norm_num : 5 ≤ 23) (φC 23) Q) (hHQ : HQ 23 (by norm_num)) :
    ∃ κ : ℤ_[23], (∃ d : ℤ_[23], κ = 5 + 23 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 23 ^ m * n + 1 →
        (23 : ℤ_[23]) ^ m ∣ (Fintype.card (Nat.Partition ((23 ^ (m + 2) * n + 1) / 24)) : ℤ_[23]) -
          κ * (Fintype.card (Nat.Partition ((23 ^ m * n + 1) / 24)) : ℤ_[23]) :=
  VLayer.atkin_obrien_23''' (UB_of_geom_Cp _ Q hQ hG) hHQ

end UBound
