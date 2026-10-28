import RamanujanTau.SharpHQ.Newton

/-!
# `HQ` from the conjugate bound, and the final theorem on `UB` and `hConj`

* `HConj φ`: for every family `f` of classical forms (`f_k` isobaric of weight `12k`) whose
  q-expansions are the elementary symmetric functions of the Tate-curve conjugates `ys (Pdisc) 12 ζ`,
  the pointwise conjugate bound `ConjBound φ f` holds. This is the explicit geometric hypothesis
  (algebraicity together with the Lie valuations of the `ℓ+1` quotients, on test curves of the break
  region).
* **`HQ_of_conj`** (any complete algebraically closed ultrametric `K` with integral
  `φ : ℤ_[ℓ] →+* K`, `0 < ‖ℓ‖ < 1`, `ℓ ≥ 11`): `HConj φ → HQ ℓ hℓ`.
* `φC ℓ : ℤ_[ℓ] →+* ℂ_[ℓ]`, the canonical map. **`HQ_of_conj_C`** is `HQ_of_conj` over `ℂ_[ℓ]`.
* **`atkin_obrien_13⁗/17⁗/19⁗/23⁗ (hUB) (hConj)`**: the final theorem on `UB` and `HConj (φC ℓ)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SharpHQ
open PowerSeries ModP AtkinOBrienFinal AtkinOBrien DBound VLayer KatzForms Igusa

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

variable (ℓ) in
/-- **`hConj`**: every family of classical forms with the q-expansions of the `Δ`-modular equation
satisfies the pointwise conjugate bound. -/
def HConj {K : Type*} [NormedField K] [IsUltrametricDist K] (φ : ℤ_[ℓ] →+* K) : Prop :=
  ∀ f : ℕ → Poly ℓ, (∀ k, Iso (f k) (k * 12)) →
    (∃ ζ : PadicAlgCl ℓ, IsPrimitiveRoot ζ ℓ ∧ ∀ k, J ℓ (map (ιz ℓ) (ev ℤ_[ℓ] (f k))) =
      MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k)) →
    ConjBound ℓ hℓ φ f

/-- **The sharp (I2) from the conjugate bound** (`ℓ ≥ 11`). -/
theorem HQ_of_conj (h11 : 11 ≤ ℓ) {K : Type*} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsAlgClosed K] (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hε : 0 < ‖(ℓ : K)‖) (hpK : ‖(ℓ : K)‖ < 1) (hConj : HConj ℓ hℓ φ) : HQ ℓ hℓ := by
  obtain ⟨ζ, hζ⟩ := exists_zeta ℓ
  obtain ⟨f, hf, hJ, hsum⟩ := modular_equation hℓ (iso_Pdisc hℓ) (by norm_num : 1 ≤ 12) hζ
  exact HQ_of_coeffBound hℓ h11 φ hφ hε hpK hζ f hf hJ hsum
    (coeffBound_of_conj hℓ φ hε (hConj f hf ⟨ζ, hζ, hJ⟩))

variable (ℓ) in
/-- the canonical map `ℤ_[ℓ] → ℂ_[ℓ]`. -/
noncomputable def φC : ℤ_[ℓ] →+* ℂ_[ℓ] :=
  (algebraMap ℚ_[ℓ] ℂ_[ℓ]).comp PadicInt.Coe.ringHom

lemma norm_φC (x : ℤ_[ℓ]) : ‖φC ℓ x‖ = ‖x‖ := by
  rw [φC, RingHom.comp_apply, PadicInt.Coe.ringHom_apply]
  exact (PadicComplex.norm_extends' (p := ℓ) (x : ℚ_[ℓ])).trans (PadicInt.padic_norm_e_of_padicInt x)

lemma norm_ell_C : ‖((ℓ : ℕ) : ℂ_[ℓ])‖ = (ℓ : ℝ)⁻¹ := by
  have := norm_φC (ℓ := ℓ) (ℓ : ℤ_[ℓ])
  rw [map_natCast] at this
  rw [this, PadicInt.norm_p]

/-- **`HQ_of_conj` over `ℂ_[ℓ]`.** -/
theorem HQ_of_conj_C (h11 : 11 ≤ ℓ) (hConj : HConj ℓ hℓ (φC ℓ)) : HQ ℓ hℓ := by
  have h1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓp.out.one_lt
  refine HQ_of_conj hℓ h11 (φC ℓ) (fun x => (norm_φC x).trans_le (PadicInt.norm_le_one x))
    ?_ ?_ hConj
  · rw [norm_ell_C]; positivity
  · rw [norm_ell_C]; exact inv_lt_one_of_one_lt₀ h1

/-! ### the final theorem -/

theorem atkin_obrien_13'''' (hUB : UB 13 (by norm_num)) (hConj : HConj 13 (by norm_num) (φC 13)) :
    ∃ κ : ℤ_[13], (∃ d : ℤ_[13], κ = 6 + 13 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 13 ^ m * n + 1 →
        (13 : ℤ_[13]) ^ m ∣ (Fintype.card (Nat.Partition ((13 ^ (m + 2) * n + 1) / 24)) : ℤ_[13]) -
          κ * (Fintype.card (Nat.Partition ((13 ^ m * n + 1) / 24)) : ℤ_[13]) :=
  atkin_obrien_13''' hUB (HQ_of_conj_C _ (by norm_num) hConj)

theorem atkin_obrien_17'''' (hUB : UB 17 (by norm_num)) (hConj : HConj 17 (by norm_num) (φC 17)) :
    ∃ κ : ℤ_[17], (∃ d : ℤ_[17], κ = 6 + 17 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 17 ^ m * n + 1 →
        (17 : ℤ_[17]) ^ m ∣ (Fintype.card (Nat.Partition ((17 ^ (m + 2) * n + 1) / 24)) : ℤ_[17]) -
          κ * (Fintype.card (Nat.Partition ((17 ^ m * n + 1) / 24)) : ℤ_[17]) :=
  atkin_obrien_17''' hUB (HQ_of_conj_C _ (by norm_num) hConj)

theorem atkin_obrien_19'''' (hUB : UB 19 (by norm_num)) (hConj : HConj 19 (by norm_num) (φC 19)) :
    ∃ κ : ℤ_[19], (∃ d : ℤ_[19], κ = 10 + 19 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 19 ^ m * n + 1 →
        (19 : ℤ_[19]) ^ m ∣ (Fintype.card (Nat.Partition ((19 ^ (m + 2) * n + 1) / 24)) : ℤ_[19]) -
          κ * (Fintype.card (Nat.Partition ((19 ^ m * n + 1) / 24)) : ℤ_[19]) :=
  atkin_obrien_19''' hUB (HQ_of_conj_C _ (by norm_num) hConj)

theorem atkin_obrien_23'''' (hUB : UB 23 (by norm_num)) (hConj : HConj 23 (by norm_num) (φC 23)) :
    ∃ κ : ℤ_[23], (∃ d : ℤ_[23], κ = 5 + 23 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 23 ^ m * n + 1 →
        (23 : ℤ_[23]) ^ m ∣ (Fintype.card (Nat.Partition ((23 ^ (m + 2) * n + 1) / 24)) : ℤ_[23]) -
          κ * (Fintype.card (Nat.Partition ((23 ^ m * n + 1) / 24)) : ℤ_[23]) :=
  atkin_obrien_23''' hUB (HQ_of_conj_C _ (by norm_num) hConj)

end SharpHQ

