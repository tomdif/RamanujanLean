import RamanujanTau.VLayer.QB1
import RamanujanTau.DBound.Final

/-!
# The V-layer reduced to a single statement: `V(Q) ∈ B_E(r)`

Proved here (no rigid geometry; `VLayer.HG_holds`, `VLayer.Q_InB1`):
* `G = E/V(E) ∈ B_E(r)` (`HG`), for every prime `ℓ ≥ 5`;
* `Q = E/A_ℓ ∈ B_E(r)` (the `B_E(r)` form of (I2)), for `ℓ ≥ 11`.

`HW_of` only uses `HV` at `f = Q` and only uses `Q^ℓ ∈ B_E(r)`; so `HW` follows from

  **`HVQ`**: `V(Q) ∈ B_E(r)`, i.e. `v_i(Q(q^ℓ)) ≥ ⌈i/(ℓ+1)⌉`,

which is implied by `HQ ∧ HV` (`HVQ_of`). Final theorems `atkin_obrien_ℓ''`: hypotheses `UB` and
`HVQ` only.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VLayer
open PowerSeries AtkinOBrienFinal AtkinOBrien DBound

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

variable (ℓ) in
/-- **The remaining V-layer input**: `V(Q) ∈ B_E(r)` (Katz coordinates `v_i ≥ ⌈i/(ℓ+1)⌉`). -/
def HVQ : Prop := InB1 ℓ hℓ (Vl ℓ (Ql ℓ hℓ))

/-- `HQ ∧ HV → HVQ`. -/
lemma HVQ_of (hQ : HQ ℓ hℓ) (hV : HV ℓ hℓ) : HVQ ℓ hℓ := hV _ hQ

/-- **`HW` from `HVQ` alone** (`ℓ ≥ 11`): `(E^sW)² = Q^ℓ·V(Q)·G` with `Q, G ∈ B_E(r)` proved. -/
theorem HW_of_HVQ (h11 : 11 ≤ ℓ) (hVQ : HVQ ℓ hℓ) : HW ℓ hℓ := by
  have hsq : Ap hℓ (Bq ℓ 0) ((E ℓ hℓ ^ sN ℓ * Wl ℓ) * (E ℓ hℓ ^ sN ℓ * Wl ℓ)) := by
    rw [eta_identity_PS hℓ]
    exact Ap_mul B1_mul (Ap_mul B1_mul (Ap_pow hℓ B1_mul B1_zero (Ap_Q hℓ h11) ℓ)
      (Ap_of_InB1 hℓ hVQ)) (Ap_of_InB1 hℓ (HG_holds hℓ))
  have h1 : Dvd (ℓ : ℤ_[ℓ]) 1 (E ℓ hℓ ^ sN ℓ * Wl ℓ - 1) := by
    obtain ⟨y, hy⟩ := PS_dvd_of_map (E ℓ hℓ ^ sN ℓ * Wl ℓ - 1)
      (by rw [map_sub, EsW_cong hℓ, map_one, sub_self])
    exact ⟨y, by rw [pow_one, hy]⟩
  obtain ⟨c, hc, hcb⟩ := isKatz_of_Ap (sqrt_Ap B1_mul B1_zero h1 hsq)
  exact ⟨c, hc, fun i => by simpa [Bq] using hcb i⟩

/-- **(DB) from (UB) and `HVQ`.** -/
theorem DB_of_UB_HVQ (h11 : 11 ≤ ℓ) (hUB : UB ℓ hℓ) (hVQ : HVQ ℓ hℓ) : DB ℓ hℓ :=
  DB_of_UB hℓ hUB (HW_of_HVQ hℓ h11 hVQ)

theorem atkin_obrien_13'' (hUB : UB 13 (by norm_num)) (hVQ : HVQ 13 (by norm_num)) :
    ∃ κ : ℤ_[13], (∃ d : ℤ_[13], κ = 6 + 13 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 13 ^ m * n + 1 →
        (13 : ℤ_[13]) ^ m ∣ (Fintype.card (Nat.Partition ((13 ^ (m + 2) * n + 1) / 24)) : ℤ_[13]) -
          κ * (Fintype.card (Nat.Partition ((13 ^ m * n + 1) / 24)) : ℤ_[13]) :=
  atkin_obrien_13 hUB (DB_of_UB_HVQ _ (by norm_num) hUB hVQ)

theorem atkin_obrien_17'' (hUB : UB 17 (by norm_num)) (hVQ : HVQ 17 (by norm_num)) :
    ∃ κ : ℤ_[17], (∃ d : ℤ_[17], κ = 6 + 17 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 17 ^ m * n + 1 →
        (17 : ℤ_[17]) ^ m ∣ (Fintype.card (Nat.Partition ((17 ^ (m + 2) * n + 1) / 24)) : ℤ_[17]) -
          κ * (Fintype.card (Nat.Partition ((17 ^ m * n + 1) / 24)) : ℤ_[17]) :=
  atkin_obrien_17 hUB (DB_of_UB_HVQ _ (by norm_num) hUB hVQ)

theorem atkin_obrien_19'' (hUB : UB 19 (by norm_num)) (hVQ : HVQ 19 (by norm_num)) :
    ∃ κ : ℤ_[19], (∃ d : ℤ_[19], κ = 10 + 19 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 19 ^ m * n + 1 →
        (19 : ℤ_[19]) ^ m ∣ (Fintype.card (Nat.Partition ((19 ^ (m + 2) * n + 1) / 24)) : ℤ_[19]) -
          κ * (Fintype.card (Nat.Partition ((19 ^ m * n + 1) / 24)) : ℤ_[19]) :=
  atkin_obrien_19 hUB (DB_of_UB_HVQ _ (by norm_num) hUB hVQ)

theorem atkin_obrien_23'' (hUB : UB 23 (by norm_num)) (hVQ : HVQ 23 (by norm_num)) :
    ∃ κ : ℤ_[23], (∃ d : ℤ_[23], κ = 5 + 23 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 23 ^ m * n + 1 →
        (23 : ℤ_[23]) ^ m ∣ (Fintype.card (Nat.Partition ((23 ^ (m + 2) * n + 1) / 24)) : ℤ_[23]) -
          κ * (Fintype.card (Nat.Partition ((23 ^ m * n + 1) / 24)) : ℤ_[23]) :=
  atkin_obrien_23 hUB (DB_of_UB_HVQ _ (by norm_num) hUB hVQ)

end VLayer
