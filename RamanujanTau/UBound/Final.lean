import RamanujanTau.UBound.Reduce
import RamanujanTau.VLayer.DBQ

/-!
# The final theorem on `QuotHyp + GeomU + HQ`

`VLayer.atkin_obrien_ℓ''' (hUB : UB ℓ) (hQ : HQ ℓ)` with `hUB` supplied by `UBound.UB_of_geom`:
for `ℓ ∈ {13, 17, 19, 23}` there is `κ ∈ ℤ_ℓ`, `κ ≡ 6, 6, 10, 5 (mod ℓ)`, with
`ℓ^m ∣ p((ℓ^{m+2}n+1)/24) − κ·p((ℓ^m n+1)/24)` for all `m ≥ 1`, `24 ∣ ℓ^m n + 1`.

Hypotheses: a complete algebraically closed ultrametric `K` with integral `φ : ℤ_ℓ → K`,
`0 < ‖ℓ‖ < 1`; non-canonical quotient curves `Q` with `QuotHyp` (Buzzard 3.3(v)); `GeomU`
(overconvergence of `U(b/E^j)` + Katz's geometric `U`); `HQ` (sharp I2).
-/

set_option autoImplicit false

namespace UBound
open AtkinOBrienFinal DBound KatzForms UpContraction

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]

theorem atkin_obrien_13_geom (φ : ℤ_[13] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hε : 0 < ‖(13 : K)‖) (hpK : ‖(13 : K)‖ < 1)
    (Q : WeierstrassCurve K → Fin 13 → WeierstrassCurve K)
    (hQ : QuotHyp 13 (Eh φ (by norm_num : 5 ≤ 13)) Q) (hG : GeomU (by norm_num : 5 ≤ 13) φ Q)
    (hHQ : HQ 13 (by norm_num)) :
    ∃ κ : ℤ_[13], (∃ d : ℤ_[13], κ = 6 + 13 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 13 ^ m * n + 1 →
        (13 : ℤ_[13]) ^ m ∣ (Fintype.card (Nat.Partition ((13 ^ (m + 2) * n + 1) / 24)) : ℤ_[13]) -
          κ * (Fintype.card (Nat.Partition ((13 ^ m * n + 1) / 24)) : ℤ_[13]) :=
  VLayer.atkin_obrien_13''' (UB_of_geom _ φ hφ hε hpK Q hQ hG) hHQ

theorem atkin_obrien_17_geom (φ : ℤ_[17] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hε : 0 < ‖(17 : K)‖) (hpK : ‖(17 : K)‖ < 1)
    (Q : WeierstrassCurve K → Fin 17 → WeierstrassCurve K)
    (hQ : QuotHyp 17 (Eh φ (by norm_num : 5 ≤ 17)) Q) (hG : GeomU (by norm_num : 5 ≤ 17) φ Q)
    (hHQ : HQ 17 (by norm_num)) :
    ∃ κ : ℤ_[17], (∃ d : ℤ_[17], κ = 6 + 17 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 17 ^ m * n + 1 →
        (17 : ℤ_[17]) ^ m ∣ (Fintype.card (Nat.Partition ((17 ^ (m + 2) * n + 1) / 24)) : ℤ_[17]) -
          κ * (Fintype.card (Nat.Partition ((17 ^ m * n + 1) / 24)) : ℤ_[17]) :=
  VLayer.atkin_obrien_17''' (UB_of_geom _ φ hφ hε hpK Q hQ hG) hHQ

theorem atkin_obrien_19_geom (φ : ℤ_[19] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hε : 0 < ‖(19 : K)‖) (hpK : ‖(19 : K)‖ < 1)
    (Q : WeierstrassCurve K → Fin 19 → WeierstrassCurve K)
    (hQ : QuotHyp 19 (Eh φ (by norm_num : 5 ≤ 19)) Q) (hG : GeomU (by norm_num : 5 ≤ 19) φ Q)
    (hHQ : HQ 19 (by norm_num)) :
    ∃ κ : ℤ_[19], (∃ d : ℤ_[19], κ = 10 + 19 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 19 ^ m * n + 1 →
        (19 : ℤ_[19]) ^ m ∣ (Fintype.card (Nat.Partition ((19 ^ (m + 2) * n + 1) / 24)) : ℤ_[19]) -
          κ * (Fintype.card (Nat.Partition ((19 ^ m * n + 1) / 24)) : ℤ_[19]) :=
  VLayer.atkin_obrien_19''' (UB_of_geom _ φ hφ hε hpK Q hQ hG) hHQ

theorem atkin_obrien_23_geom (φ : ℤ_[23] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hε : 0 < ‖(23 : K)‖) (hpK : ‖(23 : K)‖ < 1)
    (Q : WeierstrassCurve K → Fin 23 → WeierstrassCurve K)
    (hQ : QuotHyp 23 (Eh φ (by norm_num : 5 ≤ 23)) Q) (hG : GeomU (by norm_num : 5 ≤ 23) φ Q)
    (hHQ : HQ 23 (by norm_num)) :
    ∃ κ : ℤ_[23], (∃ d : ℤ_[23], κ = 5 + 23 * d) ∧
      ∀ m, 1 ≤ m → ∀ n : ℕ, 24 ∣ 23 ^ m * n + 1 →
        (23 : ℤ_[23]) ^ m ∣ (Fintype.card (Nat.Partition ((23 ^ (m + 2) * n + 1) / 24)) : ℤ_[23]) -
          κ * (Fintype.card (Nat.Partition ((23 ^ m * n + 1) / 24)) : ℤ_[23]) :=
  VLayer.atkin_obrien_23''' (UB_of_geom _ φ hφ hε hpK Q hQ hG) hHQ

end UBound
