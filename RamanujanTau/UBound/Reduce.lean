import RamanujanTau.UBound.Exist
import RamanujanTau.UpContraction.Main

/-!
# `AtkinOBrienFinal.UB` from the geometric description of `U` (reconciliation with `UpContraction`)

Let `K` be complete, ultrametric, algebraically closed, with an integral `φ : ℤ_ℓ →+* K`
(`0 < ‖ℓ‖ < 1`), and `Q W c` (`c : Fin ℓ`) the non-canonical quotients of a test curve `W`.

`U_isKatz` (unconditional) gives the integral Katz expansion `c` of `U(b/E^j)` over `ℤ_ℓ`.
**`GeomU`** is the remaining geometric input about that expansion, transported to `K` by `φ`:

* *(overconvergence)* `Σ φ(c_i)/E^i` converges on `{‖E‖ ≥ ‖s‖}` for every `v(s) < ℓ/(ℓ+1)`;
* *(Katz 3.11 / q-expansion principle for `U`)* on the break region,
  `ℓ · (Σ φ(c_i)/E^i)(W) = Σ_{C ≠ H} (b/E^j)(W/C)`.

**`UB_of_geom`**: `QuotHyp` (Buzzard 3.3(v)) + `GeomU` ⟹ `AtkinOBrienFinal.UB ℓ hℓ`, for every prime
`ℓ ≥ 5`. This is `UpContraction.UB` fed with the `ℤ_ℓ`-expansion, plus the translation
"`‖φ x‖ ≤ ‖ℓ‖^u` ⟹ `ℓ^u ∣ x`" and `Kpiece ↦ katzPiece φ (Bz ℓ hℓ 0)`.

**`UB_of_geom_models`**: the same with `QuotHyp` replaced by the formal-group quotient models
(`UpContraction.quotHyp_of_models`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UBound
open PowerSeries ModP AtkinOBrienFinal AtkinOBrien DBound KatzForms Igusa UpContraction
open Filter Topology CanonicalIsogeny

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **The geometric input on `U`** for the Katz expansion of `U(b/E^j)`, `b ∈ B_j`. -/
def GeomU (φ : ℤ_[ℓ] →+* K) (Q : WeierstrassCurve K → Fin ℓ → WeierstrassCurve K) : Prop :=
  ∀ j, ∀ x ∈ Kpiece ℓ hℓ j, ∀ c : ℕ → Poly ℓ,
    IsKatz ℓ hℓ c (BoylanWebb.U ℓ (ModP.ev ℤ_[ℓ] x * Einv ℓ hℓ ^ j)) →
    (∀ s : K, ‖(ℓ : K)‖ ^ ℓ < ‖s‖ ^ (ℓ + 1) → ‖s‖ < 1 →
      Tendsto (fun i => gnorm (MvPolynomial.map φ (c i)) / ‖s‖ ^ i) atTop (𝓝 0)) ∧
    (∀ W, IsTest W → Brk ℓ (Eh φ hℓ) W →
      (ℓ : K) * kval (Eh φ hℓ) (fun i => MvPolynomial.map φ (c i)) (pt W) =
        ∑ c', MvPolynomial.eval (pt (Q W c')) (MvPolynomial.map φ x) /
          MvPolynomial.eval (pt (Q W c')) (Eh φ hℓ) ^ j)

/-- `‖φ x‖ ≤ ‖ℓ‖^n` forces `ℓ^n ∣ x`. -/
lemma dvd_of_norm_phi (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖)
    (hpK : ‖(ℓ : K)‖ < 1) (x : ℤ_[ℓ]) (n : ℕ) (h : ‖φ x‖ ≤ ‖(ℓ : K)‖ ^ n) :
    (ℓ : ℤ_[ℓ]) ^ n ∣ x := by
  by_cases hx : x = 0
  · rw [hx]; exact dvd_zero _
  have hu : ‖φ (PadicInt.unitCoeff hx : ℤ_[ℓ])‖ = 1 := norm_phi_unit φ hφ (Units.isUnit _)
  have hxe := PadicInt.unitCoeff_spec hx
  have hn : ‖φ x‖ = ‖(ℓ : K)‖ ^ x.valuation := by
    conv_lhs => rw [hxe]
    rw [map_mul, map_pow, map_natCast, norm_mul, hu, one_mul, norm_pow]
  rw [hn] at h
  have hle : n ≤ x.valuation := (pow_le_pow_iff_right_of_lt_one₀ hε hpK).mp h
  rw [hxe]
  exact Dvd.dvd.mul_left (pow_dvd_pow _ hle) _

omit [IsUltrametricDist K] in
lemma map_mem_katzPiece (φ : ℤ_[ℓ] →+* K) {i : ℕ} {P : Poly ℓ} (hP : P ∈ Kpiece ℓ hℓ i) :
    MvPolynomial.map φ P ∈ katzPiece φ (Bz ℓ hℓ 0) i := by
  classical
  rw [P.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hdS : d ∈ S ℓ hℓ (0 + i * (ℓ - 1)) := by
    rw [zero_add]; exact (mem_Kpiece hℓ).mp hP hd
  rw [MvPolynomial.map_monomial, show MvPolynomial.monomial d (φ (P.coeff d)) =
      φ (P.coeff d) • MvPolynomial.map φ (MvPolynomial.monomial d (1 : ℤ_[ℓ])) by
    rw [MvPolynomial.map_monomial, map_one, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨d, hdS, rfl⟩, rfl⟩)

/-- **(UB) from `QuotHyp` and `GeomU`**, every prime `ℓ ≥ 5`. -/
theorem UB_of_geom [CompleteSpace K] [IsAlgClosed K] (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hε : 0 < ‖(ℓ : K)‖) (hpK : ‖(ℓ : K)‖ < 1)
    (Q : WeierstrassCurve K → Fin ℓ → WeierstrassCurve K) (hQ : QuotHyp ℓ (Eh φ hℓ) Q)
    (hG : GeomU hℓ φ Q) : UB ℓ hℓ := by
  intro j x hx
  obtain ⟨c, hc⟩ := U_isKatz hℓ j hx
  obtain ⟨hdec, hU⟩ := hG j x hx c hc
  have hbj : gnorm (MvPolynomial.map φ x) ≤ 1 :=
    gnorm_le zero_le_one fun d => by rw [MvPolynomial.coeff_map]; exact hφ _
  have hB := UpContraction.UB φ hφ hε hpK hℓ Q hQ j (MvPolynomial.map φ x) hbj
    (fun i => MvPolynomial.map φ (c i)) (fun i => map_mem_katzPiece hℓ φ (hc.1 i))
    (fun i d => ⟨(c i).coeff d, 0, by rw [MvPolynomial.coeff_map, pow_zero, div_one]⟩) hdec hU
  refine ⟨c, hc, fun i => Poly_Dvd_of_coeff _ fun d => Dvd_iff_dvd.mpr ?_⟩
  have h := hB i d
  rw [MvPolynomial.coeff_map] at h
  apply dvd_of_norm_phi φ hφ hε hpK
  rcases le_or_gt (u ℓ i j) 0 with hu | hu
  · rw [show (u ℓ i j).toNat = 0 by omega, pow_zero]; exact hφ _
  · have e : u ℓ i j = ((u ℓ i j).toNat : ℤ) := by omega
    rw [e, zpow_natCast] at h; exact h

/-- **(UB) from `GeomU` and formal-group quotient models** (`SSData` + ordinary locus). -/
theorem UB_of_geom_models [CompleteSpace K] [IsAlgClosed K] [Algebra ℤ_[ℓ] (integers K)]
    (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, (((algebraMap ℤ_[ℓ] (integers K) x) : integers K) : K) = φ x)
    (hε : 0 < ‖(ℓ : K)‖) (hpK : ‖(ℓ : K)‖ < 1)
    (Q : WeierstrassCurve K → Fin ℓ → WeierstrassCurve K)
    (hss : ∀ W, IsTest W → Brk ℓ (Eh φ hℓ) W → ‖MvPolynomial.eval (pt W) (Eh φ hℓ)‖ < 1 →
      SSData ℓ W (Q W))
    (hord : ∀ W, IsTest W → ‖MvPolynomial.eval (pt W) (Eh φ hℓ)‖ = 1 → ∀ c,
      IsTest (Q W c) ∧ ‖MvPolynomial.eval (pt (Q W c)) (Eh φ hℓ)‖ = 1)
    (hG : GeomU hℓ φ Q) : UB ℓ hℓ := by
  have hφ1 : ∀ x, ‖φ x‖ ≤ 1 := fun x => by
    rw [← hφ x]; exact (algebraMap ℤ_[ℓ] (integers K) x).2
  exact UB_of_geom hℓ φ hφ1 hε hpK Q (quotHyp_of_models φ hφ hℓ hε Q hss hord) hG

end UBound
