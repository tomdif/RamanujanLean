/-
# `UBSharp.QuotEBound` on the ordinary locus

For a test curve `W` of the break region with `‖E(W)‖ = 1` (ordinary), `H = Pt(T)` (kernel of
reduction):

* **`quotEBound_ord_partial`** (unconditional): every conjunct of `UBSharp.QuotEBound` except the
  `c₄/c₆` integrality conjunct:
  * `‖Δ(Wₛ/H)‖ ≤ ‖ℓ‖^12`, `‖Δ(Wₛ/C)‖ ≤ 1` (`C ≠ H`);
  * `‖E(Wₛ/H)‖ ≤ ‖ℓ‖^{ℓ−1}` (Vélu scaling `E(Wₛ/H) = μ^{ℓ−1} E(model)`, `‖μ‖ = ‖ℓ‖`, model
    integral);
  * `‖E(Wₛ/C)‖ ≤ 1` (`C ≠ H`, integral points ⇒ integral Vélu coefficients).
* **`quotEBound_ord`**: the full conclusion of `UBSharp.QuotEBound`, given **`ProdDelta ℓ K`**: the
  constant term of the Δ-modular equation, `∏_{|C| = ℓ} Δ(Wₛ/C) = ℓ^12 Δ(W)^{ℓ+1}` (Vélu
  normalization). It forces `‖Δ(Wₛ/H)‖ = ‖ℓ‖^12` and `‖Δ(Wₛ/C)‖ = 1`, i.e. good reduction of the
  integral models, whence `‖c₄‖³, ‖c₆‖² ≤ ‖Δ‖`.
-/
import RamanujanTau.OrdQuot.Final
import RamanujanTau.UBSharp.Velu
import RamanujanTau.QuotE.Combine

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OrdQuot
open MvPowerSeries EllipticFormal EllipticI2 CanonicalIsogeny QuotientHasse VeluLubin AllQuotients
  KatzForms

section Prod
variable (ℓ : ℕ) (K : Type*) [Field K] [CharZero K] [DecidableEq K]

/-- **the constant term of the Δ-modular equation** (Vélu normalization):
`∏_{|C| = ℓ} Δ(Wₛ/C) = ℓ^12 Δ(W)^{ℓ+1}` for every nonsingular `W` (`Wₛ` its `u = 1` short model). -/
def ProdDelta : Prop :=
  ∀ W : WeierstrassCurve K, W.Δ ≠ 0 →
    ∀ Z : Finset (Finset (Velu.short (ConjAlg.sa W) (ConjAlg.sb W)).Point),
    (∀ G, G ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ ↔ G ∈ Z) →
      ∏ G ∈ Z, (SubgroupSum.veluC G).Δ = (ℓ : K) ^ 12 * W.Δ ^ (ℓ + 1)

end Prod

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
  [CharZero K] [DecidableEq K]

local notation "𝒪" => CanonicalIsogeny.integers K

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-- `E(u • W) = u^{−(ℓ−1)} E(W)`. -/
lemma eval_Eh_scale (φ : ℤ_[ℓ] →+* K) (u : Kˣ) (W : WeierstrassCurve K) :
    MvPolynomial.eval (KatzForms.pt ((⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) • W))
        (Eh φ hℓ) = ((u⁻¹ : Kˣ) : K) ^ (ℓ - 1) * MvPolynomial.eval (KatzForms.pt W) (Eh φ hℓ) := by
  have h := HeckeQExp.aeval_ptR_scale (K := K) (L := K)
    (ModP.iso_map φ (ModP.iso_hasseA (p := ℓ) hℓ)) u W
  show MvPolynomial.eval (HeckeQExp.ptR (HeckeQExp.scaleChange u • W)) (Eh φ hℓ) =
    ((u⁻¹ : Kˣ) : K) ^ (ℓ - 1) * MvPolynomial.eval (HeckeQExp.ptR W) (Eh φ hℓ)
  rw [← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval]
  exact h

lemma integral_pt_toK (W : WeierstrassCurve ↥(CanonicalIsogeny.integers K)) :
    KatzForms.Integral (KatzForms.pt (toK W)) := by
  intro i
  fin_cases i
  · show ‖(toK W).c₄‖ ≤ 1
    rw [toK, WeierstrassCurve.map_c₄]; exact (W.c₄).2
  · show ‖-(toK W).c₆‖ ≤ 1
    rw [norm_neg, toK, WeierstrassCurve.map_c₆]; exact (W.c₆).2

lemma norm_E_le_of_integral (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) {x : Fin 2 → K}
    (hx : KatzForms.Integral x) : ‖MvPolynomial.eval x (Eh φ hℓ)‖ ≤ 1 :=
  (norm_eval_le hx _).trans (gnorm_le zero_le_one (Eh_integral φ hφ hℓ))

/-- **The ordinary-locus data**, shared by the partial and the full statement. -/
theorem ord_data (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖)
    (W : WeierstrassCurve K) (hW : IsTest W) (hB : UpContraction.Brk ℓ (Eh φ hℓ) W)
    (hord : ‖MvPolynomial.eval (KatzForms.pt W) (Eh φ hℓ)‖ = 1) :
    ‖(ℓ : K)‖ < 1 ∧ ‖(2 : K)‖ = 1 ∧ ‖(3 : K)‖ = 1 ∧
    ‖(Velu.short (ConjAlg.sa W) (ConjAlg.sb W)).Δ‖ = 1 ∧
    ∃ H ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ,
      ‖(SubgroupSum.veluC H).Δ‖ ≤ ‖(ℓ : K)‖ ^ 12 ∧
      (∃ (μ : K) (hμ : μ ≠ 0), ‖μ‖ = ‖(ℓ : K)‖ ∧ ∃ A'' B'' : ↥(CanonicalIsogeny.integers K),
        toK (shortO A'' B'') = ((⟨Units.mk0 μ hμ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) •
          (SubgroupSum.veluC H : WeierstrassCurve K))) ∧
      ∀ G ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ, G ≠ H →
        ‖SubgroupSum.aC G‖ ≤ 1 ∧ ‖SubgroupSum.bC G‖ ≤ 1 := by
  classical
  have hφ' : ∀ x, φ x ∈ CanonicalIsogeny.integers K := hφ
  letI : Algebra ℤ_[ℓ] 𝒪 := (φ.codRestrict (CanonicalIsogeny.integers K) hφ').toAlgebra
  have hφ'' : ∀ x, (((algebraMap ℤ_[ℓ] 𝒪 x) : 𝒪) : K) = φ x := fun x => rfl
  set E := MvPolynomial.eval (KatzForms.pt W) (Eh φ hℓ)
  have hl1 : ‖(ℓ : K)‖ < 1 :=
    EllipticI2.norm_p_lt_one hℓp.out.two_le (norm_nonneg _) hord.le hB
  obtain ⟨h2, h3⟩ := norm_two_three hl1 hℓ
  have h48 : ‖(48 : K)‖ = 1 := by
    rw [show (48 : K) = 2 ^ 4 * 3 by norm_num, norm_mul, norm_pow, h2, h3]; norm_num
  have h864 : ‖(864 : K)‖ = 1 := by
    rw [show (864 : K) = 2 ^ 5 * 3 ^ 3 by norm_num, norm_mul, norm_pow, norm_pow, h2, h3]; norm_num
  have hint := integral_pt hW
  have hsa : ‖ConjAlg.sa W‖ ≤ 1 := by
    have := hint 0
    simp only [KatzForms.pt, Matrix.cons_val_zero] at this
    rw [ConjAlg.sa, norm_div, norm_neg, h48, div_one]; exact this
  have hsb : ‖ConjAlg.sb W‖ ≤ 1 := by
    have := hint 1
    simp only [KatzForms.pt, Matrix.cons_val_one, Matrix.cons_val_fin_one, norm_neg] at this
    rw [ConjAlg.sb, norm_div, norm_neg, h864, div_one]; exact this
  set a : 𝒪 := ⟨ConjAlg.sa W, hsa⟩
  set b : 𝒪 := ⟨ConjAlg.sb W, hsb⟩
  have hWK : toK (shortO a b) = (Velu.short (ConjAlg.sa W) (ConjAlg.sb W) : WeierstrassCurve K) :=
    toK_shortO a b
  have hΔs : ‖(Velu.short (ConjAlg.sa W) (ConjAlg.sb W)).Δ‖ = 1 := by
    rw [ConjAlg.shortModel_Δ]; exact hW.2.2.2.2.2
  have hΔ : ‖(((shortO a b).Δ : 𝒪) : K)‖ = 1 := by
    have e := congrArg WeierstrassCurve.Δ hWK
    simp only [toK, WeierstrassCurve.map_Δ, Subring.subtype_apply] at e
    rw [e]; exact hΔs
  have hptW : KatzForms.pt (toK (shortO a b)) = KatzForms.pt W := by
    rw [hWK]; exact ConjAlg.shortModel_ptR W
  have hEE : E = ((UpContraction.EpO ℓ hℓ (shortO a b) : 𝒪) : K) := by
    rw [← UpContraction.eval_pt_toK φ hφ'' hℓ (shortO a b)]
    show MvPolynomial.eval (KatzForms.pt W) (Eh φ hℓ) =
      MvPolynomial.eval (KatzForms.pt (toK (shortO a b))) (Eh φ hℓ)
    rw [hptW]
  have hEp : ‖(ℓ : K)‖ < ‖E‖ :=
    UpContraction.lt_of_break ℓ (norm_nonneg _) (norm_nonneg _) hord.le hB
  have haE : ‖((hasse (formalGroup (shortO a b)) ℓ : 𝒪) : K)‖ = ‖E‖ := by
    rw [hEE]
    exact UpContraction.norm_hasse_eq_EpO ℓ hℓ (shortO a b)
      (lt_of_lt_of_le (hEE ▸ hEp) (le_max_right _ _))
  have ha : ‖hasse (formalGroup (shortO a b)) ℓ‖ = 1 := by
    show ‖((hasse (formalGroup (shortO a b)) ℓ : 𝒪) : K)‖ = 1
    rw [haE]; exact hord
  obtain ⟨H, hH, h1, hmod, hpts⟩ := velu_ord_data a b ℓ hℓ hε hl1 hΔ ha
  exact ⟨hl1, h2, h3, hΔs, H, hH, h1, hmod, fun G hG hne =>
    aC_bC_le_one hsa hsb h2 G (hpts G hG hne)⟩

lemma norm_short_Δ_le {A B : K} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) : ‖(Velu.short A B).Δ‖ ≤ 1 := by
  have hAO : A ∈ CanonicalIsogeny.integers K := hA
  have hBO : B ∈ CanonicalIsogeny.integers K := hB
  have : (Velu.short A B).Δ ∈ CanonicalIsogeny.integers K := by
    rw [Velu.short_Δ]
    exact mul_mem (neg_mem (ofNat_mem_O 16)) (add_mem (mul_mem (ofNat_mem_O 4) (pow_mem hAO 3))
      (mul_mem (ofNat_mem_O 27) (pow_mem hBO 2)))
  exact this

lemma integral_pt_short {A B : K} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    KatzForms.Integral (KatzForms.pt (Velu.short A B : WeierstrassCurve K)) := by
  have e : KatzForms.pt (Velu.short A B : WeierstrassCurve K) = ![-48 * A, 864 * B] :=
    SubgroupSum.ptR_short A B
  rw [e]
  have hAO : A ∈ CanonicalIsogeny.integers K := hA
  have hBO : B ∈ CanonicalIsogeny.integers K := hB
  intro i
  fin_cases i
  · exact (mul_mem (neg_mem (ofNat_mem_O 48)) hAO : -48 * A ∈ CanonicalIsogeny.integers K)
  · exact (mul_mem (ofNat_mem_O 864) hBO : 864 * B ∈ CanonicalIsogeny.integers K)

/-- **`UBSharp.QuotEBound` on the ordinary locus, all but the `c₄/c₆` conjunct** (unconditional). -/
theorem quotEBound_ord_partial (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖) :
    ∀ W : WeierstrassCurve K, KatzForms.IsTest W → UpContraction.Brk ℓ (KatzForms.Eh φ hℓ) W →
    ‖MvPolynomial.eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ = 1 →
    ∃ H ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ,
      (‖(SubgroupSum.veluC H).Δ‖ * ‖MvPolynomial.eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ ^ 12 ≤
          ‖(ℓ : K)‖ ^ 12 ∧
        ∀ C ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ, C ≠ H →
          ‖(SubgroupSum.veluC C).Δ‖ ^ ℓ ≤
            ‖MvPolynomial.eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ ^ 12) ∧
      ‖MvPolynomial.eval (KatzForms.pt (SubgroupSum.veluC H)) (KatzForms.Eh φ hℓ)‖ *
          ‖MvPolynomial.eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ ^ ℓ ≤
        max (‖(ℓ : K)‖ ^ (ℓ - 1) *
            ‖MvPolynomial.eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ ^ (ℓ + 1))
          (‖(ℓ : K)‖ ^ ℓ) ∧
      (∀ C ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ, C ≠ H →
        ‖MvPolynomial.eval (KatzForms.pt (SubgroupSum.veluC C)) (KatzForms.Eh φ hℓ)‖ ≤
          ‖MvPolynomial.eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖) := by
  intro W hW hB hord
  obtain ⟨-, -, -, -, H, hH, hΔH, ⟨μ, hμ, hμn, A'', B'', hK⟩, hab⟩ :=
    ord_data hℓ φ hφ hε W hW hB hord
  refine ⟨H, hH, ⟨?_, fun C hC hne => ?_⟩, ?_, fun C hC hne => ?_⟩
  · rw [hord, one_pow, mul_one]; exact hΔH
  · rw [hord, one_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_short_Δ_le (hab C hC hne).1 (hab C hC hne).2)
  · rw [hord, one_pow, mul_one, one_pow, mul_one]
    refine le_max_of_le_left ?_
    have e := eval_Eh_scale hℓ φ (Units.mk0 μ hμ) (SubgroupSum.veluC H : WeierstrassCurve K)
    rw [← hK] at e
    have hle := norm_E_le_of_integral hℓ φ hφ (integral_pt_toK (shortO A'' B''))
    rw [e, norm_mul, norm_pow, Units.val_inv_eq_inv_val, Units.val_mk0, norm_inv, hμn,
      inv_pow] at hle
    have hpos : 0 < ‖(ℓ : K)‖ ^ (ℓ - 1) := by positivity
    rw [inv_mul_le_iff₀ hpos, mul_one] at hle
    exact hle
  · rw [hord]
    exact norm_E_le_of_integral hℓ φ hφ (integral_pt_short (hab C hC hne).1 (hab C hC hne).2)

/-- **`UBSharp.QuotEBound` on the ordinary locus**, given the constant term `ProdDelta` of the
Δ-modular equation. -/
theorem quotEBound_ord (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖)
    (hprod : ProdDelta ℓ K) :
    ∀ W : WeierstrassCurve K, KatzForms.IsTest W → UpContraction.Brk ℓ (KatzForms.Eh φ hℓ) W →
    ‖MvPolynomial.eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ = 1 →
    ∃ H ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ,
      (‖(SubgroupSum.veluC H).Δ‖ * ‖MvPolynomial.eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ ^ 12 ≤
          ‖(ℓ : K)‖ ^ 12 ∧
        ∀ C ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ, C ≠ H →
          ‖(SubgroupSum.veluC C).Δ‖ ^ ℓ ≤
            ‖MvPolynomial.eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ ^ 12) ∧
      ‖MvPolynomial.eval (KatzForms.pt (SubgroupSum.veluC H)) (KatzForms.Eh φ hℓ)‖ *
          ‖MvPolynomial.eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ ^ ℓ ≤
        max (‖(ℓ : K)‖ ^ (ℓ - 1) *
            ‖MvPolynomial.eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖ ^ (ℓ + 1))
          (‖(ℓ : K)‖ ^ ℓ) ∧
      (∀ C ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ, C ≠ H →
        ‖MvPolynomial.eval (KatzForms.pt (SubgroupSum.veluC C)) (KatzForms.Eh φ hℓ)‖ ≤
          ‖MvPolynomial.eval (KatzForms.pt W) (KatzForms.Eh φ hℓ)‖) ∧
      ∀ C ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ,
        ‖(SubgroupSum.veluC C : WeierstrassCurve K).c₄‖ ^ 3 ≤
            ‖(SubgroupSum.veluC C : WeierstrassCurve K).Δ‖ ∧
          ‖(SubgroupSum.veluC C : WeierstrassCurve K).c₆‖ ^ 2 ≤
            ‖(SubgroupSum.veluC C : WeierstrassCurve K).Δ‖ := by
  classical
  intro W hW hB hord
  obtain ⟨-, h2, h3, hΔs, H, hH, hΔH, ⟨μ, hμ, hμn, A'', B'', hK⟩, hab⟩ :=
    ord_data hℓ φ hφ hε W hW hB hord
  have hΔ' : 4 * ConjAlg.sa W ^ 3 + 27 * ConjAlg.sb W ^ 2 ≠ 0 := by
    intro h0
    rw [Velu.short_Δ, h0, mul_zero, norm_zero] at hΔs
    exact zero_ne_one hΔs
  obtain ⟨T, hT, hTc⟩ := TorsionSpec.fullTorsion (F := K) hℓp.out.two_le _ _ hΔ'
  obtain ⟨Z, hZ, -⟩ := HeckeBridge.exists_subs_finset (p := ℓ) hT hTc
  have hW0 : W.Δ ≠ 0 := by
    intro h; have := hW.2.2.2.2.2; rw [h, norm_zero] at this; exact zero_ne_one this
  have hpr := hprod W hW0 Z hZ
  have hprn : ∏ G ∈ Z, ‖(SubgroupSum.veluC G).Δ‖ = ‖(ℓ : K)‖ ^ 12 := by
    rw [← norm_prod, hpr, norm_mul, norm_pow, norm_pow, hW.2.2.2.2.2, one_pow, mul_one]
  have hle1 : ∀ G ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ, G ≠ H →
      ‖(SubgroupSum.veluC G).Δ‖ ≤ 1 := fun G hG hne =>
    norm_short_Δ_le (hab G hG hne).1 (hab G hG hne).2
  have hHZ : H ∈ Z := (hZ H).1 hH
  have hsplit := Finset.mul_prod_erase Z (fun G => ‖(SubgroupSum.veluC G).Δ‖) hHZ
  have hrest : ∀ Y ⊆ Z.erase H, ∏ G ∈ Y, ‖(SubgroupSum.veluC G).Δ‖ ≤ 1 := fun Y hY =>
    Finset.prod_le_one (fun _ _ => norm_nonneg _) fun G hG => by
      have hG' := hY hG
      exact hle1 G ((hZ G).2 (Finset.mem_of_mem_erase hG')) (Finset.ne_of_mem_erase hG')
  have hℓ12 : 0 < ‖(ℓ : K)‖ ^ 12 := by positivity
  have hHeq : ‖(SubgroupSum.veluC H).Δ‖ = ‖(ℓ : K)‖ ^ 12 := by
    refine le_antisymm hΔH ?_
    have := hrest _ subset_rfl
    rw [← hprn, ← hsplit]
    exact mul_le_of_le_one_right (norm_nonneg _) this
  have hCeq : ∀ C ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ, C ≠ H →
      ‖(SubgroupSum.veluC C).Δ‖ = 1 := by
    intro C hC hne
    refine le_antisymm (hle1 C hC hne) ?_
    have hCZ : C ∈ Z.erase H := Finset.mem_erase.2 ⟨hne, (hZ C).1 hC⟩
    have hs2 := Finset.mul_prod_erase (Z.erase H) (fun G => ‖(SubgroupSum.veluC G).Δ‖) hCZ
    have hR := hrest ((Z.erase H).erase C) (Finset.erase_subset C (Z.erase H))
    have e : ‖(ℓ : K)‖ ^ 12 = ‖(ℓ : K)‖ ^ 12 * (‖(SubgroupSum.veluC C).Δ‖ *
        ∏ G ∈ (Z.erase H).erase C, ‖(SubgroupSum.veluC G).Δ‖) := by
      rw [hs2, ← hHeq, hsplit, hHeq, hprn]
    have hle : ‖(ℓ : K)‖ ^ 12 ≤ ‖(ℓ : K)‖ ^ 12 * ‖(SubgroupSum.veluC C).Δ‖ := by
      conv_lhs => rw [e]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (norm_nonneg _) hR) hℓ12.le
    by_contra h
    have h' := not_le.mp h
    have := mul_lt_mul_of_pos_left h' hℓ12
    rw [mul_one] at this
    linarith
  -- `c₄`, `c₆` of the scaled model of `W/H`
  have hc4H : ‖(SubgroupSum.veluC H : WeierstrassCurve K).c₄‖ ≤ ‖(ℓ : K)‖ ^ 4 := by
    have e := congrArg WeierstrassCurve.c₄ hK
    rw [WeierstrassCurve.variableChange_c₄] at e
    have hle : ‖(toK (shortO A'' B'')).c₄‖ ≤ 1 := by
      rw [toK, WeierstrassCurve.map_c₄]; exact ((shortO A'' B'').c₄).2
    rw [e, norm_mul, norm_pow, Units.val_inv_eq_inv_val, Units.val_mk0, norm_inv, hμn,
      inv_pow, inv_mul_le_iff₀ (by positivity), mul_one] at hle
    exact hle
  have hc6H : ‖(SubgroupSum.veluC H : WeierstrassCurve K).c₆‖ ≤ ‖(ℓ : K)‖ ^ 6 := by
    have e := congrArg WeierstrassCurve.c₆ hK
    rw [WeierstrassCurve.variableChange_c₆] at e
    have hle : ‖(toK (shortO A'' B'')).c₆‖ ≤ 1 := by
      rw [toK, WeierstrassCurve.map_c₆]; exact ((shortO A'' B'').c₆).2
    rw [e, norm_mul, norm_pow, Units.val_inv_eq_inv_val, Units.val_mk0, norm_inv, hμn,
      inv_pow, inv_mul_le_iff₀ (by positivity), mul_one] at hle
    exact hle
  have hcC : ∀ C ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ, C ≠ H →
      ‖(SubgroupSum.veluC C : WeierstrassCurve K).c₄‖ ≤ 1 ∧
        ‖(SubgroupSum.veluC C : WeierstrassCurve K).c₆‖ ≤ 1 := by
    intro C hC hne
    have hi := integral_pt_short (hab C hC hne).1 (hab C hC hne).2
    refine ⟨hi 0, ?_⟩
    have := hi 1
    simpa [KatzForms.pt] using this
  refine ⟨H, hH, ⟨?_, fun C hC hne => ?_⟩, ?_, fun C hC hne => ?_, fun C hC => ?_⟩
  · rw [hord, one_pow, mul_one]; exact hΔH
  · rw [hord, one_pow]; exact pow_le_one₀ (norm_nonneg _) (hle1 C hC hne)
  · -- the `E`-bound for `H`, as in `quotEBound_ord_partial`
    rw [hord, one_pow, mul_one, one_pow, mul_one]
    refine le_max_of_le_left ?_
    have e := eval_Eh_scale hℓ φ (Units.mk0 μ hμ) (SubgroupSum.veluC H : WeierstrassCurve K)
    rw [← hK] at e
    have hle := norm_E_le_of_integral hℓ φ hφ (integral_pt_toK (shortO A'' B''))
    rw [e, norm_mul, norm_pow, Units.val_inv_eq_inv_val, Units.val_mk0, norm_inv, hμn,
      inv_pow] at hle
    have hpos : 0 < ‖(ℓ : K)‖ ^ (ℓ - 1) := by positivity
    rw [inv_mul_le_iff₀ hpos, mul_one] at hle
    exact hle
  · rw [hord]
    exact norm_E_le_of_integral hℓ φ hφ (integral_pt_short (hab C hC hne).1 (hab C hC hne).2)
  · by_cases hCH : C = H
    · subst hCH
      have hΔC : ‖(SubgroupSum.veluC C : WeierstrassCurve K).Δ‖ = ‖(ℓ : K)‖ ^ 12 := hHeq
      rw [hΔC]
      constructor
      · calc _ ≤ (‖(ℓ : K)‖ ^ 4) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hc4H 3
          _ = _ := by rw [← pow_mul]
      · calc _ ≤ (‖(ℓ : K)‖ ^ 6) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hc6H 2
          _ = _ := by rw [← pow_mul]
    · have hΔC : ‖(SubgroupSum.veluC C : WeierstrassCurve K).Δ‖ = 1 := hCeq C hC hCH
      rw [hΔC]
      exact ⟨pow_le_one₀ (norm_nonneg _) (hcC C hC hCH).1,
        pow_le_one₀ (norm_nonneg _) (hcC C hC hCH).2⟩

/-! ### `QuotE.OrdEBound` -/

/-- **`QuotE.OrdEBound` from `ProdDelta`.** -/
theorem ordEBound_of_prod (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖)
    (hprod : ProdDelta ℓ K) : QuotE.OrdEBound hℓ φ :=
  fun W hW hB hord => quotEBound_ord hℓ φ hφ hε hprod W hW hB hord

/-- **`QuotE.OrdEBound hℓ (SharpHQ.φC ℓ)` from `ProdDelta ℓ ℂ_ℓ`.** -/
theorem ordEBound_C [DecidableEq ℂ_[ℓ]] (hprod : ProdDelta ℓ ℂ_[ℓ]) :
    QuotE.OrdEBound hℓ (SharpHQ.φC ℓ) :=
  ordEBound_of_prod hℓ (SharpHQ.φC ℓ)
    (fun x => (SharpHQ.norm_φC x).trans_le (PadicInt.norm_le_one x))
    (by rw [SharpHQ.norm_ell_C]; positivity) hprod

end OrdQuot
