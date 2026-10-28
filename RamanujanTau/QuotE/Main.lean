/-
# `UBSharp.QuotEBound`, supersingular part

* `scale_facts`: if `toK W' = ⟨μ,0,0,0⟩ • V` with `W'` integral of good reduction, then
  `‖Δ(V)‖ = ‖μ‖^12`, `‖c₄(V)‖³ ≤ ‖Δ(V)‖`, `‖c₆(V)‖² ≤ ‖Δ(V)‖` and
  `‖E(V)‖ = ‖μ‖^{p−1}·‖E(W')‖` (`E` isobaric of weight `p − 1`; `c₄ ↦ μ⁻⁴c₄`, `c₆ ↦ μ⁻⁶c₆`,
  `Δ ↦ μ⁻¹²Δ`).
* **`quotEBound_ss`**: the conclusion of `UBSharp.QuotEBound` at every test curve of the break region
  with `‖E(W)‖ < 1` (any complete algebraically closed ultrametric `K` of characteristic `0`).
  With `α = ‖E(W)‖`, `ε = ‖ℓ‖`, `m = ‖μ_C‖`, `e = ‖E(model_C)‖`:
  * canonical `H`: `mα = ε`, `eα ≤ max(α^{ℓ+1}, ε)` give
    `‖E(W/H)‖α^ℓ = (mα)^{ℓ−1}·eα ≤ max(ε^{ℓ−1}α^{ℓ+1}, ε^ℓ)`;
  * non-canonical `C`: `m^ℓ = e^ℓ = α` give `‖E(W/C)‖^ℓ = α^{ℓ−1}α`, so `‖E(W/C)‖ = α`.
* `quotEBound_C_ss`: the same over `ℂ_ℓ` with `φ = SharpHQ.φC ℓ`.
-/
import RamanujanTau.QuotE.Core
import RamanujanTau.UBSharp.Velu

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QuotE
open MvPowerSeries EllipticFormal EllipticI2 CanonicalIsogeny QuotientHasse VeluLubin AllQuotients
  KatzForms

section Scale
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- `E(⟨μ,0,0,0⟩ • V) = μ^{−(p−1)} E(V)`. -/
lemma eval_scale_Eh {p : ℕ} [Fact p.Prime] (φ : ℤ_[p] →+* K) (hp5 : 5 ≤ p) (μ : Kˣ)
    (V : WeierstrassCurve K) :
    MvPolynomial.eval (pt ((⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) • V)) (Eh φ hp5) =
      ((μ⁻¹ : Kˣ) : K) ^ (p - 1) * MvPolynomial.eval (pt V) (Eh φ hp5) := by
  have hI : ModP.Iso (Eh φ hp5) (p - 1) := ModP.iso_map φ (ModP.iso_hasseA hp5)
  have h := HeckeQExp.aeval_ptR_scale (K := K) (L := K) hI μ V
  simpa only [MvPolynomial.coe_aeval_eq_eval] using h

/-- **Scaling facts** for `toK W' = ⟨μ,0,0,0⟩ • V`, `W'` integral with `‖Δ‖ = 1`. -/
lemma scale_facts {p : ℕ} [Fact p.Prime] (φ : ℤ_[p] →+* K) (hp5 : 5 ≤ p) (μ : Kˣ)
    (V : WeierstrassCurve K) (W' : WeierstrassCurve ↥(CanonicalIsogeny.integers K))
    (hK : UpContraction.toK W' = (⟨μ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) • V)
    (hΔ : ‖((W'.Δ : ↥(CanonicalIsogeny.integers K)) : K)‖ = 1) :
    ‖V.Δ‖ = ‖(μ : K)‖ ^ 12 ∧ ‖V.c₄‖ ^ 3 ≤ ‖V.Δ‖ ∧ ‖V.c₆‖ ^ 2 ≤ ‖V.Δ‖ ∧
      ‖MvPolynomial.eval (pt V) (Eh φ hp5)‖ =
        ‖(μ : K)‖ ^ (p - 1) * ‖MvPolynomial.eval (pt (UpContraction.toK W')) (Eh φ hp5)‖ := by
  have hμ0 : (μ : K) ≠ 0 := μ.ne_zero
  have hm : 0 < ‖(μ : K)‖ := norm_pos_iff.2 hμ0
  have hinv : ‖((μ⁻¹ : Kˣ) : K)‖ = ‖(μ : K)‖⁻¹ := by rw [Units.val_inv_eq_inv_val, norm_inv]
  have eΔ : (UpContraction.toK W').Δ = ((μ⁻¹ : Kˣ) : K) ^ 12 * V.Δ := by
    rw [hK, WeierstrassCurve.variableChange_Δ]
  have e4 : (UpContraction.toK W').c₄ = ((μ⁻¹ : Kˣ) : K) ^ 4 * V.c₄ := by
    rw [hK, WeierstrassCurve.variableChange_c₄]
  have e6 : (UpContraction.toK W').c₆ = ((μ⁻¹ : Kˣ) : K) ^ 6 * V.c₆ := by
    rw [hK, WeierstrassCurve.variableChange_c₆]
  have nΔ : ‖(UpContraction.toK W').Δ‖ = 1 := by
    rw [WeierstrassCurve.map_Δ]; exact hΔ
  have n4 : ‖(UpContraction.toK W').c₄‖ ≤ 1 := by
    rw [WeierstrassCurve.map_c₄]; exact (W'.c₄).2
  have n6 : ‖(UpContraction.toK W').c₆‖ ≤ 1 := by
    rw [WeierstrassCurve.map_c₆]; exact (W'.c₆).2
  rw [eΔ, norm_mul, norm_pow, hinv] at nΔ
  rw [e4, norm_mul, norm_pow, hinv] at n4
  rw [e6, norm_mul, norm_pow, hinv] at n6
  have hVΔ : ‖V.Δ‖ = ‖(μ : K)‖ ^ 12 := by
    field_simp at nΔ; linarith
  refine ⟨hVΔ, ?_, ?_, ?_⟩
  · rw [hVΔ]
    have h4 : ‖V.c₄‖ ≤ ‖(μ : K)‖ ^ 4 := by
      rw [inv_pow, inv_mul_le_iff₀ (by positivity), mul_one] at n4; exact n4
    calc ‖V.c₄‖ ^ 3 ≤ (‖(μ : K)‖ ^ 4) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) h4 _
      _ = _ := by ring
  · rw [hVΔ]
    have h6 : ‖V.c₆‖ ≤ ‖(μ : K)‖ ^ 6 := by
      rw [inv_pow, inv_mul_le_iff₀ (by positivity), mul_one] at n6; exact n6
    calc ‖V.c₆‖ ^ 2 ≤ (‖(μ : K)‖ ^ 6) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h6 _
      _ = _ := by ring
  · rw [hK, eval_scale_Eh φ hp5 μ V, norm_mul, norm_pow, hinv, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hm.ne', one_pow, one_mul]

end Scale

section SS
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
  [CharZero K] [DecidableEq K]
variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-- **`QuotEBound`, supersingular part**: the conclusion of `UBSharp.QuotEBound` at a test curve of
the break region with `‖E(W)‖ < 1`. -/
theorem quotEBound_ss (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖)
    (W : WeierstrassCurve K) (hW : IsTest W) (hB : UpContraction.Brk ℓ (Eh φ hℓ) W)
    (hss : ‖MvPolynomial.eval (pt W) (Eh φ hℓ)‖ < 1) :
    ∃ H ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ,
      (‖(SubgroupSum.veluC H).Δ‖ * ‖MvPolynomial.eval (pt W) (Eh φ hℓ)‖ ^ 12 ≤ ‖(ℓ : K)‖ ^ 12 ∧
        ∀ C ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ, C ≠ H →
          ‖(SubgroupSum.veluC C).Δ‖ ^ ℓ ≤ ‖MvPolynomial.eval (pt W) (Eh φ hℓ)‖ ^ 12) ∧
      ‖MvPolynomial.eval (pt (SubgroupSum.veluC H)) (Eh φ hℓ)‖ *
          ‖MvPolynomial.eval (pt W) (Eh φ hℓ)‖ ^ ℓ ≤
        max (‖(ℓ : K)‖ ^ (ℓ - 1) * ‖MvPolynomial.eval (pt W) (Eh φ hℓ)‖ ^ (ℓ + 1))
          (‖(ℓ : K)‖ ^ ℓ) ∧
      (∀ C ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ, C ≠ H →
        ‖MvPolynomial.eval (pt (SubgroupSum.veluC C)) (Eh φ hℓ)‖ ≤
          ‖MvPolynomial.eval (pt W) (Eh φ hℓ)‖) ∧
      ∀ C ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ,
        ‖(SubgroupSum.veluC C : WeierstrassCurve K).c₄‖ ^ 3 ≤
          ‖(SubgroupSum.veluC C : WeierstrassCurve K).Δ‖ ∧
        ‖(SubgroupSum.veluC C : WeierstrassCurve K).c₆‖ ^ 2 ≤
          ‖(SubgroupSum.veluC C : WeierstrassCurve K).Δ‖ := by
  classical
  have hφ' : ∀ x, φ x ∈ CanonicalIsogeny.integers K := hφ
  letI : Algebra ℤ_[ℓ] ↥(CanonicalIsogeny.integers K) :=
    (φ.codRestrict (CanonicalIsogeny.integers K) hφ').toAlgebra
  have hφ'' : ∀ x, (((algebraMap ℤ_[ℓ] ↥(CanonicalIsogeny.integers K) x) :
      ↥(CanonicalIsogeny.integers K)) : K) = φ x := fun x => rfl
  set E := MvPolynomial.eval (pt W) (Eh φ hℓ)
  have hl1 : ‖(ℓ : K)‖ < 1 :=
    EllipticI2.norm_p_lt_one hℓp.out.two_le (norm_nonneg _) hss.le hB
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
  set a : ↥(CanonicalIsogeny.integers K) := ⟨ConjAlg.sa W, hsa⟩
  set b : ↥(CanonicalIsogeny.integers K) := ⟨ConjAlg.sb W, hsb⟩
  have hWK : toK (shortO a b) = (Velu.short (ConjAlg.sa W) (ConjAlg.sb W) : WeierstrassCurve K) :=
    toK_shortO a b
  have hΔ : ‖(((shortO a b).Δ : ↥(CanonicalIsogeny.integers K)) : K)‖ = 1 := by
    have e := congrArg WeierstrassCurve.Δ hWK
    simp only [toK, WeierstrassCurve.map_Δ, Subring.subtype_apply] at e
    rw [e, ConjAlg.shortModel_Δ]; exact hW.2.2.2.2.2
  have hptW : KatzForms.pt (toK (shortO a b)) = KatzForms.pt W := by
    rw [hWK]; exact ConjAlg.shortModel_ptR W
  have hEE : E = ((UpContraction.EpO ℓ hℓ (shortO a b) : ↥(CanonicalIsogeny.integers K)) : K) := by
    rw [← UpContraction.eval_pt_toK φ hφ'' hℓ (shortO a b)]
    show MvPolynomial.eval (KatzForms.pt W) (Eh φ hℓ) =
      MvPolynomial.eval (KatzForms.pt (toK (shortO a b))) (Eh φ hℓ)
    rw [hptW]
  have hEp : ‖(ℓ : K)‖ < ‖E‖ :=
    UpContraction.lt_of_break ℓ (norm_nonneg _) (norm_nonneg _) hss.le hB
  have haE : ‖((hasse (formalGroup (shortO a b)) ℓ : ↥(CanonicalIsogeny.integers K)) : K)‖ =
      ‖E‖ := by
    rw [hEE]
    exact UpContraction.norm_hasse_eq_EpO ℓ hℓ (shortO a b)
      (lt_of_lt_of_le (hEE ▸ hEp) (le_max_right _ _))
  have ha : ‖hasse (formalGroup (shortO a b)) ℓ‖ < 1 := by
    show ‖((hasse (formalGroup (shortO a b)) ℓ : ↥(CanonicalIsogeny.integers K)) : K)‖ < 1
    rw [haE]; exact hss
  have hbr : ‖(ℓ : K)‖ ^ ℓ < ‖hasse (formalGroup (shortO a b)) ℓ‖ ^ (ℓ + 1) := by
    show ‖(ℓ : K)‖ ^ ℓ <
      ‖((hasse (formalGroup (shortO a b)) ℓ : ↥(CanonicalIsogeny.integers K)) : K)‖ ^ (ℓ + 1)
    rw [haE]; exact hB
  have hEO : ‖((UpContraction.EpO ℓ hℓ (shortO a b) : ↥(CanonicalIsogeny.integers K)) : K)‖ =
      ‖((hasse (formalGroup (shortO a b)) ℓ : ↥(CanonicalIsogeny.integers K)) : K)‖ := by
    rw [haE, hEE]
  obtain ⟨H, hH, hmod⟩ := velu_models ℓ a b hℓ hε hΔ ha hbr hEO
  simp only [haE] at hmod
  -- per-quotient facts in terms of `α = ‖E‖`
  set α := ‖E‖ with hαd
  set ε := ‖(ℓ : K)‖ with hεd
  have hα0 : 0 < α := lt_of_le_of_lt (norm_nonneg _) hEp
  have hℓ1 : 1 ≤ ℓ := by omega
  have facts : ∀ G ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ, ∃ m e : ℝ, 0 ≤ m ∧ 0 ≤ e ∧
      ‖(SubgroupSum.veluC G).Δ‖ = m ^ 12 ∧
      ‖MvPolynomial.eval (pt (SubgroupSum.veluC G)) (Eh φ hℓ)‖ = m ^ (ℓ - 1) * e ∧
      (‖(SubgroupSum.veluC G : WeierstrassCurve K).c₄‖ ^ 3 ≤
          ‖(SubgroupSum.veluC G : WeierstrassCurve K).Δ‖ ∧
        ‖(SubgroupSum.veluC G : WeierstrassCurve K).c₆‖ ^ 2 ≤
          ‖(SubgroupSum.veluC G : WeierstrassCurve K).Δ‖) ∧
      (G = H → m * α = ε ∧ e * α ≤ max (α ^ (ℓ + 1)) ε) ∧
      (G ≠ H → m ^ ℓ = α ∧ e ^ ℓ = α) := by
    intro G hG
    obtain ⟨μ, W', hK, hΔW, hcan, hnon⟩ := hmod G hG
    obtain ⟨s1, s2, s3, s4⟩ := scale_facts φ hℓ μ _ W' hK hΔW
    rw [UpContraction.eval_pt_toK φ hφ'' hℓ W'] at s4
    exact ⟨_, _, norm_nonneg _, norm_nonneg _, s1, s4, ⟨s2, s3⟩, hcan, hnon⟩
  refine ⟨H, hH, ⟨?_, ?_⟩, ?_, ?_, fun C hC => (facts C hC).choose_spec.choose_spec.2.2.2.2.1⟩
  · obtain ⟨m, e, -, -, hD, -, -, hc, -⟩ := facts H hH
    obtain ⟨h1, -⟩ := hc rfl
    rw [hD, ← mul_pow, h1]
  · intro C hC hne
    obtain ⟨m, e, -, -, hD, -, -, -, hn⟩ := facts C hC
    obtain ⟨h1, -⟩ := hn hne
    rw [hD, ← pow_mul, mul_comm 12 ℓ, pow_mul, h1]
  · obtain ⟨m, e, hm0, he0, -, hE, -, hc, -⟩ := facts H hH
    obtain ⟨h1, h2⟩ := hc rfl
    rw [hE]
    have eq : m ^ (ℓ - 1) * e * α ^ ℓ = ε ^ (ℓ - 1) * (e * α) := by
      rw [← h1, mul_pow]
      have : α ^ ℓ = α ^ (ℓ - 1) * α := by
        rw [← pow_succ, Nat.sub_add_cancel hℓ1]
      rw [this]; ring
    rw [eq]
    calc ε ^ (ℓ - 1) * (e * α) ≤ ε ^ (ℓ - 1) * max (α ^ (ℓ + 1)) ε :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = max (ε ^ (ℓ - 1) * α ^ (ℓ + 1)) (ε ^ (ℓ - 1) * ε) := mul_max_of_nonneg _ _ (by positivity)
      _ = _ := by rw [← pow_succ, Nat.sub_add_cancel hℓ1]
  · intro C hC hne
    obtain ⟨m, e, hm0, he0, -, hE, -, -, hn⟩ := facts C hC
    obtain ⟨h1, h2⟩ := hn hne
    rw [hE]
    refine le_of_eq ((pow_left_inj₀ (by positivity) hα0.le (by omega : ℓ ≠ 0)).mp ?_)
    rw [mul_pow, ← pow_mul, mul_comm (ℓ - 1) ℓ, pow_mul, h1, h2, ← pow_succ,
      Nat.sub_add_cancel hℓ1]

end SS

section C
variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-- **`QuotEBound` over `ℂ_ℓ` on the supersingular locus**, unconditionally. -/
theorem quotEBound_C_ss [DecidableEq ℂ_[ℓ]] (W : WeierstrassCurve ℂ_[ℓ]) (hW : IsTest W)
    (hB : UpContraction.Brk ℓ (Eh (SharpHQ.φC ℓ) hℓ) W)
    (hss : ‖MvPolynomial.eval (pt W) (Eh (SharpHQ.φC ℓ) hℓ)‖ < 1) :
    ∃ H ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ,
      (‖(SubgroupSum.veluC H).Δ‖ * ‖MvPolynomial.eval (pt W) (Eh (SharpHQ.φC ℓ) hℓ)‖ ^ 12 ≤
          ‖(ℓ : ℂ_[ℓ])‖ ^ 12 ∧
        ∀ C ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ, C ≠ H →
          ‖(SubgroupSum.veluC C).Δ‖ ^ ℓ ≤ ‖MvPolynomial.eval (pt W) (Eh (SharpHQ.φC ℓ) hℓ)‖ ^ 12) ∧
      ‖MvPolynomial.eval (pt (SubgroupSum.veluC H)) (Eh (SharpHQ.φC ℓ) hℓ)‖ *
          ‖MvPolynomial.eval (pt W) (Eh (SharpHQ.φC ℓ) hℓ)‖ ^ ℓ ≤
        max (‖(ℓ : ℂ_[ℓ])‖ ^ (ℓ - 1) *
            ‖MvPolynomial.eval (pt W) (Eh (SharpHQ.φC ℓ) hℓ)‖ ^ (ℓ + 1))
          (‖(ℓ : ℂ_[ℓ])‖ ^ ℓ) ∧
      (∀ C ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ, C ≠ H →
        ‖MvPolynomial.eval (pt (SubgroupSum.veluC C)) (Eh (SharpHQ.φC ℓ) hℓ)‖ ≤
          ‖MvPolynomial.eval (pt W) (Eh (SharpHQ.φC ℓ) hℓ)‖) ∧
      ∀ C ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ,
        ‖(SubgroupSum.veluC C : WeierstrassCurve ℂ_[ℓ]).c₄‖ ^ 3 ≤
          ‖(SubgroupSum.veluC C : WeierstrassCurve ℂ_[ℓ]).Δ‖ ∧
        ‖(SubgroupSum.veluC C : WeierstrassCurve ℂ_[ℓ]).c₆‖ ^ 2 ≤
          ‖(SubgroupSum.veluC C : WeierstrassCurve ℂ_[ℓ]).Δ‖ :=
  quotEBound_ss hℓ (SharpHQ.φC ℓ)
    (fun x => (SharpHQ.norm_φC x).trans_le (PadicInt.norm_le_one x))
    (by rw [SharpHQ.norm_ell_C]; positivity) W hW hB hss

end C

end QuotE
