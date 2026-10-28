/-
# Valuations of the Vélu quotients by all order-`p` subgroups; `QuotValBound` (supersingular part)

* **`velu_valuations`** (short `W` over `𝒪`, good supersingular reduction, break region): with
  `H` the canonical subgroup (`Pt(canSub)`),
  * `‖Δ(veluC H)‖ · ‖a_W‖^12 = ‖p‖^12`             (`v(Lie φ_H) = 1 − v`),
  * `‖Δ(veluC G)‖^p = ‖a_W‖^12` for every other `G ∈ subs a b p` (`v(Lie φ_G) = v/p`).
* **`quotValBound_ss`**: the `ConjAlg.QuotValBound` conclusion for every test curve `W` in the break
  region with `‖E(W)‖ < 1`.
* **`quotValBound_of_ord`**: `QuotValBound` from the ordinary-locus statement `OrdBound`.
-/
import RamanujanTau.AllQuotients.Can
import RamanujanTau.ConjAlg.HConj
import RamanujanTau.UpContraction.Transport

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AllQuotients
open MvPowerSeries EllipticFormal EllipticI2 CanonicalIsogeny QuotientHasse VeluLubin

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
  [CharZero K] [DecidableEq K]

local notation "𝒪" => CanonicalIsogeny.integers K

lemma disc_ne_zero (a b : ↥(CanonicalIsogeny.integers K))
    (hΔ : ‖(((shortO a b).Δ : 𝒪) : K)‖ = 1) : 4 * (a : K) ^ 3 + 27 * (b : K) ^ 2 ≠ 0 := by
  intro h0
  have e : (((shortO a b).Δ : 𝒪) : K) = -16 * (4 * (a : K) ^ 3 + 27 * (b : K) ^ 2) := by
    have := congrArg (fun W : WeierstrassCurve K => W.Δ) (toK_shortO (K := K) a b)
    simp only [toK, WeierstrassCurve.map_Δ] at this
    rw [Subring.subtype_apply] at this
    rw [this, Velu.short_Δ]
  rw [e, h0, mul_zero, norm_zero] at hΔ
  exact zero_ne_one hΔ

/-- **The Lie/Δ valuations of all `p + 1` Vélu quotients** (supersingular, break region). -/
theorem velu_valuations (a b : ↥(CanonicalIsogeny.integers K)) (p : ℕ) [hpf : Fact p.Prime]
    (hp5 : 5 ≤ p) (hε : 0 < ‖(p : K)‖) (hΔ : ‖(((shortO a b).Δ : 𝒪) : K)‖ = 1)
    (ha : ‖hasse (formalGroup (shortO a b)) p‖ < 1)
    (hbreak : ‖(p : K)‖ ^ p < ‖hasse (formalGroup (shortO a b)) p‖ ^ (p + 1)) :
    ∃ H ∈ SubgroupSum.subs (a : K) (b : K) p,
      ‖(SubgroupSum.veluC H).Δ‖ * ‖((hasse (formalGroup (shortO a b)) p : 𝒪) : K)‖ ^ 12 =
          ‖(p : K)‖ ^ 12 ∧
      ∀ G ∈ SubgroupSum.subs (a : K) (b : K) p, G ≠ H →
        ‖(SubgroupSum.veluC G).Δ‖ ^ p = ‖((hasse (formalGroup (shortO a b)) p : 𝒪) : K)‖ ^ 12 := by
  classical
  have hp := hpf.out
  have hp1 : ‖(p : K)‖ < 1 :=
    EllipticI2.norm_p_lt_one hp.two_le (norm_nonneg _) ha.le hbreak
  have hu := HeightEll.topc_norm_eq_one (shortO a b) p hp5 hp1 hΔ ha
  have hΔ' := disc_ne_zero a b hΔ
  obtain ⟨T, hT, hTc⟩ := exists_torsion (formalGroup (shortO a b)) p hu ha hε hp1
  have hT' : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0 := hT
  have key : ∀ C : Lubin.FinSub (formalGroup (shortO a b)), C.H ⊆ T → C.H.card = p →
      ‖(SubgroupSum.veluC (C.H.image (Pt a b))).Δ‖ = (∏ c ∈ C.H.erase 0, ‖(c : K)‖) ^ 12 := by
    intro C hCT hcard
    have hCp : ∀ h ∈ C.H, nm a b h p = 0 := fun h hh => ((hT' h).1 (hCT hh)).2
    obtain ⟨κ, hκ⟩ := exists_kernel_of_finSub a b hp hp5 C hCp
    have hκG : κ.G = C.H.image (Pt a b) := by
      apply Finset.coe_injective; rw [hκ, Finset.coe_image]
    have := (norm_Δ_velu a b p hp5 hp1 hΔ ha C hcard κ hκ).2
    rw [hκG, norm_lie_pis] at this
    exact this
  set C₀ := canSub a b hT' hu ha hε hp1 hbreak
  have hC₀T : C₀.H ⊆ T := canSub_sub a b hT' hu ha hε hp1 hbreak
  have hC₀c : C₀.H.card = p := card_canSub a b hp5 hT' hTc hu ha hε hp1 hbreak
  refine ⟨C₀.H.image (Pt a b), image_mem_subs a b hp hp5 hT' C₀ hC₀T hC₀c, ?_, ?_⟩
  · rw [key C₀ hC₀T hC₀c, ← mul_pow]
    exact congrArg (· ^ 12)
      (prod_canonical (formalGroup (shortO a b)) p C₀ hC₀c (canSub_can a b hT' hu ha hε hp1 hbreak))
  · intro G hG hne
    set C := ofSub a b hp hp5 hT' hG.1
    have hcard : C.H.card = p := card_ofSub a b hp hp5 hT' hTc hΔ' hG
    have himg : C.H.image (Pt a b) = G := image_ofSub a b hp hp5 hT' hTc hΔ' hG
    have hCT : C.H ⊆ T := ofSub_sub a b hp hp5 hT' hG.1
    have hCH : ∀ c ∈ C.H, c ≠ 0 →
        ‖hasse (formalGroup (shortO a b)) p‖ * ‖(c : K)‖ ^ (p - 1) ≠ ‖(p : K)‖ := by
      intro c hc hc0 hcan
      apply hne
      refine himg.symm.trans ?_
      rw [eq_canSub a b hp5 hT' hTc hu ha hε hp1 hbreak C hCT hcard hc hc0 hcan]
    have hpow := prod_noncanonical (formalGroup (shortO a b)) p hu ha hε hbreak C
      (fun c hc => ((hT' c).1 (hCT hc)).2) hcard hCH
    have e := key C hCT hcard
    rw [himg] at e
    rw [e, ← pow_mul, mul_comm 12 p, pow_mul]
    exact congrArg (· ^ 12) hpow

/-! ### `QuotValBound` -/

section QVB
open KatzForms

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

lemma norm_two_three (hl1 : ‖(ℓ : K)‖ < 1) (h5 : 5 ≤ ℓ) : ‖(2 : K)‖ = 1 ∧ ‖(3 : K)‖ = 1 := by
  constructor
  · have := norm_nat_eq_one (K := K) ℓ hl1 2 (fun h => by
      have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  · have := norm_nat_eq_one (K := K) ℓ hl1 3 (fun h => by
      have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this

/-- **`QuotValBound`, supersingular part**: for a test curve `W` in the break region with
`‖E(W)‖ < 1`, the canonical `H` and the bounds for all other `C`, on the short model. -/
theorem quotValBound_ss (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖)
    (W : WeierstrassCurve K) (hW : IsTest W) (hB : UpContraction.Brk ℓ (Eh φ hℓ) W)
    (hss : ‖MvPolynomial.eval (KatzForms.pt W) (Eh φ hℓ)‖ < 1) :
    ∃ H ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ,
      ‖(SubgroupSum.veluC H).Δ‖ * ‖MvPolynomial.eval (KatzForms.pt W) (Eh φ hℓ)‖ ^ 12 ≤ ‖(ℓ : K)‖ ^ 12 ∧
      ∀ C ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ, C ≠ H →
        ‖(SubgroupSum.veluC C).Δ‖ ^ ℓ ≤ ‖MvPolynomial.eval (KatzForms.pt W) (Eh φ hℓ)‖ ^ 12 := by
  classical
  have hφ' : ∀ x, φ x ∈ CanonicalIsogeny.integers K := hφ
  letI : Algebra ℤ_[ℓ] 𝒪 := (φ.codRestrict (CanonicalIsogeny.integers K) hφ').toAlgebra
  have hφ'' : ∀ x, (((algebraMap ℤ_[ℓ] 𝒪 x) : 𝒪) : K) = φ x := fun x => rfl
  set E := MvPolynomial.eval (KatzForms.pt W) (Eh φ hℓ)
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
  set a : 𝒪 := ⟨ConjAlg.sa W, hsa⟩
  set b : 𝒪 := ⟨ConjAlg.sb W, hsb⟩
  have hWK : toK (shortO a b) = (Velu.short (ConjAlg.sa W) (ConjAlg.sb W) : WeierstrassCurve K) :=
    toK_shortO a b
  have hΔ : ‖(((shortO a b).Δ : 𝒪) : K)‖ = 1 := by
    have e := congrArg WeierstrassCurve.Δ hWK
    simp only [toK, WeierstrassCurve.map_Δ, Subring.subtype_apply] at e
    rw [e, ConjAlg.shortModel_Δ]; exact hW.2.2.2.2.2
  have hptW : KatzForms.pt (toK (shortO a b)) = KatzForms.pt W := by
    rw [hWK]; exact ConjAlg.shortModel_ptR W
  have hEE : E = ((UpContraction.EpO ℓ hℓ (shortO a b) : 𝒪) : K) := by
    rw [← UpContraction.eval_pt_toK φ hφ'' hℓ (shortO a b)]
    show MvPolynomial.eval (KatzForms.pt W) (Eh φ hℓ) = MvPolynomial.eval (KatzForms.pt (toK (shortO a b))) (Eh φ hℓ)
    rw [hptW]
  have hEp : ‖(ℓ : K)‖ < ‖E‖ :=
    UpContraction.lt_of_break ℓ (norm_nonneg _) (norm_nonneg _) hss.le hB
  have haE : ‖((hasse (formalGroup (shortO a b)) ℓ : 𝒪) : K)‖ = ‖E‖ := by
    rw [hEE]
    exact UpContraction.norm_hasse_eq_EpO ℓ hℓ (shortO a b)
      (lt_of_lt_of_le (hEE ▸ hEp) (le_max_right _ _))
  have ha : ‖hasse (formalGroup (shortO a b)) ℓ‖ < 1 := by
    show ‖((hasse (formalGroup (shortO a b)) ℓ : 𝒪) : K)‖ < 1
    rw [haE]; exact hss
  have hbr : ‖(ℓ : K)‖ ^ ℓ < ‖hasse (formalGroup (shortO a b)) ℓ‖ ^ (ℓ + 1) := by
    show ‖(ℓ : K)‖ ^ ℓ < ‖((hasse (formalGroup (shortO a b)) ℓ : 𝒪) : K)‖ ^ (ℓ + 1)
    rw [haE]; exact hB
  obtain ⟨H, hH, h1, h2⟩ := velu_valuations a b ℓ hℓ hε hΔ ha hbr
  rw [haE] at h1 h2
  exact ⟨H, hH, h1.le, fun C hC hne => (h2 C hC hne).le⟩

/-- the ordinary-locus half of `QuotValBound` (not proved here). -/
def OrdBound (φ : ℤ_[ℓ] →+* K) : Prop :=
  ∀ W : WeierstrassCurve K, IsTest W → UpContraction.Brk ℓ (Eh φ hℓ) W →
    ‖MvPolynomial.eval (KatzForms.pt W) (Eh φ hℓ)‖ = 1 →
    ∃ H ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ,
      ‖(SubgroupSum.veluC H).Δ‖ * ‖MvPolynomial.eval (KatzForms.pt W) (Eh φ hℓ)‖ ^ 12 ≤ ‖(ℓ : K)‖ ^ 12 ∧
      ∀ C ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ, C ≠ H →
        ‖(SubgroupSum.veluC C).Δ‖ ^ ℓ ≤ ‖MvPolynomial.eval (KatzForms.pt W) (Eh φ hℓ)‖ ^ 12

/-- **`QuotValBound` from its ordinary half.** -/
theorem quotValBound_of_ord (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖)
    (hord : OrdBound hℓ φ) : ConjAlg.QuotValBound ℓ hℓ φ := by
  intro W hW hB
  have hEle : ‖MvPolynomial.eval (KatzForms.pt W) (Eh φ hℓ)‖ ≤ 1 :=
    (norm_eval_le (integral_pt hW) _).trans (gnorm_le zero_le_one (Eh_integral φ hφ hℓ))
  rcases hEle.lt_or_eq with hlt | heq
  · exact quotValBound_ss hℓ φ hφ hε W hW hB hlt
  · exact hord W hW hB heq

end QVB

/-! ### Over `ℂ_ℓ` -/

section C
variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-- **`QuotValBound` over `ℂ_ℓ`** (with `φ = SharpHQ.φC ℓ`), from its ordinary half. -/
theorem quotValBound_C [DecidableEq ℂ_[ℓ]] (hord : OrdBound hℓ (SharpHQ.φC ℓ)) :
    ConjAlg.QuotValBound ℓ hℓ (SharpHQ.φC ℓ) := by
  refine quotValBound_of_ord hℓ (SharpHQ.φC ℓ)
    (fun x => (SharpHQ.norm_φC x).trans_le (PadicInt.norm_le_one x)) ?_ hord
  rw [SharpHQ.norm_ell_C]; positivity

/-- **`QuotValBound` over `ℂ_ℓ` on the supersingular locus**, unconditionally. -/
theorem quotValBound_C_ss [DecidableEq ℂ_[ℓ]] (W : WeierstrassCurve ℂ_[ℓ]) (hW : KatzForms.IsTest W)
    (hB : UpContraction.Brk ℓ (KatzForms.Eh (SharpHQ.φC ℓ) hℓ) W)
    (hss : ‖MvPolynomial.eval (KatzForms.pt W) (KatzForms.Eh (SharpHQ.φC ℓ) hℓ)‖ < 1) :
    ∃ H ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ,
      ‖(SubgroupSum.veluC H).Δ‖ *
          ‖MvPolynomial.eval (KatzForms.pt W) (KatzForms.Eh (SharpHQ.φC ℓ) hℓ)‖ ^ 12 ≤
        ‖(ℓ : ℂ_[ℓ])‖ ^ 12 ∧
      ∀ C ∈ SubgroupSum.subs (ConjAlg.sa W) (ConjAlg.sb W) ℓ, C ≠ H →
        ‖(SubgroupSum.veluC C).Δ‖ ^ ℓ ≤
          ‖MvPolynomial.eval (KatzForms.pt W) (KatzForms.Eh (SharpHQ.φC ℓ) hℓ)‖ ^ 12 :=
  quotValBound_ss hℓ (SharpHQ.φC ℓ)
    (fun x => (SharpHQ.norm_φC x).trans_le (PadicInt.norm_le_one x))
    (by rw [SharpHQ.norm_ell_C]; positivity) W hW hB hss

end C

end AllQuotients
