/-
# `AllQuotients.OrdBound`: the ordinary locus

* **`velu_ord`** (short `W` over `𝒪`, good ordinary reduction `‖a_W‖ = 1`): with `H = Pt(T)` the
  kernel of reduction on `E[p]` (`T` = the `p`-torsion of the formal group, `p` points):
  * `‖Δ(veluC H)‖ ≤ ‖p‖^12` (integral descent: `‖Δ‖ ≤ ‖Lie π_H‖^12 = (∏_{h ≠ 0} ‖h‖)^12 = ‖p‖^12`);
  * `‖Δ(veluC G)‖ ≤ 1` for every other order-`p` subgroup `G` (étale: a nonzero point of `G` with
    `‖x‖ > 1` would lift to the formal group, hence lie in `H`, forcing `G = H`; so all points of
    `G` are integral and Vélu's formulas are integral).
* **`ordBound`**: `AllQuotients.OrdBound hℓ φ` for every integral `φ : ℤ_ℓ → K`.
* **`ordBound_C`**: `AllQuotients.OrdBound hℓ (SharpHQ.φC ℓ)`.
-/
import RamanujanTau.OrdQuot.Bound

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace OrdQuot
open MvPowerSeries EllipticFormal EllipticI2 CanonicalIsogeny QuotientHasse VeluLubin AllQuotients

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K]
  [CharZero K] [DecidableEq K]

local notation "𝒪" => CanonicalIsogeny.integers K

/-- **Vélu quotients of an ordinary short curve: the data.** `H = Pt(T)`; the `μ`-scaled Vélu
quotient by `H` is integral with `‖μ‖ = ‖p‖`; every other order-`p` subgroup has integral points. -/
theorem velu_ord_data (a b : ↥(CanonicalIsogeny.integers K)) (p : ℕ) [hpf : Fact p.Prime]
    (hp5 : 5 ≤ p) (hε : 0 < ‖(p : K)‖) (hp1 : ‖(p : K)‖ < 1)
    (hΔ : ‖(((shortO a b).Δ : 𝒪) : K)‖ = 1)
    (ha : ‖hasse (formalGroup (shortO a b)) p‖ = 1) :
    ∃ H ∈ SubgroupSum.subs (a : K) (b : K) p,
      ‖(SubgroupSum.veluC H).Δ‖ ≤ ‖(p : K)‖ ^ 12 ∧
      (∃ (μ : K) (hμ : μ ≠ 0), ‖μ‖ = ‖(p : K)‖ ∧ ∃ A'' B'' : ↥(CanonicalIsogeny.integers K),
        toK (shortO A'' B'') = ((⟨Units.mk0 μ hμ, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) •
          (SubgroupSum.veluC H : WeierstrassCurve K))) ∧
      ∀ G ∈ SubgroupSum.subs (a : K) (b : K) p, G ≠ H →
        ∀ Q ∈ G, ‖Velu.xc Q‖ ≤ 1 ∧ ‖Velu.yc Q‖ ≤ 1 := by
  classical
  have hp := hpf.out
  have hΔ' := disc_ne_zero a b hΔ
  have h2 : ‖(2 : K)‖ = 1 := by
    have := norm_nat_eq_one (K := K) p hp1 2 (fun h => by
      have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  have h3 : ‖(3 : K)‖ = 1 := by
    have := norm_nat_eq_one (K := K) p hp1 3 (fun h => by
      have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  obtain ⟨T, hT, hTc, hTp⟩ := ord_torsion (formalGroup (shortO a b)) p ha hε hp1
  have hT' : ∀ z, z ∈ T ↔ ‖(z : K)‖ < 1 ∧ nm a b z p = 0 := hT
  set S := torsSub a b p T hT'
  have hpS : ∀ h ∈ S.H, nm a b h p = 0 := fun h hh => ((hT' h).1 hh).2
  obtain ⟨κ, hκ⟩ := exists_kernel_of_finSub a b hp hp5 S hpS
  have hκG : κ.G = T.image (Pt a b) := by
    apply Finset.coe_injective; rw [hκ, Finset.coe_image]; rfl
  set H := T.image (Pt a b) with hHdef
  have hH : H ∈ SubgroupSum.subs (a : K) (b : K) p :=
    image_mem_subs a b hp hp5 hT' S subset_rfl hTc
  have hTp' : ∏ c ∈ S.H.erase 0, ‖(c : K)‖ = ‖(p : K)‖ := hTp
  refine ⟨H, hH, ?_, ?_, ?_⟩
  · have e := norm_Δ_velu_le a b p hp5 hp1 hΔ' S κ hκ
    rw [hκG] at e
    rw [hTp'] at e
    exact e
  · obtain ⟨A'', B'', hK⟩ := exists_model_velu a b p hp5 hp1 hΔ' S κ hκ
    rw [hκG] at hK
    refine ⟨_, lie_pis_ne_zero S, ?_, A'', B'', hK⟩
    rw [norm_lie_pis]; exact hTp'
  · intro G hG hne Q hQ
    cases Q with
    | zero => simp [Velu.xc, Velu.yc]
    | some x y hxy =>
      have hx : ‖x‖ ≤ 1 := by
        by_contra hx
        have hx := not_le.mp hx
        obtain ⟨z, hz0, hz, hzP⟩ := lift_point a b hxy hx
        have hpQ := HeckeBridge.nsmul_eq_zero_of_mem_subs hG hQ
        have hnm := nm_p_of_Pt a b hp5 h3 hz0 hz (by rw [hzP]; exact hpQ)
        have hzT : z ∈ T := (hT' z).2 ⟨hz, hnm⟩
        have hQH : WeierstrassCurve.Affine.Point.some x y hxy ∈ H :=
          Finset.mem_image.2 ⟨z, hzT, hzP⟩
        have hQ0 : (WeierstrassCurve.Affine.Point.some x y hxy :
            (Velu.short (a : K) (b : K)).Point) ≠ 0 := fun h => by cases h
        apply hne
        rw [← HeckeBridge.eq_zm_of_mem hG hQ hQ0, HeckeBridge.eq_zm_of_mem hH hQH hQ0]
      have heq : y ^ 2 = x ^ 3 + (a : K) * x + (b : K) :=
        (Velu.short_equation_iff _ _ _ _).1 hxy.1
      have hxO : x ∈ CanonicalIsogeny.integers K := hx
      have hrhs : x ^ 3 + (a : K) * x + (b : K) ∈ CanonicalIsogeny.integers K :=
        add_mem (add_mem (pow_mem hxO 3) (mul_mem a.2 hxO)) b.2
      have hy2 : ‖y‖ ^ 2 ≤ 1 := by
        rw [← norm_pow, heq]; exact hrhs
      refine ⟨by simpa using hx, ?_⟩
      simp only [Velu.yc_some]
      exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hy2

/-- **Vélu quotients of an ordinary short curve.** -/
theorem velu_ord (a b : ↥(CanonicalIsogeny.integers K)) (p : ℕ) [hpf : Fact p.Prime]
    (hp5 : 5 ≤ p) (hε : 0 < ‖(p : K)‖) (hp1 : ‖(p : K)‖ < 1)
    (hΔ : ‖(((shortO a b).Δ : 𝒪) : K)‖ = 1)
    (ha : ‖hasse (formalGroup (shortO a b)) p‖ = 1) :
    ∃ H ∈ SubgroupSum.subs (a : K) (b : K) p,
      ‖(SubgroupSum.veluC H).Δ‖ ≤ ‖(p : K)‖ ^ 12 ∧
      ∀ G ∈ SubgroupSum.subs (a : K) (b : K) p, G ≠ H → ‖(SubgroupSum.veluC G).Δ‖ ≤ 1 := by
  obtain ⟨H, hH, h1, -, h3⟩ := velu_ord_data a b p hp5 hε hp1 hΔ ha
  have h2 : ‖(2 : K)‖ = 1 := by
    have := norm_nat_eq_one (K := K) p hp1 2 (fun h => by
      have := Nat.le_of_dvd (by norm_num) h; omega)
    simpa using this
  exact ⟨H, hH, h1, fun G hG hne => norm_Δ_veluC_le_one a.2 b.2 h2 G (h3 G hG hne)⟩

/-! ### `OrdBound` -/

section Ord
open KatzForms

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-- **`AllQuotients.OrdBound`** for every integral `φ : ℤ_ℓ → K`. -/
theorem ordBound (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖) :
    OrdBound hℓ φ := by
  classical
  intro W hW hB hord
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
  have hΔ : ‖(((shortO a b).Δ : 𝒪) : K)‖ = 1 := by
    have e := congrArg WeierstrassCurve.Δ hWK
    simp only [toK, WeierstrassCurve.map_Δ, Subring.subtype_apply] at e
    rw [e, ConjAlg.shortModel_Δ]; exact hW.2.2.2.2.2
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
  obtain ⟨H, hH, h1, h2'⟩ := velu_ord a b ℓ hℓ hε hl1 hΔ ha
  refine ⟨H, hH, ?_, fun C hC hne => ?_⟩
  · rw [hord, one_pow, mul_one]; exact h1
  · rw [hord, one_pow]; exact pow_le_one₀ (norm_nonneg _) (h2' C hC hne)

/-- **`AllQuotients.OrdBound` over `ℂ_ℓ`** (with `φ = SharpHQ.φC ℓ`). -/
theorem ordBound_C [DecidableEq ℂ_[ℓ]] : OrdBound hℓ (SharpHQ.φC ℓ) :=
  ordBound hℓ (SharpHQ.φC ℓ) (fun x => (SharpHQ.norm_φC x).trans_le (PadicInt.norm_le_one x))
    (by rw [SharpHQ.norm_ell_C]; positivity)

end Ord

end OrdQuot
