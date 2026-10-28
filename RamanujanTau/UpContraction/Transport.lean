/-
# Discharging `QuotHyp` from formal-group data (Buzzard 3.3(v) on curves)

1. **Hasse transport** (`hasse_transport`, any commutative ring `R`): a homomorphism `f : F → G` of
   commutative formal groups with Lie derivative `u = f'(0)` satisfies
   `u·a_F ≡ u^p·a_G (mod p)`, `a = coeff_p [p]`. (Compare `T^p`-coefficients of
   `f ∘ [p]_F = [p]_G ∘ f` modulo `p`, where `[p] ≡ T^p·(a + …)`.)
   Over `𝒪 = integers K`: if `‖u‖ = 1` and one of `‖a_F‖, ‖a_G‖` exceeds `‖p‖`, they are equal
   (`norm_hasse_eq_of_hom`).
2. **`quot_E_pow`**: for a good-reduction curve `W` over `𝒪` in the supersingular break region, an
   order-`p` subgroup `C ⊂ F_W[p]` with no canonical point, and a good-reduction curve `W'` whose
   formal group maps to Lubin's quotient `F_W/C` by a homomorphism with unit Lie derivative
   (`QuotModel`, the Vélu–Lubin link for `C`): `‖E_{p−1}(W')‖^p = ‖E_{p−1}(W)‖`.
   Proof: Buzzard 3.3(v) (`QuotientHasse.hasse_quot_noncanonical`), transport, and Deligne's
   congruence `a ≡ E_{p−1} (mod p)` (`HasseInv.coeff_nmul_sub_hasseA_mem'`).
3. **`quotHyp_of_models`**: `QuotHyp` (the hypothesis of `thmB`/`UB`) follows from
   * supersingular part: every test curve in the break region with `‖E‖ < 1` has an integral model
     whose `p` quotient curves `Q W c` come from `QuotModel`s for `p` order-`p` non-canonical
     subgroups;
   * ordinary part: if `‖E(W)‖ = 1`, the `Q W c` are test curves with `‖E(Q W c)‖ = 1`.
-/
import RamanujanTau.QuotientHasse.Main
import RamanujanTau.HeightEll.Reduce
import RamanujanTau.HasseInv.Unconditional
import RamanujanTau.UpContraction.ThmB

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UpContraction
open MvPowerSeries CanonicalIsogeny

/-! ### 1. Hasse transport along a homomorphism -/

section Transport
variable {R : Type*} [CommRing R]

/-- `f` is a homomorphism `F → G` (same body as `CanonicalIsogeny.IsHom` and `EllipticI2.Hom`). -/
def HomR (F G : FormalGroup R) (f : MvPowerSeries Unit R) : Prop :=
  constantCoeff f = 0 ∧
    subst (fun _ : Unit => FGL.ev F (X 0 : MvPowerSeries (Fin 2) R) (X 1)) f =
      FGL.ev G (subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) f)
        (subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) f)

variable {S : Type*} [CommRing S]

/-- `(X^n B) ∘ (X^m A)` has `T^{mn}`-coefficient `A(0)^n B(0)`. -/
lemma coeff_subst_monomial (m n : ℕ) (hm : 1 ≤ m) (A B : PowerSeries S) :
    PowerSeries.coeff (m * n)
        (subst (fun _ : Unit => (PowerSeries.X ^ m * A : PowerSeries S))
          (PowerSeries.X ^ n * B : PowerSeries S) : PowerSeries S) =
      MvPowerSeries.constantCoeff A ^ n * MvPowerSeries.constantCoeff B := by
  set g : PowerSeries S := PowerSeries.X ^ m * A
  have hg : MvPowerSeries.constantCoeff g = 0 := by
    change MvPowerSeries.constantCoeff (PowerSeries.X ^ m * A : PowerSeries S) = 0
    rw [map_mul, map_pow]
    have : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries S) = 0 := by
      change PowerSeries.constantCoeff (PowerSeries.X : PowerSeries S) = 0; simp
    rw [this, zero_pow (by omega), zero_mul]
  have h0 : ∀ s : Unit, MvPowerSeries.constantCoeff ((fun _ : Unit => g) s) = 0 := fun _ => hg
  have hs := FGL.hs h0
  have hX : subst (fun _ : Unit => g) (PowerSeries.X : PowerSeries S) = g := FGL.sX _ h0 ()
  rw [subst_mul hs, subst_pow hs, hX]
  have : g ^ n * subst (fun _ : Unit => g) B =
      PowerSeries.X ^ (m * n) * (A ^ n * subst (fun _ : Unit => g) B) := by
    simp only [g]; rw [mul_pow, ← pow_mul]; ring
  rw [this, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]
  change MvPowerSeries.constantCoeff (A ^ n * subst (fun _ : Unit => g) B) = _
  rw [map_mul, map_pow, FGL.cc_subst _ h0 B]

lemma map_mk_coeff_nmul_lt (F : FormalGroup R) [F.IsComm] (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hk : k < p) :
    PowerSeries.coeff k (MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)}))
      (FGL.nmul F p) : PowerSeries (R ⧸ Ideal.span {(p : R)})) = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    change MvPowerSeries.constantCoeff (MvPowerSeries.map _ (FGL.nmul F p)) = 0
    rw [MvPowerSeries.constantCoeff_map, FGL.cc_nmul, map_zero]
  · have hnd : ¬ p ∣ k := Nat.not_dvd_of_pos_of_lt hk0 hk
    change MvPowerSeries.coeff (Finsupp.single () k) (MvPowerSeries.map _ (FGL.nmul F p)) = 0
    rw [MvPowerSeries.coeff_map, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact FGL.p_dvd_coeff_nmul F p k hnd

/-- `[p] mod p = T^p · A` with `A(0) = a mod p`. -/
lemma nmul_mod_p (F : FormalGroup R) [F.IsComm] (p : ℕ) [Fact p.Prime] :
    ∃ A : PowerSeries (R ⧸ Ideal.span {(p : R)}),
      (MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)})) (FGL.nmul F p) :
          PowerSeries (R ⧸ Ideal.span {(p : R)})) = PowerSeries.X ^ p * A ∧
        MvPowerSeries.constantCoeff A =
          Ideal.Quotient.mk _ (coeff (Finsupp.single () p) (FGL.nmul F p)) := by
  set N : PowerSeries (R ⧸ Ideal.span {(p : R)}) :=
    MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)})) (FGL.nmul F p)
  obtain ⟨A, hA⟩ := PowerSeries.X_pow_dvd_iff.mpr fun k hk => map_mk_coeff_nmul_lt F p k hk
  refine ⟨A, hA, ?_⟩
  have h := congrArg (PowerSeries.coeff p) hA
  rw [PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  rw [show MvPowerSeries.constantCoeff A = PowerSeries.constantCoeff A from rfl, ← h]
  change MvPowerSeries.coeff (Finsupp.single () p) (MvPowerSeries.map _ (FGL.nmul F p)) = _
  rw [MvPowerSeries.coeff_map]

/-- **Hasse transport**: `u·a_F − u^p·a_G ∈ (p)` for a homomorphism `f : F → G`, `u = f'(0)`. -/
theorem hasse_transport (F G : FormalGroup R) [F.IsComm] [G.IsComm] (p : ℕ) [hp : Fact p.Prime]
    (f : MvPowerSeries Unit R) (hf : HomR F G f) :
    coeff (Finsupp.single () 1) f * coeff (Finsupp.single () p) (FGL.nmul F p) -
        coeff (Finsupp.single () 1) f ^ p * coeff (Finsupp.single () p) (FGL.nmul G p) ∈
      Ideal.span {(p : R)} := by
  set I := Ideal.span {(p : R)}
  set π := Ideal.Quotient.mk I
  have hcomp := QuotientHasse.hom_nmul F G f hf.1 hf.2 p
  have hm := congrArg (MvPowerSeries.map π) hcomp
  rw [MvPowerSeries.map_subst (FGL.hs (fun _ => hf.1)),
    MvPowerSeries.map_subst (FGL.hs (fun _ => FGL.cc_nmul F p))] at hm
  obtain ⟨AF, hAF, hAF0⟩ := nmul_mod_p F p
  obtain ⟨AG, hAG, hAG0⟩ := nmul_mod_p G p
  -- `f mod p = X · B`
  set fb : PowerSeries (R ⧸ I) := MvPowerSeries.map π f
  have hfb0 : PowerSeries.constantCoeff fb = 0 := by
    change MvPowerSeries.constantCoeff (MvPowerSeries.map π f) = 0
    rw [MvPowerSeries.constantCoeff_map, hf.1, map_zero]
  obtain ⟨B, hB⟩ := PowerSeries.X_dvd_iff.mpr hfb0
  have hB0 : MvPowerSeries.constantCoeff B = π (coeff (Finsupp.single () 1) f) := by
    have h := congrArg (PowerSeries.coeff 1) hB
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
    rw [show MvPowerSeries.constantCoeff B = PowerSeries.constantCoeff B from rfl, ← h]
    change MvPowerSeries.coeff (Finsupp.single () 1) (MvPowerSeries.map π f) = _
    rw [MvPowerSeries.coeff_map]
  have hfb : fb = PowerSeries.X ^ 1 * B := by rw [pow_one]; exact hB
  -- compare `T^p` coefficients
  have hm' := congrArg (PowerSeries.coeff p) hm
  change PowerSeries.coeff p (subst (fun _ : Unit => fb)
      (MvPowerSeries.map π (FGL.nmul G p) : PowerSeries (R ⧸ I)) : PowerSeries (R ⧸ I)) =
    PowerSeries.coeff p (subst (fun _ : Unit =>
      (MvPowerSeries.map π (FGL.nmul F p) : PowerSeries (R ⧸ I))) fb : PowerSeries (R ⧸ I)) at hm'
  rw [hfb, hAG, hAF] at hm'
  have hL := coeff_subst_monomial 1 p le_rfl B AG
  have hR := coeff_subst_monomial p 1 hp.out.one_lt.le AF B
  rw [one_mul] at hL
  rw [mul_one] at hR
  rw [hL, hR, hB0, hAG0, hAF0, pow_one] at hm'
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, map_pow]
  rw [hm']; ring

end Transport

/-! ### Norm transport over `𝒪 = integers K` -/

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => integers K

/-- ultrametric: `‖x − y‖ ≤ ε < max ‖x‖ ‖y‖` forces `‖x‖ = ‖y‖`. -/
lemma norm_eq_of_close {x y : K} {ε : ℝ} (h : ‖x - y‖ ≤ ε) (hbig : ε < max ‖x‖ ‖y‖) :
    ‖x‖ = ‖y‖ := by
  by_contra hne
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := x) (y := -y)
    (by rwa [norm_neg])
  rw [norm_neg, ← sub_eq_add_neg] at this
  linarith

lemma norm_le_of_mem_span_p (p : ℕ) {z : 𝒪} (h : z ∈ Ideal.span {(p : 𝒪)}) :
    ‖(z : K)‖ ≤ ‖(p : K)‖ := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp h
  rw [Subring.coe_mul, norm_mul, Subring.coe_natCast]
  exact mul_le_of_le_one_left (norm_nonneg _) c.2

/-- **norm transport**: a homomorphism with unit Lie derivative preserves `‖a‖` above `‖p‖`. -/
theorem norm_hasse_eq_of_hom (F G : FormalGroup 𝒪) [F.IsComm] [G.IsComm] (p : ℕ) [Fact p.Prime]
    (f : MvPowerSeries Unit 𝒪) (hf : HomR F G f)
    (hu : ‖((coeff (Finsupp.single () 1) f : 𝒪) : K)‖ = 1)
    (hbig : ‖(p : K)‖ < max ‖((QuotientHasse.hasse F p : 𝒪) : K)‖
      ‖((QuotientHasse.hasse G p : 𝒪) : K)‖) :
    ‖((QuotientHasse.hasse F p : 𝒪) : K)‖ = ‖((QuotientHasse.hasse G p : 𝒪) : K)‖ := by
  have h := norm_le_of_mem_span_p p (hasse_transport F G p f hf)
  set u : K := ((coeff (Finsupp.single () 1) f : 𝒪) : K)
  simp only [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, SubmonoidClass.coe_pow] at h
  have e1 : ‖u * ((QuotientHasse.hasse F p : 𝒪) : K)‖ = ‖((QuotientHasse.hasse F p : 𝒪) : K)‖ := by
    rw [norm_mul, hu, one_mul]
  have e2 : ‖u ^ p * ((QuotientHasse.hasse G p : 𝒪) : K)‖ =
      ‖((QuotientHasse.hasse G p : 𝒪) : K)‖ := by
    rw [norm_mul, norm_pow, hu, one_pow, one_mul]
  have := norm_eq_of_close h (by rw [e1, e2]; exact hbig)
  rwa [e1, e2] at this

/-! ### 2. `‖E(W/C)‖^p = ‖E(W)‖` for non-canonical `C` -/

section Quot
variable [CompleteSpace K]
variable (p : ℕ) [hp : Fact p.Prime] [Algebra ℤ_[p] (integers K)]

/-- `E_{p−1}(W) = A(c₄, −c₆) ∈ 𝒪`. -/
noncomputable def EpO (hp5 : 5 ≤ p) (W : WeierstrassCurve 𝒪) : 𝒪 :=
  MvPolynomial.aeval ![W.c₄, -W.c₆] (ModP.hasseA p hp5)

/-- Deligne + ultrametric: `‖a‖ = ‖E_{p−1}(W)‖` once one of them exceeds `‖p‖`. -/
theorem norm_hasse_eq_EpO (hp5 : 5 ≤ p) (W : WeierstrassCurve 𝒪)
    (hbig : ‖(p : K)‖ < max ‖((QuotientHasse.hasse (EllipticFormal.formalGroup W) p : 𝒪) : K)‖
      ‖((EpO p hp5 W : 𝒪) : K)‖) :
    ‖((QuotientHasse.hasse (EllipticFormal.formalGroup W) p : 𝒪) : K)‖ =
      ‖((EpO p hp5 W : 𝒪) : K)‖ := by
  have h := norm_le_of_mem_span_p p (HasseInv.coeff_nmul_sub_hasseA_mem' p hp5 W)
  simp only [AddSubgroupClass.coe_sub] at h
  exact norm_eq_of_close h hbig

/-- `‖p‖^p < α^{p+1}` and `α ≤ 1` give `‖p‖ < α`. -/
lemma lt_of_break {α ε : ℝ} (_hε : 0 ≤ ε) (hα0 : 0 ≤ α) (hα : α ≤ 1) (h : ε ^ p < α ^ (p + 1)) :
    ε < α := by
  by_contra hc
  push Not at hc
  have h1 : α ^ (p + 1) ≤ α ^ p := pow_le_pow_of_le_one hα0 hα (by omega)
  have h2 : α ^ p ≤ ε ^ p := pow_le_pow_left₀ hα0 hc p
  linarith

/-- **Buzzard 3.3(v) for curves**: `‖E_{p−1}(W/C)‖^p = ‖E_{p−1}(W)‖` for non-canonical `C`.
`W'` is a good-reduction model of the quotient by `C`: its formal group maps to Lubin's `F_W/C` by a
homomorphism `ψ` with unit Lie derivative (the Vélu–Lubin link for `C`; cf. `EllipticI2.VeluLubinLink`). -/
theorem quot_E_pow [IsAlgClosed K] (hp5 : 5 ≤ p) (W : WeierstrassCurve 𝒪)
    (hε : 0 < ‖(p : K)‖) (hΔ : ‖((W.Δ : 𝒪) : K)‖ = 1) (hE : ‖((EpO p hp5 W : 𝒪) : K)‖ < 1)
    (hbreak : ‖(p : K)‖ ^ p < ‖((EpO p hp5 W : 𝒪) : K)‖ ^ (p + 1))
    (C : Lubin.FinSub (EllipticFormal.formalGroup W))
    (hCp : ∀ c ∈ C.H, Lubin.pt (fun _ : Unit => c) (FGL.nmul (EllipticFormal.formalGroup W) p) = 0)
    (hcard : C.H.card = p)
    (hCH : ∀ c ∈ C.H, c ≠ 0 →
      ‖((QuotientHasse.hasse (EllipticFormal.formalGroup W) p : 𝒪) : K)‖ * ‖(c : K)‖ ^ (p - 1) ≠
        ‖(p : K)‖)
    (W' : WeierstrassCurve 𝒪) (ψ : MvPowerSeries Unit 𝒪)
    (hψ : HomR (EllipticFormal.formalGroup W') (Lubin.quot C) ψ)
    (hψu : ‖((coeff (Finsupp.single () 1) ψ : 𝒪) : K)‖ = 1) :
    ‖((EpO p hp5 W' : 𝒪) : K)‖ ^ p = ‖((EpO p hp5 W : 𝒪) : K)‖ := by
  have hEp : ‖(p : K)‖ < ‖((EpO p hp5 W : 𝒪) : K)‖ :=
    lt_of_break p (norm_nonneg _) (norm_nonneg _) (EpO p hp5 W).2 hbreak
  have haF := norm_hasse_eq_EpO p hp5 W (lt_of_lt_of_le hEp (le_max_right _ _))
  have hp1 : ‖(p : K)‖ < 1 := hEp.trans hE
  have ha : ‖((QuotientHasse.hasse (EllipticFormal.formalGroup W) p : 𝒪) : K)‖ < 1 := by
    rw [haF]; exact hE
  have hu := HeightEll.topc_norm_eq_one W p hp5 hp1 hΔ ha
  have hbF : ‖(p : K)‖ ^ p <
      ‖((QuotientHasse.hasse (EllipticFormal.formalGroup W) p : 𝒪) : K)‖ ^ (p + 1) := by
    rw [haF]; exact hbreak
  have hq := QuotientHasse.hasse_quot_noncanonical (EllipticFormal.formalGroup W) p hu ha hε hbF C
    hCp hcard hCH
  have hpow : ‖((QuotientHasse.hasse (Lubin.quot C) p : 𝒪) : K)‖ ^ p =
      ‖((QuotientHasse.hasse (EllipticFormal.formalGroup W) p : 𝒪) : K)‖ := hq.2.2.1
  have hbG := hq.2.2.2.1
  have hGp : ‖(p : K)‖ < ‖((QuotientHasse.hasse (Lubin.quot C) p : 𝒪) : K)‖ :=
    lt_of_break p (norm_nonneg _) (norm_nonneg _) (QuotientHasse.hasse (Lubin.quot C) p).2 hbG
  have htr := norm_hasse_eq_of_hom _ _ p ψ hψ hψu (lt_of_lt_of_le hGp (le_max_right _ _))
  have hW'p : ‖(p : K)‖ <
      ‖((QuotientHasse.hasse (EllipticFormal.formalGroup W') p : 𝒪) : K)‖ := by
    rw [htr]; exact hGp
  have haW' := norm_hasse_eq_EpO p hp5 W' (lt_of_lt_of_le hW'p (le_max_left _ _))
  rw [← haW', htr, hpow, haF]

end Quot

/-! ### 3. `QuotHyp` from models -/

section Models
open KatzForms MvPolynomial

variable [CompleteSpace K] {p : ℕ} [hp : Fact p.Prime] [Algebra ℤ_[p] (integers K)]

/-- the base change of an `𝒪`-curve to `K`. -/
noncomputable abbrev toK (W : WeierstrassCurve 𝒪) : WeierstrassCurve K :=
  W.map (integers K).subtype

lemma isTest_toK (W : WeierstrassCurve 𝒪) (hΔ : ‖((W.Δ : 𝒪) : K)‖ = 1) : IsTest (toK W) := by
  refine ⟨W.a₁.2, W.a₂.2, W.a₃.2, W.a₄.2, W.a₆.2, ?_⟩
  rw [WeierstrassCurve.map_Δ]; exact hΔ

/-- `E(pt (toK W)) = E_{p−1}(W)` when `φ` is the structure map. -/
lemma eval_pt_toK (φ : ℤ_[p] →+* K) (hφ : ∀ x, (((algebraMap ℤ_[p] 𝒪 x) : 𝒪) : K) = φ x)
    (hp5 : 5 ≤ p) (W : WeierstrassCurve 𝒪) :
    eval (pt (toK W)) (Eh φ hp5) = ((EpO p hp5 W : 𝒪) : K) := by
  rw [Eh, eval_map, EpO, aeval_def]
  change _ = (integers K).subtype (MvPolynomial.eval₂ (algebraMap ℤ_[p] 𝒪) ![W.c₄, -W.c₆] (ModP.hasseA p hp5))
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  · ext x; exact (hφ x).symm
  · funext i
    fin_cases i
    · simp [pt, toK, WeierstrassCurve.map_c₄]
    · simp [pt, toK, WeierstrassCurve.map_c₆]

/-- Data at a supersingular test curve `W`: an integral model `W₀`, and for each `c : Fin p` a
non-canonical order-`p` subgroup `C ⊂ F_{W₀}[p]` with a good-reduction quotient model `W'`
(formal group mapping to `F_{W₀}/C` with unit Lie derivative) whose base change is `Qs c`. -/
def SSData (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve K) (Qs : Fin p → WeierstrassCurve K) :
    Prop :=
  ∃ W₀ : WeierstrassCurve 𝒪, toK W₀ = W ∧ ∀ c : Fin p,
    ∃ C : Lubin.FinSub (EllipticFormal.formalGroup W₀),
      (∀ x ∈ C.H, Lubin.pt (fun _ : Unit => x) (FGL.nmul (EllipticFormal.formalGroup W₀) p) = 0) ∧
      C.H.card = p ∧
      (∀ x ∈ C.H, x ≠ 0 →
        ‖((QuotientHasse.hasse (EllipticFormal.formalGroup W₀) p : 𝒪) : K)‖ * ‖(x : K)‖ ^ (p - 1) ≠
          ‖(p : K)‖) ∧
      ∃ (W' : WeierstrassCurve 𝒪) (ψ : MvPowerSeries Unit 𝒪),
        ‖((W'.Δ : 𝒪) : K)‖ = 1 ∧ HomR (EllipticFormal.formalGroup W') (Lubin.quot C) ψ ∧
        ‖((coeff (Finsupp.single () 1) ψ : 𝒪) : K)‖ = 1 ∧ toK W' = Qs c

/-- **`QuotHyp` from models.** -/
theorem quotHyp_of_models [IsAlgClosed K] (φ : ℤ_[p] →+* K)
    (hφ : ∀ x, (((algebraMap ℤ_[p] 𝒪 x) : 𝒪) : K) = φ x) (hp5 : 5 ≤ p) (hε : 0 < ‖(p : K)‖)
    (Q : WeierstrassCurve K → Fin p → WeierstrassCurve K)
    (hss : ∀ W, IsTest W → Brk p (Eh φ hp5) W → ‖eval (pt W) (Eh φ hp5)‖ < 1 → SSData p W (Q W))
    (hord : ∀ W, IsTest W → ‖eval (pt W) (Eh φ hp5)‖ = 1 → ∀ c,
      IsTest (Q W c) ∧ ‖eval (pt (Q W c)) (Eh φ hp5)‖ = 1) :
    QuotHyp p (Eh φ hp5) Q := by
  intro W hW hB c
  have hEle : ‖eval (pt W) (Eh φ hp5)‖ ≤ 1 := by
    have hφ1 : ∀ x, ‖φ x‖ ≤ 1 := fun x => by rw [← hφ x]; exact (algebraMap ℤ_[p] 𝒪 x).2
    exact (norm_eval_le (integral_pt hW) _).trans
      (gnorm_le zero_le_one (Eh_integral φ hφ1 hp5))
  rcases hEle.lt_or_eq with hlt | heq
  · obtain ⟨W₀, hW₀, hC⟩ := hss W hW hB hlt
    obtain ⟨C, hCp, hcard, hCH, W', ψ, hΔ', hψ, hψu, hM⟩ := hC c
    have hΔ0 : ‖((W₀.Δ : 𝒪) : K)‖ = 1 := by
      have := hW.2.2.2.2.2
      rw [← hW₀, WeierstrassCurve.map_Δ] at this; exact this
    have hEW : eval (pt W) (Eh φ hp5) = ((EpO p hp5 W₀ : 𝒪) : K) := by
      rw [← hW₀]; exact eval_pt_toK φ hφ hp5 W₀
    have hB' := hB
    unfold Brk at hB'
    rw [hEW] at hB' hlt
    have hpow := quot_E_pow p hp5 W₀ hε hΔ0 hlt hB' C hCp hcard hCH W' ψ hψ hψu
    refine ⟨?_, ?_⟩
    · rw [← hM]; exact isTest_toK _ hΔ'
    · rw [← hM, eval_pt_toK φ hφ hp5, hEW]; exact hpow
  · obtain ⟨hT, h1⟩ := hord W hW heq c
    exact ⟨hT, by rw [h1, heq, one_pow]⟩

end Models

end UpContraction
