/-
# Step 3 of I2 at the formal-group level (conditional on the Vélu–Lubin link)

Pointwise content of Step 3: `|VΔ/Δ^p (x)| = ‖λ‖^{-12}` with `λ = Lie π̌`, hence
`|Q(x)|^{12} = ‖E_{p−1}(W)‖^{12} ‖λ‖^{-12} = 1`.

Proved here (axiom-clean):
* `hom_comp`: composites of formal-group homomorphisms are homomorphisms (any commutative ring).
* `VeluLubinLink W G`: the **hypothesis** that Lubin's quotient `G` is the formal group of a
  good-reduction Weierstrass curve `W'` up to an isomorphism `ψ : F_{W'} → G` with unit Lie
  derivative. This is the open Vélu–Lubin link (target statement in `Link_WIP.lean`).
* `elliptic_step3`: given the link,
  1. `π̌' := π̌ ∘ ψ : F_{W'} → F_W` is a homomorphism with `‖Lie π̌'‖ = ‖a‖ = ‖E_{p−1}(W)‖`;
  2. `π̌'^* ω_W = λ · ω_{W'}` (differentials `dT/Ψ`), `λ = Lie π̌'`;
  3. `W'' := ⟨λ,0,0,0⟩ • W'_K` (the curve `E'` with differential `λ ω_{W'} = π̌^* ω`) satisfies
     `F_{W''}(λX, λY) = λ F_{W'}(X, Y)` and `‖Δ(W'')‖ = ‖λ‖^{-12}`;
  4. `‖E_{p−1}(W)‖^{12} · ‖Δ(W'')‖ / ‖Δ(W)‖^p = 1`, i.e. `v(Q(x)) = 0`.
-/
import RamanujanTau.EllipticI2.Step2
import RamanujanTau.EllipticFormal.All

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EllipticI2
open MvPowerSeries EllipticFormal CanonicalIsogeny QuotientHasse FGL

section Comp
variable {R : Type*} [CommRing R]

/-- raw homomorphism property (same body as `CanonicalIsogeny.IsHom`, over any commutative ring). -/
def Hom (F G : FormalGroup R) (f : MvPowerSeries Unit R) : Prop :=
  constantCoeff f = 0 ∧
    subst (fun _ : Unit => FGL.ev F (X 0 : MvPowerSeries (Fin 2) R) (X 1)) f =
      FGL.ev G (subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) f)
        (subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) f)

lemma cX0 : constantCoeff (X 0 : MvPowerSeries (Fin 2) R) = 0 := by simp
lemma cX1 : constantCoeff (X 1 : MvPowerSeries (Fin 2) R) = 0 := by simp

/-- **composites of homomorphisms are homomorphisms**: `g ∘ f`. -/
theorem hom_comp {F₁ F₂ F₃ : FormalGroup R} {f g : MvPowerSeries Unit R} (hf : Hom F₁ F₂ f)
    (hg : Hom F₂ F₃ g) : Hom F₁ F₃ (subst (fun _ : Unit => f) g) := by
  obtain ⟨hf0, hfh⟩ := hf
  obtain ⟨hg0, hgh⟩ := hg
  have h1f : ∀ s : Unit, constantCoeff ((fun _ : Unit => f) s) = 0 := fun _ => hf0
  set f0 := subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) f
  set f1 := subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) f
  have hf00 : constantCoeff f0 = 0 := cc0 _ (fun _ => cX0) hf0
  have hf10 : constantCoeff f1 = 0 := cc0 _ (fun _ => cX1) hf0
  have hv := cc_vec2 hf00 hf10
  have hE1 : constantCoeff (FGL.ev F₁ (X 0 : MvPowerSeries (Fin 2) R) (X 1)) = 0 :=
    cc_ev F₁ cX0 cX1
  have hE2 : constantCoeff (FGL.ev F₂ (X 0 : MvPowerSeries (Fin 2) R) (X 1)) = 0 :=
    cc_ev F₂ cX0 cX1
  refine ⟨cc0 _ h1f hg0, ?_⟩
  -- the three pieces
  have hX : ∀ i : Fin 2, subst (fun _ : Unit => (X i : MvPowerSeries (Fin 2) R)) (subst (fun _ : Unit => f) g)
      = subst (fun _ : Unit => subst (fun _ : Unit => (X i : MvPowerSeries (Fin 2) R)) f) g := by
    intro i
    rw [ss _ _ h1f (fun _ => by simp)]
  have e2 : FGL.ev F₂ f0 f1 = subst ![f0, f1] (FGL.ev F₂ (X 0 : MvPowerSeries (Fin 2) R) (X 1)) := by
    rw [subst_ev F₂ _ _ _ cX0 cX1 hv, sX _ hv, sX _ hv]; rfl
  have eg : ∀ i : Fin 2, subst ![f0, f1] (subst (fun _ : Unit => (X i : MvPowerSeries (Fin 2) R)) g) =
      subst (fun _ : Unit => ![f0, f1] i) g := by
    intro i
    rw [ss _ _ (fun _ => by simp) hv]
    congr 1; funext s; rw [sX _ hv]
  rw [ss _ _ h1f (fun _ => hE1), hfh, e2, ← ss _ _ (fun _ => hE2) hv, hgh,
    subst_ev F₃ _ _ _ (cc0 _ (fun _ => cX0) hg0) (cc0 _ (fun _ => cX1) hg0) hv, eg 0, eg 1, hX 0, hX 1]
  rfl

end Comp

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "𝒪" => integers K

/-- **The Vélu–Lubin link (hypothesis)**: the formal group `G` is, up to an isomorphism
`ψ : F_{W'} → G` with unit Lie derivative, the formal group of a good-reduction Weierstrass curve
`W'` over `𝒪`. For `G = F_W/H` Lubin's quotient by the canonical subgroup, `W'` should be (an integral
model of) Vélu's `W/H`. -/
structure VeluLubinLink (G : FormalGroup 𝒪) where
  W' : WeierstrassCurve 𝒪
  hΔ' : ‖((W'.Δ : 𝒪) : K)‖ = 1
  ψ : MvPowerSeries Unit 𝒪
  hψ : Hom (formalGroup W') G ψ
  hψu : ‖((coeff (Finsupp.single () 1) ψ : 𝒪) : K)‖ = 1

/-- the base change of `W'` to `K`. -/
noncomputable abbrev toK (W' : WeierstrassCurve 𝒪) : WeierstrassCurve K := W'.map (integers K).subtype

/-- `‖Δ(⟨u,0,0,0⟩ • W)‖ = ‖u‖^{-12} ‖Δ(W)‖`. -/
lemma norm_Δ_scale (W : WeierstrassCurve K) (u : Kˣ) :
    ‖((⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) • W).Δ‖ = ‖(u : K)‖⁻¹ ^ 12 * ‖W.Δ‖ := by
  rw [WeierstrassCurve.variableChange_Δ, norm_mul, norm_pow]
  simp

variable (p : ℕ) [Fact p.Prime] [CompleteSpace K] [IsAlgClosed K] [Algebra ℤ_[p] (integers K)]

/-- **Step 3 core**: for any `π̌ : G → F_W` with `‖Lie π̌‖ = ‖a‖` (e.g. from `elliptic_step2`) and a
Vélu–Lubin link for `G`. -/
theorem step3_of_link (hp5 : 5 ≤ p) (W : WeierstrassCurve 𝒪) (hε : 0 < ‖(p : K)‖)
    (hΔ : ‖((W.Δ : 𝒪) : K)‖ = 1) (ha : ‖hasse (formalGroup W) p‖ < 1)
    (hbreak : ‖(p : K)‖ ^ p < ‖hasse (formalGroup W) p‖ ^ (p + 1))
    (G : FormalGroup 𝒪) (πd : MvPowerSeries Unit 𝒪) (hπd : Hom G (formalGroup W) πd)
    (hlie : ‖coeff (Finsupp.single () 1) πd‖ = ‖hasse (formalGroup W) p‖)
    (link : VeluLubinLink G) :
    ∃ (W' : WeierstrassCurve 𝒪) (πd' : MvPowerSeries Unit 𝒪) (lam : Kˣ),
      ‖((W'.Δ : 𝒪) : K)‖ = 1 ∧ Hom (formalGroup W') (formalGroup W) πd' ∧
      (lam : K) = ((coeff (Finsupp.single () 1) πd' : 𝒪) : K) ∧
      ‖(lam : K)‖ = ‖hasse (formalGroup W) p‖ ∧ ‖(lam : K)‖ = ‖Ep p hp5 W‖ ∧
      -- `π̌'^* ω_W = λ ω_{W'}`
      pd () πd' * Ψ (formalGroup W') (T : MvPowerSeries Unit 𝒪) =
        Ψ (formalGroup W) πd' * C (coeff (Finsupp.single () 1) πd') ∧
      -- `W'' = (E', λ ω_{W'})`
      rescale (fun _ => (lam : K))
          (F ((⟨lam, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) • toK W')) =
        C (lam : K) * F (toK W') ∧
      ‖((⟨lam, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) • toK W').Δ‖ = ‖(lam : K)‖⁻¹ ^ 12 ∧
      -- `|Q(x)|^{12} = 1`
      ‖((Ep p hp5 W : 𝒪) : K)‖ ^ 12 *
          ‖((⟨lam, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) • toK W').Δ‖ /
          ‖((W.Δ : 𝒪) : K)‖ ^ p = 1 := by
  obtain ⟨W', hΔ', ψ, hψ, hψu⟩ := link
  have hπd' := hπd
  set πd' := subst (fun _ : Unit => ψ) πd
  have hH : Hom (formalGroup W') (formalGroup W) πd' := hom_comp hψ hπd'
  have hlin : coeff (Finsupp.single () 1) πd' =
      coeff (Finsupp.single () 1) πd * coeff (Finsupp.single () 1) ψ :=
    AtkinOBrien.Lie.coeff_one_comp πd ψ hπd'.1 hψ.1
  have hnorm : ‖((coeff (Finsupp.single () 1) πd' : 𝒪) : K)‖ = ‖hasse (formalGroup W) p‖ := by
    rw [hlin, Subring.coe_mul, norm_mul, hψu, mul_one]; exact hlie
  have hp2 := (Fact.out : p.Prime).two_le
  have hapos : 0 < ‖hasse (formalGroup W) p‖ :=
    lt_of_le_of_lt hε.le (norm_p_lt_of_break hp2 (norm_nonneg _) ha.le hbreak)
  have hne : ((coeff (Finsupp.single () 1) πd' : 𝒪) : K) ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; linarith
  set lam : Kˣ := Units.mk0 _ hne
  have hE := norm_hasse_eq_norm_Ep_of_break p hp5 W hbreak
  have hΔ'' : ‖((⟨lam, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) • toK W').Δ‖ =
      ‖(lam : K)‖⁻¹ ^ 12 := by
    rw [norm_Δ_scale, WeierstrassCurve.map_Δ]
    show _ * ‖((W'.Δ : 𝒪) : K)‖ = _
    rw [hΔ', mul_one]
  refine ⟨W', πd', lam, hΔ', hH, rfl, hnorm, hnorm.trans hE, ?_, rescale_F _ _, hΔ'', ?_⟩
  · exact hom_invariant _ _ πd' hH.1 hH.2
  · rw [hΔ'', hΔ, one_pow, div_one]
    show ‖((Ep p hp5 W : 𝒪) : K)‖ ^ 12 * ‖(lam : K)‖⁻¹ ^ 12 = 1
    have : ‖(lam : K)‖ = ‖((Ep p hp5 W : 𝒪) : K)‖ := hnorm.trans hE
    rw [this, ← mul_pow, mul_inv_cancel₀ (by rw [← this]; exact norm_ne_zero_iff.mpr lam.ne_zero),
      one_pow]

/-- **Step 3 of I2 at the formal-group level, conditional on the Vélu–Lubin link.** -/
theorem elliptic_step3 (hp5 : 5 ≤ p) (W : WeierstrassCurve 𝒪) (hε : 0 < ‖(p : K)‖)
    (hΔ : ‖((W.Δ : 𝒪) : K)‖ = 1) (ha : ‖hasse (formalGroup W) p‖ < 1)
    (hbreak : ‖(p : K)‖ ^ p < ‖hasse (formalGroup W) p‖ ^ (p + 1))
    (link : ∀ (G : FormalGroup 𝒪) (π πd : MvPowerSeries Unit 𝒪), IsHom (formalGroup W) G π →
      IsHom G (formalGroup W) πd → subst (fun _ : Unit => π) πd = FGL.nmul (formalGroup W) p →
      VeluLubinLink G) :
    ∃ (W' : WeierstrassCurve 𝒪) (πd' : MvPowerSeries Unit 𝒪) (lam : Kˣ),
      ‖((W'.Δ : 𝒪) : K)‖ = 1 ∧ Hom (formalGroup W') (formalGroup W) πd' ∧
      (lam : K) = ((coeff (Finsupp.single () 1) πd' : 𝒪) : K) ∧
      ‖(lam : K)‖ = ‖hasse (formalGroup W) p‖ ∧ ‖(lam : K)‖ = ‖Ep p hp5 W‖ ∧
      -- `π̌'^* ω_W = λ ω_{W'}`
      pd () πd' * Ψ (formalGroup W') (T : MvPowerSeries Unit 𝒪) =
        Ψ (formalGroup W) πd' * C (coeff (Finsupp.single () 1) πd') ∧
      -- `W'' = (E', λ ω_{W'})`
      rescale (fun _ => (lam : K))
          (F ((⟨lam, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) • toK W')) =
        C (lam : K) * F (toK W') ∧
      ‖((⟨lam, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) • toK W').Δ‖ = ‖(lam : K)‖⁻¹ ^ 12 ∧
      -- `|Q(x)|^{12} = 1`
      ‖((Ep p hp5 W : 𝒪) : K)‖ ^ 12 *
          ‖((⟨lam, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) • toK W').Δ‖ /
          ‖((W.Δ : 𝒪) : K)‖ ^ p = 1 := by
  obtain ⟨G, π, πd, hπ, hπd, hcomp, hlie⟩ := elliptic_step2 W p hp5 hε hΔ ha hbreak
  exact step3_of_link p hp5 W hε hΔ ha hbreak G πd hπd hlie (link G π πd hπ hπd hcomp)

end EllipticI2
