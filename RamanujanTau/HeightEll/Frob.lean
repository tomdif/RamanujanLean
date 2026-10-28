/-
# Frobenius factorisation of homomorphisms; `a = b = 0 ⇒ [p] ∈ R⟦T^{p³}⟧`

In characteristic `p`: a homomorphism `f : G₁ → G₂` of formal groups with `f'(0) = 0` has `f' = 0`, so
`f = f₁(T^p)` with `f₁ : G₁^{(p)} → G₂` again a homomorphism (`fr_hom`).
Applied to `g = gV` (`[p] = g(T^p)`, `g'(0) = a`) and then to `g₂ = fr g` (`g₂'(0) = b`, the
coefficient of `T^{p²}` in `[p]`): if `a = b = 0` then `[p]` only has monomials `T^m`, `p³ ∣ m`.
-/
import RamanujanTau.FormalGroupLayer.HeightTwo

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HeightEll
open MvPowerSeries FGL

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]

/-- the homomorphism property in the form used by `hom_invariant`. -/
def HomP (G₁ G₂ : FormalGroup R) (f : MvPowerSeries Unit R) : Prop :=
  subst (fun _ : Unit => ev G₁ (X 0 : MvPowerSeries (Fin 2) R) (X 1)) f =
    ev G₂ (subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) f)
      (subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) f)

variable (G₁ G₂ : FormalGroup R) {f : MvPowerSeries Unit R}

lemma pd_eq_zero_of_hom (hf : constantCoeff f = 0) (hhom : HomP G₁ G₂ f)
    (hlin : coeff (Finsupp.single () 1) f = 0) : pd () f = 0 := by
  have hG := hom_invariant G₁ G₂ f hf hhom
  rw [hlin, map_zero, mul_zero] at hG
  exact (isUnit_Ψ_T G₁).mul_right_eq_zero.mp (by rw [mul_comm]; exact hG)

lemma coeff_eq_zero_of_hom (hf : constantCoeff f = 0) (hhom : HomP G₁ G₂ f)
    (hlin : coeff (Finsupp.single () 1) f = 0) (k : ℕ) (hk : ¬ p ∣ k) :
    coeff (Finsupp.single () k) f = 0 :=
  coeff_eq_zero_of_pd p (hpR p) f (pd_eq_zero_of_hom G₁ G₂ hf hhom hlin) k hk

/-- `f₁ = Σ c_{pk} T^k`. -/
noncomputable def fr (f : MvPowerSeries Unit R) : MvPowerSeries Unit R := fun e => coeff (p • e) f

lemma coeff_fr (k : ℕ) : coeff (Finsupp.single () k) (fr p f) = coeff (Finsupp.single () (p * k)) f := by
  show coeff (p • Finsupp.single () k) f = _
  rw [Finsupp.smul_single, smul_eq_mul]

lemma eq_expand_fr (hf : constantCoeff f = 0) (hhom : HomP G₁ G₂ f)
    (hlin : coeff (Finsupp.single () 1) f = 0) : f = expand p (hp0 p) (fr p f) := by
  refine MvPowerSeries.ext fun m => ?_
  by_cases hm : p ∣ m ()
  · obtain ⟨k, hk⟩ := hm
    have : m = p • Finsupp.single () k := Finsupp.ext fun u => by cases u; simp [hk]
    rw [this, coeff_expand_smul]; rfl
  · rw [coeff_expand_of_not_dvd p (hp0 p) _ hm]
    have : m = Finsupp.single () (m ()) := Finsupp.ext fun u => by cases u; simp
    rw [this]; exact coeff_eq_zero_of_hom p G₁ G₂ hf hhom hlin _ hm

lemma cc_fr (hf : constantCoeff f = 0) (hhom : HomP G₁ G₂ f)
    (hlin : coeff (Finsupp.single () 1) f = 0) : constantCoeff (fr p f) = 0 := by
  have h := congrArg constantCoeff (eq_expand_fr p G₁ G₂ hf hhom hlin)
  rwa [constantCoeff_expand, hf, eq_comm] at h

/-- **`f₁ : G₁^{(p)} → G₂` is a homomorphism**. -/
theorem fr_hom (hf : constantCoeff f = 0) (hhom : HomP G₁ G₂ f)
    (hlin : coeff (Finsupp.single () 1) f = 0) : HomP (G₁.map (frobenius R p)) G₂ (fr p f) := by
  haveI : ExpChar R p := ExpChar.prime hp.out
  have X0 := ccX (R := R) (0 : Fin 2)
  have X1 := ccX (R := R) (1 : Fin 2)
  have hE : ∀ i, constantCoeff ((fun i => (X i : MvPowerSeries (Fin 2) R) ^ p) i) = 0 :=
    fun i => ccXp p i
  have hc := cc_fr p G₁ G₂ hf hhom hlin
  have key : ∀ {a : MvPowerSeries (Fin 2) R}, constantCoeff a = 0 →
      subst (fun _ : Unit => a) f = subst (fun _ : Unit => a ^ p) (fr p f) := by
    intro a ha
    conv_lhs => rw [eq_expand_fr p G₁ G₂ hf hhom hlin]
    rw [expand_eq_subst, ss _ _ (fun _ => ccXp p ()) (h1 ha)]
    congr 1; funext s
    rw [subst_pow (hs (h1 ha)), sX _ (h1 ha)]
  have hendo : subst (fun _ : Unit => ev G₁ (X 0 : MvPowerSeries (Fin 2) R) (X 1)) f =
      ev G₂ (subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) f)
        (subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) f) := hhom
  rw [key (cc_ev G₁ X0 X1), key X0, key X1, ev_X0X1] at hendo
  have hFp : G₁.toPowerSeries ^ p = expand p (hp0 p) (G₁.map (frobenius R p)).toPowerSeries := by
    rw [← map_frobenius_expand p (hp0 p), map_expand]; rfl
  rw [hFp] at hendo
  apply expand_inj p
  rw [expand_eq_subst, ss _ _ (h1 (cc_ev _ X0 X1)) hE, expand_eq_subst]
  rw [subst_ev G₂ _ _ _ (cc0 _ (h1 X0) hc) (cc0 _ (h1 X1) hc) hE,
    ss _ _ (h1 X0) hE, ss _ _ (h1 X1) hE]
  have e : (fun _ : Unit => subst (fun i => (X i : MvPowerSeries (Fin 2) R) ^ p)
      (ev (G₁.map (frobenius R p)) (X 0 : MvPowerSeries (Fin 2) R) (X 1))) =
      fun _ => expand p (hp0 p) (G₁.map (frobenius R p)).toPowerSeries := by
    funext s; rw [ev_X0X1, expand_eq_subst]
  rw [e, sX _ hE, sX _ hE]
  exact hendo

variable (F : FormalGroup R) [F.IsComm]

/-- **height ≥ 3 shape**: if `a = 0` and the coefficient `b` of `T^{p²}` in `[p]` vanishes, then
`[p]` has no monomial `T^m` with `p³ ∤ m`. -/
theorem coeff_nmul_eq_zero_of_ab (ha : aH p F = 0)
    (hb : coeff (Finsupp.single () (p ^ 2)) (nmul F p) = 0) (m : ℕ) (hm : ¬ p ^ 3 ∣ m) :
    coeff (Finsupp.single () m) (nmul F p) = 0 := by
  have hg : HomP (Fp p F) F (gV p F) := gV_hom p F
  have hgc := cc_gV p F
  have hgl : coeff (Finsupp.single () 1) (gV p F) = 0 := by rw [coeff_one_gV, ha]
  have hg2 := fr_hom p (Fp p F) F hgc hg hgl
  have hg2c := cc_fr p (Fp p F) F hgc hg hgl
  have hg2l : coeff (Finsupp.single () 1) (fr p (gV p F)) = 0 := by
    rw [coeff_fr, mul_one]
    show coeff (p • Finsupp.single () p) (nmul F p) = 0
    rw [Finsupp.smul_single, smul_eq_mul, ← pow_two]; exact hb
  by_cases h1 : p ∣ m
  · obtain ⟨m₁, rfl⟩ := h1
    have e1 : coeff (Finsupp.single () (p * m₁)) (nmul F p) = coeff (Finsupp.single () m₁) (gV p F) := by
      show _ = coeff (p • Finsupp.single () m₁) (nmul F p)
      rw [Finsupp.smul_single, smul_eq_mul]
    rw [e1]
    by_cases h2 : p ∣ m₁
    · obtain ⟨m₂, rfl⟩ := h2
      have e2 : coeff (Finsupp.single () (p * m₂)) (gV p F) = coeff (Finsupp.single () m₂) (fr p (gV p F)) :=
        (coeff_fr p m₂).symm
      rw [e2]
      apply coeff_eq_zero_of_hom p _ F hg2c hg2 hg2l
      rintro ⟨m₃, rfl⟩
      exact hm ⟨m₃, by ring⟩
    · exact coeff_eq_zero_of_hom p (Fp p F) F hgc hg hgl m₁ h2
  · exact coeff_nmul_eq_zero F p (hpR p) m h1

end HeightEll
