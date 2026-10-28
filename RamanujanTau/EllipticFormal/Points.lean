/-
# Formal points as points of `W` over a fraction field, and the chord addition

For `(z, w)` with `G(z, w) = 0`, `w ≠ 0` over a field, `(x, y) = (z/w, -1/w)` is a point of `W`.
The main field-level result `chord_add`: if `(zᵢ, wᵢ)` (`i = 1, 2`) lie on the line `w = l z + n`
and `z₃` is the third root (`lead·(z₁+z₂+z₃) + B = 0`), then in Mathlib's group law
  `P(z₁, w₁) + P(z₂, w₂) = P(z₃ e, w₃ e)`,  `e = 1/(a₁ z₃ + a₃ w₃ - 1)`.
Then for a domain `R` with `2 ≠ 0`, formal points `t ∈ R⟦σ⟧` give points of `W` over
`Frac R⟦σ⟧`, and `P(s) + P(t) = P(F(s, t))` (`P_add`).
-/
import RamanujanTau.EllipticFormal.Chord

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EllipticFormal

open MvPowerSeries WeierstrassCurve.Affine

open scoped Classical

/-! ## Field level -/

section Field
variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K)

lemma equation_zw {z w : K} (hw : w ≠ 0) (hG : G W z w = 0) :
    W.toAffine.Equation (z / w) (-1 / w) := by
  rw [equation_iff']
  have : (-1 / w) ^ 2 + W.a₁ * (z / w) * (-1 / w) + W.a₃ * (-1 / w) -
      ((z / w) ^ 3 + W.a₂ * (z / w) ^ 2 + W.a₄ * (z / w) + W.a₆) = -G W z w / w ^ 3 := by
    simp only [G]; field_simp; ring
  rw [this, hG]; simp

lemma nonsingular_zw {z w : K} (hw : w ≠ 0) (hG : G W z w = 0)
    (hnd : -2 + W.a₁ * z + W.a₃ * w ≠ 0) : W.toAffine.Nonsingular (z / w) (-1 / w) := by
  rw [nonsingular_iff']
  refine ⟨equation_zw W hw hG, Or.inr ?_⟩
  have : 2 * (-1 / w) + W.a₁ * (z / w) + W.a₃ = (-2 + W.a₁ * z + W.a₃ * w) / w := by
    field_simp
  rw [this]; exact div_ne_zero hnd hw

/-- the point `(z/w, -1/w)`. -/
noncomputable def pt (z w : K) (hw : w ≠ 0) (hG : G W z w = 0) (hnd : -2 + W.a₁ * z + W.a₃ * w ≠ 0) :
    W.toAffine.Point :=
  .some (z / w) (-1 / w) (nonsingular_zw W hw hG hnd)

lemma pt_eq_pt {z w z' w' : K} (hz : z = z') (hw' : w = w') (hw : w ≠ 0) (hG : G W z w = 0)
    (hnd : -2 + W.a₁ * z + W.a₃ * w ≠ 0) (hw₂ : w' ≠ 0) (hG₂ : G W z' w' = 0)
    (hnd₂ : -2 + W.a₁ * z' + W.a₃ * w' ≠ 0) :
    pt W z w hw hG hnd = pt W z' w' hw₂ hG₂ hnd₂ := by
  subst hz hw'; rfl

/-- two points of `(z, w)`-form with the same `x`: equal, or opposite. -/
lemma x_eq_cases {z w z' w' : K} (hw : w ≠ 0) (hG : G W z w = 0) (hw' : w' ≠ 0) (hG' : G W z' w' = 0)
    (hx : z / w = z' / w') : (z = z' ∧ w = w') ∨ z * (W.a₁ * z' + W.a₃ * w' - 1) = z' := by
  have hx' : z * w' = z' * w := by rw [div_eq_div_iff hw hw'] at hx; exact hx
  rcases Y_eq_of_X_eq (equation_zw W hw hG) (equation_zw W hw' hG') hx with hy | hy
  · left
    have hww : w = w' := by field_simp at hy; linear_combination hy
    subst hww
    exact ⟨mul_right_cancel₀ hw hx', rfl⟩
  · right
    rw [negY] at hy
    field_simp at hy
    have : w * (z * (W.a₁ * z' + W.a₃ * w' - 1) - z') = 0 := by
      linear_combination z * hy + hx'
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hw)

lemma pt_inj {z w z' w' : K} {hw : w ≠ 0} {hG : G W z w = 0} {hnd : -2 + W.a₁ * z + W.a₃ * w ≠ 0}
    {hw₂ : w' ≠ 0} {hG₂ : G W z' w' = 0} {hnd₂ : -2 + W.a₁ * z' + W.a₃ * w' ≠ 0}
    (h : pt W z w hw hG hnd = pt W z' w' hw₂ hG₂ hnd₂) : z = z' ∧ w = w' := by
  simp only [pt, Point.some.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hww : w = w' := by
    have := h2; field_simp at this; linear_combination this
  subst hww
  refine ⟨?_, rfl⟩
  field_simp at h1; exact h1

/-- **the chord addition law** over a field. -/
theorem chord_add {z₁ z₂ z₃ l n e : K}
    (h₁ : G W z₁ (l * z₁ + n) = 0) (h₂ : G W z₂ (l * z₂ + n) = 0)
    (hw₁ : l * z₁ + n ≠ 0) (hw₂ : l * z₂ + n ≠ 0)
    (hnd₁ : -2 + W.a₁ * z₁ + W.a₃ * (l * z₁ + n) ≠ 0) (hnd₂ : -2 + W.a₁ * z₂ + W.a₃ * (l * z₂ + n) ≠ 0)
    (hx : z₁ / (l * z₁ + n) ≠ z₂ / (l * z₂ + n)) (hlead : lead W l ≠ 0)
    (h₃ : lead W l * (z₁ + z₂ + z₃) + B W l n = 0) (hw₃ : l * z₃ + n ≠ 0)
    (he : (W.a₁ * z₃ + W.a₃ * (l * z₃ + n) - 1) * e = 1)
    (hwF : (l * z₃ + n) * e ≠ 0) (hGF : G W (z₃ * e) ((l * z₃ + n) * e) = 0)
    (hndF : -2 + W.a₁ * (z₃ * e) + W.a₃ * ((l * z₃ + n) * e) ≠ 0) :
    pt W z₁ (l * z₁ + n) hw₁ h₁ hnd₁ + pt W z₂ (l * z₂ + n) hw₂ h₂ hnd₂ =
      pt W (z₃ * e) ((l * z₃ + n) * e) hwF hGF hndF := by
  set w₁ := l * z₁ + n with hw₁d
  set w₂ := l * z₂ + n with hw₂d
  set w₃ := l * z₃ + n with hw₃d
  have hz : z₁ ≠ z₂ := by rintro rfl; exact hx rfl
  have hn : n ≠ 0 := by
    rintro rfl
    have hl : l ≠ 0 := by rintro rfl; apply hw₁; rw [hw₁d]; ring
    have hz₁ : z₁ ≠ 0 := by rintro rfl; apply hw₁; rw [hw₁d]; ring
    have hz₂ : z₂ ≠ 0 := by rintro rfl; apply hw₂; rw [hw₂d]; ring
    apply hx; rw [hw₁d, hw₂d]; field_simp; ring
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  -- the line through the points in `(x, y)`-coordinates: `y = (l/n) x - 1/n`
  have line : ∀ {z w : K}, w = l * z + n → w ≠ 0 → -1 / w = l / n * (z / w) - 1 / n := by
    intro z w hw hw0; rw [hw] at hw0 ⊢; field_simp; ring
  -- Vieta
  rw [G_line] at h₁ h₂
  have hQ : lead W l * (z₁ ^ 2 + z₁ * z₂ + z₂ ^ 2) + B W l n * (z₁ + z₂) + Cz W l n = 0 := by
    have : (z₁ - z₂) * (lead W l * (z₁ ^ 2 + z₁ * z₂ + z₂ ^ 2) + B W l n * (z₁ + z₂) + Cz W l n) = 0 := by
      linear_combination h₁ - h₂
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hz)
  have E2 : lead W l * (z₁ * z₂ + z₁ * z₃ + z₂ * z₃) - Cz W l n = 0 := by
    linear_combination (z₁ + z₂) * h₃ - hQ
  have E3 : lead W l * (z₁ * z₂ * z₃) + Dz W n = 0 := by
    linear_combination h₁ - z₁ ^ 2 * h₃ + z₁ * E2
  have hN : (l ^ 2 + W.a₁ * l * n - W.a₂ * n ^ 2) * (w₁ * w₂ * w₃) -
      n ^ 2 * (z₁ * w₂ * w₃ + z₂ * w₁ * w₃ + z₃ * w₁ * w₂) = 0 := by
    have : lead W l * ((l ^ 2 + W.a₁ * l * n - W.a₂ * n ^ 2) * (w₁ * w₂ * w₃) -
        n ^ 2 * (z₁ * w₂ * w₃ + z₂ * w₁ * w₃ + z₃ * w₁ * w₂)) = 0 := by
      rw [hw₁d, hw₂d, hw₃d]
      linear_combination (norm := (simp only [lead, B, Cz, Dz]; ring))
        ((l ^ 2 + W.a₁ * l * n - W.a₂ * n ^ 2) * l * n ^ 2 - n ^ 4) * h₃ +
        ((l ^ 2 + W.a₁ * l * n - W.a₂ * n ^ 2) * l ^ 2 * n - 2 * l * n ^ 3) * E2 +
        ((l ^ 2 + W.a₁ * l * n - W.a₂ * n ^ 2) * l ^ 3 - 3 * l ^ 2 * n ^ 2) * E3
    exact (mul_eq_zero.1 this).resolve_left hlead
  have hX : (l / n) ^ 2 + W.a₁ * (l / n) - W.a₂ - z₁ / w₁ - z₂ / w₂ = z₃ / w₃ := by
    rw [← sub_eq_zero]
    have : (l / n) ^ 2 + W.a₁ * (l / n) - W.a₂ - z₁ / w₁ - z₂ / w₂ - z₃ / w₃ =
        ((l ^ 2 + W.a₁ * l * n - W.a₂ * n ^ 2) * (w₁ * w₂ * w₃) -
          n ^ 2 * (z₁ * w₂ * w₃ + z₂ * w₁ * w₃ + z₃ * w₁ * w₂)) / (n ^ 2 * (w₁ * w₂ * w₃)) := by
      field_simp
      ring
    rw [this, hN, zero_div]
  -- the slope
  have hslope : W.toAffine.slope (z₁ / w₁) (z₂ / w₂) (-1 / w₁) (-1 / w₂) = l / n := by
    rw [slope_of_X_ne hx, div_eq_iff (sub_ne_zero.2 hx), line hw₁d hw₁, line hw₂d hw₂]; ring
  have hxy : ¬(z₁ / w₁ = z₂ / w₂ ∧ -1 / w₁ = W.toAffine.negY (z₂ / w₂) (-1 / w₂)) :=
    fun h => hx h.1
  simp only [pt]
  rw [Point.add_some hxy, Point.some.injEq]
  have hx₃ : z₃ * e / (w₃ * e) = z₃ / w₃ := by rw [mul_div_mul_right _ _ he0]
  refine ⟨?_, ?_⟩
  · rw [addX, hslope, hx₃, ← hX]
  · rw [addY, negAddY, addX, hslope, hX, negY]
    have hd : W.a₁ * z₃ + W.a₃ * w₃ - 1 ≠ 0 := by rintro h; rw [h, zero_mul] at he; simp at he
    have he' : e = 1 / (W.a₁ * z₃ + W.a₃ * w₃ - 1) := by
      rw [eq_div_iff hd]; linear_combination he
    rw [he']
    simp only [hw₁d, hw₃d] at hd hw₁ hw₃ ⊢
    field_simp
    ring

end Field

/-! ## Formal points over `Frac R⟦σ⟧` -/

/-- the curve over `K = Frac R⟦σ⟧`. -/
noncomputable abbrev WK {R : Type*} [CommRing R] (W : WeierstrassCurve R) (σ : Type*) :
    WeierstrassCurve (FractionRing (MvPowerSeries σ R)) :=
  (WM W σ).map (algebraMap (MvPowerSeries σ R) (FractionRing (MvPowerSeries σ R)))

section Formal
variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)
variable {σ : Type*} [Fintype σ]

instance instIsDomainMvPowerSeries : IsDomain (MvPowerSeries σ R) := NoZeroDivisors.to_isDomain _

local notation "A" => MvPowerSeries σ R
local notation "K" => FractionRing (MvPowerSeries σ R)


lemma ι_inj {a b : A} (h : algebraMap A K a = algebraMap A K b) : a = b :=
  IsFractionRing.injective A K h

lemma ι_ne {a : A} (h : a ≠ 0) : algebraMap A K a ≠ 0 := fun h' =>
  h (ι_inj (by rw [h', map_zero]))

lemma G_ι (z w : A) : algebraMap A K (G (WM W σ) z w) = G (WK W σ) (algebraMap A K z) (algebraMap A K w) :=
  map_G _ _ _ _

lemma nd_ι (h2 : (2 : R) ≠ 0) {z w : A} (hz : constantCoeff z = 0) (hw : constantCoeff w = 0) :
    -2 + (WK W σ).a₁ * algebraMap A K z + (WK W σ).a₃ * algebraMap A K w ≠ 0 := by
  have : -2 + (WK W σ).a₁ * algebraMap A K z + (WK W σ).a₃ * algebraMap A K w =
      algebraMap A K (-2 + (WM W σ).a₁ * z + (WM W σ).a₃ * w) := by simp [map_ofNat]
  rw [this]
  apply ι_ne
  intro h
  have := congrArg constantCoeff h
  simp [hz, hw, map_ofNat] at this
  exact h2 this

/-- the formal point `t` as a point of `W(K)`. -/
noncomputable def P (h2 : (2 : R) ≠ 0) (t : A) (ht : constantCoeff t = 0) (h0 : t ≠ 0) :
    (WK W σ).toAffine.Point :=
  pt (WK W σ) (algebraMap A K t) (algebraMap A K (wt W t)) (ι_ne (wt_ne_zero ht h0))
    (by rw [← G_ι, G_wt ht, map_zero]) (nd_ι W h2 ht (cc_wt ht))

lemma P_inj (h2 : (2 : R) ≠ 0) {s t : A} {hs : constantCoeff s = 0} {ht : constantCoeff t = 0}
    {hs0 : s ≠ 0} {ht0 : t ≠ 0} (h : P W h2 s hs hs0 = P W h2 t ht ht0) : s = t :=
  ι_inj (pt_inj _ h).1

variable [DecidableEq σ]

lemma lin_ne_zero {t : A} {i : σ} (h : coeff (Finsupp.single i 1) t = 1) : t ≠ 0 := by
  rintro rfl; simp at h

/-- the substitution `![s, t]` as a ring hom. -/
noncomputable abbrev φ (s t : A) (hs : constantCoeff s = 0) (ht : constantCoeff t = 0) :
    MvPowerSeries (Fin 2) R →ₐ[R] A :=
  substAlgHom (FGL.hs (FGL.cc_vec2 hs ht))

lemma φ_apply (s t : A) (hs : constantCoeff s = 0) (ht : constantCoeff t = 0) (f : MvPowerSeries (Fin 2) R) :
    φ s t hs ht f = subst ![s, t] f := by
  rw [coe_substAlgHom]

lemma lead_map {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) (W : WeierstrassCurve S) (l : S) :
    f (lead W l) = lead (W.map f) (f l) := by simp [lead]

lemma B_map {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) (W : WeierstrassCurve S) (l n : S) :
    f (B W l n) = B (W.map f) (f l) (f n) := by simp [B, map_ofNat]

local notation "ι" => algebraMap (MvPowerSeries σ R) (FractionRing (MvPowerSeries σ R))

/-- **the formal group law is the group law**: `P(s) + P(t) = P(F(s, t))`. -/
theorem P_add (h2 : (2 : R) ≠ 0) {s t : A} (hs : constantCoeff s = 0) (ht : constantCoeff t = 0)
    {i : σ} (hsi : coeff (Finsupp.single i 1) s = 1) (hti : coeff (Finsupp.single i 1) t = 0)
    (ht0 : t ≠ 0) :
    P W h2 s hs (lin_ne_zero hsi) + P W h2 t ht ht0 =
      P W h2 (subst ![s, t] (F W)) (FGL.cc0 _ (FGL.cc_vec2 hs ht) (cc_F W))
        (lin_ne_zero (i := i) (by rw [lin_subst2 _ _ _ hs ht, lin_F, lin_F, hsi, hti]; ring)) := by
  set f := (φ s t hs ht : MvPowerSeries (Fin 2) R →+* A) with hf
  have hv := FGL.cc_vec2 hs ht
  have fX0 : f (X 0) = s := by rw [hf, RingHom.coe_coe, φ_apply]; exact FGL.sX _ hv 0
  have fX1 : f (X 1) = t := by rw [hf, RingHom.coe_coe, φ_apply]; exact FGL.sX _ hv 1
  have fwt : ∀ j : Fin 2, f (wt W (X j)) = wt W (f (X j)) := by
    intro j
    rw [hf, RingHom.coe_coe, φ_apply, φ_apply, subst_wt (by simp) _ hv]
  have fWM : (WM W (Fin 2)).map f = WM W σ := WM_map_eq _
  have fcc : ∀ g : MvPowerSeries (Fin 2) R, constantCoeff g = 0 → constantCoeff (f g) = 0 := by
    intro g hg; rw [hf, RingHom.coe_coe, φ_apply]; exact FGL.cc0 _ hv hg
  set l := f (lam W)
  set n := f (nu W)
  set z₃ := f (z3 W)
  set e := f (dInv W)
  have hws : wt W s = l * s + n := by
    rw [← fX0, ← fwt, nu_eq_zero, map_add, map_mul]
  have hwt : wt W t = l * t + n := by
    rw [← fX1, ← fwt, nu_eq_one, map_add, map_mul]
  have hst : s ≠ t := by rintro rfl; rw [hsi] at hti; exact one_ne_zero hti
  have h3 : lead (WM W σ) l * (s + t + z₃) + B (WM W σ) l n = 0 := by
    have := congrArg f (z3_spec W)
    rwa [map_add, map_mul, map_add, map_add, lead_map, B_map, fWM, fX0, fX1, map_zero] at this
  have hlead : lead (WM W σ) l * f (leadInv W) = 1 := by
    have := congrArg f (lead_mul_leadInv W)
    rwa [map_mul, lead_map, fWM, map_one] at this
  have he : ((WM W σ).a₁ * z₃ + (WM W σ).a₃ * (l * z₃ + n) - 1) * e = 1 := by
    have := congrArg f (dd_mul_dInv W)
    rw [map_mul, map_one, dd, w3] at this
    simpa [← fWM] using this
  have hFst : subst ![s, t] (F W) = z₃ * e := by
    rw [← φ_apply s t hs ht, ← RingHom.coe_coe, ← hf, F, map_mul]
  have hG3 : G (WM W σ) z₃ (l * z₃ + n) = 0 :=
    G_third _ (hws ▸ G_wt hs) (hwt ▸ G_wt ht) hst h3
  have hGF : G (WM W σ) (z₃ * e) ((l * z₃ + n) * e) = 0 := by
    rw [G_neg _ _ _ _ he, hG3, mul_zero]
  have hcz : constantCoeff z₃ = 0 := fcc _ (cc_z3 W)
  have hcl : constantCoeff l = 0 := fcc _ (cc_lam W)
  have hcn : constantCoeff n = 0 := fcc _ (cc_nu W)
  have hwF : wt W (z₃ * e) = (l * z₃ + n) * e := by
    have hc : constantCoeff (z₃ * e) = 0 := by simp [hcz]
    exact G_unique _ hc (cc_wt hc) (by simp [hcz, hcl, hcn]) (G_wt hc) hGF
  have hcF : constantCoeff (z₃ * e) = 0 := by simp [hcz]
  have hFne : z₃ * e ≠ 0 := by
    rw [← hFst]
    exact lin_ne_zero (i := i) (by rw [lin_subst2 _ _ _ hs ht, lin_F, lin_F, hsi, hti]; ring)
  have hw3ne : l * z₃ + n ≠ 0 := by
    intro h; apply wt_ne_zero (W := W) hcF hFne; rw [hwF, h, zero_mul]
  -- the data over `K`
  have hGs : G (WK W σ) (ι s) (ι l * ι s + ι n) = 0 := by
    have := G_wt (W := W) hs; rw [hws] at this
    have := congrArg ι this; rw [G_ι, map_zero] at this; simpa using this
  have hGt : G (WK W σ) (ι t) (ι l * ι t + ι n) = 0 := by
    have := G_wt (W := W) ht; rw [hwt] at this
    have := congrArg ι this; rw [G_ι, map_zero] at this; simpa using this
  have hwsK : ι (wt W s) = ι l * ι s + ι n := by rw [hws]; simp
  have hwtK : ι (wt W t) = ι l * ι t + ι n := by rw [hwt]; simp
  have hwsne : ι l * ι s + ι n ≠ 0 := hwsK ▸ ι_ne (wt_ne_zero hs (lin_ne_zero hsi))
  have hwtne : ι l * ι t + ι n ≠ 0 := hwtK ▸ ι_ne (wt_ne_zero ht ht0)
  have hnds : -2 + (WK W σ).a₁ * ι s + (WK W σ).a₃ * (ι l * ι s + ι n) ≠ 0 := by
    have := nd_ι W h2 hs (cc_wt (W := W) hs); rwa [hwsK] at this
  have hndt : -2 + (WK W σ).a₁ * ι t + (WK W σ).a₃ * (ι l * ι t + ι n) ≠ 0 := by
    have := nd_ι W h2 ht (cc_wt (W := W) ht); rwa [hwtK] at this
  have hx : ι s / (ι l * ι s + ι n) ≠ ι t / (ι l * ι t + ι n) := by
    intro hxe
    rcases x_eq_cases (WK W σ) hwsne hGs hwtne hGt hxe with ⟨h1, -⟩ | h1
    · exact hst (ι_inj h1)
    · have h1' : s * ((WM W σ).a₁ * t + (WM W σ).a₃ * (l * t + n) - 1) = t :=
        ι_inj (by simpa using h1)
      have := congrArg (coeff (Finsupp.single i 1)) h1'
      rw [lin_mul, hsi, hti, hs] at this
      simp [ht, hcl, hcn] at this
  have hleadK : lead (WK W σ) (ι l) ≠ 0 := by
    rw [← lead_map]; intro h
    have := congrArg ι hlead; rw [map_mul, h, zero_mul, map_one] at this; exact zero_ne_one this
  have h3K : lead (WK W σ) (ι l) * (ι s + ι t + ι z₃) + B (WK W σ) (ι l) (ι n) = 0 := by
    have := congrArg ι h3
    rw [map_add, map_mul, lead_map, B_map, map_add, map_add, map_zero] at this; exact this
  have hw3K : ι l * ι z₃ + ι n ≠ 0 := by have := ι_ne hw3ne; simpa using this
  have heK : ((WK W σ).a₁ * ι z₃ + (WK W σ).a₃ * (ι l * ι z₃ + ι n) - 1) * ι e = 1 := by
    have := congrArg ι he; simpa using this
  have hwFK : (ι l * ι z₃ + ι n) * ι e ≠ 0 := by
    have := ι_ne (wt_ne_zero (W := W) hcF hFne); rw [hwF, map_mul, map_add, map_mul] at this
    exact this
  have hGFK : G (WK W σ) (ι z₃ * ι e) ((ι l * ι z₃ + ι n) * ι e) = 0 := by
    have := congrArg ι hGF; rw [G_ι, map_zero] at this; simpa using this
  have hndFK : -2 + (WK W σ).a₁ * (ι z₃ * ι e) + (WK W σ).a₃ * ((ι l * ι z₃ + ι n) * ι e) ≠ 0 := by
    have := nd_ι W h2 (z := z₃ * e) (w := (l * z₃ + n) * e) hcF (by simp [hcz, hcl, hcn])
    simpa using this
  have key := chord_add (WK W σ) hGs hGt hwsne hwtne hnds hndt hx hleadK h3K hw3K heK hwFK hGFK hndFK
  simp only [P]
  rw [pt_eq_pt (WK W σ) rfl hwsK _ _ _ hwsne hGs hnds, pt_eq_pt (WK W σ) rfl hwtK _ _ _ hwtne hGt hndt,
    key]
  exact pt_eq_pt _ (by rw [hFst]; simp) (by rw [hFst, hwF]; simp) _ _ _ _ _ _

end Formal

end EllipticFormal
