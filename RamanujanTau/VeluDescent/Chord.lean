/-
# The generic point plus a point of `𝔪`, in `L = Frac K⟦z⟧`

For `h ∈ 𝔪`, `h ≠ 0`, evaluate the two-variable formal chord law at `(z₁, z₂) = (z, h)`: the ring hom
`fL h : 𝒪⟦z₁,z₂⟧ → L`, `z₁ ↦ z`, `z₂ ↦ h`. By `chord_add_hom`, the generic point
`P(z) = (z/w(z), -1/w(z))` plus `Pt h = (h/w(h), -1/w(h))` is `(F(z,h)/w(F(z,h)), -1/w(F(z,h)))`.
Main result (`yc_chord`): the `y`-coordinate of `P(z) + Pt h` given by the chord formula is
`-1/w(F(z,h))`.
-/
import RamanujanTau.VeluDescent.Translates

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VeluDescent
open MvPowerSeries EllipticFormal VeluLubin

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K]

local notation "𝒪" => CanonicalIsogeny.integers K
local notation "jK" => Subring.subtype (CanonicalIsogeny.integers K)
local notation "LL" => FractionRing (MvPowerSeries Unit K)
local notation "iL" => algebraMap (MvPowerSeries Unit K) (FractionRing (MvPowerSeries Unit K))

variable {a b : ↥(CanonicalIsogeny.integers K)}

/-- `z₁ ↦ z, z₂ ↦ h`. -/
noncomputable def vec2 (h : 𝒪) : Fin 2 → MvPowerSeries Unit 𝒪 := ![X (), C h]

lemma adm_vec2 {h : 𝒪} (hh : IsTopologicallyNilpotent h) : Lubin.Adm (vec2 h) :=
  Lubin.adm2 (Lubin.tn_X ()) (Lubin.tn_C hh)

noncomputable def ev2 {h : 𝒪} (hh : IsTopologicallyNilpotent h) :
    MvPowerSeries (Fin 2) 𝒪 →+* MvPowerSeries Unit 𝒪 :=
  Lubin.EH (adm_vec2 hh)

/-- `z₁ ↦ z, z₂ ↦ h`, into `L`. -/
noncomputable def fL {h : 𝒪} (hh : IsTopologicallyNilpotent h) : MvPowerSeries (Fin 2) 𝒪 →+* LL :=
  RingHom.comp iL ((MvPowerSeries.map jK).comp (ev2 hh))

section
variable {h : ↥(CanonicalIsogeny.integers K)} (hh : IsTopologicallyNilpotent h)

lemma ev2_apply (g : MvPowerSeries (Fin 2) 𝒪) :
    ev2 hh g = Lubin.E (vec2 h) g := by rw [ev2, Lubin.EH_apply]

lemma ev2_X0 : ev2 hh (X 0) = X () := by rw [ev2_apply, Lubin.E_X]; rfl
lemma ev2_X1 : ev2 hh (X 1) = C h := by rw [ev2_apply, Lubin.E_X]; rfl
lemma ev2_C (r : 𝒪) : ev2 hh (C r) = C r := by rw [ev2_apply, Lubin.E_C]

lemma ev2_F : ev2 hh (F (shortO a b)) = Fh a b h := by
  rw [ev2_apply]; rfl

lemma ev2_wt {g : MvPowerSeries (Fin 2) 𝒪} (hg : constantCoeff g = 0) :
    ev2 hh (wt (shortO a b) g) =
      Lubin.E (fun _ : Unit => ev2 hh g) (w (shortO a b) : MvPowerSeries Unit 𝒪) := by
  rw [ev2_apply, wt, PowerSeries.subst_def, Lubin.E_subst (fun _ => hg) (adm_vec2 hh)]
  congr 1; funext u; rw [ev2_apply]

lemma ev2_w0 : ev2 hh (wt (shortO a b) (X 0)) = (w (shortO a b) : MvPowerSeries Unit 𝒪) := by
  rw [ev2_wt hh (by simp), ev2_X0, X_fun, Lubin.E_X_self]

lemma ev2_w1 : ev2 hh (wt (shortO a b) (X 1)) = C (wz a b h) := by
  rw [ev2_wt hh (by simp), ev2_X1, wz]
  exact Lubin.E_const (x := fun _ : Unit => h) (fun _ => hh) _

lemma ev2_wF : ev2 hh (wt (shortO a b) (F (shortO a b))) = wh a b h := by
  rw [ev2_wt hh (cc_F _), ev2_F]; rfl

lemma fL_apply (g : MvPowerSeries (Fin 2) 𝒪) :
    fL hh g = iL (MvPowerSeries.map jK (ev2 hh g)) := rfl

lemma fL_C (r : 𝒪) : fL hh (C r) = (jj.comp jK) r := by
  rw [fL_apply, ev2_C, map_C]; rfl

end

/-! ### Base change identities -/

lemma map_w_short : MvPowerSeries.map jK (w (shortO a b) : MvPowerSeries Unit 𝒪) =
    ww (a : K) (b : K) := by
  show PowerSeries.map jK (w (shortO a b)) = w (Velu.short (a : K) (b : K))
  rw [map_w, show (shortO a b).map jK = Velu.short (a : K) (b : K) from toK_shortO a b]

lemma map_shortO_L : (shortO a b).map (jj.comp jK) =
    (Velu.short (jj (a : K)) (jj (b : K)) : WeierstrassCurve LL) := by
  ext <;> simp [shortO, Velu.short]

/-- the chord formula for the `y`-coordinate of a sum. -/
noncomputable def chordY (x0 y0 xq yq : LL) : LL :=
  -(((y0 - yq) / (x0 - xq)) * ((((y0 - yq) / (x0 - xq)) ^ 2 - x0 - xq) - x0) + y0)

lemma iL_inj {u v : MvPowerSeries Unit K} (h : iL u = iL v) : u = v := IsFractionRing.injective _ _ h

lemma jj_inj {c d : K} (h : (jj c : LL) = jj d) : c = d := by
  have := iL_inj h
  have := congrArg constantCoeff this
  simpa using this

lemma jj_ne {c : K} (h : c ≠ 0) : (jj c : LL) ≠ 0 := fun h' => h (jj_inj (h'.trans (map_zero _).symm))

lemma two_ne_LL : (2 : LL) ≠ 0 := by
  have : (jj (2 : K) : LL) = 2 := map_ofNat _ 2
  rw [← this]; exact jj_ne two_ne_zero

lemma xc_Pt {h : 𝒪} (h0 : h ≠ 0) (hh : ‖(h : K)‖ < 1) :
    Velu.xc (Pt a b h) = (h : K) / (wz a b h : K) := by
  rw [Pt_eq a b h0 hh, pt]; rfl

lemma yc_Pt {h : 𝒪} (h0 : h ≠ 0) (hh : ‖(h : K)‖ < 1) :
    Velu.yc (Pt a b h) = -1 / (wz a b h : K) := by
  rw [Pt_eq a b h0 hh, pt]; rfl

lemma cc_wh {h : 𝒪} (hh : IsTopologicallyNilpotent h) : constantCoeff (wh a b h) = wz a b h := by
  rw [wh, Lubin.cc_E (adm_Fh hh)]
  simp only [cc_Fh hh]; rfl

lemma map_wh_ne {h : 𝒪} (h0 : h ≠ 0) (hh : ‖(h : K)‖ < 1) :
    iL (MvPowerSeries.map jK (wh a b h)) ≠ 0 := by
  intro e
  have e' := iL_inj (e.trans (map_zero iL).symm)
  have := congrArg constantCoeff e'
  rw [constantCoeff_map, cc_wh (tn_of_norm hh), map_zero] at this
  exact wz_ne_zero a b hh h0 this

lemma addY_short [DecidableEq LL] (W : WeierstrassCurve LL) (h1 : W.a₁ = 0) (h3 : W.a₃ = 0) (h2 : W.a₂ = 0)
    {x1 x2 y1 y2 : LL} (hx : x1 ≠ x2) :
    W.toAffine.addY x1 x2 y1 (W.toAffine.slope x1 x2 y1 y2) = chordY x1 y1 x2 y2 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, chordY,
    WeierstrassCurve.toAffine]
  rw [h1, h2, h3]
  ring

/-- **the `y`-coordinate of `P(z) + Pt h`** is `-1/w(F(z,h))`. -/
theorem yc_chord {h : 𝒪} (h0 : h ≠ 0) (hh : ‖(h : K)‖ < 1) :
    -1 / iL (MvPowerSeries.map jK (wh a b h)) =
      chordY (xL (a : K) (b : K)) (-1 / iL (ww (a : K) (b : K))) (jj (Velu.xc (Pt a b h)))
        (jj (Velu.yc (Pt a b h))) := by
  classical
  have tn := tn_of_norm hh
  set f := fL tn with hfd
  set j : 𝒪 →+* LL := jj.comp jK with hjd
  have hj : ∀ r, f (C r) = j r := fL_C tn
  have fX0 : f (X 0) = iL (X ()) := by rw [hfd, fL_apply, ev2_X0, map_X]
  have fX1 : f (X 1) = jj (h : K) := by rw [hfd, fL_apply, ev2_X1, map_C]; rfl
  have fw0 : f (wt (shortO a b) (X 0)) = iL (ww (a : K) (b : K)) := by
    rw [hfd, fL_apply, ev2_w0, map_w_short]
  have fw1 : f (wt (shortO a b) (X 1)) = jj (wz a b h : K) := by
    rw [hfd, fL_apply, ev2_w1, map_C]; rfl
  have fwF : f (wt (shortO a b) (F (shortO a b))) = iL (MvPowerSeries.map jK (wh a b h)) := by
    rw [hfd, fL_apply, ev2_wF]
  have hw0 : f (wt (shortO a b) (X 0)) ≠ 0 := by rw [fw0]; exact ι_ww_ne
  have hw1 : f (wt (shortO a b) (X 1)) ≠ 0 := by rw [fw1]; exact jj_ne (wz_ne_zero a b hh h0)
  have hwF : f (wt (shortO a b) (F (shortO a b))) ≠ 0 := by rw [fwF]; exact map_wh_ne h0 hh
  have hnd : ∀ u v : LL, -2 + ((shortO a b).map j).a₁ * u + ((shortO a b).map j).a₃ * v ≠ 0 := by
    intro u v
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, shortO, map_zero, zero_mul,
      add_zero]
    exact neg_ne_zero.2 two_ne_LL
  have hxq : jj (Velu.xc (Pt a b h)) = f (X 1) / f (wt (shortO a b) (X 1)) := by
    rw [fX1, fw1, xc_Pt h0 hh, map_div₀]
  have hyq : jj (Velu.yc (Pt a b h)) = -1 / f (wt (shortO a b) (X 1)) := by
    rw [fw1, yc_Pt h0 hh, map_div₀, map_neg, map_one]
  have hx0 : xL (a : K) (b : K) = f (X 0) / f (wt (shortO a b) (X 0)) := by rw [fX0, fw0]
  have hx : f (X 0) / f (wt (shortO a b) (X 0)) ≠ f (X 1) / f (wt (shortO a b) (X 1)) := by
    rw [← hx0, ← hxq]
    intro e
    have := x_sub_mul_r (A := (a : K)) (B := (b : K)) (Pt a b h)
    rw [e, sub_self, zero_mul] at this
    exact zero_ne_one this
  have key := chord_add_hom (shortO a b) j f hj hw0 hw1 hwF (hnd _ _) (hnd _ _) (hnd _ _) hx
  simp only [pt] at key
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx, WeierstrassCurve.Affine.Point.some.injEq] at key
  obtain ⟨-, ky⟩ := key
  rw [← fwF, ← ky, addY_short _ (by simp [shortO]) (by simp [shortO]) (by simp [shortO]) hx,
    hx0, hxq, hyq, fw0]

end VeluDescent
