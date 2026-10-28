/-
# Formal points as points of `E(K)`, and the canonical subgroup as a Vélu kernel

* `G_z3`, `G_F`, `wt_F`: over a domain, `(z₃, w₃)` lies on the curve and `w(F(z₁,z₂)) = w₃/d`.
* `chord_add_hom`: for **any** ring hom `f : R⟦z₁,z₂⟧ → L` to a field (compatible with `j : R → L` on
  constants), the chord addition law holds for the images: `P(f z₁) + P(f z₂) = P(f F)`, given
  `f w(zᵢ) ≠ 0`, `f w(F) ≠ 0`, non-degeneracy and distinct `x`-coordinates. (`P_add` is the case
  `f = algebraMap` into the fraction field; here we use evaluation at points of `𝔪`.)
* For a short curve `W = shortO a b` over `𝒪 = integers K`: the point map `Pt : 𝒪 → E(K)`,
  `z ↦ (z/w(z), -1/w(z))` (`0` for `z = 0` or `‖z‖ ≥ 1`), with
  `Pt (z +_F z') = Pt z + Pt z'` for distinct `x`-coordinates (`Pt_add`), `Pt (-z) = -Pt z`
  (`Pt_neg`), `z +_F (-z) = 0` (`padd_neg`).
* `Pt_hom`: on any finite subgroup `S ⊆ F[p]` (`p ≥ 5` prime), `Pt` is additive.
* `exists_kernel_of_finSub`: `Pt(S)` is a subgroup of `E(K)` of odd order, hence Vélu kernel data
  `κ` with `κ.G = Pt(S)` exist.
-/
import RamanujanTau.VeluLubin.Link

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VeluLubin
open MvPowerSeries EllipticFormal

section Series
variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)

local notation "A₂" => MvPowerSeries (Fin 2) R

lemma X0_ne_X1 : (X 0 : A₂) ≠ X 1 := by
  intro h
  have := congrArg (coeff (Finsupp.single 0 1)) h
  rw [lin_X, lin_X] at this
  simp at this

/-- `(z₃, w₃)` lies on the curve. -/
theorem G_z3 : G (WM W (Fin 2)) (z3 W) (w3 W) = 0 := by
  have h0 := G_wt (W := W) (t := (X 0 : A₂)) (by simp)
  have h1 := G_wt (W := W) (t := (X 1 : A₂)) (by simp)
  rw [nu_eq_zero] at h0
  rw [nu_eq_one] at h1
  exact G_third _ h0 h1 X0_ne_X1 (z3_spec W)

/-- `(F, w₃/d)` lies on the curve. -/
theorem G_F : G (WM W (Fin 2)) (F W) (w3 W * dInv W) = 0 := by
  have he : ((WM W (Fin 2)).a₁ * z3 W + (WM W (Fin 2)).a₃ * w3 W - 1) * dInv W = 1 :=
    dd_mul_dInv W
  rw [F, G_neg _ _ _ _ he, G_z3, mul_zero]

/-- `w(F(z₁, z₂)) = w₃ / d`. -/
theorem wt_F : wt W (F W) = w3 W * dInv W :=
  G_unique (WM W (Fin 2)) (cc_F W) (cc_wt (cc_F W)) (by simp [cc_w3]) (G_wt (cc_F W)) (G_F W)

end Series

/-! ### The chord law under a ring hom to a field -/

section Chord
variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)
variable {L : Type*} [Field L] [DecidableEq L] (j : R →+* L)
  (f : MvPowerSeries (Fin 2) R →+* L) (hj : ∀ r, f (C r) = j r)

local notation "A₂" => MvPowerSeries (Fin 2) R

include hj

lemma map_WM_f : (WM W (Fin 2)).map f = W.map j := by
  ext <;> simp [WM, hj]

lemma f_G (z w : A₂) : f (G (WM W (Fin 2)) z w) = G (W.map j) (f z) (f w) := by
  rw [map_G, map_WM_f W j f hj]

lemma f_G_wt {t : A₂} (ht : constantCoeff t = 0) : G (W.map j) (f t) (f (wt W t)) = 0 := by
  rw [← f_G W j f hj, G_wt ht, map_zero]

/-- **the chord law for the images under `f`**. -/
theorem chord_add_hom
    (hw0 : f (wt W (X 0 : A₂)) ≠ 0) (hw1 : f (wt W (X 1 : A₂)) ≠ 0) (hwF : f (wt W (F W)) ≠ 0)
    (hnd0 : -2 + (W.map j).a₁ * f (X 0) + (W.map j).a₃ * f (wt W (X 0 : A₂)) ≠ 0)
    (hnd1 : -2 + (W.map j).a₁ * f (X 1) + (W.map j).a₃ * f (wt W (X 1 : A₂)) ≠ 0)
    (hndF : -2 + (W.map j).a₁ * f (F W) + (W.map j).a₃ * f (wt W (F W)) ≠ 0)
    (hx : f (X 0) / f (wt W (X 0 : A₂)) ≠ f (X 1) / f (wt W (X 1 : A₂))) :
    pt (W.map j) (f (X 0)) (f (wt W (X 0 : A₂))) hw0 (f_G_wt W j f hj (by simp)) hnd0 +
        pt (W.map j) (f (X 1)) (f (wt W (X 1 : A₂))) hw1 (f_G_wt W j f hj (by simp)) hnd1 =
      pt (W.map j) (f (F W)) (f (wt W (F W))) hwF (f_G_wt W j f hj (cc_F W)) hndF := by
  set WL := W.map j
  have hWL := map_WM_f W j f hj
  set l := f (lam W)
  set n := f (nu W)
  set z₃ := f (z3 W)
  set e := f (dInv W)
  have hws : f (wt W (X 0 : A₂)) = l * f (X 0) + n := by rw [nu_eq_zero, map_add, map_mul]
  have hwt : f (wt W (X 1 : A₂)) = l * f (X 1) + n := by rw [nu_eq_one, map_add, map_mul]
  have hGs : G WL (f (X 0)) (l * f (X 0) + n) = 0 := hws ▸ f_G_wt W j f hj (by simp)
  have hGt : G WL (f (X 1)) (l * f (X 1) + n) = 0 := hwt ▸ f_G_wt W j f hj (by simp)
  have hlead : lead WL l ≠ 0 := by
    intro h
    have := congrArg f (lead_mul_leadInv W)
    rw [map_mul, lead_map, hWL, map_one] at this
    rw [h, zero_mul] at this
    exact zero_ne_one this
  have h3 : lead WL l * (f (X 0) + f (X 1) + z₃) + B WL l n = 0 := by
    have := congrArg f (z3_spec W)
    rwa [map_add, map_mul, map_add, map_add, lead_map, B_map, hWL, map_zero] at this
  have he : (WL.a₁ * z₃ + WL.a₃ * (l * z₃ + n) - 1) * e = 1 := by
    have := congrArg f (dd_mul_dInv W)
    rw [map_mul, map_one, dd, w3] at this
    have h1 : f (WM W (Fin 2)).a₁ = WL.a₁ := by simp [WL, WM, hj]
    have h3' : f (WM W (Fin 2)).a₃ = WL.a₃ := by simp [WL, WM, hj]
    simp only [map_sub, map_add, map_mul, map_one, h1, h3'] at this
    exact this
  have hFe : f (F W) = z₃ * e := by rw [F, map_mul]
  have hwFe : f (wt W (F W)) = (l * z₃ + n) * e := by rw [wt_F, w3, map_mul, map_add, map_mul]
  have hw3 : l * z₃ + n ≠ 0 := by
    intro h; apply hwF; rw [hwFe, h, zero_mul]
  have hwFK : (l * z₃ + n) * e ≠ 0 := hwFe ▸ hwF
  have hGFK : G WL (z₃ * e) ((l * z₃ + n) * e) = 0 := by
    rw [← hFe, ← hwFe]; exact f_G_wt W j f hj (cc_F W)
  have hndFK : -2 + WL.a₁ * (z₃ * e) + WL.a₃ * ((l * z₃ + n) * e) ≠ 0 := by
    rw [← hFe, ← hwFe]; exact hndF
  have hsne : l * f (X 0) + n ≠ 0 := hws ▸ hw0
  have htne : l * f (X 1) + n ≠ 0 := hwt ▸ hw1
  have hnds : -2 + WL.a₁ * f (X 0) + WL.a₃ * (l * f (X 0) + n) ≠ 0 := hws ▸ hnd0
  have hndt : -2 + WL.a₁ * f (X 1) + WL.a₃ * (l * f (X 1) + n) ≠ 0 := hwt ▸ hnd1
  have hx' : f (X 0) / (l * f (X 0) + n) ≠ f (X 1) / (l * f (X 1) + n) := by
    rw [← hws, ← hwt]; exact hx
  have key := chord_add WL hGs hGt hsne htne hnds hndt hx' hlead h3 hw3 he hwFK hGFK hndFK
  rw [pt_eq_pt WL rfl hws _ _ _ hsne hGs hnds, pt_eq_pt WL rfl hwt _ _ _ htne hGt hndt, key]
  exact pt_eq_pt _ hFe.symm hwFe.symm _ _ _ _ _ _

end Chord

/-! ### Oddness of `w` and `F(z, -z) = 0` when `a₁ = a₃ = 0` -/

section Odd
variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)

local notation "R1" => MvPowerSeries Unit R
local notation "A₂" => MvPowerSeries (Fin 2) R

lemma G_neg_neg (h1 : W.a₁ = 0) (h3 : W.a₃ = 0) {σ : Type*} (z w : MvPowerSeries σ R) :
    G (WM W σ) (-z) (-w) = -G (WM W σ) z w := by
  simp only [G, WM, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, h1, h3, map_zero]
  ring

/-- **`w` is odd**: `w(-z) = -w(z)` (for `a₁ = a₃ = 0`). -/
theorem wt_neg (h1 : W.a₁ = 0) (h3 : W.a₃ = 0) {σ : Type*} {t : MvPowerSeries σ R}
    (ht : constantCoeff t = 0) : wt W (-t) = -wt W t := by
  have hn : constantCoeff (-t) = 0 := by simp [ht]
  refine G_unique (WM W σ) hn (cc_wt hn) (by simp [cc_wt ht]) (G_wt hn) ?_
  have := G_neg_neg W h1 h3 t (wt W t)
  rw [G_wt ht, neg_zero] at this
  exact this

/-- **`F(z, -z) = 0`** (for `a₁ = a₃ = 0`, `2 ≠ 0`). -/
theorem F_X_neg (h1 : W.a₁ = 0) (h3 : W.a₃ = 0) (h2 : (2 : R) ≠ 0) :
    subst ![(X () : R1), -X ()] (F W) = 0 := by
  have hv : ∀ s, constantCoeff ((![X (), -X ()] : Fin 2 → R1) s) = 0 :=
    FGL.cc_vec2 (by simp) (by simp)
  set g : A₂ →ₐ[R] R1 := substAlgHom (FGL.hs hv)
  have hg : ∀ f, g f = subst ![(X () : R1), -X ()] f := fun f => by rw [coe_substAlgHom]
  have g0 : g (X 0) = X () := by rw [hg]; exact FGL.sX _ hv 0
  have g1 : g (X 1) = -X () := by rw [hg]; exact FGL.sX _ hv 1
  have gw : ∀ i : Fin 2, g (wt W (X i : A₂)) = wt W (g (X i)) := by
    intro i; rw [hg, hg, subst_wt (by simp) _ hv]
  have ew : wt W (X () : R1) = (w W : R1) := PowerSeries.X_subst _
  have gW : (WM W (Fin 2)).map (g : A₂ →+* R1) = WM W Unit := WM_map_eq g
  -- the slope through `(z, w)` and `(-z, -w)`
  have hl := congrArg g (lam_spec W)
  rw [map_mul, map_sub, map_sub, gw, gw, g0, g1, wt_neg W h1 h3 (by simp), ew] at hl
  have h2' : (2 : R1) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp only [map_ofNat, map_zero] at this
    exact h2 this
  have hXl : X () * g (lam W) = (w W : R1) := by
    have : (2 : R1) * (X () * g (lam W) - w W) = 0 := by linear_combination -hl
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h2')
  have hn : g (nu W) = 0 := by
    rw [nu, map_sub, map_mul, gw, g0, ew]; linear_combination -hXl
  have hB : g (B (WM W (Fin 2)) (lam W) (nu W)) = 0 := by
    have := B_map (g : A₂ →+* R1) (WM W (Fin 2)) (lam W) (nu W)
    simp only [RingHom.coe_coe] at this
    rw [this, gW, hn]
    simp [B, WM, h1, h3]
  have hz : g (z3 W) = 0 := by
    rw [z3, map_sub, map_sub, map_neg, map_mul, hB, g0, g1]; ring
  rw [← hg, F, map_mul, hz, zero_mul]

end Odd

/-! ### Points of `𝔪` as points of `E(K)` (short curves) -/

section Pts
open CanonicalIsogeny

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]
  [DecidableEq K]

local notation "𝒪" => integers K
local notation "ι" => Subring.subtype (integers K)

lemma tn_of_norm {z : 𝒪} (hz : ‖(z : K)‖ < 1) : IsTopologicallyNilpotent z :=
  isTopologicallyNilpotent_of_norm_lt_one hz

lemma norm_lt_one_of_tn {z : 𝒪} (hz : IsTopologicallyNilpotent z) : ‖(z : K)‖ < 1 := by
  have h : Filter.Tendsto (fun n : ℕ => ((z ^ n : 𝒪) : K)) Filter.atTop (nhds 0) := by
    have := (continuous_incl (K := K)).tendsto 0
    simpa using this.comp hz
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h 1 one_pos
  have := hN (N + 1) (by omega)
  rw [dist_zero_right, Subring.coe_pow, norm_pow] at this
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 this

variable (a b : ↥(integers K))

/-- `w(z) ∈ 𝒪` for `z ∈ 𝔪`. -/
noncomputable def wz (z : 𝒪) : 𝒪 := Lubin.pt (fun _ : Unit => z) (w (shortO a b) : MvPowerSeries Unit 𝒪)

lemma admPt1 {z : 𝒪} (hz : ‖(z : K)‖ < 1) : Lubin.AdmPt (fun _ : Unit => z) := fun _ => tn_of_norm hz

lemma PH1 {z : 𝒪} (hz : ‖(z : K)‖ < 1) (g : MvPowerSeries Unit 𝒪) :
    Lubin.PH (admPt1 hz) g = Lubin.pt (fun _ : Unit => z) g := Lubin.PH_apply _ _

lemma G_wz {z : 𝒪} (hz : ‖(z : K)‖ < 1) : G (shortO a b) z (wz a b z) = 0 := by
  have h := congrArg (Lubin.PH (admPt1 hz)) (G_w (shortO a b))
  have e1 : ∀ r : 𝒪, Lubin.PH (admPt1 hz) (PowerSeries.C r) = r := fun r => by
    rw [PH1 hz]; exact Lubin.pt_C r
  have e2 : Lubin.PH (admPt1 hz) PowerSeries.X = z := by rw [PH1 hz]; exact Lubin.pt_X ()
  simp only [G, WC, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_add, map_sub, map_mul, map_pow, e1, e2,
    map_zero] at h
  unfold G
  rw [wz, ← PH1 hz]
  exact h

lemma wz_eq {z : 𝒪} (hz : ‖(z : K)‖ < 1) :
    wz a b z = z ^ 3 * Lubin.pt (fun _ : Unit => z) (v (shortO a b) : MvPowerSeries Unit 𝒪) := by
  rw [wz, ← PH1 hz, ← PH1 hz, show (w (shortO a b) : MvPowerSeries Unit 𝒪) = X () ^ 3 * v (shortO a b)
    from w_eq_X3_mul_v _, map_mul, map_pow, PH1 hz, Lubin.pt_X]

lemma isUnit_pt_v {z : 𝒪} (hz : ‖(z : K)‖ < 1) :
    IsUnit (Lubin.pt (fun _ : Unit => z) (v (shortO a b) : MvPowerSeries Unit 𝒪)) := by
  rw [← PH1 hz]
  refine IsUnit.map _ ?_
  rw [MvPowerSeries.isUnit_iff_constantCoeff]
  have := cc_v (shortO a b)
  rw [show PowerSeries.constantCoeff (v (shortO a b)) =
    constantCoeff (v (shortO a b) : MvPowerSeries Unit 𝒪) from rfl] at this
  rw [this]; exact isUnit_one

lemma wz_ne_zero {z : 𝒪} (hz : ‖(z : K)‖ < 1) (h0 : z ≠ 0) : ((wz a b z : 𝒪) : K) ≠ 0 := by
  intro h
  have h' : wz a b z = 0 := Subtype.ext h
  rw [wz_eq a b hz] at h'
  rcases mul_eq_zero.1 h' with h1 | h1
  · exact h0 (pow_eq_zero_iff (by norm_num) |>.1 h1)
  · exact (isUnit_pt_v a b hz).ne_zero h1

lemma G_wzK {z : 𝒪} (hz : ‖(z : K)‖ < 1) :
    G (Velu.short (a : K) (b : K)) (z : K) (wz a b z : K) = 0 := by
  have := congrArg ι (G_wz a b hz)
  rw [map_G, map_zero] at this
  exact this

lemma nd_short (z w : K) : -2 + (Velu.short (a : K) (b : K)).a₁ * z + (Velu.short (a : K) (b : K)).a₃ * w ≠ 0 := by
  simp only [Velu.short_a₁, Velu.short_a₃, zero_mul, add_zero]
  norm_num

/-- **the point `P(z) = (z/w(z), -1/w(z))` of `E(K)`** (`0` unless `z ≠ 0`, `‖z‖ < 1`). -/
noncomputable def Pt (z : 𝒪) : (Velu.short (a : K) (b : K)).Point :=
  if h : z ≠ 0 ∧ ‖(z : K)‖ < 1 then
    pt (Velu.short (a : K) (b : K)) (z : K) (wz a b z : K) (wz_ne_zero a b h.2 h.1) (G_wzK a b h.2)
      (nd_short a b _ _)
  else 0

lemma Pt_eq {z : 𝒪} (h0 : z ≠ 0) (hz : ‖(z : K)‖ < 1) :
    Pt a b z = pt (Velu.short (a : K) (b : K)) (z : K) (wz a b z : K) (wz_ne_zero a b hz h0)
      (G_wzK a b hz) (nd_short a b _ _) := by
  rw [Pt, dif_pos ⟨h0, hz⟩]

lemma Pt_zero : Pt a b 0 = 0 := by rw [Pt, dif_neg (by simp)]

lemma Pt_ne_zero {z : 𝒪} (h0 : z ≠ 0) (hz : ‖(z : K)‖ < 1) : Pt a b z ≠ 0 := by
  rw [Pt_eq a b h0 hz, pt]; exact fun h => by cases h

/-- `‖z +_F z'‖ < 1`. -/
lemma norm_padd_lt {z z' : 𝒪} (hz : ‖(z : K)‖ < 1) (hz' : ‖(z' : K)‖ < 1) :
    ‖((Lubin.padd (formalGroup (shortO a b)) z z' : 𝒪) : K)‖ < 1 :=
  lt_of_le_of_lt (norm_padd_le (formalGroup (shortO a b)) incl continuous_incl norm_incl_le (tn_of_norm hz) (tn_of_norm hz'))
    (max_lt hz hz')

lemma admPt2' {z z' : 𝒪} (hz : ‖(z : K)‖ < 1) (hz' : ‖(z' : K)‖ < 1) : Lubin.AdmPt ![z, z'] :=
  Lubin.admPt2 (tn_of_norm hz) (tn_of_norm hz')

lemma pt_wt2 {z z' : 𝒪} (hz : ‖(z : K)‖ < 1) (hz' : ‖(z' : K)‖ < 1) {g : MvPowerSeries (Fin 2) 𝒪}
    (hg : constantCoeff g = 0) :
    Lubin.pt ![z, z'] (wt (shortO a b) g) =
      Lubin.pt (fun _ : Unit => Lubin.pt ![z, z'] g) (w (shortO a b) : MvPowerSeries Unit 𝒪) := by
  rw [wt, PowerSeries.subst_def, Lubin.pt_subst (fun _ => hg) (admPt2' hz hz')]

/-- **the formal law is the group law at points** (distinct `x`-coordinates). -/
theorem Pt_add {z z' : 𝒪} (h0 : z ≠ 0) (h0' : z' ≠ 0) (hz : ‖(z : K)‖ < 1) (hz' : ‖(z' : K)‖ < 1)
    (hF : Lubin.padd (formalGroup (shortO a b)) z z' ≠ 0)
    (hx : (z : K) / (wz a b z : K) ≠ (z' : K) / (wz a b z' : K)) :
    Pt a b (Lubin.padd (formalGroup (shortO a b)) z z') = Pt a b z + Pt a b z' := by
  have hv := admPt2' hz hz'
  set f : MvPowerSeries (Fin 2) 𝒪 →+* K := (Subring.subtype (integers K)).comp (Lubin.PH hv)
  have hf : ∀ g, f g = ((Lubin.pt ![z, z'] g : 𝒪) : K) := fun g => by
    simp only [f, RingHom.coe_comp, Function.comp_apply, Lubin.PH_apply]; rfl
  have hj : ∀ r, f (C r) = ι r := fun r => by rw [hf, Lubin.pt_C]; rfl
  have fX0 : f (X 0) = z := by rw [hf, Lubin.pt_X]; rfl
  have fX1 : f (X 1) = z' := by rw [hf, Lubin.pt_X]; rfl
  have fw0 : f (wt (shortO a b) (X 0)) = (wz a b z : K) := by
    rw [hf, pt_wt2 a b hz hz' (by simp), Lubin.pt_X]; rfl
  have fw1 : f (wt (shortO a b) (X 1)) = (wz a b z' : K) := by
    rw [hf, pt_wt2 a b hz hz' (by simp), Lubin.pt_X]; rfl
  have fF : f (F (shortO a b)) = ((Lubin.padd (formalGroup (shortO a b)) z z' : 𝒪) : K) := by
    rw [hf]; rfl
  have fwF : f (wt (shortO a b) (F (shortO a b))) = (wz a b (Lubin.padd (formalGroup (shortO a b)) z z') : K) := by
    rw [hf, pt_wt2 a b hz hz' (cc_F _)]; rfl
  have hpz := norm_padd_lt a b hz hz'
  have key := chord_add_hom (shortO a b) ι f hj (fw0 ▸ wz_ne_zero a b hz h0)
    (fw1 ▸ wz_ne_zero a b hz' h0') (fwF ▸ wz_ne_zero a b hpz hF) (nd_short a b _ _)
    (nd_short a b _ _) (nd_short a b _ _) (by rw [fX0, fX1, fw0, fw1]; exact hx)
  rw [Pt_eq a b hF hpz, Pt_eq a b h0 hz, Pt_eq a b h0' hz']
  have e0 := pt_eq_pt (Velu.short (a : K) (b : K)) fX0 fw0 (fw0 ▸ wz_ne_zero a b hz h0)
    (f_G_wt (shortO a b) ι f hj (by simp)) (nd_short a b _ _) (wz_ne_zero a b hz h0) (G_wzK a b hz)
    (nd_short a b _ _)
  have e1 := pt_eq_pt (Velu.short (a : K) (b : K)) fX1 fw1 (fw1 ▸ wz_ne_zero a b hz' h0')
    (f_G_wt (shortO a b) ι f hj (by simp)) (nd_short a b _ _) (wz_ne_zero a b hz' h0')
    (G_wzK a b hz') (nd_short a b _ _)
  have e2 := pt_eq_pt (Velu.short (a : K) (b : K)) fF fwF (fwF ▸ wz_ne_zero a b hpz hF)
    (f_G_wt (shortO a b) ι f hj (cc_F _)) (nd_short a b _ _) (wz_ne_zero a b hpz hF)
    (G_wzK a b hpz) (nd_short a b _ _)
  rw [← e0, ← e1, ← e2]
  exact key.symm

lemma two_ne_zero_O : (2 : 𝒪) ≠ 0 := by
  intro h
  have := congrArg (fun x : 𝒪 => (x : K)) h
  simp at this

lemma pt1_neg {z : 𝒪} (hz : ‖(z : K)‖ < 1) (g : MvPowerSeries Unit 𝒪) :
    Lubin.pt (fun _ : Unit => z) (-g) = -Lubin.pt (fun _ : Unit => z) g := by
  rw [← PH1 hz, ← PH1 hz, map_neg]

/-- `w(-z) = -w(z)`. -/
lemma wz_neg {z : 𝒪} (hz : ‖(z : K)‖ < 1) : wz a b (-z) = -wz a b z := by
  have h := wt_neg (shortO a b) rfl rfl (t := (X () : MvPowerSeries Unit 𝒪)) (by simp)
  have ew : wt (shortO a b) (X () : MvPowerSeries Unit 𝒪) = (w (shortO a b) : _) :=
    PowerSeries.X_subst _
  rw [ew] at h
  have h2 := congrArg (Lubin.pt (fun _ : Unit => z)) h
  rw [pt1_neg hz, wt, PowerSeries.subst_def,
    Lubin.pt_subst (fun _ => by simp) (admPt1 hz), pt1_neg hz, Lubin.pt_X] at h2
  exact h2

lemma norm_neg_lt {z : 𝒪} (hz : ‖(z : K)‖ < 1) : ‖((-z : 𝒪) : K)‖ < 1 := by
  rw [Subring.coe_neg, norm_neg]; exact hz

/-- **`P(-z) = -P(z)`**. -/
theorem Pt_neg (z : 𝒪) : Pt a b (-z) = -Pt a b z := by
  by_cases h : z ≠ 0 ∧ ‖(z : K)‖ < 1
  · obtain ⟨h0, hz⟩ := h
    rw [Pt_eq a b (neg_ne_zero.2 h0) (norm_neg_lt hz), Pt_eq a b h0 hz, pt, pt,
      WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
    rw [wz_neg a b hz]
    simp only [Subring.coe_neg, neg_div_neg_eq, WeierstrassCurve.Affine.negY, Velu.short_a₁,
      Velu.short_a₃, zero_mul, sub_zero, true_and]
    ring
  · have h' : ¬ ((-z) ≠ 0 ∧ ‖((-z : 𝒪) : K)‖ < 1) := by
      rw [Subring.coe_neg, norm_neg, neg_ne_zero]; exact h
    rw [Pt, dif_neg h', Pt, dif_neg h, neg_zero]

/-- **`z +_F (-z) = 0`**. -/
theorem padd_neg {z : 𝒪} (hz : ‖(z : K)‖ < 1) :
    Lubin.padd (formalGroup (shortO a b)) z (-z) = 0 := by
  have h := F_X_neg (shortO a b) rfl rfl (two_ne_zero_O (K := K))
  have hv : ∀ s, constantCoeff ((![X (), -X ()] : Fin 2 → MvPowerSeries Unit 𝒪) s) = 0 :=
    FGL.cc_vec2 (by simp) (by simp)
  have h2 := congrArg (Lubin.pt (fun _ : Unit => z)) h
  rw [Lubin.pt_subst hv (admPt1 hz), ← PH1 hz, map_zero] at h2
  have e : (fun s : Fin 2 => Lubin.pt (fun _ : Unit => z) ((![X (), -X ()] : Fin 2 → MvPowerSeries Unit 𝒪) s)) =
      ![z, -z] := by
    funext s; fin_cases s
    · exact Lubin.pt_X ()
    · show Lubin.pt (fun _ : Unit => z) (-X ()) = -z
      rw [pt1_neg hz, Lubin.pt_X]
  rw [e] at h2
  exact h2

/-- equal `x`-coordinates force `z' = ±z`. -/
theorem x_eq {z z' : 𝒪} (h0 : z ≠ 0) (h0' : z' ≠ 0) (hz : ‖(z : K)‖ < 1) (hz' : ‖(z' : K)‖ < 1)
    (hx : (z : K) / (wz a b z : K) = (z' : K) / (wz a b z' : K)) : z' = z ∨ z' = -z := by
  rcases x_eq_cases (Velu.short (a : K) (b : K)) (wz_ne_zero a b hz h0) (G_wzK a b hz)
    (wz_ne_zero a b hz' h0') (G_wzK a b hz') hx with ⟨h1, -⟩ | h1
  · exact Or.inl (Subtype.ext h1.symm)
  · right
    apply Subtype.ext
    simp only [Velu.short_a₁, Velu.short_a₃, zero_mul, zero_add, zero_sub, mul_neg, mul_one] at h1
    rw [Subring.coe_neg]; exact h1.symm

/-! ### Additivity on finite subgroups of `F[p]` -/

local notation "Fo" => formalGroup (shortO a b)

lemma padd_cancel {x y : 𝒪} (hx : ‖(x : K)‖ < 1) (hy : ‖(y : K)‖ < 1)
    (h : Lubin.padd (formalGroup (shortO a b)) x y = 0) : y = -x := by
  have tx := tn_of_norm hx
  have ty := tn_of_norm hy
  have tnx := tn_of_norm (norm_neg_lt hx)
  have h1 : Lubin.padd (formalGroup (shortO a b)) (-x) x = 0 := by
    rw [Lubin.padd_comm tnx tx]; exact padd_neg a b hx
  calc y = Lubin.padd (formalGroup (shortO a b)) 0 y := (Lubin.zero_padd ty).symm
    _ = Lubin.padd (formalGroup (shortO a b)) (Lubin.padd (formalGroup (shortO a b)) (-x) x) y := by
        rw [h1]
    _ = Lubin.padd (formalGroup (shortO a b)) (-x) (Lubin.padd (formalGroup (shortO a b)) x y) :=
        Lubin.padd_assoc tnx tx ty (tn_of_norm (by rw [h1]; simp)) (tn_of_norm (norm_padd_lt a b hx hy))
    _ = -x := by rw [h, Lubin.padd_zero tnx]

/-- `[n] x` at a point. -/
noncomputable abbrev nm (x : 𝒪) (n : ℕ) : 𝒪 :=
  Lubin.pt (fun _ : Unit => x) (FGL.nmul (formalGroup (shortO a b)) n)

lemma nm_zero (x : 𝒪) (hx : ‖(x : K)‖ < 1) : nm a b x 0 = 0 :=
  pt_zero_series (tn_of_norm hx)

lemma nm_succ (x : 𝒪) (hx : ‖(x : K)‖ < 1) (n : ℕ) :
    nm a b x (n + 1) = Lubin.padd (formalGroup (shortO a b)) x (nm a b x n) :=
  pt_nmul_succ (tn_of_norm hx) n

lemma norm_nm (x : 𝒪) (hx : ‖(x : K)‖ < 1) (n : ℕ) : ‖((nm a b x n : 𝒪) : K)‖ < 1 := by
  induction n with
  | zero => rw [nm_zero a b x hx]; simp
  | succ n ih => rw [nm_succ a b x hx]; exact norm_padd_lt a b hx ih

lemma nm_one (x : 𝒪) (hx : ‖(x : K)‖ < 1) : nm a b x 1 = x := by
  rw [nm_succ a b x hx, nm_zero a b x hx, Lubin.padd_zero (tn_of_norm hx)]

lemma nm_add (x : 𝒪) (hx : ‖(x : K)‖ < 1) (m n : ℕ) :
    nm a b x (m + n) = Lubin.padd (formalGroup (shortO a b)) (nm a b x m) (nm a b x n) := by
  induction m with
  | zero => rw [zero_add, nm_zero a b x hx, Lubin.zero_padd (tn_of_norm (norm_nm a b x hx n))]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, nm_succ a b x hx, ih, nm_succ a b x hx,
      Lubin.padd_assoc (tn_of_norm hx) (tn_of_norm (norm_nm a b x hx m))
        (tn_of_norm (norm_nm a b x hx n)) (tn_of_norm (norm_padd_lt a b hx (norm_nm a b x hx m)))
        (tn_of_norm (norm_padd_lt a b (norm_nm a b x hx m) (norm_nm a b x hx n)))]

lemma nm_mul (x : 𝒪) (hx : ‖(x : K)‖ < 1) {m : ℕ} (hm : nm a b x m = 0) (k : ℕ) :
    nm a b x (m * k) = 0 := by
  induction k with
  | zero => rw [mul_zero, nm_zero a b x hx]
  | succ k ih => rw [Nat.mul_succ, nm_add a b x hx, ih, hm, Lubin.padd_zero Lubin.tn0]

lemma nm_two (x : 𝒪) (hx : ‖(x : K)‖ < 1) :
    nm a b x 2 = Lubin.padd (formalGroup (shortO a b)) x x := by
  rw [nm_succ a b x hx, nm_one a b x hx]

/-- in `F[p]`, `p ≥ 5`: `[2] x ≠ 0` and `[3] x ≠ 0` for `x ≠ 0`. -/
lemma nm_two_three (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) {x : 𝒪} (hx : ‖(x : K)‖ < 1) (h0 : x ≠ 0)
    (hpx : nm a b x p = 0) : nm a b x 2 ≠ 0 ∧ nm a b x 3 ≠ 0 := by
  have h2 : nm a b x 2 ≠ 0 := by
    intro h2
    have hodd : p = 2 * (p / 2) + 1 := by
      have := hp.eq_one_or_self_of_dvd 2
      have : p % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one p with h | h
        · exfalso
          have h2p := (Nat.dvd_iff_mod_eq_zero).2 h
          rcases hp.eq_one_or_self_of_dvd 2 h2p with h' | h' <;> omega
        · exact h
      omega
    rw [hodd, nm_add a b x hx, nm_mul a b x hx h2, nm_one a b x hx,
      Lubin.zero_padd (tn_of_norm hx)] at hpx
    exact h0 hpx
  refine ⟨h2, fun h3 => ?_⟩
  have hr : p % 3 = 1 ∨ p % 3 = 2 := by
    rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h | h | h
    · exfalso
      rcases hp.eq_one_or_self_of_dvd 3 ((Nat.dvd_iff_mod_eq_zero).2 h) with h' | h' <;> omega
    · exact Or.inl h
    · exact Or.inr h
  have hd : p = 3 * (p / 3) + p % 3 := (Nat.div_add_mod p 3).symm
  rw [hd, nm_add a b x hx, nm_mul a b x hx h3, Lubin.zero_padd (tn_of_norm (norm_nm a b x hx _))]
    at hpx
  rcases hr with hr | hr
  · rw [hr, nm_one a b x hx] at hpx; exact h0 hpx
  · rw [hr] at hpx; exact h2 hpx

variable {p : ℕ}

/-- **additivity of `Pt` on a finite subgroup of `F[p]`** (`p ≥ 5`). -/
theorem Pt_hom (hp : p.Prime) (hp5 : 5 ≤ p) (S : Lubin.FinSub (formalGroup (shortO a b)))
    (hpS : ∀ h ∈ S.H, nm a b h p = 0) {x y : 𝒪} (hx : x ∈ S.H) (hy : y ∈ S.H) :
    Pt a b (Lubin.padd (formalGroup (shortO a b)) x y) = Pt a b x + Pt a b y := by
  have nx := norm_lt_one_of_tn (S.tn x hx)
  have ny := norm_lt_one_of_tn (S.tn y hy)
  by_cases hx0 : x = 0
  · subst hx0; rw [Lubin.zero_padd (S.tn y hy), Pt_zero, zero_add]
  by_cases hy0 : y = 0
  · subst hy0; rw [Lubin.padd_zero (S.tn x hx), Pt_zero, add_zero]
  by_cases hxy : (x : K) / (wz a b x : K) = (y : K) / (wz a b y : K)
  · rcases x_eq a b hx0 hy0 nx ny hxy with hyx | hyx
    · -- doubling
      rw [hyx]
      set d := Lubin.padd (formalGroup (shortO a b)) x x
      have nd : ‖(d : K)‖ < 1 := norm_padd_lt a b nx nx
      obtain ⟨h2, h3⟩ := nm_two_three a b p hp hp5 nx hx0 (hpS x hx)
      rw [nm_two a b x nx] at h2
      have h3' : Lubin.padd (formalGroup (shortO a b)) x d ≠ 0 := by
        rwa [nm_succ a b x nx, nm_two a b x nx] at h3
      have hdx : Lubin.padd (formalGroup (shortO a b)) d (-x) = x := by
        rw [Lubin.padd_assoc (S.tn x hx) (S.tn x hx) (tn_of_norm (norm_neg_lt nx)) (tn_of_norm nd)
          (tn_of_norm (by rw [padd_neg a b nx]; simp)), padd_neg a b nx, Lubin.padd_zero (S.tn x hx)]
      have hxd : (d : K) / (wz a b d : K) ≠ ((-x : 𝒪) : K) / (wz a b (-x) : K) := by
        intro he
        rcases x_eq a b h2 (neg_ne_zero.2 hx0) nd (norm_neg_lt nx) he with h | h
        · apply h3'
          have hd' : d = -x := h.symm
          rw [hd']; exact padd_neg a b nx
        · have hdx' : d = x := neg_injective h.symm
          apply hx0
          have := hdx
          rw [hdx', padd_neg a b nx] at this
          exact this.symm
      have key := Pt_add a b h2 (neg_ne_zero.2 hx0) nd (norm_neg_lt nx) (by rw [hdx]; exact hx0) hxd
      rw [hdx, Pt_neg] at key
      show Pt a b d = _
      rw [eq_add_neg_iff_add_eq] at key
      exact key.symm
    · -- `y = -x`
      rw [hyx, padd_neg a b nx, Pt_zero, Pt_neg, add_neg_cancel]
  · have hF : Lubin.padd (formalGroup (shortO a b)) x y ≠ 0 := by
      intro h
      have := padd_cancel a b nx ny h
      subst this
      apply hxy
      rw [wz_neg a b nx, Subring.coe_neg, Subring.coe_neg, neg_div_neg_eq]
    exact Pt_add a b hx0 hy0 nx ny hF hxy

/-- **the subgroup `Pt(S) ⊆ E(K)`** of a finite subgroup `S ⊆ F[p]` of the formal group. -/
noncomputable def Hpts (hp : p.Prime) (hp5 : 5 ≤ p) (S : Lubin.FinSub (formalGroup (shortO a b)))
    (hpS : ∀ h ∈ S.H, nm a b h p = 0) : AddSubgroup (Velu.short (a : K) (b : K)).Point where
  carrier := Pt a b '' (S.H : Set 𝒪)
  zero_mem' := ⟨0, S.zero_mem, Pt_zero a b⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨_, S.add_mem x hx y hy, Pt_hom a b hp hp5 S hpS hx hy⟩
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := S.neg_mem x hx
    have := padd_cancel a b (norm_lt_one_of_tn (S.tn x hx)) (norm_lt_one_of_tn (S.tn y hy)) hxy
    exact ⟨y, hy, by rw [this, Pt_neg]⟩

lemma mem_Hpts (hp : p.Prime) (hp5 : 5 ≤ p) (S : Lubin.FinSub (formalGroup (shortO a b)))
    (hpS : ∀ h ∈ S.H, nm a b h p = 0) (P : (Velu.short (a : K) (b : K)).Point) :
    P ∈ Hpts a b hp hp5 S hpS ↔ ∃ x ∈ S.H, Pt a b x = P := Iff.rfl

instance finite_Hpts (hp : p.Prime) (hp5 : 5 ≤ p) (S : Lubin.FinSub (formalGroup (shortO a b)))
    (hpS : ∀ h ∈ S.H, nm a b h p = 0) : Finite (Hpts a b hp hp5 S hpS) :=
  ((S.H.finite_toSet).image (Pt a b)).to_subtype

/-- `Pt(S)` has odd order (no `2`-torsion, by Cauchy). -/
theorem odd_card_Hpts (hp : p.Prime) (hp5 : 5 ≤ p) (S : Lubin.FinSub (formalGroup (shortO a b)))
    (hpS : ∀ h ∈ S.H, nm a b h p = 0) : Odd (Nat.card (Hpts a b hp hp5 S hpS)) := by
  rw [Nat.odd_iff]
  by_contra hc
  have h2 : 2 ∣ Nat.card (Hpts a b hp hp5 S hpS) := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_prime_addOrderOf_dvd_card' 2 h2
  obtain ⟨x, hx, hPx⟩ := P.2
  have nx := norm_lt_one_of_tn (S.tn x hx)
  have hPP : (P : (Velu.short (a : K) (b : K)).Point) + P = 0 := by
    have := addOrderOf_nsmul_eq_zero P
    rw [hP, two_nsmul] at this
    exact congrArg Subtype.val this
  have hP0 : P ≠ 0 := by
    intro h; rw [h, addOrderOf_zero] at hP; omega
  have hx0 : x ≠ 0 := by
    rintro rfl; apply hP0; apply Subtype.ext; rw [← hPx, Pt_zero]; rfl
  rw [← hPx, ← Pt_hom a b hp hp5 S hpS hx hx] at hPP
  have hd : Lubin.padd (formalGroup (shortO a b)) x x = 0 := by
    by_contra hd
    exact Pt_ne_zero a b hd (norm_padd_lt a b nx nx) hPP
  exact (nm_two_three a b p hp hp5 nx hx0 (hpS x hx)).1 (by rw [nm_two a b x nx]; exact hd)

/-- **the canonical-subgroup Vélu kernel**: for a finite subgroup `S ⊆ F[p]` (`p ≥ 5`) of the
formal group of `y² = x³ + ax + b` over `𝒪`, there is Vélu kernel data `κ` over `K` whose group
is `Pt(S) ⊆ E(K)`. -/
theorem exists_kernel_of_finSub (hp : p.Prime) (hp5 : 5 ≤ p)
    (S : Lubin.FinSub (formalGroup (shortO a b))) (hpS : ∀ h ∈ S.H, nm a b h p = 0) :
    ∃ κ : Velu.Kernel (a : K) (b : K), (κ.G : Set (Velu.short (a : K) (b : K)).Point) =
      Pt a b '' (S.H : Set 𝒪) :=
  Velu.exists_kernel (Hpts a b hp hp5 S hpS) (odd_card_Hpts a b hp hp5 S hpS)

end Pts

end VeluLubin
