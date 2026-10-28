/-
# The chord law for formal points without the linear-coefficient hypothesis; `n • P(T) = P([n]T)`

* `chord_data`: the substituted chord data `(l, n, z₃, e)` for formal points `s, t`.
* `x_eq_of_F_eq_zero`, `F_eq_zero_of_x_eq`: for `s ≠ t`, `F(s,t) = 0 ↔ s·w(t) = t·w(s)` (equal `x`).
* `P_add'`: `P(s) + P(t) = P(F(s,t))` whenever `x(s) ≠ x(t)` and `F(s,t) ≠ 0`.
* `negS`, `P_negS`: the formal inverse point `P(i(t)) = -P(t)`.
* `nsmul_P`: `n • P(T) = P([n]T)` as long as `[m]T ≠ 0` for `m ≤ n` (one variable, `2, 3 ≠ 0`).
-/
import RamanujanTau.EllipticFormal.FormalGroup
import RamanujanTau.FormalGroupLayer.Endo

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HeightEll
open MvPowerSeries EllipticFormal WeierstrassCurve.Affine

open scoped Classical

section Formal
variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

local notation "A" => MvPowerSeries σ R
local notation "K" => FractionRing (MvPowerSeries σ R)
local notation "ι" => algebraMap (MvPowerSeries σ R) (FractionRing (MvPowerSeries σ R))

lemma P_congr (h2 : (2 : R) ≠ 0) {s t : A} (h : s = t) (hs : constantCoeff s = 0)
    (ht : constantCoeff t = 0) (hs0 : s ≠ 0) (ht0 : t ≠ 0) : P W h2 s hs hs0 = P W h2 t ht ht0 := by
  subst h; rfl

/-- the chord data of two formal points. -/
lemma chord_data {s t : A} (hs : constantCoeff s = 0) (ht : constantCoeff t = 0) :
    ∃ l n z₃ e li : A, constantCoeff l = 0 ∧ constantCoeff n = 0 ∧ constantCoeff z₃ = 0 ∧
      wt W s = l * s + n ∧ wt W t = l * t + n ∧
      lead (WM W σ) l * (s + t + z₃) + B (WM W σ) l n = 0 ∧ lead (WM W σ) l * li = 1 ∧
      ((WM W σ).a₁ * z₃ + (WM W σ).a₃ * (l * z₃ + n) - 1) * e = 1 ∧
      subst ![s, t] (F W) = z₃ * e := by
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
  refine ⟨f (lam W), f (nu W), f (z3 W), f (dInv W), f (leadInv W), fcc _ (cc_lam W), fcc _ (cc_nu W),
    fcc _ (cc_z3 W), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← fX0, ← fwt, nu_eq_zero, map_add, map_mul]
  · rw [← fX1, ← fwt, nu_eq_one, map_add, map_mul]
  · have := congrArg f (z3_spec W)
    rwa [map_add, map_mul, map_add, map_add, lead_map, B_map, fWM, fX0, fX1, map_zero] at this
  · have := congrArg f (lead_mul_leadInv W)
    rwa [map_mul, lead_map, fWM, map_one] at this
  · have := congrArg f (dd_mul_dInv W)
    rw [map_mul, map_one, dd, w3] at this
    simpa [← fWM] using this
  · rw [← φ_apply s t hs ht, ← RingHom.coe_coe, ← hf, F, map_mul]

lemma G_zero_left {S : Type*} [CommRing S] (V : WeierstrassCurve S) (n : S) :
    G V 0 n = n * (V.a₃ * n + V.a₆ * n ^ 2 - 1) := by simp only [G]; ring

/-- `F(s, t) = 0` with `s ≠ t` forces equal `x`-coordinates. -/
theorem x_eq_of_F_eq_zero {s t : A} (hs : constantCoeff s = 0) (ht : constantCoeff t = 0)
    (hst : s ≠ t) (hF : subst ![s, t] (F W) = 0) : s * wt W t = t * wt W s := by
  obtain ⟨l, n, z₃, e, li, hcl, hcn, hcz, hws, hwt, h3, hlead, he, hFst⟩ := chord_data W hs ht
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have hz : z₃ = 0 := by rw [hFst] at hF; exact (mul_eq_zero.1 hF).resolve_right he0
  have hG3 := G_third _ (hws ▸ G_wt hs) (hwt ▸ G_wt ht) hst h3
  rw [hz, mul_zero, zero_add, G_zero_left] at hG3
  have hu : (WM W σ).a₃ * n + (WM W σ).a₆ * n ^ 2 - 1 ≠ 0 := by
    intro h; have := congrArg constantCoeff h; simp [hcn] at this
  have hn : n = 0 := (mul_eq_zero.1 hG3).resolve_right hu
  rw [hws, hwt, hn]; ring

/-- equal `x`-coordinates with `s ≠ t` force `F(s, t) = 0`. -/
theorem F_eq_zero_of_x_eq {s t : A} (hs : constantCoeff s = 0) (ht : constantCoeff t = 0)
    (hs0 : s ≠ 0) (ht0 : t ≠ 0) (hst : s ≠ t) (hx : s * wt W t = t * wt W s) :
    subst ![s, t] (F W) = 0 := by
  obtain ⟨l, n, z₃, e, li, hcl, hcn, hcz, hws, hwt, h3, hlead, he, hFst⟩ := chord_data W hs ht
  have hn : n = 0 := by
    have : n * (s - t) = 0 := by rw [hws, hwt] at hx; linear_combination hx
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hst)
  have hGs := hws ▸ G_wt (W := W) hs
  have hGt := hwt ▸ G_wt (W := W) ht
  rw [G_line, hn] at hGs hGt
  have hD : Dz (WM W σ) (0 : A) = 0 := by simp [Dz]
  rw [hD] at hGs hGt
  have qs : lead (WM W σ) l * s ^ 2 + B (WM W σ) l 0 * s + Cz (WM W σ) l 0 = 0 := by
    have : s * (lead (WM W σ) l * s ^ 2 + B (WM W σ) l 0 * s + Cz (WM W σ) l 0) = 0 := by
      linear_combination hGs
    exact (mul_eq_zero.1 this).resolve_left hs0
  have qt : lead (WM W σ) l * t ^ 2 + B (WM W σ) l 0 * t + Cz (WM W σ) l 0 = 0 := by
    have : t * (lead (WM W σ) l * t ^ 2 + B (WM W σ) l 0 * t + Cz (WM W σ) l 0) = 0 := by
      linear_combination hGt
    exact (mul_eq_zero.1 this).resolve_left ht0
  have q2 : lead (WM W σ) l * (s + t) + B (WM W σ) l 0 = 0 := by
    have : (s - t) * (lead (WM W σ) l * (s + t) + B (WM W σ) l 0) = 0 := by
      linear_combination qs - qt
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hst)
  rw [hn] at h3
  have hz : z₃ = 0 := by
    have : lead (WM W σ) l * z₃ = 0 := by linear_combination h3 - q2
    have hl0 : lead (WM W σ) l ≠ 0 := by rintro h; rw [h, zero_mul] at hlead; exact zero_ne_one hlead
    exact (mul_eq_zero.1 this).resolve_left hl0
  rw [hFst, hz, zero_mul]

/-- **the chord law** without linear-coefficient hypotheses. -/
theorem P_add' (h2 : (2 : R) ≠ 0) {s t : A} (hs : constantCoeff s = 0) (ht : constantCoeff t = 0)
    (hs0 : s ≠ 0) (ht0 : t ≠ 0) (hxst : s * wt W t ≠ t * wt W s) (hF0 : subst ![s, t] (F W) ≠ 0) :
    P W h2 s hs hs0 + P W h2 t ht ht0 =
      P W h2 (subst ![s, t] (F W)) (FGL.cc0 _ (FGL.cc_vec2 hs ht) (cc_F W)) hF0 := by
  obtain ⟨l, n, z₃, e, li, hcl, hcn, hcz, hws, hwt, h3, hlead, he, hFst⟩ := chord_data W hs ht
  have hst : s ≠ t := by rintro rfl; exact hxst rfl
  have hG3 : G (WM W σ) z₃ (l * z₃ + n) = 0 :=
    G_third _ (hws ▸ G_wt hs) (hwt ▸ G_wt ht) hst h3
  have hGF : G (WM W σ) (z₃ * e) ((l * z₃ + n) * e) = 0 := by
    rw [G_neg _ _ _ _ he, hG3, mul_zero]
  have hcF : constantCoeff (z₃ * e) = 0 := by simp [hcz]
  have hwF : wt W (z₃ * e) = (l * z₃ + n) * e :=
    G_unique _ hcF (cc_wt hcF) (by simp [hcz, hcl, hcn]) (G_wt hcF) hGF
  have hFne : z₃ * e ≠ 0 := by rw [← hFst]; exact hF0
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
  have hwsne : ι l * ι s + ι n ≠ 0 := hwsK ▸ ι_ne (wt_ne_zero hs hs0)
  have hwtne : ι l * ι t + ι n ≠ 0 := hwtK ▸ ι_ne (wt_ne_zero ht ht0)
  have hnds : -2 + (WK W σ).a₁ * ι s + (WK W σ).a₃ * (ι l * ι s + ι n) ≠ 0 := by
    have := nd_ι W h2 hs (cc_wt (W := W) hs); rwa [hwsK] at this
  have hndt : -2 + (WK W σ).a₁ * ι t + (WK W σ).a₃ * (ι l * ι t + ι n) ≠ 0 := by
    have := nd_ι W h2 ht (cc_wt (W := W) ht); rwa [hwtK] at this
  have hx : ι s / (ι l * ι s + ι n) ≠ ι t / (ι l * ι t + ι n) := by
    intro hxe
    rw [div_eq_div_iff hwsne hwtne, ← hwsK, ← hwtK, ← map_mul, ← map_mul] at hxe
    exact hxst (ι_inj hxe)
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

/-! ## The formal inverse -/

/-- `a₁ t + a₃ w(t) - 1`. -/
noncomputable def dn (t : A) : A := (WM W σ).a₁ * t + (WM W σ).a₃ * wt W t - 1

lemma cc_dn {t : A} (ht : constantCoeff t = 0) : constantCoeff (dn W t) = -1 := by
  simp [dn, ht, cc_wt ht]

/-- `1 / (a₁ t + a₃ w(t) - 1)`. -/
noncomputable def en (t : A) : A := invOfUnit (dn W t) (-1)

lemma dn_mul_en {t : A} (ht : constantCoeff t = 0) : dn W t * en W t = 1 :=
  mul_invOfUnit _ _ (by rw [cc_dn W ht]; simp)

lemma cc_en (t : A) : constantCoeff (en W t) = -1 := by simp [en]

/-- the formal inverse `i(t) = t / (a₁ t + a₃ w(t) - 1)`. -/
noncomputable def negS (t : A) : A := t * en W t

lemma cc_negS {t : A} (ht : constantCoeff t = 0) : constantCoeff (negS W t) = 0 := by
  simp [negS, ht]

lemma en_ne_zero (t : A) : en W t ≠ 0 := by
  intro h; have := cc_en W t; rw [h, map_zero] at this; exact zero_ne_one (neg_eq_zero.1 this.symm).symm |>.elim

lemma negS_ne_zero {t : A} (ht0 : t ≠ 0) : negS W t ≠ 0 := mul_ne_zero ht0 (en_ne_zero W t)

lemma wt_negS {t : A} (ht : constantCoeff t = 0) : wt W (negS W t) = wt W t * en W t := by
  have hc := cc_negS W ht
  apply G_unique _ hc (cc_wt hc) (by simp [cc_wt ht]) (G_wt hc)
  rw [negS, G_neg _ _ _ _ (by have := dn_mul_en W ht; rwa [dn] at this), G_wt ht, mul_zero]

/-- `P(i(t)) = -P(t)`. -/
theorem P_negS (h2 : (2 : R) ≠ 0) {t : A} (ht : constantCoeff t = 0) (ht0 : t ≠ 0) :
    P W h2 (negS W t) (cc_negS W ht) (negS_ne_zero W ht0) = -P W h2 t ht ht0 := by
  simp only [P, pt]
  rw [Point.neg_some, Point.some.injEq]
  have hw : ι (wt W t) ≠ 0 := ι_ne (wt_ne_zero ht ht0)
  have he : ι (en W t) ≠ 0 := ι_ne (en_ne_zero W t)
  have hde : ι (dn W t) * ι (en W t) = 1 := by rw [← map_mul, dn_mul_en W ht, map_one]
  rw [wt_negS W ht, negS, map_mul, map_mul]
  rw [dn, map_sub, map_add, map_mul, map_mul, map_one] at hde
  refine ⟨by field_simp, ?_⟩
  rw [negY]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] at hde ⊢
  field_simp
  linear_combination hde

end Formal

/-! ## Multiples of the generic formal point -/

section Mult
variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)

local notation "A" => MvPowerSeries Unit R
local notation "FG" => formalGroup W
local notation "T" => (X () : MvPowerSeries Unit R)

lemma cc_T' : constantCoeff (T) = 0 := by simp

lemma lin_nmul (n : ℕ) : coeff (Finsupp.single () 1) (FGL.nmul FG n) = n := by
  induction n with
  | zero => simp [FGL.nmul]
  | succ n ih =>
    show coeff (Finsupp.single () 1) (subst ![T, FGL.nmul FG n] (F W)) = _
    rw [lin_subst2 _ _ _ cc_T' (FGL.cc_nmul _ n), lin_F, lin_F, ih, lin_X, if_pos rfl]
    push_cast; ring

lemma nmul_ne_zero {n : ℕ} (hn : (n : R) ≠ 0) : FGL.nmul FG n ≠ 0 := by
  intro h; have := lin_nmul W n; rw [h, map_zero] at this; exact hn this.symm

lemma nmul_succ' (n : ℕ) : FGL.nmul FG (n + 1) = subst ![T, FGL.nmul FG n] (F W) := rfl

lemma nmul_one' : FGL.nmul FG 1 = T := FGL.ev_T_zero FG

lemma ne_of_lin {s t : A} (h : coeff (Finsupp.single () 1) s ≠ coeff (Finsupp.single () 1) t) : s ≠ t :=
  fun e => h (by rw [e])

/-- **`n • P(T) = P([n]T)`**. -/
theorem nsmul_P (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) (N : ℕ)
    (hN : ∀ m, 1 ≤ m → m ≤ N → FGL.nmul FG m ≠ 0) :
    ∀ n (hn : 1 ≤ n) (hnN : n ≤ N), n • P W h2 T cc_T' (lin_ne_zero (lin_X' ())) =
      P W h2 (FGL.nmul FG n) (FGL.cc_nmul _ n) (hN n hn hnN) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hnN
  have hT0 : (T) ≠ 0 := lin_ne_zero (lin_X' ())
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · interval_cases n
    · rw [one_nsmul]; exact P_congr W h2 (nmul_one' W).symm _ _ _ _
    · -- `n = 2`: doubling through the formal inverse
      set u := FGL.nmul FG 2
      have hu : constantCoeff u = 0 := FGL.cc_nmul _ 2
      have hu0 : u ≠ 0 := hN 2 (by omega) hnN
      set i := negS W (T)
      have hi := cc_negS W (cc_T' (R := R))
      have hi0 : i ≠ 0 := negS_ne_zero W hT0
      have hu2 : u = subst ![T, T] (F W) := by
        rw [show u = FGL.nmul FG (1 + 1) from rfl, nmul_succ', nmul_one' W]
      -- `F(T, i) = 0`
      have hTi : (T) ≠ i := by
        apply ne_of_lin
        rw [lin_X, if_pos rfl]
        show (1 : R) ≠ coeff (Finsupp.single () 1) (T * en W T)
        rw [lin_mul, lin_X, if_pos rfl, cc_T', cc_en]; simp only [zero_mul, zero_add, mul_neg, mul_one]
        intro h; apply h2; linear_combination h
      have hFTi : subst ![T, i] (F W) = 0 := by
        apply F_eq_zero_of_x_eq W cc_T' hi hT0 hi0 hTi
        rw [wt_negS W cc_T']; show T * (wt W T * en W T) = (T * en W T) * wt W T; ring
      -- `F(u, i) = T`
      have hFui : subst ![u, i] (F W) = T := by
        have := FGL.assoc_ev FG T T i cc_T' cc_T' hi
        simp only [FGL.ev, formalGroup_toPowerSeries] at this
        rw [hu2, this, hFTi]
        exact FGL.ev_T_zero FG
      -- nondegeneracy
      have hxui : u * wt W i ≠ i * wt W u := by
        intro h
        rw [wt_negS W cc_T'] at h
        have h' : (T) * wt W u = u * wt W T := by
          apply mul_right_cancel₀ (en_ne_zero W (T))
          calc (T) * wt W u * en W T = (T * en W T) * wt W u := by ring
            _ = u * (wt W T * en W T) := h.symm
            _ = _ := by ring
        have hTu : (T) ≠ u := by
          apply ne_of_lin; rw [lin_X, if_pos rfl, lin_nmul]; push_cast
          intro h; apply one_ne_zero (α := R); linear_combination -h
        have := F_eq_zero_of_x_eq W cc_T' hu hT0 hu0 hTu h'
        exact nmul_ne_zero W (n := 3) (by exact_mod_cast h3) this
      have hFui0 : subst ![u, i] (F W) ≠ 0 := by rw [hFui]; exact hT0
      have key := P_add' W h2 hu hi hu0 hi0 hxui hFui0
      rw [P_negS W h2 cc_T' hT0, P_congr W h2 hFui _ cc_T' _ hT0] at key
      rw [two_nsmul]
      rw [← sub_eq_add_neg, sub_eq_iff_eq_add] at key
      rw [← key]
  · -- `n = m + 1 ≥ 3`: chord with `T`
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have ihm := ih m (by omega) (by omega) (by omega)
    have hm0 : FGL.nmul FG m ≠ 0 := hN m (by omega) (by omega)
    have hcm := FGL.cc_nmul FG m
    have hF0 : subst ![T, FGL.nmul FG m] (F W) ≠ 0 := hN (m + 1) hn hnN
    have hTm : (T) ≠ FGL.nmul FG m := by
      intro h
      have e1 : m • P W h2 T cc_T' hT0 = P W h2 T cc_T' hT0 := by
        rw [ihm]; exact P_congr W h2 h.symm _ _ _ _
      have e2 : (m - 1) • P W h2 T cc_T' hT0 = 0 := by
        have : m • P W h2 T cc_T' hT0 = (m - 1) • P W h2 T cc_T' hT0 + P W h2 T cc_T' hT0 := by
          rw [← succ_nsmul]; congr 1; omega
        rw [this] at e1; simpa using e1
      rw [ih (m - 1) (by omega) (by omega) (by omega)] at e2
      exact Point.some_ne_zero _ e2
    have hx : (T) * wt W (FGL.nmul FG m) ≠ FGL.nmul FG m * wt W T := by
      intro h
      exact hF0 (F_eq_zero_of_x_eq W cc_T' hcm hT0 hm0 hTm h)
    rw [succ_nsmul, ihm, add_comm, P_add' W h2 cc_T' hcm hT0 hm0 hx hF0]
    exact P_congr W h2 (nmul_succ' W m).symm _ _ _ _

end Mult

end HeightEll
