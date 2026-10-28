/-
# Translates of the formal parameter and `S`-invariant integral series

For the short curve `W = shortO a b` over `𝒪` with formal group `F = F_W`, and `h ∈ 𝔪`:
* `Fh h = F(z, h) ∈ 𝒪⟦z⟧`, `wh h = w(F(z, h))`, `vh h = v(F(z, h))`, so `wh h = (Fh h)³ · vh h`;
* translation by `h' ∈ 𝔪` (`Lubin.trs`) sends `Fh h ↦ Fh (h' +_F h)` and `wh h ↦ wh (h' +_F h)`.

For a finite subgroup `S ⊆ 𝔪` we define the integral series
* `Wall = ∏_{h∈S} w(F(z,h))`, `Vall = ∏_{h∈S} v(F(z,h))`, `Wst = ∏_{h∈S, h≠0} w(F(z,h))`,
* `Dser = Σ_{h∈S} ∏_{h'∈S, h'≠h} w(F(z,h'))`,
and prove `Wall = π³ · Vall`, `Wall = w · Wst`, and that `Wall`, `Vall`, `Dser` are `S`-invariant.
-/
import RamanujanTau.VeluLubin.Final

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VeluDescent
open MvPowerSeries EllipticFormal VeluLubin

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K]

local notation "𝒪" => CanonicalIsogeny.integers K

variable (a b : ↥(CanonicalIsogeny.integers K))

local notation "Fo" => formalGroup (shortO a b)

/-- `F(z, h)`. -/
noncomputable def Fh (h : 𝒪) : MvPowerSeries Unit 𝒪 := Lubin.E2 (formalGroup (shortO a b)) (X ()) (C h)

/-- `w(F(z, h))`. -/
noncomputable def wh (h : 𝒪) : MvPowerSeries Unit 𝒪 :=
  Lubin.E (fun _ : Unit => Fh a b h) (w (shortO a b) : MvPowerSeries Unit 𝒪)

/-- `v(F(z, h))`. -/
noncomputable def vh (h : 𝒪) : MvPowerSeries Unit 𝒪 :=
  Lubin.E (fun _ : Unit => Fh a b h) (v (shortO a b) : MvPowerSeries Unit 𝒪)

variable {a b}

lemma cc_Fh {h : 𝒪} (hh : IsTopologicallyNilpotent h) : constantCoeff (Fh a b h) = h := by
  rw [Fh, Lubin.cc_E2 (Lubin.tn_X ()) (Lubin.tn_C hh), constantCoeff_X, constantCoeff_C,
    Lubin.zero_padd hh]

lemma tn_Fh {h : 𝒪} (hh : IsTopologicallyNilpotent h) : Lubin.TN (Fh a b h) := by
  rw [Lubin.TN, cc_Fh hh]; exact hh

lemma adm_Fh {h : 𝒪} (hh : IsTopologicallyNilpotent h) : Lubin.Adm (fun _ : Unit => Fh a b h) :=
  fun _ => tn_Fh hh

lemma wh_eq {h : 𝒪} (hh : IsTopologicallyNilpotent h) : wh a b h = Fh a b h ^ 3 * vh a b h := by
  rw [wh, vh, show (w (shortO a b) : MvPowerSeries Unit 𝒪) = X () ^ 3 * v (shortO a b) from
    w_eq_X3_mul_v _, Lubin.E_mul (adm_Fh hh), Lubin.E_pow (adm_Fh hh), Lubin.E_X]

lemma Fh_zero : Fh a b 0 = X () := by
  rw [Fh, map_zero, Lubin.E2_zero (Lubin.tn_X ())]

lemma X_fun : (fun _ : Unit => (X () : MvPowerSeries Unit 𝒪)) = X := by
  funext u; rfl

lemma wh_zero : wh a b 0 = (w (shortO a b) : MvPowerSeries Unit 𝒪) := by
  rw [wh, Fh_zero, X_fun, Lubin.E_X_self]

lemma vh_zero : vh a b 0 = (v (shortO a b) : MvPowerSeries Unit 𝒪) := by
  rw [vh, Fh_zero, X_fun, Lubin.E_X_self]

lemma trs_eq (h : 𝒪) : Lubin.trs (F := Fo) () h = fun _ : Unit => Fh a b h := by
  funext u
  cases u
  rw [Lubin.trs, Function.update_self]; rfl

lemma adm_trs {h : 𝒪} (hh : IsTopologicallyNilpotent h) : Lubin.Adm (Lubin.trs (F := Fo) () h) := by
  rw [trs_eq]; exact adm_Fh hh

/-- translation: `F(F(z, h'), h) = F(z, h' + h)`. -/
lemma E_trs_Fh {h h' : 𝒪} (hh : IsTopologicallyNilpotent h) (hh' : IsTopologicallyNilpotent h') :
    Lubin.E (Lubin.trs (F := Fo) () h') (Fh a b h) = Fh a b (Lubin.padd Fo h' h) := by
  rw [trs_eq]
  show Lubin.E (fun _ : Unit => Fh a b h') (Lubin.E2 Fo (X ()) (C h)) =
    Lubin.E2 Fo (X ()) (C (Lubin.padd Fo h' h))
  rw [Lubin.E_E2 (adm_Fh hh') (Lubin.tn_X ()) (Lubin.tn_C hh), Lubin.E_X, Lubin.E_C]
  show Lubin.E2 Fo (Lubin.E2 Fo (X ()) (C h')) (C h) = _
  rw [Lubin.E2_assoc (Lubin.tn_X ()) (Lubin.tn_C hh') (Lubin.tn_C hh), Lubin.E2_C hh' hh]

lemma E_trs_wh {h h' : 𝒪} (hh : IsTopologicallyNilpotent h) (hh' : IsTopologicallyNilpotent h') :
    Lubin.E (Lubin.trs (F := Fo) () h') (wh a b h) = wh a b (Lubin.padd Fo h' h) := by
  rw [wh, Lubin.E_E (adm_Fh hh) (adm_trs hh'), wh]
  congr 1; funext u; exact E_trs_Fh hh hh'

lemma E_trs_vh {h h' : 𝒪} (hh : IsTopologicallyNilpotent h) (hh' : IsTopologicallyNilpotent h') :
    Lubin.E (Lubin.trs (F := Fo) () h') (vh a b h) = vh a b (Lubin.padd Fo h' h) := by
  rw [vh, Lubin.E_E (adm_Fh hh) (adm_trs hh'), vh]
  congr 1; funext u; exact E_trs_Fh hh hh'

/-! ### The invariant series attached to a finite subgroup -/

variable (S : Lubin.FinSub (formalGroup (shortO a b)))

/-- `∏_{h∈S} w(F(z,h))`. -/
noncomputable def Wall : MvPowerSeries Unit 𝒪 := ∏ h ∈ S.H, wh a b h

/-- `∏_{h∈S} v(F(z,h))`. -/
noncomputable def Vall : MvPowerSeries Unit 𝒪 := ∏ h ∈ S.H, vh a b h

/-- `∏_{h∈S, h≠0} w(F(z,h))`. -/
noncomputable def Wst : MvPowerSeries Unit 𝒪 := ∏ h ∈ S.H.erase 0, wh a b h

/-- `Σ_{h∈S} ∏_{h'≠h} w(F(z,h'))`. -/
noncomputable def Dser : MvPowerSeries Unit 𝒪 :=
  ∑ h ∈ S.H, ∏ h' ∈ S.H, (if h' = h then 1 else wh a b h')

lemma Wall_eq_w_mul : Wall S = (w (shortO a b) : MvPowerSeries Unit 𝒪) * Wst S := by
  rw [Wall, Wst, ← Finset.mul_prod_erase _ _ S.zero_mem, wh_zero]

lemma Wall_eq_pis : Wall S = Lubin.pis S ^ 3 * Vall S := by
  rw [Wall, Vall, Finset.prod_congr rfl (fun h hh => wh_eq (S.tn h hh)), Finset.prod_mul_distrib,
    Finset.prod_pow]
  rfl

lemma isUnit_vh {h : 𝒪} (hh : ‖(h : K)‖ < 1) : IsUnit (vh a b h) := by
  rw [isUnit_iff_constantCoeff, vh, Lubin.cc_E (adm_Fh (tn_of_norm hh))]
  simp only [cc_Fh (tn_of_norm hh)]
  exact isUnit_pt_v (K := K) a b hh

lemma isUnit_Vall : IsUnit (Vall S) := by
  rw [Vall, IsUnit.prod_iff]
  exact fun h hh => isUnit_vh (norm_lt_one_of_tn (S.tn h hh))

/-! ### Invariance -/

lemma sum_translate {M : Type*} [AddCommMonoid M] (f : 𝒪 → M) {c : 𝒪} (hc : c ∈ S.H) :
    ∑ h ∈ S.H, f (Lubin.padd Fo h c) = ∑ h ∈ S.H, f h := by
  have := S.prod_translate (fun h => Multiplicative.ofAdd (f h)) hc
  simpa using congrArg Multiplicative.toAdd this

lemma padd_comm' {x y : 𝒪} (hx : x ∈ S.H) (hy : y ∈ S.H) :
    Lubin.padd Fo x y = Lubin.padd Fo y x := Lubin.padd_comm (S.tn x hx) (S.tn y hy)

lemma inv_prod (f : 𝒪 → MvPowerSeries Unit 𝒪) (hf : ∀ h ∈ S.H, ∀ c ∈ S.H,
    Lubin.E (Lubin.trs (F := Fo) () c) (f h) = f (Lubin.padd Fo c h)) :
    Lubin.Inv S () (∏ h ∈ S.H, f h) := by
  intro c hc
  rw [← Lubin.EH_apply (adm_trs (S.tn c hc)), map_prod]
  simp only [Lubin.EH_apply]
  rw [Finset.prod_congr rfl (fun h hh => hf h hh c hc)]
  rw [Finset.prod_congr rfl (fun h hh => by rw [padd_comm' S hc hh])]
  exact S.prod_translate f hc

lemma inv_Wall : Lubin.Inv S () (Wall S) :=
  inv_prod S _ (fun h hh c hc => E_trs_wh (S.tn h hh) (S.tn c hc))

lemma inv_Vall : Lubin.Inv S () (Vall S) :=
  inv_prod S _ (fun h hh c hc => E_trs_vh (S.tn h hh) (S.tn c hc))

lemma inv_Dser : Lubin.Inv S () (Dser S) := by
  intro c hc
  have hE := adm_trs (a := a) (b := b) (S.tn c hc)
  rw [Dser, ← Lubin.EH_apply hE, map_sum]
  simp only [map_prod]
  have e1 : ∀ h ∈ S.H, ∀ h' ∈ S.H, Lubin.EH hE (if h' = h then 1 else wh a b h') =
      if Lubin.padd Fo h' c = Lubin.padd Fo h c then 1 else wh a b (Lubin.padd Fo h' c) := by
    intro h hh h' hh'
    by_cases e : h' = h
    · rw [if_pos e, if_pos (by rw [e]), map_one]
    · rw [if_neg e, if_neg (fun e' => e (S.add_right_cancel hc hh' hh e')), Lubin.EH_apply,
        E_trs_wh (S.tn h' hh') (S.tn c hc), padd_comm' S hc hh']
  rw [Finset.sum_congr rfl (fun h hh => Finset.prod_congr rfl (fun h' hh' => e1 h hh h' hh'))]
  rw [Finset.sum_congr rfl (fun h hh => S.prod_translate
    (fun y => if y = Lubin.padd Fo h c then 1 else wh a b y) hc)]
  exact sum_translate S (fun x => ∏ y ∈ S.H, if y = x then 1 else wh a b y) hc

end VeluDescent
