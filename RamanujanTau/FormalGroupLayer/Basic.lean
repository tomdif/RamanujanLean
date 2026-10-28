/-
# Formal group laws: substitution bookkeeping and `F(X, 0) = X`

Mathlib's `FormalGroup` records only the axioms. Here:
* helper lemmas for substitutions with zero constant coefficients;
* `F(X, 0) = X` and `F(0, X) = X`: `f(X) = F(X,0)` is idempotent under composition (associativity) and
  has linear coefficient `1`, so its compositional inverse forces `f = X`.
-/
import RamanujanTau.FormalGroupLayer.Chain

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace FGL
open MvPowerSeries

variable {R : Type*} [CommRing R]

section Subst
variable {α β γ : Type*} [Finite α] [Finite β] [Finite γ]

lemma hs {a : α → MvPowerSeries β R} (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a :=
  hasSubst_of_constantCoeff_zero ha

lemma ss (a : α → MvPowerSeries β R) (b : β → MvPowerSeries γ R) (ha : ∀ s, constantCoeff (a s) = 0)
    (hb : ∀ s, constantCoeff (b s) = 0) (f : MvPowerSeries α R) :
    subst b (subst a f) = subst (fun s => subst b (a s)) f :=
  subst_comp_subst_apply (hs ha) (hs hb) f

lemma cc0 (a : α → MvPowerSeries β R) (ha : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries α R}
    (hf : constantCoeff f = 0) : constantCoeff (subst a f) = 0 :=
  constantCoeff_subst_eq_zero (hs ha) ha hf

/-- the constant coefficient survives substitution of series without constant term. -/
lemma cc_subst (a : α → MvPowerSeries β R) (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries α R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have h : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  rw [h, subst_add (hs ha), subst_C, map_add, cc0 a ha (by simp), add_zero]
  simp

lemma s0 (a : α → MvPowerSeries β R) (ha : ∀ s, constantCoeff (a s) = 0) :
    subst a (0 : MvPowerSeries α R) = 0 := by
  rw [← coe_substAlgHom (hs ha)]; exact map_zero _

lemma sX (a : α → MvPowerSeries β R) (ha : ∀ s, constantCoeff (a s) = 0) (s : α) :
    subst a (X s : MvPowerSeries α R) = a s := subst_X (hs ha) s

end Subst

variable (F : FormalGroup R)

local notation "Fs" => (F.toPowerSeries : MvPowerSeries (Fin 2) R)

/-- the one-variable series `T`. -/
noncomputable abbrev T : MvPowerSeries Unit R := X ()

lemma cc_T : constantCoeff (T : MvPowerSeries Unit R) = 0 := by simp

lemma cc_vec2 {β : Type*} {a b : MvPowerSeries β R} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    ∀ s, constantCoeff (![a, b] s) = 0 := by
  intro s; fin_cases s <;> simpa

lemma cc_vec3 {β : Type*} {a b c : MvPowerSeries β R} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) (hc : constantCoeff c = 0) : ∀ s, constantCoeff (![a, b, c] s) = 0 := by
  intro s; fin_cases s <;> simpa

lemma cc_F : constantCoeff Fs = 0 := F.zero_constantCoeff

/-- `F(a, b)` for one-or-more-variable `a, b`. -/
noncomputable def ev {β : Type*} (a b : MvPowerSeries β R) : MvPowerSeries β R := subst ![a, b] Fs

lemma cc_ev {β : Type*} [Finite β] {a b : MvPowerSeries β R} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : constantCoeff (ev F a b) = 0 :=
  cc0 _ (cc_vec2 ha hb) (cc_F F)

/-- substituting into `F(a, b)`. -/
lemma subst_ev {β γ : Type*} [Finite β] [Finite γ] (a b : MvPowerSeries β R) (c : β → MvPowerSeries γ R)
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) (hc : ∀ s, constantCoeff (c s) = 0) :
    subst c (ev F a b) = ev F (subst c a) (subst c b) := by
  rw [ev, ss _ _ (cc_vec2 ha hb) hc, ev]
  congr 1; funext s; fin_cases s <;> rfl

/-- associativity in `ev` form, specialised along any substitution. -/
lemma assoc_ev {β : Type*} [Finite β] (a b c : MvPowerSeries β R) (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) (hc : constantCoeff c = 0) :
    ev F (ev F a b) c = ev F a (ev F b c) := by
  have h := congrArg (subst ![a, b, c]) F.assoc
  have hv := cc_vec3 ha hb hc
  have h01 : constantCoeff (subst ![X 0, X 1] Fs : MvPowerSeries (Fin 3) R) = 0 :=
    cc0 _ (cc_vec2 (by simp) (by simp)) (cc_F F)
  have h12 : constantCoeff (subst ![X 1, X 2] Fs : MvPowerSeries (Fin 3) R) = 0 :=
    cc0 _ (cc_vec2 (by simp) (by simp)) (cc_F F)
  rw [ss _ _ (cc_vec2 h01 (by simp)) hv, ss _ _ (cc_vec2 (by simp) h12) hv] at h
  have hX0 : constantCoeff (X 0 : MvPowerSeries (Fin 3) R) = 0 := by simp
  have hX1 : constantCoeff (X 1 : MvPowerSeries (Fin 3) R) = 0 := by simp
  have hX2 : constantCoeff (X 2 : MvPowerSeries (Fin 3) R) = 0 := by simp
  have e01 : subst ![a, b, c] (subst ![(X 0 : MvPowerSeries (Fin 3) R), X 1] Fs) = ev F a b := by
    rw [ss _ _ (cc_vec2 hX0 hX1) hv, ev]
    congr 1; funext t; fin_cases t
    · exact sX _ hv 0
    · exact sX _ hv 1
  have e12 : subst ![a, b, c] (subst ![(X 1 : MvPowerSeries (Fin 3) R), X 2] Fs) = ev F b c := by
    rw [ss _ _ (cc_vec2 hX1 hX2) hv, ev]
    congr 1; funext t; fin_cases t
    · exact sX _ hv 1
    · exact sX _ hv 2
  have e1 : (fun s => subst ![a, b, c] (![(subst ![X 0, X 1] Fs : MvPowerSeries (Fin 3) R), X 2] s)) =
      ![ev F a b, c] := by
    funext s; fin_cases s
    · exact e01
    · exact sX _ hv 2
  have e2 : (fun s => subst ![a, b, c] (![(X 0 : MvPowerSeries (Fin 3) R), subst ![X 1, X 2] Fs] s)) =
      ![a, ev F b c] := by
    funext s; fin_cases s
    · exact sX _ hv 0
    · exact e12
  rw [e1, e2] at h
  exact h


section Zero
variable {α β : Type*} [Finite α] [Finite β]

/-- substituting `0` everywhere leaves the constant term. -/
lemma subst_zeros (g : MvPowerSeries α R) :
    subst (fun _ : α => (0 : MvPowerSeries β R)) g = C (constantCoeff g) := by
  have h0 : ∀ s : α, constantCoeff ((fun _ : α => (0 : MvPowerSeries β R)) s) = 0 := fun _ => by simp
  have h : g = C (constantCoeff g) + (g - C (constantCoeff g)) := by ring
  conv_lhs => rw [h]
  rw [subst_add (hs h0), subst_C]
  suffices subst (fun _ : α => (0 : MvPowerSeries β R)) (g - C (constantCoeff g)) = 0 by rw [this, add_zero]
  have hg : 1 ≤ (g - C (constantCoeff g)).order := by
    rw [one_le_order_iff_constCoeff_eq_zero]; simp
  have := le_order_subst (hs h0) (g - C (constantCoeff g))
  have htop : (⨅ _ : α, (0 : MvPowerSeries β R).order) * (g - C (constantCoeff g)).order = ⊤ := by
    simp only [order_zero, iInf_top]
    exact ENat.top_mul (ne_of_gt (lt_of_lt_of_le zero_lt_one hg))
  rw [htop, top_le_iff, order_eq_top_iff] at this
  exact this

end Zero

lemma ev_zero_zero {β : Type*} [Finite β] : ev F (0 : MvPowerSeries β R) 0 = 0 := by
  have : (![0, 0] : Fin 2 → MvPowerSeries β R) = fun _ => 0 := by funext s; fin_cases s <;> rfl
  rw [ev, this, subst_zeros, cc_F, map_zero]

/-- the linear coefficient of `F(T, 0)` is `1`. -/
lemma coeff_one_ev_T_zero :
    coeff (Finsupp.single () 1) (ev F (T : MvPowerSeries Unit R) 0) = 1 := by
  have hv := cc_vec2 (cc_T (R := R)) (by simp : constantCoeff (0 : MvPowerSeries Unit R) = 0)
  have hd := pd_subst hv () Fs
  have h1 := congrArg constantCoeff hd
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pd] at h1
  simp only [zero_add, Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, mul_one] at h1
  rw [ev, h1, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_mul, pd_X, if_true]
  rw [show pd () (0 : MvPowerSeries Unit R) = 0 from map_zero (pdDer (R := R) ())]
  simp only [map_one, mul_one, map_zero, mul_zero, add_zero]
  rw [cc_subst _ hv, ← coeff_zero_eq_constantCoeff_apply, coeff_pd, zero_add]
  simp [F.lin_coeff_X]

/-- **`F(X, 0) = X`**. -/
theorem ev_T_zero : ev F (T : MvPowerSeries Unit R) 0 = T := by
  set f : PowerSeries R := ev F (T : MvPowerSeries Unit R) 0 with hf
  have hf0 : PowerSeries.constantCoeff f = 0 := cc_ev F cc_T (by simp)
  have hu : IsUnit (PowerSeries.coeff 1 f) := by
    rw [show PowerSeries.coeff 1 f = coeff (Finsupp.single () 1) (ev F (T : MvPowerSeries Unit R) 0) from rfl,
      coeff_one_ev_T_zero]; exact isUnit_one
  have h0 : ∀ s : Unit, constantCoeff ((fun _ : Unit => (f : MvPowerSeries Unit R)) s) = 0 := fun _ => hf0
  -- idempotence `f(f(T)) = f(T)`
  have hidem : PowerSeries.subst f f = f := by
    show subst (fun _ => (f : MvPowerSeries Unit R)) (ev F T 0) = f
    rw [subst_ev F _ _ _ cc_T (by simp) h0, sX _ h0 (), s0 _ h0]
    show ev F (ev F (T : MvPowerSeries Unit R) 0) 0 = ev F T 0
    rw [assoc_ev F _ _ _ cc_T (by simp) (by simp), ev_zero_zero]
  set g := PowerSeries.substInvOfIsUnit f hu
  have hgf : PowerSeries.subst f g = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_left f hf0 hu
  have hg0 : ∀ s : Unit, constantCoeff ((fun _ : Unit => (g : MvPowerSeries Unit R)) s) = 0 :=
    fun _ => PowerSeries.constantCoeff_substInvOfIsUnit f hu
  -- `g(f(f)) = (g ∘ f)(f) = f` and `g(f(f)) = g(f) = T`
  have e1 : PowerSeries.subst f (PowerSeries.subst f g) = f := by
    rw [hgf]; exact PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hf0)
  have e2 : PowerSeries.subst f (PowerSeries.subst f g) = PowerSeries.subst (PowerSeries.subst f f) g := by
    show subst (fun _ => (f : MvPowerSeries Unit R)) (subst (fun _ => (f : MvPowerSeries Unit R)) g) =
      subst (fun _ => subst (fun _ => (f : MvPowerSeries Unit R)) (f : MvPowerSeries Unit R)) g
    rw [ss _ _ h0 h0]
  rw [e2, hidem, hgf] at e1
  exact e1.symm

end FGL
