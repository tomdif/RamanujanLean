/-
# `[n]` is an endomorphism; homomorphisms and the invariant differential

* `nm n a := [n](a)`. `[n+1](a) = F(a, [n](a))` and `[n](F(a,b)) = F([n]a, [n]b)` (commutative `F`).
* For a homomorphism `f : G₁ → G₂` (`f(G₁(X,Y)) = G₂(f X, f Y)`):
  `f'(T)·Ψ_{G₁}(T) = Ψ_{G₂}(f(T))·f'(0)`. So `f'(0) = 0 ⇒ f' = 0`.
-/
import RamanujanTau.FormalGroupLayer.CharP

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace FGL
open MvPowerSeries

variable {R : Type*} [CommRing R] (F : FormalGroup R)

local notation "Fs" => (F.toPowerSeries : MvPowerSeries (Fin 2) R)

/-- `[n](a)`. -/
noncomputable def nm {β : Type*} (n : ℕ) (a : MvPowerSeries β R) : MvPowerSeries β R :=
  subst (fun _ : Unit => a) (nmul F n)

lemma h1 {β : Type*} {a : MvPowerSeries β R} (ha : constantCoeff a = 0) :
    ∀ s : Unit, constantCoeff ((fun _ : Unit => a) s) = 0 := fun _ => ha

lemma cc_nm {β : Type*} [Finite β] (n : ℕ) {a : MvPowerSeries β R} (ha : constantCoeff a = 0) :
    constantCoeff (nm F n a) = 0 := cc0 _ (h1 ha) (cc_nmul F n)

lemma nm_zero {β : Type*} [Finite β] {a : MvPowerSeries β R} (ha : constantCoeff a = 0) : nm F 0 a = 0 :=
  s0 _ (h1 ha)

lemma nm_succ {β : Type*} [Finite β] (n : ℕ) {a : MvPowerSeries β R} (ha : constantCoeff a = 0) :
    nm F (n + 1) a = ev F a (nm F n a) := by
  show subst _ (ev F T (nmul F n)) = _
  rw [subst_ev F _ _ _ cc_T (cc_nmul F n) (h1 ha), sX _ (h1 ha) ()]; rfl

/-- rearrangement `(a+b)+(c+d) = (a+c)+(b+d)` in a commutative formal group. -/
lemma ev_four [F.IsComm] {β : Type*} [Finite β] {a b c d : MvPowerSeries β R} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) (hc : constantCoeff c = 0) (hd : constantCoeff d = 0) :
    ev F (ev F a b) (ev F c d) = ev F (ev F a c) (ev F b d) := by
  rw [assoc_ev F _ _ _ ha hb (cc_ev F hc hd), ← assoc_ev F _ _ _ hb hc hd, ev_comm F b c hb hc,
    assoc_ev F _ _ _ hc hb hd, ← assoc_ev F _ _ _ ha hc (cc_ev F hb hd)]

/-- **`[n]` is an endomorphism**. -/
theorem nm_ev [F.IsComm] {β : Type*} [Finite β] (n : ℕ) {a b : MvPowerSeries β R} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : nm F n (ev F a b) = ev F (nm F n a) (nm F n b) := by
  induction n with
  | zero => rw [nm_zero F (cc_ev F ha hb), nm_zero F ha, nm_zero F hb, ev_zero_zero]
  | succ n ih =>
    rw [nm_succ F n (cc_ev F ha hb), ih, nm_succ F n ha, nm_succ F n hb,
      ev_four F ha hb (cc_nm F n ha) (cc_nm F n hb)]

/-- substituting the two variables of a two-variable series by `T, 0`. -/
lemma cc_T0 : ∀ s, constantCoeff ((![T, 0] : Fin 2 → MvPowerSeries Unit R) s) = 0 :=
  cc_vec2 cc_T (by simp)

/-- **homomorphism differential**: if `f(G₁(X,Y)) = G₂(f X, f Y)` then
`f'(T)·Ψ_{G₁}(T) = Ψ_{G₂}(f(T)) · C(f'(0))`. -/
theorem hom_invariant (G₁ G₂ : FormalGroup R) (f : MvPowerSeries Unit R) (hf : constantCoeff f = 0)
    (hhom : subst (fun _ : Unit => ev G₁ (X 0 : MvPowerSeries (Fin 2) R) (X 1)) f =
      ev G₂ (subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) f)
        (subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) f)) :
    pd () f * Ψ G₁ (T : MvPowerSeries Unit R) =
      Ψ G₂ f * C (coeff (Finsupp.single () 1) f) := by
  have X0 : constantCoeff (X 0 : MvPowerSeries (Fin 2) R) = 0 := by simp
  have X1 : constantCoeff (X 1 : MvPowerSeries (Fin 2) R) = 0 := by simp
  have hG := cc_ev G₁ X0 X1
  have hf0 : constantCoeff (subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) f) = 0 := cc0 _ (h1 X0) hf
  have hf1 : constantCoeff (subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) f) = 0 := cc0 _ (h1 X1) hf
  have h := congrArg (pd (1 : Fin 2)) hhom
  rw [pd_subst (h1 hG), Fintype.sum_unique, pd_ev G₂ _ _ hf0 hf1, pd_subst (h1 X0), pd_subst (h1 X1),
    Fintype.sum_unique, Fintype.sum_unique] at h
  simp only [pd_X', show (0 : Fin 2) ≠ 1 by decide, if_false, if_true, mul_zero, zero_add, mul_one] at h
  -- now set `X₀ ↦ T`, `X₁ ↦ 0`
  have h2 := congrArg (subst (![T, 0] : Fin 2 → MvPowerSeries Unit R)) h
  have hv := cc_T0 (R := R)
  rw [subst_mul (hs hv), subst_mul (hs hv)] at h2
  -- evaluate the pieces
  have eG : subst (![T, 0] : Fin 2 → MvPowerSeries Unit R) (ev G₁ (X 0) (X 1)) = T := by
    rw [subst_ev G₁ _ _ _ X0 X1 hv, sX _ hv, sX _ hv]; exact ev_T_zero G₁
  have e0 : subst (![T, 0] : Fin 2 → MvPowerSeries Unit R) (subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) f) = f := by
    rw [ss _ _ (h1 X0) hv]
    have : (fun _ : Unit => subst (![T, 0] : Fin 2 → MvPowerSeries Unit R) (X 0 : MvPowerSeries (Fin 2) R)) =
        X := by funext s; rw [sX _ hv]; rfl
    rw [this, subst_self]; rfl
  have e1 : subst (![T, 0] : Fin 2 → MvPowerSeries Unit R) (subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) f) = 0 := by
    rw [ss _ _ (h1 X1) hv]
    have : (fun _ : Unit => subst (![T, 0] : Fin 2 → MvPowerSeries Unit R) (X 1 : MvPowerSeries (Fin 2) R)) =
        fun _ => 0 := by funext s; rw [sX _ hv]; rfl
    rw [this, subst_zeros, hf, map_zero]
  have epd1 : subst (![T, 0] : Fin 2 → MvPowerSeries Unit R) (subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) (pd () f)) =
      C (coeff (Finsupp.single () 1) f) := by
    rw [ss _ _ (h1 X1) hv]
    have : (fun _ : Unit => subst (![T, 0] : Fin 2 → MvPowerSeries Unit R) (X 1 : MvPowerSeries (Fin 2) R)) =
        fun _ => 0 := by funext s; rw [sX _ hv]; rfl
    rw [this, subst_zeros, ← coeff_zero_eq_constantCoeff_apply, coeff_pd, zero_add]
    simp
  have eL : subst (![T, 0] : Fin 2 → MvPowerSeries Unit R) (subst (fun _ : Unit => ev G₁ (X 0 : MvPowerSeries (Fin 2) R) (X 1)) (pd () f)) =
      pd () f := by
    rw [ss _ _ (h1 hG) hv]
    have : (fun _ : Unit => subst (![T, 0] : Fin 2 → MvPowerSeries Unit R) (ev G₁ (X 0 : MvPowerSeries (Fin 2) R) (X 1))) =
        X := by funext s; rw [eG]
    rw [this, subst_self]; rfl
  have eΨ1 : subst (![T, 0] : Fin 2 → MvPowerSeries Unit R) (pd 1 (G₁.toPowerSeries)) = Ψ G₁ T := rfl
  have eΨ2 : subst (![T, 0] : Fin 2 → MvPowerSeries Unit R)
      (subst ![subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) f,
        subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) f] (pd 1 G₂.toPowerSeries)) = Ψ G₂ f := by
    rw [ss _ _ (cc_vec2 hf0 hf1) hv, Ψ]
    congr 1; funext s; fin_cases s
    · exact e0
    · exact e1
  have epdG : subst (![T, 0] : Fin 2 → MvPowerSeries Unit R) (pd 1 (ev G₁ (X 0 : MvPowerSeries (Fin 2) R) (X 1))) =
      Ψ G₁ T := by
    rw [pd_ev G₁ _ _ X0 X1, pd_X', pd_X']
    simp only [show (0 : Fin 2) ≠ 1 by decide, if_false, if_true, mul_zero, zero_add, mul_one]
    rw [ss _ _ (cc_vec2 X0 X1) hv]
    congr 1; funext s; fin_cases s
    · exact sX _ hv 0
    · exact sX _ hv 1
  rw [eL, epdG, eΨ2, epd1] at h2
  exact h2

end FGL
