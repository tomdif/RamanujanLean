/-
# The invariant differential and `[n]^* ω = n ω`

With `Ψ(u) := (∂₂F)(u, 0)` (so `ω = dT/Ψ(T)`):
* (I) `Ψ(F(a,b)) = (∂₂F)(a,b) · Ψ(b)` (differentiate associativity in the last variable at `0`);
* for commutative `F`: `Ψ(T) · [n]'(T) = n · Ψ([n](T))`;
* hence in characteristic `p`, `[p]'(T) = 0`, so `[p](T)` only has monomials `T^{pk}`.
-/
import RamanujanTau.FormalGroupLayer.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace FGL
open MvPowerSeries

variable {R : Type*} [CommRing R] (F : FormalGroup R)

local notation "Fs" => (F.toPowerSeries : MvPowerSeries (Fin 2) R)

/-- `F(a, 0) = a`. -/
theorem ev_zero_right {β : Type*} [Finite β] (a : MvPowerSeries β R) (ha : constantCoeff a = 0) :
    ev F a 0 = a := by
  have h0 : ∀ s : Unit, constantCoeff ((fun _ : Unit => a) s) = 0 := fun _ => ha
  have := congrArg (subst (fun _ : Unit => a)) (ev_T_zero F)
  rwa [subst_ev F _ _ _ cc_T (by simp) h0, sX _ h0 (), s0 _ h0] at this

/-- `Ψ(u) = (∂₂F)(u, 0)`. -/
noncomputable def Ψ {β : Type*} (u : MvPowerSeries β R) : MvPowerSeries β R := subst ![u, 0] (pd 1 Fs)

lemma pd_X' {β : Type*} [DecidableEq β] (i j : β) :
    pd i (X j : MvPowerSeries β R) = if j = i then 1 else 0 := pd_X i j

lemma pd_zero' {β : Type*} [DecidableEq β] (i : β) : pd i (0 : MvPowerSeries β R) = 0 :=
  map_zero (pdDer (R := R) i)

/-- derivative of `F(a, b)`. -/
lemma pd_ev {β : Type*} [Fintype β] [DecidableEq β] (a b : MvPowerSeries β R) (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) (j : β) :
    pd j (ev F a b) = subst ![a, b] (pd 0 Fs) * pd j a + subst ![a, b] (pd 1 Fs) * pd j b := by
  rw [ev, pd_subst (cc_vec2 ha hb), Fin.sum_univ_two]; rfl

/-- **(I)**: `Ψ(F(a,b)) = (∂₂F)(a,b) · Ψ(b)`. -/
theorem invariance {β : Type*} [Fintype β] (a b : MvPowerSeries β R) (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : Ψ F (ev F a b) = subst ![a, b] (pd 1 Fs) * Ψ F b := by
  -- differentiate associativity (in three variables) with respect to the last one
  have Y0 : constantCoeff (X 0 : MvPowerSeries (Fin 3) R) = 0 := by simp
  have Y1 : constantCoeff (X 1 : MvPowerSeries (Fin 3) R) = 0 := by simp
  have Y2 : constantCoeff (X 2 : MvPowerSeries (Fin 3) R) = 0 := by simp
  have h := congrArg (pd 2) (assoc_ev F _ _ _ Y0 Y1 Y2)
  rw [pd_ev F _ _ (cc_ev F Y0 Y1) Y2, pd_ev F _ _ Y0 (cc_ev F Y1 Y2), pd_ev F _ _ Y0 Y1,
    pd_ev F _ _ Y1 Y2] at h
  simp only [pd_X', show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide, if_false, if_true,
    mul_zero, zero_add, mul_one, add_zero] at h
  -- now set the last variable to `0` and the others to `a, b`
  have hv := cc_vec3 ha hb (by simp : constantCoeff (0 : MvPowerSeries β R) = 0)
  have h2 := congrArg (subst ![a, b, 0]) h
  have e01 := subst_ev F (X 0 : MvPowerSeries (Fin 3) R) (X 1) ![a, b, 0] Y0 Y1 hv
  have e12 := subst_ev F (X 1 : MvPowerSeries (Fin 3) R) (X 2) ![a, b, 0] Y1 Y2 hv
  rw [sX _ hv, sX _ hv] at e01 e12
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at e01 e12
  rw [ev_zero_right F b hb] at e12
  rw [subst_mul (hs hv), ss _ _ (cc_vec2 (cc_ev F Y0 Y1) Y2) hv, ss _ _ (cc_vec2 Y0 (cc_ev F Y1 Y2)) hv,
    ss _ _ (cc_vec2 Y1 Y2) hv] at h2
  have l1 : (fun s => subst ![a, b, 0] (![ev F (X 0 : MvPowerSeries (Fin 3) R) (X 1), X 2] s)) = ![ev F a b, 0] := by
    funext s; fin_cases s
    · exact e01
    · exact sX _ hv 2
  have l2 : (fun s => subst ![a, b, 0] (![(X 0 : MvPowerSeries (Fin 3) R), ev F (X 1) (X 2)] s)) = ![a, b] := by
    funext s; fin_cases s
    · exact sX _ hv 0
    · exact e12
  have l3 : (fun s => subst ![a, b, 0] (![(X 1 : MvPowerSeries (Fin 3) R), X 2] s)) = ![b, 0] := by
    funext s; fin_cases s
    · exact sX _ hv 1
    · exact sX _ hv 2
  rw [l1, l2, l3] at h2
  exact h2

/-- the multiplication-by-`n` series `[n](T)`: `[0] = 0`, `[n+1] = F(T, [n])`. -/
noncomputable def nmul : ℕ → MvPowerSeries Unit R
  | 0 => 0
  | n + 1 => ev F T (nmul n)

lemma cc_nmul (n : ℕ) : constantCoeff (nmul F n) = 0 := by
  induction n with
  | zero => simp [nmul]
  | succ n ih => exact cc_ev F cc_T ih

/-- commutativity in `ev` form. -/
lemma ev_comm [F.IsComm] {β : Type*} [Finite β] (a b : MvPowerSeries β R) (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : ev F a b = ev F b a := by
  have hv := cc_vec2 ha hb
  have h := congrArg (subst ![a, b]) (FormalGroup.IsComm.comm (F := F))
  rw [ss _ _ (cc_vec2 (by simp) (by simp)) hv] at h
  have : (fun s => subst ![a, b] (![(X 1 : MvPowerSeries (Fin 2) R), X 0] s)) = ![b, a] := by
    funext s; fin_cases s
    · exact sX _ hv 1
    · exact sX _ hv 0
  rw [this] at h
  exact h

/-- commutativity for the partial derivatives: `(∂₁F)(a,b) = (∂₂F)(b,a)`. -/
lemma pd0_comm [F.IsComm] {β : Type*} [Finite β] (a b : MvPowerSeries β R) (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : subst ![a, b] (pd 0 Fs) = subst ![b, a] (pd 1 Fs) := by
  have hX : ∀ s, constantCoeff ((![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) R) s) = 0 :=
    cc_vec2 (by simp) (by simp)
  have h : pd 0 Fs = subst ![X 1, X 0] (pd 1 Fs) := by
    conv_lhs => rw [FormalGroup.IsComm.comm (F := F)]
    rw [pd_subst hX, Fin.sum_univ_two]
    simp [pd_X']
  have hv := cc_vec2 ha hb
  rw [h, ss _ _ hX hv]
  congr 1; funext s; fin_cases s
  · exact sX _ hv 1
  · exact sX _ hv 0

/-- **`[n]^* ω = n ω`**: `Ψ(T) · [n]'(T) = n · Ψ([n](T))`. -/
theorem nmul_invariant [F.IsComm] (n : ℕ) :
    Ψ F (T : MvPowerSeries Unit R) * pd () (nmul F n) = (n : MvPowerSeries Unit R) * Ψ F (nmul F n) := by
  induction n with
  | zero => simp [nmul, pd_zero']
  | succ n ih =>
    have hm := cc_nmul F n
    show Ψ F T * pd () (ev F T (nmul F n)) = _ * Ψ F (ev F T (nmul F n))
    rw [pd_ev F _ _ cc_T hm, pd_X', if_pos rfl, mul_one, mul_add,
      mul_left_comm (Ψ F T) _ (pd () _), ih, pd0_comm F _ _ cc_T hm]
    have i1 := invariance F T (nmul F n) cc_T hm
    have i2 := invariance F (nmul F n) T hm cc_T
    rw [ev_comm F _ _ hm cc_T] at i2
    rw [mul_comm (Ψ F T), ← i2,
      mul_left_comm (subst ![T, nmul F n] (pd 1 Fs)) ((n : MvPowerSeries Unit R)) (Ψ F (nmul F n)), ← i1]
    push_cast; ring

end FGL
