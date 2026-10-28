/-
# Evaluating a formal group law at topologically nilpotent arguments

`E2 F a b = F(a, b)` for series `a, b` with topologically nilpotent constant terms, and the point
addition `padd F x y = F(x, y) ∈ O`. Associativity, commutativity and `F(a, 0) = a` transfer from
the formal identities.
-/
import RamanujanTau.LubinQuotient.Factor

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Lubin
open MvPowerSeries MvPowerSeries.WithPiTopology

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [IsTopologicalRing O]
  [IsLinearTopology O O] [CompleteSpace O] [T2Space O]

variable (F : FormalGroup O)

local notation "Fs" => (F.toPowerSeries : MvPowerSeries (Fin 2) O)

/-- `F(a, b)`. -/
noncomputable def E2 {τ : Type*} (a b : MvPowerSeries τ O) : MvPowerSeries τ O := E ![a, b] Fs

/-- the point addition `x +_F y = F(x, y)`. -/
noncomputable def padd (x y : O) : O := pt ![x, y] Fs

/-- topological nilpotence of the constant term. -/
abbrev TN {τ : Type*} (a : MvPowerSeries τ O) : Prop := IsTopologicallyNilpotent (constantCoeff a)

lemma adm2 {τ : Type*} {a b : MvPowerSeries τ O} (ha : TN a) (hb : TN b) : Adm ![a, b] := by
  intro i; fin_cases i <;> simpa

lemma adm3 {τ : Type*} {a b c : MvPowerSeries τ O} (ha : TN a) (hb : TN b) (hc : TN c) :
    Adm ![a, b, c] := by
  intro i; fin_cases i <;> simpa

lemma admPt2 {x y : O} (hx : IsTopologicallyNilpotent x) (hy : IsTopologicallyNilpotent y) :
    AdmPt ![x, y] := by
  intro i; fin_cases i <;> simpa

lemma tn_C {τ : Type*} {x : O} (hx : IsTopologicallyNilpotent x) : TN (C x : MvPowerSeries τ O) := by
  simpa using hx

lemma tn_of_cc {τ : Type*} {a : MvPowerSeries τ O} (ha : constantCoeff a = 0) : TN a := by
  rw [TN, ha]; exact IsTopologicallyNilpotent.zero

lemma tn_X {τ : Type*} (t : τ) : TN (X t : MvPowerSeries τ O) := tn_of_cc (by simp)

lemma tn_zero {τ : Type*} : TN (0 : MvPowerSeries τ O) := tn_of_cc (by simp)

variable {F}

lemma E2_eq_ev {τ : Type*} [Finite τ] [DecidableEq τ] [Fintype τ] {a b : MvPowerSeries τ O}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) : E2 F a b = FGL.ev F a b :=
  E_eq_subst (FGL.cc_vec2 ha hb) _

/-- evaluation commutes with `F(·,·)`. -/
lemma E_E2 {τ υ : Type*} [Finite τ] {v : τ → MvPowerSeries υ O} (hv : Adm v)
    {a b : MvPowerSeries τ O} (ha : TN a) (hb : TN b) :
    E v (E2 F a b) = E2 F (E v a) (E v b) := by
  rw [E2, E_E (adm2 ha hb) hv, E2]
  congr 1; funext i; fin_cases i <;> rfl

lemma pt_E2 {τ : Type*} [Finite τ] {x : τ → O} (hx : AdmPt x)
    {a b : MvPowerSeries τ O} (ha : TN a) (hb : TN b) :
    pt x (E2 F a b) = padd F (pt x a) (pt x b) := by
  rw [E2, pt_E (adm2 ha hb) hx, padd]
  congr 1; funext i; fin_cases i <;> rfl

lemma E2_C {τ : Type*} {x y : O} (hx : IsTopologicallyNilpotent x) (hy : IsTopologicallyNilpotent y) :
    E2 F (C x : MvPowerSeries τ O) (C y) = C (padd F x y) := by
  rw [E2, padd, ← E_const (admPt2 hx hy)]
  congr 1; funext i; fin_cases i <;> rfl

lemma cc_E2 {τ : Type*} {a b : MvPowerSeries τ O} (ha : TN a) (hb : TN b) :
    constantCoeff (E2 F a b) = padd F (constantCoeff a) (constantCoeff b) := by
  rw [E2, cc_E (adm2 ha hb), padd]
  congr 1; funext i; fin_cases i <;> rfl

lemma tn_E2 {τ : Type*} {a b : MvPowerSeries τ O} (ha : TN a) (hb : TN b)
    (h : IsTopologicallyNilpotent (padd F (constantCoeff a) (constantCoeff b))) : TN (E2 F a b) := by
  rw [TN, cc_E2 ha hb]; exact h

/-- **associativity**. -/
theorem E2_assoc {τ : Type*} [Finite τ] {a b c : MvPowerSeries τ O} (ha : TN a) (hb : TN b) (hc : TN c) :
    E2 F (E2 F a b) c = E2 F a (E2 F b c) := by
  have X0 : constantCoeff (X 0 : MvPowerSeries (Fin 3) O) = 0 := by simp
  have X1 : constantCoeff (X 1 : MvPowerSeries (Fin 3) O) = 0 := by simp
  have X2 : constantCoeff (X 2 : MvPowerSeries (Fin 3) O) = 0 := by simp
  have h := FGL.assoc_ev F (X 0 : MvPowerSeries (Fin 3) O) (X 1) (X 2) X0 X1 X2
  rw [← E2_eq_ev (FGL.cc_ev F X0 X1) X2, ← E2_eq_ev X0 (FGL.cc_ev F X1 X2), ← E2_eq_ev X0 X1,
    ← E2_eq_ev X1 X2] at h
  have t01 : TN (E2 F (X 0 : MvPowerSeries (Fin 3) O) (X 1)) :=
    tn_of_cc (by rw [E2_eq_ev X0 X1]; exact FGL.cc_ev F X0 X1)
  have t12 : TN (E2 F (X 1 : MvPowerSeries (Fin 3) O) (X 2)) :=
    tn_of_cc (by rw [E2_eq_ev X1 X2]; exact FGL.cc_ev F X1 X2)
  have hv := adm3 ha hb hc
  have h2 := congrArg (E ![a, b, c]) h
  rw [E_E2 hv t01 (tn_X 2), E_E2 hv (tn_X 0) t12, E_E2 hv (tn_X 0) (tn_X 1),
    E_E2 hv (tn_X 1) (tn_X 2)] at h2
  simpa [E_X] using h2

/-- **commutativity**. -/
theorem E2_comm [F.IsComm] {τ : Type*} [Finite τ] {a b : MvPowerSeries τ O} (ha : TN a) (hb : TN b) :
    E2 F a b = E2 F b a := by
  have X0 : constantCoeff (X 0 : MvPowerSeries (Fin 2) O) = 0 := by simp
  have X1 : constantCoeff (X 1 : MvPowerSeries (Fin 2) O) = 0 := by simp
  have h := FGL.ev_comm F (X 0 : MvPowerSeries (Fin 2) O) (X 1) X0 X1
  rw [← E2_eq_ev X0 X1, ← E2_eq_ev X1 X0] at h
  have h2 := congrArg (E ![a, b]) h
  rw [E_E2 (adm2 ha hb) (tn_X 0) (tn_X 1), E_E2 (adm2 ha hb) (tn_X 1) (tn_X 0)] at h2
  simpa [E_X] using h2

/-- **`F(a, 0) = a`**. -/
theorem E2_zero {τ : Type*} [Finite τ] {a : MvPowerSeries τ O} (ha : TN a) : E2 F a 0 = a := by
  have h := FGL.ev_T_zero F
  rw [← E2_eq_ev FGL.cc_T (by simp)] at h
  have hv : Adm (fun _ : Unit => a) := fun _ => ha
  have h2 := congrArg (E (fun _ : Unit => a)) h
  rw [E_E2 hv (tn_X ()) tn_zero, E_X, E_zero hv] at h2
  exact h2

theorem zero_E2 [F.IsComm] {τ : Type*} [Finite τ] {a : MvPowerSeries τ O} (ha : TN a) : E2 F 0 a = a := by
  rw [E2_comm tn_zero ha, E2_zero ha]

/-! ### points -/

variable {x y z : O}

lemma padd_eq (hx : IsTopologicallyNilpotent x) (hy : IsTopologicallyNilpotent y) :
    (C (padd F x y) : MvPowerSeries Unit O) = E2 F (C x) (C y) := (E2_C hx hy).symm

theorem padd_assoc (hx : IsTopologicallyNilpotent x) (hy : IsTopologicallyNilpotent y)
    (hz : IsTopologicallyNilpotent z) (hxy : IsTopologicallyNilpotent (padd F x y))
    (hyz : IsTopologicallyNilpotent (padd F y z)) :
    padd F (padd F x y) z = padd F x (padd F y z) := by
  apply C_injective (σ := Unit) (R := O)
  rw [padd_eq hxy hz, padd_eq hx hy, padd_eq hx hyz, padd_eq hy hz]
  exact E2_assoc (tn_C hx) (tn_C hy) (tn_C hz)

theorem padd_comm [F.IsComm] (hx : IsTopologicallyNilpotent x) (hy : IsTopologicallyNilpotent y) :
    padd F x y = padd F y x := by
  apply C_injective (σ := Unit) (R := O)
  rw [padd_eq hx hy, padd_eq hy hx]
  exact E2_comm (tn_C hx) (tn_C hy)

theorem padd_zero (hx : IsTopologicallyNilpotent x) : padd F x 0 = x := by
  apply C_injective (σ := Unit) (R := O)
  rw [padd_eq hx tn0, map_zero]
  exact E2_zero (tn_C hx)

theorem zero_padd [F.IsComm] (hx : IsTopologicallyNilpotent x) : padd F 0 x = x := by
  rw [padd_comm tn0 hx, padd_zero hx]

end Lubin
