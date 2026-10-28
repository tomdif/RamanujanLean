/-
# Finite subgroups and the Lubin series `π(X) = ∏_{h ∈ H} F(X, h)`
-/
import RamanujanTau.LubinQuotient.Points

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Lubin
open MvPowerSeries MvPowerSeries.WithPiTopology

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [IsTopologicalRing O]
  [IsLinearTopology O O] [CompleteSpace O] [T2Space O]

variable (F : FormalGroup O)

local notation "Fs" => (F.toPowerSeries : MvPowerSeries (Fin 2) O)

/-- a finite subgroup of the topologically nilpotent points of `F`. -/
structure FinSub where
  H : Finset O
  tn : ∀ h ∈ H, IsTopologicallyNilpotent h
  zero_mem : (0 : O) ∈ H
  add_mem : ∀ a ∈ H, ∀ b ∈ H, padd F a b ∈ H
  neg_mem : ∀ a ∈ H, ∃ b ∈ H, padd F a b = 0

variable {F} [F.IsComm] (S : FinSub F)

namespace FinSub

/-- the inverse in `H`. -/
noncomputable def neg (a : O) : O := by
  classical exact if h : a ∈ S.H then Classical.choose (S.neg_mem a h) else 0

lemma neg_spec {a : O} (ha : a ∈ S.H) : S.neg a ∈ S.H ∧ padd F a (S.neg a) = 0 := by
  classical
  rw [neg, dif_pos ha]; exact Classical.choose_spec (S.neg_mem a ha)

lemma neg_mem' {a : O} (ha : a ∈ S.H) : S.neg a ∈ S.H := (S.neg_spec ha).1
lemma add_neg {a : O} (ha : a ∈ S.H) : padd F a (S.neg a) = 0 := (S.neg_spec ha).2
lemma neg_add {a : O} (ha : a ∈ S.H) : padd F (S.neg a) a = 0 := by
  rw [padd_comm (S.tn _ (S.neg_mem' ha)) (S.tn _ ha), S.add_neg ha]

lemma add_right_cancel {a b c : O} (ha : a ∈ S.H) (hb : b ∈ S.H) (hc : c ∈ S.H)
    (h : padd F b a = padd F c a) : b = c := by
  have := congrArg (fun x => padd F x (S.neg a)) h
  simp only at this
  have tn := S.tn
  rwa [padd_assoc (tn _ hb) (tn _ ha) (tn _ (S.neg_mem' ha)) (tn _ (S.add_mem _ hb _ ha))
      (tn _ (S.add_mem _ ha _ (S.neg_mem' ha))),
    padd_assoc (tn _ hc) (tn _ ha) (tn _ (S.neg_mem' ha)) (tn _ (S.add_mem _ hc _ ha))
      (tn _ (S.add_mem _ ha _ (S.neg_mem' ha))), S.add_neg ha, padd_zero (tn _ hb),
    padd_zero (tn _ hc)] at this

lemma neg_neg {a : O} (ha : a ∈ S.H) : S.neg (S.neg a) = a := by
  apply S.add_right_cancel (S.neg_mem' ha) (S.neg_mem' (S.neg_mem' ha)) ha
  rw [S.neg_add (S.neg_mem' ha), S.add_neg ha]

/-- translation by `a ∈ H` permutes `H`. -/
lemma prod_translate {M : Type*} [CommMonoid M] (f : O → M) {a : O} (ha : a ∈ S.H) :
    ∏ h ∈ S.H, f (padd F h a) = ∏ h ∈ S.H, f h := by
  have tn := S.tn
  refine Finset.prod_nbij' (fun h => padd F h a) (fun h => padd F h (S.neg a))
    (fun h hh => S.add_mem _ hh _ ha) (fun h hh => S.add_mem _ hh _ (S.neg_mem' ha)) ?_ ?_
    (fun _ _ => rfl)
  · intro h hh
    simp only
    rw [padd_assoc (tn _ hh) (tn _ ha) (tn _ (S.neg_mem' ha)) (tn _ (S.add_mem _ hh _ ha))
      (tn _ (S.add_mem _ ha _ (S.neg_mem' ha))), S.add_neg ha, padd_zero (tn _ hh)]
  · intro h hh
    simp only
    rw [padd_assoc (tn _ hh) (tn _ (S.neg_mem' ha)) (tn _ ha) (tn _ (S.add_mem _ hh _ (S.neg_mem' ha)))
      (tn _ (S.add_mem _ (S.neg_mem' ha) _ ha)), S.neg_add ha, padd_zero (tn _ hh)]

/-- inversion permutes `H`. -/
lemma prod_neg {M : Type*} [CommMonoid M] (f : O → M) :
    ∏ h ∈ S.H, f (S.neg h) = ∏ h ∈ S.H, f h :=
  Finset.prod_nbij' S.neg S.neg (fun _ hh => S.neg_mem' hh) (fun _ hh => S.neg_mem' hh)
    (fun _ hh => S.neg_neg hh) (fun _ hh => S.neg_neg hh) (fun _ _ => rfl)

end FinSub

/-- **Lubin's series** `π(Z) = ∏_{h ∈ H} F(Z, h)`. -/
noncomputable def piE {τ : Type*} (Z : MvPowerSeries τ O) : MvPowerSeries τ O :=
  ∏ h ∈ S.H, E2 F Z (C h)

/-- the one-variable series `π(X)`. -/
noncomputable def pis : MvPowerSeries Unit O := piE S (X ())

lemma cc_piE {τ : Type*} {Z : MvPowerSeries τ O} (hZ : constantCoeff Z = 0) :
    constantCoeff (piE S Z) = 0 := by
  rw [piE, map_prod]
  apply Finset.prod_eq_zero S.zero_mem
  rw [cc_E2 (tn_of_cc hZ) (tn_C tn0), hZ, map_zero, map_zero, padd_zero tn0]

lemma cc_pis : constantCoeff (pis S) = 0 := cc_piE S (by simp)

lemma E_piE {τ υ : Type*} [Finite τ] {v : τ → MvPowerSeries υ O} (hv : Adm v)
    {Z : MvPowerSeries τ O} (hZ : TN Z) : E v (piE S Z) = piE S (E v Z) := by
  rw [piE, E_prod hv, piE]
  refine Finset.prod_congr rfl fun h hh => ?_
  rw [E_E2 hv hZ (tn_C (S.tn h hh)), E_C]

/-- `π(Z)` is `pis` evaluated at `Z`. -/
lemma piE_eq {τ : Type*} [Finite τ] {Z : MvPowerSeries τ O} (hZ : TN Z) :
    piE S Z = E (fun _ : Unit => Z) (pis S) := by
  rw [pis, E_piE S (fun _ => hZ) (tn_X ()), E_X]

/-- **invariance** `π(F(Z, a)) = π(Z)` for `a ∈ H`. -/
theorem piE_translate {τ : Type*} [Finite τ] {Z : MvPowerSeries τ O} (hZ : TN Z) {a : O} (ha : a ∈ S.H) :
    piE S (E2 F Z (C a)) = piE S Z := by
  rw [piE, piE]
  have : ∀ h ∈ S.H, E2 F (E2 F Z (C a)) (C h) = E2 F Z (C (padd F h a)) := by
    intro h hh
    rw [E2_assoc hZ (tn_C (S.tn a ha)) (tn_C (S.tn h hh)), E2_C (S.tn a ha) (S.tn h hh),
      padd_comm (S.tn a ha) (S.tn h hh)]
  rw [Finset.prod_congr rfl this]
  exact S.prod_translate (fun h => E2 F Z (C h)) ha

omit [F.IsComm] in
/-- `F = X₀ + X₁ · B`. -/
lemma F_decomp : Fs = X 0 + X 1 * shift 1 Fs := by
  conv_lhs => rw [decomp (1 : Fin 2) Fs]
  congr 1
  have : Function.update (X : Fin 2 → MvPowerSeries (Fin 2) O) 1 (C 0) = ![X 0, 0] := by
    funext i; fin_cases i <;> simp
  rw [ev, this]
  exact E2_zero (F := F) (tn_X 0)

omit [F.IsComm] in
/-- the linear coefficient of `F(X, h)` is `1 + h c`. -/
lemma coeff_one_tau {h : O} (hh : IsTopologicallyNilpotent h) :
    ∃ c, coeff (Finsupp.single () 1) (E2 F (X () : MvPowerSeries Unit O) (C h)) = 1 + h * c := by
  refine ⟨coeff (Finsupp.single () 1) (E ![(X () : MvPowerSeries Unit O), C h] (shift 1 Fs)), ?_⟩
  have hv := adm2 (tn_X ()) (tn_C (τ := Unit) hh)
  rw [E2, show E ![(X () : MvPowerSeries Unit O), C h] Fs =
    E ![(X () : MvPowerSeries Unit O), C h] (X 0 + X 1 * shift 1 Fs) by rw [← F_decomp],
    E_add hv, E_mul hv, E_X, E_X, map_add]
  simp [coeff_X, coeff_C_mul]

/-- `F(X, h) = (X - h⁻¹) · q` with `q(0)` a unit. -/
lemma tau_factor {h : O} (hh : h ∈ S.H) : ∃ q : MvPowerSeries Unit O, IsUnit (constantCoeff q) ∧
    E2 F (X () : MvPowerSeries Unit O) (C h) = (X () - C (S.neg h)) * q := by
  have tnh := S.tn h hh
  have tnn := S.tn _ (S.neg_mem' hh)
  obtain ⟨q, hq⟩ := factor () tnn (E2 F (X () : MvPowerSeries Unit O) (C h))
  have hroot : ev () (S.neg h) (E2 F (X () : MvPowerSeries Unit O) (C h)) = 0 := by
    rw [ev, E_E2 (adm_ev () tnn) (tn_X ()) (tn_C tnh), E_X, Function.update_self, E_C,
      E2_C tnn tnh, S.neg_add hh, map_zero]
  rw [hroot, sub_zero] at hq
  refine ⟨q, ?_, hq⟩
  obtain ⟨c, hc⟩ := coeff_one_tau (F := F) tnh
  have h1 := congrArg (coeff (Finsupp.single () 1)) hq
  rw [hc, sub_mul, map_sub, coeff_X_mul', if_pos le_rfl, tsub_self, coeff_C_mul,
    coeff_zero_eq_constantCoeff_apply] at h1
  have : constantCoeff q = 1 + (h * c + S.neg h * coeff (Finsupp.single () 1) q) := by
    linear_combination -h1
  rw [this]
  exact isUnit_one_add ((tnh.mul_right c).add (tnn.mul_right _))

/-- **Weierstrass factorization of `π`**: `π(X) = ∏_{h ∈ H} (X - h) · U` with `U` a unit. -/
theorem pis_factor : ∃ U : MvPowerSeries Unit O, IsUnit U ∧
    pis S = (∏ h ∈ S.H, (X () - C h)) * U := by
  classical
  set q : O → MvPowerSeries Unit O := fun h =>
    if hh : h ∈ S.H then Classical.choose (tau_factor S hh) else 1 with hqdef
  have hq : ∀ h ∈ S.H, IsUnit (constantCoeff (q h)) ∧
      E2 F (X () : MvPowerSeries Unit O) (C h) = (X () - C (S.neg h)) * q h := by
    intro h hh
    simp only [hqdef, dif_pos hh]
    exact Classical.choose_spec (tau_factor S hh)
  refine ⟨∏ h ∈ S.H, q h, ?_, ?_⟩
  · rw [isUnit_iff_constantCoeff, map_prod, IsUnit.prod_iff]
    exact fun h hh => (hq h hh).1
  · rw [pis, piE, Finset.prod_congr rfl (fun h hh => (hq h hh).2), Finset.prod_mul_distrib]
    congr 1
    exact S.prod_neg (fun h => X () - C h)

end Lubin
