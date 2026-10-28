/-
# Consequences of Lubin's lemma: injectivity in several variables, the one-variable lemma, and the
dual isogeny `π̌` with `π̌ ∘ π = [p]` when `H ⊆ F[p]`.
-/
import RamanujanTau.LubinQuotient.Descent

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Lubin
open MvPowerSeries MvPowerSeries.WithPiTopology

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [IsTopologicalRing O]
  [IsLinearTopology O O] [CompleteSpace O] [T2Space O]

variable {F : FormalGroup O} [F.IsComm] (S : FinSub F)

section Multi
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- `X i ↦ π(X i)` for all variables. -/
noncomputable def pp : σ → MvPowerSeries σ O := fun i => piE S (X i)

lemma adm_pp : Adm (pp S : σ → MvPowerSeries σ O) := fun i => tn_of_cc (cc_piX S i)

lemma E_pp_X (i : σ) : E (pp S) (X i : MvPowerSeries σ O) = piE S (X i) := E_X i

/-- `X i ↦ π(X i)` for `i ∈ T`. -/
noncomputable def ppT (T : Finset σ) : σ → MvPowerSeries σ O :=
  fun i => if i ∈ T then piE S (X i) else X i

lemma adm_ppT (T : Finset σ) : Adm (ppT S T) := by
  intro i; unfold ppT; split_ifs
  · exact tn_of_cc (cc_piX S i)
  · exact tn_X i

variable [IsDomain O]

lemma inj_ppT (T : Finset σ) {g g' : MvPowerSeries σ O} (h : E (ppT S T) g = E (ppT S T) g') :
    g = g' := by
  induction T using Finset.induction_on generalizing g g' with
  | empty =>
    have : ppT S (∅ : Finset σ) = X := by funext i; simp [ppT]
    rwa [this, E_X_self, E_X_self] at h
  | insert a T haT ih =>
    have hcomp : ∀ f : MvPowerSeries σ O, E (ppT S (insert a T)) f = E (bs S a) (E (ppT S T) f) := by
      intro f
      rw [E_E (adm_ppT S T) (adm_bs S a)]
      congr 1; funext i
      by_cases hia : i = a
      · subst hia
        simp only [ppT, Finset.mem_insert_self, if_true, if_neg haT, E_X, bs_self]
      · by_cases hiT : i ∈ T
        · simp only [ppT, Finset.mem_insert, hia, hiT, or_true, if_true]
          rw [E_piE S (adm_bs S a) (tn_X i), E_X, bs_ne S a hia]
        · simp only [ppT, Finset.mem_insert, hia, hiT, or_false, if_false]
          rw [E_X, bs_ne S a hia]
    rw [hcomp, hcomp] at h
    exact ih (inj' S a h)

/-- substituting `π(X i)` for every variable is injective. -/
theorem inj_pp {g g' : MvPowerSeries σ O} (h : E (pp S) g = E (pp S) g') : g = g' := by
  apply inj_ppT S Finset.univ
  have : ppT S (Finset.univ : Finset σ) = pp S := by funext i; simp [ppT, pp]
  rwa [this]

end Multi

section One

lemma bs_unit : bs S () = fun _ : Unit => pis S := by
  funext u; cases u; exact bs_self S ()

lemma trs_unit (h : O) : trs (F := F) () h = fun _ : Unit => E2 F (X ()) (C h) := by
  funext u; cases u; exact Function.update_self _ _ _

lemma E_bs_unit (g : MvPowerSeries Unit O) : E (bs S ()) g = subst (fun _ : Unit => pis S) g := by
  rw [bs_unit]; exact E_eq_subst (fun _ => cc_pis S) g

variable [IsDomain O]

/-- **Lubin's lemma (one variable)**: a series invariant under `X ↦ F(X, h)`, `h ∈ H`, is a unique
series in `π(X)`. -/
theorem lubin_one {f : MvPowerSeries Unit O}
    (hf : ∀ h ∈ S.H, E (fun _ : Unit => E2 F (X ()) (C h)) f = f) :
    ∃! g : MvPowerSeries Unit O, subst (fun _ : Unit => pis S) g = f := by
  have hinv : Inv S () f := by intro h hh; rw [trs_unit]; exact hf h hh
  obtain ⟨g, hg⟩ := descent S () hinv
  refine ⟨g, by show subst _ g = f; rw [← E_bs_unit]; exact hg, fun g' hg' => inj' S () ?_⟩
  rw [E_bs_unit, E_bs_unit, hg', ← E_bs_unit, hg]

end One

section Dual
variable (p : ℕ)

omit [F.IsComm] in
lemma tn_nmul : TN (FGL.nmul F p) := tn_of_cc (FGL.cc_nmul F p)

omit [F.IsComm] in
lemma tn_nm (i : Fin 2) : TN (E (fun _ : Unit => (X i : MvPowerSeries (Fin 2) O)) (FGL.nmul F p)) :=
  tn_of_cc (by rw [E_eq_subst (fun _ => by simp)]; exact FGL.cc_nm F p (by simp))

omit [F.IsComm] in
lemma tn_E2X01 : TN (E2 F (X 0 : MvPowerSeries (Fin 2) O) (X 1)) :=
  tn_of_cc (by rw [E2_eq_ev (by simp) (by simp)]; exact FGL.cc_ev F (by simp) (by simp))

/-- `[p]` is an endomorphism, in evaluation form. -/
lemma nmul_hom : E (fun _ : Unit => E2 F (X 0 : MvPowerSeries (Fin 2) O) (X 1)) (FGL.nmul F p) =
    E2 F (E (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) O)) (FGL.nmul F p))
      (E (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) O)) (FGL.nmul F p)) := by
  have X0 : constantCoeff (X 0 : MvPowerSeries (Fin 2) O) = 0 := by simp
  have X1 : constantCoeff (X 1 : MvPowerSeries (Fin 2) O) = 0 := by simp
  have c0 : constantCoeff (subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) O)) (FGL.nmul F p)) = 0 :=
    FGL.cc_nm F p X0
  have c1 : constantCoeff (subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) O)) (FGL.nmul F p)) = 0 :=
    FGL.cc_nm F p X1
  have h1 := FGL.nm_ev F p X0 X1
  unfold FGL.nm at h1
  rw [← E2_eq_ev c0 c1, ← E_eq_subst (fun _ => FGL.cc_ev F X0 X1), ← E2_eq_ev X0 X1,
    ← E_eq_subst (fun _ => X0), ← E_eq_subst (fun _ => X1)] at h1
  exact h1

lemma E_unitX (f : MvPowerSeries Unit O) : E (fun _ : Unit => (X () : MvPowerSeries Unit O)) f = f := by
  rw [show (fun _ : Unit => (X () : MvPowerSeries Unit O)) = X from funext fun u => rfl, E_X_self]

/-- `[p](F(X, h)) = [p](X)` when `[p](h) = 0`. -/
lemma nmul_translate {h : O} (hh : IsTopologicallyNilpotent h)
    (hp : pt (fun _ : Unit => h) (FGL.nmul F p) = 0) :
    E (fun _ : Unit => E2 F (X ()) (C h)) (FGL.nmul F p) = FGL.nmul F p := by
  have hv := adm2 (tn_X ()) (tn_C (τ := Unit) hh)
  have h2 := congrArg (E ![(X () : MvPowerSeries Unit O), C h]) (nmul_hom (F := F) p)
  rw [E_E (fun _ => tn_E2X01) hv, E_E2 hv (tn_nm p 0) (tn_nm p 1),
    E_E (fun _ => tn_X 0) hv, E_E (fun _ => tn_X 1) hv] at h2
  simp only [E_E2 hv (tn_X 0) (tn_X 1), E_X, Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  rw [h2, E_const (fun _ => hh), hp, map_zero, E_unitX, E2_zero (tn_nmul p)]

variable [IsDomain O]

/-- **the dual isogeny**: if `H ⊆ F[p]` there is a unique `π̌` with `π̌ ∘ π = [p]`. -/
theorem exists_dual (hp : ∀ h ∈ S.H, pt (fun _ : Unit => h) (FGL.nmul F p) = 0) :
    ∃! πd : MvPowerSeries Unit O, subst (fun _ : Unit => pis S) πd = FGL.nmul F p :=
  lubin_one S (fun h hh => nmul_translate p (S.tn h hh) (hp h hh))

end Dual

end Lubin
