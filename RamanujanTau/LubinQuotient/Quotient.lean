/-
# Lubin's quotient formal group `G = F/H`

There is a unique `G ∈ O⟦X₀, X₁⟧` with `π(F(X₀, X₁)) = G(π X₀, π X₁)`; it is a commutative formal
group law, `π : F → G` is a homomorphism, and (if `H ⊆ F[p]`) so is the dual `π̌ : G → F`.
-/
import RamanujanTau.LubinQuotient.Dual

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Lubin
open MvPowerSeries MvPowerSeries.WithPiTopology

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [IsTopologicalRing O]
  [IsLinearTopology O O] [CompleteSpace O] [T2Space O]

variable {F : FormalGroup O} [F.IsComm] (S : FinSub F)

/-- `π(F(X₀, X₁))`. -/
noncomputable def PF : MvPowerSeries (Fin 2) O := piE S (E2 F (X 0) (X 1))

lemma piE_zero {τ : Type*} [Finite τ] : piE S (0 : MvPowerSeries τ O) = 0 := by
  rw [piE]
  exact Finset.prod_eq_zero S.zero_mem (by rw [map_zero, E2_zero tn_zero])

/-- invariance of `π(F(X₀, X₁))` in the first variable. -/
lemma PF_inv0 : Inv S (0 : Fin 2) (PF S) := by
  intro h hh
  have tnh := S.tn h hh
  have ha := adm_trs (F := F) (0 : Fin 2) tnh
  rw [PF, E_piE S ha tn_E2X01, E_E2 ha (tn_X 0) (tn_X 1), E_X, E_X, trs, Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),
    E2_assoc (tn_X 0) (tn_C tnh) (tn_X 1), E2_comm (tn_C tnh) (tn_X 1),
    ← E2_assoc (tn_X 0) (tn_X 1) (tn_C tnh), piE_translate S tn_E2X01 hh]

/-- invariance of `π(F(X₀, X₁))` in the second variable. -/
lemma PF_inv1 : Inv S (1 : Fin 2) (PF S) := by
  intro h hh
  have tnh := S.tn h hh
  have ha := adm_trs (F := F) (1 : Fin 2) tnh
  rw [PF, E_piE S ha tn_E2X01, E_E2 ha (tn_X 0) (tn_X 1), E_X, E_X, trs, Function.update_self,
    Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
    ← E2_assoc (tn_X 0) (tn_X 1) (tn_C tnh), piE_translate S tn_E2X01 hh]

/-- substituting `π` in the first variable commutes with translating the second. -/
lemma bs0_trs1 (h : O) (hh : IsTopologicallyNilpotent h) (g : MvPowerSeries (Fin 2) O) :
    E (bs S (0 : Fin 2)) (E (trs (F := F) (1 : Fin 2) h) g) =
      E (trs (F := F) (1 : Fin 2) h) (E (bs S (0 : Fin 2)) g) := by
  have hb := adm_bs S (0 : Fin 2)
  have ht := adm_trs (F := F) (1 : Fin 2) hh
  rw [E_E ht hb, E_E hb ht]
  congr 1; funext i; fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [trs_ne _ (by decide : (0 : Fin 2) ≠ 1), E_X, bs_self, E_piE S ht (tn_X 0), E_X,
      trs_ne _ (by decide : (0 : Fin 2) ≠ 1)]
  · simp only [Fin.mk_one, Fin.isValue]
    rw [bs_ne S _ (by decide : (1 : Fin 2) ≠ 0), E_X, trs, Function.update_self,
      E_E2 hb (tn_X 1) (tn_C hh), E_X, E_C, bs_ne S _ (by decide : (1 : Fin 2) ≠ 0)]

lemma bs0_bs1 (g : MvPowerSeries (Fin 2) O) :
    E (bs S (0 : Fin 2)) (E (bs S (1 : Fin 2)) g) = E (pp S) g := by
  have hb0 := adm_bs S (0 : Fin 2)
  have hb1 := adm_bs S (1 : Fin 2)
  rw [E_E hb1 hb0]
  congr 1; funext i; fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [bs_ne S _ (by decide : (0 : Fin 2) ≠ 1), E_X, bs_self]; rfl
  · simp only [Fin.mk_one, Fin.isValue]
    rw [bs_self, E_piE S hb0 (tn_X 1), E_X, bs_ne S _ (by decide : (1 : Fin 2) ≠ 0)]; rfl

variable [IsDomain O]

/-- **existence of the quotient law**: `π(F(X₀,X₁)) = G(π X₀, π X₁)` for some `G`. -/
theorem exists_quot : ∃ G : MvPowerSeries (Fin 2) O, E (pp S) G = PF S := by
  obtain ⟨g1, hg1⟩ := descent S (0 : Fin 2) (PF_inv0 S)
  have hinv1 : Inv S (1 : Fin 2) g1 := by
    intro h hh
    apply inj' S (0 : Fin 2)
    rw [bs0_trs1 S h (S.tn h hh), hg1]
    exact PF_inv1 S h hh
  obtain ⟨G, hG⟩ := descent S (1 : Fin 2) hinv1
  exact ⟨G, by rw [← bs0_bs1, hG, hg1]⟩

/-- the quotient law `G`. -/
noncomputable def Gs : MvPowerSeries (Fin 2) O := Classical.choose (exists_quot S)

lemma Gs_spec : E (pp S) (Gs S) = PF S := Classical.choose_spec (exists_quot S)

/-- **`π` is a homomorphism `F → G`**, in general evaluation form:
`G(π a, π b) = π(F(a, b))`. -/
theorem G_hom {τ : Type*} [Finite τ] (v : Fin 2 → MvPowerSeries τ O) (hv : ∀ i, TN (v i)) :
    E (fun i => piE S (v i)) (Gs S) = piE S (E2 F (v 0) (v 1)) := by
  have h := congrArg (E v) (Gs_spec S)
  rw [E_E (adm_pp S) hv, PF, E_piE S hv tn_E2X01, E_E2 hv (tn_X 0) (tn_X 1), E_X, E_X] at h
  rw [← h]
  congr 1; funext i
  rw [pp, E_piE S hv (tn_X i), E_X]

lemma cc_E_pp {σ : Type*} [Fintype σ] [DecidableEq σ] (g : MvPowerSeries σ O) :
    constantCoeff (E (pp S) g) = constantCoeff g := by
  rw [cc_E (adm_pp S)]
  have : (fun s => constantCoeff (pp S s : MvPowerSeries σ O)) = fun _ => 0 := by
    funext s; exact cc_piX S s
  rw [this, pt_zero]

lemma cc_Gs : constantCoeff (Gs S) = 0 := by
  rw [← cc_E_pp S, Gs_spec, PF]
  exact cc_piE S (by rw [E2_eq_ev (by simp) (by simp)]; exact FGL.cc_ev F (by simp) (by simp))

omit [IsDomain O] [F.IsComm] in
lemma tn_E2XX {τ : Type*} [Fintype τ] [DecidableEq τ] (i j : τ) : TN (E2 F (X i : MvPowerSeries τ O) (X j)) :=
  tn_of_cc (by rw [E2_eq_ev (by simp) (by simp)]; exact FGL.cc_ev F (by simp) (by simp))

/-- `G(X, 0) = X`. -/
lemma Gs_X0 : subst ![(X () : MvPowerSeries Unit O), 0] (Gs S) = X () := by
  apply inj_pp S
  have hv : ∀ s, constantCoeff (![(X () : MvPowerSeries Unit O), 0] s) = 0 :=
    FGL.cc_vec2 (by simp) (by simp)
  rw [E_subst hv (adm_pp S), E_pp_X]
  have : (fun s => E (pp S) (![(X () : MvPowerSeries Unit O), 0] s)) =
      fun i => piE S (![(X () : MvPowerSeries Unit O), 0] i) := by
    funext i; fin_cases i
    · exact E_pp_X S ()
    · show E (pp S) 0 = piE S 0
      rw [E_zero (adm_pp S), piE_zero]
  rw [this, G_hom S _ (by intro i; fin_cases i; exacts [tn_X (), tn_zero])]
  show piE S (E2 F (X ()) 0) = _
  rw [E2_zero (tn_X ())]

/-- `G(0, X) = X`. -/
lemma Gs_0X : subst ![0, (X () : MvPowerSeries Unit O)] (Gs S) = X () := by
  apply inj_pp S
  have hv : ∀ s, constantCoeff (![0, (X () : MvPowerSeries Unit O)] s) = 0 :=
    FGL.cc_vec2 (by simp) (by simp)
  rw [E_subst hv (adm_pp S), E_pp_X]
  have : (fun s => E (pp S) (![0, (X () : MvPowerSeries Unit O)] s)) =
      fun i => piE S (![0, (X () : MvPowerSeries Unit O)] i) := by
    funext i; fin_cases i
    · show E (pp S) 0 = piE S 0
      rw [E_zero (adm_pp S), piE_zero]
    · exact E_pp_X S ()
  rw [this, G_hom S _ (by intro i; fin_cases i; exacts [tn_zero, tn_X ()])]
  show piE S (E2 F 0 (X ())) = _
  rw [zero_E2 (tn_X ())]

/-- **commutativity of `G`**. -/
lemma Gs_comm : Gs S = subst ![X 1, X 0] (Gs S) := by
  apply inj_pp S
  rw [E_subst (FGL.cc_vec2 (by simp) (by simp)) (adm_pp S)]
  have : (fun s => E (pp S) (![(X 1 : MvPowerSeries (Fin 2) O), X 0] s)) =
      fun i => piE S (![(X 1 : MvPowerSeries (Fin 2) O), X 0] i) := by
    funext i; fin_cases i
    · exact E_pp_X S 1
    · exact E_pp_X S 0
  rw [this, G_hom S _ (by intro i; fin_cases i; exacts [tn_X 1, tn_X 0]), Gs_spec, PF]
  show _ = piE S (E2 F (X 1) (X 0))
  rw [E2_comm (tn_X 0) (tn_X 1)]

/-- **associativity of `G`**. -/
lemma Gs_assoc : subst ![subst ![(X 0 : MvPowerSeries (Fin 3) O), X 1] (Gs S), X 2] (Gs S) =
    subst ![X 0, subst ![(X 1 : MvPowerSeries (Fin 3) O), X 2] (Gs S)] (Gs S) := by
  apply inj_pp S
  have hv01 : ∀ s, constantCoeff (![(X 0 : MvPowerSeries (Fin 3) O), X 1] s) = 0 :=
    FGL.cc_vec2 (by simp) (by simp)
  have hv12 : ∀ s, constantCoeff (![(X 1 : MvPowerSeries (Fin 3) O), X 2] s) = 0 :=
    FGL.cc_vec2 (by simp) (by simp)
  have c01 := FGL.cc0 _ hv01 (cc_Gs S)
  have c12 := FGL.cc0 _ hv12 (cc_Gs S)
  have e01 : E (pp S) (subst ![(X 0 : MvPowerSeries (Fin 3) O), X 1] (Gs S)) =
      piE S (E2 F (X 0) (X 1)) := by
    rw [E_subst hv01 (adm_pp S)]
    have : (fun s => E (pp S) (![(X 0 : MvPowerSeries (Fin 3) O), X 1] s)) =
        fun i => piE S (![(X 0 : MvPowerSeries (Fin 3) O), X 1] i) := by
      funext i; fin_cases i
      · exact E_pp_X S 0
      · exact E_pp_X S 1
    rw [this, G_hom S _ (by intro i; fin_cases i; exacts [tn_X 0, tn_X 1])]; rfl
  have e12 : E (pp S) (subst ![(X 1 : MvPowerSeries (Fin 3) O), X 2] (Gs S)) =
      piE S (E2 F (X 1) (X 2)) := by
    rw [E_subst hv12 (adm_pp S)]
    have : (fun s => E (pp S) (![(X 1 : MvPowerSeries (Fin 3) O), X 2] s)) =
        fun i => piE S (![(X 1 : MvPowerSeries (Fin 3) O), X 2] i) := by
      funext i; fin_cases i
      · exact E_pp_X S 1
      · exact E_pp_X S 2
    rw [this, G_hom S _ (by intro i; fin_cases i; exacts [tn_X 1, tn_X 2])]; rfl
  rw [E_subst (FGL.cc_vec2 c01 (by simp)) (adm_pp S), E_subst (FGL.cc_vec2 (by simp) c12) (adm_pp S)]
  have l : (fun s => E (pp S) (![subst ![(X 0 : MvPowerSeries (Fin 3) O), X 1] (Gs S), X 2] s)) =
      fun i => piE S (![E2 F (X 0 : MvPowerSeries (Fin 3) O) (X 1), X 2] i) := by
    funext i; fin_cases i
    · exact e01
    · exact E_pp_X S 2
  have r : (fun s => E (pp S) (![X 0, subst ![(X 1 : MvPowerSeries (Fin 3) O), X 2] (Gs S)] s)) =
      fun i => piE S (![X 0, E2 F (X 1 : MvPowerSeries (Fin 3) O) (X 2)] i) := by
    funext i; fin_cases i
    · exact E_pp_X S 0
    · exact e12
  rw [l, r, G_hom S _ (by intro i; fin_cases i; exacts [tn_E2XX 0 1, tn_X 2]),
    G_hom S _ (by intro i; fin_cases i; exacts [tn_X 0, tn_E2XX 1 2])]
  show piE S (E2 F (E2 F (X 0) (X 1)) (X 2)) = piE S (E2 F (X 0) (E2 F (X 1) (X 2)))
  rw [E2_assoc (tn_X 0) (tn_X 1) (tn_X 2)]

omit [IsDomain O] [F.IsComm] in
/-- the linear coefficient of `G(X, 0)` is the `X₀`-coefficient of `G`. -/
lemma coeff_one_T0 (G : MvPowerSeries (Fin 2) O) :
    coeff (Finsupp.single () 1) (subst ![(X () : MvPowerSeries Unit O), 0] G) =
      coeff (Finsupp.single 0 1) G := by
  have hv := FGL.cc_vec2 (FGL.cc_T (R := O)) (by simp : constantCoeff (0 : MvPowerSeries Unit O) = 0)
  have hd := pd_subst hv () G
  have h1 := congrArg constantCoeff hd
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pd] at h1
  simp only [zero_add, Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, mul_one] at h1
  rw [h1, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_mul, pd_X, if_true]
  rw [show pd () (0 : MvPowerSeries Unit O) = 0 from map_zero (pdDer (R := O) ())]
  simp only [map_one, mul_one, map_zero, mul_zero, add_zero]
  rw [FGL.cc_subst _ hv, ← coeff_zero_eq_constantCoeff_apply, coeff_pd, zero_add]
  simp

omit [IsDomain O] [F.IsComm] in
lemma coeff_one_0T (G : MvPowerSeries (Fin 2) O) :
    coeff (Finsupp.single () 1) (subst ![0, (X () : MvPowerSeries Unit O)] G) =
      coeff (Finsupp.single 1 1) G := by
  have hv := FGL.cc_vec2 (by simp : constantCoeff (0 : MvPowerSeries Unit O) = 0) (FGL.cc_T (R := O))
  have hd := pd_subst hv () G
  have h1 := congrArg constantCoeff hd
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pd] at h1
  simp only [zero_add, Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, mul_one] at h1
  rw [h1, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_mul, pd_X, if_true]
  rw [show pd () (0 : MvPowerSeries Unit O) = 0 from map_zero (pdDer (R := O) ())]
  simp only [map_one, mul_one, map_zero, mul_zero, zero_add]
  rw [FGL.cc_subst _ hv, ← coeff_zero_eq_constantCoeff_apply, coeff_pd, zero_add]
  simp

/-- **Lubin's quotient formal group `F/H`**. -/
noncomputable def quot : FormalGroup O where
  toPowerSeries := Gs S
  zero_constantCoeff := cc_Gs S
  lin_coeff_X := by rw [← coeff_one_T0, Gs_X0]; simp [coeff_X]
  lin_coeff_Y := by rw [← coeff_one_0T, Gs_0X]; simp [coeff_X]
  assoc := Gs_assoc S

instance : (quot S).IsComm := ⟨Gs_comm S⟩

lemma quot_toPowerSeries : (quot S).toPowerSeries = Gs S := rfl

lemma E_pp_eq_E2 : E (pp S) (Gs S) = E2 (quot S) (piE S (X 0)) (piE S (X 1)) := by
  rw [E2, quot_toPowerSeries]
  congr 1; funext i; fin_cases i <;> rfl

omit [IsDomain O] in
lemma piE_X_eq {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) :
    piE S (X i : MvPowerSeries σ O) = subst (fun _ : Unit => X i) (pis S) := by
  rw [piE_eq S (tn_X i), E_eq_subst (fun _ => by simp)]

/-- **`π : F → F/H` is a homomorphism**: `π(F(X₀, X₁)) = G(π X₀, π X₁)`. -/
theorem pis_hom : subst (fun _ : Unit => FGL.ev F (X 0 : MvPowerSeries (Fin 2) O) (X 1)) (pis S) =
    FGL.ev (quot S) (subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) O)) (pis S))
      (subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) O)) (pis S)) := by
  rw [← piE_X_eq, ← piE_X_eq, ← E2_eq_ev (cc_piX S 0) (cc_piX S 1), ← E_pp_eq_E2, Gs_spec, PF,
    ← E2_eq_ev (by simp) (by simp), piE_eq S tn_E2X01,
    E_eq_subst (fun _ => by rw [E2_eq_ev (by simp) (by simp)]; exact FGL.cc_ev F (by simp) (by simp))]

/-- **uniqueness of the quotient law**: `G` is the only series with `π(F(X₀,X₁)) = G(π X₀, π X₁)`. -/
theorem quot_unique (G' : MvPowerSeries (Fin 2) O)
    (h : subst ![subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) O)) (pis S),
      subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) O)) (pis S)] G' =
      subst (fun _ : Unit => FGL.ev F (X 0 : MvPowerSeries (Fin 2) O) (X 1)) (pis S)) :
    G' = (quot S).toPowerSeries := by
  apply inj_pp S
  rw [quot_toPowerSeries, Gs_spec]
  have h2 := h.trans (pis_hom S)
  rw [← piE_X_eq, ← piE_X_eq, ← E2_eq_ev (cc_piX S 0) (cc_piX S 1), ← E_pp_eq_E2, Gs_spec,
    ← E_eq_subst (FGL.cc_vec2 (cc_piX S 0) (cc_piX S 1))] at h2
  rw [← h2]
  congr 1; funext i; fin_cases i <;> rfl

variable (p : ℕ)

/-- **the dual `π̌ : F/H → F` is a homomorphism**, given `π̌ ∘ π = [p]`. -/
theorem dual_hom (πd : MvPowerSeries Unit O) (hπd : subst (fun _ : Unit => pis S) πd = FGL.nmul F p) :
    subst (fun _ : Unit => FGL.ev (quot S) (X 0 : MvPowerSeries (Fin 2) O) (X 1)) πd =
      FGL.ev F (subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) O)) πd)
        (subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) O)) πd) := by
  have hcc : constantCoeff πd = 0 := by
    have := congrArg constantCoeff hπd
    rwa [FGL.cc_subst _ (fun _ => cc_pis S), FGL.cc_nmul] at this
  have hp' : E (fun _ : Unit => pis S) πd = FGL.nmul F p := by
    rw [E_eq_subst (fun _ => cc_pis S)]; exact hπd
  have cQ : constantCoeff (FGL.ev (quot S) (X 0 : MvPowerSeries (Fin 2) O) (X 1)) = 0 :=
    FGL.cc_ev (quot S) (by simp) (by simp)
  have c0 : constantCoeff (subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) O)) πd) = 0 :=
    FGL.cc0 _ (fun _ => by simp) hcc
  have c1 : constantCoeff (subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) O)) πd) = 0 :=
    FGL.cc0 _ (fun _ => by simp) hcc
  have hpp := adm_pp S (σ := Fin 2)
  apply inj_pp S
  -- left side
  have eQ : E (pp S) (FGL.ev (quot S) (X 0 : MvPowerSeries (Fin 2) O) (X 1)) =
      E (fun _ : Unit => E2 F (X 0 : MvPowerSeries (Fin 2) O) (X 1)) (pis S) := by
    rw [← E2_eq_ev (by simp) (by simp), E_E2 hpp (tn_X 0) (tn_X 1), E_pp_X, E_pp_X, ← E_pp_eq_E2,
      Gs_spec, PF, piE_eq S tn_E2X01]
  rw [E_subst (fun _ => cQ) hpp, eQ,
    ← E_E (fun _ => tn_of_cc (cc_pis S)) (fun _ => tn_E2X01), hp', nmul_hom]
  -- right side
  have eA : ∀ i : Fin 2, E (pp S) (subst (fun _ : Unit => (X i : MvPowerSeries (Fin 2) O)) πd) =
      E (fun _ : Unit => (X i : MvPowerSeries (Fin 2) O)) (FGL.nmul F p) := by
    intro i
    rw [E_subst (fun _ => by simp) hpp, E_pp_X, piE_eq S (tn_X i),
      ← E_E (fun _ => tn_of_cc (cc_pis S)) (fun _ => tn_X i), hp']
  rw [← E2_eq_ev c0 c1, E_E2 hpp (tn_of_cc c0) (tn_of_cc c1), eA, eA]

end Lubin
