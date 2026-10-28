import RamanujanTau.FormalGroupLayer.Endo

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Lubin
open MvPowerSeries MvPowerSeries.WithPiTopology

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [IsTopologicalRing O]
  [IsLinearTopology O O] [CompleteSpace O] [T2Space O]

section E
variable {σ τ υ : Type*}

/-- topological evaluation `f(a)` of a power series at a family of power series. -/
noncomputable def E (a : σ → MvPowerSeries τ O) (f : MvPowerSeries σ O) : MvPowerSeries τ O :=
  MvPowerSeries.eval₂ (algebraMap O (MvPowerSeries τ O)) a f

/-- evaluation `f(x)` of a power series at a point `x : σ → O`. -/
noncomputable def pt (x : σ → O) (f : MvPowerSeries σ O) : O :=
  MvPowerSeries.eval₂ (RingHom.id O) x f

/-- admissible families: topologically nilpotent constant coefficients. -/
def Adm (a : σ → MvPowerSeries τ O) : Prop := ∀ s, IsTopologicallyNilpotent (constantCoeff (a s))

/-- admissible points. -/
def AdmPt (x : σ → O) : Prop := ∀ s, IsTopologicallyNilpotent (x s)

lemma hasEval [Finite σ] {a : σ → MvPowerSeries τ O} (ha : Adm a) : HasEval a :=
  ⟨fun s => LinearTopology.isTopologicallyNilpotent_of_constantCoeff (ha s), by
    simp [Filter.cofinite_eq_bot]⟩

lemma hasEvalPt [Finite σ] {x : σ → O} (hx : AdmPt x) : HasEval x :=
  ⟨hx, by simp [Filter.cofinite_eq_bot]⟩

lemma adm_of_hasEval {a : σ → MvPowerSeries τ O} (ha : HasEval a) : Adm a := fun s =>
  (LinearTopology.isTopologicallyNilpotent_iff_constantCoeff (a s)).mp (ha.hpow s)

lemma adm_of_cc_zero {a : σ → MvPowerSeries τ O} (ha : ∀ s, constantCoeff (a s) = 0) : Adm a :=
  fun s => by rw [ha s]; exact IsTopologicallyNilpotent.zero

lemma adm_X : Adm (X : σ → MvPowerSeries σ O) := adm_of_cc_zero (fun s => by simp)

variable [Finite σ]

/-- `E a` as a ring homomorphism. -/
noncomputable def EH {a : σ → MvPowerSeries τ O} (ha : Adm a) : MvPowerSeries σ O →+* MvPowerSeries τ O :=
  eval₂Hom (continuous_algebraMap O (MvPowerSeries τ O)) (hasEval ha)

lemma EH_apply {a : σ → MvPowerSeries τ O} (ha : Adm a) (f : MvPowerSeries σ O) : EH ha f = E a f := by
  rw [EH, coe_eval₂Hom]; rfl

lemma continuous_E {a : σ → MvPowerSeries τ O} (ha : Adm a) : Continuous (E a) :=
  continuous_eval₂ (continuous_algebraMap O (MvPowerSeries τ O)) (hasEval ha)

/-- `pt x` as a ring homomorphism. -/
noncomputable def PH {x : σ → O} (hx : AdmPt x) : MvPowerSeries σ O →+* O :=
  eval₂Hom (show Continuous (RingHom.id O) from continuous_id) (hasEvalPt hx)

lemma PH_apply {x : σ → O} (hx : AdmPt x) (f : MvPowerSeries σ O) : PH hx f = pt x f := by
  rw [PH, coe_eval₂Hom]; rfl

lemma continuous_pt {x : σ → O} (hx : AdmPt x) : Continuous (pt x) :=
  continuous_eval₂ (show Continuous (RingHom.id O) from continuous_id) (hasEvalPt hx)

variable {a : σ → MvPowerSeries τ O}

lemma E_X (s : σ) : E a (X s) = a s := eval₂_X _ _ s
lemma E_C (r : O) : E a (C r) = C r := by rw [E, eval₂_C]; rfl
lemma pt_X {x : σ → O} (s : σ) : pt x (X s) = x s := eval₂_X _ _ s
lemma pt_C {x : σ → O} (r : O) : pt x (C r) = r := eval₂_C _ _ r

lemma E_add (ha : Adm a) (f g : MvPowerSeries σ O) : E a (f + g) = E a f + E a g := by
  simp only [← EH_apply ha, map_add]
lemma E_sub (ha : Adm a) (f g : MvPowerSeries σ O) : E a (f - g) = E a f - E a g := by
  simp only [← EH_apply ha, map_sub]
lemma E_mul (ha : Adm a) (f g : MvPowerSeries σ O) : E a (f * g) = E a f * E a g := by
  simp only [← EH_apply ha, map_mul]
lemma E_neg (ha : Adm a) (f : MvPowerSeries σ O) : E a (-f) = - E a f := by
  simp only [← EH_apply ha, map_neg]
lemma E_pow (ha : Adm a) (f : MvPowerSeries σ O) (n : ℕ) : E a (f ^ n) = E a f ^ n := by
  simp only [← EH_apply ha, map_pow]
lemma E_zero (ha : Adm a) : E a (0 : MvPowerSeries σ O) = 0 := by
  simp only [← EH_apply ha, map_zero]
lemma E_one (ha : Adm a) : E a (1 : MvPowerSeries σ O) = 1 := by
  simp only [← EH_apply ha, map_one]
lemma E_prod (ha : Adm a) {ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries σ O) :
    E a (∏ i ∈ s, f i) = ∏ i ∈ s, E a (f i) := by
  simp only [← EH_apply ha, map_prod]

lemma pt_add {x : σ → O} (hx : AdmPt x) (f g : MvPowerSeries σ O) : pt x (f + g) = pt x f + pt x g := by
  simp only [← PH_apply hx, map_add]
lemma pt_mul {x : σ → O} (hx : AdmPt x) (f g : MvPowerSeries σ O) : pt x (f * g) = pt x f * pt x g := by
  simp only [← PH_apply hx, map_mul]

/-- admissibility is preserved by evaluation. -/
lemma adm_E [Finite τ] {b : τ → MvPowerSeries υ O} (ha : Adm a) (hb : Adm b) :
    Adm (fun s => E b (a s)) :=
  adm_of_hasEval (by
    have := (hasEval ha).map (φ := EH hb) (by rw [show ⇑(EH hb) = E b from funext (EH_apply hb)]; exact continuous_E hb)
    simpa only [EH_apply] using this)

/-- **composition of evaluations**. -/
theorem E_E [Finite τ] {b : τ → MvPowerSeries υ O} (ha : Adm a) (hb : Adm b) (f : MvPowerSeries σ O) :
    E b (E a f) = E (fun s => E b (a s)) f := by
  have h := comp_eval₂ (continuous_algebraMap O (MvPowerSeries τ O)) (hasEval ha)
    (ε := EH hb) (by rw [show ⇑(EH hb) = E b from funext (EH_apply hb)]; exact continuous_E hb)
  have hc : (EH hb).comp (algebraMap O (MvPowerSeries τ O)) = algebraMap O (MvPowerSeries υ O) := by
    ext r : 1; simp only [RingHom.coe_comp, Function.comp_apply, EH_apply]
    rw [← c_eq_algebraMap, ← c_eq_algebraMap, E_C]
  have h2 : EH hb (E a f) = E (⇑(EH hb) ∘ a) f := by
    have := congrFun h f
    simp only [Function.comp_apply, hc] at this
    exact this
  rw [← EH_apply hb, h2]
  congr 1; funext s; exact EH_apply hb _

/-- evaluation at a point after evaluation at series. -/
theorem pt_E [Finite τ] {x : τ → O} (ha : Adm a) (hx : AdmPt x) (f : MvPowerSeries σ O) :
    pt x (E a f) = pt (fun s => pt x (a s)) f := by
  have h := comp_eval₂ (continuous_algebraMap O (MvPowerSeries τ O)) (hasEval ha)
    (ε := PH hx) (by rw [show ⇑(PH hx) = pt x from funext (PH_apply hx)]; exact continuous_pt hx)
  have hc : (PH hx).comp (algebraMap O (MvPowerSeries τ O)) = RingHom.id O := by
    ext r : 1; simp only [RingHom.coe_comp, Function.comp_apply, PH_apply]
    rw [← c_eq_algebraMap, pt_C]; rfl
  have h2 : PH hx (E a f) = pt (⇑(PH hx) ∘ a) f := by
    have := congrFun h f
    simp only [Function.comp_apply, hc] at this
    exact this
  rw [← PH_apply hx, h2]
  congr 1; funext s; exact PH_apply hx _

/-- evaluation at constants. -/
theorem E_const {x : σ → O} (hx : AdmPt x) (f : MvPowerSeries σ O) :
    E (fun s => (C (x s) : MvPowerSeries τ O)) f = C (pt x f) := by
  have h := comp_eval₂ (show Continuous (RingHom.id O) from continuous_id) (hasEvalPt hx) (ε := (C : O →+* MvPowerSeries τ O)) continuous_C
  have := congrFun h f
  simp only [Function.comp_apply, RingHom.comp_id] at this
  exact this.symm

/-- the constant coefficient of an evaluation. -/
theorem cc_E (ha : Adm a) (f : MvPowerSeries σ O) :
    constantCoeff (E a f) = pt (fun s => constantCoeff (a s)) f := by
  have h := comp_eval₂ (continuous_algebraMap O (MvPowerSeries τ O)) (hasEval ha)
    (ε := (constantCoeff : MvPowerSeries τ O →+* O)) (continuous_constantCoeff O)
  have hc : (constantCoeff : MvPowerSeries τ O →+* O).comp (algebraMap O (MvPowerSeries τ O)) =
      RingHom.id O := by
    ext r : 1; simp [← c_eq_algebraMap]
  have := congrFun h f
  simp only [Function.comp_apply, hc] at this
  exact this

end E

section Bridge
variable {σ τ : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq τ]

/-- substitution of series without constant term is continuous for the coefficientwise topology. -/
lemma continuous_subst' {a : σ → MvPowerSeries τ O} (ha : ∀ s, constantCoeff (a s) = 0) :
    Continuous (fun f : MvPowerSeries σ O => subst a f) := by
  classical
  apply continuous_pi
  intro e
  set N := Finsupp.degree e + 1
  have key : ∀ f : MvPowerSeries σ O, coeff e (subst a f) = ∑ d ∈ (Finsupp.finite_of_degree_lt N).toFinset,
      coeff d f * coeff e (d.prod fun i k => a i ^ k) := by
    intro f
    have h1 : coeff e (subst a f) = coeff e (subst a (truncTotal N f : MvPowerSeries σ O)) :=
      coeff_subst_congr ha N _ _ (fun d hd => by rw [MvPolynomial.coeff_coe, coeff_truncTotal _ hd]) e
        (by omega)
    rw [h1, subst_coe, truncTotal, truncFinset_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [MvPolynomial.aeval_monomial, ← c_eq_algebraMap, coeff_C_mul]
  exact (continuous_finsetSum _ fun d _ => (continuous_coeff O d).mul continuous_const).congr
    (fun f => (key f).symm)

/-- **bridge**: for substitutions without constant term, topological evaluation is substitution. -/
theorem E_eq_subst {a : σ → MvPowerSeries τ O} (ha : ∀ s, constantCoeff (a s) = 0)
    (f : MvPowerSeries σ O) : E a f = subst a f := by
  have := eval₂_unique (continuous_algebraMap O (MvPowerSeries τ O)) (hasEval (adm_of_cc_zero ha))
    (ε := subst a) (continuous_subst' ha) (fun p => by rw [subst_coe, MvPolynomial.aeval_def])
  exact (congrFun this f).symm

lemma E_X_self (f : MvPowerSeries σ O) : E (X : σ → MvPowerSeries σ O) f = f := by
  rw [E_eq_subst (fun s => by simp), subst_self]; rfl

/-- composing an evaluation with a substitution without constant term. -/
lemma E_subst {υ : Type*} [Fintype τ] {a : σ → MvPowerSeries τ O} (ha : ∀ s, constantCoeff (a s) = 0)
    {b : τ → MvPowerSeries υ O} (hb : Adm b) (f : MvPowerSeries σ O) :
    E b (subst a f) = E (fun s => E b (a s)) f := by
  rw [← E_eq_subst ha, E_E (adm_of_cc_zero ha) hb]

lemma pt_subst [Fintype τ] {a : σ → MvPowerSeries τ O} (ha : ∀ s, constantCoeff (a s) = 0)
    {x : τ → O} (hx : AdmPt x) (f : MvPowerSeries σ O) :
    pt x (subst a f) = pt (fun s => pt x (a s)) f := by
  rw [← E_eq_subst ha, pt_E (adm_of_cc_zero ha) hx]

/-- evaluation at `0` is the constant coefficient. -/
lemma pt_zero (f : MvPowerSeries σ O) : pt (fun _ : σ => (0 : O)) f = constantCoeff f := by
  have h := E_const (τ := σ) (fun _ => IsTopologicallyNilpotent.zero) f
  simp only [map_zero] at h
  rw [E_eq_subst (fun _ => by simp), FGL.subst_zeros] at h
  exact (C_injective (σ := σ) (R := O) h).symm

end Bridge

/-- `1 + t` is a unit for topologically nilpotent `t`. -/
lemma isUnit_one_add {t : O} (ht : IsTopologicallyNilpotent t) : IsUnit (1 + t) := by
  set u : MvPowerSeries Unit O := 1 + X () with hu
  have hcu : constantCoeff u = ((1 : Oˣ) : O) := by simp [hu]
  have hx : AdmPt (fun _ : Unit => t) := fun _ => ht
  have h := congrArg (pt (fun _ : Unit => t)) (mul_invOfUnit u 1 hcu)
  have h1 : pt (fun _ : Unit => t) u = 1 + t := by
    rw [hu, pt_add hx, show (1 : MvPowerSeries Unit O) = C 1 from (map_one C).symm, pt_C, pt_X]
  have h2 : pt (fun _ : Unit => t) (1 : MvPowerSeries Unit O) = 1 := by
    rw [show (1 : MvPowerSeries Unit O) = C 1 from (map_one C).symm, pt_C]
  rw [pt_mul hx, h1, h2] at h
  exact IsUnit.of_mul_eq_one _ h

section Coeff
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- the monomial evaluated at `X` with `X s ↦ C h`. -/
lemma prod_update (s : σ) (h : O) (d : σ →₀ ℕ) :
    (d.prod fun t n => (Function.update (X : σ → MvPowerSeries σ O) s (C h) t) ^ n) =
      C (h ^ d s) * monomial (d.erase s) 1 := by
  conv_lhs => rw [← Finsupp.single_add_erase s d]
  rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_single_index (by simp), Function.update_self, map_pow, monomial_one_eq]
  congr 1
  refine Finsupp.prod_congr fun t ht => ?_
  have : t ≠ s := by rintro rfl; simp at ht
  rw [Function.update_of_ne this]

/-- **coefficients of evaluation at `X s = h`**. -/
theorem hasSum_coeff_E_update (s : σ) {h : O} (hh : IsTopologicallyNilpotent h) (g : MvPowerSeries σ O)
    (e : σ →₀ ℕ) (he : e s = 0) :
    HasSum (fun n : ℕ => coeff (e + Finsupp.single s n) g * h ^ n)
      (coeff e (E (Function.update X s (C h)) g)) := by
  classical
  have ha : Adm (Function.update (X : σ → MvPowerSeries σ O) s (C h)) := by
    intro t; by_cases hts : t = s
    · subst hts; simpa using hh
    · rw [Function.update_of_ne hts]; simpa using IsTopologicallyNilpotent.zero
  have H := (hasSum_eval₂ (continuous_algebraMap O (MvPowerSeries σ O)) (hasEval ha) g).map
    (coeff e) (continuous_coeff O e)
  simp only [Function.comp_def] at H
  simp only [prod_update, ← c_eq_algebraMap, ← mul_assoc, ← map_mul, coeff_C_mul, coeff_monomial] at H
  have hinj : Function.Injective (fun n : ℕ => e + Finsupp.single s n) := by
    intro m n hmn
    have := congrArg (fun d => d s) hmn
    simpa using this
  rw [← hinj.hasSum_iff] at H
  · convert H using 1
    funext n
    simp only [Function.comp_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, he,
      zero_add]
    rw [if_pos]
    · ring
    · ext t; by_cases hts : t = s
      · subst hts; simp [he]
      · simp [Finsupp.erase_ne hts]
  · intro d hd
    rw [if_neg, mul_zero]
    rintro hed
    apply hd
    refine ⟨d s, ?_⟩
    simp only
    rw [hed, Finsupp.erase_add_single]

/-- evaluation at `X s = h` has no `X s`. -/
theorem coeff_E_update_of_ne (s : σ) {h : O} (hh : IsTopologicallyNilpotent h) (g : MvPowerSeries σ O)
    (e : σ →₀ ℕ) (he : e s ≠ 0) : coeff e (E (Function.update X s (C h)) g) = 0 := by
  classical
  have ha : Adm (Function.update (X : σ → MvPowerSeries σ O) s (C h)) := by
    intro t; by_cases hts : t = s
    · subst hts; simpa using hh
    · rw [Function.update_of_ne hts]; simpa using IsTopologicallyNilpotent.zero
  have H := (hasSum_eval₂ (continuous_algebraMap O (MvPowerSeries σ O)) (hasEval ha) g).map
    (coeff e) (continuous_coeff O e)
  simp only [Function.comp_def] at H
  simp only [prod_update, ← c_eq_algebraMap, ← mul_assoc, ← map_mul, coeff_C_mul, coeff_monomial] at H
  have h0 : ∀ d : σ →₀ ℕ, (if e = d.erase s then (1 : O) else 0) = 0 := by
    intro d; rw [if_neg]; rintro rfl; simp at he
  simp only [h0, mul_zero] at H
  exact H.unique hasSum_zero

end Coeff

end Lubin
