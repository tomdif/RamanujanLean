/-
# Formal logarithms over a `ℚ`-algebra, and "differential ⇒ homomorphism"

Over a commutative `ℚ`-algebra `R`, for commutative formal groups `F₁, F₂`:
* `eq_C_of_pd_eq_zero`: a power series with all partial derivatives `0` is constant.
* `log F` (`L` with `L(0) = 0`, `L'(T) Ψ_F(T) = 1`, i.e. `dL = ω_F`) and **`log_hom`**:
  `L(F(X,Y)) = L(X) + L(Y)`.
* **`hom_of_invariant`** (converse of `FGL.hom_invariant`): a series `φ` with `φ(0) = 0` and
  `φ'(T)·Ψ_{F₁}(T) = Ψ_{F₂}(φ(T))·φ'(0)` (i.e. `φ^*ω₂ = φ'(0)·ω₁`) is a homomorphism `F₁ → F₂`.

This is the step of the Vélu–Lubin link that turns Vélu's `invariant_differential` (`π^*ω' = ω`)
into the homomorphism property of the formal Vélu map (over `K`, characteristic `0`).
-/
import RamanujanTau.EllipticI2.Step3

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EllipticI2.Log
open MvPowerSeries FGL

variable {R : Type*} [CommRing R] [Algebra ℚ R]

lemma isUnit_natCast_succ (n : ℕ) : IsUnit ((n : R) + 1) := by
  have h : ((n : R) + 1) = algebraMap ℚ R ((n : ℚ) + 1) := by simp
  rw [h]
  exact (IsUnit.mk0 _ (by positivity)).map _

/-- **a series with all partial derivatives `0` is constant.** -/
theorem eq_C_of_pd_eq_zero {σ : Type*} [DecidableEq σ] (g : MvPowerSeries σ R)
    (h : ∀ i, pd i g = 0) : g = C (constantCoeff g) := by
  ext e
  by_cases he : e = 0
  · subst he; simp
  · obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
      by_contra hc; push Not at hc; exact he (Finsupp.ext hc)
    set e' := e - Finsupp.single i 1
    have hee : e' + Finsupp.single i 1 = e := by
      ext j; simp only [e', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
      by_cases hj : j = i
      · subst hj; simp; omega
      · simp [Ne.symm hj]
    have h1 := congrArg (coeff e') (h i)
    rw [coeff_pd, hee, map_zero] at h1
    rw [coeff_C, if_neg he]
    exact (isUnit_natCast_succ (e' i)).mul_left_eq_zero.mp h1

/-! ### The formal logarithm -/

/-- the antiderivative of a one-variable series, with zero constant term. -/
noncomputable def integ (ν : MvPowerSeries Unit R) : MvPowerSeries Unit R :=
  fun e => if e () = 0 then 0 else algebraMap ℚ R ((e () : ℚ))⁻¹ * coeff (e - Finsupp.single () 1) ν

lemma cc_integ (ν : MvPowerSeries Unit R) : constantCoeff (integ ν) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  change (if (0 : Unit →₀ ℕ) () = 0 then (0 : R) else algebraMap ℚ R (((0 : Unit →₀ ℕ) () : ℕ) : ℚ)⁻¹ *
    coeff ((0 : Unit →₀ ℕ) - Finsupp.single () 1) ν) = 0
  simp

lemma pd_integ (ν : MvPowerSeries Unit R) : pd () (integ ν) = ν := by
  refine MvPowerSeries.ext fun e => ?_
  rw [coeff_pd]
  show (if (e + Finsupp.single () 1 : Unit →₀ ℕ) () = 0 then 0 else
      algebraMap ℚ R (((e + Finsupp.single () 1 : Unit →₀ ℕ) () : ℕ) : ℚ)⁻¹ *
        coeff (e + Finsupp.single () 1 - Finsupp.single () 1) ν) * ((e () : R) + 1) = coeff e ν
  rw [if_neg (by simp), add_tsub_cancel_right]
  have : ((e () : R) + 1) = algebraMap ℚ R (((e + Finsupp.single () 1 : Unit →₀ ℕ) () : ℕ) : ℚ) := by
    simp
  rw [this, mul_comm, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (by simp; positivity), map_one, one_mul]

variable (F : FormalGroup R)

local notation "Fs" => (F.toPowerSeries : MvPowerSeries (Fin 2) R)

lemma cc_Ψ : constantCoeff (Ψ F (T : MvPowerSeries Unit R)) = 1 := by
  have hv : ∀ s, constantCoeff ((![T, 0] : Fin 2 → MvPowerSeries Unit R) s) = 0 := cc_T0
  show constantCoeff (subst ![T, 0] (pd 1 Fs)) = 1
  rw [cc_subst _ hv, ← coeff_zero_eq_constantCoeff_apply, coeff_pd, zero_add]
  simp [F.lin_coeff_Y]

/-- `ν = 1/Ψ_F`. -/
noncomputable def nu : MvPowerSeries Unit R := invOfUnit (Ψ F (T : MvPowerSeries Unit R)) 1

lemma Ψ_mul_nu : Ψ F (T : MvPowerSeries Unit R) * nu F = 1 :=
  mul_invOfUnit _ _ (by rw [cc_Ψ]; rfl)

/-- **the formal logarithm** `L = ∫ ω_F`. -/
noncomputable def log : MvPowerSeries Unit R := integ (nu F)

lemma cc_log : constantCoeff (log F) = 0 := cc_integ _

lemma pd_log_mul_Ψ : pd () (log F) * Ψ F (T : MvPowerSeries Unit R) = 1 := by
  rw [log, pd_integ, mul_comm, Ψ_mul_nu]

/-- `L(a)`. -/
noncomputable abbrev Lof {β : Type*} (a : MvPowerSeries β R) : MvPowerSeries β R :=
  subst (fun _ : Unit => a) (log F)

lemma h1' {β : Type*} {a : MvPowerSeries β R} (ha : constantCoeff a = 0) :
    ∀ s : Unit, constantCoeff ((fun _ : Unit => a) s) = 0 := fun _ => ha

lemma subst_Ψ {β : Type*} [Finite β] {a : MvPowerSeries β R} (ha : constantCoeff a = 0) :
    subst (fun _ : Unit => a) (Ψ F (T : MvPowerSeries Unit R)) = Ψ F a := by
  have hv : ∀ s, constantCoeff ((![T, 0] : Fin 2 → MvPowerSeries Unit R) s) = 0 := cc_T0
  show subst _ (subst ![T, 0] (pd 1 Fs)) = subst ![a, 0] (pd 1 Fs)
  rw [ss _ _ hv (h1' ha)]
  congr 1; funext s; fin_cases s
  · exact sX _ (h1' ha) ()
  · exact s0 _ (h1' ha)

/-- `L'(a)·Ψ(a) = 1`. -/
lemma pdlog_at {β : Type*} [Finite β] {a : MvPowerSeries β R} (ha : constantCoeff a = 0) :
    subst (fun _ : Unit => a) (pd () (log F)) * Ψ F a = 1 := by
  have h := congrArg (subst (fun _ : Unit => a)) (pd_log_mul_Ψ F)
  have e1 : subst (fun _ : Unit => a) (1 : MvPowerSeries Unit R) = 1 := by
    rw [← coe_substAlgHom (hs (h1' ha))]; exact map_one _
  rwa [subst_mul (hs (h1' ha)), subst_Ψ F ha, e1] at h

lemma pd_Lof {β : Type*} [Fintype β] [DecidableEq β] {a : MvPowerSeries β R}
    (ha : constantCoeff a = 0) (j : β) :
    pd j (Lof F a) = subst (fun _ : Unit => a) (pd () (log F)) * pd j a := by
  rw [Lof, pd_subst (h1' ha), Fintype.sum_unique]

lemma cc_Lof {β : Type*} [Finite β] {a : MvPowerSeries β R} (ha : constantCoeff a = 0) :
    constantCoeff (Lof F a) = 0 := cc0 _ (h1' ha) (cc_log F)

lemma subst_Lof {β γ : Type*} [Finite β] [Finite γ] {a : MvPowerSeries β R}
    (ha : constantCoeff a = 0) (c : β → MvPowerSeries γ R) (hc : ∀ s, constantCoeff (c s) = 0) :
    subst c (Lof F a) = Lof F (subst c a) := by
  rw [Lof, ss _ _ (h1' ha) hc]

/-- **the logarithm is a homomorphism to `Ĝₐ`**: `L(F(X,Y)) = L(X) + L(Y)`. -/
theorem log_hom [F.IsComm] :
    Lof F (ev F (X 0 : MvPowerSeries (Fin 2) R) (X 1)) =
      Lof F (X 0 : MvPowerSeries (Fin 2) R) + Lof F (X 1) := by
  have X0 : constantCoeff (X 0 : MvPowerSeries (Fin 2) R) = 0 := by simp
  have X1 : constantCoeff (X 1 : MvPowerSeries (Fin 2) R) = 0 := by simp
  have hE := cc_ev F X0 X1
  set D := Lof F (ev F (X 0 : MvPowerSeries (Fin 2) R) (X 1)) - Lof F (X 0) - Lof F (X 1) with hD
  -- `∂₂ D = 0`
  have hd1 : pd 1 D = 0 := by
    rw [hD, pd_sub, pd_sub, pd_Lof F hE, pd_Lof F X0, pd_Lof F X1, pd_ev F _ _ X0 X1]
    simp only [pd_X', show (0 : Fin 2) ≠ 1 by decide, if_false, if_true, mul_zero, zero_add, mul_one,
      sub_zero]
    have i1 := invariance F (X 0 : MvPowerSeries (Fin 2) R) (X 1) X0 X1
    have l1 := pdlog_at F hE
    have l2 := pdlog_at F X1
    rw [i1] at l1
    linear_combination (subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) (pd () (log F))) * l1 -
      (subst (fun _ : Unit => ev F (X 0 : MvPowerSeries (Fin 2) R) (X 1)) (pd () (log F)) *
        subst ![X 0, X 1] (pd 1 Fs)) * l2
  -- symmetry `D(Y, X) = D(X, Y)`
  have hsw : ∀ s, constantCoeff ((![X 1, X 0] : Fin 2 → MvPowerSeries (Fin 2) R) s) = 0 :=
    cc_vec2 X1 X0
  have hDs : subst ![X 1, X 0] D = D := by
    rw [hD, subst_sub (hs hsw), subst_sub (hs hsw), subst_Lof F hE _ hsw, subst_Lof F X0 _ hsw,
      subst_Lof F X1 _ hsw, subst_ev F _ _ _ X0 X1 hsw, sX _ hsw, sX _ hsw]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [ev_comm F _ _ X1 X0]; ring
  have hd0 : pd 0 D = 0 := by
    rw [← hDs, pd_subst hsw, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, pd_X',
      show (1 : Fin 2) ≠ 0 by decide, if_false, if_true, mul_zero, zero_add, mul_one, hd1]
    exact s0 _ hsw
  have hcc : constantCoeff D = 0 := by
    rw [hD, map_sub, map_sub, cc_Lof F hE, cc_Lof F X0, cc_Lof F X1]; simp
  have hD0 : D = 0 := by
    rw [eq_C_of_pd_eq_zero D (fun i => by fin_cases i; exacts [hd0, hd1]), hcc, map_zero]
  rw [hD] at hD0
  linear_combination hD0

/-- `L` has linear coefficient `1`. -/
lemma coeff_one_log : coeff (Finsupp.single () 1) (log F) = 1 := by
  have h := congrArg constantCoeff (pd_log_mul_Ψ F)
  rw [map_mul, cc_Ψ, mul_one, map_one, ← coeff_zero_eq_constantCoeff_apply, coeff_pd, zero_add] at h
  simpa using h

/-- **`L ∘ ·` is injective** on series without constant term. -/
lemma Lof_inj {β : Type*} [Finite β] {a b : MvPowerSeries β R} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) (h : Lof F a = Lof F b) : a = b := by
  set f : PowerSeries R := log F
  have hf0 : PowerSeries.constantCoeff f = 0 := cc_log F
  have hu : IsUnit (PowerSeries.coeff 1 f) := by
    rw [show PowerSeries.coeff 1 f = coeff (Finsupp.single () 1) (log F) from rfl, coeff_one_log]
    exact isUnit_one
  set g := PowerSeries.substInvOfIsUnit f hu
  have hgf : PowerSeries.subst f g = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_left f hf0 hu
  have hf0' : ∀ s : Unit, constantCoeff ((fun _ : Unit => (f : MvPowerSeries Unit R)) s) = 0 :=
    fun _ => hf0
  have key : ∀ c : MvPowerSeries β R, constantCoeff c = 0 →
      subst (fun _ : Unit => Lof F c) (g : MvPowerSeries Unit R) = c := by
    intro c hc
    have e : subst (fun _ : Unit => Lof F c) (g : MvPowerSeries Unit R) =
        subst (fun _ : Unit => c) (subst (fun _ : Unit => (f : MvPowerSeries Unit R)) g) := by
      rw [ss _ _ hf0' (h1' hc)]
    rw [e]
    have : subst (fun _ : Unit => (f : MvPowerSeries Unit R)) (g : MvPowerSeries Unit R) = X () :=
      hgf
    rw [this, sX _ (h1' hc)]
  rw [← key a ha, ← key b hb, h]

/-! ### Differential ⇒ homomorphism -/

variable (F₂ : FormalGroup R)

/-- **converse of `hom_invariant`** (characteristic `0`): if `φ(0) = 0` and
`φ'(T)·Ψ_{F₁}(T) = Ψ_{F₂}(φ(T))·φ'(0)`, then `φ(F₁(X,Y)) = F₂(φ X, φ Y)`. -/
theorem hom_of_invariant [F.IsComm] [F₂.IsComm] (φ : MvPowerSeries Unit R)
    (hφ : constantCoeff φ = 0)
    (hinv : pd () φ * Ψ F (T : MvPowerSeries Unit R) =
      Ψ F₂ φ * C (coeff (Finsupp.single () 1) φ)) :
    Hom F F₂ φ := by
  set c := coeff (Finsupp.single () 1) φ
  -- `L₂(φ) = c L₁`
  have hLφ : Lof F₂ φ = C c * log F := by
    have hd : pd () (Lof F₂ φ - C c * log F) = 0 := by
      rw [pd_sub, pd_Lof F₂ hφ, pd_mul, pd_C, zero_mul, zero_add]
      have l2 := pdlog_at F₂ hφ
      have l1 := pd_log_mul_Ψ F
      linear_combination (-(subst (fun _ : Unit => φ) (pd () (log F₂)) * pd () φ)) * l1 +
        (subst (fun _ : Unit => φ) (pd () (log F₂)) * pd () (log F)) * hinv + (C c * pd () (log F)) * l2
    have hc : constantCoeff (Lof F₂ φ - C c * log F) = 0 := by
      rw [map_sub, cc_Lof F₂ hφ, map_mul, cc_log]; simp
    have := eq_C_of_pd_eq_zero (Lof F₂ φ - C c * log F) (fun i => by cases i; exact hd)
    rw [hc, map_zero] at this
    exact sub_eq_zero.mp this
  have X0 : constantCoeff (X 0 : MvPowerSeries (Fin 2) R) = 0 := by simp
  have X1 : constantCoeff (X 1 : MvPowerSeries (Fin 2) R) = 0 := by simp
  have hE := cc_ev F X0 X1
  set φ0 := subst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) R)) φ
  set φ1 := subst (fun _ : Unit => (X 1 : MvPowerSeries (Fin 2) R)) φ
  have hφ0 : constantCoeff φ0 = 0 := cc0 _ (h1' X0) hφ
  have hφ1 : constantCoeff φ1 = 0 := cc0 _ (h1' X1) hφ
  have hv := cc_vec2 hφ0 hφ1
  -- `L₂(φ(a)) = c L₁(a)`
  have hLa : ∀ a : MvPowerSeries (Fin 2) R, constantCoeff a = 0 →
      Lof F₂ (subst (fun _ : Unit => a) φ) = C c * Lof F a := by
    intro a ha
    rw [← subst_Lof F₂ hφ _ (h1' ha), hLφ, subst_mul (hs (h1' ha)), subst_C]
  refine ⟨hφ, Lof_inj F₂ (cc0 _ (h1' hE) hφ) (cc_ev F₂ hφ0 hφ1) ?_⟩
  rw [hLa _ hE, log_hom F]
  have h2 := congrArg (subst ![φ0, φ1]) (log_hom F₂)
  rw [subst_Lof F₂ (cc_ev F₂ X0 X1) _ hv, subst_ev F₂ _ _ _ X0 X1 hv, sX _ hv, sX _ hv,
    subst_add (hs hv), subst_Lof F₂ X0 _ hv, subst_Lof F₂ X1 _ hv, sX _ hv, sX _ hv] at h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h2
  rw [h2, hLa _ X0, hLa _ X1, mul_add]

end EllipticI2.Log
