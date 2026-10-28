/-
# Lubin's lemma: `H`-invariant series are series in `π`

Fix a variable `s`. If `f ∈ O⟦σ⟧` is invariant under `X s ↦ F(X s, h)` for all `h ∈ H`, then
`f = g(…, π(X s), …)` for a unique `g` (substituting `π(X s)` for `X s`).
-/
import RamanujanTau.LubinQuotient.Pi

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Lubin
open MvPowerSeries MvPowerSeries.WithPiTopology

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [IsTopologicalRing O]
  [IsLinearTopology O O] [CompleteSpace O] [T2Space O]

variable {F : FormalGroup O} [F.IsComm] (S : FinSub F)
variable {σ : Type*} [Fintype σ] [DecidableEq σ] (s : σ)

/-- translation of the variable `s` by `h`: `X s ↦ F(X s, h)`. -/
noncomputable def trs (h : O) : σ → MvPowerSeries σ O :=
  Function.update X s (E2 F (X s) (C h))

/-- `X s ↦ π(X s)`. -/
noncomputable def bs : σ → MvPowerSeries σ O := Function.update X s (piE S (X s))

/-- `f` is `H`-invariant in the variable `s`. -/
def Inv (f : MvPowerSeries σ O) : Prop := ∀ h ∈ S.H, E (trs (F := F) s h) f = f

lemma tn_E2X {h : O} (hh : IsTopologicallyNilpotent h) : TN (E2 F (X s : MvPowerSeries σ O) (C h)) := by
  apply tn_E2 (tn_X s) (tn_C hh)
  simp only [constantCoeff_X, constantCoeff_C]; rw [zero_padd hh]; exact hh

lemma adm_trs {h : O} (hh : IsTopologicallyNilpotent h) : Adm (trs (F := F) s h) :=
  adm_update s (tn_E2X s hh)

lemma cc_piX : constantCoeff (piE S (X s : MvPowerSeries σ O)) = 0 := cc_piE S (by simp)

lemma adm_bs : Adm (bs S s) := adm_update s (tn_of_cc (cc_piX S s))

lemma ev_add' {h : O} (hh : IsTopologicallyNilpotent h) (f g : MvPowerSeries σ O) :
    ev s h (f + g) = ev s h f + ev s h g := E_add (adm_ev s hh) f g
lemma ev_sub' {h : O} (hh : IsTopologicallyNilpotent h) (f g : MvPowerSeries σ O) :
    ev s h (f - g) = ev s h f - ev s h g := E_sub (adm_ev s hh) f g
lemma ev_mul' {h : O} (hh : IsTopologicallyNilpotent h) (f g : MvPowerSeries σ O) :
    ev s h (f * g) = ev s h f * ev s h g := E_mul (adm_ev s hh) f g

lemma trs_ne {h : O} {t : σ} (ht : t ≠ s) : trs (F := F) s h t = X t := Function.update_of_ne ht _ _
lemma bs_self : bs S s s = piE S (X s) := Function.update_self _ _ _
lemma bs_ne {t : σ} (ht : t ≠ s) : bs S s t = X t := Function.update_of_ne ht _ _

variable [IsDomain O]

/-- `π(X s) = ∏ (X s - h) · U` with `U` a unit. -/
lemma piX_factor : ∃ U : MvPowerSeries σ O, IsUnit U ∧
    piE S (X s) = (∏ h ∈ S.H, (X s - C h)) * U := by
  obtain ⟨U, hU, hpi⟩ := pis_factor S
  have hv : Adm (fun _ : Unit => (X s : MvPowerSeries σ O)) := fun _ => tn_X s
  refine ⟨E (fun _ : Unit => X s) U, by rw [← EH_apply hv]; exact hU.map _, ?_⟩
  rw [piE_eq S (tn_X s), hpi, E_mul hv, E_prod hv]
  congr 1
  refine Finset.prod_congr rfl fun h _ => ?_
  rw [E_sub hv, E_X, E_C]

lemma piX_ne_zero : piE S (X s : MvPowerSeries σ O) ≠ 0 := by
  obtain ⟨U, hU, hpi⟩ := piX_factor S s
  rw [hpi]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun h _ => ?_) hU.ne_zero
  intro heq
  have := congrArg (coeff (Finsupp.single s 1)) heq
  rw [map_sub, coeff_X, if_pos rfl, coeff_C, if_neg (by
    intro h0; have := congrArg (fun d => d s) h0; simp at this), sub_zero, map_zero] at this
  exact one_ne_zero this

lemma ev0_trs {h : O} (hh : IsTopologicallyNilpotent h) (t : σ) :
    ev s 0 (trs (F := F) s h t) = Function.update X s (C h) t := by
  by_cases hts : t = s
  · subst hts
    rw [trs, Function.update_self, Function.update_self, ev, E_E2 (adm_ev t tn0) (tn_X t) (tn_C hh),
      E_X, Function.update_self, E_C, E2_C tn0 hh, zero_padd hh]
  · rw [trs_ne s hts, Function.update_of_ne hts, ev_X_ne s t 0 hts]

/-- an invariant series takes the same value at all `X s = h`, `h ∈ H`. -/
lemma inv_ev {f : MvPowerSeries σ O} (hf : Inv S s f) {h : O} (hh : h ∈ S.H) : ev s h f = ev s 0 f := by
  have h1 : ev s 0 (E (trs (F := F) s h) f) = ev s 0 f := by rw [hf h hh]
  have h2 : ev s 0 (E (trs (F := F) s h) f) = E (fun t => ev s 0 (trs (F := F) s h t)) f :=
    E_E (adm_trs s (S.tn h hh)) (adm_ev s tn0) f
  rw [← h1, h2]
  unfold ev
  congr 1; funext t; exact (ev0_trs s (S.tn h hh) t).symm

/-- **descent step**: `f = f|_{X s = 0} + π(X s) · f₁` with `f₁` invariant. -/
lemma step {f : MvPowerSeries σ O} (hf : Inv S s f) :
    ∃ f1, Inv S s f1 ∧ f = ev s 0 f + piE S (X s) * f1 := by
  obtain ⟨q, hq⟩ := dvd_of_vanish s S.H S.tn (f - ev s 0 f) (fun h hh => by
    rw [ev_sub' s (S.tn h hh), inv_ev S s hf hh, ev_free s (S.tn h hh) (free_ev s tn0 f), sub_self])
  obtain ⟨U, hU, hpi⟩ := piX_factor S s
  obtain ⟨u, rfl⟩ := hU
  have hdec : f - ev s 0 f = piE S (X s) * (q * ↑u⁻¹) := by
    rw [hpi, hq]
    have : (↑u : MvPowerSeries σ O) * ↑u⁻¹ = 1 := Units.mul_inv u
    linear_combination (-(∏ h ∈ S.H, (X s - C h)) * q) * this
  refine ⟨q * ↑u⁻¹, ?_, by linear_combination hdec⟩
  intro h hh
  have ha := adm_trs (F := F) s (S.tn h hh)
  have e1 : E (trs (F := F) s h) (f - ev s 0 f) = f - ev s 0 f := by
    rw [E_sub ha, hf h hh, E_free s ha (fun t ht => trs_ne s ht) (free_ev s tn0 f)]
  have e2 : E (trs (F := F) s h) (piE S (X s)) = piE S (X s) := by
    rw [E_piE S ha (tn_X s), E_X, trs, Function.update_self, piE_translate S (tn_X s) hh]
  have := congrArg (E (trs (F := F) s h)) hdec
  rw [e1, E_mul ha, e2, hdec] at this
  exact (mul_left_cancel₀ (piX_ne_zero S s) this).symm

/-- gluing a sequence of `s`-free series into `Σ_k c_k X_s^k`. -/
noncomputable def glue (c : ℕ → MvPowerSeries σ O) : MvPowerSeries σ O :=
  fun e => coeff (e.erase s) (c (e s))

omit [IsDomain O] in
lemma glue_decomp (c : ℕ → MvPowerSeries σ O) (hc : ∀ k, Free s (c k)) :
    glue s c = c 0 + X s * glue s (fun k => c (k + 1)) := by
  ext e
  rw [map_add, coeff_X_mul']
  change coeff (e.erase s) (c (e s)) = _
  by_cases he : e s = 0
  · have hee : e.erase s = e := by
      ext t; by_cases hts : t = s
      · subst hts; simp [he]
      · simp [Finsupp.erase_ne hts]
    rw [if_neg, add_zero, he, hee]
    intro hle; have := hle s; simp [he] at this
  · rw [if_pos, hc 0 e he, zero_add]
    · change _ = coeff ((e - Finsupp.single s 1).erase s) (c ((e - Finsupp.single s 1 : σ →₀ ℕ) s + 1))
      have h1 : (e - Finsupp.single s 1).erase s = e.erase s := by
        ext t; by_cases hts : t = s
        · subst hts; simp
        · simp [Finsupp.erase_ne hts, Finsupp.single_eq_of_ne hts]
      have h2 : (e - Finsupp.single s 1 : σ →₀ ℕ) s + 1 = e s := by simp; omega
      rw [h1, h2]
    · intro t; by_cases hts : t = s
      · subst hts; simp; omega
      · simp [Finsupp.single_eq_of_ne hts]

omit [IsDomain O] in
lemma E_glue (c : ℕ → MvPowerSeries σ O) (hc : ∀ k, Free s (c k)) :
    E (bs S s) (glue s c) = c 0 + piE S (X s) * E (bs S s) (glue s (fun k => c (k + 1))) := by
  have hb := adm_bs S s
  conv_lhs => rw [glue_decomp s c hc]
  rw [E_add hb, E_mul hb, E_X, bs_self,
    E_free s hb (fun t ht => bs_ne S s ht) (hc 0)]

omit [IsDomain O] in
lemma glue_diff (N : ℕ) (c f : ℕ → MvPowerSeries σ O) (hc : ∀ k, Free s (c k))
    (hrel : ∀ k, f k = c k + piE S (X s) * f (k + 1)) :
    E (bs S s) (glue s c) - f 0 =
      piE S (X s) ^ N * (E (bs S s) (glue s (fun k => c (k + N))) - f N) := by
  induction N generalizing c f with
  | zero => simp
  | succ N ih =>
    have := ih (fun k => c (k + 1)) (fun k => f (k + 1)) (fun k => hc _) (fun k => hrel _)
    beta_reduce at this
    have hfun : (fun k => c (k + N + 1)) = fun k => c (k + (N + 1)) := by
      funext k; rw [add_assoc]
    rw [hfun, zero_add] at this
    rw [E_glue S s c hc, hrel 0, zero_add]
    linear_combination piE S (X s) * this

omit [IsDomain O] in
/-- a series divisible by every power of a series without constant term is `0`. -/
lemma eq_zero_of_dvd_pow {p D : MvPowerSeries σ O} (hp : constantCoeff p = 0)
    (h : ∀ N : ℕ, ∃ w, D = p ^ N * w) : D = 0 := by
  ext e
  obtain ⟨w, hw⟩ := h (Finsupp.degree e + 1)
  rw [hw, map_zero]
  apply coeff_of_lt_order
  refine lt_of_lt_of_le ?_ (le_trans (le_trans (le_order_pow_of_constantCoeff_eq_zero _ hp)
    le_self_add) le_order_mul)
  exact_mod_cast Nat.lt_succ_self _

/-- **Lubin's lemma (existence)**: an `H`-invariant series is a series in `π(X s)`. -/
theorem descent {f : MvPowerSeries σ O} (hf : Inv S s f) : ∃ g, E (bs S s) g = f := by
  classical
  have hstep := fun f (hf : Inv S s f) => step S s hf
  let nxt : MvPowerSeries σ O → MvPowerSeries σ O := fun f =>
    if hf : Inv S s f then Classical.choose (hstep f hf) else 0
  have hnxt : ∀ f, Inv S s f → Inv S s (nxt f) ∧ f = ev s 0 f + piE S (X s) * nxt f := by
    intro f hf
    simp only [nxt, dif_pos hf]
    exact Classical.choose_spec (hstep f hf)
  let fs : ℕ → MvPowerSeries σ O := fun k => nxt^[k] f
  have hfs_inv : ∀ k, Inv S s (fs k) := by
    intro k
    induction k with
    | zero => exact hf
    | succ k ih =>
      simp only [fs, Function.iterate_succ_apply']
      exact (hnxt _ ih).1
  have hrel : ∀ k, fs k = ev s 0 (fs k) + piE S (X s) * fs (k + 1) := by
    intro k
    have := (hnxt _ (hfs_inv k)).2
    simp only [fs, Function.iterate_succ_apply'] at this ⊢
    exact this
  refine ⟨glue s (fun k => ev s 0 (fs k)), ?_⟩
  have hD := eq_zero_of_dvd_pow (cc_piX S s) (fun N => ⟨_, glue_diff S s N (fun k => ev s 0 (fs k)) fs
    (fun k => free_ev s tn0 _) hrel⟩)
  rw [sub_eq_zero] at hD
  exact hD

lemma E_bs_decomp (g : MvPowerSeries σ O) :
    E (bs S s) g = ev s 0 g + piE S (X s) * E (bs S s) (shift s g) := by
  have hb := adm_bs S s
  conv_lhs => rw [decomp s g]
  rw [E_add hb, E_mul hb, E_X, bs_self,
    E_free s hb (fun t ht => bs_ne S s ht) (free_ev s tn0 g)]

lemma ev0_piX : ev s 0 (piE S (X s : MvPowerSeries σ O)) = 0 := by
  rw [show ev s 0 (piE S (X s : MvPowerSeries σ O)) = piE S (ev s 0 (X s)) from
    E_piE S (adm_ev s tn0) (tn_X s), ev_X_self, piE]
  exact Finset.prod_eq_zero S.zero_mem (by rw [E2_C tn0 tn0, padd_zero tn0, map_zero])

lemma ev0_of_E_bs {g : MvPowerSeries σ O} (hg : E (bs S s) g = 0) : ev s 0 g = 0 := by
  have h2 := congrArg (ev s 0) (E_bs_decomp S s g)
  rw [hg, ev_add' s tn0, ev_mul' s tn0, ev0_piX, zero_mul, add_zero,
    ev_free s tn0 (free_ev s tn0 g)] at h2
  rw [← h2]
  exact E_zero (adm_ev s tn0)

/-- **Lubin's lemma (uniqueness)**: substituting `π(X s)` for `X s` is injective. -/
theorem inj {g : MvPowerSeries σ O} (hg : E (bs S s) g = 0) : g = 0 := by
  have key : ∀ k, ∀ g : MvPowerSeries σ O, E (bs S s) g = 0 → ev s 0 ((shift s)^[k] g) = 0 := by
    intro k
    induction k with
    | zero => intro g hg; exact ev0_of_E_bs S s hg
    | succ k ih =>
      intro g hg
      rw [Function.iterate_succ_apply]
      apply ih
      have h1 := E_bs_decomp S s g
      rw [hg, ev0_of_E_bs S s hg, zero_add] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left (piX_ne_zero S s)
  ext e
  have := congrArg (coeff (e.erase s)) (key (e s) g hg)
  rw [coeff_ev_zero, if_pos (by simp), coeff_shift_iter, Finsupp.erase_add_single, map_zero] at this
  rw [this, map_zero]

theorem inj' {g g' : MvPowerSeries σ O} (h : E (bs S s) g = E (bs S s) g') : g = g' := by
  rw [← sub_eq_zero]
  apply inj S s
  rw [E_sub (adm_bs S s), h, sub_self]

end Lubin
