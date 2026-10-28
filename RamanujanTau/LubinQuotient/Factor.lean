/-
# Evaluation at `X s = h` and the factor theorem

For `f ∈ O⟦σ⟧`, a variable `s` and a topologically nilpotent `h ∈ O`, `ev s h f` is `f` with
`X s ↦ h`. We prove: `f - ev s h f = (X s - h) · q` (factor theorem), and that a series vanishing
at finitely many distinct points `h` is divisible by `∏ (X s - h)` (over a domain).
-/
import RamanujanTau.LubinQuotient.Eval

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Lubin
open MvPowerSeries MvPowerSeries.WithPiTopology

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [IsTopologicalRing O]
  [IsLinearTopology O O] [CompleteSpace O] [T2Space O]

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- `f` with `X s ↦ h`. -/
noncomputable def ev (s : σ) (h : O) (f : MvPowerSeries σ O) : MvPowerSeries σ O :=
  E (Function.update X s (C h)) f

/-- `f` does not involve `X s`. -/
def Free (s : σ) (f : MvPowerSeries σ O) : Prop := ∀ e : σ →₀ ℕ, e s ≠ 0 → coeff e f = 0

/-- `(f - f|_{X s = 0}) / X s`. -/
noncomputable def shift (s : σ) (f : MvPowerSeries σ O) : MvPowerSeries σ O := fun e => coeff (e + Finsupp.single s 1) f

lemma coeff_shift (s : σ) (f : MvPowerSeries σ O) (e : σ →₀ ℕ) :
    coeff e (shift s f) = coeff (e + Finsupp.single s 1) f := rfl

lemma coeff_shift_iter (s : σ) (k : ℕ) (f : MvPowerSeries σ O) (e : σ →₀ ℕ) :
    coeff e ((shift s)^[k] f) = coeff (e + Finsupp.single s k) f := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, coeff_shift, add_assoc, ← Finsupp.single_add]

lemma adm_update (s : σ) {x : MvPowerSeries σ O} (hx : IsTopologicallyNilpotent (constantCoeff x)) :
    Adm (Function.update (X : σ → MvPowerSeries σ O) s x) := by
  intro t; by_cases hts : t = s
  · subst hts; simpa using hx
  · rw [Function.update_of_ne hts]; simpa using IsTopologicallyNilpotent.zero

lemma adm_ev (s : σ) {h : O} (hh : IsTopologicallyNilpotent h) :
    Adm (Function.update (X : σ → MvPowerSeries σ O) s (C h)) :=
  adm_update s (by simpa using hh)

lemma tn0 : IsTopologicallyNilpotent (0 : O) := IsTopologicallyNilpotent.zero

lemma coeff_ev_zero (s : σ) (f : MvPowerSeries σ O) (e : σ →₀ ℕ) :
    coeff e (ev s 0 f) = if e s = 0 then coeff e f else 0 := by
  split_ifs with he
  · have H := hasSum_coeff_E_update s tn0 f e he
    have H' : HasSum (fun n : ℕ => coeff (e + Finsupp.single s n) f * (0 : O) ^ n) (coeff e f) := by
      have := hasSum_ite_eq (0 : ℕ) (coeff e f)
      convert this using 1
      funext n; rcases n with _ | n <;> simp
    exact H.unique H'
  · exact coeff_E_update_of_ne s tn0 f e he

lemma free_ev (s : σ) {h : O} (hh : IsTopologicallyNilpotent h) (f : MvPowerSeries σ O) :
    Free s (ev s h f) := fun e he => coeff_E_update_of_ne s hh f e he

lemma free_iff (s : σ) (f : MvPowerSeries σ O) : Free s f ↔ ev s 0 f = f := by
  constructor
  · intro hf; ext e; rw [coeff_ev_zero]; split_ifs with he
    · rfl
    · exact (hf e he).symm
  · intro hf e he; rw [← hf]; exact free_ev s tn0 f e he

lemma coeff_X_mul' (s : σ) (g : MvPowerSeries σ O) (e : σ →₀ ℕ) :
    coeff e (X s * g) = if Finsupp.single s 1 ≤ e then coeff (e - Finsupp.single s 1) g else 0 := by
  rw [X, coeff_monomial_mul, one_mul]

/-- **decomposition** `f = f|_{X s = 0} + X s · shift f`. -/
lemma decomp (s : σ) (f : MvPowerSeries σ O) : f = ev s 0 f + X s * shift s f := by
  ext e
  rw [map_add, coeff_ev_zero, coeff_X_mul']
  by_cases he : e s = 0
  · rw [if_pos he, if_neg, add_zero]
    intro hle; have := hle s; simp [he] at this
  · rw [if_neg he, if_pos, zero_add, coeff_shift, tsub_add_cancel_of_le]
    · intro t; by_cases hts : t = s
      · subst hts; simp; omega
      · simp [Finsupp.single_eq_of_ne hts]
    · intro t; by_cases hts : t = s
      · subst hts; simp; omega
      · simp [Finsupp.single_eq_of_ne hts]

/-- evaluation fixing all variables but `s` leaves `s`-free series unchanged. -/
lemma E_free (s : σ) {b : σ → MvPowerSeries σ O} (hb : Adm b) (hbt : ∀ t, t ≠ s → b t = X t)
    {f : MvPowerSeries σ O} (hf : Free s f) : E b f = f := by
  rw [free_iff] at hf
  rw [← hf, ev, E_E (adm_ev s tn0) hb]
  congr 1; funext t
  by_cases hts : t = s
  · subst hts; rw [Function.update_self, E_C]
  · rw [Function.update_of_ne hts, E_X, hbt t hts]

lemma ev_free (s : σ) {h : O} (hh : IsTopologicallyNilpotent h) {f : MvPowerSeries σ O} (hf : Free s f) :
    ev s h f = f :=
  E_free s (adm_ev s hh) (fun _ ht => Function.update_of_ne ht _ _) hf

lemma ev_X_self (s : σ) (h : O) : ev s h (X s : MvPowerSeries σ O) = C h := by
  rw [ev, E_X, Function.update_self]

lemma ev_X_ne (s t : σ) (h : O) (hts : t ≠ s) : ev s h (X t : MvPowerSeries σ O) = X t := by
  rw [ev, E_X, Function.update_of_ne hts]

/-- **factor theorem**: `f - f|_{X s = h} = (X s - h) · q`. -/
theorem factor (s : σ) {h : O} (hh : IsTopologicallyNilpotent h) (f : MvPowerSeries σ O) :
    ∃ q, f - ev s h f = (X s - C h) * q := by
  have ha := adm_ev s hh
  set r : ℕ → MvPowerSeries σ O := fun k => ev s h ((shift s)^[k] f) with hr
  -- the recursion `r k = (shift^k f)|₀ + h · r (k+1)`
  have hrec : ∀ k, r k = ev s 0 ((shift s)^[k] f) + C h * r (k + 1) := by
    intro k
    simp only [hr]
    conv_lhs => rw [decomp s ((shift s)^[k] f)]
    rw [ev, E_add ha, E_mul ha, E_X, Function.update_self, ← ev, ← ev,
      ev_free s hh (free_ev s tn0 _), Function.iterate_succ_apply']
  refine ⟨fun e => coeff (e.erase s) (r (e s + 1)), ?_⟩
  ext e
  have hq : ∀ e' : σ →₀ ℕ, coeff e' (fun e => coeff (e.erase s) (r (e s + 1)) : MvPowerSeries σ O) =
      coeff (e'.erase s) (r (e' s + 1)) := fun _ => rfl
  rw [sub_mul, map_sub, map_sub, coeff_X_mul', coeff_C_mul, hq, hq]
  have key : ∀ k, coeff (e.erase s) (r k) = coeff (e.erase s + Finsupp.single s k) f +
      h * coeff (e.erase s) (r (k + 1)) := by
    intro k
    rw [hrec k, map_add, coeff_C_mul, coeff_ev_zero, if_pos (by simp), coeff_shift_iter]
  by_cases he : e s = 0
  · have hee : e.erase s = e := by
      ext t; by_cases hts : t = s
      · subst hts; simp [he]
      · simp [Finsupp.erase_ne hts]
    rw [if_neg, he]
    · have k0 := key 0
      rw [hee, Finsupp.single_zero, add_zero] at k0
      have : r 0 = ev s h f := rfl
      rw [← this, k0, hee]; ring
    · intro hle; have := hle s; simp [he] at this
  · rw [if_pos, show coeff e (ev s h f) = 0 from coeff_E_update_of_ne s hh f e he, sub_zero]
    · have h1 : (e - Finsupp.single s 1).erase s = e.erase s := by
        ext t; by_cases hts : t = s
        · subst hts; simp
        · simp [Finsupp.erase_ne hts, Finsupp.single_eq_of_ne hts]
      have h2 : (e - Finsupp.single s 1 : σ →₀ ℕ) s + 1 = e s := by simp; omega
      have h3 : e.erase s + Finsupp.single s (e s) = e := Finsupp.erase_add_single s e
      rw [h1, h2, key (e s), h3]; ring
    · intro t; by_cases hts : t = s
      · subst hts; simp; omega
      · simp [Finsupp.single_eq_of_ne hts]

/-- a series vanishing at finitely many distinct points is divisible by `∏ (X s - h)`. -/
theorem dvd_of_vanish [IsDomain O] (s : σ) (S : Finset O) (hS : ∀ h ∈ S, IsTopologicallyNilpotent h)
    (g : MvPowerSeries σ O) (hg : ∀ h ∈ S, ev s h g = 0) :
    ∃ q, g = (∏ h ∈ S, (X s - C h)) * q := by
  classical
  induction S using Finset.induction_on generalizing g with
  | empty => exact ⟨g, by simp⟩
  | insert a S haS ih =>
    obtain ⟨q1, hq1⟩ := factor s (hS a (Finset.mem_insert_self a S)) g
    rw [hg a (Finset.mem_insert_self a S), sub_zero] at hq1
    have hq1v : ∀ h ∈ S, ev s h q1 = 0 := by
      intro h hh
      have hht := hS h (Finset.mem_insert_of_mem hh)
      have := hg h (Finset.mem_insert_of_mem hh)
      rw [hq1, ev, E_mul (adm_ev s hht), E_sub (adm_ev s hht), E_X, Function.update_self, E_C,
        ← ev] at this
      rcases mul_eq_zero.mp this with h0 | h0
      · exfalso; rw [sub_eq_zero] at h0
        exact haS (C_injective (σ := σ) (R := O) h0 ▸ hh)
      · exact h0
    obtain ⟨q, hq⟩ := ih (fun h hh => hS h (Finset.mem_insert_of_mem hh)) q1 hq1v
    exact ⟨q, by rw [hq1, hq, Finset.prod_insert haS, mul_assoc]⟩

end Lubin
