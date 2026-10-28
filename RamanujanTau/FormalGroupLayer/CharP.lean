/-
# `[p]` in characteristic `p`, and its lift

* If `(p : R) = 0` then `[p]'(T) = 0`, so the coefficient of `T^k` in `[p](T)` vanishes for `p ∤ k`.
* Over any `R`, reducing mod `p`: the coefficient of `T^k` in `[p](T)` is divisible by `p` whenever
  `p ∤ k`. This is the shape `[p](T) = pT + ⋯ + aT^p + ⋯` used in Katz 3.10.7.
-/
import RamanujanTau.FormalGroupLayer.Invariant

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace FGL
open MvPowerSeries

variable {R : Type*} [CommRing R] (F : FormalGroup R)

local notation "Fs" => (F.toPowerSeries : MvPowerSeries (Fin 2) R)

lemma isUnit_Ψ_T : IsUnit (Ψ F (T : MvPowerSeries Unit R)) := by
  rw [isUnit_iff_constantCoeff, Ψ, cc_subst _ (cc_vec2 cc_T (by simp)), ← coeff_zero_eq_constantCoeff_apply,
    coeff_pd, zero_add]
  simp [F.lin_coeff_Y]

/-- **characteristic `p`**: `[p]'(T) = 0`. -/
theorem pd_nmul_eq_zero [F.IsComm] (p : ℕ) (hp : (p : R) = 0) : pd () (nmul F p) = 0 := by
  have h := nmul_invariant F p
  rw [show ((p : MvPowerSeries Unit R)) = C (p : R) by simp, hp, map_zero, zero_mul] at h
  exact (isUnit_Ψ_T F).mul_right_eq_zero.mp h

/-- in characteristic `p`, `[p](T)` has no monomial `T^k` with `p ∤ k`. -/
theorem coeff_nmul_eq_zero [F.IsComm] (p : ℕ) [hp : Fact p.Prime] (hpR : (p : R) = 0) (k : ℕ)
    (hk : ¬ p ∣ k) : coeff (Finsupp.single () k) (nmul F p) = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simpa using cc_nmul F p
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h : coeff (Finsupp.single () (j + 1)) (nmul F p) * ((j : R) + 1) = 0 := by
    have := congrArg (coeff (Finsupp.single () j)) (pd_nmul_eq_zero F p hpR)
    rw [coeff_pd, ← Finsupp.single_add, Finsupp.single_eq_same] at this
    simpa using this
  -- `j + 1` is a unit in `R`
  have hcop : Nat.Coprime (j + 1) p :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hk))
  obtain ⟨a, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.out.one_lt
  have hunit : ((j + 1 : ℕ) : R) * (a : R) = 1 := by
    have := Nat.div_add_mod ((j + 1) * a) p
    rw [ha.2] at this
    have h' : (((j + 1) * a : ℕ) : R) = 1 := by
      rw [← this]; push_cast; rw [hpR]; ring
    exact_mod_cast h'
  have : coeff (Finsupp.single () (j + 1)) (nmul F p) * (((j + 1 : ℕ) : R) * a) = 0 := by
    rw [← mul_assoc]; push_cast; rw [h, zero_mul]
  rwa [hunit, mul_one] at this

/-- `[n]` commutes with change of coefficients. -/
lemma nmul_map {S : Type*} [CommRing S] (f : R →+* S) (n : ℕ) :
    nmul (F.map f) n = MvPowerSeries.map f (nmul F n) := by
  induction n with
  | zero => simp [nmul]
  | succ n ih =>
    show ev (F.map f) T (nmul (F.map f) n) = MvPowerSeries.map f (ev F T (nmul F n))
    rw [ev, ev, map_subst (hs (cc_vec2 cc_T (cc_nmul F n))), ih]
    congr 1
    · funext s; fin_cases s <;> simp [T]

/-- **mixed characteristic**: the coefficient of `T^k` in `[p](T)` is divisible by `p` when `p ∤ k`. -/
theorem p_dvd_coeff_nmul [F.IsComm] (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : ¬ p ∣ k) :
    (p : R) ∣ coeff (Finsupp.single () k) (nmul F p) := by
  set I := Ideal.span {(p : R)}
  set π := Ideal.Quotient.mk I
  have hpS : ((p : R ⧸ I)) = 0 := by
    rw [← map_natCast π, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
  haveI : (F.map π).IsComm := ⟨by
    have := congrArg (MvPowerSeries.map π) (FormalGroup.IsComm.comm (F := F))
    rw [map_subst (hs (cc_vec2 (by simp) (by simp)))] at this
    simp only [FormalGroup.map_toPowerSeries]
    convert this using 2
    funext s; fin_cases s <;> simp⟩
  have h := coeff_nmul_eq_zero (F.map π) p hpS k hk
  rw [nmul_map, coeff_map, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
  exact h

end FGL
