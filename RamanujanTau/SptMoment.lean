/-
# Andrews' spt moment identity: `2·spt(n) = M₂(n) − N₂(n)`

`M₂(n) = Σ_{λ⊢n} crank(λ)²`, `N₂(n) = Σ_{λ⊢n} rank(λ)²`. The spt-crank identity
`R(z) − C(z) = (1−z)(1−z⁻¹)·S(z)` holds coefficientwise as an identity of integer Laurent polynomials (equal at every
unit `z`), and the second-moment functional `Σ c_k z^k ↦ Σ k²c_k` sends `(2 − z − z⁻¹)·L` to `−2·L(1)`, while
`S(1)` is the spt generating function.
-/
import RamanujanTau.SptFinal

set_option autoImplicit false

namespace CrankProof
open PowerSeries Finset LaurentPolynomial

/-- a Laurent polynomial vanishing at every unit of `ℂ` is zero. -/
lemma laurent_eq_zero_of_evU {R : LaurentPolynomial ℤ} (h : ∀ u : ℂˣ, evU u R = 0) : R = 0 := by
  obtain ⟨n, f, hf⟩ := exists_T_pow R
  have hf0 : f.map (Int.castRingHom ℂ) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := {x : ℂ | x ≠ 0}) (fun x hx => ?_) ?_
    · have := congrArg (evU (Units.mk0 x hx)) hf
      rw [map_mul, h, zero_mul, evU, eval₂_toLaurent] at this
      show Polynomial.IsRoot _ x
      rw [Polynomial.IsRoot, Polynomial.eval_map, ← this]
      rfl
    · exact (Set.finite_singleton (0 : ℂ)).infinite_compl
  have : f = 0 := Polynomial.map_injective _ (Int.cast_injective) (by rw [hf0, Polynomial.map_zero])
  rw [this, map_zero] at hf
  have hT : IsUnit (T n : LaurentPolynomial ℤ) := isUnit_T n
  exact (hT.mul_left_eq_zero).mp hf.symm

/-- the second moment `Σ c_k z^k ↦ Σ k² c_k`. -/
noncomputable def mom2 : LaurentPolynomial ℤ →+ ℤ := Finsupp.liftAddHom fun k => AddMonoidHom.mulLeft (k ^ 2)

/-- the value at `z = 1`, `Σ c_k z^k ↦ Σ c_k`. -/
noncomputable def ev1 : LaurentPolynomial ℤ →+ ℤ := Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ

lemma mom2_CT (a k : ℤ) : mom2 (LaurentPolynomial.C a * T k) = k ^ 2 * a := by
  rw [← single_eq_C_mul_T]; exact Finsupp.liftAddHom_apply_single _ _ _

lemma ev1_CT (a k : ℤ) : ev1 (LaurentPolynomial.C a * T k) = a := by
  rw [← single_eq_C_mul_T]; exact Finsupp.liftAddHom_apply_single _ _ _

lemma mom2_T (k : ℤ) : mom2 (T k) = k ^ 2 := by
  simpa using mom2_CT 1 k

lemma mom2_kernel (L : LaurentPolynomial ℤ) : mom2 (((2 : LaurentPolynomial ℤ) - T 1 - T (-1)) * L) = -2 * ev1 L := by
  induction L using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => rw [mul_add, map_add, hP, hQ, map_add]; ring
  | C_mul_T n a =>
    have e : ((2 : LaurentPolynomial ℤ) - T 1 - T (-1)) * (LaurentPolynomial.C a * T n : LaurentPolynomial ℤ)
        = LaurentPolynomial.C (2 * a) * T n - LaurentPolynomial.C a * T (n + 1) - LaurentPolynomial.C a * T (n - 1) := by
      rw [map_mul, show (C 2 : LaurentPolynomial ℤ) = 2 by simp, sub_eq_add_neg n 1, T_add, T_add]
      ring
    rw [e, map_sub, map_sub, mom2_CT, mom2_CT, mom2_CT, ev1_CT]
    ring

lemma evU_one_ev1 (L : LaurentPolynomial ℤ) : evU 1 L = (ev1 L : ℂ) := by
  induction L using LaurentPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, hP, hQ, map_add]; push_cast; ring
  | C_mul_T n a => rw [map_mul, evU_C, evU_T, ev1_CT]; simp

/-- `Σ_λ z^{rank λ}` as a Laurent polynomial. -/
noncomputable def rankL (m : ℕ) : LaurentPolynomial ℤ := ∑ l : m.Partition, T (rank l)

/-- `Σ_λ z^{crank λ}` as a Laurent polynomial. -/
noncomputable def crankL (m : ℕ) : LaurentPolynomial ℤ := ∑ l : m.Partition, T (crank l)

lemma evU_rankL (u : ℂˣ) (m : ℕ) : evU u (rankL m) = ∑ l : m.Partition, (u : ℂ) ^ rank l := by
  rw [rankL, map_sum]; simp_rw [evU_T]

lemma evU_crankL (u : ℂˣ) (m : ℕ) : evU u (crankL m) = ∑ l : m.Partition, (u : ℂ) ^ crank l := by
  rw [crankL, map_sum]; simp_rw [evU_T]

/-- the spt-crank identity, coefficientwise in `ℤ[z,z⁻¹]`. -/
theorem rankL_sub_crankL {m : ℕ} (hm : 2 ≤ m) :
    rankL m - crankL m = ((2 : LaurentPolynomial ℤ) - T 1 - T (-1)) * coeff m (CgfL * UL) := by
  rw [← sub_eq_zero]
  apply laurent_eq_zero_of_evU
  intro u
  have hu : (u : ℂ) ≠ 0 := u.ne_zero
  have h := congrArg (coeff m) (RankProof.rank_sub_crank hu)
  have hC : ∑ l : m.Partition, (u : ℂ) ^ crank l = coeff m (RankProof.Cgf u) := crank_generating_function hu hm
  rw [map_sub, coeff_C_mul, ← rank_durfee hu, ← hC] at h
  rw [map_sub, map_sub, map_mul, evU_rankL, evU_crankL, evU_coeff_S, map_sub, map_sub, evU_T1, evU_Tm1, h]
  simp only [map_ofNat]
  field_simp
  ring

/-- **Andrews' spt identity (moment form)**: `M₂(n) − N₂(n) = 2·spt(n)` for `n ≥ 2`. -/
theorem crank_moment_sub_rank_moment {m : ℕ} (hm : 2 ≤ m) :
    (∑ l : m.Partition, crank l ^ 2) - (∑ l : m.Partition, rank l ^ 2) = 2 * (spt m : ℤ) := by
  have h := congrArg mom2 (rankL_sub_crankL hm)
  rw [map_sub, mom2_kernel, rankL, crankL, map_sum, map_sum] at h
  simp_rw [mom2_T] at h
  have hs : (ev1 (coeff m (CgfL * UL)) : ℂ) = spt m := by
    rw [← evU_one_ev1, evU_coeff_S, show ((1 : ℂˣ) : ℂ) = 1 from rfl, spt_gf]
  have hs' : ev1 (coeff m (CgfL * UL)) = spt m := by exact_mod_cast hs
  rw [hs'] at h
  linarith

end CrankProof
