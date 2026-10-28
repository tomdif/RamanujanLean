import RamanujanTau.ModP.Formal
import RamanujanTau.TateCurve.Hasse

/-!
# Level-one modular forms are isobaric polynomials in `E₄, E₆` (q-expansion form)

* `exists_poly_qExpansion` — for every weight `k : ℤ` and every `f : ModularForm 𝒮ℒ k` there is an isobaric
  `P ∈ ℂ[X₀,X₁]` of weight `k.toNat` with `qExpansion 1 f = P(E₄, E₆)`. Proved by induction on the weight
  using Mathlib's `discriminantEquiv` (cusp forms of weight `k` = `Δ ·` forms of weight `k − 12`).
* `exists_poly_Eis` — for even `k ≥ 4` the formal Eisenstein series `TateCurve.Eis k ∈ ℚ⟦q⟧` equals
  `P(E₄, E₆)` for an isobaric `P ∈ ℚ[X₀,X₁]` of weight `k` (descent `ℂ → ℚ` via `ModP.descend`).
-/

set_option autoImplicit false

namespace ModP
open MvPolynomial ModularForm EisensteinSeries ModularFormClass UpperHalfPlane
open scoped MatrixGroups ArithmeticFunction.sigma
open RamanujanTau.DiscriminantBridge (Δmod)

lemma qExpansion_E4 : qExpansion 1 E₄ = E4 ℂ := RamanujanTau.Mod691.qExpansion_E4_eq
lemma qExpansion_E6 : qExpansion 1 E₆ = E6 ℂ := RamanujanTau.Mod691.qExpansion_E6_eq

lemma qExpansion_mcast {a b : ℤ} (h : a = b) (f : ModularForm 𝒮ℒ a) :
    qExpansion 1 (mcast h f) = qExpansion 1 f := rfl

lemma analytic (k : ℤ) (f : ModularForm 𝒮ℒ k) : AnalyticAt ℂ (cuspFunction 1 (f : ℍ → ℂ)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL

/-- Realization of monomials `E₄^a E₆^b` as modular forms. -/
lemma exists_mono_form (a b : ℕ) :
    ∃ F : ModularForm 𝒮ℒ ((4 * a + 6 * b : ℕ) : ℤ), qExpansion 1 F = E4 ℂ ^ a * E6 ℂ ^ b := by
  induction b with
  | zero =>
    induction a with
    | zero =>
      refine ⟨mcast (by simp) (1 : ModularForm 𝒮ℒ 0), ?_⟩
      rw [qExpansion_mcast, ModularForm.qExpansion_one]; simp
    | succ a ih =>
      obtain ⟨F, hF⟩ := ih
      refine ⟨mcast (by push_cast; ring) (F.mul E₄), ?_⟩
      rw [qExpansion_mcast, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL, hF,
        qExpansion_E4]
      ring
  | succ b ih =>
    obtain ⟨F, hF⟩ := ih
    refine ⟨mcast (by push_cast; ring) (F.mul E₆), ?_⟩
    rw [qExpansion_mcast, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL, hF,
      qExpansion_E6]
    ring

lemma ev_C {R : Type*} [CommRing R] (c : R) : ev R (C c) = PowerSeries.C c := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]; rfl

lemma ev_C_mul (c : ℂ) (P : MvPolynomial (Fin 2) ℂ) : ev ℂ (C c * P) = c • ev ℂ P := by
  rw [map_mul, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← Algebra.smul_def]

/-- **Structure theorem (q-expansion form).** -/
theorem exists_poly_qExpansion :
    ∀ (N : ℕ) (k : ℤ), k < 12 * N → ∀ f : ModularForm 𝒮ℒ k,
      ∃ P : MvPolynomial (Fin 2) ℂ, Iso P k.toNat ∧ ev ℂ P = qExpansion 1 f := by
  intro N
  induction N with
  | zero =>
    intro k hk f
    have hf : (f : ℍ → ℂ) = 0 := levelOne_neg_weight_eq_zero (by omega) f
    exact ⟨0, isWeightedHomogeneous_zero ℂ wt _, by rw [hf, qExpansion_zero, map_zero]⟩
  | succ N ih =>
    intro k hk f
    have zero_case : (f : ℍ → ℂ) = 0 →
        ∃ P : MvPolynomial (Fin 2) ℂ, Iso P k.toNat ∧ ev ℂ P = qExpansion 1 f := fun hf =>
      ⟨0, isWeightedHomogeneous_zero ℂ wt _, by rw [hf, qExpansion_zero, map_zero]⟩
    rcases lt_or_ge k 0 with hneg | hnn
    · exact zero_case (levelOne_neg_weight_eq_zero hneg f)
    rcases Int.even_or_odd k with hev | hodd
    swap
    · exact zero_case (by rw [levelOne_odd_weight_eq_zero hodd f, ModularForm.coe_zero])
    by_cases h2 : k = 2
    · subst h2
      have := levelOne_weight_two_rank_zero
      rw [rank_zero_iff_forall_zero] at this
      exact zero_case (by rw [this f, ModularForm.coe_zero])
    -- the generic case: `k = 4a + 6b`
    set n := k.toNat with hn
    have hkn : k = (n : ℤ) := by omega
    have hn' : 4 * bexp0 n + 6 * bexp1 n = n := by
      obtain ⟨m, hm⟩ := hev
      unfold bexp0 bexp1; omega
    obtain ⟨F, hF⟩ := exists_mono_form (bexp0 n) (bexp1 n)
    set M : ModularForm 𝒮ℒ k := mcast (by rw [hn', hkn]) F with hM
    have hqM : qExpansion 1 M = ev ℂ (base n) := by
      rw [hM, qExpansion_mcast, hF, base]; simp
    set c := (qExpansion 1 f).coeff 0 with hc
    set g : ModularForm 𝒮ℒ k := f - c • M with hg
    have hqg : qExpansion 1 g = qExpansion 1 f - c • ev ℂ (base n) := by
      rw [hg, ModularForm.coe_sub, ModularFormClass.qExpansion_sub one_pos one_mem_strictPeriods_SL,
        show ((c • M : ModularForm 𝒮ℒ k) : ℍ → ℂ) = c • (M : ℍ → ℂ) from rfl,
        ModularFormClass.qExpansion_smul one_pos one_mem_strictPeriods_SL, hqM]
    have hg0 : (qExpansion 1 g).coeff 0 = 0 := by
      rw [hqg, map_sub, PowerSeries.coeff_smul, PowerSeries.coeff_zero_eq_constantCoeff_apply
        (ev ℂ _), constantCoeff_ev, eval_base, ← hc]; simp
    set gc := ModularForm.toCuspForm g hg0 with hgc
    set h := CuspForm.divDiscriminant gc with hh
    have hfun : (g : ℍ → ℂ) = (Δmod : ℍ → ℂ) * (h : ℍ → ℂ) := by
      ext z
      have := congrArg (fun F : CuspForm 𝒮ℒ k => F z) (CuspForm.discriminantEquiv.left_inv gc)
      simp only at this
      change _ = Δmod z * h z
      rw [← ModularForm.toCuspForm_apply g hg0 z, ← hgc]
      exact this.symm
    have hqgh : qExpansion 1 g = Dq ℂ * qExpansion 1 h := by
      rw [hfun, UpperHalfPlane.qExpansion_mul (analytic _ Δmod) (analytic _ h),
        RamanujanTau.TauModular.qExpansion_discriminant_eq, Dq]
    have hfP : qExpansion 1 f = ev ℂ (C c * base n) + Dq ℂ * qExpansion 1 h := by
      rw [ev_C_mul, ← hqgh, hqg]; ring
    have hbase : Iso (base n : MvPolynomial (Fin 2) ℂ) n := iso_base hn'
    by_cases hk12 : k < 12
    · have hh0 : (h : ℍ → ℂ) = 0 := levelOne_neg_weight_eq_zero (by omega) h
      refine ⟨C c * base n, hbase.C_mul c, ?_⟩
      rw [hfP, hh0, qExpansion_zero, mul_zero, add_zero]
    · obtain ⟨Q, hQ, hQe⟩ := ih (k - 12) (by push_cast at hk; omega) h
      refine ⟨C c * base n + C (1728 : ℂ)⁻¹ * (X 0 ^ 3 - X 1 ^ 2) * Q, ?_, ?_⟩
      · have h12 : Iso (X 0 ^ 3 - X 1 ^ 2 : MvPolynomial (Fin 2) ℂ) 12 :=
          iso_sub (iso_of_eq (by simpa using iso_mono (R := ℂ) 3 0) (by norm_num))
            (iso_of_eq (by simpa using iso_mono (R := ℂ) 0 2) (by norm_num))
        refine (hbase.C_mul c).add ?_
        rw [mul_assoc]
        exact iso_of_eq ((h12.mul hQ).C_mul _) (by omega)
      · rw [hfP, map_add, map_mul, map_mul, map_mul, ev_disc, hQe, ev_C, ev_C]
        rw [show (1728 : PowerSeries ℂ) = PowerSeries.C (1728 : ℂ) from (map_ofNat _ _).symm]
        have : (PowerSeries.C (1728 : ℂ)⁻¹) * PowerSeries.C (1728 : ℂ) = 1 := by
          rw [← map_mul, inv_mul_cancel₀ (by norm_num), map_one]
        linear_combination (Dq ℂ * qExpansion 1 h) * this

/-- The q-expansion of Mathlib's normalized Eisenstein series is the image of `TateCurve.Eis k`. -/
lemma qExpansion_E_eq_Eis {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    qExpansion 1 (E hk) = PowerSeries.map (Rat.castHom ℂ) (TateCurve.Eis k) := by
  ext m
  rw [E_qExpansion_coeff hk hk2, PowerSeries.coeff_map, TateCurve.coeff_Eis, TateCurve.kappa]
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg hm, if_neg hm]; simp only [Rat.coe_castHom, zero_add]; push_cast; ring

/-- **`E_k` is an isobaric polynomial in `E₄, E₆` with rational coefficients.** -/
theorem exists_poly_Eis {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    ∃ P : MvPolynomial (Fin 2) ℚ, Iso P k ∧ ev ℚ P = TateCurve.Eis k := by
  obtain ⟨PC, hPC, hPCe⟩ := exists_poly_qExpansion (k + 1) (k : ℤ) (by push_cast; omega) (E hk)
  rw [Int.toNat_natCast] at hPC
  have hinj : Function.Injective (Rat.castHom ℂ) := (Rat.castHom ℂ).injective
  obtain ⟨P, hP, hPe⟩ := descend (Rat.castHom ℂ) hinj (isUnit_iff_ne_zero.mpr (by norm_num)) k PC hPC
    ⟨TateCurve.Eis k, by rw [hPCe, qExpansion_E_eq_Eis hk hk2]⟩
  refine ⟨P, hP, PowerSeries.map_injective _ hinj ?_⟩
  rw [map_ev, hPe, hPCe, qExpansion_E_eq_Eis hk hk2]

end ModP
