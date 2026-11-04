/-
# Ingredients for `XiKernelHyp`: the root `c`, the binomial expansion of `F(M+i)`, normalized moments

* `cRoot M` : a root `c ∈ [1, log(M+1)]` of `(πe^c − ¼)c = M` (`cRoot_spec`, for `M ≥ 9`, IVT);
  `cRoot → ∞`; for large `M` the `RootData` hypotheses of `XiMoments` hold (`rootData_ev`).
* `FXi_pos` : `F(M) > 0`.
* `FXi_add` : `F(M+i) = F(M) c^i Σ_{l≤L} C(i,l) μ_l`, `μ_l = ∫ u^M (u−c)^l t^{−3/4}θ₀ / (F(M) c^l)`.
* `abs_muX_le` : `|μ_l| ≤ (1 + 2B_l) ε^l`, `ε = λ₁^{−1/2}/c`.
* `SP_choose` : `j ↦ C(2j+a, l)·r` is a small-coefficient polynomial when `|r| ≤ R η^l`.
-/
import RamanujanTau.GORZXi.XiMoments

set_option autoImplicit false

namespace GORZXi

open Real Set MeasureTheory Filter Topology

/-! ## the root -/

open Classical in
/-- a root `c ∈ [1, log(M+1)]` of `(πe^c − ¼)c = M` (junk `1` if none). -/
noncomputable def cRoot (M : ℕ) : ℝ :=
  if h : ∃ c : ℝ, 1 ≤ c ∧ c ≤ Real.log ((M : ℝ) + 1) ∧ (π * rexp c - 1 / 4) * c = M then h.choose else 1

lemma cRoot_exists {M : ℕ} (hM : 9 ≤ M) :
    ∃ c : ℝ, 1 ≤ c ∧ c ≤ Real.log ((M : ℝ) + 1) ∧ (π * rexp c - 1 / 4) * c = M := by
  have hM' : (9 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog : 1 ≤ Real.log ((M : ℝ) + 1) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith [exp_one_lt_d9]
  have hcont : ContinuousOn (fun u : ℝ => (π * rexp u - 1 / 4) * u) (Icc 1 (Real.log ((M : ℝ) + 1))) := by
    fun_prop
  have h1 : (π * rexp 1 - 1 / 4) * 1 ≤ (M : ℝ) := by
    have := exp_one_lt_d9; have := pi_lt_d2
    have : π * rexp 1 ≤ 3.15 * 2.7182818286 := by
      apply mul_le_mul (by linarith) (by linarith) (exp_pos _).le (by norm_num)
    norm_num at this ⊢; linarith
  have h2 : (M : ℝ) ≤ (π * rexp (Real.log ((M : ℝ) + 1)) - 1 / 4) * Real.log ((M : ℝ) + 1) := by
    rw [Real.exp_log (by positivity)]
    have : (M : ℝ) ≤ π * ((M : ℝ) + 1) - 1 / 4 := by nlinarith [pi_gt_three]
    nlinarith
  obtain ⟨c, hc, hc'⟩ := intermediate_value_Icc hlog hcont ⟨h1, h2⟩
  exact ⟨c, hc.1, hc.2, hc'⟩

lemma cRoot_spec {M : ℕ} (hM : 9 ≤ M) :
    1 ≤ cRoot M ∧ cRoot M ≤ Real.log ((M : ℝ) + 1) ∧ (π * rexp (cRoot M) - 1 / 4) * cRoot M = M := by
  have h := cRoot_exists hM
  rw [cRoot, dif_pos h]
  exact h.choose_spec

lemma cRoot_tendsto : Tendsto cRoot atTop atTop := by
  rw [tendsto_atTop]
  intro K
  obtain ⟨N, hN⟩ := exists_nat_gt ((π * rexp K) * |K| + 9)
  filter_upwards [eventually_ge_atTop N] with M hM
  have hM' : (N : ℝ) ≤ M := by exact_mod_cast hM
  have h9 : 9 ≤ M := by
    have : (9 : ℝ) < M := by nlinarith [abs_nonneg K, exp_pos K, pi_pos, mul_nonneg (mul_nonneg pi_pos.le (exp_pos K).le) (abs_nonneg K)]
    exact_mod_cast this.le
  obtain ⟨h1, _, h3⟩ := cRoot_spec h9
  by_contra hlt
  push Not at hlt
  have : (M : ℝ) ≤ π * rexp K * |K| := by
    rw [← h3]
    have hK : 1 ≤ K := by linarith
    have : rexp (cRoot M) ≤ rexp K := exp_le_exp.mpr hlt.le
    rw [abs_of_nonneg (by linarith)]
    have a : π * rexp (cRoot M) * cRoot M ≤ π * rexp K * K :=
      mul_le_mul (mul_le_mul_of_nonneg_left this pi_pos.le) hlt.le (by linarith) (by positivity)
    have : (π * rexp (cRoot M) - 1 / 4) * cRoot M = π * rexp (cRoot M) * cRoot M - cRoot M / 4 := by ring
    linarith
  nlinarith [abs_nonneg K, exp_pos K, pi_pos]

lemma eventually_log4 : ∀ᶠ M : ℕ in atTop, Real.log ((M : ℝ) + 1) ^ 4 ≤ ((M : ℝ) + 1) / 4 := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 4)).bound (by norm_num : (0 : ℝ) < 1 / 4)
  have h' : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  filter_upwards [h'.eventually h, h'.eventually (eventually_ge_atTop 1)] with M hM hM1
  simp only [norm_pow, Real.norm_eq_abs, id] at hM
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (M : ℝ) + 1),
    abs_of_nonneg (Real.log_nonneg (by linarith))] at hM
  linarith

lemma rootData_ev : ∀ᶠ M : ℕ in atTop, RootData (M - 1) (cRoot M) ∧ cRoot M ^ 4 ≤ ((M : ℝ) + 1) / 4 := by
  filter_upwards [eventually_log4, eventually_ge_atTop 9] with M hM h9
  obtain ⟨h1, h2, h3⟩ := cRoot_spec h9
  have hcast : ((M - 1 : ℕ) : ℝ) + 1 = M := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hc4 : cRoot M ^ 4 ≤ ((M : ℝ) + 1) / 4 :=
    (pow_le_pow_left₀ (by linarith) h2 4).trans hM
  refine ⟨⟨h1, by rw [hcast]; exact h3, ?_⟩, hc4⟩
  rw [hcast]
  set c := cRoot M
  have hc0 : 0 < c := by linarith
  have hM9 : (9 : ℝ) ≤ M := by exact_mod_cast h9
  -- `πe^{c−1} ≤ πe^c = M/c + 1/4 ≤ M + 1/4 ≤ M²/c⁴`
  have e1 : π * rexp c = M / c + 1 / 4 := by
    have := h3; field_simp; linarith
  have hA : π * rexp (c - 1) ≤ (M : ℝ) + 1 / 4 := by
    have : rexp (c - 1) ≤ rexp c := exp_le_exp.mpr (by linarith)
    have : (M : ℝ) / c ≤ M := div_le_self (by positivity) h1
    nlinarith [pi_pos]
  have hB : (M : ℝ) + 1 / 4 ≤ ((M : ℝ) / c ^ 2) ^ 2 := by
    rw [div_pow, ← pow_mul, le_div_iff₀ (by positivity)]
    have hc4' : c ^ (2 * 2) ≤ ((M : ℝ) + 1) / 4 := by simpa using hc4
    have : ((M : ℝ) + 1 / 4) * c ^ (2 * 2) ≤ ((M : ℝ) + 1 / 4) * (((M : ℝ) + 1) / 4) :=
      mul_le_mul_of_nonneg_left hc4' (by positivity)
    nlinarith
  linarith

/-! ## positivity and the binomial expansion -/

lemma FXi_pos (M : ℕ) : 0 < FXi M := by
  rw [FXi_eq M 0]
  have hpos : ∀ t ∈ Ioi (1 : ℝ), 0 < rhoT M 0 0 t := by
    intro t ht
    have ht1 : 1 < t := ht
    unfold rhoT
    have := Real.log_pos ht1
    have := theta0_lower (by linarith : (0 : ℝ) < t)
    have := exp_pos (-π * t)
    have : 0 < t ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    simp only [pow_zero, mul_one]
    have : 0 < theta0 t := by linarith
    positivity
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (hpos t ht).le) (integrable_rhoT M 0 0)]
  have : Function.support (rhoT M 0 0) ∩ Ioi 1 = Ioi 1 := by
    ext t; simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
    exact ⟨fun h => h.2, fun h => ⟨(hpos t h).ne', h⟩⟩
  rw [this, Real.volume_Ioi]; simp

/-- the normalized moments `μ_l = ∫ u^M x^l t^{−3/4} θ₀ / (F(M) c^l)`. -/
noncomputable def muX (M : ℕ) (c : ℝ) (l : ℕ) : ℝ := (∫ t in Ioi 1, rhoT M c l t) / (FXi M * c ^ l)

lemma FXi_add_aux (M i : ℕ) (c : ℝ) :
    FXi (M + i) = ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * c ^ (i - l) * ∫ t in Ioi 1, rhoT M c l t := by
  rw [FXi_eq (M + i) c]
  have e : (fun t => rhoT (M + i) c 0 t) =
      fun t => ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * c ^ (i - l) * rhoT M c l t := by
    funext t
    have hb := add_pow (Real.log t - c) c i
    rw [sub_add_cancel] at hb
    simp only [rhoT, pow_add, hb, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => by ring
  rw [e, integral_finsetSum _ fun l _ => (integrable_rhoT M l c).const_mul _]
  exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _

lemma FXi_add (M : ℕ) {c : ℝ} (hc : c ≠ 0) {i L : ℕ} (hiL : i ≤ L) :
    FXi (M + i) = FXi M * c ^ i * ∑ l ∈ Finset.range (L + 1), (i.choose l : ℝ) * muX M c l := by
  have hF := (FXi_pos M).ne'
  rw [FXi_add_aux, Finset.mul_sum]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : i + 1 ≤ L + 1)) (fun l _ hl => by
    simp only [Finset.mem_range, not_lt] at hl
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hli : l ≤ i := by simp at hl; omega
  rw [muX, show c ^ i = c ^ (i - l) * c ^ l by rw [← pow_add]; congr 1; omega]
  field_simp

lemma abs_muX_le {m : ℕ} {c : ℝ} (hc : RootData m c) (l : ℕ) :
    |muX (m + 1) c l| ≤ (1 + 2 * Bcst l) * ((Real.sqrt (π * rexp (c - 1)))⁻¹ / c) ^ l := by
  have hc0 : 0 < c := by linarith [hc.one_le]
  have hF := FXi_pos (m + 1)
  rw [muX, abs_div, abs_of_pos (by positivity : 0 < FXi (m + 1) * c ^ l), div_le_iff₀ (by positivity),
    div_pow]
  calc _ ≤ _ := abs_rhoT_le hc l
    _ = _ := by field_simp

/-! ## binomials as small-coefficient polynomials -/

open Polynomial in
/-- the coefficient constant of `j ↦ C(2j+a, l)`. -/
noncomputable def Cpoly (l a : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (l + 1), |((descPochhammer ℝ l).comp (C 2 * X + C (a : ℝ))).coeff p| / (l.factorial : ℝ)

lemma Cpoly_nonneg (l a : ℕ) : 0 ≤ Cpoly l a := Finset.sum_nonneg fun _ _ => by positivity

open Polynomial in
lemma SP_choose (K a l : ℕ) {η R r : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hR : 0 ≤ R) (hr : |r| ≤ R * η ^ l) :
    SP K η (R * Cpoly l a) (l + 1) 0 (fun j => ((2 * j + a).choose l : ℝ) * r) := by
  set P : ℝ[X] := (descPochhammer ℝ l).comp (C 2 * X + C (a : ℝ)) with hP
  have hdeg : P.natDegree < l + 1 := by
    have h1 : (C 2 * X + C (a : ℝ) : ℝ[X]).natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans (by simp)) (by simp))
    have := (natDegree_comp_le (p := descPochhammer ℝ l) (q := C 2 * X + C (a : ℝ))).trans
      (Nat.mul_le_mul (descPochhammer_natDegree ℝ l).le h1)
    rw [hP]; omega
  have hf : (0 : ℝ) < l.factorial := by exact_mod_cast Nat.factorial_pos l
  refine ⟨Fin (l + 1), inferInstance, fun p => r * P.coeff p / l.factorial, fun p => (p : ℕ), by simp,
    fun _ => Nat.zero_le _, fun p => ?_, fun j _ => ?_⟩
  · have hp : (p : ℕ) ≤ l := Nat.lt_succ_iff.mp p.2
    have hterm : |P.coeff p| / l.factorial ≤ Cpoly l a :=
      Finset.single_le_sum (f := fun p => |P.coeff p| / (l.factorial : ℝ)) (fun _ _ => by positivity)
        (Finset.mem_range.mpr p.2)
    rw [abs_div, abs_mul, abs_of_pos hf]
    calc |r| * |P.coeff p| / l.factorial = |r| * (|P.coeff p| / l.factorial) := by ring
      _ ≤ (R * η ^ l) * Cpoly l a := mul_le_mul hr hterm (by positivity) (by positivity)
      _ ≤ (R * η ^ (p : ℕ)) * Cpoly l a :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hη0 hη1 hp) hR)
            (Cpoly_nonneg l a)
      _ = _ := by ring
  · have hc : ((2 * j + a).choose l : ℝ) = P.eval (j : ℝ) / l.factorial := by
      have e0 : eval (j : ℝ) (C 2 * X + C (a : ℝ)) = (((2 * j + a : ℕ)) : ℝ) := by
        simp only [eval_add, eval_mul, eval_C, eval_X]; push_cast; ring
      have e1 : P.eval (j : ℝ) = (((2 * j + a).descFactorial l : ℕ) : ℝ) := by
        rw [hP, eval_comp, e0, descPochhammer_eval_eq_descFactorial]
      rw [e1, Nat.descFactorial_eq_factorial_mul_choose]
      push_cast; field_simp
    dsimp only
    rw [hc, eval_eq_sum_range' hdeg,
      ← Fin.sum_univ_eq_sum_range (fun p => P.coeff p * (j : ℝ) ^ p), Finset.sum_div, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring

end GORZXi
