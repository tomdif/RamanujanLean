/-
# M3 step 3b: Abel summation for the base sum

`S₀(α) = Σ_n (λ(n)²/n) t^{iv} W̃(αn²)` (with `λ(n)² = bb n`) equals `−∫₁^∞ f'(t) A(t) dt`,
`A(t) = Σ_{n ≤ t} λ(n)²/n = AA ⌊t⌋` (`base_abel`).  Level 1.
-/
import RamanujanTau.SelbergKeyDiag2.Base1
import RamanujanTau.GoodSecondTerm.DiagD

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex MeasureTheory Set Filter Topology Finset RamanujanTau.HeckeAFE RamanujanTau.SelbergKey
  RamanujanTau.SelbergKey2
open RamanujanTau.GoodSecondTerm (AA bb c0 gammaD AA_asymp bb_nonneg)
open scoped Real

/-- `c_n = λ(n)²/n`. -/
noncomputable def cA (n : ℕ) : ℂ := ((bb n / n : ℝ) : ℂ)

lemma sum_cA (N : ℕ) : ∑ k ∈ Icc 0 N, cA k = (AA N : ℂ) := by
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_left (Nat.zero_le 1)) (fun k hk hk' => ?_)]
  · unfold AA cA; push_cast; rfl
  · have : k = 0 := by simp at hk hk'; omega
    subst this; simp [cA]

lemma AA_nonneg (N : ℕ) : 0 ≤ AA N :=
  Finset.sum_nonneg fun n _ => div_nonneg (bb_nonneg n) (Nat.cast_nonneg n)

lemma AA_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, AA N ≤ K * (1 + N) := by
  obtain ⟨C, hC0, hC⟩ := AA_asymp
  refine ⟨|c0| + |gammaD| + C, by positivity, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [AA]; positivity
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have h := hC N hN
  have hlog : Real.log N ≤ N := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hp : (N : ℝ) ^ (-(1 / 5 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have h1 := (abs_le.1 h).2
  have h2 : c0 * Real.log N ≤ |c0| * N :=
    (le_abs_self _).trans (by rw [abs_mul, abs_of_nonneg hlog0]; gcongr)
  nlinarith [le_abs_self gammaD, abs_nonneg c0, abs_nonneg gammaD]

lemma bb_div_le_AA (n : ℕ) : bb n / n ≤ AA n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [AA]
  exact Finset.single_le_sum (f := fun k : ℕ => bb k / k)
    (fun k _ => div_nonneg (bb_nonneg k) (Nat.cast_nonneg k)) (Finset.mem_Icc.2 ⟨hn, le_rfl⟩)

lemma inv_one_add_sq_le {x : ℝ} (hx : 0 < x) : (1 + x) ^ (-(2:ℝ)) ≤ x⁻¹ ^ 2 := by
  rw [Real.rpow_neg (by positivity), show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, inv_pow]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hx.le (by linarith) 2)

section
variable (u v : ℝ) {α : ℝ} (hα : 0 < α)
include hα

lemma ft_decay : ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t → ‖ft u v α t‖ ≤ K * t⁻¹ ^ 4 := by
  obtain ⟨C, hC0, hC⟩ := Wsh_bound (A := 2) (by norm_num)
  refine ⟨C * (TT u v / α) ^ 2, by have := TT_pos u v; positivity, fun t ht => ?_⟩
  rw [norm_ft_eq u v ht]
  have h := hC u (u + v) (α * t ^ 2) (by positivity)
  have hx : 0 < α * t ^ 2 / (Tq u * Tq (u + v)) := by have := TT_pos u v; unfold TT at this; positivity
  refine h.trans ((mul_le_mul_of_nonneg_left (inv_one_add_sq_le hx) hC0).trans (le_of_eq ?_))
  unfold TT
  have := Tq_pos u; have := Tq_pos (u + v)
  field_simp

lemma ft'_decay : ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t → ‖ft' u v α t‖ ≤ K * t⁻¹ ^ 5 := by
  obtain ⟨C, hC0, hC⟩ := Wsh_bound (A := 2) (by norm_num)
  obtain ⟨C', hC'0, hC'⟩ := norm_xi_Wd_decay (A := 2) (by norm_num)
  have hT := TT_pos u v
  refine ⟨(|v| * C + 2 * C') * (TT u v / α) ^ 2, by positivity, fun t ht => ?_⟩
  have hx : 0 < α * t ^ 2 / TT u v := by positivity
  have h1 := (hC u (u + v) (α * t ^ 2) (by positivity)).trans
    (mul_le_mul_of_nonneg_left (inv_one_add_sq_le hx) hC0)
  have h2 := (hC' u v (α * t ^ 2) (by positivity)).trans
    (mul_le_mul_of_nonneg_left (inv_one_add_sq_le hx) hC'0)
  unfold TT at h1
  refine (norm_ft'_le u v hα ht).trans ?_
  have e : (α * t ^ 2 / TT u v)⁻¹ ^ 2 = (TT u v / α) ^ 2 * t⁻¹ ^ 4 := by
    field_simp
  have e' : (α * t ^ 2 / (Tq u * Tq (u + v)))⁻¹ ^ 2 = (TT u v / α) ^ 2 * t⁻¹ ^ 4 := by
    rw [← e]; rfl
  rw [e'] at h1; rw [e] at h2
  have ht0 : 0 ≤ t⁻¹ := by positivity
  calc |v| * t⁻¹ * ‖Wsh u (u + v) (α * t ^ 2)‖ + 2 * t⁻¹ * ‖((α * t ^ 2 : ℝ) : ℂ) * Wd u v (α * t ^ 2)‖
      ≤ |v| * t⁻¹ * (C * ((TT u v / α) ^ 2 * t⁻¹ ^ 4)) +
          2 * t⁻¹ * (C' * ((TT u v / α) ^ 2 * t⁻¹ ^ 4)) := by gcongr
    _ = _ := by ring

/-- **Abel summation for the base sum.** -/
theorem base_abel :
    ∑' n : ℕ, cA n * ft u v α n =
      -∫ t in Ioi (1:ℝ), ft' u v α t * (AA ⌊t⌋₊ : ℂ) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := ft_decay u v hα
  obtain ⟨K₂, hK₂0, hK₂⟩ := ft'_decay u v hα
  obtain ⟨K₃, hK₃0, hK₃⟩ := AA_le
  have hderiv : ∀ t : ℝ, 0 < t → deriv (ft u v α) t = ft' u v α t :=
    fun t ht => (hasDerivAt_ft u v hα ht).deriv
  -- bound for `A(t)`
  have hA : ∀ t : ℝ, 0 ≤ t → ‖(AA ⌊t⌋₊ : ℂ)‖ ≤ K₃ * (1 + t) := by
    intro t ht
    rw [Complex.norm_real, Real.norm_of_nonneg (AA_nonneg _)]
    exact (hK₃ _).trans (by gcongr; exact Nat.floor_le ht)
  -- summability
  have hsum : Summable fun n : ℕ => cA n * ft u v α n := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => K₃ * K₁ * (2 * ((n : ℝ) ^ 2)⁻¹)) ?_ (fun n => ?_)
    · exact ((Real.summable_nat_pow_inv.2 (by norm_num)).mul_left 2).mul_left _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [cA]
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0:ℝ) < n := by linarith
    rw [norm_mul, cA, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (bb_nonneg n) (Nat.cast_nonneg n))]
    have h1 := (bb_div_le_AA n).trans (hK₃ n)
    have h2 := hK₁ n hn0
    have h3 : (1 + (n : ℝ)) * (n : ℝ)⁻¹ ^ 4 ≤ 2 * ((n : ℝ) ^ 2)⁻¹ := by
      rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      have : (2:ℝ) * ((n : ℝ) ^ 2)⁻¹ * (n : ℝ) ^ 4 = 2 * n ^ 2 := by field_simp
      rw [this]; nlinarith
    calc bb n / n * ‖ft u v α n‖ ≤ (K₃ * (1 + n)) * (K₁ * (n : ℝ)⁻¹ ^ 4) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = K₃ * K₁ * ((1 + (n : ℝ)) * (n : ℝ)⁻¹ ^ 4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hc0 : cA 0 = 0 := by simp [cA]
  -- the Abel summation limit
  have hlim := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (c := cA) (f := ft u v α) hc0
    (fun t ht => (hasDerivAt_ft u v hα (lt_of_lt_of_le one_pos ht)).differentiableAt)
    ?hint (l := 0) ?hl (g := fun t : ℝ => K₂ * K₃ * 2 * t ^ (-(2:ℝ))) ?hdom ?hgi
  case hint =>
    refine IntegrableOn.locallyIntegrableOn ?_
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-5:ℝ) < -1) one_pos).const_mul K₂)
      (measurable_deriv _).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0:ℝ) < t := lt_trans one_pos ht
    rw [hderiv t ht0]
    refine (hK₂ t ht0).trans (le_of_eq ?_)
    rw [Real.rpow_neg ht0.le, show (5:ℝ) = ((5:ℕ):ℝ) by norm_num, Real.rpow_natCast, inv_pow]
  case hl =>
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (2 * K₁ * K₃))
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0:ℝ) < n := by linarith
    rw [norm_mul, sum_cA]
    have h1 := hK₁ n hn0
    have h2 := hA n hn0.le
    rw [Nat.floor_natCast] at h2
    calc ‖ft u v α n‖ * ‖(AA n : ℂ)‖ ≤ (K₁ * (n : ℝ)⁻¹ ^ 4) * (K₃ * (1 + n)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ ≤ 2 * K₁ * K₃ / n := by
          rw [inv_pow, le_div_iff₀ hn0]
          have : K₁ * ((n : ℝ) ^ 4)⁻¹ * (K₃ * (1 + n)) * n = K₁ * K₃ * ((1 + n) * n / n ^ 4) := by ring
          rw [this]
          have h3 : (1 + (n : ℝ)) * n / n ^ 4 ≤ 2 := by
            rw [div_le_iff₀ (by positivity)]
            have h4 : (n:ℝ) ^ 2 ≤ n ^ 4 := pow_le_pow_right₀ hn1 (by norm_num)
            have h5 : (n:ℝ) ≤ n ^ 2 := by nlinarith
            nlinarith
          nlinarith [mul_nonneg hK₁0 hK₃0]
  case hdom =>
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    have ht0 : (0:ℝ) < t := by linarith
    rw [hderiv t ht0, sum_cA, norm_mul, one_mul, Real.norm_of_nonneg (by positivity)]
    have h1 := hK₂ t ht0
    have h2 := hA t ht0.le
    calc ‖ft' u v α t‖ * ‖(AA ⌊t⌋₊ : ℂ)‖ ≤ (K₂ * t⁻¹ ^ 5) * (K₃ * (1 + t)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ ≤ K₂ * K₃ * 2 * t ^ (-(2:ℝ)) := by
          rw [Real.rpow_neg ht0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
          have e : K₂ * t⁻¹ ^ 5 * (K₃ * (1 + t)) = K₂ * K₃ * ((1 + t) / t ^ 5) := by
            field_simp
          rw [e]
          have h3 : (1 + t) / t ^ 5 ≤ 2 * (t ^ 2)⁻¹ := by
            rw [div_le_iff₀ (by positivity)]
            have : 2 * (t ^ 2)⁻¹ * t ^ 5 = 2 * t ^ 3 := by field_simp
            rw [this]; nlinarith [pow_le_pow_left₀ zero_le_one ht 2, pow_le_pow_left₀ zero_le_one ht 3]
          calc K₂ * K₃ * ((1 + t) / t ^ 5) ≤ K₂ * K₃ * (2 * (t ^ 2)⁻¹) :=
                mul_le_mul_of_nonneg_left h3 (by positivity)
            _ = _ := by ring
  case hgi =>
    exact ⟨Ioi 1, Ioi_mem_atTop 1,
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) one_pos).const_mul _⟩
  have hlim2 : Tendsto (fun n : ℕ => ∑ k ∈ Icc 0 n, ft u v α k * cA k) atTop
      (𝓝 (∑' n : ℕ, cA n * ft u v α n)) := by
    have := hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun n => ?_
    simp only [Function.comp_def]
    rw [Nat.range_succ_eq_Icc_zero]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have huniq := tendsto_nhds_unique hlim2 hlim
  rw [huniq, zero_sub]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [hderiv t (lt_trans one_pos ht), sum_cA]

end

end RamanujanTau.SelbergKeyDiag2
