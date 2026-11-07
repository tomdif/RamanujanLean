/-
# `∃ L, HorocycleLimit L`, and the unconditional Rankin–Selberg asymptotic

Integrates the pointwise sandwich of `HoroMain.lean` over the horocycle, passes to the limit
with `tendsto_boxR`/`tendsto_horoR`, and concludes by a Cauchy argument.
-/
import RamanujanTau.EisensteinReal.HoroMain

set_option autoImplicit false

namespace RamanujanTau.EisensteinReal.Horo

open Finset Real Filter Topology MeasureTheory ModularGroup
open RamanujanTau.RankinSelberg
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal

/-- The horocycle mean `∫₀¹ G(x+iy) dx` (junk value `0` for `y ≤ 0`). -/
noncomputable def Aint (y : ℝ) : ℝ := if hy : 0 < y then ∫ x in (0 : ℝ)..1, G (hp hy x) else 0

lemma continuous_G_hp {y : ℝ} (hy : 0 < y) : Continuous fun x => G (hp hy x) :=
  continuous_G.comp (continuous_hp hy)

lemma Aint_nonneg (y : ℝ) : 0 ≤ Aint y := by
  unfold Aint
  split_ifs with hy
  · exact intervalIntegral.integral_nonneg zero_le_one fun x _ => (G_pos _).le
  · exact le_rfl

lemma ofReal_Aint {y : ℝ} (hy : 0 < y) :
    ENNReal.ofReal (Aint y) = ∫⁻ x in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (G (hp hy x)) := by
  unfold Aint
  rw [dif_pos hy, intervalIntegral.integral_of_le zero_le_one]
  exact ofReal_integral_eq_lintegral_ofReal
    ((continuous_G_hp hy).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
    (Filter.Eventually.of_forall fun x => (G_pos _).le)

lemma measurable_ofReal_G_hp {y : ℝ} (hy : 0 < y) :
    Measurable fun x => ENNReal.ofReal (G (hp hy x)) :=
  (ENNReal.continuous_ofReal.comp (continuous_G_hp hy)).measurable

/-- Box horocycle mean for the grid box `i`. -/
noncomputable def bxHoro (K : ℕ) (i : ℕ × ℕ) {y : ℝ} (hy : 0 < y) : ℝ≥0∞ :=
  boxHoro (xj K i.1) (xj K i.1 + 1 / K) (ajk K i.1 i.2) (ajk K i.1 i.2 + 1 / K) hy

noncomputable def bxR (K : ℕ) (i : ℕ × ℕ) (y : ℝ) : ℝ :=
  boxR (xj K i.1) (xj K i.1 + 1 / K) (ajk K i.1 i.2) (ajk K i.1 i.2 + 1 / K) y

/-- `∫₀¹ ∑_γ ∑_i cᵢ 1_{boxᵢ}(γ(x+iy)) dx = ∑_i cᵢ · boxHoroᵢ`. -/
lemma lintegral_combo (K L : ℕ) (c : ℕ × ℕ → ℝ) {y : ℝ} (hy : 0 < y) :
    ∫⁻ x in Set.Ioc (0 : ℝ) 1, ∑' γ : SL(2, ℤ),
        ∑ i ∈ Idx K L, ENNReal.ofReal (c i) * bxInd K i (γ • hp hy x) =
      ∑ i ∈ Idx K L, ENNReal.ofReal (c i) * bxHoro K i hy := by
  have hm : ∀ i, Measurable fun x : ℝ => ∑' γ : SL(2, ℤ), bxInd K i (γ • hp hy x) :=
    fun i => measurable_cnt_hp hy (measurable_boxInd _ _ _ _)
  have e : ∀ x : ℝ, ∑' γ : SL(2, ℤ), ∑ i ∈ Idx K L, ENNReal.ofReal (c i) * bxInd K i (γ • hp hy x)
      = ∑ i ∈ Idx K L, ENNReal.ofReal (c i) * ∑' γ : SL(2, ℤ), bxInd K i (γ • hp hy x) := by
    intro x
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    exact Finset.sum_congr rfl fun i _ => ENNReal.tsum_mul_left
  simp_rw [e]
  rw [lintegral_finsetSum _ (fun i _ => (hm i).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_const_mul _ (hm i)]
  rfl

section Sandwich
variable {K L : ℕ} {δ M : ℝ} (hK : 6 ≤ K) (hL : 1 ≤ L) (hδ : 0 < δ) (hM : ∀ z : ℍ, G z ≤ M)
  (huc : ∀ w w' : ℍ,
    w.re ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → w'.re ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) →
    w.im ∈ Set.Icc (1 / 4 : ℝ) (L + 2) → w'.im ∈ Set.Icc (1 / 4 : ℝ) (L + 2) →
    |w.re - w'.re| ≤ 1 / K → |w.im - w'.im| ≤ 1 / K → |G w - G w'| ≤ δ)

include hK hL hM huc in
lemma upper_lintegral {y : ℝ} (hy : 0 < y) :
    2 * ENNReal.ofReal (Aint y) ≤ ∑ i ∈ Idx K L, ENNReal.ofReal (cUp K δ i) * bxHoro K i hy +
      ENNReal.ofReal M * horo (-(1 / 2)) (1 / 2) L hy := by
  rw [ofReal_Aint hy, ← lintegral_const_mul _ (measurable_ofReal_G_hp hy)]
  have hpt : ∀ x : ℝ, 2 * ENNReal.ofReal (G (hp hy x)) ≤
      ∑' γ : SL(2, ℤ), up K L δ M (γ • hp hy x) := by
    intro x
    obtain ⟨γ₀, h₀⟩ := exists_smul_mem_U (hp hy x)
    calc 2 * ENNReal.ofReal (G (hp hy x)) = 2 * ENNReal.ofReal (G (γ₀ • hp hy x)) := by
          rw [G_smul]
      _ ≤ 2 * up K L δ M (γ₀ • hp hy x) := by gcongr; exact up_ge hK hL hM huc h₀
      _ ≤ _ := two_le_tsum _ _ γ₀
  refine (setLIntegral_mono' measurableSet_Ioc fun x _ => hpt x).trans (le_of_eq ?_)
  unfold up
  have hm1 : Measurable fun x : ℝ => ∑' γ : SL(2, ℤ),
      ∑ i ∈ Idx K L, ENNReal.ofReal (cUp K δ i) * bxInd K i (γ • hp hy x) :=
    measurable_cnt_hp hy (Finset.measurable_sum _ fun i _ =>
      (measurable_boxInd _ _ _ _).const_mul _)
  simp_rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
  rw [lintegral_add_left hm1, lintegral_combo, lintegral_const_mul]
  · rfl
  · exact measurable_cnt_hp hy (measurable_ind _ _ _)

include hK hL hM huc in
lemma lower_lintegral {y : ℝ} (hy : 0 < y) :
    ∑ i ∈ Idx K L, ENNReal.ofReal (cLo K δ i) * bxHoro K i hy ≤ 2 * ENNReal.ofReal (Aint y) := by
  rw [ofReal_Aint hy, ← lintegral_const_mul _ (measurable_ofReal_G_hp hy), ← lintegral_combo]
  refine setLIntegral_mono' measurableSet_Ioc fun x _ => ?_
  obtain ⟨h0, hle⟩ := lo_spec (δ := δ) hK hL hM huc
  exact tsum_le_two (lo K L δ) (fun w => ENNReal.ofReal (G w)) (fun γ w => by simp only [G_smul])
    h0 hle (hp hy x)

include hδ in
lemma cUp_nonneg (i : ℕ × ℕ) : 0 ≤ cUp K δ i := by
  unfold cUp Gc'; have := G_pos (gpt (xj K i.1) (ajk K i.1 i.2)); linarith

lemma cLo_nonneg (i : ℕ × ℕ) : 0 ≤ cLo K δ i := by
  unfold cLo; split_ifs <;> simp

include hK in
lemma bxHoro_ne_top {i : ℕ × ℕ} (hi : i ∈ Idx K L) {y : ℝ} (hy : 0 < y) (hy2 : y < 1 / 2) :
    bxHoro K i hy ≠ ⊤ := by
  have hjK := Finset.mem_range.1 (Finset.mem_product.1 hi).1
  have ha := ajk_ge hK hjK (k := i.2)
  have hK' := K_pos hK
  exact boxHoro_ne_top (by linarith [show (0 : ℝ) < 1 / K by positivity]) (by linarith)
    (by linarith [show (0 : ℝ) < 1 / K by positivity]) hy (by linarith)

include hK hL hδ hM huc in
/-- Real upper bound: `2 A(y) ≤ ∑ c⁺ boxR + M horoR` for `0 < y < 1/2`. -/
lemma upper_real {y : ℝ} (hy : 0 < y) (hy2 : y < 1 / 2) :
    2 * Aint y ≤ ∑ i ∈ Idx K L, cUp K δ i * bxR K i y + M * horoR (-(1 / 2)) (1 / 2) L y := by
  have hM0 : 0 ≤ M := (G_pos (gpt 0 0)).le.trans (hM _)
  have hLy : y < L := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hfin1 : ∀ i ∈ Idx K L, ENNReal.ofReal (cUp K δ i) * bxHoro K i hy ≠ ⊤ :=
    fun i hi => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (bxHoro_ne_top hK hi hy hy2)
  have hfin2 : ENNReal.ofReal M * horo (-(1 / 2)) (1 / 2) L hy ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (horo_ne_top (by norm_num) (by linarith) hy hLy)
  have hsum_ne : ∑ i ∈ Idx K L, ENNReal.ofReal (cUp K δ i) * bxHoro K i hy ≠ ⊤ :=
    (ENNReal.sum_lt_top.2 fun i hi => (hfin1 i hi).lt_top).ne
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hsum_ne, hfin2⟩)
    (upper_lintegral hK hL hM huc hy)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Aint_nonneg y), ENNReal.toReal_add hsum_ne hfin2,
    ENNReal.toReal_sum hfin1, ENNReal.toReal_mul, ENNReal.toReal_ofReal hM0] at h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (cUp_nonneg hδ _)] at h
  unfold bxR boxR horoR
  simp only [dif_pos hy]
  convert h using 2

include hK hL hM huc in
/-- Real lower bound: `∑ c⁻ boxR ≤ 2 A(y)` for `0 < y < 1/2`. -/
lemma lower_real {y : ℝ} (hy : 0 < y) (hy2 : y < 1 / 2) :
    ∑ i ∈ Idx K L, cLo K δ i * bxR K i y ≤ 2 * Aint y := by
  have hfin1 : ∀ i ∈ Idx K L, ENNReal.ofReal (cLo K δ i) * bxHoro K i hy ≠ ⊤ :=
    fun i hi => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (bxHoro_ne_top hK hi hy hy2)
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
    (lower_lintegral hK hL hM huc hy (δ := δ))
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Aint_nonneg y), ENNReal.toReal_sum hfin1] at h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (cLo_nonneg _)] at h
  unfold bxR boxR
  simp only [dif_pos hy]
  convert h using 2

end Sandwich

/-! ### Limits of the two sides, and the gap -/

/-- `μᵢ = (1/K)(1/a − 1/(a+1/K))`. -/
noncomputable def mu (K : ℕ) (i : ℕ × ℕ) : ℝ :=
  (xj K i.1 + 1 / K - xj K i.1) * (1 / ajk K i.1 i.2 - 1 / (ajk K i.1 i.2 + 1 / K))

lemma tendsto_bxR {K L : ℕ} (hK : 6 ≤ K) {i : ℕ × ℕ} (hi : i ∈ Idx K L) :
    Tendsto (bxR K i) (𝓝[>] 0) (𝓝 (K0 * mu K i)) := by
  have hjK := Finset.mem_range.1 (Finset.mem_product.1 hi).1
  have ha := ajk_ge hK hjK (k := i.2)
  have hK' := K_pos hK
  exact tendsto_boxR (by linarith [show (0 : ℝ) < 1 / K by positivity]) (by linarith)
    (by linarith [show (0 : ℝ) < 1 / K by positivity])

lemma mu_le {K L : ℕ} (hK : 6 ≤ K) {i : ℕ × ℕ} (hi : i ∈ Idx K L) :
    0 ≤ mu K i ∧ mu K i ≤ 4 / (K : ℝ) ^ 2 := by
  have hjK := Finset.mem_range.1 (Finset.mem_product.1 hi).1
  have ha := ajk_ge hK hjK (k := i.2)
  have hK' := K_pos hK
  unfold mu
  set a := ajk K i.1 i.2
  have e : (xj K i.1 + 1 / K - xj K i.1) * (1 / a - 1 / (a + 1 / K)) =
      1 / K * (1 / K / (a * (a + 1 / K))) := by
    field_simp; ring
  rw [e]
  constructor
  · positivity
  · have h1 : 1 / 4 ≤ a * (a + 1 / K) := by
      have : (0 : ℝ) < 1 / K := by positivity
      nlinarith
    have h2 : 1 / K / (a * (a + 1 / K)) ≤ 1 / K / (1 / 4) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) h1
    calc 1 / K * (1 / K / (a * (a + 1 / K))) ≤ 1 / K * (1 / K / (1 / 4)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 4 / (K : ℝ) ^ 2 := by field_simp

lemma cUp_sub_cLo_le {K : ℕ} {δ M : ℝ} (hδ : 0 < δ) (hM : ∀ z : ℍ, G z ≤ M) (i : ℕ × ℕ) :
    cUp K δ i - cLo K δ i ≤ (if i.2 < 4 then M + δ else 0) + 2 * δ := by
  have hG := G_pos (gpt (xj K i.1) (ajk K i.1 i.2))
  have hGM := hM (gpt (xj K i.1) (ajk K i.1 i.2))
  unfold cUp cLo Gc'
  split_ifs with h1 h2 h2
  · omega
  · have := le_max_left (G (gpt (xj K i.1) (ajk K i.1 i.2)) - δ) 0
    linarith
  · linarith
  · omega

lemma cUp_sub_cLo_nonneg {K : ℕ} {δ : ℝ} (hδ : 0 < δ) (i : ℕ × ℕ) :
    0 ≤ cUp K δ i - cLo K δ i := by
  have hG := G_pos (gpt (xj K i.1) (ajk K i.1 i.2))
  unfold cUp cLo Gc'
  split_ifs
  · rcases le_total (G (gpt (xj K i.1) (ajk K i.1 i.2)) - δ) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  · linarith

lemma card_filter_lt_four (K L : ℕ) :
    ((Idx K L).filter (fun i : ℕ × ℕ => i.2 < 4)).card ≤ 4 * K := by
  calc ((Idx K L).filter (fun i : ℕ × ℕ => i.2 < 4)).card ≤ (range K ×ˢ range 4).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Idx, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hi ⊢
        exact ⟨hi.1.1, hi.2⟩
    _ = 4 * K := by rw [Finset.card_product, Finset.card_range, Finset.card_range, mul_comm]

/-- **Gap bound:** `∑ (c⁺ − c⁻)μ ≤ 16(M+δ)/K + 8δL`. -/
lemma gap_le {K L : ℕ} (hK : 6 ≤ K) {δ M : ℝ} (hδ : 0 < δ) (hM : ∀ z : ℍ, G z ≤ M) :
    ∑ i ∈ Idx K L, (cUp K δ i - cLo K δ i) * mu K i ≤ 16 * (M + δ) / K + 8 * δ * L := by
  have hK' := K_pos hK
  have hM0 : 0 ≤ M := (G_pos (gpt 0 0)).le.trans (hM _)
  calc ∑ i ∈ Idx K L, (cUp K δ i - cLo K δ i) * mu K i
      ≤ ∑ i ∈ Idx K L, ((if i.2 < 4 then M + δ else 0) + 2 * δ) * (4 / (K : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun i hi => ?_
        obtain ⟨hμ0, hμ⟩ := mu_le (L := L) hK hi
        exact mul_le_mul (cUp_sub_cLo_le hδ hM i) hμ hμ0
          (by split_ifs <;> positivity)
    _ = 4 / (K : ℝ) ^ 2 * ((M + δ) * ((Idx K L).filter (fun i : ℕ × ℕ => i.2 < 4)).card +
          2 * δ * (Idx K L).card) := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
          add_zero, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
        ring
    _ ≤ 4 / (K : ℝ) ^ 2 * ((M + δ) * (4 * K) + 2 * δ * (K * (K * L))) := by
        gcongr
        · exact_mod_cast card_filter_lt_four K L
        · simp [Idx, Finset.card_product]
    _ = 16 * (M + δ) / K + 8 * δ * L := by field_simp; ring

/-! ### The Cauchy argument -/

lemma exists_lim_of_sandwich {A : ℝ → ℝ}
    (h : ∀ ε > 0, ∃ U V : ℝ, U - V ≤ ε ∧ (∀ᶠ y in 𝓝[>] 0, A y ≤ U + ε) ∧
      ∀ᶠ y in 𝓝[>] 0, V - ε ≤ A y) :
    ∃ Λ, Tendsto A (𝓝[>] 0) (𝓝 Λ) := by
  have hc : Cauchy (map A (𝓝[>] (0 : ℝ))) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨U, V, hUV, hU, hV⟩ := h (ε / 4) (by positivity)
    refine ⟨Set.Icc (V - ε / 4) (U + ε / 4), ?_, ?_⟩
    · rw [Filter.mem_map]
      exact (hU.and hV).mono fun y hy => ⟨hy.2, hy.1⟩
    · intro a ha b hb
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  exact cauchy_map_iff_exists_tendsto.1 hc

/-- **Main analytic theorem.** `∫₀¹ G(x+iy) dx` converges as `y → 0⁺`. -/
theorem exists_tendsto_Aint : ∃ Λ, Tendsto Aint (𝓝[>] 0) (𝓝 Λ) := by
  obtain ⟨M, hM0, hM⟩ := exists_G_le
  refine exists_lim_of_sandwich fun ε hε => ?_
  set Kc : ℝ := |K0| + 1 with hKc
  have hKc0 : 0 < Kc := by positivity
  -- height
  obtain ⟨L, hL⟩ := exists_nat_gt (3 * Kc * M / ε)
  have hL1 : 1 ≤ L := by
    have : (0 : ℝ) < L := lt_of_le_of_lt (by positivity) hL
    exact_mod_cast this
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  -- precision
  set δ : ℝ := min 1 (ε / (24 * Kc * L)) with hδdef
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ ε / (24 * Kc * L) := min_le_right _ _
  obtain ⟨η, hη, huc0⟩ := exists_uc ((L : ℝ) + 2) δ hδ
  -- grid size
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / η + 48 * Kc * (M + 1) / ε + 6)
  have hK6 : 6 ≤ K := by
    have : (6 : ℝ) < K := by
      have : 0 ≤ 1 / η + 48 * Kc * (M + 1) / ε := by positivity
      linarith
    exact_mod_cast this.le
  have hK' := K_pos hK6
  have hKη : 1 / (K : ℝ) ≤ η := by
    rw [div_le_iff₀ hK']
    have : 1 / η < K := by
      have : 0 ≤ 48 * Kc * (M + 1) / ε := by positivity
      linarith
    rw [div_lt_iff₀ hη] at this
    linarith
  have hKε : 48 * Kc * (M + 1) / ε < K := by
    have : 0 ≤ 1 / η := by positivity
    linarith
  have huc : ∀ w w' : ℍ,
      w.re ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → w'.re ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) →
      w.im ∈ Set.Icc (1 / 4 : ℝ) (L + 2) → w'.im ∈ Set.Icc (1 / 4 : ℝ) (L + 2) →
      |w.re - w'.re| ≤ 1 / K → |w.im - w'.im| ≤ 1 / K → |G w - G w'| ≤ δ :=
    fun w w' h1 h2 h3 h4 h5 h6 => huc0 w w' h1 h2 h3 h4 (h5.trans hKη) (h6.trans hKη)
  -- the two limits
  set LU : ℝ := ∑ i ∈ Idx K L, cUp K δ i * (K0 * mu K i) +
    M * (4 * (1 / 2 - -(1 / 2)) / L * (kappa * Wc)) with hLU
  set LL : ℝ := ∑ i ∈ Idx K L, cLo K δ i * (K0 * mu K i) with hLL
  have hTU : Tendsto (fun y => ∑ i ∈ Idx K L, cUp K δ i * bxR K i y +
      M * horoR (-(1 / 2)) (1 / 2) L y) (𝓝[>] 0) (𝓝 LU) :=
    (tendsto_finsetSum _ fun i hi => (tendsto_bxR hK6 hi).const_mul _).add
      ((tendsto_horoR (by norm_num) hLpos).const_mul _)
  have hTL : Tendsto (fun y => ∑ i ∈ Idx K L, cLo K δ i * bxR K i y) (𝓝[>] 0) (𝓝 LL) :=
    tendsto_finsetSum _ fun i hi => (tendsto_bxR hK6 hi).const_mul _
  refine ⟨LU / 2, LL / 2, ?_, ?_, ?_⟩
  · -- the gap
    have e : LU - LL = K0 * (∑ i ∈ Idx K L, (cUp K δ i - cLo K δ i) * mu K i + M / L) := by
      rw [hLU, hLL, add_sub_right_comm, ← Finset.sum_sub_distrib, mul_add, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · unfold K0; field_simp; ring
    have hstuff0 : 0 ≤ ∑ i ∈ Idx K L, (cUp K δ i - cLo K δ i) * mu K i + M / L :=
      add_nonneg (Finset.sum_nonneg fun i hi =>
        mul_nonneg (cUp_sub_cLo_nonneg hδ i) (mu_le (L := L) hK6 hi).1) (by positivity)
    have hgap := gap_le (L := L) hK6 hδ hM
    have hLU_LL : LU - LL ≤ Kc * (16 * (M + δ) / K + 8 * δ * L + M / L) := by
      rw [e]
      calc K0 * (∑ i ∈ Idx K L, (cUp K δ i - cLo K δ i) * mu K i + M / L)
          ≤ |K0| * (∑ i ∈ Idx K L, (cUp K δ i - cLo K δ i) * mu K i + M / L) := by
            exact mul_le_mul_of_nonneg_right (le_abs_self _) hstuff0
        _ ≤ Kc * (∑ i ∈ Idx K L, (cUp K δ i - cLo K δ i) * mu K i + M / L) :=
            mul_le_mul_of_nonneg_right (by linarith) hstuff0
        _ ≤ Kc * (16 * (M + δ) / K + 8 * δ * L + M / L) := by gcongr
    -- each piece is at most `ε/3`
    have p1 : Kc * (16 * (M + δ) / K) ≤ ε / 3 := by
      have : 16 * (M + δ) / K ≤ 16 * (M + 1) / K := by gcongr
      have h2 : 48 * Kc * (M + 1) ≤ ε * K := by
        rw [div_lt_iff₀ hε] at hKε; linarith
      calc Kc * (16 * (M + δ) / K) ≤ Kc * (16 * (M + 1) / K) := by gcongr
        _ = 48 * Kc * (M + 1) / (3 * K) := by field_simp; ring
        _ ≤ ε * K / (3 * K) := by gcongr
        _ = ε / 3 := by field_simp
    have p2 : Kc * (8 * δ * L) ≤ ε / 3 := by
      calc Kc * (8 * δ * L) ≤ Kc * (8 * (ε / (24 * Kc * L)) * L) := by gcongr
        _ = ε / 3 := by field_simp; ring
    have p3 : Kc * (M / L) ≤ ε / 3 := by
      have : 3 * Kc * M < ε * L := by rw [div_lt_iff₀ hε] at hL; linarith
      calc Kc * (M / L) = 3 * Kc * M / (3 * L) := by field_simp
        _ ≤ ε * L / (3 * L) := by gcongr
        _ = ε / 3 := by field_simp
    have : LU - LL ≤ ε := by nlinarith
    linarith
  · -- upper eventually
    have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), ∑ i ∈ Idx K L, cUp K δ i * bxR K i y +
        M * horoR (-(1 / 2)) (1 / 2) L y < LU + ε :=
      hTU (Iio_mem_nhds (by linarith))
    have hy2 : ∀ᶠ y in 𝓝[>] (0 : ℝ), y < 1 / 2 := nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
    filter_upwards [hev, hy2, self_mem_nhdsWithin] with y h1 h2 h3
    have := upper_real hK6 hL1 hδ hM huc h3 h2
    linarith
  · have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), LL - ε < ∑ i ∈ Idx K L, cLo K δ i * bxR K i y :=
      hTL (Ioi_mem_nhds (by linarith))
    have hy2 : ∀ᶠ y in 𝓝[>] (0 : ℝ), y < 1 / 2 := nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
    filter_upwards [hev, hy2, self_mem_nhdsWithin] with y h1 h2 h3
    have := lower_real hK6 hL1 hM huc h3 h2 (δ := δ)
    linarith

end RamanujanTau.EisensteinReal.Horo

namespace RamanujanTau.EisensteinReal

open Real Filter Topology Finset
open RamanujanTau.RankinSelberg

/-- **Horocycle equidistribution for `G = |Δ|²y¹²` (unconditional).** The limit
`L = lim_{y→0⁺} ∫₀¹ |Δ(x+iy)|² y¹² dx` exists. (Its value `(3/π)‖Δ‖²` is not identified here.) -/
theorem exists_horocycleLimit : ∃ L, HorocycleLimit L := by
  obtain ⟨Λ, hΛ⟩ := Horo.exists_tendsto_Aint
  refine ⟨Λ, fun ε hε => ?_⟩
  rw [Metric.tendsto_nhdsWithin_nhds] at hΛ
  obtain ⟨y₀, hy₀, h⟩ := hΛ ε hε
  refine ⟨y₀, hy₀, fun y hy hyy => ?_⟩
  have hd : dist y 0 < y₀ := by rw [Real.dist_eq, sub_zero, abs_of_pos hy]; exact hyy
  have := h (show y ∈ Set.Ioi (0 : ℝ) from hy) hd
  rw [Real.dist_eq] at this
  unfold Horo.Aint at this
  rwa [dif_pos hy] at this

/-- **The Rankin–Selberg asymptotic, unconditional:**
`(1/N) ∑_{n ≤ N} τ(n)²/n¹¹ → c` for some `c > 0` (`c = (4π)¹² L/11!`). -/
theorem rankinSelberg_asymptotic_unconditional : ∃ c > 0,
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2 / (n : ℝ) ^ 11) / N) atTop (𝓝 c) := by
  obtain ⟨L, hL⟩ := exists_horocycleLimit
  refine ⟨(4 * π) ^ 12 * L / (Nat.factorial 11 : ℝ), ?_, rankinSelberg_asymptotic_of_horocycle hL⟩
  have := horocycleLimit_pos hL
  positivity

/-- **Mean square of `τ`, unconditional:** `∑_{n ≤ N} τ(n)² / N¹² → c' > 0`. -/
theorem sum_tau_sq_asymptotic_unconditional : ∃ c > 0,
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ((tau n : ℝ)) ^ 2) / (N : ℝ) ^ 12) atTop (𝓝 c) := by
  obtain ⟨L, hL⟩ := exists_horocycleLimit
  refine ⟨(4 * π) ^ 12 * L / (Nat.factorial 12 : ℝ), ?_, tendsto_sum_tau_sq_of_horocycle hL⟩
  have := horocycleLimit_pos hL
  positivity

end RamanujanTau.EisensteinReal

#print axioms RamanujanTau.EisensteinReal.Horo.exists_tendsto_Aint
#print axioms RamanujanTau.EisensteinReal.exists_horocycleLimit
#print axioms RamanujanTau.EisensteinReal.rankinSelberg_asymptotic_unconditional
#print axioms RamanujanTau.EisensteinReal.sum_tau_sq_asymptotic_unconditional
