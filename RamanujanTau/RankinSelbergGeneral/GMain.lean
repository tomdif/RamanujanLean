/-
# Horocycle equidistribution for `G = |Δ|²y¹²`, and the unconditional Rankin–Selberg asymptotic

Route B, completed. `G` is sandwiched between box counts:

* upper: `2G(z) ≤ ∑_γ up(γz)`, `up = ∑_{boxes} (G(corner)+δ)·1_box + M·1_{[−½,½)×[L,∞)}`,
  because every orbit meets `U = {−½ ≤ Re < ½, |w| ≥ 1}` (twice: `±γ`);
* lower: `∑_γ lo(γz) ≤ 2G(z)`, `lo = ∑_{boxes ⊂ S} (G(corner)−δ)⁺·1_box`, because each orbit
  meets `S = {−½ ≤ Re < ½, |w| > 1}` at most at `±γ`.

The boxes form a `1/K`-grid adapted to the arc `|w| = 1` column by column (`√(1−x²)` is
1-Lipschitz on `[−½, ½]`). Every box count has a horocycle limit (`tendsto_boxR`), and the
limits of `up` and `lo` differ by `|K₀|(16(M+δ)/K + 8δL + M/L)`, which is arbitrarily small.
So `∫₀¹ G(x+iy) dx` is Cauchy as `y → 0⁺`.

Headlines: `exists_horocycleLimit : ∃ L, HorocycleLimit L` and
`rankinSelberg_asymptotic_unconditional : ∃ c > 0, (1/N)∑_{n≤N} τ(n)²/n¹¹ → c`.
-/
import RamanujanTau.RankinSelbergGeneral.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.RankinSelbergGeneral.Horo

open RamanujanTau.EisensteinReal.Horo
open HoroFn
variable [HoroFn]

open Finset Real Filter Topology MeasureTheory ModularGroup
open RamanujanTau.RankinSelberg hiding G G_smul continuous_G G_pos
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal

/-! ### Elementary facts -/

/-- The point `x + i·max(y, 1/4)`. -/
noncomputable def gpt (x y : ℝ) : ℍ :=
  ⟨(x : ℂ) + (max y (1 / 4) : ℝ) * Complex.I, by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
    exact lt_max_of_lt_right (by norm_num)⟩

lemma gpt_re (x y : ℝ) : (gpt x y).re = x := by
  simp [gpt, UpperHalfPlane.re]

lemma gpt_im (x y : ℝ) : (gpt x y).im = max y (1 / 4) := by
  simp [gpt, UpperHalfPlane.im]

lemma gpt_eq {w : ℍ} (hw : 1 / 4 ≤ w.im) : gpt w.re w.im = w := by
  apply UpperHalfPlane.ext
  apply Complex.ext
  · simpa using gpt_re w.re w.im
  · have := gpt_im w.re w.im
    rw [max_eq_left hw] at this
    simpa using this

lemma continuous_gpt : Continuous fun p : ℝ × ℝ => gpt p.1 p.2 :=
  Continuous.upperHalfPlaneMk (by fun_prop) _

/-- Uniform continuity of `G` on `[−½,½] × [¼, Y]`. -/
lemma exists_uc (Y δ : ℝ) (hδ : 0 < δ) : ∃ η > 0, ∀ w w' : ℍ,
    w.re ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → w'.re ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) →
    w.im ∈ Set.Icc (1 / 4 : ℝ) Y → w'.im ∈ Set.Icc (1 / 4 : ℝ) Y →
    |w.re - w'.re| ≤ η → |w.im - w'.im| ≤ η → |G w - G w'| ≤ δ := by
  set s : Set (ℝ × ℝ) := Set.Icc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Set.Icc (1 / 4 : ℝ) Y
  have hs : IsCompact s := isCompact_Icc.prod isCompact_Icc
  have hf := hs.uniformContinuousOn_of_continuous
    (continuous_G.comp continuous_gpt).continuousOn
  rw [Metric.uniformContinuousOn_iff_le] at hf
  obtain ⟨η, hη, h⟩ := hf δ hδ
  refine ⟨η, hη, fun w w' h1 h2 h3 h4 h5 h6 => ?_⟩
  have := h (w.re, w.im) ⟨h1, h3⟩ (w'.re, w'.im) ⟨h2, h4⟩ (by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; exact max_le h5 h6)
  simp only [Function.comp, Real.dist_eq] at this
  rwa [gpt_eq h3.1, gpt_eq h4.1] at this

lemma le_sqrt_of {t : ℝ} (h : (17 / 20 : ℝ) ^ 2 ≤ t) : (17 / 20 : ℝ) ≤ Real.sqrt t := by
  rw [show (17 / 20 : ℝ) = Real.sqrt ((17 / 20) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt h

/-- `√(1−x²)` is 1-Lipschitz on `[−½, ½]`. -/
lemma sqrt_lip {x x' : ℝ} (hx : |x| ≤ 1 / 2) (hx' : |x'| ≤ 1 / 2) :
    |Real.sqrt (1 - x ^ 2) - Real.sqrt (1 - x' ^ 2)| ≤ |x - x'| := by
  have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs x, abs_nonneg x]
  have hx'2 : x' ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs x', abs_nonneg x']
  set p := Real.sqrt (1 - x ^ 2)
  set q := Real.sqrt (1 - x' ^ 2)
  have hp2 : p ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by linarith)
  have hq2 : q ^ 2 = 1 - x' ^ 2 := Real.sq_sqrt (by linarith)
  have hp : (17 / 20 : ℝ) ≤ p := le_sqrt_of (by nlinarith)
  have hq : (17 / 20 : ℝ) ≤ q := le_sqrt_of (by nlinarith)
  have hsum : |x + x'| ≤ 1 := by
    calc |x + x'| ≤ |x| + |x'| := abs_add_le _ _
      _ ≤ 1 := by linarith
  have key : |p - q| * (p + q) = |x - x'| * |x + x'| := by
    rw [← abs_of_pos (by linarith : (0 : ℝ) < p + q), ← abs_mul, ← abs_mul]
    rw [show (p - q) * (p + q) = -((x - x') * (x + x')) by nlinarith]
    exact abs_neg _
  have h1 : |x - x'| * |x + x'| ≤ |x - x'| :=
    mul_le_of_le_one_right (abs_nonneg _) hsum
  have h2 : |p - q| ≤ |p - q| * (p + q) :=
    le_mul_of_one_le_right (abs_nonneg _) (by linarith)
  linarith

/-! ### The grid -/

section Grid
variable (K L : ℕ) (δ : ℝ)

noncomputable def xj (j : ℕ) : ℝ := -(1 / 2) + j / K
noncomputable def fj (j : ℕ) : ℝ := Real.sqrt (1 - xj K j ^ 2)
noncomputable def ajk (j k : ℕ) : ℝ := fj K j - 2 / K + k / K
def Idx : Finset (ℕ × ℕ) := range K ×ˢ range (K * L)
noncomputable def bx (i : ℕ × ℕ) : Set ℍ :=
  box (xj K i.1) (xj K i.1 + 1 / K) (ajk K i.1 i.2) (ajk K i.1 i.2 + 1 / K)
noncomputable def bxInd (i : ℕ × ℕ) (w : ℍ) : ℝ≥0∞ :=
  boxInd (xj K i.1) (xj K i.1 + 1 / K) (ajk K i.1 i.2) (ajk K i.1 i.2 + 1 / K) w
noncomputable def Gc' (i : ℕ × ℕ) : ℝ := G (gpt (xj K i.1) (ajk K i.1 i.2))
noncomputable def cUp (i : ℕ × ℕ) : ℝ := Gc' K i + δ
noncomputable def cLo (i : ℕ × ℕ) : ℝ := if 4 ≤ i.2 then max (Gc' K i - δ) 0 else 0

/-- The upper function. -/
noncomputable def up (M : ℝ) (w : ℍ) : ℝ≥0∞ :=
  ∑ i ∈ Idx K L, ENNReal.ofReal (cUp K δ i) * bxInd K i w +
    ENNReal.ofReal M * ind (-(1 / 2)) (1 / 2) L w

/-- The lower function. -/
noncomputable def lo (w : ℍ) : ℝ≥0∞ :=
  ∑ i ∈ Idx K L, ENNReal.ofReal (cLo K δ i) * bxInd K i w

end Grid

section GridFacts
variable {K : ℕ} (hK : 6 ≤ K)
include hK

lemma K_pos : (0 : ℝ) < K := by
  have h : (6 : ℝ) ≤ K := (by exact_mod_cast hK)
  linarith

lemma xj_bounds {j : ℕ} (hj : j < K) : -(1 / 2) ≤ xj K j ∧ xj K j + 1 / K ≤ 1 / 2 := by
  have hK' := K_pos hK
  have hj' : (j : ℝ) + 1 ≤ K := by exact_mod_cast hj
  unfold xj
  constructor
  · have : (0 : ℝ) ≤ j / K := by positivity
    linarith
  · have : (j : ℝ) / K + 1 / K ≤ 1 := by
      rw [← add_div, div_le_one hK']; exact hj'
    linarith

lemma fj_bounds {j : ℕ} (hj : j < K) : (17 / 20 : ℝ) ≤ fj K j ∧ fj K j ≤ 1 := by
  obtain ⟨h1, h2⟩ := xj_bounds hK hj
  have hK' := K_pos hK
  have h3 : xj K j ≤ 1 / 2 := by
    have : (0 : ℝ) < 1 / K := by positivity
    linarith
  have hx2 : xj K j ^ 2 ≤ 1 / 4 := by nlinarith
  unfold fj
  constructor
  · exact le_sqrt_of (by nlinarith)
  · rw [Real.sqrt_le_one]; nlinarith [sq_nonneg (xj K j)]

lemma inv_K_le : (1 : ℝ) / K ≤ 1 / 6 := by
  have : (6 : ℝ) ≤ K := by exact_mod_cast hK
  exact one_div_le_one_div_of_le (by norm_num) this

lemma ajk_ge {j k : ℕ} (hj : j < K) : (1 / 2 : ℝ) ≤ ajk K j k := by
  have := (fj_bounds hK hj).1
  have h6 := inv_K_le hK
  have hk : (0 : ℝ) ≤ k / K := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  unfold ajk
  have : (2 : ℝ) / K = 2 * (1 / K) := by ring
  linarith

end GridFacts

/-! ### Upper and lower pointwise bounds -/

lemma mem_box_iff {α β a b : ℝ} {w : ℍ} :
    w ∈ box α β a b ↔ α ≤ w.re ∧ w.re < β ∧ a ≤ w.im ∧ w.im < b := Iff.rfl

lemma boxInd_of_mem {α β a b : ℝ} {w : ℍ} (h : w ∈ box α β a b) : boxInd α β a b w = 1 := by
  unfold boxInd; rw [Set.indicator_of_mem h]; rfl

lemma boxInd_of_notMem {α β a b : ℝ} {w : ℍ} (h : w ∉ box α β a b) :
    boxInd α β a b w = 0 := by
  unfold boxInd; rw [Set.indicator_of_notMem h]

lemma bxInd_of_notMem {K : ℕ} {i : ℕ × ℕ} {w : ℍ} (h : w ∉ bx K i) : bxInd K i w = 0 :=
  boxInd_of_notMem h

/-- The column index of `x ∈ [−½, ½)`. -/
lemma exists_col {K : ℕ} (hK : 6 ≤ K) {x : ℝ} (h1 : -(1 / 2) ≤ x) (h2 : x < 1 / 2) :
    ∃ j < K, xj K j ≤ x ∧ x < xj K j + 1 / K := by
  have hK' := K_pos hK
  set t := (x + 1 / 2) * K
  have ht0 : 0 ≤ t := mul_nonneg (by linarith) hK'.le
  refine ⟨⌊t⌋₊, ?_, ?_, ?_⟩
  · have : t < K := by
      have : x + 1 / 2 < 1 := by linarith
      calc t = (x + 1 / 2) * K := rfl
        _ < 1 * K := mul_lt_mul_of_pos_right this hK'
        _ = K := one_mul _
    exact (Nat.floor_lt ht0).2 this
  · have := Nat.floor_le ht0
    unfold xj
    have : (⌊t⌋₊ : ℝ) / K ≤ x + 1 / 2 := by rw [div_le_iff₀ hK']; exact this
    linarith
  · have := Nat.lt_floor_add_one t
    unfold xj
    have : x + 1 / 2 < (⌊t⌋₊ : ℝ) / K + 1 / K := by
      rw [← add_div, lt_div_iff₀ hK']; exact this
    linarith

/-- Uniqueness of the column index. -/
lemma col_unique {K : ℕ} (hK : 6 ≤ K) {x : ℝ} {j j' : ℕ}
    (h1 : xj K j ≤ x) (h2 : x < xj K j + 1 / K) (h1' : xj K j' ≤ x) (h2' : x < xj K j' + 1 / K) :
    j = j' := by
  have hK' := K_pos hK
  unfold xj at *
  have a1 : (j : ℝ) < j' + 1 := by
    have : (j : ℝ) / K < j' / K + 1 / K := by linarith
    rw [← add_div, div_lt_div_iff_of_pos_right hK'] at this; exact this
  have a2 : (j' : ℝ) < j + 1 := by
    have : (j' : ℝ) / K < j / K + 1 / K := by linarith
    rw [← add_div, div_lt_div_iff_of_pos_right hK'] at this; exact this
  have b1 : j < j' + 1 := by exact_mod_cast a1
  have b2 : j' < j + 1 := by exact_mod_cast a2
  omega

/-- The row index of `t ≥ b`. -/
lemma exists_row {K : ℕ} (hK : 6 ≤ K) {b t : ℝ} (hbt : b ≤ t) :
    ∃ k : ℕ, b + k / K ≤ t ∧ t < b + k / K + 1 / K ∧ (k : ℝ) ≤ (t - b) * K := by
  have hK' := K_pos hK
  set u := (t - b) * K
  have hu0 : 0 ≤ u := mul_nonneg (by linarith) hK'.le
  refine ⟨⌊u⌋₊, ?_, ?_, Nat.floor_le hu0⟩
  · have := Nat.floor_le hu0
    have : (⌊u⌋₊ : ℝ) / K ≤ t - b := by rw [div_le_iff₀ hK']; exact this
    linarith
  · have := Nat.lt_floor_add_one u
    have : t - b < (⌊u⌋₊ : ℝ) / K + 1 / K := by
      rw [← add_div, lt_div_iff₀ hK']; exact this
    linarith

lemma row_unique {K : ℕ} (hK : 6 ≤ K) {b t : ℝ} {k k' : ℕ}
    (h1 : b + k / K ≤ t) (h2 : t < b + k / K + 1 / K)
    (h1' : b + k' / K ≤ t) (h2' : t < b + k' / K + 1 / K) : k = k' := by
  have hK' := K_pos hK
  have a1 : (k : ℝ) < k' + 1 := by
    have : (k : ℝ) / K < k' / K + 1 / K := by linarith
    rw [← add_div, div_lt_div_iff_of_pos_right hK'] at this; exact this
  have a2 : (k' : ℝ) < k + 1 := by
    have : (k' : ℝ) / K < k / K + 1 / K := by linarith
    rw [← add_div, div_lt_div_iff_of_pos_right hK'] at this; exact this
  have b1 : k < k' + 1 := by exact_mod_cast a1
  have b2 : k' < k + 1 := by exact_mod_cast a2
  omega

lemma im_ge_sqrt {w : ℍ} (h : 1 ≤ Complex.normSq (w : ℂ)) :
    Real.sqrt (1 - w.re ^ 2) ≤ w.im := by
  rw [Complex.normSq_apply] at h
  have him := w.im_pos
  have e1 : (w : ℂ).re = w.re := rfl
  have e2 : (w : ℂ).im = w.im := rfl
  rw [e1, e2] at h
  calc Real.sqrt (1 - w.re ^ 2) ≤ Real.sqrt (w.im ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = w.im := Real.sqrt_sq him.le

section Bounds
variable {K L : ℕ} {δ M : ℝ} (hK : 6 ≤ K) (hL : 1 ≤ L) (hM : ∀ z : ℍ, G z ≤ M)
  (huc : ∀ w w' : ℍ,
    w.re ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → w'.re ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) →
    w.im ∈ Set.Icc (1 / 4 : ℝ) (L + 2) → w'.im ∈ Set.Icc (1 / 4 : ℝ) (L + 2) →
    |w.re - w'.re| ≤ 1 / K → |w.im - w'.im| ≤ 1 / K → |G w - G w'| ≤ δ)

include hK hL hM huc in
/-- **Upper pointwise bound** on `U`. -/
theorem up_ge {w : ℍ} (hw : w ∈ Uset) : ENNReal.ofReal (G w) ≤ up K L δ M w := by
  obtain ⟨h1, h2, h3⟩ := hw
  have hK' := K_pos hK
  have h6 := inv_K_le hK
  unfold up
  by_cases hL' : (L : ℝ) ≤ w.im
  · -- cusp
    have hmem : w ∈ rect (-(1 / 2)) (1 / 2) L := ⟨h1, h2, hL'⟩
    have : ind (-(1 / 2)) (1 / 2) L w = 1 := by
      unfold ind; rw [Set.indicator_of_mem hmem]; rfl
    rw [this, mul_one]
    exact le_add_left (ENNReal.ofReal_le_ofReal (hM w))
  · push_neg at hL'
    obtain ⟨j, hjK, hj1, hj2⟩ := exists_col hK h1 h2
    obtain ⟨hx1, hx2⟩ := xj_bounds hK hjK
    -- `Im w ≥ f_j − 1/K`
    have hlip := sqrt_lip (x := w.re) (x' := xj K j) (by rw [abs_le]; constructor <;> linarith)
      (by rw [abs_le]; constructor <;> linarith)
    have hdx : |w.re - xj K j| ≤ 1 / K := by rw [abs_le]; constructor <;> linarith
    have hsq := im_ge_sqrt h3
    have hfj : fj K j - 1 / K ≤ w.im := by
      unfold fj
      have := (abs_le.1 (hlip.trans hdx)).1
      linarith
    have hb : fj K j - 2 / K ≤ w.im := by
      have : (2 : ℝ) / K = 1 / K + 1 / K := by ring
      linarith [show (0 : ℝ) < 1 / K by positivity]
    obtain ⟨k, hk1, hk2, hk3⟩ := exists_row hK hb
    have hk1' : ajk K j k ≤ w.im := hk1
    have hk2' : w.im < ajk K j k + 1 / K := hk2
    have hkN : k < K * L := by
      have hbpos : 0 < fj K j - 2 / K := by
        have := (fj_bounds hK hjK).1
        have : (2 : ℝ) / K = 2 * (1 / K) := by ring
        linarith
      have : (k : ℝ) < K * L := by
        calc (k : ℝ) ≤ (w.im - (fj K j - 2 / K)) * K := hk3
          _ < L * K := mul_lt_mul_of_pos_right (by linarith) hK'
          _ = K * L := mul_comm _ _
      exact_mod_cast this
    have hi : (j, k) ∈ Idx K L := Finset.mem_product.2 ⟨Finset.mem_range.2 hjK,
      Finset.mem_range.2 hkN⟩
    have hmem : w ∈ bx K (j, k) := ⟨hj1, hj2, hk1, hk2⟩
    have hind : bxInd K (j, k) w = 1 := boxInd_of_mem hmem
    -- `G(w) ≤ G(corner) + δ`
    have ha := ajk_ge hK hjK (k := k)
    have haL : ajk K j k ≤ L + 1 := by
      have : ajk K j k ≤ w.im := hk1
      linarith
    have hGc : G w ≤ cUp K δ (j, k) := by
      have hc := huc w (gpt (xj K j) (ajk K j k))
        ⟨by linarith, by linarith⟩
        (by rw [gpt_re]; exact ⟨hx1, by linarith⟩)
        ⟨by linarith, by linarith⟩
        (by rw [gpt_im, max_eq_left (by linarith)]; exact ⟨by linarith, by linarith⟩)
        (by rw [gpt_re]; exact hdx)
        (by rw [gpt_im, max_eq_left (by linarith), abs_le]
            constructor <;> linarith)
      unfold cUp Gc'
      linarith [(abs_le.1 hc).2]
    calc ENNReal.ofReal (G w) ≤ ENNReal.ofReal (cUp K δ (j, k)) * bxInd K (j, k) w := by
          rw [hind, mul_one]; exact ENNReal.ofReal_le_ofReal hGc
      _ ≤ ∑ i ∈ Idx K L, ENNReal.ofReal (cUp K δ i) * bxInd K i w :=
          Finset.single_le_sum (f := fun i => ENNReal.ofReal (cUp K δ i) * bxInd K i w)
            (fun _ _ => zero_le) hi
      _ ≤ _ := le_self_add

include hK hL hM huc in
/-- **Lower pointwise bound:** `lo` vanishes off `S` and is `≤ G` on `S`. -/
theorem lo_spec : (∀ w, w ∉ Sset → lo K L δ w = 0) ∧
    (∀ w ∈ Sset, lo K L δ w ≤ ENNReal.ofReal (G w)) := by
  have hK' := K_pos hK
  have h6 := inv_K_le hK
  -- a box with `k ≥ 4` lies in `S`
  have hsub : ∀ i ∈ Idx K L, 4 ≤ i.2 → ∀ w ∈ bx K i, w ∈ Sset := by
    intro i hi hk w hw
    obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
    have hjK := Finset.mem_range.1 (Finset.mem_product.1 hi).1
    obtain ⟨hx1, hx2⟩ := xj_bounds hK hjK
    refine ⟨by linarith, by linarith, ?_⟩
    have hlip := sqrt_lip (x := w.re) (x' := xj K i.1) (by rw [abs_le]; constructor <;> linarith)
      (by rw [abs_le]; constructor <;> linarith)
    have hdx : |w.re - xj K i.1| ≤ 1 / K := by rw [abs_le]; constructor <;> linarith
    have hk4 : (4 : ℝ) / K ≤ i.2 / K := by
      have : (4 : ℝ) ≤ i.2 := by exact_mod_cast hk
      exact div_le_div_of_nonneg_right this hK'.le
    have hlt : Real.sqrt (1 - w.re ^ 2) < w.im := by
      have := (abs_le.1 (hlip.trans hdx)).2
      unfold ajk at hw3
      unfold fj at hw3
      have : (4 : ℝ) / K = 2 / K + 2 * (1 / K) := by ring
      linarith [show (0 : ℝ) < 1 / K by positivity]
    have hre2 : w.re ^ 2 ≤ 1 := by nlinarith
    have hs0 := Real.sqrt_nonneg (1 - w.re ^ 2)
    have hsq : Real.sqrt (1 - w.re ^ 2) ^ 2 = 1 - w.re ^ 2 := Real.sq_sqrt (by linarith)
    rw [Complex.normSq_apply]
    have e1 : (w : ℂ).re = w.re := rfl
    have e2 : (w : ℂ).im = w.im := rfl
    rw [e1, e2]
    nlinarith
  constructor
  · intro w hw
    unfold lo
    refine Finset.sum_eq_zero fun i hi => ?_
    unfold cLo
    split_ifs with hk
    · rw [bxInd_of_notMem (fun hm => hw (hsub i hi hk w hm)), mul_zero]
    · simp
  · intro w hw
    unfold lo
    by_cases hex : ∃ i ∈ Idx K L, w ∈ bx K i
    · obtain ⟨i₀, hi₀, hw₀⟩ := hex
      rw [Finset.sum_eq_single_of_mem i₀ hi₀]
      · rw [show bxInd K i₀ w = 1 from boxInd_of_mem hw₀, mul_one]
        apply ENNReal.ofReal_le_ofReal
        unfold cLo
        split_ifs
        · have hjK := Finset.mem_range.1 (Finset.mem_product.1 hi₀).1
          obtain ⟨hx1, hx2⟩ := xj_bounds hK hjK
          obtain ⟨hw1, hw2, hw3, hw4⟩ := hw₀
          have ha := ajk_ge hK hjK (k := i₀.2)
          have hkN := Finset.mem_range.1 (Finset.mem_product.1 hi₀).2
          have haL : ajk K i₀.1 i₀.2 ≤ L + 1 := by
            unfold ajk
            have hf := (fj_bounds hK hjK).2
            have : (i₀.2 : ℝ) + 1 ≤ K * L := by exact_mod_cast hkN
            have : (i₀.2 : ℝ) / K ≤ L - 1 / K := by
              rw [div_le_iff₀ hK']; field_simp; linarith
            linarith [show (0 : ℝ) < 2 / K by positivity]
          have hc := huc w (gpt (xj K i₀.1) (ajk K i₀.1 i₀.2))
            ⟨by linarith, by linarith⟩
            (by rw [gpt_re]; exact ⟨hx1, by linarith⟩)
            ⟨by linarith, by linarith⟩
            (by rw [gpt_im, max_eq_left (by linarith)]; exact ⟨by linarith, by linarith⟩)
            (by rw [gpt_re, abs_le]; constructor <;> linarith)
            (by rw [gpt_im, max_eq_left (by linarith), abs_le]
                constructor <;> linarith)
          unfold Gc'
          exact max_le (by linarith [(abs_le.1 hc).1]) (G_nonneg w)
        · exact (G_nonneg w)
      · intro i hi hne
        rw [bxInd_of_notMem, mul_zero]
        intro hmem
        apply hne
        obtain ⟨a1, a2, a3, a4⟩ := hmem
        obtain ⟨b1, b2, b3, b4⟩ := hw₀
        have hj := col_unique hK a1 a2 b1 b2
        have hk : i.2 = i₀.2 := by
          unfold ajk at a3 a4 b3 b4
          rw [hj] at a3 a4
          exact row_unique hK a3 a4 b3 b4
        exact Prod.ext hj hk
    · push_neg at hex
      rw [Finset.sum_eq_zero fun i hi => by rw [bxInd_of_notMem (hex i hi), mul_zero]]
      exact zero_le

end Bounds

end RamanujanTau.RankinSelbergGeneral.Horo
