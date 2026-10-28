import Mathlib

/-!
# Katz expansions and the sup norm: the analytic layer of step (K)

`K` is an ultrametric normed field. Classical forms are polynomials in `X 0 ↦ E₄`, `X 1 ↦ E₆` with
coefficients in `K`, and a "point" is a vector `x : Fin 2 → K` (in the application `x = (c₄(W), −c₆(W))`).

* `gnorm P` is the Gauss norm (largest coefficient norm) of `P ∈ K[X₀, X₁]`.
* `norm_eval_le` (ultrametric estimate): `‖P(x)‖ ≤ gnorm P` at integral points.
* `norm_eval_sub_le`: `‖P(x) − P(y)‖ ≤ gnorm P · δ` when `‖xᵢ − yᵢ‖ ≤ δ`.
* `kval E b x = Σ' i, b_i(x) / E(x)^i`, the value of the Katz series `Σ b_i / E^i` at `x`.
* `katz_iff`: for `0 < ‖r‖ < 1` and `gnorm b_i / ‖r‖^i → 0`,
  `(∀ i, gnorm b_i ≤ ‖r‖^i) ↔ (∀ test x with ‖E(x)‖ ≥ ‖r‖, ‖f(x)‖ ≤ 1)`.
  `⇒` holds for every family of integral test points. `⇐` assumes `DetectsNear T E (b i)`: every `b_i`
  attains its Gauss norm at test points whose `‖E‖` lies in any prescribed subinterval of `(0, 1]`.
  The proof uses no genericity: it picks the least index `i₀` of maximal excess and evaluates slightly
  outside the boundary `‖E‖ = ‖r‖`, where the `i₀` term strictly dominates.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace KatzForms
open MvPolynomial Filter Topology

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-! ### Gauss norm -/

/-- The Gauss norm: the largest norm of a coefficient. -/
noncomputable def gnorm (P : MvPolynomial (Fin 2) K) : ℝ :=
  ((P.support.sup fun d => ‖P.coeff d‖₊ : NNReal) : ℝ)

lemma gnorm_nonneg (P : MvPolynomial (Fin 2) K) : 0 ≤ gnorm P := NNReal.coe_nonneg _

lemma norm_coeff_le_gnorm (P : MvPolynomial (Fin 2) K) (d : Fin 2 →₀ ℕ) : ‖P.coeff d‖ ≤ gnorm P := by
  by_cases hd : d ∈ P.support
  · have : ‖P.coeff d‖₊ ≤ P.support.sup fun d => ‖P.coeff d‖₊ :=
      Finset.le_sup (f := fun d => ‖P.coeff d‖₊) hd
    exact_mod_cast this
  · rw [notMem_support_iff.mp hd, norm_zero]; exact gnorm_nonneg P

lemma gnorm_le {P : MvPolynomial (Fin 2) K} {C : ℝ} (hC : 0 ≤ C) (h : ∀ d, ‖P.coeff d‖ ≤ C) :
    gnorm P ≤ C := by
  have : (P.support.sup fun d => ‖P.coeff d‖₊) ≤ (⟨C, hC⟩ : NNReal) :=
    Finset.sup_le fun d _ => by
      change (‖P.coeff d‖₊ : ℝ) ≤ C
      exact h d
  exact_mod_cast this

lemma exists_coeff_eq_gnorm (P : MvPolynomial (Fin 2) K) : ∃ d, ‖P.coeff d‖ = gnorm P := by
  by_cases hs : P.support.Nonempty
  · obtain ⟨d, _, hd⟩ := Finset.exists_mem_eq_sup _ hs fun d => ‖P.coeff d‖₊
    refine ⟨d, ?_⟩
    unfold gnorm; rw [hd]; rfl
  · rw [Finset.not_nonempty_iff_eq_empty] at hs
    refine ⟨0, ?_⟩
    have : P = 0 := by rw [← support_eq_empty, hs]
    simp [this, gnorm]

/-! ### Integral points and the ultrametric estimate -/

/-- An integral point: both coordinates have norm `≤ 1`. -/
def Integral (x : Fin 2 → K) : Prop := ∀ i, ‖x i‖ ≤ 1

lemma norm_monomial_le {x : Fin 2 → K} (hx : Integral x) (d : Fin 2 →₀ ℕ) :
    ‖∏ i, x i ^ d i‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hx i)

/-- **Ultrametric estimate.** -/
theorem norm_eval_le {x : Fin 2 → K} (hx : Integral x) (P : MvPolynomial (Fin 2) K) :
    ‖eval x P‖ ≤ gnorm P := by
  rw [eval_eq']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (gnorm_nonneg P) fun d _ => ?_
  rw [norm_mul]
  calc ‖P.coeff d‖ * ‖∏ i, x i ^ d i‖ ≤ gnorm P * 1 :=
        mul_le_mul (norm_coeff_le_gnorm P d) (norm_monomial_le hx d) (norm_nonneg _) (gnorm_nonneg P)
    _ = gnorm P := mul_one _

lemma norm_pow_sub_pow_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖a‖ * ‖a ^ n - b ^ n‖ ≤ 1 * ‖a - b‖ := mul_le_mul ha ih (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    · rw [norm_mul, norm_pow]
      calc ‖a - b‖ * ‖b‖ ^ n ≤ ‖a - b‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hb) (norm_nonneg _)
        _ = _ := mul_one _

lemma norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → K) {δ : ℝ} (hδ : 0 ≤ δ)
    (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1) (h : ∀ i, ‖f i - g i‖ ≤ δ) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hδ
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖f a‖ * _ ≤ 1 * δ := mul_le_mul (hf a) ih (norm_nonneg _) zero_le_one
        _ = δ := one_mul _
    · rw [norm_mul, norm_prod]
      calc ‖f a - g a‖ * ∏ i ∈ s, ‖g i‖ ≤ δ * 1 :=
            mul_le_mul (h a) (Finset.prod_le_one (fun i _ => norm_nonneg _) fun i _ => hg i)
              (Finset.prod_nonneg fun i _ => norm_nonneg _) hδ
        _ = δ := mul_one _

/-- **Continuity estimate.** -/
theorem norm_eval_sub_le {x y : Fin 2 → K} (hx : Integral x) (hy : Integral y) {δ : ℝ} (hδ : 0 ≤ δ)
    (hxy : ∀ i, ‖x i - y i‖ ≤ δ) (P : MvPolynomial (Fin 2) K) :
    ‖eval x P - eval y P‖ ≤ gnorm P * δ := by
  rw [eval_eq', eval_eq', ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg (gnorm_nonneg P) hδ)
    fun d _ => ?_
  rw [← mul_sub, norm_mul]
  refine mul_le_mul (norm_coeff_le_gnorm P d) ?_ (norm_nonneg _) (gnorm_nonneg P)
  refine norm_prod_sub_prod_le _ _ _ hδ (fun i => ?_) (fun i => ?_) fun i => ?_
  · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hx i)
  · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hy i)
  · exact (norm_pow_sub_pow_le (hx i) (hy i) _).trans (hxy i)

/-- If `x` is congruent to `y` and `P` attains its Gauss norm at `y`, it attains it at `x`. -/
theorem norm_eval_eq_of_close {x y : Fin 2 → K} (hx : Integral x) (hy : Integral y)
    (hxy : ∀ i, ‖x i - y i‖ < 1) (P : MvPolynomial (Fin 2) K) (hP : ‖eval y P‖ = gnorm P) :
    ‖eval x P‖ = gnorm P := by
  set δ := max ‖x 0 - y 0‖ ‖x 1 - y 1‖
  have hδ0 : 0 ≤ δ := le_max_of_le_left (norm_nonneg _)
  have hδ1 : δ < 1 := max_lt (hxy 0) (hxy 1)
  have hle : ∀ i, ‖x i - y i‖ ≤ δ := by
    intro i; fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hd := norm_eval_sub_le hx hy hδ0 hle P
  rcases (gnorm_nonneg P).eq_or_lt with h0 | hpos
  · exact le_antisymm (h0 ▸ norm_eval_le hx P) (h0 ▸ norm_nonneg _)
  have hlt : ‖eval x P - eval y P‖ < ‖eval y P‖ := by
    rw [hP]; calc _ ≤ gnorm P * δ := hd
      _ < gnorm P * 1 := mul_lt_mul_of_pos_left hδ1 hpos
      _ = gnorm P := mul_one _
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
  rw [sub_add_cancel, max_eq_right hlt.le] at this
  rw [this, hP]

/-! ### Katz series -/

/-- The value at `x` of the Katz series `Σ b_i / E^i`. -/
noncomputable def kval (E : MvPolynomial (Fin 2) K) (b : ℕ → MvPolynomial (Fin 2) K)
    (x : Fin 2 → K) : K :=
  ∑' i, eval x (b i) / eval x E ^ i

lemma norm_term_le {E : MvPolynomial (Fin 2) K} {x : Fin 2 → K} (hx : Integral x)
    (P : MvPolynomial (Fin 2) K) (i : ℕ) :
    ‖eval x P / eval x E ^ i‖ ≤ gnorm P / ‖eval x E‖ ^ i := by
  rw [norm_div, norm_pow]
  exact div_le_div_of_nonneg_right (norm_eval_le hx P) (pow_nonneg (norm_nonneg _) _)

lemma norm_term_le' {E : MvPolynomial (Fin 2) K} {x : Fin 2 → K} (hx : Integral x) {r : K}
    (hr0 : 0 < ‖r‖) (hrE : ‖r‖ ≤ ‖eval x E‖) (P : MvPolynomial (Fin 2) K) (i : ℕ) :
    ‖eval x P / eval x E ^ i‖ ≤ gnorm P / ‖r‖ ^ i :=
  (norm_term_le hx P i).trans
    (div_le_div_of_nonneg_left (gnorm_nonneg P) (pow_pos hr0 i) (pow_le_pow_left₀ hr0.le hrE i))

theorem summable_kval [CompleteSpace K] {E : MvPolynomial (Fin 2) K} {b : ℕ → MvPolynomial (Fin 2) K}
    {r : K} (hr0 : 0 < ‖r‖) (hb : Tendsto (fun i => gnorm (b i) / ‖r‖ ^ i) atTop (𝓝 0))
    {x : Fin 2 → K} (hx : Integral x) (hrE : ‖r‖ ≤ ‖eval x E‖) :
    Summable fun i => eval x (b i) / eval x E ^ i := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  exact squeeze_zero_norm (fun i => norm_term_le' hx hr0 hrE (b i) i) hb

/-- **(K), easy direction**: the ultrametric estimate. -/
theorem kval_le_one_of_coeff [CompleteSpace K] {E : MvPolynomial (Fin 2) K}
    {b : ℕ → MvPolynomial (Fin 2) K} {r : K} (hr0 : 0 < ‖r‖) (hcoef : ∀ i, gnorm (b i) ≤ ‖r‖ ^ i)
    {x : Fin 2 → K} (hx : Integral x) (hrE : ‖r‖ ≤ ‖eval x E‖) : ‖kval E b x‖ ≤ 1 := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun i => ?_
  refine (norm_term_le' hx hr0 hrE (b i) i).trans ?_
  rw [div_le_one (pow_pos hr0 i)]
  exact hcoef i

/-- The detection hypothesis for one polynomial `P`: `P` attains its Gauss norm at test points whose
`‖E‖` lies in any prescribed subinterval of `(0, 1]`. -/
def DetectsNear (T : (Fin 2 → K) → Prop) (E P : MvPolynomial (Fin 2) K) : Prop :=
  ∀ s₀ s₁ : ℝ, 0 < s₀ → s₀ < s₁ → s₁ ≤ 1 →
    ∃ x, T x ∧ s₀ < ‖eval x E‖ ∧ ‖eval x E‖ < s₁ ∧ ‖eval x P‖ = gnorm P

/-- Maximal excess: a sequence tending to `0` that exceeds `1` somewhere has a least index of maximum. -/
lemma exists_first_max {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) {k : ℕ} (hk : 1 < a k) :
    ∃ i₀, 1 < a i₀ ∧ (∀ j, a j ≤ a i₀) ∧ ∀ j < i₀, a j < a i₀ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ha.eventually (gt_mem_nhds one_pos))
  have hkN : k < N := by
    by_contra h; exact absurd (hN k (not_lt.mp h)) (not_lt.mpr hk.le)
  obtain ⟨i₁, hi₁, hmax⟩ := Finset.exists_max_image (Finset.range N) a ⟨k, Finset.mem_range.mpr hkN⟩
  have hk1 : a k ≤ a i₁ := hmax k (Finset.mem_range.mpr hkN)
  have hglob : ∀ j, a j ≤ a i₁ := by
    intro j
    rcases lt_or_ge j N with hj | hj
    · exact hmax j (Finset.mem_range.mpr hj)
    · linarith [hN j hj]
  have hex : ∃ j, a j = a i₁ := ⟨i₁, rfl⟩
  classical
  refine ⟨Nat.find hex, ?_, ?_, ?_⟩
  · rw [Nat.find_spec hex]; linarith
  · intro j; rw [Nat.find_spec hex]; exact hglob j
  · intro j hj
    rw [Nat.find_spec hex]
    exact lt_of_le_of_ne (hglob j) (Nat.find_min hex hj)

/-- **(K) Katz expansions = sup norm.** -/
theorem katz_iff [CompleteSpace K] (E : MvPolynomial (Fin 2) K) (b : ℕ → MvPolynomial (Fin 2) K)
    (r : K) (hr0 : 0 < ‖r‖) (hr1 : ‖r‖ < 1)
    (hb : Tendsto (fun i => gnorm (b i) / ‖r‖ ^ i) atTop (𝓝 0))
    (T : (Fin 2 → K) → Prop) (hT : ∀ x, T x → Integral x)
    (hdet : ∀ i, DetectsNear T E (b i)) :
    (∀ i, gnorm (b i) ≤ ‖r‖ ^ i) ↔ ∀ x, T x → ‖r‖ ≤ ‖eval x E‖ → ‖kval E b x‖ ≤ 1 := by
  refine ⟨fun h x hx hrE => kval_le_one_of_coeff hr0 h (hT x hx) hrE, fun hval => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := hcon
  set a : ℕ → ℝ := fun i => gnorm (b i) / ‖r‖ ^ i with ha
  have hk' : 1 < a k := by rw [ha]; exact (one_lt_div (pow_pos hr0 k)).mpr hk
  obtain ⟨i₀, hM1, hmax, hfirst⟩ := exists_first_max hb hk'
  set M := a i₀ with hM
  have hM0 : 0 < M := one_pos.trans hM1
  -- choose the radius ratio `t ∈ (1, t₁)`
  have ev1 : ∀ᶠ t in 𝓝 (1 : ℝ), t ^ i₀ < M := by
    have := ((continuous_pow i₀).tendsto (1 : ℝ))
    rw [one_pow] at this
    exact this.eventually_lt_const hM1
  have ev2 : ∀ᶠ t in 𝓝 (1 : ℝ), ∀ j ∈ Finset.range i₀, a j * t ^ (i₀ + 1) < M * t ^ j := by
    rw [Filter.eventually_all_finset]
    intro j hj
    have h1 : Tendsto (fun t : ℝ => a j * t ^ (i₀ + 1)) (𝓝 1) (𝓝 (a j)) := by
      simpa using ((continuous_pow (i₀ + 1)).tendsto (1 : ℝ)).const_mul (a j)
    have h2 : Tendsto (fun t : ℝ => M * t ^ j) (𝓝 1) (𝓝 M) := by
      simpa using ((continuous_pow j).tendsto (1 : ℝ)).const_mul M
    exact h1.eventually_lt h2 (hfirst j (Finset.mem_range.mp hj))
  have ev3 : ∀ᶠ t in 𝓝 (1 : ℝ), ‖r‖ * t < 1 := by
    have : Tendsto (fun t : ℝ => ‖r‖ * t) (𝓝 1) (𝓝 ‖r‖) := by
      simpa using (continuous_id.tendsto (1 : ℝ)).const_mul ‖r‖
    exact this.eventually_lt_const hr1
  have evW := nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)) ((ev1.and ev2).and ev3)
  obtain ⟨u, hu1, hu⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp evW
  set t₂ := (1 + u) / 2
  have hu1' : (1 : ℝ) < u := hu1
  have ht₂ : t₂ ∈ Set.Ioo 1 u := ⟨by simp only [t₂]; linarith, by simp only [t₂]; linarith⟩
  have hgood₂ := hu ht₂
  obtain ⟨x, hxT, hx0, hx1, hxP⟩ := hdet i₀ ‖r‖ (‖r‖ * t₂) hr0
    (by nlinarith [ht₂.1]) hgood₂.2.le
  have hx := hT x hxT
  set s := ‖eval x E‖ with hs
  set t := s / ‖r‖ with ht
  have hst : s = ‖r‖ * t := by rw [ht]; field_simp
  have ht1 : 1 < t := by rw [ht, one_lt_div hr0]; exact hx0
  have ht2 : t < t₂ := by rw [ht, div_lt_iff₀ hr0]; linarith
  have hgood := hu ⟨ht1, ht2.trans ht₂.2⟩
  obtain ⟨⟨hc1, hc2⟩, _⟩ := hgood
  have ht0 : 0 < t := one_pos.trans ht1
  have hrE : ‖r‖ ≤ ‖eval x E‖ := hx0.le
  -- term bounds
  have hterm : ∀ j, ‖eval x (b j) / eval x E ^ j‖ ≤ a j / t ^ j := by
    intro j
    refine (norm_term_le hx (b j) j).trans (le_of_eq ?_)
    rw [← hs, hst, mul_pow, ha]; field_simp
  have hrest : ∀ j, ‖(if j = i₀ then (0 : K) else eval x (b j) / eval x E ^ j)‖ ≤ M / t ^ (i₀ + 1) := by
    intro j
    split_ifs with hj
    · rw [norm_zero]; positivity
    refine (hterm j).trans ?_
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · have := hc2 j (Finset.mem_range.mpr hlt)
      rw [div_le_div_iff₀ (pow_pos ht0 _) (pow_pos ht0 _)]; linarith
    · calc a j / t ^ j ≤ M / t ^ j := div_le_div_of_nonneg_right (hmax j) (pow_nonneg ht0.le _)
        _ ≤ M / t ^ (i₀ + 1) :=
          div_le_div_of_nonneg_left hM0.le (pow_pos ht0 _) (pow_le_pow_right₀ ht1.le hgt)
  have hmain : ‖eval x (b i₀) / eval x E ^ i₀‖ = M / t ^ i₀ := by
    rw [norm_div, norm_pow, hxP, ← hs, hst, mul_pow, hM, ha]; field_simp
  have hsum := summable_kval (E := E) hr0 hb hx hrE
  have hsplit := hsum.tsum_eq_add_tsum_ite i₀
  have hR : ‖∑' j, (if j = i₀ then (0 : K) else eval x (b j) / eval x E ^ j)‖ ≤ M / t ^ (i₀ + 1) :=
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) hrest
  have hlt : M / t ^ (i₀ + 1) < M / t ^ i₀ :=
    div_lt_div_of_pos_left hM0 (pow_pos ht0 _) (pow_lt_pow_right₀ ht1 (Nat.lt_succ_self _))
  have hne : ‖∑' j, (if j = i₀ then (0 : K) else eval x (b j) / eval x E ^ j)‖ ≠
      ‖eval x (b i₀) / eval x E ^ i₀‖ := by rw [hmain]; exact (hR.trans_lt hlt).ne
  have hnorm : ‖kval E b x‖ = M / t ^ i₀ := by
    rw [kval, hsplit, add_comm, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, hmain]
    exact max_eq_right (hR.trans hlt.le)
  have h1 : 1 < M / t ^ i₀ := by rw [one_lt_div (pow_pos ht0 _)]; exact hc1
  linarith [hval x hxT hrE]

end KatzForms
