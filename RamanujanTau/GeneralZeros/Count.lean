/-
# Zeros of `L(f,s)` in unit windows, for every nonzero level-one cusp form `f`

`N_f(a,b)` counts the zeros of `Λ(f,s)` with `a < Im ≤ b`, with multiplicity; off the real axis
these are exactly the zeros of `L(f,s)`, with the same multiplicities (`zeroSet_eq_fL`,
`ord_eq_fL`).  All of them lie in `k − σ₁ < Re < σ₁` (`NormData`).

* `window_right`: Jensen (Mathlib `AnalyticOnNhd.sum_divisor_le`) for `L(f,·)` on the disc
  about `σ₁ + i(T+1/2)` of radius `d + 1/4`, `d = σ₁ − k/2`, inside the disc of radius `d + 1/2`
  (which stays in `Re ≥ (k−1)/2`, where `L ≪ (1+|s|)²`).  The lower bound at the centre is
  `|L(c)| ≥ (3/4)|a_f(n₀)| n₀^{−σ₁}`, from `|G − 1| ≤ 1/4` (no Euler product is used).
* `window_count`: zeros with `Re < k/2` are reflected by `s ↦ k − s` (functional equation, same
  order), so every unit window carries `≪ log(|T|+2)` zeros.
* `zeroSet_finite`, `zeroCountAB_add`, `zeroCount_window`, `zeroCount_le`.
-/
import RamanujanTau.GeneralZeros.Setup
import Mathlib.Analysis.Complex.JensenFormula

set_option autoImplicit false

namespace RamanujanTau.GeneralZeros

open Complex Set Filter Topology Metric MeromorphicOn ModularForm
open RamanujanTau.HeckeConvexGeneral
open scoped Real MatrixGroups

variable {k : ℕ}

/-- Multiplicity of `u` as a zero of `Λ(f,·)`. -/
noncomputable def ord (f : CuspForm 𝒮ℒ (k : ℤ)) (u : ℂ) : ℕ :=
  analyticOrderNatAt (heckeLambda f) u

/-- Zeros of `Λ(f,·)` with `a < Im ≤ b`. -/
def zeroSet (f : CuspForm 𝒮ℒ (k : ℤ)) (a b : ℝ) : Set ℂ :=
  {u | heckeLambda f u = 0 ∧ a < u.im ∧ u.im ≤ b}

/-- `N_f(a,b)`, with multiplicity. -/
noncomputable def zeroCountAB (f : CuspForm 𝒮ℒ (k : ℤ)) (a b : ℝ) : ℕ :=
  ∑ᶠ u ∈ zeroSet f a b, ord f u

/-- `N_f(T) = N_f(0,T)`. -/
noncomputable def zeroCount (f : CuspForm 𝒮ℒ (k : ℤ)) (T : ℝ) : ℕ := zeroCountAB f 0 T

lemma Lam_not_identically_zero (f : CuspForm 𝒮ℒ (k : ℤ)) (D : NormData f) :
    heckeLambda f (D.σ₁ : ℂ) ≠ 0 := D.Lam_ne_zero_right (by simp)

lemma order_Lam_ne_top (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) (D : NormData f) (u : ℂ) :
    analyticOrderAt (heckeLambda f) u ≠ ⊤ := by
  intro h
  rw [AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero u
    (fun z => (heckeLambda_entire f hk).analyticAt z)] at h
  exact Lam_not_identically_zero f D (by rw [h]; rfl)

lemma one_le_ord (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) (D : NormData f) {u : ℂ}
    (hu : heckeLambda f u = 0) : 1 ≤ ord f u := by
  have h0 : analyticOrderAt (heckeLambda f) u ≠ 0 :=
    analyticOrderAt_ne_zero.2 ⟨(heckeLambda_entire f hk).analyticAt u, hu⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (order_Lam_ne_top f hk D u)
  have : n ≠ 0 := by rintro rfl; exact h0 (by rw [← hn]; rfl)
  unfold ord analyticOrderNatAt
  rw [← hn, ENat.toNat_coe]; omega

lemma ord_reflect (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) (u : ℂ) :
    ord f ((k : ℂ) - u) = ord f u := by
  unfold ord analyticOrderNatAt; rw [order_reflect f hk]

lemma Lam_reflect_zero (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {u : ℂ}
    (hu : heckeLambda f u = 0) : heckeLambda f ((k : ℂ) - u) = 0 := by
  rw [heckeLambda_functional_equation f hk, hu, mul_zero]

/-! ### Jensen on the right half -/

lemma mem_disc_of_rect {σ₁ κ T : ℝ} (hd : 1 ≤ σ₁ - κ) {u : ℂ} (h1 : κ ≤ u.re) (h2 : u.re ≤ σ₁)
    (h3 : T ≤ u.im) (h4 : u.im ≤ T + 1) :
    u ∈ closedBall ((σ₁ : ℂ) + ((T + 1 / 2 : ℝ) : ℂ) * I) |σ₁ - κ + 1 / 4| := by
  rw [mem_closedBall, dist_eq_norm, abs_of_pos (by linarith)]
  set w : ℂ := u - ((σ₁ : ℂ) + ((T + 1 / 2 : ℝ) : ℂ) * I) with hw
  have hwr : w.re = u.re - σ₁ := by simp [hw]
  have hwi : w.im = u.im - (T + 1 / 2) := by simp [hw]
  have hsq : ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have hb : ‖w‖ ^ 2 ≤ (σ₁ - κ + 1 / 4) ^ 2 := by
    rw [hsq, hwr, hwi]; nlinarith
  nlinarith [norm_nonneg w]

set_option maxHeartbeats 1000000 in
/-- **Jensen for the right half of a window** `[k/2, σ₁] × [T, T+1]`. -/
theorem window_right (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 12 ≤ k) (D : NormData f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, ∀ S : Finset ℂ,
      (∀ u ∈ S, heckeLambda f u = 0 ∧ (k : ℝ) / 2 ≤ u.re ∧ u.re ≤ D.σ₁ ∧
        T ≤ u.im ∧ u.im ≤ T + 1) →
      ((∑ u ∈ S, ord f u : ℕ) : ℝ) ≤ C * Real.log (|T| + 2) := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨B, hB0, hB⟩ := fL_growth f hk
  have hkR : (12 : ℝ) ≤ k := by exact_mod_cast hk
  set κ : ℝ := (k : ℝ) / 2 with hκ
  set σ₁ := D.σ₁ with hσ₁def
  have hσ₁ : ((k : ℝ) + 1) / 2 + 1 ≤ σ₁ := D.hσ₁
  set d : ℝ := σ₁ - κ with hd
  have hd1 : 1 ≤ d := by rw [hd, hκ]; linarith
  set r : ℝ := d + 1 / 4 with hr
  set R : ℝ := d + 1 / 2 with hR
  have hr0 : 0 < r := by linarith
  have hrR : r < R := by linarith
  have hlam : 0 < Real.log (R / r) := Real.log_pos (by rw [one_lt_div hr0]; linarith)
  set lam := Real.log (R / r)
  set n₀ := D.n₀
  set a₀ := coef f n₀
  have ha₀n : 0 < ‖a₀‖ := norm_pos_iff.mpr D.ha₀
  have hn₀R : (1 : ℝ) ≤ n₀ := by exact_mod_cast D.hn₀
  set ℓ₀ : ℝ := 3 / 4 * ‖a₀‖ / (n₀ : ℝ) ^ σ₁ with hℓ₀
  have hℓ₀pos : 0 < ℓ₀ := by rw [hℓ₀]; have := Real.rpow_pos_of_pos (by linarith : (0:ℝ) < n₀) σ₁; positivity
  have hσ₁0 : 0 < σ₁ := by linarith
  set E : ℝ := Real.log (B + 1) + 2 * Real.log (1 + σ₁) - Real.log ℓ₀ with hE
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C : ℝ := (2 + |E| / Real.log 2) / lam with hC
  refine ⟨C, by rw [hC]; positivity, fun T S hS => ?_⟩
  set c : ℂ := (σ₁ : ℂ) + ((T + 1 / 2 : ℝ) : ℂ) * I with hc
  have hcre : c.re = σ₁ := by simp [hc]
  have hcim : c.im = T + 1 / 2 := by simp [hc]
  -- lower bound at the centre
  have hLc : ℓ₀ ≤ ‖fL f c‖ := by
    have hG := D.Gn_re_ge (s := c) (by rw [hcre])
    have hGn : 3 / 4 ≤ ‖Gn f n₀ c‖ := hG.trans (Complex.re_le_norm _)
    rw [norm_Gn f D.hn₀, hcre] at hGn
    have hp : 0 < (n₀ : ℝ) ^ σ₁ := Real.rpow_pos_of_pos (by linarith) σ₁
    rw [hℓ₀, div_le_iff₀ hp]
    rw [div_mul_eq_mul_div, le_div_iff₀ ha₀n] at hGn
    linarith
  have hc0 : fL f c ≠ 0 := by intro h; rw [h, norm_zero] at hLc; linarith
  -- the big circle
  set X : ℝ := 2 + 2 * σ₁ + |T| with hX
  have hX1 : 1 ≤ X := by rw [hX]; linarith [abs_nonneg T]
  set M : ℝ := (B + 1) * X ^ 2 with hM
  have hM1 : 1 ≤ M := by
    have : 1 ≤ X ^ 2 := one_le_pow₀ hX1
    rw [hM]; nlinarith
  have hbound : ∀ z ∈ sphere c |R|, ‖fL f z‖ ≤ M := by
    intro z hz
    rw [mem_sphere, abs_of_pos (by linarith), dist_eq_norm] at hz
    have hre : |z.re - σ₁| ≤ R := by
      have := Complex.abs_re_le_norm (z - c)
      rw [sub_re, hcre, hz] at this; exact this
    have hcn : ‖c‖ ≤ σ₁ + |T| + 1 / 2 := by
      refine (Complex.norm_le_abs_re_add_abs_im c).trans ?_
      rw [hcre, hcim, abs_of_pos hσ₁0]
      have := abs_add_le T (1 / 2)
      norm_num at this ⊢; linarith
    have hzn : ‖z‖ ≤ σ₁ + |T| + 1 / 2 + R := by
      have : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
        calc ‖z‖ = ‖(z - c) + c‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith
    have hRle : R ≤ σ₁ := by rw [hR, hd, hκ]; linarith
    have h := hB z (by rw [hR, hd] at hre; linarith [(abs_le.mp hre).1])
    have h1 : 1 + ‖z‖ ≤ X := by rw [hX]; linarith
    calc ‖fL f z‖ ≤ B * (1 + ‖z‖) ^ 2 := h
      _ ≤ B * X ^ 2 := by gcongr
      _ ≤ M := by rw [hM]; nlinarith [sq_nonneg X]
  have hJ := AnalyticOnNhd.sum_divisor_le (c := c) (r := r) (R := R) (M := M)
    (by rw [abs_of_pos hr0]; exact hr0)
    (by rw [abs_of_pos hr0, abs_of_pos (by linarith)]; exact hrR)
    hM1 (fun z _ => (fL_entire f hk1).analyticAt z) hc0 hbound
  -- divisor = ord on the small disc
  set U := closedBall c |r|
  set Dv := divisor (fL f) U
  have hfin := Dv.finiteSupport (isCompact_closedBall _ _)
  have hSball : ∀ u ∈ S, u ∈ U := by
    intro u hu
    obtain ⟨_, h1, h2, h3, h4⟩ := hS u hu
    have := mem_disc_of_rect (σ₁ := σ₁) (κ := κ) (T := T) hd1 h1 h2 h3 h4
    simpa [U, hr, hd, hc] using this
  have hLnt : ∀ u, analyticOrderAt (fL f) u ≠ ⊤ := by
    intro u h
    rw [AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero u
      (fun z => (fL_entire f hk1).analyticAt z)] at h
    exact hc0 (by rw [h]; rfl)
  have hDord : ∀ u ∈ S, Dv u = (ord f u : ℤ) := by
    intro u hu
    have hpos : 0 < u.re := by
      have := (hS u hu).2.1
      have : (0 : ℝ) < k / 2 := by positivity
      linarith
    rw [AnalyticOnNhd.divisor_apply (fun z _ => (fL_entire f hk1).analyticAt z) (hSball u hu)]
    unfold ord analyticOrderNatAt
    rw [order_Lam_eq_fL f hk1 (Or.inl hpos)]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hLnt u)
    rw [← hn, ENat.toNat_coe]
    rfl
  have hle : ((∑ u ∈ S, ord f u : ℕ) : ℤ) ≤ ∑ᶠ u, Dv u := by
    classical
    rw [finsum_eq_sum_of_support_subset (s := S ∪ hfin.toFinset) Dv
      (by intro x hx; simp [hx])]
    push_cast
    calc ∑ u ∈ S, (ord f u : ℤ) = ∑ u ∈ S, Dv u :=
          Finset.sum_congr rfl fun u hu => (hDord u hu).symm
      _ ≤ ∑ u ∈ S ∪ hfin.toFinset, Dv u :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
            fun u _ _ => AnalyticOnNhd.divisor_nonneg
              (fun z _ => (fL_entire f hk1).analyticAt z) u
  have hleR : ((∑ u ∈ S, ord f u : ℕ) : ℝ) ≤ ((∑ᶠ u, Dv u : ℤ) : ℝ) := by exact_mod_cast hle
  refine hleR.trans (hJ.trans ?_)
  -- arithmetic
  have hLT : Real.log 2 ≤ Real.log (|T| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg T])
  have hLcpos : 0 < ‖fL f c‖ := norm_pos_iff.2 hc0
  have h1 : Real.log (M / ‖fL f c‖) ≤ Real.log M - Real.log ℓ₀ := by
    rw [Real.log_div (by linarith) hLcpos.ne']
    linarith [Real.log_le_log hℓ₀pos hLc]
  have h2 : Real.log M = Real.log (B + 1) + 2 * Real.log X := by
    rw [hM, Real.log_mul (by linarith) (by positivity), Real.log_pow]; push_cast; ring
  have h3 : Real.log X ≤ Real.log (1 + σ₁) + Real.log (|T| + 2) := by
    rw [← Real.log_mul (by linarith) (by linarith [abs_nonneg T])]
    apply Real.log_le_log (by linarith)
    rw [hX]; nlinarith [abs_nonneg T]
  have hK : E ≤ |E| / Real.log 2 * Real.log (|T| + 2) := by
    have : |E| ≤ |E| / Real.log 2 * Real.log (|T| + 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hLT (abs_nonneg E)
    linarith [le_abs_self E]
  rw [hC, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hlam.le
  rw [hE] at hK
  nlinarith

/-! ### Windows -/

/-- **Zeros in unit windows, with multiplicity**, for every nonzero level-one cusp form. -/
theorem window_count (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, ∀ S : Finset ℂ, (↑S : Set ℂ) ⊆ zeroSet f T (T + 1) →
      ((∑ u ∈ S, ord f u : ℕ) : ℝ) ≤ C * Real.log (|T| + 2) := by
  classical
  have hk := weight_ge f hf
  have hk1 : 1 ≤ k := by omega
  obtain ⟨n₀, ha₀, hmin⟩ := exists_first f hf hk1
  obtain ⟨D, -⟩ := exists_normData f hk1 ha₀ hmin
  obtain ⟨C₀, hC₀, hW⟩ := window_right f hk D
  refine ⟨3 * C₀, by positivity, fun T S hS => ?_⟩
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hre_lt : ∀ u ∈ S, u.re < D.σ₁ := by
    intro u hu; by_contra h; push Not at h; exact D.Lam_ne_zero_right h (hS hu).1
  have hre_gt : ∀ u ∈ S, (k : ℝ) - D.σ₁ < u.re := by
    intro u hu; by_contra h; push Not at h; exact D.Lam_ne_zero_left hk1 h (hS hu).1
  set S₁ := S.filter (fun u => (k : ℝ) / 2 ≤ u.re)
  set S₂ := S.filter (fun u => ¬ (k : ℝ) / 2 ≤ u.re)
  have hsplit : ∑ u ∈ S, ord f u = ∑ u ∈ S₁, ord f u + ∑ u ∈ S₂, ord f u :=
    (Finset.sum_filter_add_sum_filter_not S _ _).symm
  have h1 : ((∑ u ∈ S₁, ord f u : ℕ) : ℝ) ≤ C₀ * Real.log (|T| + 2) := by
    apply hW T S₁
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨h0, h3, h4⟩ := hS hu.1
    exact ⟨h0, hu.2, (hre_lt u hu.1).le, h3.le, h4⟩
  set g : ℂ → ℂ := fun u => (k : ℂ) - u
  have hginj : Set.InjOn g S₂ := by
    intro x _ y _ h; simpa [g] using h
  have himg : ∑ u ∈ S₂.image g, ord f u = ∑ u ∈ S₂, ord f u := by
    rw [Finset.sum_image hginj]
    exact Finset.sum_congr rfl fun u _ => ord_reflect f hk1 u
  have h2 : ((∑ u ∈ S₂, ord f u : ℕ) : ℝ) ≤ C₀ * Real.log (|(-T - 1)| + 2) := by
    rw [← himg]
    apply hW (-T - 1) (S₂.image g)
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    rw [Finset.mem_filter] at hu
    obtain ⟨h0, h3, h4⟩ := hS hu.1
    have := hre_gt u hu.1
    refine ⟨Lam_reflect_zero f hk1 h0, ?_, ?_, ?_, ?_⟩ <;> simp [g] <;> push Not at hu <;>
      linarith [hu.2]
  have hlog : Real.log (|(-T - 1)| + 2) ≤ 2 * Real.log (|T| + 2) := by
    have hT2 : (2 : ℝ) ≤ |T| + 2 := by linarith [abs_nonneg T]
    have hab : |(-T - 1)| ≤ |T| + 1 := by
      rw [show -T - 1 = -(T + 1) by ring, abs_neg]
      exact (abs_add_le T 1).trans (by norm_num)
    have : Real.log (|(-T - 1)| + 2) ≤ Real.log 2 + Real.log (|T| + 2) := by
      rw [← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by positivity) (by linarith)
    linarith [Real.log_le_log (by norm_num) hT2]
  rw [hsplit]
  have := mul_le_mul_of_nonneg_left hlog hC₀
  have e : ((∑ u ∈ S₁, ord f u + ∑ u ∈ S₂, ord f u : ℕ) : ℝ) =
      ((∑ u ∈ S₁, ord f u : ℕ) : ℝ) + ((∑ u ∈ S₂, ord f u : ℕ) : ℝ) := by push_cast; ring
  rw [e]
  linarith

lemma card_le_sum_ord (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) (D : NormData f) (S : Finset ℂ)
    (hS : ∀ u ∈ S, heckeLambda f u = 0) : S.card ≤ ∑ u ∈ S, ord f u := by
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun u hu => one_le_ord f hk D (hS u hu)

lemma zeroSet_window_finite (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (T : ℝ) :
    (zeroSet f T (T + 1)).Finite := by
  have hk1 : 1 ≤ k := by have := weight_ge f hf; omega
  obtain ⟨n₀, ha₀, hmin⟩ := exists_first f hf hk1
  obtain ⟨D, -⟩ := exists_normData f hk1 ha₀ hmin
  obtain ⟨C, _, hC⟩ := window_count f hf
  by_contra h
  obtain ⟨S, hS, hcard⟩ :=
    Set.Infinite.exists_subset_card_eq h (⌈C * Real.log (|T| + 2)⌉₊ + 1)
  have h1 := hC T S hS
  have h2 : S.card ≤ ∑ u ∈ S, ord f u := card_le_sum_ord f hk1 D S fun u hu => (hS hu).1
  have h3 : ((S.card : ℕ) : ℝ) ≤ C * Real.log (|T| + 2) :=
    le_trans (by exact_mod_cast h2) h1
  rw [hcard] at h3
  push_cast at h3
  linarith [Nat.le_ceil (C * Real.log (|T| + 2))]

/-- Index of the unit window containing `u`. -/
noncomputable def winIdx (a : ℝ) (u : ℂ) : ℕ := ⌈u.im - a⌉₊ - 1

lemma winIdx_spec {a : ℝ} {u : ℂ} (h : a < u.im) :
    a + (winIdx a u : ℝ) < u.im ∧ u.im ≤ a + (winIdx a u : ℝ) + 1 := by
  have hpos : 0 < ⌈u.im - a⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have he : winIdx a u + 1 = ⌈u.im - a⌉₊ := by unfold winIdx; omega
  have hne : winIdx a u + 1 ≠ 0 := by omega
  have := (Nat.ceil_eq_iff hne).mp he.symm
  push_cast at this
  constructor <;> linarith [this.1, this.2]

lemma winIdx_lt {a b : ℝ} {u : ℂ} (h1 : a < u.im) (h2 : u.im ≤ b) :
    winIdx a u < ⌈b - a⌉₊ := by
  have hpos : 0 < ⌈u.im - a⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have hm : ⌈u.im - a⌉₊ ≤ ⌈b - a⌉₊ := Nat.ceil_mono (by linarith)
  unfold winIdx; omega

/-- Every `zeroSet f a b` is finite. -/
theorem zeroSet_finite (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (a b : ℝ) :
    (zeroSet f a b).Finite := by
  have hsub : zeroSet f a b ⊆ ⋃ j ∈ Set.Iio ⌈b - a⌉₊, zeroSet f (a + j) (a + j + 1) := by
    intro u hu
    obtain ⟨h0, h3, h4⟩ := hu
    obtain ⟨s1, s2⟩ := winIdx_spec h3
    exact Set.mem_biUnion (x := winIdx a u) (winIdx_lt h3 h4) ⟨h0, s1, s2⟩
  exact ((Set.finite_Iio (⌈b - a⌉₊ : ℕ)).biUnion fun (j : ℕ) _ =>
    zeroSet_window_finite f hf (a + j)).subset hsub

lemma zeroCountAB_eq (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) (a b : ℝ) :
    zeroCountAB f a b = ∑ u ∈ (zeroSet_finite f hf a b).toFinset, ord f u :=
  finsum_mem_eq_finite_toFinset_sum _ _

/-- Additivity `N(a,c) = N(a,b) + N(b,c)`. -/
theorem zeroCountAB_add (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) {a b c : ℝ} (hab : a ≤ b)
    (hbc : b ≤ c) : zeroCountAB f a c = zeroCountAB f a b + zeroCountAB f b c := by
  classical
  rw [zeroCountAB_eq f hf, zeroCountAB_eq f hf, zeroCountAB_eq f hf]
  have hU : (zeroSet_finite f hf a c).toFinset =
      (zeroSet_finite f hf a b).toFinset ∪ (zeroSet_finite f hf b c).toFinset := by
    ext u
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, zeroSet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h0, h3, h4⟩
      rcases le_or_gt u.im b with h | h
      · exact Or.inl ⟨h0, h3, h⟩
      · exact Or.inr ⟨h0, h, h4⟩
    · rintro (⟨h0, h3, h4⟩ | ⟨h0, h3, h4⟩)
      · exact ⟨h0, h3, by linarith⟩
      · exact ⟨h0, by linarith, h4⟩
  rw [hU, Finset.sum_union]
  rw [Finset.disjoint_left]
  intro u hu hu'
  simp only [Set.Finite.mem_toFinset, zeroSet, Set.mem_setOf_eq] at hu hu'
  linarith [hu.2.2, hu'.2.1]

/-- **`N_f(T+1) − N_f(T) ≪ log T`.** -/
theorem zeroCount_window (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) : ∃ C : ℝ, 0 ≤ C ∧
    (∀ T : ℝ, (zeroCountAB f T (T + 1) : ℝ) ≤ C * Real.log (|T| + 2)) ∧
    (∀ T : ℝ, 0 ≤ T → (zeroCount f (T + 1) : ℝ) - zeroCount f T ≤ C * Real.log (T + 2)) := by
  obtain ⟨C, hC0, hC⟩ := window_count f hf
  have hw : ∀ T : ℝ, (zeroCountAB f T (T + 1) : ℝ) ≤ C * Real.log (|T| + 2) := fun T => by
    rw [zeroCountAB_eq f hf]
    exact hC T _ (by intro u hu; exact (Set.Finite.mem_toFinset _).mp hu)
  refine ⟨C, hC0, hw, fun T hT => ?_⟩
  unfold zeroCount
  rw [zeroCountAB_add f hf hT (by linarith : T ≤ T + 1)]
  push_cast
  have := hw T
  rw [abs_of_nonneg hT] at this
  linarith

/-- **`N_f(T) ≪ T log T`**: `N_f(T) ≤ C (T+1) log(T+2)` for `T ≥ 0`. -/
theorem zeroCount_le (f : CuspForm 𝒮ℒ (k : ℤ)) (hf : f ≠ 0) : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
    (zeroCount f T : ℝ) ≤ C * (T + 1) * Real.log (T + 2) := by
  classical
  obtain ⟨C, hC0, hC⟩ := window_count f hf
  refine ⟨C, hC0, fun T hT => ?_⟩
  unfold zeroCount
  rw [zeroCountAB_eq f hf]
  set S := (zeroSet_finite f hf 0 T).toFinset
  have hS : ∀ u ∈ S, u ∈ zeroSet f 0 T := fun u hu => (Set.Finite.mem_toFinset _).mp hu
  set n := ⌈T - 0⌉₊ with hn
  have hmaps : ∀ u ∈ S, winIdx 0 u ∈ Finset.range n := by
    intro u hu
    obtain ⟨_, h3, h4⟩ := hS u hu
    exact Finset.mem_range.mpr (winIdx_lt h3 h4)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  push_cast
  have hlogT : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
  have hfib : ∀ j ∈ Finset.range n,
      (∑ u ∈ S with winIdx 0 u = j, (ord f u : ℝ)) ≤ C * Real.log (T + 2) := by
    intro j hj
    have hjT : (j : ℝ) < T := by
      have := Finset.mem_range.mp hj
      rw [hn, sub_zero] at this
      exact (Nat.lt_ceil).mp this
    have hsub : (↑(S.filter (fun u => winIdx 0 u = j)) : Set ℂ) ⊆ zeroSet f j (j + 1) := by
      intro u hu
      rw [Finset.coe_filter] at hu
      obtain ⟨hu, hj'⟩ := hu
      obtain ⟨h0, h3, _⟩ := hS u hu
      obtain ⟨s1, s2⟩ := winIdx_spec h3
      rw [hj', zero_add] at s1 s2
      exact ⟨h0, s1, s2⟩
    have := hC j _ hsub
    push_cast at this
    rw [abs_of_nonneg (Nat.cast_nonneg j)] at this
    refine this.trans ?_
    gcongr
  refine (Finset.sum_le_sum hfib).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn1 : (n : ℝ) ≤ T + 1 := by
    rw [hn, sub_zero]; exact (Nat.ceil_lt_add_one hT).le
  have : 0 ≤ C * Real.log (T + 2) := mul_nonneg hC0 hlogT
  nlinarith

/-! ### `N_f` counts the zeros of `L(f,s)` -/

/-- For `0 ≤ a`, `zeroSet f a b` is the set of zeros of `L(f,s)` with `a < Im ≤ b`. -/
theorem zeroSet_eq_fL (f : CuspForm 𝒮ℒ (k : ℤ)) {a b : ℝ} (ha : 0 ≤ a) :
    zeroSet f a b = {u : ℂ | fL f u = 0 ∧ a < u.im ∧ u.im ≤ b} := by
  ext u
  have hg : ∀ (h : a < u.im), u ∈ goodSet := fun h => Or.inr (by
    show u.im ≠ 0; linarith)
  constructor
  · rintro ⟨h0, h3, h4⟩; exact ⟨(Lam_zero_iff_fL f (hg h3)).mp h0, h3, h4⟩
  · rintro ⟨h0, h3, h4⟩; exact ⟨(Lam_zero_iff_fL f (hg h3)).mpr h0, h3, h4⟩

/-- Off the real axis, `ord f u` is the order of `u` as a zero of `L(f,s)`. -/
theorem ord_eq_fL (f : CuspForm 𝒮ℒ (k : ℤ)) (hk : 1 ≤ k) {u : ℂ} (hu : u.im ≠ 0) :
    ord f u = analyticOrderNatAt (fL f) u := by
  unfold ord analyticOrderNatAt; rw [order_Lam_eq_fL f hk (Or.inr hu)]

end RamanujanTau.GeneralZeros
