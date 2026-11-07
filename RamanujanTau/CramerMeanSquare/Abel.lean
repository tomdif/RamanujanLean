/-
# A parametric Abelian lemma

`abel_param`: let `f_η ≥ 0` be continuous (`η > 0` a parameter), `a > 0`, `c_η → c₀` as
`η → 0⁺`, and suppose that for every `ε > 0` there is `D ≥ 0` with, for all small `η`,

    |∫_a^T f_η − c_η T| ≤ ε T + D        (T ≥ a).

Then `η ∫_a^∞ t^{−1−η} f_η(t) dt → c₀` as `η → 0⁺`.

The point is the uniformity in `η`: the mean-value hypothesis is required uniformly in the
parameter, which is exactly what the uniform Carlson–Potter theorem (`Unif.lean`) gives.

Proof: integration by parts `∫_a^T t^{−1−η} f = T^{−1−η} G(T) + (1+η) ∫_a^T t^{−2−η} G`,
`G(T) = ∫_a^T f`, the two-sided bound on `G`, explicit power integrals, and `T → ∞`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.CramerMeanSquare

open Real Filter Topology MeasureTheory Set

lemma pos_of_mem_uIcc {a T x : ℝ} (ha : 0 < a) (haT : a ≤ T) (hx : x ∈ uIcc a T) : 0 < x := by
  rw [uIcc_of_le haT] at hx; exact lt_of_lt_of_le ha hx.1

/-- Integration by parts with the weight `t^{−1−η}`. -/
lemma ibp_weight {f : ℝ → ℝ} (hf : Continuous f) {a η T : ℝ} (ha : 0 < a) (haT : a ≤ T) :
    ∫ t in a..T, t ^ (-1 - η) * f t =
      T ^ (-1 - η) * (∫ t in a..T, f t) +
        (1 + η) * ∫ t in a..T, t ^ (-2 - η) * (∫ s in a..t, f s) := by
  have hpos := fun x (hx : x ∈ uIcc a T) => pos_of_mem_uIcc ha haT hx
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := T)
    (u := fun x : ℝ => x ^ (-1 - η)) (u' := fun x => (-1 - η) * x ^ (-1 - η - 1))
    (v := fun x => ∫ s in a..x, f s) (v' := f)
    (fun x hx => Real.hasDerivAt_rpow_const (Or.inl (hpos x hx).ne'))
    (fun x _ => (hf.integral_hasStrictDerivAt a x).hasDerivAt)
    (ContinuousOn.intervalIntegrable (continuousOn_const.mul (fun x hx =>
      (Real.continuousAt_rpow_const x _ (Or.inl (hpos x hx).ne')).continuousWithinAt)))
    (hf.intervalIntegrable a T)
  simp only [intervalIntegral.integral_same, mul_zero, sub_zero] at hibp
  rw [hibp]
  have e : ∫ x in a..T, (-1 - η) * x ^ (-1 - η - 1) * ∫ s in a..x, f s =
      -((1 + η) * ∫ x in a..T, x ^ (-2 - η) * ∫ s in a..x, f s) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [show -1 - η - 1 = -2 - η by ring]; ring
  rw [e]; ring

lemma integral_rpow_aT {a T r : ℝ} (ha : 0 < a) (haT : a ≤ T) (hr : r ≠ -1) :
    ∫ t in a..T, t ^ r = (T ^ (r + 1) - a ^ (r + 1)) / (r + 1) := by
  refine integral_rpow (Or.inr ⟨hr, ?_⟩)
  intro h0
  have := pos_of_mem_uIcc ha haT h0
  exact lt_irrefl _ this

/-- Explicit form of `∫_a^T t^{−2−η}((κ)t + D)`. -/
lemma integral_lin_weight {a T η κ D : ℝ} (ha : 0 < a) (haT : a ≤ T) (hη : 0 < η) :
    ∫ t in a..T, t ^ (-2 - η) * (κ * t + D) =
      κ * ((T ^ (-η) - a ^ (-η)) / (-η)) + D * ((T ^ (-1 - η) - a ^ (-1 - η)) / (-1 - η)) := by
  have hpos := fun x (hx : x ∈ uIcc a T) => pos_of_mem_uIcc ha haT hx
  have e : ∀ x ∈ uIcc a T, x ^ (-2 - η) * (κ * x + D) = κ * x ^ (-1 - η) + D * x ^ (-2 - η) := by
    intro x hx
    have hx0 := hpos x hx
    have : x ^ (-1 - η) = x ^ (-2 - η) * x := by
      rw [← Real.rpow_add_one hx0.ne']; congr 1; ring
    rw [this]; ring
  have hc1 : ContinuousOn (fun x : ℝ => x ^ (-1 - η)) (uIcc a T) := fun x hx =>
    (Real.continuousAt_rpow_const x _ (Or.inl (hpos x hx).ne')).continuousWithinAt
  have hc2 : ContinuousOn (fun x : ℝ => x ^ (-2 - η)) (uIcc a T) := fun x hx =>
    (Real.continuousAt_rpow_const x _ (Or.inl (hpos x hx).ne')).continuousWithinAt
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_add
    ((hc1.intervalIntegrable).const_mul κ) ((hc2.intervalIntegrable).const_mul D),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_rpow_aT ha haT (by linarith), integral_rpow_aT ha haT (by linarith)]
  congr 2 <;> ring_nf

/-- **Bounds for a single parameter.** -/
lemma abel_bounds {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t) {a η c ε D : ℝ}
    (ha : 0 < a) (hη : 0 < η) (_hD : 0 ≤ D)
    (hG : ∀ T, a ≤ T → |(∫ t in a..T, f t) - c * T| ≤ ε * T + D) :
    IntegrableOn (fun t => t ^ (-1 - η) * f t) (Ioi a) ∧
      η * ∫ t in Ioi a, t ^ (-1 - η) * f t ≤ (1 + η) * (c + ε) * a ^ (-η) + η * D * a ^ (-1 - η) ∧
      (1 + η) * (c - ε) * a ^ (-η) - η * D * a ^ (-1 - η) ≤ η * ∫ t in Ioi a, t ^ (-1 - η) * f t := by
  set G : ℝ → ℝ := fun T => ∫ t in a..T, f t with hGdef
  have hGc : Continuous G := intervalIntegral.continuous_primitive
    (fun x y => hf.intervalIntegrable x y) a
  have hGup : ∀ t, a ≤ t → G t ≤ (c + ε) * t + D := fun t ht => by
    have := (abs_le.1 (hG t ht)).2; simp only [hGdef]; linarith
  have hGlo : ∀ t, a ≤ t → (c - ε) * t - D ≤ G t := fun t ht => by
    have := (abs_le.1 (hG t ht)).1; simp only [hGdef]; linarith
  have hG0 : ∀ t, a ≤ t → 0 ≤ G t := fun t ht =>
    intervalIntegral.integral_nonneg ht fun s _ => hf0 s
  -- the weighted integral on `[a,T]`
  set J : ℝ → ℝ := fun T => ∫ t in a..T, t ^ (-1 - η) * f t with hJ
  set P1 : ℝ → ℝ := fun T => (T ^ (-η) - a ^ (-η)) / (-η) with hP1
  set P2 : ℝ → ℝ := fun T => (T ^ (-1 - η) - a ^ (-1 - η)) / (-1 - η) with hP2
  have hcW : ∀ T, a ≤ T → ContinuousOn (fun x : ℝ => x ^ (-2 - η)) (uIcc a T) :=
    fun T haT x hx => (Real.continuousAt_rpow_const x _
      (Or.inl (pos_of_mem_uIcc ha haT hx).ne')).continuousWithinAt
  have hWint : ∀ T, a ≤ T → IntervalIntegrable (fun t => t ^ (-2 - η) * G t) volume a T :=
    fun T haT => ((hcW T haT).mul hGc.continuousOn).intervalIntegrable
  have hLint : ∀ T, a ≤ T → ∀ κ D' : ℝ,
      IntervalIntegrable (fun t => t ^ (-2 - η) * (κ * t + D')) volume a T :=
    fun T haT κ D' => ((hcW T haT).mul (by fun_prop)).intervalIntegrable
  have hupT : ∀ T, a ≤ T → η * J T ≤
      η * (T ^ (-1 - η) * ((c + ε) * T + D)) + η * (1 + η) * ((c + ε) * P1 T + D * P2 T) := by
    intro T haT
    have hT0 : 0 < T := lt_of_lt_of_le ha haT
    have hibp := ibp_weight hf (η := η) ha haT
    have hW : ∫ t in a..T, t ^ (-2 - η) * G t ≤ ∫ t in a..T, t ^ (-2 - η) * ((c + ε) * t + D) :=
      intervalIntegral.integral_mono_on haT (hWint T haT) (hLint T haT _ _) fun t ht => by
        have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
        exact mul_le_mul_of_nonneg_left (hGup t ht.1) (Real.rpow_pos_of_pos ht0 _).le
    rw [integral_lin_weight ha haT hη] at hW
    have hb : T ^ (-1 - η) * G T ≤ T ^ (-1 - η) * ((c + ε) * T + D) :=
      mul_le_mul_of_nonneg_left (hGup T haT) (Real.rpow_pos_of_pos hT0 _).le
    simp only [hJ]
    rw [hibp]
    have h1η : 0 ≤ 1 + η := by linarith
    have := mul_le_mul_of_nonneg_left hW h1η
    simp only [hGdef, hP1, hP2] at hb this ⊢
    nlinarith
  have hloT : ∀ T, a ≤ T → η * (1 + η) * ((c - ε) * P1 T + (-D) * P2 T) ≤ η * J T := by
    intro T haT
    have hT0 : 0 < T := lt_of_lt_of_le ha haT
    have hibp := ibp_weight hf (η := η) ha haT
    have hW : ∫ t in a..T, t ^ (-2 - η) * ((c - ε) * t + (-D)) ≤ ∫ t in a..T, t ^ (-2 - η) * G t :=
      intervalIntegral.integral_mono_on haT (hLint T haT _ _) (hWint T haT) fun t ht => by
        have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
        have := hGlo t ht.1
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_pos_of_pos ht0 _).le
    rw [integral_lin_weight ha haT hη] at hW
    have hb : 0 ≤ T ^ (-1 - η) * G T :=
      mul_nonneg (Real.rpow_pos_of_pos hT0 _).le (hG0 T haT)
    simp only [hJ]
    rw [hibp]
    have h1η : 0 ≤ 1 + η := by linarith
    have := mul_le_mul_of_nonneg_left hW h1η
    simp only [hGdef, hP1, hP2] at hb this ⊢
    nlinarith
  -- limits of the explicit bounds
  have hT1 : Tendsto (fun T : ℝ => T ^ (-η)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hη
  have hT2 : Tendsto (fun T : ℝ => T ^ (-1 - η)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (y := 1 + η) (by linarith)
    simpa [show -(1 + η) = -1 - η by ring] using this
  have hP1l : Tendsto P1 atTop (𝓝 ((0 - a ^ (-η)) / (-η))) :=
    (hT1.sub tendsto_const_nhds).div_const _
  have hP2l : Tendsto P2 atTop (𝓝 ((0 - a ^ (-1 - η)) / (-1 - η))) :=
    (hT2.sub tendsto_const_nhds).div_const _
  have hbd : Tendsto (fun T : ℝ => η * (T ^ (-1 - η) * ((c + ε) * T + D))) atTop (𝓝 0) := by
    have h := ((hT1.const_mul (c + ε)).add (hT2.const_mul D)).const_mul η
    rw [mul_zero, mul_zero, add_zero, mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    have : T ^ (-η) = T ^ (-1 - η) * T := by
      rw [← Real.rpow_add_one hT.ne']; congr 1; ring
    rw [this]; ring
  have hUl : Tendsto (fun T => η * (T ^ (-1 - η) * ((c + ε) * T + D)) +
      η * (1 + η) * ((c + ε) * P1 T + D * P2 T)) atTop
      (𝓝 ((1 + η) * (c + ε) * a ^ (-η) + η * D * a ^ (-1 - η))) := by
    have h := hbd.add ((((hP1l.const_mul (c + ε)).add (hP2l.const_mul D))).const_mul (η * (1 + η)))
    convert h using 2
    have h1 : (1 : ℝ) + η ≠ 0 := by linarith
    have h2 : (-1 : ℝ) - η ≠ 0 := by linarith
    have h3 : η ≠ 0 := hη.ne'
    field_simp
    ring
  have hLl : Tendsto (fun T => η * (1 + η) * ((c - ε) * P1 T + (-D) * P2 T)) atTop
      (𝓝 ((1 + η) * (c - ε) * a ^ (-η) - η * D * a ^ (-1 - η))) := by
    have h := (((hP1l.const_mul (c - ε)).add (hP2l.const_mul (-D)))).const_mul (η * (1 + η))
    convert h using 2
    have h1 : (1 : ℝ) + η ≠ 0 := by linarith
    have h2 : (-1 : ℝ) - η ≠ 0 := by linarith
    have h3 : η ≠ 0 := hη.ne'
    field_simp
    ring
  -- integrability
  have hint : IntegrableOn (fun t => t ^ (-1 - η) * f t) (Ioi a) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
      (((1 + η) * (c + ε) * a ^ (-η) + η * D * a ^ (-1 - η)) / η + 1) a
      (l := atTop) (b := id) (fun T => ?_) tendsto_id ?_
    · show IntegrableOn _ (Ioc a T)
      rcases le_or_gt T a with h | h
      · rw [Ioc_eq_empty (not_lt.2 h)]; exact integrableOn_empty
      · have hc : ContinuousOn (fun t : ℝ => t ^ (-1 - η) * f t) (Icc a T) := fun x hx =>
          ((Real.continuousAt_rpow_const x _ (Or.inl (lt_of_lt_of_le ha hx.1).ne')).mul
            hf.continuousAt).continuousWithinAt
        exact (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    · have hev := (hUl.div_const η).eventually
        (gt_mem_nhds (lt_add_one (((1 + η) * (c + ε) * a ^ (-η) + η * D * a ^ (-1 - η)) / η)))
      filter_upwards [hev, eventually_ge_atTop a] with T hT haT
      have e : ∫ x in a..id T, ‖x ^ (-1 - η) * f x‖ = J T := by
        refine intervalIntegral.integral_congr fun x hx => ?_
        have hx0 := pos_of_mem_uIcc ha haT hx
        rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos hx0 _).le (hf0 x))]
      rw [e]
      have h1 := hupT T haT
      have h2 : J T ≤ (η * (T ^ (-1 - η) * ((c + ε) * T + D)) +
          η * (1 + η) * ((c + ε) * P1 T + D * P2 T)) / η := by
        rw [le_div_iff₀ hη]; linarith
      linarith
  have hJl : Tendsto (fun T => η * J T) atTop
      (𝓝 (η * ∫ t in Ioi a, t ^ (-1 - η) * f t)) :=
    (intervalIntegral_tendsto_integral_Ioi a hint tendsto_id).const_mul η
  refine ⟨hint, ?_, ?_⟩
  · refine le_of_tendsto_of_tendsto hJl hUl ?_
    filter_upwards [eventually_ge_atTop a] with T hT using hupT T hT
  · refine le_of_tendsto_of_tendsto hLl hJl ?_
    filter_upwards [eventually_ge_atTop a] with T hT using hloT T hT

lemma tendsto_rpow_const_base {a : ℝ} (ha : 0 < a) (k : ℝ) :
    Tendsto (fun η : ℝ => a ^ (k * η)) (𝓝[>] 0) (𝓝 1) := by
  have h : Continuous fun η : ℝ => a ^ (k * η) :=
    (Real.continuous_const_rpow ha.ne').comp (continuous_const.mul continuous_id) |>.congr
      fun _ => rfl
  have := h.tendsto 0
  simp only [mul_zero, Real.rpow_zero] at this
  exact tendsto_nhdsWithin_of_tendsto_nhds this

/-- **Parametric Abelian lemma.** -/
theorem abel_param {f : ℝ → ℝ → ℝ} {c : ℝ → ℝ} {c0 a : ℝ} (ha : 0 < a)
    (hf : ∀ η, Continuous (f η)) (hf0 : ∀ η t, 0 ≤ f η t)
    (hc : Tendsto c (𝓝[>] 0) (𝓝 c0))
    (hG : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ T, a ≤ T →
      |(∫ t in a..T, f η t) - c η * T| ≤ ε * T + D) :
    Tendsto (fun η => η * ∫ t in Ioi a, t ^ (-1 - η) * f η t) (𝓝[>] 0) (𝓝 c0) := by
  have hpos : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η := self_mem_nhdsWithin
  have hη0 : Tendsto (fun η : ℝ => η) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto 0)
  have ha1 : Tendsto (fun η : ℝ => a ^ (-η)) (𝓝[>] 0) (𝓝 1) := by
    simpa [neg_one_mul] using tendsto_rpow_const_base ha (-1)
  have ha2 : Tendsto (fun η : ℝ => a ^ (-1 - η)) (𝓝[>] 0) (𝓝 (a ^ (-1 : ℝ))) := by
    have h : Continuous fun η : ℝ => a ^ (-1 - η) :=
      (Real.continuous_const_rpow ha.ne').comp (continuous_const.sub continuous_id)
    have := h.tendsto 0
    simp only [sub_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  -- the two explicit bounds tend to `c₀ ± ε`
  have hlim : ∀ (s D : ℝ), Tendsto (fun η => (1 + η) * (c η + s) * a ^ (-η) + s * η * D * a ^ (-1 - η))
      (𝓝[>] 0) (𝓝 (c0 + s)) := by
    intro s D
    have h := ((((tendsto_const_nhds (x := (1:ℝ))).add hη0).mul
      (hc.add (tendsto_const_nhds (x := s)))).mul ha1).add
      ((((tendsto_const_nhds (x := s)).mul hη0).mul (tendsto_const_nhds (x := D))).mul ha2)
    simpa using h
  rw [tendsto_order]
  constructor
  · intro l hl
    set ε := (c0 - l) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    obtain ⟨D, hD, hev⟩ := hG ε hε0
    have h := hlim (-ε) (D / ε)
    have hl' : l < c0 + -ε := by rw [hε]; linarith
    filter_upwards [h.eventually (lt_mem_nhds hl'), hev, hpos] with η h1 h2 h3
    have hb := (abel_bounds (hf η) (hf0 η) ha h3 hD h2).2.2
    have e : -ε * η * (D / ε) * a ^ (-1 - η) = -(η * D * a ^ (-1 - η)) := by
      field_simp
    have e2 : (1 + η) * (c η + -ε) * a ^ (-η) = (1 + η) * (c η - ε) * a ^ (-η) := by ring
    rw [e, e2] at h1
    linarith
  · intro u hu
    set ε := (u - c0) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    obtain ⟨D, hD, hev⟩ := hG ε hε0
    have h := hlim ε (D / ε)
    have hu' : c0 + ε < u := by rw [hε]; linarith
    filter_upwards [h.eventually (gt_mem_nhds hu'), hev, hpos] with η h1 h2 h3
    have hb := (abel_bounds (hf η) (hf0 η) ha h3 hD h2).2.1
    have e : ε * η * (D / ε) * a ^ (-1 - η) = η * D * a ^ (-1 - η) := by
      field_simp
    rw [e] at h1
    linarith

end RamanujanTau.CramerMeanSquare
