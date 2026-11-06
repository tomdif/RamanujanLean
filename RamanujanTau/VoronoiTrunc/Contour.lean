/-
# From the vertical line to the steepest-descent path

For `c > 0` the vertical line integral `(1/2π) ∫_ℝ f(c+iu) du` of
`f(v) = v^{−(ν+1)} e^{L(v−1/v)}` equals `I_ν(L) = Im A_ν(L)/π` (`lineInt_eq_Ik`).

Proof: on `u ≥ 0` the region between the line `Re v = c` and the path `v(u) = (1−u)+ui`
is swept by the horizontal segments `[c+iu, v(u)]`.  With `F(u) = ∫_{[c+iu, v(u)]} f`,
`F' = f(v(u))(−1+i) − i f(c+iu)` (a primitive of `f` on a large disc in the upper half-plane,
`DifferentiableOn.isExactOn_ball`), `F(T) → 0`, and `F(0)` is real.  The half `u ≤ 0` is the
complex conjugate (`f(v̄) = conj f(v)`).
-/
import RamanujanTau.VoronoiTrunc.Kernel
import Mathlib.Analysis.Complex.HasPrimitives

set_option autoImplicit false

namespace RamanujanTau.VoronoiTrunc

open Complex Real MeasureTheory Set Filter Topology Metric ComplexConjugate

lemma differentiableAt_fk (ν : ℕ) (L : ℝ) {v : ℂ} (hv : v ≠ 0) : DifferentiableAt ℂ (fk ν L) v := by
  unfold fk
  refine ((differentiableAt_id.pow _).inv (pow_ne_zero _ hv)).mul ?_
  exact (differentiableAt_const _ |>.mul (differentiableAt_id.sub (differentiableAt_id.inv hv))).cexp

lemma continuousAt_fk (ν : ℕ) (L : ℝ) {v : ℂ} (hv : v ≠ 0) : ContinuousAt (fk ν L) v :=
  (differentiableAt_fk ν L hv).continuousAt

lemma fk_conj (ν : ℕ) (L : ℝ) (v : ℂ) : fk ν L (conj v) = conj (fk ν L v) := by
  unfold fk
  rw [map_mul, map_inv₀, map_pow, ← Complex.exp_conj, map_mul, map_sub, map_inv₀, Complex.conj_ofReal]

lemma fk_ofReal_im (ν : ℕ) (L : ℝ) (x : ℝ) : (fk ν L x).im = 0 := by
  have : fk ν L x = (((x ^ (ν + 1))⁻¹ * Real.exp (L * (x - x⁻¹)) : ℝ) : ℂ) := by
    unfold fk; push_cast; rfl
  rw [this, Complex.ofReal_im]

/-- `‖f(c+iu)‖ ≤ e^{Lc} / (κ (1+u²))`. -/
lemma norm_fk_line_le {ν : ℕ} (hν : 1 ≤ ν) {L : ℝ} (hL : 0 ≤ L) {c : ℝ} (hc : 0 < c) (u : ℝ) :
    ‖fk ν L ((c : ℂ) + u * I)‖ ≤
      Real.exp (L * c) / (c ^ (ν - 1) * min (c ^ 2) 1) * (1 + u ^ 2)⁻¹ := by
  set v : ℂ := (c : ℂ) + u * I with hv
  have hvre : v.re = c := by simp [hv]
  have hvim : v.im = u := by simp [hv]
  have hsq : ‖v‖ ^ 2 = c ^ 2 + u ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hvre, hvim]; ring
  have hcv : c ≤ ‖v‖ := by rw [← hvre]; exact (le_abs_self _).trans (abs_re_le_norm v)
  have hv0 : 0 < ‖v‖ := lt_of_lt_of_le hc hcv
  rw [norm_fk]
  have hre : (v - v⁻¹).re ≤ c := by
    rw [sub_re, inv_re, hvre]
    have : 0 ≤ c / Complex.normSq v := div_nonneg hc.le (Complex.normSq_nonneg _)
    linarith
  have he : Real.exp (L * (v - v⁻¹).re) ≤ Real.exp (L * c) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hre hL)
  have hm : 0 < min (c ^ 2) 1 := lt_min (by positivity) one_pos
  have hmin : min (c ^ 2) 1 * (1 + u ^ 2) ≤ ‖v‖ ^ 2 := by
    rw [hsq]
    have h1 := min_le_left (c ^ 2) 1
    have h2 := min_le_right (c ^ 2) 1
    nlinarith [sq_nonneg u]
  have hpow : c ^ (ν - 1) * min (c ^ 2) 1 * (1 + u ^ 2) ≤ ‖v‖ ^ (ν + 1) := by
    have : ‖v‖ ^ (ν + 1) = ‖v‖ ^ (ν - 1) * ‖v‖ ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [this, mul_assoc]
    exact mul_le_mul (pow_le_pow_left₀ hc.le hcv _) hmin (by positivity) (by positivity)
  have hd : 0 < c ^ (ν - 1) * min (c ^ 2) 1 * (1 + u ^ 2) := by positivity
  calc (‖v‖ ^ (ν + 1))⁻¹ * Real.exp (L * (v - v⁻¹).re)
      ≤ (c ^ (ν - 1) * min (c ^ 2) 1 * (1 + u ^ 2))⁻¹ * Real.exp (L * c) := by
        gcongr
    _ = _ := by field_simp

lemma continuous_fk_line (ν : ℕ) (L : ℝ) {c : ℝ} (hc : 0 < c) :
    Continuous fun u : ℝ => fk ν L ((c : ℂ) + u * I) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hne : (c : ℂ) + u * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  exact ContinuousAt.comp (g := fk ν L) (continuousAt_fk ν L hne)
    (by fun_prop : ContinuousAt (fun u : ℝ => (c : ℂ) + u * I) u)

lemma integrable_fk_line {ν : ℕ} (hν : 1 ≤ ν) {L : ℝ} (hL : 0 ≤ L) {c : ℝ} (hc : 0 < c) :
    Integrable fun u : ℝ => fk ν L ((c : ℂ) + u * I) := by
  refine Integrable.mono'
    (integrable_inv_one_add_sq.const_mul (Real.exp (L * c) / (c ^ (ν - 1) * min (c ^ 2) 1)))
    (continuous_fk_line ν L hc).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  exact norm_fk_line_le hν hL hc u

/-- A large disc in the upper half-plane containing a given rectangle. -/
lemma exists_ball_sub {u0 T A : ℝ} (hu0 : 0 < u0) (hT : u0 ≤ T) (hA : 0 ≤ A) :
    ∃ c0 : ℂ, ∃ r : ℝ, ball c0 r ⊆ {v : ℂ | 0 < v.im} ∧
      ∀ v : ℂ, |v.re| ≤ A → u0 ≤ v.im → v.im ≤ T → v ∈ ball c0 r := by
  set R : ℝ := T + (A ^ 2 + 1) / u0 + u0 with hR
  have hR1 : (A ^ 2 + 1) / u0 * u0 = A ^ 2 + 1 := by field_simp
  have hRT : T ≤ R := by have : 0 ≤ (A ^ 2 + 1) / u0 := by positivity
                         linarith
  refine ⟨(R : ℂ) * I, R - u0 / 2, ?_, ?_⟩
  · intro v hv
    rw [mem_ball, Complex.dist_eq] at hv
    have h1 : |v.im - R| ≤ ‖v - R * I‖ := by
      have := abs_im_le_norm (v - R * I); simpa using this
    simp only [mem_setOf_eq]
    have := abs_lt.1 (lt_of_le_of_lt h1 hv)
    linarith
  · intro v hre him1 him2
    rw [mem_ball, Complex.dist_eq]
    have hpos : 0 < R - u0 / 2 := by linarith
    have hsq : ‖v - R * I‖ ^ 2 = v.re ^ 2 + (v.im - R) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    refine (pow_lt_pow_iff_left₀ (norm_nonneg _) hpos.le (two_ne_zero)).1 ?_
    rw [hsq]
    have hre2 : v.re ^ 2 ≤ A ^ 2 := by
      have := sq_abs v.re ▸ (pow_le_pow_left₀ (abs_nonneg _) hre 2); linarith
    have him : (v.im - R) ^ 2 ≤ (R - u0) ^ 2 := by nlinarith
    have hkey : A ^ 2 + 1 + u0 ^ 2 ≤ u0 * R := by
      rw [hR]; nlinarith [hR1]
    nlinarith

/-- The horizontal segment integral `F(u) = ∫_{[c+iu, v(u)]} f`. -/
noncomputable def Fs (ν : ℕ) (L c u : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, ((1 - u - c : ℝ) : ℂ) * fk ν L ((c : ℂ) + t * ((1 - u - c : ℝ) : ℂ) + u * I)

lemma seg_pt_ne_zero {c : ℝ} (hc : 0 < c) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (u : ℝ) :
    (c : ℂ) + t * ((1 - u - c : ℝ) : ℂ) + u * I ≠ 0 := by
  intro h
  have h1 := congrArg Complex.im h
  have h2 := congrArg Complex.re h
  simp at h1 h2
  rw [h1] at h2
  nlinarith [mul_nonneg hc.le (sub_nonneg.2 ht1)]

lemma graph_finite {ν : ℕ} (L : ℝ) {c u0 T : ℝ} (hc : 0 < c) (hu0 : 0 < u0) (hT : u0 ≤ T) :
    ∫ u in u0..T, (Gk ν L u - I * fk ν L ((c : ℂ) + u * I)) = Fs ν L c T - Fs ν L c u0 := by
  obtain ⟨c0, r, hsub, hmem⟩ := exists_ball_sub (A := 2 * c + T + 1) hu0 hT (by linarith)
  have hdiff : DifferentiableOn ℂ (fk ν L) (ball c0 r) := by
    intro v hv
    have : 0 < v.im := hsub hv
    have hv0 : v ≠ 0 := by intro h; rw [h] at this; simp at this
    exact (differentiableAt_fk ν L hv0).differentiableWithinAt
  obtain ⟨Φ, hΦ⟩ := hdiff.isExactOn_ball
  -- points of the segments lie in the ball
  have hp : ∀ u ∈ Icc u0 T, ∀ t ∈ Icc (0 : ℝ) 1,
      (c : ℂ) + t * ((1 - u - c : ℝ) : ℂ) + u * I ∈ ball c0 r := by
    intro u hu t ht
    apply hmem
    · simp
      rw [abs_le]
      constructor <;> nlinarith [hu.1, hu.2, ht.1, ht.2, mul_nonneg ht.1 (by linarith [hu.1] : (0:ℝ) ≤ u)]
    · simp; exact hu.1
    · simp; exact hu.2
  have hpv : ∀ u : ℝ, pv u = (c : ℂ) + (1 : ℝ) * ((1 - u - c : ℝ) : ℂ) + u * I := by
    intro u; unfold pv; push_cast; ring
  have hF : ∀ u ∈ Icc u0 T, Fs ν L c u = Φ (pv u) - Φ ((c : ℂ) + u * I) := by
    intro u hu
    unfold Fs
    have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt
        (fun t : ℝ => Φ ((c : ℂ) + t * ((1 - u - c : ℝ) : ℂ) + u * I))
        (((1 - u - c : ℝ) : ℂ) * fk ν L ((c : ℂ) + t * ((1 - u - c : ℝ) : ℂ) + u * I)) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have h1 : HasDerivAt (fun t : ℝ => (c : ℂ) + t * ((1 - u - c : ℝ) : ℂ) + u * I)
          ((1 - u - c : ℝ) : ℂ) t := by
        have := ((hasDerivAt_id t).ofReal_comp).mul_const ((1 - u - c : ℝ) : ℂ)
        simpa using (this.const_add (c : ℂ)).add_const ((u : ℂ) * I)
      have h2 := (hΦ _ (hp u hu t ht)).comp t h1
      exact h2.congr_deriv (mul_comm _ _)
    have hint : IntervalIntegrable (fun t : ℝ => ((1 - u - c : ℝ) : ℂ) *
        fk ν L ((c : ℂ) + t * ((1 - u - c : ℝ) : ℂ) + u * I)) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le zero_le_one]
      intro t ht
      exact (continuousAt_const.mul (ContinuousAt.comp (g := fk ν L)
        (f := fun t : ℝ => (c : ℂ) + t * ((1 - u - c : ℝ) : ℂ) + u * I) (x := t)
        (continuousAt_fk ν L (seg_pt_ne_zero hc ht.1 ht.2 u))
        (by fun_prop : ContinuousAt (fun t : ℝ => (c : ℂ) + t * ((1 - u - c : ℝ) : ℂ) + u * I) t))).continuousWithinAt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint, hpv]
    simp
  have hderiv : ∀ u ∈ uIcc u0 T, HasDerivAt (fun u : ℝ => Φ (pv u) - Φ ((c : ℂ) + u * I))
      (Gk ν L u - I * fk ν L ((c : ℂ) + u * I)) u := by
    intro u hu
    rw [uIcc_of_le hT] at hu
    have hpvd : HasDerivAt pv (-1 + I) u := by
      unfold pv
      have h1 := ((hasDerivAt_id u).ofReal_comp)
      have h2 : HasDerivAt (fun u : ℝ => (((1 - u : ℝ)) : ℂ)) (-1) u := by
        have := ((hasDerivAt_id u).const_sub 1).ofReal_comp
        simpa using this
      have := h2.add (h1.mul_const I)
      simpa using this
    have hld : HasDerivAt (fun u : ℝ => (c : ℂ) + u * I) I u := by
      have := ((hasDerivAt_id u).ofReal_comp).mul_const I
      simpa using this.const_add (c : ℂ)
    have hm1 : pv u ∈ ball c0 r := by rw [hpv]; exact hp u hu 1 ⟨zero_le_one, le_rfl⟩
    have hm2 : (c : ℂ) + u * I ∈ ball c0 r := by
      have := hp u hu 0 ⟨le_rfl, zero_le_one⟩; simpa using this
    have := ((hΦ _ hm1).comp u hpvd).sub ((hΦ _ hm2).comp u hld)
    convert this using 1
    unfold Gk; ring
  have hcont : Continuous fun u : ℝ => Gk ν L u - I * fk ν L ((c : ℂ) + u * I) :=
    (continuous_Gk ν L).sub (continuous_const.mul (continuous_fk_line ν L hc))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _),
    hF T ⟨hT, le_rfl⟩, hF u0 ⟨le_rfl, hT⟩]


lemma clamp_mem (t : ℝ) : max 0 (min t 1) ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

lemma Fs_eq_clamp (ν : ℕ) (L c u : ℝ) : Fs ν L c u = ∫ t in (0 : ℝ)..1, ((1 - u - c : ℝ) : ℂ) *
    fk ν L ((c : ℂ) + ((max 0 (min t 1) : ℝ) : ℂ) * ((1 - u - c : ℝ) : ℂ) + u * I) := by
  unfold Fs
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [uIcc_of_le zero_le_one] at ht
  simp only [min_eq_left ht.2, max_eq_right ht.1]

lemma continuous_Fs (ν : ℕ) (L : ℝ) {c : ℝ} (hc : 0 < c) : Continuous (Fs ν L c) := by
  have e : Fs ν L c = fun u => ∫ t in (0 : ℝ)..1, ((1 - u - c : ℝ) : ℂ) *
      fk ν L ((c : ℂ) + ((max 0 (min t 1) : ℝ) : ℂ) * ((1 - u - c : ℝ) : ℂ) + u * I) :=
    funext (Fs_eq_clamp ν L c)
  rw [e]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  rw [continuous_iff_continuousAt]
  rintro ⟨u, t⟩
  have hm := clamp_mem t
  have hne := seg_pt_ne_zero hc hm.1 hm.2 u
  have hin : Continuous fun q : ℝ × ℝ =>
      (c : ℂ) + ((max 0 (min q.2 1) : ℝ) : ℂ) * ((1 - q.1 - c : ℝ) : ℂ) + q.1 * I := by
    fun_prop
  refine (continuous_ofReal.comp (by fun_prop : Continuous fun q : ℝ × ℝ => 1 - q.1 - c)).continuousAt.mul ?_
  exact ContinuousAt.comp (g := fk ν L) (continuousAt_fk ν L hne) hin.continuousAt

lemma graph_zero {ν : ℕ} (L : ℝ) {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ∫ u in (0 : ℝ)..T, (Gk ν L u - I * fk ν L ((c : ℂ) + u * I)) = Fs ν L c T - Fs ν L c 0 := by
  set h : ℝ → ℂ := fun u => Gk ν L u - I * fk ν L ((c : ℂ) + u * I) with hh
  have hcont : Continuous h := (continuous_Gk ν L).sub (continuous_const.mul (continuous_fk_line ν L hc))
  have hprim : Continuous fun a : ℝ => ∫ u in (0 : ℝ)..a, h u :=
    intervalIntegral.continuous_primitive (fun a b => hcont.intervalIntegrable a b) 0
  have hL : Tendsto (fun a => ∫ u in a..T, h u) (𝓝[>] 0) (𝓝 (∫ u in (0 : ℝ)..T, h u)) := by
    have e : ∀ a, ∫ u in a..T, h u = (∫ u in (0 : ℝ)..T, h u) - ∫ u in (0 : ℝ)..a, h u := by
      intro a
      have := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := 0) (b := a) (c := T)
        (hcont.intervalIntegrable 0 a) (hcont.intervalIntegrable a T)
      rw [← this]; ring
    rw [show (fun a => ∫ u in a..T, h u) = fun a => (∫ u in (0 : ℝ)..T, h u) - ∫ u in (0 : ℝ)..a, h u
      from funext e]
    have : Tendsto (fun a => ∫ u in (0 : ℝ)..a, h u) (𝓝[>] 0) (𝓝 0) := by
      have := (hprim.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      have h0 : ∫ u in (0 : ℝ)..0, h u = 0 := intervalIntegral.integral_same
      rwa [h0] at this
    have := (tendsto_const_nhds (x := ∫ u in (0 : ℝ)..T, h u)).sub this
    rwa [sub_zero] at this
  have hR : Tendsto (fun a => Fs ν L c T - Fs ν L c a) (𝓝[>] 0) (𝓝 (Fs ν L c T - Fs ν L c 0)) :=
    tendsto_const_nhds.sub (((continuous_Fs ν L hc).tendsto 0).mono_left nhdsWithin_le_nhds)
  have hev : ∀ᶠ a in 𝓝[>] (0 : ℝ), ∫ u in a..T, h u = Fs ν L c T - Fs ν L c a := by
    filter_upwards [Ioo_mem_nhdsGT hT] with a ha
    exact graph_finite L hc ha.1 ha.2.le
  exact tendsto_nhds_unique (hL.congr' hev) hR

lemma norm_Fs_le {ν : ℕ} (hν : 1 ≤ ν) {L : ℝ} (hL : 0 ≤ L) {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 1 ≤ T) :
    ‖Fs ν L c T‖ ≤ (T + c) * Real.exp (L * (c + 1)) / T ^ 2 := by
  unfold Fs
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖((1 - T - c : ℝ) : ℂ) *
      fk ν L ((c : ℂ) + t * ((1 - T - c : ℝ) : ℂ) + T * I)‖ ≤ (T + c) * Real.exp (L * (c + 1)) / T ^ 2 := by
    intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    set p : ℂ := (c : ℂ) + t * ((1 - T - c : ℝ) : ℂ) + T * I with hp
    have hpre : p.re = c + t * (1 - T - c) := by simp [hp]
    have hpim : p.im = T := by simp [hp]
    have hTp : T ≤ ‖p‖ := by rw [← hpim]; exact (le_abs_self _).trans (abs_im_le_norm p)
    have hp0 : 0 < ‖p‖ := by linarith
    rw [norm_mul, norm_fk, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |1 - T - c| ≤ T + c := by rw [abs_le]; constructor <;> linarith
    have hre : (p - p⁻¹).re ≤ c + 1 := by
      rw [sub_re, inv_re, hpre]
      have hns : Complex.normSq p = ‖p‖ ^ 2 := (Complex.sq_norm p).symm
      have ha : |c + t * (1 - T - c)| ≤ ‖p‖ := by rw [← hpre]; exact abs_re_le_norm p
      have : -(c + t * (1 - T - c)) / Complex.normSq p ≤ 1 := by
        rw [hns, div_le_one (by positivity)]
        have := neg_le_abs (c + t * (1 - T - c))
        nlinarith
      have h2 : t * (1 - T - c) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.1.le (by linarith)
      have : -(c + t * (1 - T - c)) / Complex.normSq p = -((c + t * (1 - T - c)) / Complex.normSq p) := by ring
      linarith
    have he : Real.exp (L * (p - p⁻¹).re) ≤ Real.exp (L * (c + 1)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hre hL)
    have hpow : T ^ 2 ≤ ‖p‖ ^ (ν + 1) := by
      calc T ^ 2 ≤ ‖p‖ ^ 2 := pow_le_pow_left₀ (by linarith) hTp 2
        _ ≤ ‖p‖ ^ (ν + 1) := pow_le_pow_right₀ (by linarith) (by omega)
    have hinv : (‖p‖ ^ (ν + 1))⁻¹ ≤ (T ^ 2)⁻¹ := inv_anti₀ (by positivity) hpow
    calc |1 - T - c| * ((‖p‖ ^ (ν + 1))⁻¹ * Real.exp (L * (p - p⁻¹).re))
        ≤ (T + c) * ((T ^ 2)⁻¹ * Real.exp (L * (c + 1))) := by gcongr
      _ = (T + c) * Real.exp (L * (c + 1)) / T ^ 2 := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa using this

lemma tendsto_Fs {ν : ℕ} (hν : 1 ≤ ν) {L : ℝ} (hL : 0 ≤ L) {c : ℝ} (hc : 0 < c) :
    Tendsto (Fs ν L c) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun T : ℝ => (T + c) * Real.exp (L * (c + 1)) / T ^ 2) atTop (𝓝 0) := by
    have e : ∀ᶠ T : ℝ in atTop, (T + c) * Real.exp (L * (c + 1)) / T ^ 2 =
        Real.exp (L * (c + 1)) * (T⁻¹ + c * (T⁻¹) ^ 2) := by
      filter_upwards [eventually_gt_atTop 0] with T hT
      field_simp
    rw [tendsto_congr' e]
    have h1 := tendsto_inv_atTop_zero (𝕜 := ℝ)
    have : Tendsto (fun T : ℝ => T⁻¹ + c * (T⁻¹) ^ 2) atTop (𝓝 (0 + c * 0 ^ 2)) :=
      h1.add ((h1.pow 2).const_mul c)
    simpa using this.const_mul (Real.exp (L * (c + 1)))
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with T hT
  exact norm_Fs_le hν hL hc hT

lemma Fs_zero_im (ν : ℕ) (L c : ℝ) : (Fs ν L c 0).im = 0 := by
  have e : Fs ν L c 0 = ((∫ t in (0 : ℝ)..1, (1 - 0 - c) * (fk ν L ((c + t * (1 - 0 - c) : ℝ) : ℂ)).re : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    unfold Fs
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have h1 : (c : ℂ) + t * ((1 - 0 - c : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I = ((c + t * (1 - 0 - c) : ℝ) : ℂ) := by
      push_cast; ring
    rw [h1]
    have h2 : fk ν L ((c + t * (1 - 0 - c) : ℝ) : ℂ) = ((fk ν L ((c + t * (1 - 0 - c) : ℝ) : ℂ)).re : ℂ) := by
      apply Complex.ext
      · simp
      · simp only [Complex.ofReal_im]; exact fk_ofReal_im ν L _
    conv_lhs => rw [h2]
    push_cast; ring
  rw [e, Complex.ofReal_im]

/-- The vertical line integral `(1/2π) ∫_ℝ f(c+iu) du`. -/
noncomputable def LineInt (ν : ℕ) (L c : ℝ) : ℂ :=
  ((1 / (2 * π) : ℝ) : ℂ) * ∫ u : ℝ, fk ν L ((c : ℂ) + u * I)

/-- **Contour identification**: `(1/2π) ∫_ℝ f(c+iu) du = I_ν(L)` for every `c > 0`. -/
theorem lineInt_eq_Ik {ν : ℕ} (hν : 1 ≤ ν) {L : ℝ} (hL : 0 ≤ L) {c : ℝ} (hc : 0 < c) :
    LineInt ν L c = (Ik ν L : ℂ) := by
  set g : ℝ → ℂ := fun u => fk ν L ((c : ℂ) + u * I) with hg
  have hgi : Integrable g := integrable_fk_line hν hL hc
  set J : ℂ := ∫ u in Ioi (0 : ℝ), g u with hJ
  -- A − iJ = −F(0)
  have hkey : Ak ν L - I * J = -Fs ν L c 0 := by
    have hint : IntegrableOn (fun u => Gk ν L u - I * g u) (Ioi 0) :=
      (integrableOn_Gk hν hL).sub (hgi.integrableOn.const_mul I)
    have h1 := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
    have h2 : ∫ u in Ioi (0 : ℝ), (Gk ν L u - I * g u) = Ak ν L - I * J := by
      rw [integral_sub (integrableOn_Gk hν hL) (hgi.integrableOn.const_mul I), integral_const_mul]
      rfl
    rw [h2] at h1
    have h3 : Tendsto (fun T => Fs ν L c T - Fs ν L c 0) atTop (𝓝 (0 - Fs ν L c 0)) :=
      (tendsto_Fs hν hL hc).sub tendsto_const_nhds
    have hev : ∀ᶠ T in atTop, ∫ u in (0 : ℝ)..id T, (Gk ν L u - I * g u) = Fs ν L c T - Fs ν L c 0 := by
      filter_upwards [eventually_gt_atTop 0] with T hT
      exact graph_zero L hc hT
    have := tendsto_nhds_unique (h1.congr' hev) h3
    rw [this]; ring
  -- the full line is J + conj J
  have hneg : ∫ u in Iic (0 : ℝ), g u = conj J := by
    have h1 := integral_comp_neg_Ioi (c := 0) g
    simp only [neg_zero] at h1
    rw [← h1, hJ, ← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    simp only [hg]
    rw [← fk_conj]
    congr 1
    apply Complex.ext <;> simp
  have hfull : ∫ u : ℝ, g u = J + conj J := by
    rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hgi.integrableOn hgi.integrableOn, hneg]; ring
  have hJre : J.re = (Ak ν L).im := by
    have : I * J = Ak ν L + Fs ν L c 0 := by linear_combination -hkey
    have h2 := congrArg Complex.im this
    simp only [mul_im, I_re, I_im, zero_mul, one_mul, zero_add, add_im] at h2
    rw [h2, Fs_zero_im, add_zero]
  unfold LineInt Ik
  rw [hfull, Complex.add_conj, hJre]
  push_cast
  field_simp

end RamanujanTau.VoronoiTrunc
