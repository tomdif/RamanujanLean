/-
# Landau's lemma: a one-sided bound for the logarithmic derivative

If `f` is analytic on `|z − c| ≤ r`, `f(c) ≠ 0`, `|f(z)| ≤ e^M |f(c)|` there, and every zero of `f`
in `|z − c| ≤ r/3` has real part `≤ Re c`, then for every zero `ρ₀` in `|z − c| ≤ r/3` of order
`≥ m`,

  `−Re f'/f(c) ≤ 12 M / r − m · Re 1/(c − ρ₀)`.

Proof (Titchmarsh §3.9, Montgomery–Vaughan Lemma 6.3).  Divide out the zeros of `f` in the disc
`r/3` (Mathlib's `MeromorphicOn.extract_zeros_poles`): `f = P · G` with `P = ∏ (z − u)^{ord_u}`.
On `|z − c| = 2r/3` each factor satisfies `|z − u| ≥ |c − u|`, so `|G| ≤ e^M |G(c)|` there and,
by the maximum principle, inside.  `G` is zero-free on the disc `r/3`, so it has a logarithm `H`
(Mathlib's primitives on discs) with `H(c) = 0`, `Re H ≤ M`; Borel–Carathéodory (Mathlib) plus
Cauchy's estimate give `|H'(c)| ≤ 12 M / r`.  Finally `f'/f(c) = Σ ord_u/(c − u) + H'(c)` and
every `Re 1/(c − u) ≥ 0`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.ZeroFreeRegion

open Complex Metric Set Filter Topology MeromorphicOn

/-- Borel–Carathéodory + Cauchy: if `h c = 0` and `Re h ≤ M` on `ball c R`, then
`‖h'(c)‖ ≤ 4M/R`. -/
lemma norm_deriv_le_of_re_le {h : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hd : DifferentiableOn ℂ h (ball c R)) (hre : ∀ z ∈ ball c R, (h z).re ≤ M)
    (h0 : h c = 0) : ‖deriv h c‖ ≤ 4 * M / R := by
  set k : ℂ → ℂ := fun w => h (c + w) with hk
  have hmaps : MapsTo (fun w : ℂ => c + w) (ball 0 R) (ball c R) := by
    intro w hw
    simp only [mem_ball, dist_zero_right] at hw
    simpa [mem_ball, dist_eq] using hw
  have hkd : DifferentiableOn ℂ k (ball 0 R) :=
    hd.comp (differentiableOn_const c |>.add differentiableOn_id) hmaps
  have hk1 : MapsTo k (ball 0 R) {z | z.re ≤ M} := fun w hw => hre _ (hmaps hw)
  have hk0 : k 0 = 0 := by simp [hk, h0]
  have hsph : ∀ z ∈ sphere c (R / 2), ‖h z‖ ≤ 2 * M := by
    intro z hz
    have hzn : ‖z - c‖ = R / 2 := by rw [← dist_eq]; exact hz
    have hw : z - c ∈ ball (0 : ℂ) R := by
      rw [mem_ball, dist_zero_right, hzn]; linarith
    have := Complex.borelCaratheodory_zero hM hkd hk1 hR hw hk0
    simp only [hk, add_sub_cancel] at this
    rw [hzn] at this
    calc ‖h z‖ ≤ 2 * M * (R / 2) / (R - R / 2) := this
      _ = 2 * M := by field_simp; ring
  have hdc : DiffContOnCl ℂ h (ball c (R / 2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball c (by linarith : R / 2 ≠ 0)]
    exact hd.mono (closedBall_subset_ball (by linarith))
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith : 0 < R / 2) hdc hsph
  calc ‖deriv h c‖ ≤ 2 * M / (R / 2) := this
    _ = 4 * M / R := by field_simp; ring

lemma re_one_div_nonneg {c u : ℂ} (h : u.re ≤ c.re) : 0 ≤ (1 / (c - u)).re := by
  rw [one_div, Complex.inv_re]
  exact div_nonneg (by simp; linarith) (Complex.normSq_nonneg _)

/-- **Landau's lemma.** -/
theorem landau {f : ℂ → ℂ} {c : ℂ} {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hfc : f c ≠ 0)
    (hbd : ∀ z ∈ closedBall c r, ‖f z‖ ≤ Real.exp M * ‖f c‖)
    (hzero : ∀ u ∈ closedBall c (r / 3), f u = 0 → u.re ≤ c.re)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ closedBall c (r / 3)) {m : ℕ} (hm : (m : ℕ∞) ≤ analyticOrderAt f ρ₀) :
    -(deriv f c / f c).re ≤ 12 * M / r - m * (1 / (c - ρ₀)).re := by
  classical
  set U : Set ℂ := closedBall c r with hU
  have hUc : IsPreconnected U := (convex_closedBall c r).isPreconnected
  have hcU : c ∈ U := mem_closedBall_self hr.le
  have hballU : ball c r ⊆ U := ball_subset_closedBall
  have hord : ∀ u ∈ U, analyticOrderAt f u ≠ ⊤ := by
    intro u hu htop
    rw [analyticOrderAt_eq_top] at htop
    have := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hu
      (htop.mono fun z hz => by simpa using hz) hcU
    exact hfc (by simpa using this)
  have h₂ : ∀ u : U, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    rw [(hf u u.2).meromorphicOrderAt_eq]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hord u u.2)
    rw [← hn]; simp
  set D := divisor f U with hDdef
  have h₃ : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := hf.meromorphicOn.extract_zeros_poles h₂ h₃
  set n : ℂ → ℕ := fun u => analyticOrderNatAt f u with hn
  have hD : ∀ u ∈ U, D u = (n u : ℤ) := by
    intro u hu
    rw [hDdef, AnalyticOnNhd.divisor_apply hf hu]
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hord u hu)
    simp only [hn, analyticOrderNatAt]
    rw [← hm, ENat.toNat_coe]
    rfl
  set Sall : Finset ℂ := h₃.toFinset with hSall
  have hmemSall : ∀ u, u ∈ Sall ↔ (u ∈ U ∧ f u = 0) := by
    intro u
    rw [hSall, Set.Finite.mem_toFinset, Function.mem_support]
    constructor
    · intro h
      have huU : u ∈ U := D.supportWithinDomain (by simpa using h)
      refine ⟨huU, ?_⟩
      rw [hD u huU] at h
      have h0 : analyticOrderAt f u ≠ 0 := by
        intro h0; apply h; simp [hn, analyticOrderNatAt, h0]
      exact (analyticOrderAt_ne_zero.mp h0).2
    · rintro ⟨huU, hFu⟩
      rw [hD u huU]
      have h0 : analyticOrderAt f u ≠ 0 := analyticOrderAt_ne_zero.2 ⟨hf u huU, hFu⟩
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hord u huU)
      have hm0 : m ≠ 0 := by rintro rfl; exact h0 (by rw [← hm]; rfl)
      simp only [hn, analyticOrderNatAt, ← hm, ENat.toNat_coe]
      exact_mod_cast hm0
  set P : ℂ → ℂ := fun w => ∏ u ∈ Sall, (w - u) ^ (n u) with hP
  have hloc : ∀ z ∈ ball c r, f =ᶠ[𝓝 z] fun w => P w * g w := by
    intro z hz
    have hzU : z ∈ U := hballU hz
    have hprod : (∏ᶠ u, (· - u) ^ D u : ℂ → ℂ) = ∏ u ∈ Sall, (· - u) ^ D u := by
      apply finprod_eq_prod_of_mulSupport_subset
      intro u hu
      rw [Function.mem_mulSupport] at hu
      simp only [Finset.mem_coe, hSall, Set.Finite.mem_toFinset, Function.mem_support]
      intro h0; apply hu; rw [h0]; funext w; simp
    have hrhs : ∀ w, ((∏ᶠ u, (· - u) ^ D u : ℂ → ℂ) • g) w = P w * g w := by
      intro w
      rw [hprod, Pi.smul_apply', Finset.prod_apply, smul_eq_mul, hP]
      congr 1
      apply Finset.prod_congr rfl
      intro u hu
      rw [hD u ((hmemSall u).1 hu).1, zpow_natCast, Pi.pow_apply]
    have hNE : f =ᶠ[𝓝[≠] z] fun w => P w * g w := by
      have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hfg) z hzU
      have hUn : U ∈ 𝓝[≠] z :=
        mem_nhdsWithin_of_mem_nhds (mem_of_superset (isOpen_ball.mem_nhds hz) hballU)
      filter_upwards [h1, hUn] with w hw hwU
      rcases hw with hw | hw
      · rw [Set.mem_setOf_eq] at hw; rw [hw, hrhs]
      · exact absurd hwU hw
    have hgc : ContinuousAt g z := (hg_an z hzU).continuousAt
    have hPc : ContinuousAt P z := by rw [hP]; fun_prop
    exact (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (hf z hzU).continuousAt (hPc.mul hgc)).mp hNE
  -- split the zeros
  set Sin := Sall.filter (fun u => dist u c ≤ r / 3) with hSin
  set Sout := Sall.filter (fun u => ¬ dist u c ≤ r / 3) with hSout
  set Pin : ℂ → ℂ := fun w => ∏ u ∈ Sin, (w - u) ^ (n u) with hPin
  set Pout : ℂ → ℂ := fun w => ∏ u ∈ Sout, (w - u) ^ (n u) with hPout
  set G : ℂ → ℂ := fun w => Pout w * g w with hG
  have hPsplit : ∀ w, P w = Pin w * Pout w := fun w =>
    (Finset.prod_filter_mul_prod_filter_not Sall (fun u => dist u c ≤ r / 3) _).symm
  have hPin_d : Differentiable ℂ Pin := by rw [hPin]; fun_prop
  have hPout_d : Differentiable ℂ Pout := by rw [hPout]; fun_prop
  have hGan : AnalyticOnNhd ℂ G U := fun z hz =>
    ((hPout_d.analyticAt z).mul (hg_an z hz))
  have hfG : ∀ z ∈ ball c r, f =ᶠ[𝓝 z] fun w => Pin w * G w := by
    intro z hz
    filter_upwards [hloc z hz] with w hw
    rw [hw, hPsplit, hG]; ring
  have hcball : c ∈ ball c r := mem_ball_self hr
  have hfc' : f c = Pin c * G c := (hfG c hcball).eq_of_nhds
  have hPinc : Pin c ≠ 0 := by
    intro h; apply hfc; rw [hfc', h, zero_mul]
  have hGc : G c ≠ 0 := by
    intro h; apply hfc; rw [hfc', h, mul_zero]
  -- maximum principle for `G` on the disc `2r/3`
  have hGsph : ∀ z ∈ sphere c (2 * r / 3), ‖G z‖ ≤ Real.exp M * ‖G c‖ := by
    intro z hz
    have hzd : dist z c = 2 * r / 3 := hz
    have hzb : z ∈ ball c r := by rw [mem_ball, hzd]; linarith
    have hfz : f z = Pin z * G z := (hfG z hzb).eq_of_nhds
    have hle : ‖Pin c‖ ≤ ‖Pin z‖ := by
      simp only [hPin, norm_prod, norm_pow]
      apply Finset.prod_le_prod (fun u _ => by positivity)
      intro u hu
      have hu' : dist u c ≤ r / 3 := (Finset.mem_filter.mp hu).2
      apply pow_le_pow_left₀ (norm_nonneg _)
      have h1 : ‖c - u‖ ≤ r / 3 := by rw [← dist_eq, dist_comm]; exact hu'
      have h2 : dist z c ≤ dist z u + dist u c := dist_triangle _ _ _
      rw [← dist_eq z u]
      linarith
    have hPz : 0 < ‖Pin z‖ := lt_of_lt_of_le (norm_pos_iff.mpr hPinc) hle
    have hb := hbd z (hballU hzb)
    rw [hfz, hfc', norm_mul (Pin z) (G z), norm_mul (Pin c) (G c)] at hb
    have : ‖Pin z‖ * ‖G z‖ ≤ ‖Pin z‖ * (Real.exp M * ‖G c‖) := by
      calc ‖Pin z‖ * ‖G z‖ ≤ Real.exp M * (‖Pin c‖ * ‖G c‖) := hb
        _ ≤ Real.exp M * (‖Pin z‖ * ‖G c‖) := by gcongr
        _ = ‖Pin z‖ * (Real.exp M * ‖G c‖) := by ring
    exact le_of_mul_le_mul_left this hPz
  have hGbd : ∀ z ∈ ball c (r / 3), ‖G z‖ ≤ Real.exp M * ‖G c‖ := by
    intro z hz
    have hdc : DiffContOnCl ℂ G (ball c (2 * r / 3)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball c (by positivity : 2 * r / 3 ≠ 0)]
      exact hGan.differentiableOn.mono (closedBall_subset_closedBall (by linarith))
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc
    · rw [frontier_ball c (by positivity : 2 * r / 3 ≠ 0)]; exact hGsph
    · rw [closure_ball c (by positivity : 2 * r / 3 ≠ 0)]
      exact closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz)
  have hsmallU : ball c (r / 3) ⊆ U := fun z hz =>
    ball_subset_closedBall (ball_subset_ball (by linarith) hz)
  have hGne : ∀ z ∈ ball c (r / 3), G z ≠ 0 := by
    intro z hz
    refine mul_ne_zero ?_ (hg_ne ⟨z, hsmallU hz⟩)
    rw [hPout, Finset.prod_ne_zero_iff]
    intro u hu
    apply pow_ne_zero
    intro h
    rw [sub_eq_zero] at h
    subst h
    exact (Finset.mem_filter.mp hu).2 (le_of_lt hz)
  -- a logarithm of `G` on the disc `r/3`
  set k : ℂ → ℂ := fun z => deriv G z / G z with hk
  have hkd : DifferentiableOn ℂ k (ball c (r / 3)) := by
    intro z hz
    have hzU := hsmallU hz
    exact (((hGan z hzU).deriv.differentiableAt).div (hGan z hzU).differentiableAt
      (hGne z hz)).differentiableWithinAt
  obtain ⟨H, hH0, hH⟩ := (hkd.isExactOn_ball).with_val_at c 0
  have hHd : DifferentiableOn ℂ H (ball c (r / 3)) := fun z hz =>
    (hH z hz).differentiableAt.differentiableWithinAt
  have hexp : ∀ z ∈ ball c (r / 3), G z = G c * Complex.exp (H z) := by
    set Q : ℂ → ℂ := fun z => G z * Complex.exp (-H z) with hQ
    have hQd : ∀ z ∈ ball c (r / 3), HasDerivAt Q 0 z := by
      intro z hz
      have hzU := hsmallU hz
      have h1 := (hGan z hzU).differentiableAt.hasDerivAt
      have h2 := ((hH z hz).neg).cexp
      have := h1.mul h2
      convert this using 1
      simp only [hk]
      field_simp [hGne z hz]
      ring
    have hQdiff : DifferentiableOn ℂ Q (ball c (r / 3)) := fun z hz =>
      (hQd z hz).differentiableAt.differentiableWithinAt
    have hconst := fun z (hz : z ∈ ball c (r / 3)) =>
      isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c (r / 3)).isPreconnected hQdiff
        (fun w hw => (hQd w hw).deriv) hz (mem_ball_self (by linarith : 0 < r / 3))
    intro z hz
    have := hconst z hz
    simp only [hQ, hH0, neg_zero, Complex.exp_zero, mul_one] at this
    calc G z = G z * Complex.exp (-H z) * Complex.exp (H z) := by
          rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
      _ = G c * Complex.exp (H z) := by rw [this]
  have hHre : ∀ z ∈ ball c (r / 3), (H z).re ≤ M := by
    intro z hz
    have h1 := hGbd z hz
    rw [hexp z hz, norm_mul, Complex.norm_exp] at h1
    have h2 : Real.exp (H z).re ≤ Real.exp M := by
      have hGc0 : 0 < ‖G c‖ := norm_pos_iff.mpr hGc
      nlinarith
    exact Real.exp_le_exp.mp h2
  have hHc : deriv H c = deriv G c / G c := (hH c (mem_ball_self (by linarith))).deriv
  have hHbound : ‖deriv G c / G c‖ ≤ 12 * M / r := by
    rw [← hHc]
    have := norm_deriv_le_of_re_le (by linarith : 0 < r / 3) hM hHd hHre hH0
    calc ‖deriv H c‖ ≤ 4 * M / (r / 3) := this
      _ = 12 * M / r := by field_simp; ring
  -- the logarithmic derivative of `f` at `c`
  have hlog : deriv f c / f c = (∑ u ∈ Sin, (n u : ℂ) * (1 / (c - u))) + deriv G c / G c := by
    have he := hfG c hcball
    have hzu : ∀ u ∈ Sin, c - u ≠ 0 := by
      intro u hu h
      rw [sub_eq_zero] at h
      subst h
      exact hfc ((hmemSall _).1 (Finset.mem_filter.mp hu).1).2
    have h1 : deriv f c / f c = logDeriv (fun w => Pin w * G w) c := by
      rw [logDeriv_apply, he.deriv_eq, he.eq_of_nhds]
    rw [h1, logDeriv_mul c hPinc hGc (hPin_d c) (hGan c hcU).differentiableAt, logDeriv_apply G]
    congr 1
    rw [hPin, logDeriv_prod]
    · apply Finset.sum_congr rfl
      intro u hu
      rw [logDeriv_fun_pow (by fun_prop), logDeriv_apply]
      simp [div_eq_mul_inv]
    · intro u hu; exact pow_ne_zero _ (hzu u hu)
    · intro u _; fun_prop
  -- each zero contributes with the good sign
  have hterm : ∀ u ∈ Sin, 0 ≤ (n u : ℝ) * (1 / (c - u)).re := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := Finset.mem_filter.mp hu
    exact mul_nonneg (Nat.cast_nonneg _)
      (re_one_div_nonneg (hzero u hu2 ((hmemSall u).1 hu1).2))
  have hsum_re : (∑ u ∈ Sin, (n u : ℂ) * (1 / (c - u))).re =
      ∑ u ∈ Sin, (n u : ℝ) * (1 / (c - u)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp
  have hpick : (m : ℝ) * (1 / (c - ρ₀)).re ≤ ∑ u ∈ Sin, (n u : ℝ) * (1 / (c - ρ₀ + ρ₀ - u)).re := by
    simp only [sub_add_cancel]
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · rw [hm0, Nat.cast_zero, zero_mul]
      exact Finset.sum_nonneg hterm
    have hρ₀U : ρ₀ ∈ U := closedBall_subset_closedBall (by linarith) hρ₀
    have hord0 : analyticOrderAt f ρ₀ ≠ 0 := by
      intro h; rw [h] at hm
      have : (m : ℕ∞) = 0 := le_antisymm hm bot_le
      exact absurd (by exact_mod_cast this) hm0.ne'
    have hfρ : f ρ₀ = 0 := (analyticOrderAt_ne_zero.mp hord0).2
    have hmem : ρ₀ ∈ Sin := Finset.mem_filter.mpr ⟨(hmemSall ρ₀).2 ⟨hρ₀U, hfρ⟩, hρ₀⟩
    have hmn : m ≤ n ρ₀ := by
      have h1 : (analyticOrderNatAt f ρ₀ : ℕ∞) = analyticOrderAt f ρ₀ :=
        ENat.coe_toNat (hord ρ₀ hρ₀U)
      have : (m : ℕ∞) ≤ (n ρ₀ : ℕ∞) := by simp only [hn]; rw [h1]; exact hm
      exact_mod_cast this
    have hre0 : 0 ≤ (1 / (c - ρ₀)).re := re_one_div_nonneg (hzero ρ₀ hρ₀ hfρ)
    calc (m : ℝ) * (1 / (c - ρ₀)).re ≤ (n ρ₀ : ℝ) * (1 / (c - ρ₀)).re :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) hre0
      _ ≤ ∑ u ∈ Sin, (n u : ℝ) * (1 / (c - u)).re :=
          Finset.single_le_sum hterm hmem
  simp only [sub_add_cancel] at hpick
  rw [hlog, Complex.add_re, hsum_re]
  have hGre : -(deriv G c / G c).re ≤ 12 * M / r :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hHbound)
  linarith

end RamanujanTau.ZeroFreeRegion
