/-
# Landau's lemma in partial-fraction form

If `f` is analytic on `|z − c| ≤ r`, `f(c) ≠ 0` and `|f(z)| ≤ e^M |f(c)|` there, then there is a
finite set `S` of zeros of `f` in `|z − c| ≤ r/3`, with multiplicities `n`, such that for every
`z` with `|z − c| ≤ r/12` and `f(z) ≠ 0`

  `‖f'/f(z) − Σ_{u ∈ S} n_u/(z − u)‖ ≤ 24 M / r`.

(Titchmarsh §3.9 Lemma α, Montgomery–Vaughan Lemma 6.3.)  The proof is the one of
`ZeroFreeRegion.landau` (copied: zeros of the disc `r/3` divided out, maximum principle, logarithm
`H` of the quotient), but `H'` is now bounded off the centre: Borel–Carathéodory gives
`|H| ≤ 2M` on `|w − c| ≤ r/6`, and Cauchy's estimate on circles of radius `r/12` gives
`|H'(z)| ≤ 24M/r`.
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.TauPNTError

open Complex Metric Set Filter Topology MeromorphicOn

/-- **Landau's lemma, partial-fraction form.** -/
theorem landau_pf {f : ℂ → ℂ} {c : ℂ} {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hfc : f c ≠ 0)
    (hbd : ∀ z ∈ closedBall c r, ‖f z‖ ≤ Real.exp M * ‖f c‖) :
    ∃ (S : Finset ℂ) (n : ℂ → ℕ), (∀ u ∈ S, dist u c ≤ r / 3 ∧ f u = 0) ∧
      ∀ z ∈ closedBall c (r / 12), f z ≠ 0 →
        ‖deriv f z / f z - ∑ u ∈ S, (n u : ℂ) * (1 / (z - u))‖ ≤ 24 * M / r := by
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
  -- Borel–Carathéodory: `‖H‖ ≤ 2M` on `closedBall c (r/6)`
  have hHsmall : ∀ w ∈ closedBall c (r / 6), ‖H w‖ ≤ 2 * M := by
    intro w hw
    set k : ℂ → ℂ := fun v => H (c + v) with hk
    have hmaps : MapsTo (fun v : ℂ => c + v) (ball 0 (r / 3)) (ball c (r / 3)) := by
      intro v hv
      simp only [mem_ball, dist_zero_right] at hv
      simpa [mem_ball, dist_eq] using hv
    have hkd : DifferentiableOn ℂ k (ball 0 (r / 3)) :=
      hHd.comp (differentiableOn_const c |>.add differentiableOn_id) hmaps
    have hk1 : MapsTo k (ball 0 (r / 3)) {z | z.re ≤ M} := fun v hv => hHre _ (hmaps hv)
    have hk0 : k 0 = 0 := by simp [hk, hH0]
    have hwn : ‖w - c‖ ≤ r / 6 := by rw [← dist_eq]; exact hw
    have hwb : w - c ∈ ball (0 : ℂ) (r / 3) := by
      rw [mem_ball, dist_zero_right]; linarith
    have := Complex.borelCaratheodory_zero hM hkd hk1 (by linarith) hwb hk0
    simp only [hk, add_sub_cancel] at this
    refine this.trans ?_
    have hpos : 0 < r / 3 - ‖w - c‖ := by linarith
    rw [div_le_iff₀ hpos]
    nlinarith [norm_nonneg (w - c)]
  refine ⟨Sin, n, fun u hu => ⟨(Finset.mem_filter.mp hu).2,
    ((hmemSall u).1 (Finset.mem_filter.mp hu).1).2⟩, ?_⟩
  intro z hz hfz
  have hzc : dist z c ≤ r / 12 := hz
  have hzball : z ∈ ball c r := by rw [mem_ball]; linarith
  have hzsmall : z ∈ ball c (r / 3) := by rw [mem_ball]; linarith
  have hzU : z ∈ U := hballU hzball
  have he := hfG z hzball
  have hfz' : f z = Pin z * G z := he.eq_of_nhds
  have hPinz : Pin z ≠ 0 := by intro h; apply hfz; rw [hfz', h, zero_mul]
  have hGz : G z ≠ 0 := by intro h; apply hfz; rw [hfz', h, mul_zero]
  have hHz : deriv H z = deriv G z / G z := (hH z hzsmall).deriv
  -- Cauchy's estimate on the circle of radius `r/12` about `z`
  have hHz_bd : ‖deriv H z‖ ≤ 24 * M / r := by
    have hsub : closedBall z (r / 12) ⊆ ball c (r / 3) := by
      intro w hw
      rw [mem_closedBall] at hw
      rw [mem_ball]
      have := dist_triangle w z c
      linarith
    have hdc : DiffContOnCl ℂ H (ball z (r / 12)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball z (by positivity : r / 12 ≠ 0)]
      exact hHd.mono hsub
    have hsph : ∀ w ∈ sphere z (r / 12), ‖H w‖ ≤ 2 * M := by
      intro w hw
      apply hHsmall
      rw [mem_closedBall]
      have h1 : dist w z = r / 12 := hw
      have := dist_triangle w z c
      linarith
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < r / 12)
      hdc hsph
    calc ‖deriv H z‖ ≤ 2 * M / (r / 12) := this
      _ = 24 * M / r := by field_simp; ring
  have hlog : deriv f z / f z = (∑ u ∈ Sin, (n u : ℂ) * (1 / (z - u))) + deriv G z / G z := by
    have hzu : ∀ u ∈ Sin, z - u ≠ 0 := by
      intro u hu h
      rw [sub_eq_zero] at h
      subst h
      exact hfz ((hmemSall _).1 (Finset.mem_filter.mp hu).1).2
    have h1 : deriv f z / f z = logDeriv (fun w => Pin w * G w) z := by
      rw [logDeriv_apply, he.deriv_eq, he.eq_of_nhds]
    rw [h1, logDeriv_mul z hPinz hGz (hPin_d z) (hGan z hzU).differentiableAt, logDeriv_apply G]
    congr 1
    rw [hPin, logDeriv_prod]
    · apply Finset.sum_congr rfl
      intro u hu
      rw [logDeriv_fun_pow (by fun_prop), logDeriv_apply]
      simp [div_eq_mul_inv]
    · intro u hu; exact pow_ne_zero _ (hzu u hu)
    · intro u _; fun_prop
  rw [hlog, add_sub_cancel_left, ← hHz]
  exact hHz_bd

end RamanujanTau.TauPNTError
