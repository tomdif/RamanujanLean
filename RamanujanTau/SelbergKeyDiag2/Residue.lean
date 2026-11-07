/-
# A residue at a pole `iβ` on the imaginary axis

`vline_residue_at`: for `F` holomorphic and bounded on `a ≤ Re u ≤ b` (`a < 0 < b`) and `β ∈ ℝ`,

    vline (F e^{u²}/(u − iβ)) b − vline (F e^{u²}/(u − iβ)) a = 2π F(iβ) e^{−β²}.

`HeckeAFE.vline_residue` is the case `β = 0`.  The Gaussian `e^{u²}` is not centred at the pole,
so we write `e^{u²} = e^{(u−iβ)²} e^{2iβu+β²}`; the factor `Ψ = F e^{2iβu+β²}` grows like
`e^{2|β||y|}`, which `e^{(u−iβ)²}` still beats.  Level 1.
-/
import RamanujanTau.HeckeAFE.Contour

set_option autoImplicit false

namespace RamanujanTau.SelbergKeyDiag2

open Complex MeasureTheory Set Filter Topology RamanujanTau.HeckeAFE
open scoped Real

lemma vline_translate (g : ℂ → ℂ) (c β : ℝ) :
    vline (fun u => g (u - β * I)) c = vline g c := by
  unfold vline
  have : (fun y : ℝ => g ((c : ℂ) + y * I - β * I)) = fun y => g ((c : ℂ) + ((y - β : ℝ) : ℂ) * I) := by
    funext y; congr 1; push_cast; ring
  rw [this, integral_sub_right_eq_self (fun y : ℝ => g ((c : ℂ) + (y : ℂ) * I)) β]

lemma integrable_gauss_div_translate {c : ℝ} (hc : c ≠ 0) (β : ℝ) :
    Integrable (fun y : ℝ => cexp (((c : ℂ) + y * I - β * I) ^ 2) / ((c : ℂ) + y * I - β * I)) := by
  have h := (integrable_gauss_div hc).comp_sub_right β
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only
  have : (c : ℂ) + ((y - β : ℝ) : ℂ) * I = (c : ℂ) + y * I - β * I := by push_cast; ring
  rw [this]

theorem vline_residue_at {F : ℂ → ℂ} {a b : ℝ} (β : ℝ) (ha : a < 0) (hb : 0 < b)
    (hF : DifferentiableOn ℂ F (strip a b)) (hM : ∃ M, ∀ u ∈ strip a b, ‖F u‖ ≤ M) :
    vline (fun u => F u * cexp (u ^ 2) / (u - β * I)) b -
        vline (fun u => F u * cexp (u ^ 2) / (u - β * I)) a =
      2 * π * (F (β * I) * Real.exp (-β ^ 2)) := by
  obtain ⟨M, hM⟩ := hM
  set p : ℂ := β * I with hp
  have hpre : p.re = 0 := by simp [hp]
  have hpim : p.im = β := by simp [hp]
  have hpS : p ∈ strip a b := ⟨by rw [hpre]; exact ha.le, by rw [hpre]; exact hb.le⟩
  have hnhds : strip a b ∈ 𝓝 p := strip_mem_nhds (by rw [hpre]; exact ha) (by rw [hpre]; exact hb)
  set Ψ : ℂ → ℂ := fun u => F u * cexp (2 * p * u - p ^ 2) with hΨ
  have hΨd : DifferentiableOn ℂ Ψ (strip a b) :=
    hF.mul (Complex.differentiable_exp.comp (by fun_prop)).differentiableOn
  have hΨp : Ψ p = F p * Real.exp (-β ^ 2) := by
    simp only [hΨ]; congr 1
    rw [Complex.ofReal_exp]; congr 1; rw [hp]; push_cast; ring_nf; rw [I_sq]; ring
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM p hpS)
  -- growth of `Ψ`
  have hΨb : ∀ x y : ℝ, a ≤ x → x ≤ b →
      ‖Ψ ((x : ℂ) + y * I)‖ ≤ M * Real.exp (β ^ 2) * Real.exp (2 * |β| * |y|) := by
    intro x y hax hxb
    simp only [hΨ]
    rw [norm_mul, Complex.norm_exp]
    have hre : (2 * p * ((x : ℂ) + y * I) - p ^ 2).re = -2 * β * y + β ^ 2 := by
      rw [hp]; simp [sq]
    rw [hre]
    have h1 := hM _ (mem_strip_line hax hxb y)
    have h2 : Real.exp (-2 * β * y + β ^ 2) ≤ Real.exp (β ^ 2) * Real.exp (2 * |β| * |y|) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2
      have : -2 * β * y ≤ 2 * |β| * |y| := by
        have := neg_abs_le (β * y); rw [abs_mul] at this; linarith
      linarith
    calc ‖F ((x : ℂ) + y * I)‖ * Real.exp (-2 * β * y + β ^ 2)
        ≤ M * (Real.exp (β ^ 2) * Real.exp (2 * |β| * |y|)) :=
          mul_le_mul h1 h2 (by positivity) hM0
      _ = _ := by ring
  -- bound for `dslope Ψ p`
  have hD : DifferentiableOn ℂ (dslope Ψ p) (strip a b) :=
    (Complex.differentiableOn_dslope hnhds).2 hΨd
  have hKc : IsCompact (strip a b ∩ Metric.closedBall p 1) :=
    (isCompact_closedBall p 1).inter_left (isClosed_strip a b)
  obtain ⟨K, hK⟩ := hKc.exists_bound_of_continuousOn (hD.continuousOn.mono inter_subset_left)
  set K' : ℝ := max K (2 * (M * Real.exp (β ^ 2))) with hK'
  have hK'0 : 0 ≤ K' := le_trans (by positivity) (le_max_right _ _)
  have hdsl : ∀ x y : ℝ, a ≤ x → x ≤ b →
      ‖dslope Ψ p ((x : ℂ) + y * I)‖ ≤ K' * Real.exp (2 * |β| * |y|) := by
    intro x y hax hxb
    set u : ℂ := (x : ℂ) + y * I
    have hu := mem_strip_line hax hxb y
    have he1 : 1 ≤ Real.exp (2 * |β| * |y|) := Real.one_le_exp (by positivity)
    by_cases h1 : ‖u - p‖ ≤ 1
    · have := hK u ⟨hu, by rw [Metric.mem_closedBall, dist_eq_norm]; exact h1⟩
      calc ‖dslope Ψ p u‖ ≤ K := this
        _ ≤ K' := le_max_left _ _
        _ ≤ K' * Real.exp (2 * |β| * |y|) := le_mul_of_one_le_right hK'0 he1
    · push Not at h1
      have hup : u ≠ p := by rintro h; rw [h, sub_self, norm_zero] at h1; linarith
      rw [dslope_of_ne _ hup, slope_def_field, norm_div, div_le_iff₀ (by linarith)]
      have hb1 := hΨb x y hax hxb
      have hb2 : ‖Ψ p‖ ≤ M := by
        rw [hΨp, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        calc ‖F p‖ * Real.exp (-β ^ 2) ≤ M * 1 :=
              mul_le_mul (hM p hpS) (Real.exp_le_one_iff.2 (by nlinarith)) (by positivity) hM0
          _ = M := mul_one M
      have hE : 1 ≤ Real.exp (β ^ 2) := Real.one_le_exp (by positivity)
      have hmm : M ≤ M * Real.exp (β ^ 2) * Real.exp (2 * |β| * |y|) := by
        calc M = M * 1 * 1 := by ring
          _ ≤ M * Real.exp (β ^ 2) * Real.exp (2 * |β| * |y|) := by gcongr
      calc ‖Ψ u - Ψ p‖ ≤ ‖Ψ u‖ + ‖Ψ p‖ := norm_sub_le _ _
        _ ≤ 2 * (M * Real.exp (β ^ 2)) * Real.exp (2 * |β| * |y|) := by linarith
        _ ≤ K' * Real.exp (2 * |β| * |y|) := by gcongr; exact le_max_right _ _
        _ ≤ K' * Real.exp (2 * |β| * |y|) * ‖u - p‖ := le_mul_of_one_le_right (by positivity) h1.le
  -- the regular part has Gaussian decay
  set H : ℂ → ℂ := fun u => dslope Ψ p u * cexp ((u - p) ^ 2) with hH
  have hHd : DifferentiableOn ℂ H (strip a b) :=
    hD.mul (Complex.differentiable_exp.comp (by fun_prop)).differentiableOn
  have hHg : GaussDecay H a b := by
    refine ⟨K' * Real.exp (a ^ 2 + b ^ 2) * Real.exp (7 * β ^ 2), fun x y hax hxb => ?_⟩
    simp only [hH]
    rw [norm_mul, Complex.norm_exp]
    have hre : (((x : ℂ) + y * I - p) ^ 2).re = x ^ 2 - (y - β) ^ 2 := by
      rw [hp]; simp [sq]
    rw [hre]
    have h1 := hdsl x y hax hxb
    have hx2 : x ^ 2 ≤ a ^ 2 + b ^ 2 := by rcases le_total 0 x with h | h <;> nlinarith
    have h2 : Real.exp (2 * |β| * |y|) * Real.exp (x ^ 2 - (y - β) ^ 2) ≤
        Real.exp (a ^ 2 + b ^ 2) * Real.exp (7 * β ^ 2) * Real.exp (-(1 / 2) * y ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.2
      have hby : β * y ≤ |β| * |y| := by rw [← abs_mul]; exact le_abs_self _
      have hsq : (|β| * |y|) * 4 ≤ y ^ 2 / 2 + 8 * β ^ 2 := by
        nlinarith [sq_nonneg (|y| / 2 - 2 * |β|), sq_abs y, sq_abs β]
      nlinarith
    calc ‖dslope Ψ p ((x : ℂ) + y * I)‖ * Real.exp (x ^ 2 - (y - β) ^ 2)
        ≤ K' * Real.exp (2 * |β| * |y|) * Real.exp (x ^ 2 - (y - β) ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = K' * (Real.exp (2 * |β| * |y|) * Real.exp (x ^ 2 - (y - β) ^ 2)) := by ring
      _ ≤ K' * (Real.exp (a ^ 2 + b ^ 2) * Real.exp (7 * β ^ 2) * Real.exp (-(1 / 2) * y ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 hK'0
      _ = _ := by ring
  have hshift := vline_shift (by linarith) hHd hHg
  have hsplit : ∀ c : ℝ, c ≠ 0 → a ≤ c → c ≤ b →
      vline (fun u => F u * cexp (u ^ 2) / (u - β * I)) c =
        vline H c + Ψ p * vline (fun u => cexp (u ^ 2) / u) c := by
    intro c hc hac hcb
    rw [← vline_translate (fun u => cexp (u ^ 2) / u) c β]
    unfold vline
    rw [← integral_const_mul, ← integral_add (integrable_line hHd.continuousOn hHg hac hcb)
      ((integrable_gauss_div_translate hc β).const_mul _)]
    congr 1; ext y
    have hu : (c : ℂ) + y * I - p ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp [hp] at this; exact hc this
    simp only [hH, hΨ]
    rw [dslope_of_ne _ (sub_ne_zero.1 hu), slope_def_field]
    rw [← hp]
    field_simp
    rw [sub_add_cancel, mul_left_comm, ← Complex.exp_add]
    congr 2
    rw [hp]; ring
  rw [hsplit b hb.ne' (by linarith) le_rfl, hsplit a ha.ne le_rfl (by linarith), hshift,
    vline_gauss_div hb, vline_gauss_div_neg ha, hΨp]
  ring

end RamanujanTau.SelbergKeyDiag2
