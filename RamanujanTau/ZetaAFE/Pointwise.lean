/-
# Pointwise form: `|ζ(1/2+it)|² = D(t) + O(t) + O(t^{c−1})`

`D(t) = Σ_n V(2 log n − log(t/2π))/n` (diagonal), `O(t) = Σ_{m≠n} b_{m,n}(t)` (off-diagonal).
-/
import RamanujanTau.ZetaAFE.OffDiag
import RamanujanTau.ZetaAFE.GammaBound

set_option autoImplicit false

namespace RamanujanTau.ZetaAFE

open Complex MeasureTheory Set Filter Topology
open scoped Interval

/-- `|ζ(1/2+it)|²`. -/
noncomputable def zsq (t : ℝ) : ℝ := ‖riemannZeta (1 / 2 + t * I)‖ ^ 2

/-- Off-diagonal coefficients. -/
noncomputable def bo (t : ℝ) (p : ℕ × ℕ) : ℂ := if p.1 = p.2 then 0 else bterm t (ellT t) p

/-- The off-diagonal sum `O(t)`. -/
noncomputable def Oft (t : ℝ) : ℂ := ∑' p, bo t p

lemma bterm_diag (t ℓ : ℝ) (n : ℕ) :
    bterm t ℓ (n, n) = ((1 / ((n : ℝ) + 1) * V (2 * lg n - ℓ) : ℝ) : ℂ) := by
  unfold bterm
  simp only [sub_self, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  have h1 : cexp (-(((lg n + lg n : ℝ) : ℂ) / 2)) = ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by
    rw [show -(((lg n + lg n : ℝ) : ℂ) / 2) = ((-(lg n) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp, Real.exp_neg]
    unfold lg; rw [Real.exp_log (by positivity), one_div]
  rw [h1, show 2 * lg n - ℓ = lg n + lg n - ℓ by ring]
  push_cast; ring

lemma tsum_bterm_split (t : ℝ) :
    ∑' p, bterm t (ellT t) p = (Dsum (ellT t) : ℂ) + Oft t := by
  set bd : ℕ × ℕ → ℂ := fun p => if p.1 = p.2 then bterm t (ellT t) p else 0 with hbd
  have hsplit : ∀ p, bterm t (ellT t) p = bd p + bo t p := by
    intro p; simp only [hbd, bo]; split_ifs <;> simp
  have hS := summable_bterm t (ellT t)
  have hsd : Summable bd := Summable.of_norm_bounded hS.norm (fun p => by
    simp only [hbd]; split_ifs <;> simp)
  have hso : Summable (bo t) := Summable.of_norm_bounded hS.norm (fun p => by
    simp only [bo]; split_ifs <;> simp)
  simp_rw [hsplit]
  rw [hsd.tsum_add hso]
  congr 1
  have hinj : Function.Injective fun n : ℕ => (n, n) := fun a b h => by simpa using h
  have hsupp : Function.support bd ⊆ Set.range fun n : ℕ => (n, n) := by
    intro p hp
    rw [Function.mem_support] at hp
    simp only [hbd] at hp
    split_ifs at hp with h
    · exact ⟨p.1, by ext <;> simp [h]⟩
    · exact absurd rfl hp
  rw [← hinj.tsum_eq hsupp]
  simp only [hbd, if_true]
  simp_rw [bterm_diag]
  unfold Dsum
  rw [Complex.ofReal_tsum]

lemma continuous_zeta_half : Continuous fun t : ℝ => riemannZeta (1 / 2 + t * I) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have h : (1 / 2 : ℂ) + t * I ≠ 1 := half_line_ne_one t
  exact ((differentiableAt_riemannZeta h).continuousAt).comp
    (f := fun t : ℝ => (1 / 2 : ℂ) + t * I) (by fun_prop)

lemma continuous_zsq : Continuous zsq := by
  unfold zsq; exact (continuous_zeta_half.norm).pow 2

lemma exp_ellT {t : ℝ} (ht : 0 < t) : Real.exp (ellT t) = t / (2 * Real.pi) := by
  unfold ellT; rw [Real.exp_log (by positivity)]

lemma exp_c_ellT_le {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t) : Real.exp (c * ellT t) ≤ t ^ c := by
  rw [mul_comm, Real.exp_mul, exp_ellT ht]
  apply Real.rpow_le_rpow (by positivity) _ hc
  rw [div_le_iff₀ (by positivity)]
  have := Real.pi_gt_three
  nlinarith

/-- **Pointwise AFE error.** -/
theorem pointwise_err {c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≤ 1) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ t : ℝ, 8 ≤ t →
      ‖((zsq t : ℝ) : ℂ) - (Dsum (ellT t) : ℂ) - Oft t‖ ≤ CE * t ^ (c - 1) := by
  obtain ⟨K, hK0, hK⟩ := gamma_ratio_line hc hc1
  set Cc : ℝ := Real.exp (c ^ 2) * Real.sqrt (2 * Real.pi) / c with hCc
  have hc0 : 0 < c := by linarith
  refine ⟨K * Cc / Real.pi * Zs (1 / 2 + c) ^ 2, by positivity, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hRc := continuous_Rt_line t hc0.le
  have hB : ∀ y : ℝ, ‖Rt t (c + y * I) * cexp (-(((c : ℂ) + y * I) * (ellT t : ℂ))) - 1‖ ≤
      (K / t) * Real.exp (y ^ 2 / 2) := by
    intro y; have := hK t y ht; unfold ellT
    calc _ ≤ K * Real.exp (y ^ 2 / 2) / t := this
      _ = _ := by ring
  have hR : ∀ y : ℝ, ‖Rt t (c + y * I)‖ ≤ ((1 + K / t) * Real.exp (c * ellT t)) * Real.exp (y ^ 2 / 2) := by
    intro y
    have h1 : Rt t (c + y * I) = (Rt t (c + y * I) * cexp (-(((c : ℂ) + y * I) * (ellT t : ℂ)))) *
        cexp (((c : ℂ) + y * I) * (ellT t : ℂ)) := by
      rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    rw [h1, norm_mul]
    have h2 : ‖cexp (((c : ℂ) + y * I) * (ellT t : ℂ))‖ = Real.exp (c * ellT t) := by
      rw [Complex.norm_exp]; congr 1; simp
    have h3 : ‖Rt t (c + y * I) * cexp (-(((c : ℂ) + y * I) * (ellT t : ℂ)))‖ ≤
        (1 + K / t) * Real.exp (y ^ 2 / 2) := by
      have := hB y
      have h4 := norm_sub_norm_le (Rt t (c + y * I) * cexp (-(((c : ℂ) + y * I) * (ellT t : ℂ)))) 1
      have h5 : 1 ≤ Real.exp (y ^ 2 / 2) := Real.one_le_exp (by positivity)
      rw [norm_one] at h4
      nlinarith
    rw [h2]
    calc ‖Rt t (c + y * I) * cexp (-(((c : ℂ) + y * I) * (ellT t : ℂ)))‖ * Real.exp (c * ellT t)
        ≤ (1 + K / t) * Real.exp (y ^ 2 / 2) * Real.exp (c * ellT t) := by gcongr
      _ = _ := by ring
  have happrox := zeta_sq_approx hc hc1 hRc hR hB
  rw [tsum_bterm_split] at happrox
  have heq : ((zsq t : ℝ) : ℂ) - (Dsum (ellT t) : ℂ) - Oft t =
      ((‖riemannZeta (1 / 2 + t * I)‖ ^ 2 : ℝ) : ℂ) - ((Dsum (ellT t) : ℂ) + Oft t) := by
    unfold zsq; ring
  rw [heq]
  refine happrox.trans ?_
  have hexp := exp_c_ellT_le hc0.le ht0
  have htc : t ^ c / t = t ^ (c - 1) := by
    rw [Real.rpow_sub ht0, Real.rpow_one]
  have hZ : 0 ≤ Zs (1 / 2 + c) ^ 2 := sq_nonneg _
  calc K / t * Cc / Real.pi * Real.exp (c * ellT t) * Zs (1 / 2 + c) ^ 2
      ≤ K / t * Cc / Real.pi * t ^ c * Zs (1 / 2 + c) ^ 2 := by gcongr
    _ = K * Cc / Real.pi * Zs (1 / 2 + c) ^ 2 * (t ^ c / t) := by ring
    _ = _ := by rw [htc]

/-- **Diagonal, pointwise.** -/
theorem diag_err {c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≤ 1) :
    ∃ CD : ℝ, 0 ≤ CD ∧ ∀ t : ℝ, 8 ≤ t →
      |Dsum (ellT t) - ellT t - 2 * Real.eulerMascheroniConstant| ≤ CD * t ^ (c - 1) := by
  set δ : ℝ := c - 1 / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hAD : 0 ≤ AD := by
    unfold AD
    exact integral_nonneg fun u => by have := gk_pos u; positivity
  refine ⟨AD / δ * (2 * Real.pi), by positivity, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hℓ : 0 ≤ ellT t := Real.log_nonneg (by
    rw [le_div_iff₀ (by positivity)]; linarith [Real.pi_lt_four])
  refine (abs_Dsum_sub_le (ellT t)).trans ?_
  rw [abs_of_nonneg hℓ]
  -- (1+ℓ) e^{−ℓ/2} ≤ (1/δ) e^{−(1−c)ℓ}
  have h1 : (1 + ellT t) * Real.exp (-ellT t / 2) ≤ 1 / δ * Real.exp (-((1 - c) * ellT t)) := by
    have hδ1 : δ ≤ 1 := by rw [hδ]; linarith
    have he : δ * (1 + ellT t) ≤ Real.exp (δ * ellT t) := by
      have := Real.add_one_le_exp (δ * ellT t)
      nlinarith
    have hsplit : Real.exp (-ellT t / 2) = Real.exp (-(δ * ellT t)) * Real.exp (-((1 - c) * ellT t)) := by
      rw [← Real.exp_add]; congr 1; rw [hδ]; ring
    rw [hsplit, ← mul_assoc]
    gcongr
    rw [le_div_iff₀ hδ0, Real.exp_neg]
    rw [mul_comm, ← mul_assoc]
    calc δ * (1 + ellT t) * (Real.exp (δ * ellT t))⁻¹ ≤ Real.exp (δ * ellT t) * (Real.exp (δ * ellT t))⁻¹ := by
          gcongr
      _ = 1 := by field_simp
  have h2 : Real.exp (-((1 - c) * ellT t)) ≤ 2 * Real.pi * t ^ (c - 1) := by
    rw [show -((1 - c) * ellT t) = (c - 1) * ellT t by ring, mul_comm, Real.exp_mul, exp_ellT ht0,
      Real.div_rpow ht0.le (by positivity)]
    rw [div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)]
    have : (2 * Real.pi) ^ (c - 1) * (2 * Real.pi) ≥ 1 := by
      rw [← Real.rpow_add_one (by positivity)]
      exact Real.one_le_rpow (by linarith [Real.pi_gt_three]) (by linarith)
    have htc : 0 ≤ t ^ (c - 1) := by positivity
    nlinarith
  calc AD * (1 + ellT t) * Real.exp (-ellT t / 2) = AD * ((1 + ellT t) * Real.exp (-ellT t / 2)) := by ring
    _ ≤ AD * (1 / δ * Real.exp (-((1 - c) * ellT t))) := by gcongr
    _ ≤ AD * (1 / δ * (2 * Real.pi * t ^ (c - 1))) := by gcongr
    _ = _ := by ring

end RamanujanTau.ZetaAFE
