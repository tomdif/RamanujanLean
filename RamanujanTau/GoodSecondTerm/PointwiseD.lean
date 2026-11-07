/-
# Pointwise: `|L(Δ,6+it)|² = D(t) + O(t) + O(t^{−1/2})`, and `D(t) = 2c₀ log(t/2π) + 2γ_Δ + O(t^{−1/10})`

(line `c = 3/4`). `D(t)` is the diagonal `m = n`, `O(t)` the off-diagonal sum (`OftD`).
-/
import RamanujanTau.GoodSecondTerm.DiagD2
import RamanujanTau.ZetaAFE.Pointwise

set_option autoImplicit false

namespace RamanujanTau.GoodSecondTerm

open Complex MeasureTheory Set Filter Topology
open RamanujanTau.ZetaAFE RamanujanTau.HeckeL

/-- Off-diagonal coefficients at `ℓ = 2 log(t/2π)`. -/
noncomputable def boD (t : ℝ) (p : ℕ × ℕ) : ℂ := if p.1 = p.2 then 0 else bD t (2 * ellT t) p

/-- The off-diagonal sum `O(t) = Σ_{m≠n} τ(m)τ(n)(mn)^{−6}(n/m)^{it} V(log(mn) − 2 log(t/2π))`. -/
noncomputable def OftD (t : ℝ) : ℂ := ∑' p, boD t p

lemma bD_diag (t ℓ : ℝ) (n : ℕ) :
    bD t ℓ (n, n) = ((bb (n + 1) / ((n : ℝ) + 1) * V (2 * lg n - ℓ) : ℝ) : ℂ) := by
  unfold bD coefD
  simp only [sub_self, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : Real.exp (-(6 * (lg n + lg n))) = (((n : ℝ) + 1) ^ 12)⁻¹ := by
    rw [show -(6 * (lg n + lg n)) = -(Real.log (((n : ℝ) + 1) ^ 12)) by
      rw [Real.log_pow]; unfold lg; push_cast; ring, Real.exp_neg, Real.exp_log (by positivity)]
  rw [h1, show 2 * lg n - ℓ = lg n + lg n - ℓ by ring]
  unfold bb
  push_cast
  field_simp

lemma tsum_bD_split (t : ℝ) :
    ∑' p, bD t (2 * ellT t) p = (DsumD (2 * ellT t) : ℂ) + OftD t := by
  set bd : ℕ × ℕ → ℂ := fun p => if p.1 = p.2 then bD t (2 * ellT t) p else 0 with hbd
  have hsplit : ∀ p, bD t (2 * ellT t) p = bd p + boD t p := by
    intro p; simp only [hbd, boD]; split_ifs <;> simp
  have hS := summable_bD t (2 * ellT t)
  have hsd : Summable bd := Summable.of_norm_bounded hS.norm (fun p => by
    simp only [hbd]; split_ifs <;> simp)
  have hso : Summable (boD t) := Summable.of_norm_bounded hS.norm (fun p => by
    simp only [boD]; split_ifs <;> simp)
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
  simp_rw [bD_diag]
  unfold DsumD
  rw [Complex.ofReal_tsum]

/-- **Pointwise Δ-AFE error** (line `c = 3/4`): `O(t^{−1/2})`. -/
theorem pointwise_err_D :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ t : ℝ, 16 ≤ t →
      ‖((‖tauL (6 + t * I)‖ ^ 2 : ℝ) : ℂ) - (DsumD (2 * ellT t) : ℂ) - OftD t‖ ≤
        CE * t ^ (-(1 / 2 : ℝ)) := by
  set c : ℝ := 3 / 4 with hcdef
  obtain ⟨K, hK0, hK⟩ := gamma_ratio_delta (c := c) (by norm_num) (by norm_num)
  set Cc : ℝ := Real.exp (c ^ 2) * Real.sqrt (2 * Real.pi) / c with hCc
  refine ⟨K * Cc / Real.pi * Ztau (6 + c) ^ 2, by positivity, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hRc := continuous_RtD_line t (c := c) (by norm_num)
  have hB : ∀ y : ℝ, ‖RtD t (c + y * I) * cexp (-(((c : ℂ) + y * I) * ((2 * ellT t : ℝ) : ℂ))) - 1‖ ≤
      (K / t ^ 2) * Real.exp (y ^ 2 / 2) := by
    intro y
    have h := hK t y ht
    have e : -(((c : ℂ) + y * I) * ((2 * ellT t : ℝ) : ℂ)) = -(2 * ((c : ℂ) + y * I) * (ellT t : ℂ)) := by
      push_cast; ring
    rw [e]
    calc _ ≤ K * Real.exp (y ^ 2 / 2) / t ^ 2 := h
      _ = _ := by ring
  have hR : ∀ y : ℝ, ‖RtD t (c + y * I)‖ ≤
      ((1 + K / t ^ 2) * Real.exp (c * (2 * ellT t))) * Real.exp (y ^ 2 / 2) := by
    intro y
    have h1 : RtD t (c + y * I) = (RtD t (c + y * I) * cexp (-(((c : ℂ) + y * I) * ((2 * ellT t : ℝ) : ℂ)))) *
        cexp (((c : ℂ) + y * I) * ((2 * ellT t : ℝ) : ℂ)) := by
      rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    rw [h1, norm_mul]
    have h2 : ‖cexp (((c : ℂ) + y * I) * ((2 * ellT t : ℝ) : ℂ))‖ = Real.exp (c * (2 * ellT t)) := by
      rw [Complex.norm_exp]; congr 1; simp
    have h3 : ‖RtD t (c + y * I) * cexp (-(((c : ℂ) + y * I) * ((2 * ellT t : ℝ) : ℂ)))‖ ≤
        (1 + K / t ^ 2) * Real.exp (y ^ 2 / 2) := by
      have := hB y
      have h4 := norm_sub_norm_le
        (RtD t (c + y * I) * cexp (-(((c : ℂ) + y * I) * ((2 * ellT t : ℝ) : ℂ)))) 1
      have h5 : 1 ≤ Real.exp (y ^ 2 / 2) := Real.one_le_exp (by positivity)
      rw [norm_one] at h4
      nlinarith
    rw [h2]
    calc _ ≤ (1 + K / t ^ 2) * Real.exp (y ^ 2 / 2) * Real.exp (c * (2 * ellT t)) := by gcongr
      _ = _ := by ring
  have happrox := delta_sq_approx (by norm_num) (by norm_num) hRc hR hB
  rw [tsum_bD_split] at happrox
  rw [sub_sub]
  refine happrox.trans ?_
  have hexp : Real.exp (c * (2 * ellT t)) ≤ t ^ (3 / 2 : ℝ) := by
    rw [show c * (2 * ellT t) = (3 / 2) * ellT t by rw [hcdef]; ring]
    exact exp_c_ellT_le (by norm_num) ht0
  have htc : t ^ (3 / 2 : ℝ) / t ^ 2 = t ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub ht0]; norm_num
  have hZ : 0 ≤ Ztau (6 + c) ^ 2 := sq_nonneg _
  calc K / t ^ 2 * Cc / Real.pi * Real.exp (c * (2 * ellT t)) * Ztau (6 + c) ^ 2
      ≤ K / t ^ 2 * Cc / Real.pi * t ^ (3 / 2 : ℝ) * Ztau (6 + c) ^ 2 := by gcongr
    _ = K * Cc / Real.pi * Ztau (6 + c) ^ 2 * (t ^ (3 / 2 : ℝ) / t ^ 2) := by ring
    _ = _ := by rw [htc]

/-- **Diagonal, pointwise**: `|D(t) − 2c₀ log(t/2π) − 2γ_Δ| ≤ C t^{−1/10}`. -/
theorem diag_err_D :
    ∃ CD : ℝ, 0 ≤ CD ∧ ∀ t : ℝ, 16 ≤ t →
      |DsumD (2 * ellT t) - 2 * c0 * ellT t - 2 * gammaD| ≤ CD * t ^ (-(1 / 10 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := abs_DsumD_sub_le
  refine ⟨40 * C, by positivity, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hℓ : 0 ≤ ellT t := Real.log_nonneg (by
    rw [le_div_iff₀ (by positivity)]; linarith [Real.pi_lt_four])
  have h := hC (2 * ellT t)
  rw [show c0 * (2 * ellT t) = 2 * c0 * ellT t by ring, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * ellT t)] at h
  refine h.trans ?_
  -- (1 + 2ℓ) e^{−ℓ/5} ≤ 20 e^{−ℓ/10} ≤ 40 t^{−1/10}
  have h1 : 1 + 2 * ellT t ≤ 20 * Real.exp (ellT t / 10) := by
    have := Real.add_one_le_exp (ellT t / 10); linarith
  have h2 : Real.exp (ellT t / 10) * Real.exp (-(2 * ellT t) / 10) = Real.exp (-(ellT t / 10)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (-(ellT t / 10)) ≤ 2 * t ^ (-(1 / 10 : ℝ)) := by
    rw [show -(ellT t / 10) = ellT t * (-(1 / 10 : ℝ)) by ring, Real.exp_mul, exp_ellT ht0,
      Real.div_rpow ht0.le (by positivity), Real.rpow_neg (by positivity : (0:ℝ) ≤ 2 * Real.pi),
      div_inv_eq_mul]
    have hpow : (2 * Real.pi) ^ (1 / 10 : ℝ) ≤ 2 := by
      calc (2 * Real.pi) ^ (1 / 10 : ℝ) ≤ ((2 : ℝ) ^ (10 : ℕ)) ^ (1 / 10 : ℝ) :=
            Real.rpow_le_rpow (by positivity) (by norm_num; nlinarith [Real.pi_lt_four]) (by norm_num)
        _ = 2 := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have htp : 0 ≤ t ^ (-(1 / 10 : ℝ)) := by positivity
    nlinarith
  have hE := Real.exp_pos (-(ellT t / 10))
  calc C * (1 + 2 * ellT t) * Real.exp (-(2 * ellT t) / 10)
      ≤ C * (20 * Real.exp (ellT t / 10)) * Real.exp (-(2 * ellT t) / 10) := by gcongr
    _ = 20 * C * (Real.exp (ellT t / 10) * Real.exp (-(2 * ellT t) / 10)) := by ring
    _ = 20 * C * Real.exp (-(ellT t / 10)) := by rw [h2]
    _ ≤ 20 * C * (2 * t ^ (-(1 / 10 : ℝ))) := by gcongr
    _ = _ := by ring

end RamanujanTau.GoodSecondTerm
