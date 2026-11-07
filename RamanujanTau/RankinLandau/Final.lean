/-
# Rankin–Selberg with every exponent `δ < 2/5`, conditional on one kernel bound

`KernelOneBound m` is the single analytic input that is **not** proved here: the
stationary-phase estimate

    ‖J_1(y)‖ = ‖(1/2π) ∫ y^{3/2+it} Q_1(1/2+it) dt‖ ≪_η y^{9/8+η}         (y ≥ 1),

for the explicit `Γ`-integral `J_1 = Jc m 1 (1/2)`, `Q_1(s) = R_1(s)γₘ(1−s)`
(`Q_1(s) = π^{2s−1}(4π)^{2s−1} Γ(1−s)Γ(1−s+m)/(Γ(s+2)Γ(s+m))`). The phase-free bound
`norm_Jc_le` gives only `y^{5/4+η}`, which reproduces `δ < 1/3`.

Everything else is proved: the exact dual expansion (`dual_rep`), the kernel relations and
phase-free bounds (`KernelLine`), and Landau's differencing (`landau_core`).
-/
import RamanujanTau.RankinLandau.Core
import RamanujanTau.RankinLandau.DualB
import RamanujanTau.RankinSharpGeneral.Sharp

set_option autoImplicit false

namespace RamanujanTau.RankinLandau

open Complex Real MeasureTheory Set Filter Topology
open RamanujanTau.RankinError RamanujanTau.RankinErrorGeneral RamanujanTau.RankinSharpGeneral
open RamanujanTau.RankinSharp (chi chi_nonneg LSeriesSummable_chi LSeries_chi coe_mul_apply
  sum_a_eq_mobius mobius_transfer summable_of_LSeriesSummable LSeriesSummable_of_one_lt)
open ArithmeticFunction

/-- **The named hypothesis**: the stationary-phase bound for the first dual kernel of weight
`m + 1`, `‖J_1(y)‖ ≤ C_η y^{9/8+η}` for `y ≥ 1`. (A statement about an explicit absolutely
convergent integral of `Γ`-functions; true by the classical asymptotics of Meijer-`G` /
Voronoi kernels, Chandrasekharan–Narasimhan 1962, Lemma 6.) -/
def KernelOneBound (m : ℕ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y → ‖Jc m 1 (1 / 2) y‖ ≤ C * y ^ ((9 : ℝ) / 8 + η)

/-- The real kernel family used by `landau_core`. -/
noncomputable def Jr (m j : ℕ) (y : ℝ) : ℝ := if 1 ≤ j then (Jc m j (1 / 2) y).re else 0

lemma Rk_one (m k : ℕ) : Rk m k 1 =
    ((π * (4 * π) ^ (m + 1) / (2 * ((k : ℝ) + 1) * (m.factorial : ℝ)) : ℝ) : ℂ) := by
  have g1 : Complex.Gamma (1 + k + 1) = ((k + 1).factorial : ℂ) := by
    rw [show (1 : ℂ) + k + 1 = ((k + 1 : ℕ) : ℂ) + 1 by push_cast; ring]
    exact Complex.Gamma_nat_eq_factorial _
  have g2 : Complex.Gamma (1 + m) = (m.factorial : ℂ) := by
    rw [show (1 : ℂ) + m = (m : ℂ) + 1 by ring]
    exact Complex.Gamma_nat_eq_factorial _
  have c1 : ((4 * π : ℝ) : ℂ) ^ ((1 : ℂ) + m) = (((4 * π) ^ (m + 1) : ℝ) : ℂ) := by
    rw [show (1 : ℂ) + m = ((m + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast]; push_cast; ring
  unfold Rk
  rw [g1, g2, c1, cpow_one]
  have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hkf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  push_cast [Nat.factorial_succ]
  field_simp

/-- The exponent bookkeeping: for `δ < 2/5` the constraints of `landau_core` are met with
`ξ = (2−5δ)/32`, `α = 1/8 + ξ`, `ε = ξ`, `σ = (2−k)/4 + ξ`, `θ = 1−δ`,
`μ = (1−2δ−α)/(α+ε)` and any `k ≥ max(18, 10/(2−5δ))`. -/
lemma exponents_ok {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 2 / 5) {k : ℕ} (hk18 : 18 ≤ k)
    (hk : 10 ≤ (k : ℝ) * (2 - 5 * δ)) :
    let ξ : ℝ := (2 - 5 * δ) / 32
    let α : ℝ := 1 / 8 + ξ
    let σ : ℝ := (2 - k) / 4 + ξ
    let μ : ℝ := (1 - 2 * δ - α) / (α + ξ)
    0 < ξ ∧ 0 ≤ μ ∧ σ + ξ ≤ 0 ∧ 0 ≤ (k : ℝ) + σ ∧ σ ≤ 1 / 2 ∧ 1 - 4 * σ - k < -1 ∧
      1 + α + μ * (α + ξ) ≤ 2 * (1 - δ) ∧
      (k : ℝ) + σ + μ * (σ + ξ) ≤ ((k : ℝ) + 1) * (1 - δ) := by
  intro ξ α σ μ
  have hk18' : (18 : ℝ) ≤ k := by exact_mod_cast hk18
  have hξ : 0 < ξ := by simp only [ξ]; linarith
  have hξ1 : ξ ≤ 1 / 16 := by simp only [ξ]; linarith
  have hαξ : 0 < α + ξ := by simp only [α]; linarith
  have hnum : 0 ≤ 1 - 2 * δ - α := by simp only [α, ξ]; linarith
  refine ⟨hξ, div_nonneg hnum hαξ.le, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [σ]; linarith
  · simp only [σ]; linarith
  · simp only [σ]; linarith
  · simp only [σ]; linarith
  · have : μ * (α + ξ) = 1 - 2 * δ - α := div_mul_cancel₀ _ hαξ.ne'
    linarith
  · -- multiply by `α + ξ > 0`
    have hμ : μ * (α + ξ) = 1 - 2 * δ - α := div_mul_cancel₀ _ hαξ.ne'
    have key : ((k : ℝ) + σ) * (α + ξ) + (1 - 2 * δ - α) * (σ + ξ) ≤
        ((k : ℝ) + 1) * (1 - δ) * (α + ξ) := by
      simp only [σ, α, ξ]
      have h1 : (130 : ℝ) ≤ (k : ℝ) * (2 - 5 * δ) * (17 - 8 * δ) := by
        have : (13 : ℝ) ≤ 17 - 8 * δ := by linarith
        nlinarith
      nlinarith [sq_nonneg δ]
    have e : ((k : ℝ) + σ + μ * (σ + ξ)) * (α + ξ) =
        ((k : ℝ) + σ) * (α + ξ) + (1 - 2 * δ - α) * (σ + ξ) := by
      rw [← hμ]; ring
    have := (mul_le_mul_iff_of_pos_right hαξ).1 (e ▸ key)
    linarith

section Main

variable {m : ℕ} {a : ℕ → ℝ} {κ : ℝ}

/-- **Every `δ < 2/5`** for the weight-`(m+1)` Rankin–Selberg data, conditional on
`KernelOneBound m`. -/
theorem landau_of_RSDataM (hm : 2 ≤ m) (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 0) (hκ : 0 ≤ κ)
    (d : RSDataM m a κ)
    (habs : LSeries.abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ ((1 : ℝ) : EReal))
    (hK : KernelOneBound m) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 2 / 5) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, a n - κ * rsConstM m * N| ≤ C * (N : ℝ) ^ (1 - δ) := by
  have hm1 : 1 ≤ m := by omega
  -- the twisted coefficients `b = χ * a`
  set aF : ArithmeticFunction ℝ := ⟨a, ha0⟩ with haF
  set b : ArithmeticFunction ℝ := chi * aF with hbdef
  have hb : ∀ n, 0 ≤ b n := by
    intro n; rw [hbdef, mul_apply]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (chi_nonneg _) (ha _)
  have hb0 : b 0 = 0 := by simp
  have hbconv : (fun n => ((b n : ℝ) : ℂ)) =
      LSeries.convolution (fun n => (chi n : ℂ)) (fun n => (a n : ℂ)) := by
    funext n; rw [hbdef, coe_mul_apply]; rfl
  have hbS : ∀ w : ℂ, 1 < w.re → LSeriesSummable (fun n => ((b n : ℝ) : ℂ)) w := by
    intro w hw
    rw [hbconv]
    exact (LSeriesSummable_chi (by linarith)).convolution (LSeriesSummable_of_one_lt habs hw)
  have hbL : ∀ w : ℂ, 2 < w.re →
      LSeries (fun n => ((b n : ℝ) : ℂ)) w = riemannZeta (2 * w) * LSeries (fun n => (a n : ℂ)) w := by
    intro w hw
    rw [hbconv, LSeries_convolution' (LSeriesSummable_chi (by linarith))
      (LSeriesSummable_of_one_lt habs (by linarith)), LSeries_chi (by linarith)]
  have hsumA : LSeriesSummable (fun n => (a n : ℂ)) ((5 / 2 : ℝ) : ℂ) :=
    LSeriesSummable_of_one_lt habs (by simp; norm_num)
  -- parameters
  set ξ : ℝ := (2 - 5 * δ) / 32 with hξ
  have hgap : 0 < 2 - 5 * δ := by linarith
  set k : ℕ := max 18 ⌈10 / (2 - 5 * δ)⌉₊ with hkdef
  have hk18 : 18 ≤ k := le_max_left _ _
  have hk10 : 10 ≤ (k : ℝ) * (2 - 5 * δ) := by
    have h1 : 10 / (2 - 5 * δ) ≤ (k : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
    rwa [div_le_iff₀ hgap] at h1
  obtain ⟨hξ0, hμ0, hσε, hkσ, hσh, hσk, h1, h2⟩ := exponents_ok hδ0 hδ hk18 hk10
  set α : ℝ := 1 / 8 + ξ with hα
  set σ : ℝ := (2 - k) / 4 + ξ with hσ
  set μ : ℝ := (1 - 2 * δ - α) / (α + ξ) with hμ
  -- kernel bounds
  obtain ⟨K₁, hK₁⟩ := hK ξ hξ0
  obtain ⟨Kk, hKk0, hKk⟩ := norm_Jc_le m k hm1 hσh hσk
  set A : ℝ := |K₁| + Kk with hA
  -- the constants
  set c : ℝ := ((k : ℝ) + 1) * (κ * Rk m k 1).re with hc
  set d' : ℝ := -(κ * Rk m k 0).re with hd'
  have hc_eq : c = cB m κ := by
    rw [hc, Rk_one]
    unfold cB rsConstM
    have hpi := Real.pi_pos
    have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    simp only [← ofReal_mul, ofReal_re]
    field_simp
    ring
  have hc0 : 0 ≤ c := by rw [hc_eq]; unfold cB rsConstM; positivity
  -- the Landau hypotheses
  have hsummε : Summable fun n : ℕ => b n * (n : ℝ) ^ (-1 - ξ) := by
    have := summable_of_LSeriesSummable hb hb0 (hbS ((1 + ξ : ℝ) : ℂ) (by simp; linarith))
    simpa [show -(1 + ξ) = -1 - ξ by ring] using this
  have hJ1 : ∀ y, 1 ≤ y → |Jr m 1 y| ≤ A * y ^ (1 + α) := by
    intro y hy
    simp only [Jr, le_refl, if_true]
    refine (Complex.abs_re_le_norm _).trans ((hK₁ y hy).trans ?_)
    rw [show (9 : ℝ) / 8 + ξ = 1 + α by rw [hα]; ring]
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (by rw [hA]; linarith))
      (by positivity)
  have hJk : ∀ y, 1 ≤ y → |Jr m k y| ≤ A * y ^ ((k : ℝ) + σ) := by
    intro y hy
    simp only [Jr, show 1 ≤ k by omega, if_true]
    have hy0 : 0 < y := by linarith
    rw [← Jc_shift m k hm1 hσk (σ₁ := σ) (σ₂ := 1 / 2) le_rfl hσh hσh (by norm_num) hy0]
    refine (Complex.abs_re_le_norm _).trans ((hKk y hy0).trans ?_)
    rw [add_comm σ]
    exact mul_le_mul_of_nonneg_right (by rw [hA]; linarith [abs_nonneg K₁]) (by positivity)
  have hcont : ∀ j, ContinuousOn (Jr m j) (Ioi 0) := by
    intro j
    by_cases hj : 1 ≤ j
    · have e : Jr m j = fun y => (Jc m j (1 / 2) y).re := by funext y; simp [Jr, hj]
      rw [e]
      exact Complex.continuous_re.comp_continuousOn (continuousOn_Jc m j hm1 hj)
    · have e : Jr m j = fun _ => 0 := by funext y; simp [Jr, hj]
      rw [e]; exact continuousOn_const
  have hrel : ∀ j, 1 ≤ j → j < k → ∀ u, 0 < u → ∀ v, 0 ≤ v →
      Jr m (j + 1) (u + v) - Jr m (j + 1) u = ((j : ℝ) + 1) * ∫ w in (0 : ℝ)..v, Jr m j (u + w) := by
    intro j hj _ u hu v hv
    simp only [Jr, hj, show 1 ≤ j + 1 by omega, if_true]
    have hr := Jc_rel m j hm1 hj hu hv
    have hII : IntervalIntegrable (fun w => Jc m j (1 / 2) (u + w)) volume 0 v := by
      apply ContinuousOn.intervalIntegrable
      refine (continuousOn_Jc m j hm1 hj).comp (continuous_const.add continuous_id).continuousOn
        (fun w hw => ?_)
      rw [uIcc_of_le hv] at hw; simp only [mem_Ioi]; linarith [hw.1]
    have := congrArg Complex.re hr
    rw [Complex.sub_re] at this
    have hre : (∫ w in (0 : ℝ)..v, Jc m j (1 / 2) (u + w)).re =
        ∫ w in (0 : ℝ)..v, (Jc m j (1 / 2) (u + w)).re := by
      have h' := Complex.reCLM.intervalIntegral_comp_comm hII
      simp only [Complex.reCLM_apply] at h'
      exact h'.symm
    rw [this, show ((j : ℂ) + 1) = (((j : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul,
      hre]
  have hrep : ∀ x : ℝ, 1 ≤ x → W b k x = c * x ^ (k + 1) / ((k : ℝ) + 1) + d' * x ^ k +
      ∑' n : ℕ, b n / (n : ℝ) ^ (k + 1) * Jr m k (n * x) := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hD := dual_rep d k hm hsumA b hb hb0 hbL (hbS _ (by simp; norm_num)) hk18 hx
    -- summability of the complex dual series
    have hsumc : Summable fun n : ℕ => ((b n / (n : ℝ) ^ (k + 1) : ℝ) : ℂ) * Jc m k (1 / 2) (n * x) := by
      refine Summable.of_norm_bounded (hsummε.mul_left (Kk * x ^ (σ + k))) (fun n => ?_)
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [hb0]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < n := by linarith
      have hnx : 0 < (n : ℝ) * x := by positivity
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by have := hb n; positivity),
        ← Jc_shift m k hm1 hσk (σ₁ := σ) (σ₂ := 1 / 2) le_rfl hσh hσh (by norm_num) hnx]
      have hbn := hb n
      have hσn : (n : ℝ) ^ (σ + ξ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 hσε
      calc b n / (n : ℝ) ^ (k + 1) * ‖Jc m k σ (n * x)‖
          ≤ b n / (n : ℝ) ^ (k + 1) * (Kk * ((n : ℝ) * x) ^ (σ + k)) := by
            gcongr; exact hKk _ hnx
        _ = Kk * x ^ (σ + k) * (b n * ((n : ℝ) ^ σ / n)) := by
            rw [Real.mul_rpow hn0.le hx0.le, Real.rpow_add hn0, Real.rpow_natCast, pow_succ]
            field_simp
        _ = Kk * x ^ (σ + k) * (b n * (n : ℝ) ^ (-1 - ξ) * (n : ℝ) ^ (σ + ξ)) := by
            rw [rpow_div_self_eq hn0 σ ξ]; ring
        _ ≤ Kk * x ^ (σ + k) * (b n * (n : ℝ) ^ (-1 - ξ) * 1) := by gcongr
        _ = Kk * x ^ (σ + k) * (b n * (n : ℝ) ^ (-1 - ξ)) := by ring
    have := congrArg Complex.re hD
    rw [Complex.ofReal_re, Complex.add_re, Complex.re_tsum hsumc] at this
    rw [this]
    have e1 : ((Psi d k x 1 - Psi d k x 0) * (x : ℂ) ^ k).re =
        c * x ^ (k + 1) / ((k : ℝ) + 1) + d' * x ^ k := by
      have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
      unfold Psi
      rw [show ((x : ℂ) ^ k) = (((x ^ k : ℝ)) : ℂ) by push_cast; ring, Complex.re_mul_ofReal,
        cpow_one, cpow_zero]
      simp only [hc, hd', Complex.sub_re]
      simp only [one_mul, mul_zero, zero_mul, sub_self, zero_sub, mul_one, one_mul, zero_add]
      rw [show (x : ℂ) * Rk m k 1 * (κ : ℂ) = ((x : ℝ) : ℂ) * ((κ : ℂ) * Rk m k 1) by ring,
        Complex.re_ofReal_mul, show Rk m k 0 * (κ : ℂ) = (κ : ℂ) * Rk m k 0 by ring]
      field_simp
      ring
    rw [e1]
    congr 1
    congr 1
    funext n
    rw [Complex.re_ofReal_mul]
    simp only [Jr, show 1 ≤ k by omega, if_true]
  have H : LandauHyp b k (Jr m) c d' A σ α ξ :=
    { nonneg := hb, zero := hb0, hk := by omega, hc := hc0, hA := by positivity, hε := hξ0,
      hα := by rw [hα]; linarith, hσ := hσε, hkσ := hkσ, summ := hsummε, cont := hcont,
      rel := hrel, top := hJk, one := hJ1, rep := hrep }
  obtain ⟨C, hC⟩ := landau_core H (θ := 1 - δ) (μ := μ) (by linarith) (by linarith) hμ0 h1 h2
  -- back to `a` by Möbius
  have hIcc : ∀ M : ℕ, Finset.Icc 1 M = Finset.Ioc 0 M := by
    intro M; ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hW0 : ∀ M : ℕ, W b 0 M = ∑ n ∈ Finset.Ioc 0 M, b n := by
    intro M; unfold W; rw [Nat.floor_natCast, hIcc]; simp
  obtain ⟨C', hC'⟩ := mobius_transfer (A := fun N => ∑ n ∈ Finset.Ioc 0 N, a n)
    (B := fun M => ∑ n ∈ Finset.Ioc 0 M, b n) (c₀ := cB m κ) (C := C) (δ := δ) hδ0.le
    (by linarith) (fun N => sum_a_eq_mobius aF N) (by simp)
    (fun M hM => by
      have := hC M (by exact_mod_cast hM)
      rw [hW0, hc_eq] at this
      exact this)
  refine ⟨C', fun N hN => ?_⟩
  have := hC' N hN
  rw [hIcc]
  have e : cB m κ * (6 / π ^ 2) = κ * rsConstM m := by
    unfold cB; have := Real.pi_pos; field_simp
  rw [e] at this
  exact this

end Main

end RamanujanTau.RankinLandau

#print axioms RamanujanTau.RankinLandau.exponents_ok
#print axioms RamanujanTau.RankinLandau.landau_of_RSDataM
