/-
# Non-vanishing of the Rankin–Selberg L-function `L(Δ × Δ, s)` on the edge `Re s = 1`

Normalized: `R(s) = ∑ τ(n)² n^{−11−s}`, `H(s) = ζ(2s) R(s) = ζ(s) L(Sym²Δ, s)`.
We use the completed function `R*(s)` (`RankinSelbergFE.RStar`, continued to `ℂ ∖ {0,1}`) and put

  `HH(s) = R*(s) γ(s)⁻¹`  (holomorphic on `ℂ ∖ {0,1}`; `= ζ(2s)R(s)` on `Re s > 1`),
  `KK(s) = (s−1) HH(s)`   (extended to an entire-on-`s ≠ 0` function, `KK(1) = ‖Δ‖²γ(1)⁻¹ ≠ 0`).

**Theorem** (`HH_ne_zero_edge`): `HH(1+it) ≠ 0` for real `t ≠ 0`.
Proof: the classical 3–4–1 argument.  `log HH(s) = ∑ cR(n) n^{−s}` with `cR ≥ 0`
(`RSLog.exp_LSeries_cR`, no Deligne), and `Re(3 + 4n^{−it} + n^{−2it}) = 2(1 + cos)² ≥ 0`, so
`‖HH(σ)³ HH(σ+it)⁴ HH(σ+2it)‖ ≥ 1` for `σ > 1`.  A zero at `1+it` gives `O(σ−1)⁴`, against the
simple pole `O((σ−1)^{−3})` and the bounded `HH(σ+2it)` (holomorphic at `1+2it`).

Corollaries:
* `Rcont_ne_zero_edge`: `R(1+it) ≠ 0` (the continued Rankin–Selberg series), `t ≠ 0`;
* `Lsym2_ne_zero_edge`: `L(Sym²Δ, 1+it) := HH(1+it)/ζ(1+it) ≠ 0`, `t ≠ 0`;
* `KK_ne_zero`: `KK(s) ≠ 0` on `Re s ≥ 1`;
* `continuousOn_negLogDerivK`, `negLogDerivK_eq`: `−KK'/KK` is continuous on `Re s ≥ 1` and equals
  `∑ vR(n) n^{−s} − 1/(s−1)` on `Re s > 1` (input for Wiener–Ikehara).
-/
import RamanujanTau.TauPNTUncond.RSLog
import RamanujanTau.RankinSelbergFE.Proper

set_option autoImplicit false

namespace RamanujanTau.TauPNTUncond

open Complex Filter Topology LSeries
open RamanujanTau.EdgeNonvanishing RamanujanTau.TauPNT RamanujanTau.RankinSelbergFE
open RamanujanTau.RankinError (invGam gam gam_mul_invGam differentiable_invGam)
open RamanujanTau.EisensteinReal (petNormSq)

/-- `HH(s) = R*(s)/γ(s)`, i.e. `ζ(2s)R(s)` continued. -/
noncomputable def HH (s : ℂ) : ℂ := RStar s * invGam s

/-- `KK(s) = (s−1)·HH(s)`, with the removable singularity at `s = 1` filled in. -/
noncomputable def KK (s : ℂ) : ℂ :=
  ((s - 1) * RStar₀ s - (petNormSq : ℂ) * (s - 1) / s + (petNormSq : ℂ)) * invGam s

lemma HH_eq {s : ℂ} (hs : 1 < s.re) : HH s = riemannZeta (2 * s) * RS s := by
  have hg := gam_mul_invGam (s := s) (by linarith)
  rw [HH, RStar_eq_of_one_lt hs]
  linear_combination (riemannZeta (2 * s) * RS s) * hg

lemma HH_exp {s : ℂ} (hs : 1 < s.re) : HH s = cexp (LSeries (fun n => (cR n : ℂ)) s) := by
  rw [HH_eq hs, exp_LSeries_cR hs]

lemma HH_ne_zero_of_gt {s : ℂ} (hs : 1 < s.re) : HH s ≠ 0 := by
  rw [HH_exp hs]; exact Complex.exp_ne_zero _

lemma differentiableAt_HH {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : DifferentiableAt ℂ HH s :=
  (differentiableAt_RStar h0 h1).mul (differentiable_invGam s)

lemma KK_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : KK s = (s - 1) * HH s := by
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1'' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [KK, HH, RStar_eq]
  field_simp
  ring

lemma differentiableAt_KK {s : ℂ} (h0 : s ≠ 0) : DifferentiableAt ℂ KK s := by
  unfold KK
  exact ((((differentiableAt_id.sub_const 1).mul (differentiable_RStar₀ s)).sub
    (((differentiableAt_const _).mul (differentiableAt_id.sub_const 1)).div differentiableAt_id
      h0)).add (differentiableAt_const _)).mul (differentiable_invGam s)

lemma invGam_one_ne : invGam 1 ≠ 0 := by
  intro h
  have := gam_mul_invGam (s := 1) (by norm_num)
  rw [h, mul_zero] at this
  exact zero_ne_one this

lemma KK_one : KK 1 = (petNormSq : ℂ) * invGam 1 := by
  simp [KK]

lemma KK_one_ne : KK 1 ≠ 0 := by
  rw [KK_one]; exact mul_ne_zero petNormSq_ne_zero invGam_one_ne

/-! ### Global positivity: the 3–4–1 inequality -/

lemma re_comb_nonneg (w : ℂ) (hw : ‖w‖ = 1) : 0 ≤ (3 + 4 * w + w ^ 2).re := by
  have h : w.re * w.re + w.im * w.im = 1 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, hw, one_pow]
  have e : (3 + 4 * w + w ^ 2).re = 3 + 4 * w.re + (w.re * w.re - w.im * w.im) := by
    simp [sq, Complex.add_re, Complex.mul_re]
  rw [e]
  nlinarith [sq_nonneg (w.re + 1)]

lemma term_shift (f : ℕ → ℂ) (σ u : ℝ) {n : ℕ} (hn : n ≠ 0) :
    term f ((σ : ℂ) + (u : ℂ) * I) n = term f σ n * (n : ℂ) ^ (-((u : ℂ) * I)) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [term_of_ne_zero hn, term_of_ne_zero hn, cpow_add _ _ hn', cpow_neg]
  rw [div_mul_eq_div_div, div_eq_mul_inv (f n / (n : ℂ) ^ (σ : ℂ))]

lemma npow_two_shift {n : ℕ} (t : ℝ) :
    (n : ℂ) ^ (-(((2 * t : ℝ) : ℂ) * I)) = ((n : ℂ) ^ (-((t : ℂ) * I))) ^ 2 := by
  rw [← cpow_nat_mul]; congr 1; push_cast; ring

/-- `‖HH(σ)³ HH(σ+it)⁴ HH(σ+2it)‖ ≥ 1` for `σ > 1`. -/
theorem one_le_norm_comb {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    1 ≤ ‖HH σ ^ 3 * HH ((σ : ℂ) + (t : ℂ) * I) ^ 4 * HH ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ := by
  set f : ℕ → ℂ := fun n => (cR n : ℂ)
  set s1 : ℂ := (σ : ℂ) + (t : ℂ) * I
  set s2 : ℂ := (σ : ℂ) + ((2 * t : ℝ) : ℂ) * I
  have hre0 : 1 < (σ : ℂ).re := by simpa using hσ
  have hre1 : 1 < s1.re := by simp [s1]; linarith
  have hre2 : 1 < s2.re := by simp [s2]; linarith
  have h0 := (LSeriesSummable_cR hre0).LSeriesHasSum
  have h1 := (LSeriesSummable_cR hre1).LSeriesHasSum
  have h2 := (LSeriesSummable_cR hre2).LSeriesHasSum
  set Z := 3 * LSeries f σ + 4 * LSeries f s1 + LSeries f s2
  have hZ : HasSum (fun n => 3 * term f σ n + 4 * term f s1 n + term f s2 n) Z :=
    ((h0.mul_left 3).add (h1.mul_left 4)).add h2
  have hZre := Complex.hasSum_re hZ
  have hnn : ∀ n, 0 ≤ (3 * term f σ n + 4 * term f s1 n + term f s2 n).re := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [term_shift f σ t hn, term_shift f σ (2 * t) hn, npow_two_shift]
    set w := (n : ℂ) ^ (-((t : ℂ) * I))
    have hw : ‖w‖ = 1 := by
      simp only [w]; rw [norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]; simp
    have hT : term f σ n = ((cR n * ((n : ℝ) ^ σ)⁻¹ : ℝ) : ℂ) := by
      rw [term_of_ne_zero hn]
      simp only [f]
      rw [show ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) by
        rw [Complex.ofReal_cpow (by positivity)]; push_cast; rfl]
      push_cast; ring
    have e : 3 * term f σ n + 4 * (term f σ n * w) + term f σ n * w ^ 2 =
        ((cR n * ((n : ℝ) ^ σ)⁻¹ : ℝ) : ℂ) * (3 + 4 * w + w ^ 2) := by rw [hT]; ring
    rw [e, Complex.re_ofReal_mul]
    exact mul_nonneg (mul_nonneg (cR_nonneg n) (by positivity)) (re_comb_nonneg w hw)
  have hZnn : 0 ≤ Z.re := hZre.nonneg hnn
  have hprod : HH σ ^ 3 * HH s1 ^ 4 * HH s2 = cexp Z := by
    rw [HH_exp hre0, HH_exp hre1, HH_exp hre2]
    simp only [Z, Complex.exp_add]
    rw [show (3 : ℂ) * LSeries f σ = ((3 : ℕ) : ℂ) * LSeries f σ by norm_num,
      show (4 : ℂ) * LSeries f s1 = ((4 : ℕ) : ℂ) * LSeries f s1 by norm_num,
      Complex.exp_nat_mul, Complex.exp_nat_mul]
  rw [hprod, Complex.norm_exp]
  exact Real.one_le_exp hZnn

/-! ### The edge -/

/-- **`ζ(2s)R(s)` (continued) has no zero on `Re s = 1`, `s ≠ 1`.** -/
theorem HH_ne_zero_edge {t : ℝ} (ht : t ≠ 0) : HH (1 + (t : ℂ) * I) ≠ 0 := by
  intro h0
  set a1 : ℂ := 1 + (t : ℂ) * I
  set a2 : ℂ := 1 + ((2 * t : ℝ) : ℂ) * I
  have hne : ∀ u : ℝ, u ≠ 0 → (1 + (u : ℂ) * I ≠ 0 ∧ 1 + (u : ℂ) * I ≠ 1) := by
    intro u hu
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := congrArg Complex.re h; simp at this
    · have := congrArg Complex.im h; simp at this; exact hu this
  have ht2 : (2 * t : ℝ) ≠ 0 := by positivity
  obtain ⟨Ca, hCa⟩ := zero_bound (differentiableAt_HH (hne t ht).1 (hne t ht).2) h0
  have hc2 := cont_bound (g := HH) (a := a2) (b := 1)
    (differentiableAt_HH (hne _ ht2).1 (hne _ ht2).2).continuousAt
  have hcK := cont_bound (g := KK) (a := 1) (b := 1) (differentiableAt_KK one_ne_zero).continuousAt
  set M : ℝ := |Ca| ^ 4 * (‖KK 1‖ + 1) ^ 3 * (‖HH a2‖ + 1)
  have hM : 0 ≤ M := by positivity
  have hsmallE : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x ∈ Set.Ioo 0 (1 / (M + 1)) :=
    Ioo_mem_nhdsGT (by positivity)
  have hposE : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x ∈ Set.Ioi 0 := eventually_mem_nhdsWithin
  obtain ⟨h, ha, hb, hk, hpos, hsmall⟩ :=
    (hCa.and (hc2.and (hcK.and (hposE.and hsmallE)))).exists
  have hpos : 0 < h := hpos
  have hsm : h < 1 / (M + 1) := hsmall.2
  have hF := one_le_norm_comb (σ := 1 + h) (by linarith) t
  have e0 : ((1 + h : ℝ) : ℂ) = 1 + 1 * (h : ℂ) := by push_cast; ring
  have e1 : ((1 + h : ℝ) : ℂ) + (t : ℂ) * I = a1 + (h : ℂ) := by simp only [a1]; push_cast; ring
  have e2 : ((1 + h : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I = a2 + 1 * (h : ℂ) := by
    simp only [a2]; push_cast; ring
  rw [e1, e2, e0] at hF
  have hH0 : ‖HH (1 + 1 * (h : ℂ))‖ ≤ (‖KK 1‖ + 1) / h := by
    have hs0 : (1 : ℂ) + 1 * (h : ℂ) ≠ 0 := by
      intro hh; have := congrArg Complex.re hh; simp at this; linarith
    have hs1 : (1 : ℂ) + 1 * (h : ℂ) ≠ 1 := by
      intro hh; have := congrArg Complex.re hh; simp at this; linarith
    have hK := KK_eq hs0 hs1
    have hsub : (1 : ℂ) + 1 * (h : ℂ) - 1 = (h : ℂ) := by ring
    rw [hsub] at hK
    rw [le_div_iff₀ hpos]
    have : ‖KK (1 + 1 * (h : ℂ))‖ = ‖HH (1 + 1 * (h : ℂ))‖ * h := by
      rw [hK, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, mul_comm]
    linarith
  rw [norm_mul, norm_mul, norm_pow, norm_pow] at hF
  have ha' : ‖HH (a1 + (h : ℂ))‖ ≤ |Ca| * h :=
    ha.trans (mul_le_mul_of_nonneg_right (le_abs_self Ca) hpos.le)
  have key : 1 ≤ ((‖KK 1‖ + 1) / h) ^ 3 * (|Ca| * h) ^ 4 * (‖HH a2‖ + 1) := by
    refine hF.trans ?_
    gcongr
  have hval : ((‖KK 1‖ + 1) / h) ^ 3 * (|Ca| * h) ^ 4 * (‖HH a2‖ + 1) = M * h := by
    simp only [M]; field_simp
  rw [hval] at key
  have : M * h < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hsm
    nlinarith
  linarith

/-- `KK ≠ 0` on the closed half-plane `Re s ≥ 1`. -/
theorem KK_ne_zero {s : ℂ} (hs : 1 ≤ s.re) : KK s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  by_cases h1 : s = 1
  · rw [h1]; exact KK_one_ne
  rw [KK_eq hs0 h1]
  refine mul_ne_zero (sub_ne_zero.mpr h1) ?_
  rcases hs.lt_or_eq with hs' | hs'
  · exact HH_ne_zero_of_gt hs'
  · have him : s.im ≠ 0 := by
      intro him; apply h1; apply Complex.ext <;> simp [← hs', him]
    have : s = 1 + (s.im : ℂ) * I := by apply Complex.ext <;> simp [← hs']
    rw [this]; exact HH_ne_zero_edge him

/-- **The continued Rankin–Selberg series `R(s) = ∑ τ(n)² n^{−11−s}` has no zero on
`Re s = 1`** (`s ≠ 1`). -/
theorem Rcont_ne_zero_edge {t : ℝ} (ht : t ≠ 0) : Rcont (1 + (t : ℂ) * I) ≠ 0 := by
  set s : ℂ := 1 + (t : ℂ) * I
  have hζ : riemannZeta (2 * s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp [s])
  have : Rcont s = HH s / riemannZeta (2 * s) := by
    simp only [Rcont, HH]
  rw [this]
  exact div_ne_zero (HH_ne_zero_edge ht) hζ

/-- `L(Sym²Δ, s) := ζ(2s)R(s)/ζ(s)` (local factors `((1−α²Y)(1−Y)(1−β²Y))⁻¹`). -/
noncomputable def Lsym2 (s : ℂ) : ℂ := HH s / riemannZeta s

/-- **`L(Sym²Δ, 1+it) ≠ 0` for `t ≠ 0`** (Shimura / Gelbart–Jacquet edge non-vanishing). -/
theorem Lsym2_ne_zero_edge {t : ℝ} (ht : t ≠ 0) : Lsym2 (1 + (t : ℂ) * I) ≠ 0 := by
  have hζ : riemannZeta (1 + (t : ℂ) * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp)
  exact div_ne_zero (HH_ne_zero_edge ht) hζ

/-- `L(Sym²Δ, s) → KK(1) ≠ 0` as `s → 1`: no zero (and no pole) at `s = 1`. -/
theorem Lsym2_tendsto_one :
    Tendsto Lsym2 (𝓝[≠] 1) (𝓝 (KK 1)) ∧ KK 1 ≠ 0 := by
  refine ⟨?_, KK_one_ne⟩
  have hK : Tendsto KK (𝓝[≠] 1) (𝓝 (KK 1)) :=
    ((differentiableAt_KK one_ne_zero).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hz := riemannZeta_residue_one
  have := hK.div hz one_ne_zero
  rw [div_one] at this
  refine this.congr' ?_
  have h0 : ∀ᶠ s in 𝓝[≠] (1 : ℂ), s ≠ 0 :=
    (eventually_ne_nhds one_ne_zero).filter_mono nhdsWithin_le_nhds
  filter_upwards [h0, self_mem_nhdsWithin] with s hs0 hs1
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  simp only [Pi.div_apply]
  rw [Lsym2, KK_eq hs0 hs1]
  by_cases hz0 : riemannZeta s = 0
  · simp [hz0]
  · field_simp

/-! ### `−KK'/KK` on the closed half-plane -/

/-- `−KK'/KK`. -/
noncomputable def negLogDerivK (s : ℂ) : ℂ := -deriv KK s / KK s

lemma differentiableOn_KK : DifferentiableOn ℂ KK {s : ℂ | 0 < s.re} := fun s hs =>
  (differentiableAt_KK (fun h => by rw [h] at hs; simp at hs)).differentiableWithinAt

theorem continuousOn_negLogDerivK : ContinuousOn negLogDerivK {s | 1 ≤ s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd := differentiableOn_KK.deriv hopen
  intro s hs
  have hs1 : 1 ≤ s.re := hs
  have hs0 : s ∈ {s : ℂ | 0 < s.re} := by simp only [Set.mem_setOf_eq]; linarith
  have h1 : ContinuousAt (deriv KK) s := (hd.differentiableAt (hopen.mem_nhds hs0)).continuousAt
  have h2 : ContinuousAt KK s :=
    (differentiableAt_KK (fun h => by rw [h] at hs1; simp at hs1; linarith)).continuousAt
  exact (h1.neg.div h2 (KK_ne_zero hs1)).continuousWithinAt

theorem negLogDerivK_eq {s : ℂ} (hs : 1 < s.re) :
    negLogDerivK s = LSeries (fun n => (vR n : ℂ)) s - 1 / (s - 1) := by
  set G := LSeries (fun n => (cR n : ℂ))
  have hab : abscissaOfAbsConv (fun n => (cR n : ℂ)) < s.re :=
    abscissa_cR_le.trans_lt (by exact_mod_cast hs)
  have hG : HasDerivAt G (-LSeries (logMul fun n => (cR n : ℂ)) s) s := LSeries_hasDerivAt hab
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hne : ∀ z : ℂ, 1 < z.re → z ≠ 0 ∧ z ≠ 1 := fun z hz =>
    ⟨fun h => by rw [h] at hz; simp at hz; linarith, fun h => by rw [h] at hz; simp at hz⟩
  have hev : (fun z => (z - 1) * cexp (G z)) =ᶠ[𝓝 s] KK := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    rw [KK_eq (hne z hz).1 (hne z hz).2, HH_exp hz]
  have hd : HasDerivAt KK (1 * cexp (G s) + (s - 1) * (cexp (G s) *
      -LSeries (logMul fun n => (cR n : ℂ)) s)) s :=
    (((hasDerivAt_id' s).sub_const 1).mul hG.cexp).congr_of_eventuallyEq hev.symm
  rw [negLogDerivK, hd.deriv, KK_eq (hne s hs).1 (hne s hs).2, HH_exp hs, vR_eq_logMul]
  have h0 : cexp (G s) ≠ 0 := Complex.exp_ne_zero _
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr (hne s hs).2
  field_simp
  ring

end RamanujanTau.TauPNTUncond
