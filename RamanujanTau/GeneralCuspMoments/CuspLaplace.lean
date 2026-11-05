/-
# Good's asymptotic for a level-one cusp form of weight `k = 2p + 2`

With `λ = π − 2β` and the exact Gamma weight (`Gamma.lean`),

    ∫ |Λ(f,k/2+it)|² e^{2βt} dt = N(β) + ∫_0^∞ kΓ(t) e^{−λt} |L(f,k/2+it)|² dt,

`t^{k−1}/(2π)^{k−1} ≤ kΓ(t) ≤ (1+ν) t^{k−1}/(2π)^{k−1} + C_ν 1_{t ≤ T_ν}`, and the weighted
asymptotic `weighted_asymptotic_f` give the Laplace asymptotic

    λ^k ∫_0^∞ t^{k−1} e^{−λt} |L(f,k/2+it)|² dt / log(1/λ) → Kc f = (2π)^{k−1} 2^k · 12‖f‖²,

and the abstract Tauberian step `tendsto_of_laplace` (`n = k − 1`) gives

    ∫_0^T |L(f,k/2+it)|² dt / (T log T) → Kc f / (k−1)! = 2 · rsConst f.
-/
import RamanujanTau.GeneralCuspMoments.CuspRay
import RamanujanTau.GeneralCuspMoments.Gamma
import RamanujanTau.GeneralCuspMoments.Tauber
import RamanujanTau.RankinSelbergGeneral.Positive

set_option autoImplicit false

namespace RamanujanTau.GeneralCuspMoments

open Complex ModularForm MeasureTheory Set Filter Topology
open UpperHalfPlane hiding I
open RamanujanTau.HeckeConvexGeneral RamanujanTau.HardyZerosGeneral
open scoped MatrixGroups Real

variable {p : ℕ}

/-- `|L(f, k/2+it)|²`. -/
noncomputable def Lsq (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (t : ℝ) : ℝ :=
  ‖fL f (sc (2 * p + 2) t)‖ ^ 2

lemma continuous_Lsq (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) : Continuous (Lsq f) :=
  ((fL_entire f (by omega)).continuous.comp (by unfold sc; fun_prop)).norm.pow 2

lemma Lsq_nonneg (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (t : ℝ) : 0 ≤ Lsq f t := sq_nonneg _

/-- The weighted integrand `|Λ(f,k/2+it)|² e^{2βt}`. -/
noncomputable def fW (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (β t : ℝ) : ℝ :=
  ‖heckeLambda f (sc (2 * p + 2) t)‖ ^ 2 * Real.exp (2 * β * t)

lemma continuous_fW (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (β : ℝ) : Continuous (fW f β) :=
  ((continuous_heckeLambda_line f (by omega)).norm.pow 2).mul (by fun_prop)

lemma fW_nonneg (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (β t : ℝ) : 0 ≤ fW f β t := by
  unfold fW; positivity

lemma integrable_fW (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ : β < π / 2) : Integrable (fW f β) := by
  obtain ⟨C, hC⟩ := heckeLambda_line_decay f hk hβ
  refine (integrable_inv_one_add_sq.const_mul (C ^ 2)).mono'
    (continuous_fW f β).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (fW_nonneg f β t)]
  set a := ‖heckeLambda f (sc (2 * p + 2) t)‖
  set e := Real.exp (β * |t|)
  set q := (1 + t ^ 2)⁻¹
  have ha : 0 ≤ a := norm_nonneg _
  have he : 0 < e := Real.exp_pos _
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg t])
  have h1 := hC t
  have hae : a * e ≤ C * q := by
    have : a * e ≤ a * (1 + |t|) * e := by
      have := abs_nonneg t
      nlinarith [mul_nonneg ha he.le]
    linarith
  have hae0 : 0 ≤ a * e := by positivity
  have hexp : Real.exp (2 * β * t) ≤ e ^ 2 := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have : β * t ≤ β * |t| := mul_le_mul_of_nonneg_left (le_abs_self t) hβ0
    push_cast; linarith
  unfold fW
  calc a ^ 2 * Real.exp (2 * β * t) ≤ a ^ 2 * e ^ 2 := by gcongr
    _ = (a * e) ^ 2 := by ring
    _ ≤ (C * q) ^ 2 := pow_le_pow_left₀ hae0 hae 2
    _ = C ^ 2 * q * q := by ring
    _ ≤ C ^ 2 * q * 1 := by gcongr
    _ = C ^ 2 * q := mul_one _

lemma sc_eq (t : ℝ) : sc (2 * p + 2) t = (p : ℂ) + 1 + t * I := by
  unfold sc; rw [half_k]; push_cast; ring

lemma norm_heckeLambda_sq (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) {t : ℝ} (ht : t ≠ 0) :
    ‖heckeLambda f (sc (2 * p + 2) t)‖ ^ 2 =
      Pq p t * (π * t / Real.sinh (π * t)) / (2 * π) ^ (2 * p + 2) * Lsq f t := by
  have hs := sc_ne_neg_nat (k := 2 * p + 2) (by omega) t
  rw [heckeLambda_eq_fL f hs, norm_mul, norm_mul, mul_pow, mul_pow, sc_eq, norm_Gamma_sq p ht]
  have h2π : ‖(2 * π : ℂ) ^ (-((p : ℂ) + 1 + t * I))‖ = ((2 * π) ^ (p + 1))⁻¹ := by
    have e : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
    rw [e, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have hre : (-((p : ℂ) + 1 + t * I)).re = -(((p + 1 : ℕ) : ℝ)) := by simp
    rw [hre, Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [h2π]
  unfold Lsq
  rw [sc_eq]
  have : (0 : ℝ) < (2 * π) ^ (p + 1) := by positivity
  have hpow : (2 * π) ^ (2 * p + 2) = ((2 * π) ^ (p + 1)) ^ 2 := by ring
  rw [hpow]
  field_simp

/-- **The weight identity**, `t ≠ 0`. -/
lemma weight_eq (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) {t : ℝ} (ht : t ≠ 0) (β : ℝ) :
    fW f β t = kG p t * Real.exp (-((π - 2 * β) * t)) * Lsq f t := by
  unfold fW
  rw [norm_heckeLambda_sq f ht]
  unfold kG
  have : Real.exp (2 * β * t) = Real.exp (π * t) * Real.exp (-((π - 2 * β) * t)) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]; ring

lemma fW_eq (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) {t : ℝ} (ht : t ≠ 0) (l : ℝ) :
    fW f ((π - l) / 2) t = kG p t * Real.exp (-(l * t)) * Lsq f t := by
  rw [weight_eq f ht]; congr 3; ring

/-- The Laplace transform `∫_0^∞ t^{2p+1} |L|² e^{−λt} dt`. -/
noncomputable def Lap (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (l : ℝ) : ℝ :=
  LapG (Lsq f) (2 * p + 1) l

/-- The Gamma-weighted transform `∫_0^∞ kΓ(t) e^{−λt} |L|² dt`. -/
noncomputable def KGL (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (l : ℝ) : ℝ :=
  ∫ x in Ioi 0, kG p x * Real.exp (-(l * x)) * Lsq f x

lemma integrableOn_KGL (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) {l : ℝ}
    (hl0 : 0 < l) (hl : l < π) :
    IntegrableOn (fun x => kG p x * Real.exp (-(l * x)) * Lsq f x) (Ioi 0) := by
  have hi := (integrable_fW f hk (β := (π - l) / 2) (by linarith) (by linarith)).integrableOn
    (s := Ioi 0)
  exact hi.congr_fun (fun x hx => fW_eq f (ne_of_gt hx) l) measurableSet_Ioi

lemma integrableOn_Lap (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) {l : ℝ}
    (hl : 0 < l) :
    IntegrableOn (fun x => x ^ (2 * p + 1) * Lsq f x * Real.exp (-(x * l))) (Ioi 0) := by
  set l' := min l (π / 2) with hl'
  have hl'0 : 0 < l' := lt_min hl (by positivity)
  have hl'π : l' < π := lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
  have hc : Continuous fun x : ℝ => x ^ (2 * p + 1) * Lsq f x * Real.exp (-(x * l)) :=
    ((continuous_pow _).mul (continuous_Lsq f)).mul (by fun_prop)
  refine (((integrableOn_KGL f hk hl'0 hl'π).const_mul ((2 * π) ^ (2 * p + 1)))).mono'
    hc.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
  have hx0 : 0 < x := hx
  have hL := Lsq_nonneg f x
  rw [Real.norm_of_nonneg (by positivity)]
  have hk' := kG_ge p hx0
  have := kG_nonneg p hx0
  have h1 : x ^ (2 * p + 1) ≤ (2 * π) ^ (2 * p + 1) * kG p x := by
    rw [div_le_iff₀ (by positivity)] at hk'; linarith
  have h2 : Real.exp (-(x * l)) ≤ Real.exp (-(l' * x)) := by
    apply Real.exp_le_exp.mpr
    have : l' * x ≤ l * x := mul_le_mul_of_nonneg_right (min_le_left _ _) hx0.le
    linarith
  calc x ^ (2 * p + 1) * Lsq f x * Real.exp (-(x * l))
      ≤ ((2 * π) ^ (2 * p + 1) * kG p x) * Lsq f x * Real.exp (-(l' * x)) := by gcongr
    _ = _ := by ring

lemma Lap_nonneg (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (l : ℝ) : 0 ≤ Lap f l :=
  setIntegral_nonneg measurableSet_Ioi fun x hx => by
    have := Lsq_nonneg f x; have : (0 : ℝ) < x := hx; positivity

lemma W_split (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) {l : ℝ}
    (hl0 : 0 < l) (hl : l < π) :
    ∫ t, fW f ((π - l) / 2) t = (∫ t in Iic 0, fW f ((π - l) / 2) t) + KGL f l := by
  have hi := integrable_fW f hk (β := (π - l) / 2) (by linarith) (by linarith)
  rw [← setIntegral_univ, ← Set.Iic_union_Ioi (a := 0),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hi.integrableOn hi.integrableOn]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx => fW_eq f (ne_of_gt hx) l

lemma N_bounds (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ : β < π / 2) :
    0 ≤ ∫ t in Iic 0, fW f β t ∧ ∫ t in Iic 0, fW f β t ≤ ∫ t in Iic 0, fW f 0 t := by
  refine ⟨setIntegral_nonneg measurableSet_Iic fun t _ => fW_nonneg f β t, ?_⟩
  refine setIntegral_mono_on (integrable_fW f hk hβ0 hβ).integrableOn
    (integrable_fW f hk le_rfl (by positivity)).integrableOn measurableSet_Iic fun t ht => ?_
  unfold fW
  have ht' : t ≤ 0 := ht
  have hbt := mul_nonpos_of_nonneg_of_nonpos hβ0 ht'
  have : Real.exp (2 * β * t) ≤ Real.exp (2 * 0 * t) := Real.exp_le_exp.mpr (by nlinarith)
  exact mul_le_mul_of_nonneg_left this (sq_nonneg _)

lemma Lap_le_KGL (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) {l : ℝ}
    (hl0 : 0 < l) (hl : l < π) : Lap f l / (2 * π) ^ (2 * p + 1) ≤ KGL f l := by
  unfold Lap LapG KGL
  rw [← integral_div]
  refine setIntegral_mono_on ((integrableOn_Lap f hk hl0).div_const _) (integrableOn_KGL f hk hl0 hl)
    measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := hx
  have hk' := kG_ge p hx0
  have hL := Lsq_nonneg f x
  have e : Real.exp (-(x * l)) = Real.exp (-(l * x)) := by ring_nf
  rw [e]
  calc x ^ (2 * p + 1) * Lsq f x * Real.exp (-(l * x)) / (2 * π) ^ (2 * p + 1) =
      x ^ (2 * p + 1) / (2 * π) ^ (2 * p + 1) * Real.exp (-(l * x)) * Lsq f x := by ring
    _ ≤ _ := by gcongr

lemma KGL_le (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) {ν : ℝ} (hν : 0 < ν) :
    ∃ C : ℝ, ∀ l : ℝ, 0 < l → l < π →
      KGL f l ≤ (1 + ν) * (Lap f l / (2 * π) ^ (2 * p + 1)) + C := by
  have hev := (tendsto_order.1 (tendsto_kG_ratio p)).2 (1 + ν) (by linarith)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hev
  set T := max T₀ 1 with hT
  have hT1 : 1 ≤ T := le_max_right _ _
  set Ck := Pq p T * Real.exp (π * T) / (2 * π) ^ (2 * p + 2) with hCk
  refine ⟨Ck * ∫ x in Ioc 0 T, Lsq f x, fun l hl0 hl => ?_⟩
  have hiK := integrableOn_KGL f hk hl0 hl
  have hiL := integrableOn_Lap f hk hl0
  unfold KGL
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ T by linarith),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi (hiK.mono_set Ioc_subset_Ioi_self)
      (hiK.mono_set (Ioi_subset_Ioi (by linarith)))]
  have hLsqi : IntegrableOn (Lsq f) (Ioc 0 T) :=
    ((continuous_Lsq f).integrableOn_Icc (a := 0) (b := T)).mono_set Ioc_subset_Icc_self
  have h1 : ∫ x in Ioc 0 T, kG p x * Real.exp (-(l * x)) * Lsq f x ≤
      Ck * ∫ x in Ioc 0 T, Lsq f x := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hiK.mono_set Ioc_subset_Ioi_self) (hLsqi.const_mul _)
      measurableSet_Ioc fun x hx => ?_
    have hk' := kG_le p hx.1 hx.2
    have hL := Lsq_nonneg f x
    have he : Real.exp (-(l * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := mul_pos hl0 hx.1; linarith)
    have hk0 : 0 ≤ kG p x := kG_nonneg p hx.1
    calc kG p x * Real.exp (-(l * x)) * Lsq f x ≤ kG p x * 1 * Lsq f x := by gcongr
      _ ≤ Ck * Lsq f x := by rw [mul_one]; exact mul_le_mul_of_nonneg_right hk' hL
  have h2 : ∫ x in Ioi T, kG p x * Real.exp (-(l * x)) * Lsq f x ≤
      (1 + ν) * (Lap f l / (2 * π) ^ (2 * p + 1)) := by
    have hsub : ∫ x in Ioi T, x ^ (2 * p + 1) * Lsq f x * Real.exp (-(x * l)) ≤ Lap f l := by
      unfold Lap LapG
      refine setIntegral_mono_set hiL (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
        (Eventually.of_forall (Ioi_subset_Ioi (by linarith)))
      have : (0 : ℝ) < x := hx
      have := Lsq_nonneg f x
      positivity
    calc ∫ x in Ioi T, kG p x * Real.exp (-(l * x)) * Lsq f x
        ≤ ∫ x in Ioi T, (1 + ν) / (2 * π) ^ (2 * p + 1) *
            (x ^ (2 * p + 1) * Lsq f x * Real.exp (-(x * l))) := by
          refine setIntegral_mono_on (hiK.mono_set (Ioi_subset_Ioi (by linarith)))
            ((hiL.mono_set (Ioi_subset_Ioi (by linarith))).const_mul _) measurableSet_Ioi
            fun x hx => ?_
          have hxT : T < x := hx
          have hx0 : 0 < x := by linarith
          have hr := hT₀ x (by linarith [le_max_left T₀ 1])
          rw [div_lt_iff₀ (by positivity)] at hr
          have hk' : kG p x ≤ (1 + ν) / (2 * π) ^ (2 * p + 1) * x ^ (2 * p + 1) := by
            rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; linarith
          have hL := Lsq_nonneg f x
          have e : Real.exp (-(x * l)) = Real.exp (-(l * x)) := by ring_nf
          rw [e]
          calc kG p x * Real.exp (-(l * x)) * Lsq f x ≤
              (1 + ν) / (2 * π) ^ (2 * p + 1) * x ^ (2 * p + 1) * Real.exp (-(l * x)) * Lsq f x := by
                gcongr
            _ = _ := by ring
      _ = (1 + ν) / (2 * π) ^ (2 * p + 1) *
            ∫ x in Ioi T, x ^ (2 * p + 1) * Lsq f x * Real.exp (-(x * l)) :=
          integral_const_mul _ _
      _ ≤ (1 + ν) / (2 * π) ^ (2 * p + 1) * Lap f l := by gcongr
      _ = _ := by ring
  linarith

/-! ### The weighted asymptotic in the variable `λ = π − 2β` -/

lemma tendsto_beta_of_l' :
    Tendsto (fun l : ℝ => (π - l) / 2) (𝓝[>] 0) (𝓝[<] (π / 2)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun l : ℝ => (π - l) / 2) (𝓝 0) (𝓝 ((π - 0) / 2)) :=
      ((continuous_const.sub continuous_id).div_const 2).tendsto 0
    rw [sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with l hl
    show (π - l) / 2 < π / 2
    have : (0 : ℝ) < l := hl
    linarith

lemma cot_of_l' (l : ℝ) : Real.cos ((π - l) / 2) / Real.sin ((π - l) / 2) =
    Real.sin (l / 2) / Real.cos (l / 2) := by
  rw [show (π - l) / 2 = π / 2 - l / 2 by ring, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]

lemma tendsto_l_div_kappa' : Tendsto (fun l : ℝ => l / (Real.sin (l / 2) / Real.cos (l / 2)))
    (𝓝[>] 0) (𝓝 2) := by
  have hs : Tendsto (fun l : ℝ => Real.sinc (l / 2)) (𝓝[>] 0) (𝓝 1) := by
    have hcont : Continuous (fun l : ℝ => Real.sinc (l / 2)) :=
      Real.continuous_sinc.comp (by fun_prop)
    have := hcont.tendsto 0
    simp only [zero_div, Real.sinc_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hc : Tendsto (fun l : ℝ => Real.cos (l / 2)) (𝓝[>] 0) (𝓝 1) := by
    have hcont : Continuous (fun l : ℝ => Real.cos (l / 2)) :=
      Real.continuous_cos.comp (by fun_prop)
    have := hcont.tendsto 0
    simp only [zero_div, Real.cos_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h := (hc.const_mul 2).div hs one_ne_zero
  rw [mul_one, div_one] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π by positivity)] with l hl
  have hl0 : 0 < l := hl.1
  have hs0 : 0 < Real.sin (l / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [hl.2])
  show 2 * Real.cos (l / 2) / Real.sinc (l / 2) = _
  rw [Real.sinc_of_ne_zero (by positivity : l / 2 ≠ 0)]
  field_simp

lemma alg2' (N : ℕ) {l κ W A B : ℝ} (hl : l ≠ 0) (hκ : κ ≠ 0) (hA : A ≠ 0) (hAB : A + B ≠ 0) :
    l ^ N / A * W = κ ^ N * W / (A + B) * (l / κ) ^ N * (1 + B * A⁻¹) := by
  rw [div_pow]
  field_simp

lemma Xnn' (N : ℕ) {l : ℝ} (h0 : 0 < l) (h1 : l < 1) : 0 ≤ l ^ N / Real.log (1 / l) :=
  div_nonneg (by positivity) (Real.log_nonneg (by rw [le_div_iff₀ h0]; linarith))

/-- The weighted asymptotic in `λ`. -/
theorem weighted_lambda_f (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) :
    Tendsto (fun l : ℝ => l ^ (2 * p + 2) / Real.log (1 / l) * ∫ t, fW f ((π - l) / 2) t)
      (𝓝[>] 0)
      (𝓝 (2 ^ (2 * p + 2) * (12 * RankinSelbergGeneral.petNormSqF f))) := by
  have hB := (weighted_asymptotic_f f hk).comp tendsto_beta_of_l'
  have h2 := tendsto_l_div_kappa'
  have hL : Tendsto (fun l : ℝ => Real.log (1 / l)) (𝓝[>] 0) atTop := by
    have := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    refine this.congr fun t => ?_
    simp [one_div]
  have hr : Tendsto (fun l : ℝ => 1 + Real.log (l / (Real.sin (l / 2) / Real.cos (l / 2))) *
      (Real.log (1 / l))⁻¹) (𝓝[>] 0) (𝓝 1) := by
    have hlog := (Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp h2
    have := (hlog.mul hL.inv_tendsto_atTop).const_add 1
    simpa using this
  have hlim := (hB.mul (h2.pow (2 * p + 2))).mul hr
  rw [mul_one, mul_comm (12 * RankinSelbergGeneral.petNormSqF f)] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num), hL.eventually_gt_atTop 0]
    with l hl hLl
  have hl0 : 0 < l := hl.1
  have hlπ : l < π := by linarith [hl.2, Real.pi_gt_three]
  have hs0 : 0 < Real.sin (l / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have hc0 : 0 < Real.cos (l / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  set κ := Real.sin (l / 2) / Real.cos (l / 2) with hκ
  have hκ0 : 0 < κ := div_pos hs0 hc0
  have hlogκ : Real.log (1 / κ) = Real.log (1 / l) + Real.log (l / κ) := by
    rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
  have hκ1 : κ < 1 := by
    have h1 : Real.sin (l / 2) < l / 2 := Real.sin_lt (by positivity)
    have h2 : 1 - (l / 2) ^ 2 / 2 ≤ Real.cos (l / 2) := Real.one_sub_sq_div_two_le_cos
    rw [hκ, div_lt_one hc0]
    nlinarith [hl.2]
  have hLκ : 0 < Real.log (1 / l) + Real.log (l / κ) := by
    rw [← hlogκ]; exact Real.log_pos (by rw [lt_div_iff₀ hκ0, one_mul]; exact hκ1)
  simp only [Function.comp, cot_of_l']
  rw [← hκ, hlogκ]
  exact (alg2' (2 * p + 2) hl0.ne' hκ0.ne' hLl.ne' hLκ.ne').symm

/-- The Laplace constant `Kc f = (2π)^{2p+1} 2^{2p+2} · 12‖f‖²`. -/
noncomputable def Kc (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) : ℝ :=
  (2 * π) ^ (2 * p + 1) * (2 ^ (2 * p + 2) * (12 * RankinSelbergGeneral.petNormSqF f))

/-- **The Laplace asymptotic**: `λ^k ∫_0^∞ t^{k−1} |L|² e^{−λt} dt / log(1/λ) → Kc f`. -/
theorem laplace_asymptotic_f (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) :
    Tendsto (fun l : ℝ => l ^ (2 * p + 2) / Real.log (1 / l) * Lap f l) (𝓝[>] 0) (𝓝 (Kc f)) := by
  set A₁ := 2 ^ (2 * p + 2) * (12 * RankinSelbergGeneral.petNormSqF f) with hA₁
  set X : ℝ → ℝ := fun l => l ^ (2 * p + 2) / Real.log (1 / l) with hX
  have hL : Tendsto (fun l : ℝ => Real.log (1 / l)) (𝓝[>] 0) atTop := by
    have := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    refine this.congr fun t => ?_
    simp [one_div]
  have hX0 : Tendsto X (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun l : ℝ => l ^ (2 * p + 2)) (𝓝[>] 0) (𝓝 0) := by
      have := ((continuous_pow (2 * p + 2)).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    have := h1.mul hL.inv_tendsto_atTop
    rw [mul_zero] at this
    refine this.congr fun l => ?_
    simp only [hX, div_eq_mul_inv, Pi.inv_apply]
  have hW := weighted_lambda_f f hk
  set N₀ := ∫ t in Iic 0, fW f 0 t
  have hK : Tendsto (fun l => X l * KGL f l) (𝓝[>] 0) (𝓝 A₁) := by
    have hN : Tendsto (fun l => X l * ∫ t in Iic 0, fW f ((π - l) / 2) t) (𝓝[>] 0) (𝓝 0) := by
      have hb : Tendsto (fun l => X l * N₀) (𝓝[>] 0) (𝓝 0) := by
        simpa using hX0.mul_const N₀
      refine squeeze_zero' ?_ ?_ hb
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with l hl
        exact mul_nonneg (Xnn' _ hl.1 hl.2) (N_bounds f hk (by linarith [hl.2, Real.pi_gt_three])
            (by linarith [hl.1, Real.pi_pos])).1
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with l hl
        exact mul_le_mul_of_nonneg_left (N_bounds f hk (by linarith [hl.2, Real.pi_gt_three])
            (by linarith [hl.1, Real.pi_pos])).2 (Xnn' _ hl.1 hl.2)
    have := hW.sub hN
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with l hl
    have hlπ : l < π := by linarith [hl.2, Real.pi_gt_three]
    simp only [hX]
    rw [W_split f hk hl.1 hlπ]; ring
  have hY : Tendsto (fun l => X l * (Lap f l / (2 * π) ^ (2 * p + 1))) (𝓝[>] 0) (𝓝 A₁) := by
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · by_cases hb0 : b < 0
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with l hl
        have hX0' : 0 ≤ X l := Xnn' _ hl.1 hl.2
        have := Lap_nonneg f l
        have : 0 ≤ X l * (Lap f l / (2 * π) ^ (2 * p + 1)) := by positivity
        linarith
      push Not at hb0
      set ν : ℝ := (A₁ - b) / (2 * (b + 1)) with hν
      have hν0 : 0 < ν := by rw [hν]; apply div_pos <;> linarith
      have hbν : b * (1 + ν) < A₁ := by
        rw [hν]
        have h1 : b * (1 + (A₁ - b) / (2 * (b + 1))) = b + b * (A₁ - b) / (2 * (b + 1)) := by ring
        rw [h1]
        have h2 : b * (A₁ - b) / (2 * (b + 1)) < A₁ - b := by
          rw [div_lt_iff₀ (by linarith)]; nlinarith
        linarith
      obtain ⟨C, hC⟩ := KGL_le f hk hν0
      have hconv : Tendsto (fun l => X l * KGL f l - X l * C) (𝓝[>] 0) (𝓝 A₁) := by
        have := hK.sub (hX0.mul_const C)
        rwa [zero_mul, sub_zero] at this
      filter_upwards [(tendsto_order.1 hconv).1 (b * (1 + ν)) hbν,
        Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with l h1 hl
      have hlπ : l < π := by linarith [hl.2, Real.pi_gt_three]
      have hX0' : 0 ≤ X l := Xnn' _ hl.1 hl.2
      have h2 := mul_le_mul_of_nonneg_left (hC l hl.1 hlπ) hX0'
      have h3 : b * (1 + ν) < (1 + ν) * (X l * (Lap f l / (2 * π) ^ (2 * p + 1))) := by nlinarith
      nlinarith
    · filter_upwards [(tendsto_order.1 hK).2 b hb,
        Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with l h1 hl
      have hlπ : l < π := by linarith [hl.2, Real.pi_gt_three]
      have hX0' : 0 ≤ X l := Xnn' _ hl.1 hl.2
      exact (mul_le_mul_of_nonneg_left (Lap_le_KGL f hk hl.1 hlπ) hX0').trans_lt h1
  have := hY.const_mul ((2 * π) ^ (2 * p + 1))
  rw [show (2 * π) ^ (2 * p + 1) * A₁ = Kc f by rw [hA₁]; rfl] at this
  refine this.congr fun l => ?_
  simp only [hX]
  field_simp

/-! ### Good's theorem -/

lemma lapHyp_f (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) (hk : 12 ≤ 2 * p + 2) :
    LapHyp (Lsq f) (2 * p + 1) (Kc f) where
  cont := continuous_Lsq f
  nonneg := Lsq_nonneg f
  integ l hl := integrableOn_Lap f hk hl
  lim := laplace_asymptotic_f f hk

lemma Kc_div_eq (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ)) :
    Kc f / ((2 * p + 1).factorial : ℝ) = 2 * RankinSelbergGeneral.rsConst f := by
  unfold Kc RankinSelbergGeneral.rsConst
  rw [show 2 * p + 2 - 1 = 2 * p + 1 by omega]
  have hf : (0 : ℝ) < ((2 * p + 1).factorial : ℝ) := by positivity
  push_cast
  field_simp
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, mul_pow (π : ℝ), ← pow_mul]
  ring

/-- **Good's theorem for `f` of weight `2p+2`.** -/
theorem critical_mean_square_asymptotic_f (f : CuspForm 𝒮ℒ ((2 * p + 2 : ℕ) : ℤ))
    (hk : 12 ≤ 2 * p + 2) :
    Tendsto (fun T : ℝ => (∫ t in Icc 0 T, Lsq f t) / (T * Real.log T)) atTop
      (𝓝 (2 * RankinSelbergGeneral.rsConst f)) := by
  have := tendsto_of_laplace (lapHyp_f f hk)
  rwa [Kc_div_eq] at this

end RamanujanTau.GeneralCuspMoments
