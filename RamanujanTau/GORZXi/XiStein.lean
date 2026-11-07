/-
# Moment bounds for the Riemann kernel by a Stein (integration-by-parts) argument

All integrals are over `t ∈ (1, ∞)` in the original variable of `FXi`, with `u = log t`, `x = u − c`.

* `theta0_lower`, `theta0_upper` : `e^{−πt} ≤ θ₀(t) ≤ 2e^{−πt}` for `t ≥ 1` (from the series).
* `stein_identity` : `∫ ((πt − ¼)u − M) u^{M−1} x^{2q+1} t^{−3/4}e^{−πt} = (2q+1) ∫ u^M x^{2q} t^{−3/4}e^{−πt}`
  (`d/dt [u^M x^{2q+1} t^{1/4} e^{−πt}]`, boundary terms `0`).
* with `c` the root of `(πe^c − ¼)c = M`, `λ₁ = πe^{c−1}`, `λ₂ = M/c²`, the pointwise inequalities give
  `λ₂ S_{q+1} ≤ (2q+1)S_q` and `λ₁ S_{q+1} ≤ (2q+1)S_q + λ₁ S_{2q+2}`, hence (if `λ₁ ≤ λ₂²`)
  `S_q ≤ B_q λ₁^{−q} S_0` (`moment_rec`).
-/
import RamanujanTau.GORZXi.XiPoly

set_option autoImplicit false

namespace GORZXi

open Real Set MeasureTheory Filter Topology

/-! ## the theta sandwich -/

lemma theta0_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => rexp (-π * ((n : ℝ) + 1) ^ 2 * t)) (theta0 t) := by
  have h := (HurwitzZeta.hasSum_int_evenKernel 0 ht).nat_add_neg
  simp only [Int.cast_natCast, add_zero, Int.cast_neg, neg_sq, Int.cast_zero, QuotientAddGroup.mk_zero] at h
  have h2 : HasSum (fun n : ℕ => rexp (-π * (n : ℝ) ^ 2 * t)) ((HurwitzZeta.evenKernel 0 t + 1) / 2) := by
    have := h.div_const 2
    convert this using 1
    · funext n; ring
    · simp
  rw [← hasSum_nat_add_iff' 1] at h2
  convert h2 using 1
  · funext n; push_cast; ring_nf
  · simp [theta0]; ring

lemma theta0_lower {t : ℝ} (ht : 0 < t) : rexp (-π * t) ≤ theta0 t := by
  have := le_hasSum (theta0_hasSum ht) 0 (fun _ _ => (exp_pos _).le)
  simpa using this

lemma theta0_upper {t : ℝ} (ht : 1 ≤ t) : theta0 t ≤ 2 * rexp (-π * t) := by
  have ht0 : 0 < t := by linarith
  set r := rexp (-π * t) with hr
  have hr0 : 0 ≤ r := (exp_pos _).le
  have hr1 : r ≤ 1 / 2 := by
    have : rexp (-π * t) ≤ rexp (-1) := exp_le_exp.mpr (by nlinarith [pi_gt_three])
    linarith [exp_neg_one_lt_half]
  have hg : HasSum (fun n : ℕ => r * r ^ n) (r * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0 (by linarith)).mul_left r
  have hle := hasSum_le (fun n : ℕ => by
    show rexp (-π * ((n : ℝ) + 1) ^ 2 * t) ≤ r * r ^ n
    rw [hr, ← exp_nat_mul, ← exp_add]
    apply exp_le_exp.mpr
    have : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hpt : 0 ≤ π * t := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hpt]) (theta0_hasSum ht0) hg
  calc theta0 t ≤ r * (1 - r)⁻¹ := hle
    _ ≤ r * 2 := by
        gcongr
        rw [inv_le_comm₀ (by linarith) two_pos]; linarith
    _ = 2 * r := by ring

lemma theta0_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ theta0 t := (exp_pos _).le.trans (theta0_lower ht)

lemma continuousOn_theta0 : ContinuousOn theta0 (Ioi 0) :=
  ((HurwitzZeta.continuousOn_evenKernel 0).sub continuousOn_const).div_const 2

/-! ## integrability -/

lemma pow_mul_exp_le (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t ^ N * rexp (-π * t) ≤ (N.factorial : ℝ) * rexp (-t) := by
  have h1 : t ≤ (π - 1) * t := by nlinarith [pi_gt_three]
  have h2 := pow_div_factorial_le_exp (x := (π - 1) * t) (by nlinarith [pi_gt_three]) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have h3 : t ^ N ≤ (N.factorial : ℝ) * rexp ((π - 1) * t) := by
    rw [div_le_iff₀ hf] at h2
    calc t ^ N ≤ ((π - 1) * t) ^ N := pow_le_pow_left₀ ht h1 N
      _ ≤ _ := by linarith
  calc t ^ N * rexp (-π * t) ≤ (N.factorial : ℝ) * rexp ((π - 1) * t) * rexp (-π * t) :=
        mul_le_mul_of_nonneg_right h3 (exp_pos _).le
    _ = _ := by rw [mul_assoc, ← exp_add]; ring_nf

lemma integrableOn_of_bound {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 1)) {A : ℝ} {N : ℕ}
    (hb : ∀ t, 1 < t → |f t| ≤ A * (t ^ N * rexp (-π * t))) : IntegrableOn f (Ioi 1) := by
  have hi : IntegrableOn (fun t : ℝ => A * (N.factorial : ℝ) * rexp (-1 * t)) (Ioi 1) :=
    (exp_neg_integrableOn_Ioi 1 one_pos).const_mul _
  refine hi.mono' (hf.aestronglyMeasurable measurableSet_Ioi) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  have ht1 : 1 < t := ht
  rw [Real.norm_eq_abs]
  have hA : 0 ≤ A := by
    have := (abs_nonneg _).trans (hb t ht1)
    exact nonneg_of_mul_nonneg_left this (by positivity)
  calc |f t| ≤ A * (t ^ N * rexp (-π * t)) := hb t ht1
    _ ≤ A * ((N.factorial : ℝ) * rexp (-t)) :=
        mul_le_mul_of_nonneg_left (pow_mul_exp_le N (by linarith)) hA
    _ = _ := by ring_nf

lemma tendsto_of_bound {f : ℝ → ℝ} {A : ℝ} {N : ℕ}
    (hb : ∀ t, 1 < t → |f t| ≤ A * (t ^ N * rexp (-π * t))) : Tendsto f atTop (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => A * ((N.factorial : ℝ) * rexp (-t))) atTop (𝓝 0) := by
    simpa using (tendsto_exp_neg_atTop_nhds_zero.const_mul (N.factorial : ℝ)).const_mul A
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_gt_atTop 1] with t ht
  rw [Real.norm_eq_abs]
  have hA : 0 ≤ A := by
    have := (abs_nonneg _).trans (hb t ht)
    exact nonneg_of_mul_nonneg_left this (by positivity)
  exact (hb t ht).trans (mul_le_mul_of_nonneg_left (pow_mul_exp_le N (by linarith)) hA)

lemma abs_log_le_self {t : ℝ} (ht : 1 ≤ t) : |Real.log t| ≤ t := by
  rw [abs_of_nonneg (Real.log_nonneg ht)]
  linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < t)]

lemma abs_log_sub_le {t : ℝ} (ht : 1 ≤ t) (c : ℝ) : |Real.log t - c| ≤ (1 + |c|) * t := by
  have := abs_log_le_self ht
  calc |Real.log t - c| ≤ |Real.log t| + |c| := abs_sub _ _
    _ ≤ t + |c| * t := by nlinarith [abs_nonneg c]
    _ = _ := by ring

lemma rpow_neg34_le {t : ℝ} (ht : 1 ≤ t) : t ^ (-(3 / 4 : ℝ)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos ht (by norm_num)

lemma continuousOn_log1 : ContinuousOn Real.log (Ioi 1) :=
  Real.continuousOn_log.mono fun x hx => by
    simp only [mem_Ioi] at hx; exact (show x ≠ 0 from ne_of_gt (by linarith))

lemma continuousOn_rpow1 (a : ℝ) : ContinuousOn (fun t : ℝ => t ^ a) (Ioi 1) :=
  continuousOn_id.rpow_const fun x hx => Or.inl (zero_lt_one.trans (show (1 : ℝ) < x from hx)).ne'

/-- the clean density moment `u^m x^l t^{−3/4} e^{−πt}`. -/
noncomputable def rho0 (m : ℕ) (c : ℝ) (l : ℕ) (t : ℝ) : ℝ :=
  Real.log t ^ m * (Real.log t - c) ^ l * t ^ (-(3 / 4 : ℝ)) * rexp (-π * t)

/-- the theta density moment `u^m x^l t^{−3/4} θ₀(t)`. -/
noncomputable def rhoT (m : ℕ) (c : ℝ) (l : ℕ) (t : ℝ) : ℝ :=
  Real.log t ^ m * (Real.log t - c) ^ l * t ^ (-(3 / 4 : ℝ)) * theta0 t

/-- the Stein integrand `((πt − ¼)u − (m+1)) u^m x^{2q+1} t^{−3/4} e^{−πt}`. -/
noncomputable def steinI (m : ℕ) (c : ℝ) (q : ℕ) (t : ℝ) : ℝ :=
  ((π * t - 1 / 4) * Real.log t - ((m : ℝ) + 1)) * Real.log t ^ m * (Real.log t - c) ^ (2 * q + 1) *
    t ^ (-(3 / 4 : ℝ)) * rexp (-π * t)

lemma base_bound {t : ℝ} (ht : 1 ≤ t) (m l : ℕ) (c : ℝ) :
    |Real.log t ^ m * (Real.log t - c) ^ l * t ^ (-(3 / 4 : ℝ))| ≤ (1 + |c|) ^ l * t ^ (m + l) := by
  rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg (Real.rpow_nonneg (by linarith) _), pow_add]
  have h1 := pow_le_pow_left₀ (abs_nonneg _) (abs_log_le_self ht) m
  have h2 := pow_le_pow_left₀ (abs_nonneg _) (abs_log_sub_le ht c) l
  rw [mul_pow] at h2
  calc |Real.log t| ^ m * |Real.log t - c| ^ l * t ^ (-(3 / 4 : ℝ))
      ≤ t ^ m * ((1 + |c|) ^ l * t ^ l) * 1 :=
        mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) (rpow_neg34_le ht)
          (Real.rpow_nonneg (by linarith) _) (by positivity)
    _ = _ := by ring

lemma continuousOn_base (m l : ℕ) (c : ℝ) :
    ContinuousOn (fun t => Real.log t ^ m * (Real.log t - c) ^ l * t ^ (-(3 / 4 : ℝ))) (Ioi 1) :=
  ((continuousOn_log1.pow m).mul ((continuousOn_log1.sub continuousOn_const).pow l)).mul
    (continuousOn_rpow1 _)

lemma rho0_bound {t : ℝ} (ht : 1 < t) (m l : ℕ) (c : ℝ) :
    |rho0 m c l t| ≤ (1 + |c|) ^ l * (t ^ (m + l) * rexp (-π * t)) := by
  unfold rho0
  rw [abs_mul, abs_of_pos (exp_pos _)]
  calc _ ≤ (1 + |c|) ^ l * t ^ (m + l) * rexp (-π * t) :=
        mul_le_mul_of_nonneg_right (base_bound ht.le m l c) (exp_pos _).le
    _ = _ := by ring

lemma rhoT_bound {t : ℝ} (ht : 1 < t) (m l : ℕ) (c : ℝ) :
    |rhoT m c l t| ≤ (2 * (1 + |c|) ^ l) * (t ^ (m + l) * rexp (-π * t)) := by
  unfold rhoT
  rw [abs_mul, abs_of_nonneg (theta0_nonneg (by linarith))]
  calc _ ≤ (1 + |c|) ^ l * t ^ (m + l) * (2 * rexp (-π * t)) :=
        mul_le_mul (base_bound ht.le m l c) (theta0_upper ht.le) (theta0_nonneg (by linarith))
          (by positivity)
    _ = _ := by ring

lemma steinI_bound {t : ℝ} (ht : 1 < t) (m q : ℕ) (c : ℝ) :
    |steinI m c q t| ≤ ((π + 1 / 4 + ((m : ℝ) + 1)) * (1 + |c|) ^ (2 * q + 1)) *
      (t ^ (m + (2 * q + 1) + 2) * rexp (-π * t)) := by
  unfold steinI
  have hl := abs_log_le_self ht.le
  have hl0 : 0 ≤ Real.log t := Real.log_nonneg ht.le
  have hD : |(π * t - 1 / 4) * Real.log t - ((m : ℝ) + 1)| ≤ (π + 1 / 4 + ((m : ℝ) + 1)) * t ^ 2 := by
    rw [abs_of_nonneg hl0] at hl
    have ht2 : 1 ≤ t ^ 2 := by nlinarith
    have hpt : 0 ≤ π * t := by positivity
    have a1 := mul_le_mul_of_nonneg_left hl hpt
    have a2 : 0 ≤ π * t * Real.log t := mul_nonneg hpt hl0
    have a3 : t ≤ t ^ 2 := by nlinarith
    have a4 : ((m : ℝ) + 1) ≤ ((m : ℝ) + 1) * t ^ 2 := by
      have : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
      nlinarith
    rw [abs_le]; constructor <;> nlinarith [pi_pos]
  have hb := base_bound ht.le m (2 * q + 1) c
  rw [show ((π * t - 1 / 4) * Real.log t - ((m : ℝ) + 1)) * Real.log t ^ m * (Real.log t - c) ^ (2 * q + 1) *
      t ^ (-(3 / 4 : ℝ)) * rexp (-π * t) = ((π * t - 1 / 4) * Real.log t - ((m : ℝ) + 1)) *
      (Real.log t ^ m * (Real.log t - c) ^ (2 * q + 1) * t ^ (-(3 / 4 : ℝ))) * rexp (-π * t) by ring,
    abs_mul, abs_mul, abs_of_pos (exp_pos _)]
  calc _ ≤ ((π + 1 / 4 + ((m : ℝ) + 1)) * t ^ 2) * ((1 + |c|) ^ (2 * q + 1) * t ^ (m + (2 * q + 1))) *
        rexp (-π * t) := by gcongr
    _ = _ := by ring

lemma integrable_rho0 (m l : ℕ) (c : ℝ) : IntegrableOn (rho0 m c l) (Ioi 1) :=
  integrableOn_of_bound ((continuousOn_base m l c).mul (by fun_prop)) fun t ht => rho0_bound ht m l c

lemma integrable_rhoT (m l : ℕ) (c : ℝ) : IntegrableOn (rhoT m c l) (Ioi 1) :=
  integrableOn_of_bound ((continuousOn_base m l c).mul
    (continuousOn_theta0.mono fun x hx => by simp only [mem_Ioi] at hx ⊢; linarith))
    fun t ht => rhoT_bound ht m l c

lemma integrable_steinI (m q : ℕ) (c : ℝ) : IntegrableOn (steinI m c q) (Ioi 1) := by
  refine integrableOn_of_bound ?_ fun t ht => steinI_bound ht m q c
  have : ContinuousOn (fun t => ((π * t - 1 / 4) * Real.log t - ((m : ℝ) + 1)) *
      (Real.log t ^ m * (Real.log t - c) ^ (2 * q + 1) * t ^ (-(3 / 4 : ℝ))) * rexp (-π * t)) (Ioi 1) :=
    ((((continuousOn_const.mul continuousOn_id).sub continuousOn_const).mul continuousOn_log1).sub
      continuousOn_const |>.mul (continuousOn_base m (2 * q + 1) c)).mul (by fun_prop)
  refine this.congr fun t _ => ?_
  simp only [steinI]; ring

lemma FXi_eq (m : ℕ) (c : ℝ) : FXi m = ∫ t in Ioi 1, rhoT m c 0 t := by
  unfold FXi rhoT; congr 1; funext t; ring

/-! ## the Stein identity -/

/-- `Φ(t) = u^{m+1} x^{2q+1} t^{1/4} e^{−πt}`. -/
noncomputable def steinPhi (m : ℕ) (c : ℝ) (q : ℕ) (t : ℝ) : ℝ :=
  Real.log t ^ (m + 1) * (Real.log t - c) ^ (2 * q + 1) * t ^ (1 / 4 : ℝ) * rexp (-π * t)

lemma steinPhi_hasDerivAt (m : ℕ) (c : ℝ) (q : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (steinPhi m c q) ((2 * (q : ℝ) + 1) * rho0 (m + 1) c (2 * q) t - steinI m c q t) t := by
  have hlog := Real.hasDerivAt_log ht.ne'
  have h1 := hlog.pow (m + 1)
  have h2 := (hlog.sub_const c).pow (2 * q + 1)
  have h3 := Real.hasDerivAt_rpow_const (x := t) (p := (1 / 4 : ℝ)) (Or.inl ht.ne')
  have h4 := ((hasDerivAt_id t).const_mul (-π)).exp
  have := ((h1.mul h2).mul h3).mul h4
  unfold steinPhi
  convert this using 1
  have hy : t ^ (1 / 4 : ℝ) = t * t ^ (-(3 / 4 : ℝ)) := by
    rw [show (1 / 4 : ℝ) = 1 + (-(3 / 4 : ℝ)) by norm_num, Real.rpow_add ht, Real.rpow_one]
  have hy' : t ^ ((1 / 4 : ℝ) - 1) = t ^ (-(3 / 4 : ℝ)) := by norm_num
  simp only [Pi.pow_apply, Pi.mul_apply]
  rw [hy', hy]
  simp only [rho0, steinI, id, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat,
    Nat.add_sub_cancel, show 2 * q + 1 - 1 = 2 * q by omega]
  set y := t ^ (-(3 / 4 : ℝ))
  set L := Real.log t
  have ht' : t ≠ 0 := ht.ne'
  field_simp
  ring

theorem stein_identity (m : ℕ) (c : ℝ) (q : ℕ) :
    ∫ t in Ioi 1, steinI m c q t = (2 * (q : ℝ) + 1) * ∫ t in Ioi 1, rho0 (m + 1) c (2 * q) t := by
  have hd : ∀ t ∈ Ioi (1 : ℝ), HasDerivAt (steinPhi m c q)
      ((2 * (q : ℝ) + 1) * rho0 (m + 1) c (2 * q) t - steinI m c q t) t :=
    fun t ht => steinPhi_hasDerivAt m c q (by simp only [mem_Ioi] at ht; linarith)
  have hint : IntegrableOn (fun t => (2 * (q : ℝ) + 1) * rho0 (m + 1) c (2 * q) t - steinI m c q t) (Ioi 1) :=
    ((integrable_rho0 _ _ _).const_mul _).sub (integrable_steinI _ _ _)
  have hlim : Tendsto (steinPhi m c q) atTop (𝓝 0) := by
    refine tendsto_of_bound (A := (1 + |c|) ^ (2 * q + 1)) (N := m + 1 + (2 * q + 1) + 1) fun t ht => ?_
    have hb := base_bound ht.le (m + 1) (2 * q + 1) c
    have hy : t ^ (1 / 4 : ℝ) = t * t ^ (-(3 / 4 : ℝ)) := by
      rw [show (1 / 4 : ℝ) = 1 + (-(3 / 4 : ℝ)) by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
    unfold steinPhi
    rw [hy, show Real.log t ^ (m + 1) * (Real.log t - c) ^ (2 * q + 1) * (t * t ^ (-(3 / 4 : ℝ))) *
      rexp (-π * t) = t * (Real.log t ^ (m + 1) * (Real.log t - c) ^ (2 * q + 1) * t ^ (-(3 / 4 : ℝ))) *
      rexp (-π * t) by ring, abs_mul, abs_mul, abs_of_pos (exp_pos _), abs_of_pos (by linarith : (0:ℝ) < t)]
    calc t * |Real.log t ^ (m + 1) * (Real.log t - c) ^ (2 * q + 1) * t ^ (-(3 / 4 : ℝ))| * rexp (-π * t)
        ≤ t * ((1 + |c|) ^ (2 * q + 1) * t ^ (m + 1 + (2 * q + 1))) * rexp (-π * t) := by gcongr
      _ = _ := by ring
  have hcont : ContinuousWithinAt (steinPhi m c q) (Ici 1) 1 :=
    (steinPhi_hasDerivAt m c q one_pos).continuousAt.continuousWithinAt
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hint hlim
  have h1 : steinPhi m c q 1 = 0 := by simp [steinPhi]
  rw [h1, sub_zero, integral_sub ((integrable_rho0 _ _ _).const_mul _) (integrable_steinI _ _ _),
    integral_const_mul] at h
  linarith

end GORZXi
