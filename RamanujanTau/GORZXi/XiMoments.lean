/-
# Moment bounds for the Riemann kernel `u^m t^{−3/4} θ₀(t) dt` (`u = log t`, `t > 1`)

With `M = m + 1` and `c ≥ 1` the root of `(πe^c − ¼)c = M`, put `λ₁ = πe^{c−1}`, `λ₂ = M/c²`.

* `ineqI`, `ineqII` : pointwise, for `u > 0`, `x = u − c`, `D = (πe^u − ¼)u − M`:
  `λ₂ u x² ≤ D x` and `λ₁ u x² ≤ D x + λ₁ u x^{2R}` (`R ≥ 1`).
* `steinI_ineq`, `steinII_ineq` : integrated against `u^m x^{2q} t^{−3/4}e^{−πt}` and combined with the
  Stein identity: `λ₂ S_{q+1} ≤ (2q+1) S_q`, `λ₁ S_{q+1} ≤ (2q+1) S_q + λ₁ S_{2q+2}`.
* `moment_rec` : `S_q λ₁^q ≤ B_q S_0` when `λ₁ ≤ λ₂²`.
* **`abs_rhoT_le`** : `|∫ u^M x^l t^{−3/4} θ₀| ≤ (1 + 2B_l) λ₁^{−l/2} F(M)`.
-/
import RamanujanTau.GORZXi.XiStein

set_option autoImplicit false

namespace GORZXi

open Real Set MeasureTheory Filter Topology

/-! ## pointwise inequalities -/

lemma D_identity (u c M : ℝ) (hc : c ≠ 0) (hroot : (π * rexp c - 1 / 4) * c = M) :
    ((π * rexp u - 1 / 4) * u - M) * (u - c) =
      π * u * ((rexp u - rexp c) * (u - c)) + M / c * (u - c) ^ 2 := by
  rw [← hroot]; field_simp; ring

lemma exp_sub_mul_nonneg (u c : ℝ) : 0 ≤ (rexp u - rexp c) * (u - c) := by
  rcases le_total u c with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith [exp_le_exp.mpr h]) (by linarith)
  · exact mul_nonneg (by linarith [exp_le_exp.mpr h]) (by linarith)

lemma exp_sub_ge (u c : ℝ) : rexp c * (u - c) ≤ rexp u - rexp c := by
  have := add_one_le_exp (u - c)
  have h : rexp u = rexp c * rexp (u - c) := by rw [← exp_add]; ring_nf
  rw [h]; nlinarith [exp_pos c]

lemma ineqI {u c M : ℝ} (hu : 0 < u) (hc : 1 ≤ c) (hM : 0 ≤ M) (hroot : (π * rexp c - 1 / 4) * c = M) :
    M / c ^ 2 * u * (u - c) ^ 2 ≤ ((π * rexp u - 1 / 4) * u - M) * (u - c) := by
  have hc0 : 0 < c := by linarith
  rw [D_identity u c M hc0.ne' hroot]
  have hP := exp_sub_mul_nonneg u c
  have hx2 : 0 ≤ (u - c) ^ 2 := sq_nonneg _
  rcases le_total u c with h | h
  · have : M / c ^ 2 * u ≤ M / c := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hc0]
      have := mul_le_mul_of_nonneg_left h (mul_nonneg hM hc0.le); nlinarith
    nlinarith [mul_nonneg (mul_nonneg pi_pos.le hu.le) hP]
  · -- `π e^c ≥ M/c ≥ M/c²`
    have h1 : M / c ^ 2 ≤ π * rexp c := by
      have e1 : π * rexp c = M / c + 1 / 4 := by rw [← hroot]; field_simp; ring
      have : M / c ^ 2 ≤ M / c := div_le_div_of_nonneg_left hM hc0 (by nlinarith)
      linarith
    have h2 : rexp c * (u - c) ^ 2 ≤ (rexp u - rexp c) * (u - c) := by
      have := exp_sub_ge u c
      have hx : 0 ≤ u - c := by linarith
      nlinarith
    have h3 : M / c ^ 2 * u * (u - c) ^ 2 ≤ π * u * ((rexp u - rexp c) * (u - c)) := by
      calc M / c ^ 2 * u * (u - c) ^ 2 ≤ π * rexp c * u * (u - c) ^ 2 := by gcongr
        _ = π * u * (rexp c * (u - c) ^ 2) := by ring
        _ ≤ _ := by gcongr
    have : 0 ≤ M / c * (u - c) ^ 2 := by positivity
    linarith

lemma ineqII {u c M : ℝ} (hu : 0 < u) (hc : 1 ≤ c) (hM : 0 ≤ M) (hroot : (π * rexp c - 1 / 4) * c = M)
    {R : ℕ} (hR : 1 ≤ R) :
    π * rexp (c - 1) * u * (u - c) ^ 2 ≤ ((π * rexp u - 1 / 4) * u - M) * (u - c) +
      π * rexp (c - 1) * u * (u - c) ^ (2 * R) := by
  have hc0 : 0 < c := by linarith
  rw [D_identity u c M hc0.ne' hroot]
  have hP := exp_sub_mul_nonneg u c
  have hA : 0 ≤ π * u * ((rexp u - rexp c) * (u - c)) := mul_nonneg (mul_nonneg pi_pos.le hu.le) hP
  have hB : 0 ≤ M / c * (u - c) ^ 2 := by positivity
  have hpu : 0 ≤ π * rexp (c - 1) * u := by positivity
  have hE : 0 ≤ π * rexp (c - 1) * u * (u - c) ^ (2 * R) := by
    rw [pow_mul]; positivity
  have hec : rexp (c - 1) ≤ rexp c := exp_le_exp.mpr (by linarith)
  by_cases h1 : c - 1 ≤ u
  · -- `(e^u − e^c)(u − c) ≥ e^{c−1}(u − c)²`
    have hkey : rexp (c - 1) * (u - c) ^ 2 ≤ (rexp u - rexp c) * (u - c) := by
      rcases le_total c u with h | h
      · have := exp_sub_ge u c
        have hx : 0 ≤ u - c := by linarith
        have : rexp (c - 1) * (u - c) ^ 2 ≤ rexp c * (u - c) ^ 2 := by gcongr
        nlinarith
      · have := exp_sub_ge c u
        have hx : 0 ≤ c - u := by linarith
        have heu : rexp (c - 1) ≤ rexp u := exp_le_exp.mpr h1
        have : rexp (c - 1) * (u - c) ^ 2 ≤ rexp u * (c - u) ^ 2 := by
          rw [show (u - c) ^ 2 = (c - u) ^ 2 by ring]; gcongr
        nlinarith
    have : π * rexp (c - 1) * u * (u - c) ^ 2 ≤ π * u * ((rexp u - rexp c) * (u - c)) := by
      calc π * rexp (c - 1) * u * (u - c) ^ 2 = π * u * (rexp (c - 1) * (u - c) ^ 2) := by ring
        _ ≤ _ := by gcongr
    linarith
  · -- far left: `|x| ≥ 1`
    have hx : 1 ≤ (u - c) ^ 2 := by nlinarith
    have hpow : (u - c) ^ 2 ≤ (u - c) ^ (2 * R) := by
      rw [pow_mul]
      calc (u - c) ^ 2 = ((u - c) ^ 2) ^ 1 := (pow_one _).symm
        _ ≤ ((u - c) ^ 2) ^ R := pow_le_pow_right₀ hx hR
    have : π * rexp (c - 1) * u * (u - c) ^ 2 ≤ π * rexp (c - 1) * u * (u - c) ^ (2 * R) := by gcongr
    linarith

/-! ## the integrated inequalities -/

/-- `S_q = ∫ u^M x^{2q} t^{−3/4}e^{−πt}`. -/
noncomputable def Smom (M : ℕ) (c : ℝ) (q : ℕ) : ℝ := ∫ t in Ioi 1, rho0 M c (2 * q) t

lemma Smom_nonneg (M : ℕ) (c : ℝ) (q : ℕ) : 0 ≤ Smom M c q := by
  unfold Smom
  refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
  have ht1 : 1 < t := ht
  unfold rho0
  have := Real.log_nonneg ht1.le
  rw [pow_mul]
  have : 0 ≤ t ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
  positivity

/-- the weight `u^m x^{2q} t^{−3/4} e^{−πt} ≥ 0`. -/
lemma weight_nonneg {t : ℝ} (ht : 1 < t) (m : ℕ) (c : ℝ) (q : ℕ) :
    0 ≤ Real.log t ^ m * (Real.log t - c) ^ (2 * q) * t ^ (-(3 / 4 : ℝ)) * rexp (-π * t) := by
  have := Real.log_nonneg ht.le
  have : 0 ≤ t ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
  rw [pow_mul]; positivity

lemma steinI_eq {t : ℝ} (ht : 1 < t) (m : ℕ) (c : ℝ) (q : ℕ) :
    steinI m c q t = (((π * rexp (Real.log t) - 1 / 4) * Real.log t - ((m : ℝ) + 1)) * (Real.log t - c)) *
      (Real.log t ^ m * (Real.log t - c) ^ (2 * q) * t ^ (-(3 / 4 : ℝ)) * rexp (-π * t)) := by
  rw [Real.exp_log (by linarith)]; unfold steinI; ring

lemma rho0_eq {t : ℝ} (m : ℕ) (c : ℝ) (q R : ℕ) :
    rho0 (m + 1) c (2 * q + 2 * R) t = (Real.log t * (Real.log t - c) ^ (2 * R)) *
      (Real.log t ^ m * (Real.log t - c) ^ (2 * q) * t ^ (-(3 / 4 : ℝ)) * rexp (-π * t)) := by
  unfold rho0; ring

theorem stein_ineqI (m : ℕ) {c : ℝ} (hc : 1 ≤ c) (hroot : (π * rexp c - 1 / 4) * c = (m : ℝ) + 1) (q : ℕ) :
    ((m : ℝ) + 1) / c ^ 2 * Smom (m + 1) c (q + 1) ≤ (2 * (q : ℝ) + 1) * Smom (m + 1) c q := by
  unfold Smom
  rw [← stein_identity, ← integral_const_mul]
  refine setIntegral_mono_on ((integrable_rho0 _ _ _).const_mul _) (integrable_steinI _ _ _)
    measurableSet_Ioi fun t ht => ?_
  have ht1 : 1 < t := ht
  rw [steinI_eq ht1, show 2 * (q + 1) = 2 * q + 2 * 1 by ring, rho0_eq, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (weight_nonneg ht1 m c q)
  have := ineqI (Real.log_pos ht1) hc (by positivity) hroot
  convert this using 1; ring

theorem stein_ineqII (m : ℕ) {c : ℝ} (hc : 1 ≤ c) (hroot : (π * rexp c - 1 / 4) * c = (m : ℝ) + 1) (q : ℕ) :
    π * rexp (c - 1) * Smom (m + 1) c (q + 1) ≤
      (2 * (q : ℝ) + 1) * Smom (m + 1) c q + π * rexp (c - 1) * Smom (m + 1) c (2 * (q + 1)) := by
  unfold Smom
  rw [← stein_identity, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (integrable_steinI _ _ _) ((integrable_rho0 _ _ _).const_mul _)]
  refine setIntegral_mono_on ((integrable_rho0 _ _ _).const_mul _)
    ((integrable_steinI _ _ _).add ((integrable_rho0 _ _ _).const_mul _)) measurableSet_Ioi fun t ht => ?_
  have ht1 : 1 < t := ht
  rw [steinI_eq ht1, show 2 * (q + 1) = 2 * q + 2 * 1 by ring, rho0_eq,
    show 2 * (2 * q + 2 * 1) = 2 * q + 2 * (q + 2) by ring, rho0_eq]
  have hw := weight_nonneg ht1 m c q
  have := ineqII (Real.log_pos ht1) hc (by positivity) hroot (R := q + 2) (by omega)
  have h2 := mul_le_mul_of_nonneg_right this hw
  convert h2 using 1 <;> ring

/-! ## the recursion -/

/-- `A_q = ∏_{i<q} (2i+1)`. -/
noncomputable def Acst : ℕ → ℝ
  | 0 => 1
  | q + 1 => (2 * (q : ℝ) + 1) * Acst q

/-- `B_0 = 1`, `B_{q+1} = (2q+1) B_q + A_{2q+2}`. -/
noncomputable def Bcst : ℕ → ℝ
  | 0 => 1
  | q + 1 => (2 * (q : ℝ) + 1) * Bcst q + Acst (2 * (q + 1))

lemma Acst_nonneg : ∀ q, 0 ≤ Acst q
  | 0 => zero_le_one
  | q + 1 => mul_nonneg (by positivity) (Acst_nonneg q)

lemma Bcst_nonneg : ∀ q, 0 ≤ Bcst q
  | 0 => zero_le_one
  | q + 1 => add_nonneg (mul_nonneg (by positivity) (Bcst_nonneg q)) (Acst_nonneg _)

theorem moment_rec (S : ℕ → ℝ) (hS : ∀ q, 0 ≤ S q) {l1 l2 : ℝ} (h1 : 0 < l1) (h2 : 0 < l2)
    (h12 : l1 ≤ l2 ^ 2) (hI : ∀ q, l2 * S (q + 1) ≤ (2 * (q : ℝ) + 1) * S q)
    (hII : ∀ q, l1 * S (q + 1) ≤ (2 * (q : ℝ) + 1) * S q + l1 * S (2 * (q + 1))) :
    ∀ q, S q * l1 ^ q ≤ Bcst q * S 0 := by
  have hA : ∀ q, S q * l2 ^ q ≤ Acst q * S 0 := by
    intro q
    induction q with
    | zero => simp [Acst]
    | succ q ih =>
      calc S (q + 1) * l2 ^ (q + 1) = (l2 * S (q + 1)) * l2 ^ q := by ring
        _ ≤ ((2 * (q : ℝ) + 1) * S q) * l2 ^ q := mul_le_mul_of_nonneg_right (hI q) (pow_nonneg h2.le _)
        _ = (2 * (q : ℝ) + 1) * (S q * l2 ^ q) := by ring
        _ ≤ (2 * (q : ℝ) + 1) * (Acst q * S 0) := mul_le_mul_of_nonneg_left ih (by positivity)
        _ = _ := by simp only [Acst]; ring
  intro q
  induction q with
  | zero => simp [Bcst]
  | succ q ih =>
    have hpow : l1 ^ (q + 1) ≤ l2 ^ (2 * (q + 1)) := by
      rw [pow_mul]; exact pow_le_pow_left₀ h1.le h12 _
    calc S (q + 1) * l1 ^ (q + 1) = (l1 * S (q + 1)) * l1 ^ q := by ring
      _ ≤ ((2 * (q : ℝ) + 1) * S q + l1 * S (2 * (q + 1))) * l1 ^ q :=
          mul_le_mul_of_nonneg_right (hII q) (pow_nonneg h1.le _)
      _ = (2 * (q : ℝ) + 1) * (S q * l1 ^ q) + S (2 * (q + 1)) * l1 ^ (q + 1) := by ring
      _ ≤ (2 * (q : ℝ) + 1) * (Bcst q * S 0) + S (2 * (q + 1)) * l2 ^ (2 * (q + 1)) :=
          add_le_add (mul_le_mul_of_nonneg_left ih (by positivity)) (mul_le_mul_of_nonneg_left hpow (hS _))
      _ ≤ (2 * (q : ℝ) + 1) * (Bcst q * S 0) + Acst (2 * (q + 1)) * S 0 := add_le_add le_rfl (hA _)
      _ = _ := by simp only [Bcst]; ring

/-! ## the theta moments -/

/-- the hypotheses on the root `c` used below. -/
structure RootData (m : ℕ) (c : ℝ) : Prop where
  one_le : 1 ≤ c
  root : (π * rexp c - 1 / 4) * c = (m : ℝ) + 1
  lam : π * rexp (c - 1) ≤ (((m : ℝ) + 1) / c ^ 2) ^ 2

lemma Smom_bound {m : ℕ} {c : ℝ} (hc : RootData m c) (q : ℕ) :
    Smom (m + 1) c q * (π * rexp (c - 1)) ^ q ≤ Bcst q * Smom (m + 1) c 0 :=
  moment_rec (Smom (m + 1) c) (Smom_nonneg _ _) (by positivity)
    (by have := hc.one_le; positivity) hc.lam (stein_ineqI m hc.one_le hc.root)
    (stein_ineqII m hc.one_le hc.root) q

lemma rhoT_le_two_rho0 {t : ℝ} (ht : 1 < t) (M : ℕ) (c : ℝ) (q : ℕ) :
    rhoT M c (2 * q) t ≤ 2 * rho0 M c (2 * q) t := by
  unfold rhoT rho0
  have h0 : 0 ≤ Real.log t ^ M * (Real.log t - c) ^ (2 * q) * t ^ (-(3 / 4 : ℝ)) := by
    have := Real.log_nonneg ht.le
    have : 0 ≤ t ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
    rw [pow_mul]; positivity
  have := mul_le_mul_of_nonneg_left (theta0_upper ht.le) h0
  linarith

lemma rho0_le_rhoT {t : ℝ} (ht : 1 < t) (M : ℕ) (c : ℝ) : rho0 M c 0 t ≤ rhoT M c 0 t := by
  unfold rhoT rho0
  have h0 : 0 ≤ Real.log t ^ M * (Real.log t - c) ^ 0 * t ^ (-(3 / 4 : ℝ)) := by
    have := Real.log_nonneg ht.le
    have : 0 ≤ t ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
    positivity
  exact mul_le_mul_of_nonneg_left (theta0_lower (by linarith)) h0

/-- **Moment bound**: `|∫ u^M x^l t^{−3/4} θ₀| ≤ (1 + 2B_l) σ^l F(M)`, `σ = λ₁^{−1/2}`. -/
theorem abs_rhoT_le {m : ℕ} {c : ℝ} (hc : RootData m c) (l : ℕ) :
    |∫ t in Ioi 1, rhoT (m + 1) c l t| ≤
      (1 + 2 * Bcst l) * (Real.sqrt (π * rexp (c - 1)))⁻¹ ^ l * FXi (m + 1) := by
  set l1 := π * rexp (c - 1) with hl1
  have hl1p : 0 < l1 := by positivity
  set s := (Real.sqrt l1)⁻¹ ^ l with hs
  have hsp : 0 < s := by positivity
  have hs2 : s ^ 2 * l1 ^ l = 1 := by
    rw [hs, ← pow_mul, mul_comm l 2, pow_mul, inv_pow, Real.sq_sqrt hl1p.le, inv_pow]
    exact inv_mul_cancel₀ (pow_pos hl1p l).ne'
  have hF : FXi (m + 1) = ∫ t in Ioi 1, rhoT (m + 1) c 0 t := FXi_eq _ c
  -- pointwise `|rhoT l| ≤ s rhoT 0 + s⁻¹ rhoT (2l)`
  have hpt : ∀ t ∈ Ioi (1 : ℝ), |rhoT (m + 1) c l t| ≤ s * rhoT (m + 1) c 0 t + s⁻¹ * rhoT (m + 1) c (2 * l) t := by
    intro t ht
    have ht1 : 1 < t := ht
    set g := Real.log t ^ (m + 1) * t ^ (-(3 / 4 : ℝ)) * theta0 t with hg
    have hg0 : 0 ≤ g := by
      have := Real.log_nonneg ht1.le
      have : 0 ≤ t ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
      have := theta0_nonneg (by linarith : (0:ℝ) < t)
      positivity
    have e1 : ∀ l', rhoT (m + 1) c l' t = (Real.log t - c) ^ l' * g := fun l' => by
      simp only [rhoT, hg]; ring
    rw [e1, e1, e1, abs_mul, abs_of_nonneg hg0, pow_zero]
    have hx : |Real.log t - c| ^ l ≤ s + s⁻¹ * (Real.log t - c) ^ (2 * l) := by
      rw [pow_mul, ← sq_abs, ← pow_mul, mul_comm 2 l, pow_mul]
      set a := |Real.log t - c| ^ l
      have ha : 0 ≤ a := by positivity
      rcases le_total a s with h | h
      · have : 0 ≤ s⁻¹ * a ^ 2 := by positivity
        linarith
      · have : a ≤ s⁻¹ * a ^ 2 := by
          rw [inv_mul_eq_div, le_div_iff₀ hsp]; nlinarith
        linarith
    rw [abs_pow]
    nlinarith
  have hint0 := integrable_rhoT (m + 1) 0 c
  have hint2 := integrable_rhoT (m + 1) (2 * l) c
  calc |∫ t in Ioi 1, rhoT (m + 1) c l t| ≤ ∫ t in Ioi 1, |rhoT (m + 1) c l t| := by
        rw [← Real.norm_eq_abs]
        exact (norm_integral_le_integral_norm _).trans_eq (by simp only [Real.norm_eq_abs])
    _ ≤ ∫ t in Ioi 1, (s * rhoT (m + 1) c 0 t + s⁻¹ * rhoT (m + 1) c (2 * l) t) :=
        setIntegral_mono_on (integrable_rhoT (m + 1) l c).abs
          ((hint0.const_mul _).add (hint2.const_mul _)) measurableSet_Ioi hpt
    _ = s * FXi (m + 1) + s⁻¹ * ∫ t in Ioi 1, rhoT (m + 1) c (2 * l) t := by
        rw [integral_add (hint0.const_mul _) (hint2.const_mul _), integral_const_mul, integral_const_mul, hF]
    _ ≤ s * FXi (m + 1) + s⁻¹ * (2 * Smom (m + 1) c l) := by
        gcongr
        rw [Smom, ← integral_const_mul]
        exact setIntegral_mono_on hint2 ((integrable_rho0 _ _ _).const_mul _) measurableSet_Ioi
          fun t ht => rhoT_le_two_rho0 ht _ _ _
    _ ≤ s * FXi (m + 1) + s⁻¹ * (2 * (Bcst l * FXi (m + 1) * s ^ 2)) := by
        gcongr
        have hb := Smom_bound hc l
        have h0 : Smom (m + 1) c 0 ≤ FXi (m + 1) := by
          rw [hF, Smom]
          simp only [mul_zero]
          exact setIntegral_mono_on (integrable_rho0 _ _ _) hint0 measurableSet_Ioi
            fun t ht => rho0_le_rhoT ht _ _
        have : Smom (m + 1) c l = Smom (m + 1) c l * (s ^ 2 * l1 ^ l) := by rw [hs2, mul_one]
        rw [this]
        calc Smom (m + 1) c l * (s ^ 2 * l1 ^ l) = (Smom (m + 1) c l * l1 ^ l) * s ^ 2 := by ring
          _ ≤ (Bcst l * Smom (m + 1) c 0) * s ^ 2 := by gcongr
          _ ≤ (Bcst l * FXi (m + 1)) * s ^ 2 := by gcongr; exact Bcst_nonneg l
    _ = (1 + 2 * Bcst l) * s * FXi (m + 1) := by field_simp

end GORZXi
