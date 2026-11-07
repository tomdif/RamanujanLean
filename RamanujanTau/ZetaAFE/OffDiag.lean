/-
# The off-diagonal terms: first-derivative test

For `m ≠ n`, `b_{m,n}(t) = (MN)^{−1/2} e^{itλ} V(Λ − log(t/2π))` with `λ = log(N/M) ≠ 0`. The weight
`f(t) = V(Λ − log(t/2π))` is increasing (`f' = g(·)/t ≥ 0`), so integration by parts gives
`|∫_a^T e^{itλ} f| ≤ 2 f(T)/|λ|`, and `f(T) ≤ 2 e^{−c(Λ − log(T/2π))}` for `0 ≤ c ≤ 1`. With
`1/|λ| ≤ N/|N−M|` the pair bound is `≤ 4 (T/2π)^c M^{−σ} |N−M|^{−σ}`, `σ = 1/2 + c > 1`, and the
double sum is `≤ 8 (T/2π)^c Z_σ²`.
-/
import RamanujanTau.ZetaAFE.Diag

set_option autoImplicit false

namespace RamanujanTau.ZetaAFE

open Complex MeasureTheory Set Filter Topology
open scoped Interval

noncomputable def ellT (t : ℝ) : ℝ := Real.log (t / (2 * Real.pi))
noncomputable def fV (Λ t : ℝ) : ℝ := V (Λ - ellT t)

lemma hasDerivAt_ellT {t : ℝ} (ht : 0 < t) : HasDerivAt ellT (1 / t) t := by
  have h := ((hasDerivAt_id t).div_const (2 * Real.pi)).log (by positivity)
  unfold ellT
  convert h using 1
  simp only [id]; field_simp

lemma hasDerivAt_fV (Λ : ℝ) {t : ℝ} (ht : 0 < t) : HasDerivAt (fV Λ) (gk (Λ - ellT t) / t) t := by
  have h := (hasDerivAt_V (Λ - ellT t)).comp t ((hasDerivAt_const t Λ).sub (hasDerivAt_ellT ht))
  unfold fV
  convert h using 1
  ring

lemma continuousOn_ellT {a b : ℝ} (ha : 0 < a) : ContinuousOn ellT (Icc a b) := fun t ht =>
  (hasDerivAt_ellT (ha.trans_le ht.1)).continuousAt.continuousWithinAt

lemma continuousOn_fV (Λ : ℝ) {a b : ℝ} (ha : 0 < a) : ContinuousOn (fV Λ) (Icc a b) := fun t ht =>
  (hasDerivAt_fV Λ (ha.trans_le ht.1)).continuousAt.continuousWithinAt

lemma fV_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (Λ T : ℝ) :
    fV Λ T ≤ 2 * Real.exp (-(c * (Λ - ellT T))) := by
  unfold fV
  set x := Λ - ellT T
  rcases le_total 0 x with hx | hx
  · refine (V_le_exp x).trans ?_
    gcongr; nlinarith
  · refine (V_le_two x).trans ?_
    have : 1 ≤ Real.exp (-(c * x)) := Real.one_le_exp (by nlinarith)
    linarith

/-- **First-derivative test** for the increasing weight `fV`. -/
theorem norm_integral_osc_le {a T lam Λ : ℝ} (ha : 0 < a) (haT : a ≤ T) (hlam : lam ≠ 0) :
    ‖∫ t in a..T, cexp (t * I * lam) * (fV Λ t : ℂ)‖ ≤ 2 * fV Λ T / |lam| := by
  have hIl : I * (lam : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hlam)
  set u : ℝ → ℂ := fun t => (fV Λ t : ℂ) with hu
  set u' : ℝ → ℂ := fun t => ((gk (Λ - ellT t) / t : ℝ) : ℂ) with hu'
  set v : ℝ → ℂ := fun t => cexp (t * I * lam) / (I * lam) with hv
  set v' : ℝ → ℂ := fun t => cexp (t * I * lam) with hv'
  have hIcc : ∀ x ∈ [[a, T]], 0 < x := fun x hx => by
    rw [uIcc_of_le haT] at hx; exact ha.trans_le hx.1
  have huu : ∀ x ∈ [[a, T]], HasDerivAt u (u' x) x := fun x hx =>
    (hasDerivAt_fV Λ (hIcc x hx)).ofReal_comp
  have hvv : ∀ x ∈ [[a, T]], HasDerivAt v (v' x) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * I * lam) (I * lam) x := by
      simpa using (((hasDerivAt_id x).ofReal_comp).mul_const I).mul_const (lam : ℂ)
    have h2 := (h1.cexp).div_const (I * lam)
    simp only [hv, hv']
    convert h2 using 1
    have : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
    field_simp
  have hcu' : ContinuousOn u' [[a, T]] := by
    rw [uIcc_of_le haT]
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    refine ContinuousOn.div ?_ continuousOn_id (fun x hx => (ha.trans_le hx.1).ne')
    exact continuous_gk.comp_continuousOn (continuousOn_const.sub (continuousOn_ellT ha))
  have hu'i : IntervalIntegrable u' volume a T := hcu'.intervalIntegrable
  have hv'i : IntervalIntegrable v' volume a T := (by fun_prop : Continuous v').intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul huu hvv hu'i hv'i
  have heq : (∫ t in a..T, cexp (t * I * lam) * (fV Λ t : ℂ)) = ∫ t in a..T, u t * v' t := by
    congr 1; funext t; simp only [hu, hv']; ring
  rw [heq, hibp]
  have hnv : ∀ t : ℝ, ‖v t‖ = 1 / |lam| := by
    intro t; simp only [hv]
    rw [norm_div, Complex.norm_exp, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    simp
  have hfa : 0 ≤ fV Λ a := V_nonneg _
  have hfT : 0 ≤ fV Λ T := V_nonneg _
  have hint : ‖∫ t in a..T, u' t * v t‖ ≤ (fV Λ T - fV Λ a) / |lam| := by
    refine (intervalIntegral.norm_integral_le_integral_norm haT).trans (le_of_eq ?_)
    have hpt : ∀ t ∈ [[a, T]], ‖u' t * v t‖ = gk (Λ - ellT t) / t / |lam| := by
      intro t ht
      rw [norm_mul, hnv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (gk_pos _).le (hIcc t ht).le)]
      ring
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_div]
    congr 1
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hasDerivAt_fV Λ (hIcc x hx)) ?_
    have := hcu'.intervalIntegrable (μ := volume)
    refine (ContinuousOn.intervalIntegrable ?_)
    rw [uIcc_of_le haT]
    refine ContinuousOn.div ?_ continuousOn_id (fun x hx => (ha.trans_le hx.1).ne')
    exact continuous_gk.comp_continuousOn (continuousOn_const.sub (continuousOn_ellT ha))
  have h1 : ‖u T * v T‖ = fV Λ T / |lam| := by
    rw [norm_mul, hnv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfT]; ring
  have h2 : ‖u a * v a‖ = fV Λ a / |lam| := by
    rw [norm_mul, hnv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfa]; ring
  calc ‖u T * v T - u a * v a - ∫ t in a..T, u' t * v t‖
      ≤ ‖u T * v T‖ + ‖u a * v a‖ + ‖∫ t in a..T, u' t * v t‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr; exact norm_sub_le _ _
    _ ≤ fV Λ T / |lam| + fV Λ a / |lam| + (fV Λ T - fV Λ a) / |lam| := by
        rw [h1, h2]; gcongr
    _ = 2 * fV Λ T / |lam| := by ring

/-- `1/|log(N/M)| ≤ N/(N−M)` for `M < N`. -/
lemma inv_abs_lg_sub_le {m n : ℕ} (h : m < n) :
    1 / |lg n - lg m| ≤ ((n : ℝ) + 1) / ((n : ℝ) - m) := by
  have hmn : (m : ℝ) < n := by exact_mod_cast h
  have hM : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlog : ((n : ℝ) - m) / ((n : ℝ) + 1) ≤ lg n - lg m := by
    unfold lg
    rw [← Real.log_div hN.ne' hM.ne']
    have := Real.one_sub_inv_le_log_of_pos (x := ((n : ℝ) + 1) / ((m : ℝ) + 1)) (by positivity)
    rw [inv_div] at this
    have e : 1 - ((m : ℝ) + 1) / ((n : ℝ) + 1) = ((n : ℝ) - m) / ((n : ℝ) + 1) := by
      field_simp; ring
    linarith
  have hpos : 0 < ((n : ℝ) - m) / ((n : ℝ) + 1) := div_pos (by linarith) hN
  rw [abs_of_pos (hpos.trans_le hlog)]
  rw [show ((n : ℝ) + 1) / ((n : ℝ) - m) = 1 / (((n : ℝ) - m) / ((n : ℝ) + 1)) by field_simp]
  exact one_div_le_one_div_of_le hpos hlog

/-- `u_σ(k) = (k+1)^{−σ}`. -/
noncomputable def uσ (σ : ℝ) (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ (-σ)

/-- The off-diagonal majorant `φ(m,n) = u(min) u(|n−m|−1)`. -/
noncomputable def phi1 (σ : ℝ) (p : ℕ × ℕ) : ℝ := if p.1 < p.2 then uσ σ p.1 * uσ σ (p.2 - p.1 - 1) else 0
noncomputable def phiO (σ : ℝ) (p : ℕ × ℕ) : ℝ := phi1 σ p + phi1 σ p.swap

lemma uσ_nonneg (σ : ℝ) (k : ℕ) : 0 ≤ uσ σ k := by unfold uσ; positivity
lemma phi1_nonneg (σ : ℝ) (p : ℕ × ℕ) : 0 ≤ phi1 σ p := by
  unfold phi1; split_ifs
  · exact mul_nonneg (uσ_nonneg _ _) (uσ_nonneg _ _)
  · exact le_rfl

lemma emb_injective : Function.Injective fun q : ℕ × ℕ => (q.1, q.1 + q.2 + 1) := by
  intro q r h
  simp only [Prod.mk.injEq] at h
  ext <;> omega

lemma phi1_comp (σ : ℝ) (q : ℕ × ℕ) : phi1 σ (q.1, q.1 + q.2 + 1) = uσ σ q.1 * uσ σ q.2 := by
  unfold phi1
  rw [if_pos (by simp only; omega)]
  congr 2; simp only; omega

lemma phi1_support (σ : ℝ) : Function.support (phi1 σ) ⊆ Set.range fun q : ℕ × ℕ => (q.1, q.1 + q.2 + 1) := by
  intro p hp
  rw [Function.mem_support] at hp
  unfold phi1 at hp
  split_ifs at hp with h
  · exact ⟨(p.1, p.2 - p.1 - 1), by ext <;> simp <;> omega⟩
  · exact absurd rfl hp

lemma summable_phi1 {σ : ℝ} (hσ : 1 < σ) : Summable (phi1 σ) := by
  rw [← (emb_injective).summable_iff (fun p hp => Function.notMem_support.mp fun h => hp (phi1_support σ h))]
  have : (phi1 σ ∘ fun q : ℕ × ℕ => (q.1, q.1 + q.2 + 1)) = fun q => uσ σ q.1 * uσ σ q.2 := by
    funext q; exact phi1_comp σ q
  rw [this]; exact summable_uu hσ

lemma tsum_phi1 {σ : ℝ} (hσ : 1 < σ) : ∑' p, phi1 σ p = Zs σ ^ 2 := by
  rw [← (emb_injective).tsum_eq (phi1_support σ)]
  simp_rw [phi1_comp]
  exact tsum_uu hσ

lemma summable_phi1_swap {σ : ℝ} (hσ : 1 < σ) : Summable fun p : ℕ × ℕ => phi1 σ p.swap := by
  have e : (fun p : ℕ × ℕ => phi1 σ p.swap) = phi1 σ ∘ (Equiv.prodComm ℕ ℕ) := rfl
  rw [e]
  exact (Equiv.summable_iff (Equiv.prodComm ℕ ℕ)).mpr (summable_phi1 hσ)

lemma summable_phiO {σ : ℝ} (hσ : 1 < σ) : Summable (phiO σ) :=
  (summable_phi1 hσ).add (summable_phi1_swap hσ)

lemma tsum_phiO {σ : ℝ} (hσ : 1 < σ) : ∑' p, phiO σ p = 2 * Zs σ ^ 2 := by
  have h := (summable_phi1 hσ).tsum_add (summable_phi1_swap hσ)
  have e : (fun p => phiO σ p) = fun p => phi1 σ p + phi1 σ p.swap := rfl
  rw [e, h]
  have : ∑' p : ℕ × ℕ, phi1 σ p.swap = ∑' p, phi1 σ p :=
    (Equiv.prodComm ℕ ℕ).tsum_eq (phi1 σ)
  rw [this, tsum_phi1 hσ]; ring

/-- Pair bound `e^{−σΛ} · N/(N−M) ≤ u(m) u(n−m−1)` for `m < n`, `σ ≥ 1`. -/
lemma pair_bound {σ : ℝ} (hσ : 1 ≤ σ) {m n : ℕ} (h : m < n) :
    Real.exp (-(σ * (lg m + lg n))) * (((n : ℝ) + 1) / ((n : ℝ) - m)) ≤ uσ σ m * uσ σ (n - m - 1) := by
  have hcast : (((n - m - 1 : ℕ) : ℝ) + 1) = (n : ℝ) - m := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hmn : (1 : ℝ) ≤ (n : ℝ) - m := by
    have : m + 1 ≤ n := h
    have : ((m + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    push_cast at this; linarith
  unfold uσ
  rw [hcast, show (lg m + lg n) = lg (m, n).1 + lg (m, n).2 from rfl, exp_neg_lg]
  simp only
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hD : (0 : ℝ) < (n : ℝ) - m := by linarith
  have hle : (n : ℝ) - m ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  -- ((n+1))^{-σ} (n+1)/(n−m) ≤ (n−m)^{-σ}
  have key : ((n : ℝ) + 1) ^ (-σ) * (((n : ℝ) + 1) / ((n : ℝ) - m)) ≤ ((n : ℝ) - m) ^ (-σ) := by
    have e1 : ((n : ℝ) + 1) ^ (-σ) * (((n : ℝ) + 1) / ((n : ℝ) - m)) =
        ((n : ℝ) + 1) ^ (1 - σ) / ((n : ℝ) - m) := by
      rw [Real.rpow_sub hN, Real.rpow_one, Real.rpow_neg hN.le]; field_simp
    have e2 : ((n : ℝ) - m) ^ (-σ) = ((n : ℝ) - m) ^ (1 - σ) / ((n : ℝ) - m) := by
      rw [Real.rpow_sub hD, Real.rpow_one, Real.rpow_neg hD.le]; field_simp
    rw [e1, e2]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hD hle (by linarith)) hD.le
  have hM : 0 ≤ ((m : ℝ) + 1) ^ (-σ) := by positivity
  calc ((m : ℝ) + 1) ^ (-σ) * ((n : ℝ) + 1) ^ (-σ) * (((n : ℝ) + 1) / ((n : ℝ) - m))
      = ((m : ℝ) + 1) ^ (-σ) * (((n : ℝ) + 1) ^ (-σ) * (((n : ℝ) + 1) / ((n : ℝ) - m))) := by ring
    _ ≤ ((m : ℝ) + 1) ^ (-σ) * ((n : ℝ) - m) ^ (-σ) := by gcongr

/-- **Off-diagonal pair bound** after integration over `[a,T]`. -/
theorem norm_integral_bterm_off {c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≤ 1) {a T : ℝ} (ha : 0 < a)
    (haT : a ≤ T) (p : ℕ × ℕ) (hp : p.1 ≠ p.2) :
    ‖∫ t in a..T, bterm t (ellT t) p‖ ≤ 4 * Real.exp (c * ellT T) * phiO (1 / 2 + c) p := by
  set Λ := lg p.1 + lg p.2 with hΛ
  set lam := lg p.2 - lg p.1 with hlam
  have hlam0 : lam ≠ 0 := by
    intro h
    have : lg p.2 = lg p.1 := by linarith
    unfold lg at this
    have h2 := Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) this
    have : (p.2 : ℝ) = p.1 := by linarith
    exact hp (by exact_mod_cast this.symm)
  have hb : ∀ t, bterm t (ellT t) p = cexp (-((Λ : ℂ) / 2)) * (cexp (t * I * lam) * (fV Λ t : ℂ)) := by
    intro t; unfold bterm fV; rw [hΛ, hlam]; push_cast; ring
  simp_rw [hb]
  rw [intervalIntegral.integral_const_mul, norm_mul]
  have hn : ‖cexp (-((Λ : ℂ) / 2))‖ = Real.exp (-((1 / 2) * Λ)) := by
    rw [Complex.norm_exp]; congr 1; simp; ring
  rw [hn]
  have hosc := norm_integral_osc_le (Λ := Λ) ha haT hlam0
  have hfT := fV_le (by linarith) hc1 Λ T
  have hσ : (1 : ℝ) ≤ 1 / 2 + c := by linarith
  have hφ : Real.exp (-((1 / 2 + c) * Λ)) / |lam| ≤ phiO (1 / 2 + c) p := by
    unfold phiO
    rcases lt_or_gt_of_ne hp with h | h
    · have hpb := pair_bound hσ h
      have hinv := inv_abs_lg_sub_le h
      have h1 : phi1 (1 / 2 + c) p = uσ (1 / 2 + c) p.1 * uσ (1 / 2 + c) (p.2 - p.1 - 1) := by
        unfold phi1; rw [if_pos h]
      have h2 : 0 ≤ phi1 (1 / 2 + c) p.swap := phi1_nonneg _ _
      rw [h1]
      calc Real.exp (-((1 / 2 + c) * Λ)) / |lam| = Real.exp (-((1 / 2 + c) * Λ)) * (1 / |lg p.2 - lg p.1|) := by
            rw [hlam]; ring
        _ ≤ Real.exp (-((1 / 2 + c) * Λ)) * (((p.2 : ℝ) + 1) / ((p.2 : ℝ) - p.1)) := by gcongr
        _ ≤ _ := by rw [hΛ]; linarith
    · have hpb := pair_bound hσ h
      have hinv := inv_abs_lg_sub_le h
      have h1 : phi1 (1 / 2 + c) p.swap = uσ (1 / 2 + c) p.2 * uσ (1 / 2 + c) (p.1 - p.2 - 1) := by
        unfold phi1; rw [if_pos (by simpa using h)]; rfl
      have h2 : 0 ≤ phi1 (1 / 2 + c) p := phi1_nonneg _ _
      rw [h1]
      have habs : |lam| = |lg p.1 - lg p.2| := by rw [hlam, abs_sub_comm]
      calc Real.exp (-((1 / 2 + c) * Λ)) / |lam| = Real.exp (-((1 / 2 + c) * (lg p.2 + lg p.1))) *
            (1 / |lg p.1 - lg p.2|) := by rw [habs, hΛ, add_comm]; ring
        _ ≤ Real.exp (-((1 / 2 + c) * (lg p.2 + lg p.1))) * (((p.1 : ℝ) + 1) / ((p.1 : ℝ) - p.2)) := by
            gcongr
        _ ≤ _ := by linarith
  have hlampos : 0 < |lam| := abs_pos.mpr hlam0
  calc Real.exp (-((1 / 2) * Λ)) * ‖∫ t in a..T, cexp (t * I * lam) * (fV Λ t : ℂ)‖
      ≤ Real.exp (-((1 / 2) * Λ)) * (2 * fV Λ T / |lam|) := by gcongr
    _ ≤ Real.exp (-((1 / 2) * Λ)) * (2 * (2 * Real.exp (-(c * (Λ - ellT T)))) / |lam|) := by gcongr
    _ = 4 * Real.exp (c * ellT T) * (Real.exp (-((1 / 2 + c) * Λ)) / |lam|) := by
        have : Real.exp (-((1 / 2) * Λ)) * Real.exp (-(c * (Λ - ellT T))) =
            Real.exp (c * ellT T) * Real.exp (-((1 / 2 + c) * Λ)) := by
          simp only [← Real.exp_add]; congr 1; ring
        rw [show Real.exp (-((1 / 2) * Λ)) * (2 * (2 * Real.exp (-(c * (Λ - ellT T)))) / |lam|) =
          4 * (Real.exp (-((1 / 2) * Λ)) * Real.exp (-(c * (Λ - ellT T)))) / |lam| by ring, this]
        ring
    _ ≤ _ := by gcongr

end RamanujanTau.ZetaAFE
