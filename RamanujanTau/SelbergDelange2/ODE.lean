/-
# The differential inequality (real-variable Selberg–Delange, step 3)

In the variable `t = log x`:

* `Î(t) = I(e^t)` is continuous with right derivative `Ŝ(t) = S(e^t)` (`Ihat_hasDeriv`,
  `Ihat_continuousOn`): `Î(t) = Σ_{n≤N} (f(n)/n) max(t − log n, 0)`.
* `limit_of_deriv_bound`: if `ψ` is continuous on `[a₀,∞)` with right derivative `ψ'`,
  `|ψ'(t)| ≤ D(1+log(1+t)) t^{−β−1}` (`β ≥ 1`, `a₀ ≥ 2`), then `ψ(t) → C` with
  `|ψ(t) − C| ≤ (2D/β)(1+log(1+t)) t^{−β}` (Mathlib's
  `image_norm_le_of_norm_deriv_right_le_deriv_boundary`, then a Cauchy sequence).
-/
import RamanujanTau.SelbergDelange2.Identity

set_option autoImplicit false

namespace RamanujanTau.SelbergDelange2

open Finset Set Filter Topology

lemma Isum_exp_eq (f : ℕ → ℝ) {t T : ℝ} (htT : t ≤ T) :
    Isum f (Real.exp t) = ∑ n ∈ Finset.Ioc 0 ⌊Real.exp T⌋₊, f n / n * max (t - Real.log n) 0 := by
  have hsub : Finset.Ioc 0 ⌊Real.exp t⌋₊ ⊆ Finset.Ioc 0 ⌊Real.exp T⌋₊ :=
    Ioc_subset_Ioc_right (Nat.floor_le_floor (Real.exp_le_exp.mpr htT))
  rw [Isum]
  have h1 : ∑ n ∈ Finset.Ioc 0 ⌊Real.exp t⌋₊, f n / n * Real.log (Real.exp t / n) =
      ∑ n ∈ Finset.Ioc 0 ⌊Real.exp t⌋₊, f n / n * max (t - Real.log n) 0 := by
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.1 hn).1
    have hnle : (n : ℝ) ≤ Real.exp t :=
      (Nat.cast_le.2 (Finset.mem_Ioc.1 hn).2).trans (Nat.floor_le (Real.exp_pos t).le)
    have hl : Real.log n ≤ t := by
      rw [← Real.log_exp t]; exact Real.log_le_log hn0 hnle
    rw [Real.log_div (Real.exp_pos t).ne' hn0.ne', Real.log_exp, max_eq_left (by linarith)]
  rw [h1]
  refine sum_subset hsub fun n hn hn' => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.1 hn).1
  have hlt : Real.exp t < n := by
    by_contra h; push Not at h
    exact hn' (Finset.mem_Ioc.2 ⟨(Finset.mem_Ioc.1 hn).1, Nat.le_floor h⟩)
  have : t < Real.log n := by rw [← Real.log_exp t]; exact Real.log_lt_log (Real.exp_pos t) hlt
  rw [max_eq_right (by linarith), mul_zero]

lemma Ssum_exp_eq (f : ℕ → ℝ) {t T : ℝ} (htT : t ≤ T) :
    Ssum f (Real.exp t) =
      ∑ n ∈ Finset.Ioc 0 ⌊Real.exp T⌋₊, f n / n * (if Real.log n ≤ t then 1 else 0) := by
  have hsub : Finset.Ioc 0 ⌊Real.exp t⌋₊ ⊆ Finset.Ioc 0 ⌊Real.exp T⌋₊ :=
    Ioc_subset_Ioc_right (Nat.floor_le_floor (Real.exp_le_exp.mpr htT))
  rw [Ssum]
  have h1 : ∑ n ∈ Finset.Ioc 0 ⌊Real.exp t⌋₊, f n / n =
      ∑ n ∈ Finset.Ioc 0 ⌊Real.exp t⌋₊, f n / n * (if Real.log n ≤ t then 1 else 0) := by
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.1 hn).1
    have hnle : (n : ℝ) ≤ Real.exp t :=
      (Nat.cast_le.2 (Finset.mem_Ioc.1 hn).2).trans (Nat.floor_le (Real.exp_pos t).le)
    have hl : Real.log n ≤ t := by
      rw [← Real.log_exp t]; exact Real.log_le_log hn0 hnle
    rw [if_pos hl, mul_one]
  rw [h1]
  refine sum_subset hsub fun n hn hn' => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.1 hn).1
  have hlt : Real.exp t < n := by
    by_contra h; push Not at h
    exact hn' (Finset.mem_Ioc.2 ⟨(Finset.mem_Ioc.1 hn).1, Nat.le_floor h⟩)
  have : t < Real.log n := by rw [← Real.log_exp t]; exact Real.log_lt_log (Real.exp_pos t) hlt
  rw [if_neg (by linarith), mul_zero]

lemma hasDerivWithinAt_max (c t : ℝ) :
    HasDerivWithinAt (fun u => max (u - c) 0) (if c ≤ t then 1 else 0) (Ici t) t := by
  by_cases h : c ≤ t
  · rw [if_pos h]
    have h1 : HasDerivWithinAt (fun u : ℝ => u - c) 1 (Ici t) t :=
      ((hasDerivAt_id t).sub_const c).hasDerivWithinAt
    refine h1.congr_of_mem (fun u hu => ?_) self_mem_Ici
    rw [max_eq_left]; have : t ≤ u := hu; linarith
  · rw [if_neg h]
    push Not at h
    have h1 : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Ici t) t := hasDerivWithinAt_const _ _ _
    refine h1.congr_of_eventuallyEq ?_ (by show max (t - c) 0 = 0; exact max_eq_right (by linarith))
    have : Iio c ∈ 𝓝[Ici t] t := nhdsWithin_le_nhds (Iio_mem_nhds h)
    filter_upwards [this] with u hu
    have : u < c := hu
    rw [max_eq_right (by linarith)]

/-- `Î' = Ŝ` (right derivative). -/
theorem Ihat_hasDeriv (f : ℕ → ℝ) (t : ℝ) :
    HasDerivWithinAt (fun u => Isum f (Real.exp u)) (Ssum f (Real.exp t)) (Ici t) t := by
  set N := ⌊Real.exp (t + 1)⌋₊
  set G : ℝ → ℝ := fun u => ∑ n ∈ Finset.Ioc 0 N, f n / n * max (u - Real.log n) 0 with hG
  have hd : HasDerivWithinAt G (∑ n ∈ Finset.Ioc 0 N, f n / n * (if Real.log n ≤ t then 1 else 0))
      (Ici t) t := by
    have := HasDerivWithinAt.fun_sum (u := Finset.Ioc 0 N)
      (fun n _ => (hasDerivWithinAt_max (Real.log n) t).const_mul (f n / n))
    simpa [hG] using this
  rw [Ssum_exp_eq f (le_of_lt (lt_add_one t))]
  refine hd.congr_of_eventuallyEq ?_ (Isum_exp_eq f (le_of_lt (lt_add_one t)))
  have : Iio (t + 1) ∈ 𝓝[Ici t] t := nhdsWithin_le_nhds (Iio_mem_nhds (lt_add_one t))
  filter_upwards [this] with u hu
  exact Isum_exp_eq f (le_of_lt hu)

theorem Ihat_continuousOn (f : ℕ → ℝ) (a b : ℝ) :
    ContinuousOn (fun u => Isum f (Real.exp u)) (Icc a b) := by
  set G : ℝ → ℝ := fun u => ∑ n ∈ Finset.Ioc 0 ⌊Real.exp b⌋₊, f n / n * max (u - Real.log n) 0 with hG
  have hc : Continuous G := by
    rw [hG]; fun_prop
  exact hc.continuousOn.congr fun u hu => Isum_exp_eq f hu.2

/-! ### The comparison function `G(t) = (1 + log(1+t)) t^{−β}` -/

noncomputable def Gfun (β t : ℝ) : ℝ := (1 + Real.log (1 + t)) * t ^ (-β)

lemma Gfun_nonneg (β : ℝ) {t : ℝ} (ht : 0 < t) : 0 ≤ Gfun β t := by
  unfold Gfun
  have : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
  positivity

lemma Gfun_hasDeriv (β : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (Gfun β) (1 / (1 + t) * t ^ (-β) + (1 + Real.log (1 + t)) * (-β * t ^ (-β - 1))) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + Real.log (1 + t)) (1 / (1 + t)) t := by
    have := (((hasDerivAt_id t).const_add 1).log (by simp; linarith)).const_add 1
    simpa using this
  have h2 : HasDerivAt (fun t : ℝ => t ^ (-β)) (-β * t ^ (-β - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  exact h1.mul h2

lemma neg_Gfun_deriv_ge {β : ℝ} (hβ : 1 ≤ β) {t : ℝ} (ht : 2 ≤ t) :
    (β / 2) * ((1 + Real.log (1 + t)) * t ^ (-β - 1)) ≤
      -(1 / (1 + t) * t ^ (-β) + (1 + Real.log (1 + t)) * (-β * t ^ (-β - 1))) := by
  have ht0 : 0 < t := by linarith
  have hlog : 1 ≤ Real.log (1 + t) := by
    rw [Real.le_log_iff_exp_le (by linarith)]; have := Real.exp_one_lt_d9; linarith
  have hp : 0 < t ^ (-β - 1) := Real.rpow_pos_of_pos ht0 _
  have e : t ^ (-β) = t * t ^ (-β - 1) := by
    rw [show -β = (-β - 1) + 1 by ring, Real.rpow_add_one ht0.ne']; ring
  have h1 : 1 / (1 + t) * t ^ (-β) ≤ t ^ (-β - 1) := by
    rw [e, ← mul_assoc]
    have : 1 / (1 + t) * t ≤ 1 := by rw [div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]; linarith
    nlinarith
  have hk : 1 ≤ β / 2 * (1 + Real.log (1 + t)) := by nlinarith
  have hk2 : t ^ (-β - 1) ≤ β / 2 * (1 + Real.log (1 + t)) * t ^ (-β - 1) := by nlinarith
  nlinarith

/-- **Limit with rate from a right-derivative bound.** -/
theorem limit_of_deriv_bound {ψ ψ' : ℝ → ℝ} {a₀ β D : ℝ} (ha₀ : 2 ≤ a₀) (hβ : 1 ≤ β) (hD : 0 ≤ D)
    (hcont : ∀ b, ContinuousOn ψ (Icc a₀ b))
    (hder : ∀ t, a₀ ≤ t → HasDerivWithinAt ψ (ψ' t) (Ici t) t)
    (hbd : ∀ t, a₀ ≤ t → |ψ' t| ≤ D * ((1 + Real.log (1 + t)) * t ^ (-β - 1))) :
    ∃ C : ℝ, ∀ t, a₀ ≤ t → |ψ t - C| ≤ 2 * D / β * Gfun β t := by
  have hβ0 : 0 < β := by linarith
  -- the comparison on `[a, u]`
  have hcmp : ∀ a u, a₀ ≤ a → a ≤ u → |ψ u - ψ a| ≤ 2 * D / β * (Gfun β a - Gfun β u) := by
    intro a u ha hau
    have hcontA : ContinuousOn (fun v => ψ v - ψ a) (Icc a u) :=
      ((hcont u).mono (Icc_subset_Icc ha le_rfl)).sub continuousOn_const
    have hderA : ∀ x ∈ Ico a u, HasDerivWithinAt (fun v => ψ v - ψ a) (ψ' x) (Ici x) x :=
      fun x hx => by simpa using (hder x (ha.trans hx.1)).sub_const (ψ a)
    have hBc : ContinuousOn (fun v => 2 * D / β * (Gfun β a - Gfun β v)) (Icc a u) := by
      intro v hv
      have hv0 : 0 < v := by linarith [hv.1]
      exact ((continuousAt_const.sub (Gfun_hasDeriv β hv0).continuousAt).const_mul _).continuousWithinAt
    have hBd : ∀ x ∈ Ico a u, HasDerivWithinAt (fun v => 2 * D / β * (Gfun β a - Gfun β v))
        (2 * D / β * -(1 / (1 + x) * x ^ (-β) + (1 + Real.log (1 + x)) * (-β * x ^ (-β - 1))))
        (Ici x) x := by
      intro x hx
      have hx0 : 0 < x := by linarith [hx.1]
      have := ((hasDerivAt_const x (Gfun β a)).sub (Gfun_hasDeriv β hx0)).const_mul (2 * D / β)
      simpa using this.hasDerivWithinAt
    have hbound : ∀ x ∈ Ico a u, ‖ψ' x‖ ≤
        2 * D / β * -(1 / (1 + x) * x ^ (-β) + (1 + Real.log (1 + x)) * (-β * x ^ (-β - 1))) := by
      intro x hx
      have hx2 : 2 ≤ x := by linarith [hx.1]
      rw [Real.norm_eq_abs]
      refine (hbd x (ha.trans hx.1)).trans ?_
      have h := neg_Gfun_deriv_ge hβ hx2
      have e : 2 * D / β * ((β / 2) * ((1 + Real.log (1 + x)) * x ^ (-β - 1))) =
          D * ((1 + Real.log (1 + x)) * x ^ (-β - 1)) := by field_simp
      rw [← e]
      exact mul_le_mul_of_nonneg_left h (by positivity)
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary' hcontA hderA
      (B := fun v => 2 * D / β * (Gfun β a - Gfun β v)) (by simp) hBc hBd hbound
      (x := u) ⟨hau, le_rfl⟩
    simpa [Real.norm_eq_abs] using this
  -- `G → 0`
  have hGle : ∀ t, 1 ≤ t → Gfun β t ≤ 5 * t ^ (-(1 / 2 : ℝ)) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hl := Real.log_le_rpow_div (x := 1 + t) (by linarith) (ε := 1 / 2) (by norm_num)
    have hs : (1 + t) ^ (1 / 2 : ℝ) ≤ 2 * t ^ (1 / 2 : ℝ) := by
      calc (1 + t) ^ (1 / 2 : ℝ) ≤ (4 * t) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
        _ = 4 ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) := Real.mul_rpow (by norm_num) ht0.le
        _ = 2 * t ^ (1 / 2 : ℝ) := by
            rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    have hh : 1 ≤ t ^ (1 / 2 : ℝ) := Real.one_le_rpow ht (by norm_num)
    have h1 : 1 + Real.log (1 + t) ≤ 5 * t ^ (1 / 2 : ℝ) := by
      have : Real.log (1 + t) ≤ 4 * t ^ (1 / 2 : ℝ) := by
        calc Real.log (1 + t) ≤ (1 + t) ^ (1 / 2 : ℝ) / (1 / 2) := hl
          _ ≤ 2 * t ^ (1 / 2 : ℝ) / (1 / 2) := by gcongr
          _ = 4 * t ^ (1 / 2 : ℝ) := by ring
      linarith
    have h2 : t ^ (-β) ≤ t ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht (by linarith)
    have h3 : t ^ (1 / 2 : ℝ) * t ^ (-1 : ℝ) = t ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add ht0]; norm_num
    unfold Gfun
    have hlog0 : 0 ≤ 1 + Real.log (1 + t) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + t by linarith); linarith
    calc (1 + Real.log (1 + t)) * t ^ (-β) ≤ (5 * t ^ (1 / 2 : ℝ)) * t ^ (-1 : ℝ) := by
          gcongr
      _ = 5 * t ^ (-(1 / 2 : ℝ)) := by rw [mul_assoc, h3]
  -- the Cauchy sequence
  set s : ℕ → ℝ := fun n => ψ (a₀ + n) with hs
  set b : ℕ → ℝ := fun N => 2 * (2 * D / β * (5 * (a₀ + N) ^ (-(1 / 2 : ℝ)))) with hb
  have hcs : CauchySeq s := by
    refine cauchySeq_of_le_tendsto_0 b (fun n m N hn hm => ?_) ?_
    · have hN : a₀ ≤ a₀ + N := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      have hNn : a₀ + N ≤ a₀ + n := by exact_mod_cast (by linarith [(Nat.cast_le.2 hn : (N : ℝ) ≤ n)] : a₀ + (N : ℝ) ≤ a₀ + n)
      have hNm : a₀ + N ≤ a₀ + m := by linarith [(Nat.cast_le.2 hm : (N : ℝ) ≤ m)]
      have h1 := hcmp (a₀ + N) (a₀ + n) hN hNn
      have h2 := hcmp (a₀ + N) (a₀ + m) hN hNm
      have g1 := Gfun_nonneg β (show 0 < a₀ + n by linarith)
      have g2 := Gfun_nonneg β (show 0 < a₀ + m by linarith)
      have gN := hGle (a₀ + N) (by linarith)
      have hc0 : 0 ≤ 2 * D / β := by positivity
      rw [Real.dist_eq]
      have : |s n - s m| ≤ |ψ (a₀ + n) - ψ (a₀ + N)| + |ψ (a₀ + m) - ψ (a₀ + N)| := by
        simp only [hs]
        calc |ψ (a₀ + n) - ψ (a₀ + m)| = |(ψ (a₀ + n) - ψ (a₀ + N)) - (ψ (a₀ + m) - ψ (a₀ + N))| := by
              ring_nf
          _ ≤ _ := abs_sub _ _
      simp only [hb]
      nlinarith
    · have h := (tendsto_rpow_neg_atTop (y := 1 / 2) (by norm_num)).comp
        (tendsto_atTop_add_const_left _ a₀ (tendsto_natCast_atTop_atTop (R := ℝ)))
      have := (h.const_mul (5 : ℝ)).const_mul (2 * D / β) |>.const_mul 2
      simp only [mul_zero] at this
      refine this.congr fun N => ?_
      simp [hb, Function.comp]
  obtain ⟨C, hC⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨C, fun t ht => ?_⟩
  have hev : ∀ᶠ n : ℕ in atTop, |ψ t - s n| ≤ 2 * D / β * Gfun β t := by
    obtain ⟨n0, hn0⟩ := exists_nat_ge t
    filter_upwards [eventually_ge_atTop n0] with n hn
    have htn : t ≤ a₀ + n := by
      have : (n0 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h := hcmp t (a₀ + n) ht htn
    have g := Gfun_nonneg β (show 0 < a₀ + n by linarith)
    have hc0 : 0 ≤ 2 * D / β := by positivity
    rw [abs_sub_comm]
    simp only [hs]
    nlinarith
  have hlim : Tendsto (fun n => |ψ t - s n|) atTop (𝓝 |ψ t - C|) :=
    ((continuous_const.sub continuous_id).abs.tendsto C).comp hC
  exact le_of_tendsto hlim hev

end RamanujanTau.SelbergDelange2
