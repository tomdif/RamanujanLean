/-
# Andrews 1966, M-c (first half): the coefficient integral on a horizontal line and its Farey dissection

* `coeff_line`: for `y > 0` and any `x₀`, `∫_{x₀}^{x₀+1} f(e^{2πiτ}) e^{−2πinτ} dx = α(n)`, `τ = x + iy`.
* Farey arcs of order `N` on the line `Im τ = y`: the arc of `h/k` (neighbour denominators `k_p`, `k_n`) is
  `[h/k − 1/(k(k+k_p)), h/k + 1/(k(k+k_n))]`; neighbouring arcs meet at the mediant, so the arcs of
  `0/1, …, (N−1)/N` tile `[−1/(N+1), N/(N+1)]` (`farey_line`).
* `arcs_approx`: if every arc integral is within `B(k)` of `M(h,k)`, then
  `‖α(n) − Σ_{h/k ∈ F_N} M(h,k)‖ ≤ Σ_{k ≤ N} k·B(k)`.
-/
import RamanujanTau.Andrews66.BNear
import RamanujanTau.Dragonette.Setup
import RamanujanTau.Rademacher.Assembly

set_option autoImplicit false

namespace Andrews66
open Complex Metric Filter MeasureTheory intervalIntegral HardyRamanujan
open scoped Real Topology

noncomputable section

/-- `τ = x + iy`. -/
abbrev tau (y x : ℝ) : ℂ := (x : ℂ) + y * I

/-- the integrand `f(e^{2πiτ}) e^{−2πinτ}`. -/
def gI (n : ℕ) (y x : ℝ) : ℂ := fA (cexp (2 * π * I * tau y x)) * cexp (-(2 * π * I * n * tau y x))

lemma norm_qtau (y x : ℝ) : ‖cexp (2 * π * I * tau y x)‖ = Real.exp (-(2 * π * y)) := by
  rw [norm_exp]; congr 1; simp [tau]

lemma qtau_mem {y : ℝ} (hy : 0 < y) (x : ℝ) : cexp (2 * π * I * tau y x) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_qtau, Real.exp_lt_one_iff]
  have := Real.pi_pos; nlinarith

lemma hasSum_f {q : ℂ} (hq : q ∈ ball (0 : ℂ) 1) : HasSum (fun k => (Dragonette.α k : ℂ) * q ^ k) (fA q) := by
  have h := MockTheta3.Radial.fA_T.1.hasSum hq
  simp only [Dragonette.coeff_T_fA] at h
  exact h

lemma fA_cont_on : ContinuousOn fA (ball 0 1) := MockTheta3.Radial.fA_T.1.continuousOn

lemma gI_cont (n : ℕ) {y : ℝ} (hy : 0 < y) : Continuous (gI n y) := by
  unfold gI
  refine Continuous.mul ?_ (by fun_prop)
  exact fA_cont_on.comp_continuous (by fun_prop) (fun x => qtau_mem hy x)

lemma integral_exp_period (m : ℤ) (x₀ : ℝ) :
    ∫ x in x₀..x₀ + 1, cexp (2 * π * I * m * x) = if m = 0 then 1 else 0 := by
  split_ifs with hm
  · subst hm; simp
  · have hc : (2 * π * I * m : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero)
        (by exact_mod_cast hm)
    have := integral_exp_mul_complex (a := x₀) (b := x₀ + 1) hc
    rw [this]
    have h2 : cexp (2 * π * I * m * ((x₀ + 1 : ℝ) : ℂ)) = cexp (2 * π * I * m * x₀) := by
      rw [show 2 * π * I * m * ((x₀ + 1 : ℝ) : ℂ) = 2 * π * I * m * x₀ + (m : ℂ) * (2 * π * I) by push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [h2, sub_self, zero_div]

/-- **the coefficient integral on a horizontal line**. -/
theorem coeff_line (n : ℕ) {y : ℝ} (hy : 0 < y) (x₀ : ℝ) :
    ∫ x in x₀..x₀ + 1, gI n y x = (Dragonette.α n : ℂ) := by
  have ht : 0 < 2 * π * y := by have := Real.pi_pos; positivity
  have hab : ∀ k, ‖(Dragonette.α k : ℂ)‖ ≤ p k := fun k => by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]; exact Dragonette.abs_α_le k
  let f : ℕ → C(ℝ, ℂ) := fun k =>
    ⟨fun x => (Dragonette.α k : ℂ) * cexp (2 * π * I * ((k : ℤ) - n : ℤ) * tau y x), by fun_prop⟩
  have hb : ∀ k, ‖(f k).restrict (⟨Set.uIcc x₀ (x₀ + 1), isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖
      ≤ (p k : ℝ) * Real.exp (-(k * (2 * π * y))) * Real.exp (n * (2 * π * y)) := by
    intro k
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun x => ?_
    simp only [ContinuousMap.restrict_apply, ContinuousMap.coe_mk, f]
    rw [norm_mul _ (cexp _), norm_exp, mul_assoc (p k : ℝ), ← Real.exp_add]
    gcongr
    · exact hab k
    · refine le_of_eq ?_; simp [tau]; ring
  have hsum : Summable fun k => ‖(f k).restrict (⟨Set.uIcc x₀ (x₀ + 1), isCompact_uIcc⟩ :
      TopologicalSpace.Compacts ℝ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb ((summable_p_exp ht).mul_right _)
  have H := hasSum_intervalIntegral_of_summable_norm hsum
  have hpt : ∀ x : ℝ, ∑' k, f k x = gI n y x := by
    intro x
    have h := (hasSum_f (qtau_mem hy x)).mul_right (cexp (-(2 * π * I * n * tau y x)))
    rw [gI, ← h.tsum_eq]
    congr 1; funext k
    simp only [f, ContinuousMap.coe_mk]
    rw [← Complex.exp_nat_mul, mul_assoc _ (cexp _) (cexp _), ← Complex.exp_add]
    congr 2; push_cast; ring
  simp only [hpt] at H
  rw [← H.tsum_eq]
  have hk : ∀ k, ∫ x in x₀..x₀ + 1, f k x = if k = n then (Dragonette.α n : ℂ) else 0 := by
    intro k
    simp only [f, ContinuousMap.coe_mk]
    have e : ∀ x : ℝ, (Dragonette.α k : ℂ) * cexp (2 * π * I * ((k : ℤ) - n : ℤ) * tau y x) =
        ((Dragonette.α k : ℂ) * cexp (-(2 * π * (((k : ℤ) - n : ℤ) : ℂ) * y))) *
          cexp (2 * π * I * (((k : ℤ) - n : ℤ) : ℂ) * x) := by
      intro x; rw [mul_assoc _ (cexp _) (cexp _), ← Complex.exp_add]; congr 2; simp only [tau]
      ring_nf; rw [I_sq]; ring
    simp only [e, intervalIntegral.integral_const_mul, integral_exp_period]
    split_ifs with h1 h2 h2
    · subst h2; simp
    · exact absurd (by omega) h2
    · exact absurd (by subst h2; simp) h1
    · simp
  simp only [hk]
  rw [tsum_ite_eq]

/-! ### Farey arcs on the line -/

/-- the left end `h/k − 1/(k(k+k_p))`. -/
def Lend (h k kp : ℕ) : ℝ := (h : ℝ) / k - 1 / (k * (k + kp))
/-- the right end `h/k + 1/(k(k+k_n))`. -/
def Rend (h k kn : ℕ) : ℝ := (h : ℝ) / k + 1 / (k * (k + kn))

/-- the arc integral. -/
def arcI (n : ℕ) (y : ℝ) (h k kp kn : ℕ) : ℂ := ∫ x in Lend h k kp..Rend h k kn, gI n y x

lemma Rend_eq_Lend {h k h₂ k₂ : ℕ} (hk : 0 < k) (hk₂ : 0 < k₂) (hdet : k * h₂ = h * k₂ + 1) :
    Rend h k k₂ = Lend h₂ k₂ k := by
  have hdet' : (k : ℝ) * h₂ = h * k₂ + 1 := by exact_mod_cast hdet
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hk20 : (k₂ : ℝ) ≠ 0 := by exact_mod_cast hk₂.ne'
  have hs : (k : ℝ) + k₂ ≠ 0 := by positivity
  have hs' : (k₂ : ℝ) + k ≠ 0 := by positivity
  have e : (h₂ : ℝ) = (h * k₂ + 1) / k := by rw [eq_div_iff hk0, ← hdet']; ring
  unfold Rend Lend
  rw [e]
  field_simp
  ring

/-- the sum of the arc integrals along a chain. -/
def arcSum (n : ℕ) (y : ℝ) : ℕ → List (ℕ × ℕ) → ℂ
  | _, [] => 0
  | _, [_] => 0
  | kp, x :: z :: rest => arcI n y x.1 x.2 kp z.2 + arcSum n y x.2 (z :: rest)

lemma tele_line (n N : ℕ) {y : ℝ} (hy : 0 < y) : ∀ (rest : List (ℕ × ℕ)) (kp : ℕ) (x : ℕ × ℕ),
    List.IsChain (Rademacher.Farey.Nb N) (x :: rest) → (∀ z ∈ x :: rest, 0 < z.2) →
    arcSum n y kp (x :: rest) = ∫ u in Lend x.1 x.2 kp..Lend (Rademacher.lastPrev kp (x :: rest)).1.1
      (Rademacher.lastPrev kp (x :: rest)).1.2 (Rademacher.lastPrev kp (x :: rest)).2, gI n y u := by
  intro rest
  induction rest with
  | nil => intro kp x _ _; simp [arcSum, Rademacher.lastPrev]
  | cons z rest ih =>
    intro kp x hc hpos
    rw [List.isChain_cons_cons] at hc
    have hx : 0 < x.2 := hpos x (by simp)
    have hz : 0 < z.2 := hpos z (by simp)
    have ih' := ih x.2 z hc.2 (fun w hw => hpos w (List.mem_cons_of_mem _ hw))
    rw [arcSum, ih', Rademacher.lastPrev, arcI, Rend_eq_Lend hx hz hc.1.1]
    exact intervalIntegral.integral_add_adjacent_intervals ((gI_cont n hy).intervalIntegrable _ _)
      ((gI_cont n hy).intervalIntegrable _ _)

/-- **the Farey dissection of the line**: `α(n) = Σ_{arcs} ∫_{arc} f(e^{2πiτ}) e^{−2πinτ} dx`. -/
theorem farey_line (n N : ℕ) (hN : 1 ≤ N) {y : ℝ} (hy : 0 < y) :
    (Dragonette.α n : ℂ) = arcSum n y N (Rademacher.fareyList N) := by
  have ht := tele_line n N hy (Rademacher.Farey.sb N 0 1 1 1 ++ [(1, 1)]) N (0, 1)
    (Rademacher.farey_chain N) (Rademacher.farey_pos N)
  rw [Rademacher.fareyList, ht]
  rw [show (0, 1) :: (Rademacher.Farey.sb N 0 1 1 1 ++ [(1, 1)]) =
      ((0, 1) :: Rademacher.Farey.sb N 0 1 1 1) ++ [(1, 1)] by simp,
    Rademacher.lastPrev_append N (1, 1) _ (List.cons_ne_nil _ _)]
  set w := ((0, 1) :: Rademacher.Farey.sb N 0 1 1 1).getLast (List.cons_ne_nil _ _) with hw
  have hwN : w.2 = N := by
    have hc := Rademacher.farey_chain N
    rw [Rademacher.fareyList, show (0, 1) :: (Rademacher.Farey.sb N 0 1 1 1 ++ [(1, 1)]) =
      ((0, 1) :: Rademacher.Farey.sb N 0 1 1 1) ++ [(1, 1)] by simp, List.isChain_append] at hc
    have hrel := hc.2.2 w (by simp [hw, List.getLast?_eq_some_getLast]) (1, 1) (by simp)
    have hmem : w ∈ (0, 1) :: Rademacher.Farey.sb N 0 1 1 1 := List.getLast_mem _
    have hle : w.2 ≤ N := by
      rcases List.mem_cons.mp hmem with h | h
      · rw [h]; exact hN
      · exact (Rademacher.Farey.mem_sb N 0 1 1 1 (by norm_num) w h).2.2.2.1
    have := hrel.2
    simp only at this hrel
    omega
  simp only [hwN]
  have hL : Lend 1 1 N = Lend 0 1 N + 1 := by unfold Lend; push_cast; ring
  rw [hL, coeff_line n hy]

/-! ### approximating the arcs -/

/-- **the whole chain**, for an arbitrary per-arc approximation `M` with error `B`. -/
lemma arcSum_approx (n N : ℕ) {y : ℝ} (M : ℕ × ℕ → ℂ) (B : ℕ → ℝ)
    (hM : ∀ h k kp kn : ℕ, 0 < k → k ≤ N → kp ≤ N → kn ≤ N → N < k + kp → N < k + kn → Nat.Coprime h k →
      (k : ℤ) ∣ h * kn + 1 → ‖arcI n y h k kp kn - M (h, k)‖ ≤ B k) :
    ∀ (rest : List (ℕ × ℕ)) (kp : ℕ) (x : ℕ × ℕ),
    List.IsChain (Rademacher.Farey.Nb N) (x :: rest) → (∀ z ∈ x :: rest, Rademacher.Good N z) → kp ≤ N →
    N < x.2 + kp →
    ‖arcSum n y kp (x :: rest) - (((x :: rest).dropLast).map M).sum‖ ≤
      (((x :: rest).dropLast).map fun z => B z.2).sum := by
  intro rest
  induction rest with
  | nil => intro kp x _ _ _ _; simp [arcSum]
  | cons z rest ih =>
    intro kp x hc hg hkp1 hkp
    rw [List.isChain_cons_cons] at hc
    have hx := hg x (by simp)
    have hz := hg z (by simp)
    have ih' := ih x.2 z hc.2 (fun w hw => hg w (List.mem_cons_of_mem _ hw)) hx.2.1 (by have := hc.1.2; omega)
    rw [arcSum, List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _), List.map_cons, List.sum_cons,
      List.map_cons, List.sum_cons]
    have hp := hM x.1 x.2 kp z.2 hx.1 hx.2.1 hkp1 hz.2.1 (by omega) (by have := hc.1.2; omega) hx.2.2 (by
        have h1 : x.2 * z.1 = x.1 * z.2 + 1 := hc.1.1
        exact ⟨z.1, by push_cast; linarith [show ((x.2 : ℤ) * z.1) = x.1 * z.2 + 1 by exact_mod_cast h1]⟩)
    calc ‖arcI n y x.1 x.2 kp z.2 + arcSum n y x.2 (z :: rest) -
          (M x + (((z :: rest).dropLast).map M).sum)‖
        = ‖(arcI n y x.1 x.2 kp z.2 - M x) + (arcSum n y x.2 (z :: rest) -
          (((z :: rest).dropLast).map M).sum)‖ := by congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hp ih')

/-- **the approximation of `α(n)` by per-arc main terms**. -/
theorem arcs_approx (n N : ℕ) (hN : 1 ≤ N) {y : ℝ} (hy : 0 < y) (M : ℕ × ℕ → ℂ) (B : ℕ → ℝ)
    (hB : ∀ k, 0 ≤ B k)
    (hM : ∀ h k kp kn : ℕ, 0 < k → k ≤ N → kp ≤ N → kn ≤ N → N < k + kp → N < k + kn → Nat.Coprime h k →
      (k : ℤ) ∣ h * kn + 1 → ‖arcI n y h k kp kn - M (h, k)‖ ≤ B k) :
    ‖(Dragonette.α n : ℂ) - ∑ k ∈ Finset.Icc 1 N,
        ∑ h ∈ (Finset.range k).filter (fun h => Nat.Coprime h k), M (h, k)‖ ≤
      ∑ k ∈ Finset.Icc 1 N, k * B k := by
  have h1 := arcSum_approx n N M B hM _ N (0, 1) (Rademacher.farey_chain N) (Rademacher.fareyList_good hN)
    le_rfl (by simp)
  rw [← Rademacher.fareyList, ← farey_line n N hN hy, Rademacher.fareyList_dropLast,
    Rademacher.fracList_sum hN, Rademacher.fracList_sum hN, Rademacher.Frac_sum, Rademacher.Frac_sum] at h1
  refine h1.trans (Finset.sum_le_sum fun k _ => ?_)
  simp only
  rw [Finset.sum_const, nsmul_eq_mul]
  gcongr
  · exact hB k
  exact (Finset.card_filter_le _ _).trans (by simp)

end

end Andrews66
