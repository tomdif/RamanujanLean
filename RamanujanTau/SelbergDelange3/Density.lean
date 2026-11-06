/-
# Upper bounds for non-negative functions with a Mertens-type upper bound on `Λ_F`

Let `F, G ≥ 0` with `F log = G ∗ F`, `Σ_{m≤z} G(m)/m ≤ σ log z + A` and `Σ_{m≤z} G(m) ≤ A₂ z`.

* `logmean_upper_nonneg`: `Σ_{n≤y} F(n)/n ≤ C (1 + log y)^σ`
  (`key_identity` with `R ≤ 0`; `Î(t)(t−A)^{−(1+σ)}` is non-increasing).
* `cheb_step`: `Σ_{n≤N} F(n) log n ≤ A₂ N Σ_{n≤N} F(n)/n`.
* `density_nonneg`: `Σ_{n≤y} F(n) ≤ K y (1 + log y)^{σ−1}` (split at `√y`).
-/
import RamanujanTau.SelbergDelange2.ODE

set_option autoImplicit false

namespace RamanujanTau.SelbergDelange3

open Finset Set Filter Topology ArithmeticFunction
open RamanujanTau.SelbergDelange2

variable (F G : ArithmeticFunction ℝ)

lemma Ssum_mono (hF0 : ∀ n, 0 ≤ F n) {y z : ℝ} (hyz : y ≤ z) : Ssum F y ≤ Ssum F z := by
  unfold Ssum
  refine sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right (Nat.floor_le_floor hyz))
    fun n _ _ => div_nonneg (hF0 n) (Nat.cast_nonneg n)

theorem logmean_upper_nonneg (hF0 : ∀ n, 0 ≤ F n) (hconv : ∀ n : ℕ, 0 < n → F n * Real.log n = (G * F) n)
    {σ A : ℝ} (hσ : 0 ≤ σ) (hA : 0 ≤ A) (hMu : ∀ z : ℝ, 1 ≤ z → Msum G z ≤ σ * Real.log z + A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y → Ssum F y ≤ C * (1 + Real.log y) ^ σ := by
  set a₀ : ℝ := A + 1 with ha₀
  set p : ℝ := -(1 + σ) with hp
  set ψ : ℝ → ℝ := fun u => Isum F (Real.exp u) * (u - A) ^ p with hψ
  have hErr : ∀ z : ℝ, 1 ≤ z → Err G σ A z ≤ 0 := fun z hz => by
    have := hMu z hz; unfold Err; linarith
  have hR : ∀ x : ℝ, 1 ≤ x → Rsum F G σ A x ≤ 0 := by
    intro x hx
    unfold Rsum
    refine sum_nonpos fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.1 hn).1
    have hxn : 1 ≤ x / n := by
      rw [le_div_iff₀ hn0, one_mul]
      exact (Nat.cast_le.2 (Finset.mem_Ioc.1 hn).2).trans (Nat.floor_le (by linarith))
    exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg (hF0 n) hn0.le) (hErr _ hxn)
  -- ψ is non-increasing on `[a₀, ∞)`
  have hmono : ∀ t, a₀ ≤ t → ψ t ≤ ψ a₀ := by
    intro t ht
    have hc : ContinuousOn ψ (Icc a₀ t) := by
      refine (Ihat_continuousOn F a₀ t).mul ?_
      refine ContinuousOn.rpow_const (continuousOn_id.sub continuousOn_const) fun u hu => Or.inl ?_
      have h2 : a₀ ≤ u := hu.1
      have h : (0 : ℝ) < u - A := by linarith
      exact h.ne'
    have hd : ∀ x ∈ Ico a₀ t, HasDerivWithinAt ψ
        (Rsum F G σ A (Real.exp x) * (x - A) ^ (p - 1)) (Ici x) x := by
      intro x hx
      have hpos : 0 < x - A := by linarith [hx.1]
      have h1 := Ihat_hasDeriv F x
      have h2 : HasDerivAt (fun u : ℝ => (u - A) ^ p) (1 * p * (x - A) ^ (p - 1)) x :=
        ((hasDerivAt_id x).sub_const A).rpow_const (Or.inl hpos.ne')
      refine (h1.mul h2.hasDerivWithinAt).congr_deriv ?_
      have hx1 : 1 ≤ Real.exp x := Real.one_le_exp (by linarith [hx.1])
      have hid := key_identity F G hconv σ A hx1
      rw [Real.log_exp] at hid
      have e : (x - A) ^ p = (x - A) * (x - A) ^ (p - 1) := by
        rw [show p = (p - 1) + 1 by ring, Real.rpow_add_one hpos.ne']; ring_nf
      rw [e]
      have : Ssum F (Real.exp x) * ((x - A) * (x - A) ^ (p - 1)) +
          Isum F (Real.exp x) * (1 * p * (x - A) ^ (p - 1)) =
          ((x - A) * Ssum F (Real.exp x) + p * Isum F (Real.exp x)) * (x - A) ^ (p - 1) := by ring
      rw [this, hid, hp]; ring
    have := image_le_of_deriv_right_le_deriv_boundary hc hd (B := fun _ => ψ a₀) (B' := fun _ => 0)
      le_rfl continuousOn_const (fun x _ => hasDerivWithinAt_const _ _ _) (fun x hx => ?_)
      (x := t) ⟨ht, le_rfl⟩
    · exact this
    · have hpos : 0 < x - A := by linarith [hx.1]
      exact mul_nonpos_of_nonpos_of_nonneg (hR _ (Real.one_le_exp (by linarith [hx.1])))
        (Real.rpow_nonneg hpos.le _)
  set P : ℝ := max (ψ a₀) 0 with hP
  have hP0 : 0 ≤ P := le_max_right _ _
  -- the bound for `t ≥ a₀`
  have hbig : ∀ t, a₀ ≤ t → Ssum F (Real.exp t) ≤ (1 + σ) * P * (1 + t) ^ σ := by
    intro t ht
    have hpos : 0 < t - A := by linarith
    have hx1 : 1 ≤ Real.exp t := Real.one_le_exp (by linarith)
    have hid := key_identity F G hconv σ A hx1
    rw [Real.log_exp] at hid
    have hI : Isum F (Real.exp t) = ψ t * (t - A) ^ (1 + σ) := by
      have h1 : (t - A) ^ p * (t - A) ^ (1 + σ) = 1 := by
        rw [← Real.rpow_add hpos, hp]; simp
      calc Isum F (Real.exp t) = Isum F (Real.exp t) * ((t - A) ^ p * (t - A) ^ (1 + σ)) := by
            rw [h1, mul_one]
        _ = ψ t * (t - A) ^ (1 + σ) := by simp only [hψ]; ring
    have hψP : ψ t ≤ P := (hmono t ht).trans (le_max_left _ _)
    have hRt := hR _ hx1
    have hq : 0 ≤ (t - A) ^ (1 + σ) := Real.rpow_nonneg hpos.le _
    have e : (t - A) ^ (1 + σ) = (t - A) * (t - A) ^ σ := by
      rw [Real.rpow_add hpos, Real.rpow_one]
    have h2 : (t - A) * Ssum F (Real.exp t) ≤ (t - A) * ((1 + σ) * P * (t - A) ^ σ) := by
      rw [hid, hI]
      have : (1 + σ) * (ψ t * (t - A) ^ (1 + σ)) ≤ (1 + σ) * (P * (t - A) ^ (1 + σ)) := by
        gcongr
      rw [e] at this ⊢
      linarith
    have h3 := le_of_mul_le_mul_left h2 hpos
    have h4 : (t - A) ^ σ ≤ (1 + t) ^ σ := Real.rpow_le_rpow hpos.le (by linarith) hσ
    calc Ssum F (Real.exp t) ≤ (1 + σ) * P * (t - A) ^ σ := h3
      _ ≤ (1 + σ) * P * (1 + t) ^ σ := by gcongr
  refine ⟨(1 + σ) * P * (1 + a₀) ^ σ, by positivity, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  have hl0 : 0 ≤ Real.log y := Real.log_nonneg hy
  have hone : 1 ≤ (1 + Real.log y) ^ σ := Real.one_le_rpow (by linarith) hσ
  have hone' : 1 ≤ (1 + a₀) ^ σ := Real.one_le_rpow (by linarith) hσ
  rcases le_or_gt a₀ (Real.log y) with h | h
  · have := hbig (Real.log y) h
    rw [Real.exp_log hy0] at this
    refine this.trans ?_
    have : 0 ≤ (1 + σ) * P * (1 + Real.log y) ^ σ := by positivity
    nlinarith
  · have h1 : Ssum F y ≤ Ssum F (Real.exp a₀) := by
      apply Ssum_mono F hF0
      rw [← Real.exp_log hy0]; exact Real.exp_le_exp.mpr h.le
    have h2 := hbig a₀ le_rfl
    have : 0 ≤ (1 + σ) * P * (1 + a₀) ^ σ := by positivity
    nlinarith

theorem cheb_step (hF0 : ∀ n, 0 ≤ F n) (hconv : ∀ n : ℕ, 0 < n → F n * Real.log n = (G * F) n)
    {A₂ : ℝ} (hA2 : 0 ≤ A₂) (hCh : ∀ z : ℝ, 1 ≤ z → ∑ d ∈ Finset.Ioc 0 ⌊z⌋₊, G d ≤ A₂ * z) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, F n * Real.log n ≤ A₂ * N * ∑ n ∈ Finset.Ioc 0 N, F n / n := by
  have h := sum_Ioc_mul_eq_sum_sum F G N
  rw [mul_comm F G] at h
  rw [show ∑ n ∈ Finset.Ioc 0 N, F n * Real.log n = ∑ n ∈ Finset.Ioc 0 N, (G * F) n from
    sum_congr rfl fun n hn => hconv n (Finset.mem_Ioc.1 hn).1, h, mul_sum]
  refine sum_le_sum fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Ioc.1 hk).1
  have hkN : k ≤ N := (Finset.mem_Ioc.1 hk).2
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hq : 1 ≤ N / k := (Nat.one_le_div_iff hk1).2 hkN
  have h1 := hCh ((N / k : ℕ) : ℝ) (by exact_mod_cast hq)
  rw [Nat.floor_natCast] at h1
  have h2 : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / k := Nat.cast_div_le
  calc F k * ∑ d ∈ Finset.Ioc 0 (N / k), G d ≤ F k * (A₂ * ((N / k : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (hF0 k)
    _ ≤ F k * (A₂ * ((N : ℝ) / k)) := by gcongr; exact hF0 k
    _ = A₂ * N * (F k / k) := by ring

theorem density_nonneg (hF0 : ∀ n, 0 ≤ F n) (hG0 : ∀ n, 0 ≤ G n)
    (hconv : ∀ n : ℕ, 0 < n → F n * Real.log n = (G * F) n)
    {σ A A₂ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hA : 0 ≤ A)
    (hMu : ∀ z : ℝ, 1 ≤ z → Msum G z ≤ σ * Real.log z + A)
    (hCh : ∀ z : ℝ, 1 ≤ z → ∑ d ∈ Finset.Ioc 0 ⌊z⌋₊, G d ≤ A₂ * z) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 1 ≤ y →
      ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, F n ≤ K * y * (1 + Real.log y) ^ (σ - 1) := by
  obtain ⟨C, hC0, hC⟩ := logmean_upper_nonneg F G hF0 hconv hσ hA hMu
  have hA2 : 0 ≤ A₂ := by
    have := hCh 1 le_rfl
    have h0 : ∑ d ∈ Finset.Ioc 0 ⌊(1 : ℝ)⌋₊, G d = G 1 := by simp
    rw [h0] at this; linarith [hG0 1]
  refine ⟨C * (12 + 4 * A₂), by positivity, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  set t := Real.log y with ht
  have ht0 : 0 ≤ t := Real.log_nonneg hy
  set N := ⌊y⌋₊ with hN
  have hNy : (N : ℝ) ≤ y := Nat.floor_le hy0.le
  have hS := hC y hy
  have hSnn : 0 ≤ Ssum F y := sum_nonneg fun n _ => div_nonneg (hF0 n) (Nat.cast_nonneg n)
  have hpow : (1 + t) ^ σ = (1 + t) * (1 + t) ^ (σ - 1) := by
    rw [show σ = (σ - 1) + 1 by ring, Real.rpow_add_one (by linarith)]; ring_nf
  have hq0 : 0 < (1 + t) ^ (σ - 1) := Real.rpow_pos_of_pos (by linarith) _
  rcases lt_or_ge t 1 with h1 | h1
  · -- small `y`: `N ≤ 2`
    have hy3 : y < 3 := by
      have := Real.exp_one_lt_d9
      have : y < Real.exp 1 := by rw [← Real.exp_log hy0]; exact Real.exp_lt_exp.mpr h1
      linarith
    have hterm : ∀ n ∈ Finset.Ioc 0 N, F n ≤ 3 * (F n / n) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.1 hn).1
      have hn3 : (n : ℝ) ≤ 3 := by
        have := (Nat.cast_le.2 (Finset.mem_Ioc.1 hn).2).trans hNy; linarith
      rw [mul_div_assoc', le_div_iff₀ hn0]
      nlinarith [hF0 n]
    have hsum : ∑ n ∈ Finset.Ioc 0 N, F n ≤ 3 * Ssum F y := by
      rw [Ssum, mul_sum]; exact sum_le_sum hterm
    have hq1 : 1 / 2 ≤ (1 + t) ^ (σ - 1) := by
      have : (2 : ℝ) ^ (σ - 1) ≤ (1 + t) ^ (σ - 1) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
      have h2 : (1 / 2 : ℝ) ≤ 2 ^ (σ - 1) := by
        calc (1 / 2 : ℝ) = 2 ^ (-1 : ℝ) := by norm_num
          _ ≤ 2 ^ (σ - 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      linarith
    have hpw : (1 + t) ^ σ ≤ 2 := by
      calc (1 + t) ^ σ ≤ (1 + t) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hσ1
        _ ≤ 2 := by rw [Real.rpow_one]; linarith
    calc ∑ n ∈ Finset.Ioc 0 N, F n ≤ 3 * Ssum F y := hsum
      _ ≤ 3 * (C * 2) := by
          have := mul_le_mul_of_nonneg_left hpw hC0; linarith
      _ ≤ C * (12 + 4 * A₂) * y * (1 + t) ^ (σ - 1) := by
          have hyq : 1 / 2 ≤ y * (1 + t) ^ (σ - 1) := by
            have := mul_le_mul_of_nonneg_right hy hq0.le
            linarith
          have hK : 0 ≤ C * (12 + 4 * A₂) := by positivity
          have := mul_le_mul_of_nonneg_left hyq hK
          have e : C * (12 + 4 * A₂) * y * (1 + t) ^ (σ - 1) =
              C * (12 + 4 * A₂) * (y * (1 + t) ^ (σ - 1)) := by ring
          rw [e]
          have : 0 ≤ C * A₂ := by positivity
          nlinarith
  · -- `y ≥ e`
    have hsq : Real.sqrt y * (1 + t) ≤ 2 * y := by
      have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
      have hl : t ≤ 2 * (Real.sqrt y - 1) := by
        have := Real.log_le_sub_one_of_pos hs0
        have h2 := Real.log_sqrt hy0.le
        rw [← ht] at h2
        linarith
      have hss : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
      nlinarith
    have hterm : ∀ n ∈ Finset.Ioc 0 N,
        F n ≤ Real.sqrt y * (F n / n) + 2 / t * (F n * Real.log n) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.1 hn).1
      have hFn := hF0 n
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.1 hn).1
      have hln : 0 ≤ Real.log n := Real.log_nonneg hn1
      have ht1 : 0 < t := by linarith
      rcases le_or_gt (n : ℝ) (Real.sqrt y) with hc | hc
      · have : F n ≤ Real.sqrt y * (F n / n) := by
          rw [mul_div_assoc', le_div_iff₀ hn0]; nlinarith
        have : 0 ≤ 2 / t * (F n * Real.log n) := by positivity
        linarith
      · have hl : t / 2 < Real.log n := by
          have := Real.log_lt_log (Real.sqrt_pos.2 hy0) hc
          rw [Real.log_sqrt hy0.le] at this; linarith
        have : F n ≤ 2 / t * (F n * Real.log n) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ ht1]; nlinarith
        have : 0 ≤ Real.sqrt y * (F n / n) := by positivity
        linarith
    have hsum : ∑ n ∈ Finset.Ioc 0 N, F n ≤ Real.sqrt y * Ssum F y +
        2 / t * (A₂ * N * Ssum F y) := by
      have h1 := sum_le_sum hterm
      rw [sum_add_distrib, ← mul_sum, ← mul_sum] at h1
      have h2 := cheb_step F G hF0 hconv hA2 hCh N
      have ht1 : 0 < t := by linarith
      rw [Ssum, ← hN]
      have : 2 / t * ∑ n ∈ Finset.Ioc 0 N, F n * Real.log n ≤
          2 / t * (A₂ * N * ∑ n ∈ Finset.Ioc 0 N, F n / n) := by gcongr
      linarith
    have ht1 : 0 < t := by linarith
    have h2t : (1 + t) / t ≤ 2 := by rw [div_le_iff₀ ht1]; linarith
    have hB : 2 / t * (A₂ * N * Ssum F y) ≤ A₂ * y * (2 / t) * (C * (1 + t) ^ σ) := by
      have : 2 / t * (A₂ * N * Ssum F y) = A₂ * N * (2 / t) * Ssum F y := by ring
      rw [this]
      have : 0 ≤ A₂ * (2 / t) := by positivity
      have hN' : A₂ * N * (2 / t) ≤ A₂ * y * (2 / t) := by
        have := mul_le_mul_of_nonneg_left hNy (le_of_lt (by positivity : (0:ℝ) < 1) |>.trans le_rfl)
        nlinarith
      exact mul_le_mul hN' hS hSnn (by positivity)
    have hA' : Real.sqrt y * Ssum F y ≤ Real.sqrt y * (C * (1 + t) ^ σ) :=
      mul_le_mul_of_nonneg_left hS (Real.sqrt_nonneg _)
    rw [hpow] at hA' hB
    have e1 : Real.sqrt y * (C * ((1 + t) * (1 + t) ^ (σ - 1))) =
        C * (1 + t) ^ (σ - 1) * (Real.sqrt y * (1 + t)) := by ring
    have e2 : A₂ * y * (2 / t) * (C * ((1 + t) * (1 + t) ^ (σ - 1))) =
        2 * A₂ * C * y * (1 + t) ^ (σ - 1) * ((1 + t) / t) := by field_simp
    rw [e1] at hA'
    rw [e2] at hB
    have hX : 0 ≤ C * (1 + t) ^ (σ - 1) := by positivity
    have hY : 0 ≤ 2 * A₂ * C * y * (1 + t) ^ (σ - 1) := by positivity
    have h3 : C * (1 + t) ^ (σ - 1) * (Real.sqrt y * (1 + t)) ≤ C * (1 + t) ^ (σ - 1) * (2 * y) :=
      mul_le_mul_of_nonneg_left hsq hX
    have h4 : 2 * A₂ * C * y * (1 + t) ^ (σ - 1) * ((1 + t) / t) ≤
        2 * A₂ * C * y * (1 + t) ^ (σ - 1) * 2 := mul_le_mul_of_nonneg_left h2t hY
    have hfin : ∑ n ∈ Finset.Ioc 0 N, F n ≤ C * (2 + 4 * A₂) * y * (1 + t) ^ (σ - 1) := by
      nlinarith
    have : 0 ≤ C * y * (1 + t) ^ (σ - 1) := by positivity
    nlinarith

end RamanujanTau.SelbergDelange3
