/-
# One `k`-th order difference instead of `k` halvings

`riesz_kdiff`: for `aₙ ≥ 0`, `c ≥ 0`, if `W_k(x) = c x^{k+1}/(k+1) + O(x^{k+1−θ})` then
`W_0(x) = c x + O(x^{1−θ/(k+1)})` (compare `riesz_descend`: `θ/2^k`).

Proof. With `Δ_h f(x) = f(x+h) − f(x)` and `D_h^k = Δ_h^k`:
* `W_{j+1}(x+h) − W_{j+1}(x) = (j+1)∫₀^h W_j(x+s) ds` (from `ψ_{j+1}' = (j+1)ψ_j`,
  `ψ_j(u) = u_+^j`), and the same for `M_j(x) = c x^{j+1}/(j+1)`;
* hence (`bracket`), for every such family with `F_0` monotone,
  `k! h^k F_0(x) ≤ D_h^k F_k(x) ≤ k! h^k F_0(x + kh)`;
* `|D_h^k E(x)| ≤ 2^k sup_{[x, x+kh]} |E|`;
* take `h = x^{1−θ/(k+1)}/(k+1)`.
-/
import RamanujanTau.RankinError.Riesz

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Finset Real MeasureTheory Set intervalIntegral

/-! ### The difference operator -/

/-- `Dk h k f = Δ_h^k f`, `Δ_h f(x) = f(x+h) − f(x)`. -/
noncomputable def Dk (h : ℝ) : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | k + 1, f => Dk h k (fun x => f (x + h) - f x)

lemma Dk_sub (h : ℝ) (k : ℕ) : ∀ (f g : ℝ → ℝ) (x : ℝ),
    Dk h k (fun y => f y - g y) x = Dk h k f x - Dk h k g x := by
  induction k with
  | zero => intro f g x; rfl
  | succ k ih =>
    intro f g x
    simp only [Dk]
    rw [← ih]
    congr 1; funext y; ring

lemma Dk_const_mul (h : ℝ) (k : ℕ) : ∀ (c : ℝ) (f : ℝ → ℝ) (x : ℝ),
    Dk h k (fun y => c * f y) x = c * Dk h k f x := by
  induction k with
  | zero => intro c f x; rfl
  | succ k ih =>
    intro c f x
    simp only [Dk]
    rw [← ih]
    congr 1; funext y; ring

lemma Dk_congr (h : ℝ) (k : ℕ) {f g : ℝ → ℝ} (hfg : f = g) (x : ℝ) : Dk h k f x = Dk h k g x := by
  rw [hfg]

/-- Locally integrable on every interval. -/
def LocII (f : ℝ → ℝ) : Prop := ∀ a b : ℝ, IntervalIntegrable f volume a b

lemma LocII.shift {f : ℝ → ℝ} (hf : LocII f) (c : ℝ) : LocII fun x => f (x + c) := by
  intro a b
  have := (hf (a + c) (b + c)).comp_add_right c
  simpa using this

lemma LocII.delta {f : ℝ → ℝ} (hf : LocII f) (h : ℝ) : LocII fun x => f (x + h) - f x :=
  fun a b => (hf.shift h a b).sub (hf a b)

lemma LocII.Dk {f : ℝ → ℝ} (hf : LocII f) (h : ℝ) (k : ℕ) : LocII (Dk h k f) := by
  induction k generalizing f with
  | zero => exact hf
  | succ k ih => exact ih (hf.delta h)

/-- `Δ^k` commutes with `∫₀^h · (·+s) ds`. -/
lemma Dk_integral (h : ℝ) (k : ℕ) : ∀ (g : ℝ → ℝ), LocII g → ∀ x : ℝ,
    Dk h k (fun y => ∫ s in (0 : ℝ)..h, g (y + s)) x = ∫ s in (0 : ℝ)..h, Dk h k g (x + s) := by
  induction k with
  | zero => intro g _ x; rfl
  | succ k ih =>
    intro g hg x
    simp only [Dk]
    have e : (fun y => (∫ s in (0 : ℝ)..h, g (y + h + s)) - ∫ s in (0 : ℝ)..h, g (y + s)) =
        fun y => ∫ s in (0 : ℝ)..h, (fun z => g (z + h) - g z) (y + s) := by
      funext y
      rw [← intervalIntegral.integral_sub]
      · congr 1; funext s; simp only; ring_nf
      · have := (hg.shift (y + h)) 0 h
        simpa [add_comm] using this
      · have := (hg.shift y) 0 h
        simpa [add_comm] using this
    rw [e, ih _ (hg.delta h)]

lemma abs_Dk_le (h : ℝ) (hh : 0 ≤ h) (k : ℕ) : ∀ (f : ℝ → ℝ) (x B : ℝ),
    (∀ y ∈ Icc x (x + k * h), |f y| ≤ B) → |Dk h k f x| ≤ 2 ^ k * B := by
  induction k with
  | zero =>
    intro f x B hB
    simpa using hB x ⟨le_rfl, by simp⟩
  | succ k ih =>
    intro f x B hB
    simp only [Dk]
    have := ih (fun y => f (y + h) - f y) x (2 * B) (fun y hy => by
      have h1 := hB (y + h) ⟨by linarith [hy.1], by push_cast at hy ⊢; linarith [hy.2]⟩
      have h2 := hB y ⟨hy.1, by push_cast at hy ⊢; nlinarith [hy.2]⟩
      calc |f (y + h) - f y| ≤ |f (y + h)| + |f y| := abs_sub _ _
        _ ≤ 2 * B := by linarith)
    rw [pow_succ]; linarith

/-! ### The bracket -/

/-- **Bracket.** For a family `F` with `F_{j+1}(x+h) − F_{j+1}(x) = (j+1)∫₀^h F_j(x+s) ds` and
`F_0` monotone: `k! h^k F_0(x) ≤ Δ_h^k F_k(x) ≤ k! h^k F_0(x + kh)`. -/
theorem bracket (F : ℕ → ℝ → ℝ) (hint : ∀ j, LocII (F j)) (hmono : Monotone (F 0))
    {h : ℝ} (hh : 0 ≤ h)
    (hrel : ∀ (j : ℕ) (x : ℝ), F (j + 1) (x + h) - F (j + 1) x =
      ((j : ℝ) + 1) * ∫ s in (0 : ℝ)..h, F j (x + s)) :
    ∀ (k : ℕ) (x : ℝ), (Nat.factorial k : ℝ) * h ^ k * F 0 x ≤ Dk h k (F k) x ∧
      Dk h k (F k) x ≤ (Nat.factorial k : ℝ) * h ^ k * F 0 (x + k * h) := by
  intro k
  induction k with
  | zero => intro x; simp [Dk]
  | succ k ih =>
    intro x
    have e : Dk h (k + 1) (F (k + 1)) x = ((k : ℝ) + 1) * ∫ s in (0 : ℝ)..h, Dk h k (F k) (x + s) := by
      simp only [Dk]
      rw [Dk_congr h k (show (fun y => F (k + 1) (y + h) - F (k + 1) y) =
        fun y => ((k : ℝ) + 1) * ∫ s in (0 : ℝ)..h, F k (y + s) from funext fun y => hrel k y),
        Dk_const_mul, Dk_integral h k _ (hint k)]
    rw [e]
    have hI : IntervalIntegrable (fun s => Dk h k (F k) (x + s)) volume 0 h := by
      have := ((hint k).Dk h k).shift x 0 h
      simpa [add_comm] using this
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hfac : ((Nat.factorial (k + 1) : ℕ) : ℝ) = ((k : ℝ) + 1) * (Nat.factorial k : ℝ) := by
      push_cast [Nat.factorial_succ]; ring
    constructor
    · have hlow : ∫ s in (0 : ℝ)..h, (Nat.factorial k : ℝ) * h ^ k * F 0 x ≤
          ∫ s in (0 : ℝ)..h, Dk h k (F k) (x + s) := by
        refine intervalIntegral.integral_mono_on hh intervalIntegral.intervalIntegrable_const hI fun s hs => ?_
        refine le_trans ?_ (ih (x + s)).1
        exact mul_le_mul_of_nonneg_left (hmono (by linarith [hs.1])) (by positivity)
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hlow
      rw [hfac, pow_succ]
      nlinarith
    · have hup : ∫ s in (0 : ℝ)..h, Dk h k (F k) (x + s) ≤
          ∫ s in (0 : ℝ)..h, (Nat.factorial k : ℝ) * h ^ k * F 0 (x + ((k + 1 : ℕ) : ℝ) * h) := by
        refine intervalIntegral.integral_mono_on hh hI intervalIntegral.intervalIntegrable_const fun s hs => ?_
        refine le_trans (ih (x + s)).2 ?_
        refine mul_le_mul_of_nonneg_left (hmono ?_) (by positivity)
        push_cast; nlinarith [hs.2]
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hup
      rw [hfac, pow_succ]
      nlinarith

/-! ### The two families -/

/-- `ψ_j(u) = u_+^j` (with `ψ_0 = 1_{u ≥ 0}`). -/
noncomputable def psi (j : ℕ) (u : ℝ) : ℝ := if 0 ≤ u then u ^ j else 0

lemma psi_eq_indicator (j : ℕ) : psi j = (Ici (0 : ℝ)).indicator fun u => u ^ j := by
  funext u; simp [psi, indicator]

lemma psi_intervalIntegrable (j : ℕ) (a b : ℝ) : IntervalIntegrable (psi j) volume a b := by
  rw [psi_eq_indicator, intervalIntegrable_iff]
  exact ((continuous_pow j).integrableOn_uIoc).indicator measurableSet_Ici

lemma continuous_psi_succ (j : ℕ) : Continuous (psi (j + 1)) := by
  unfold psi
  refine continuous_if_le continuous_const continuous_id (continuous_pow _).continuousOn
    continuousOn_const fun x hx => ?_
  simp [← hx]

lemma psi_ftc (j : ℕ) {a b : ℝ} (hab : a ≤ b) :
    psi (j + 1) b - psi (j + 1) a = ((j : ℝ) + 1) * ∫ u in a..b, psi j u := by
  rw [← intervalIntegral.integral_const_mul]
  symm
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    (continuous_psi_succ j).continuousOn (fun x _ => ?_)
    ((psi_intervalIntegrable j a b).const_mul _)
  rcases le_or_gt 0 x with hx | hx
  · have hd := (hasDerivAt_pow (j + 1) x).hasDerivWithinAt (s := Ioi x)
    have e : ((j + 1 : ℕ) : ℝ) * x ^ j = ((j : ℝ) + 1) * psi j x := by
      simp [psi, hx]
    rw [Nat.add_sub_cancel, e] at hd
    refine hd.congr (fun y hy => ?_) ?_
    · simp [psi, show (0 : ℝ) ≤ y by linarith [mem_Ioi.1 hy]]
    · simp [psi, hx]
  · have e : ((j : ℝ) + 1) * psi j x = 0 := by simp [psi, not_le.2 hx]
    rw [e]
    refine (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, (Iio_mem_nhds hx : Iio (0 : ℝ) ∈ nhds x) |>
        nhdsWithin_le_nhds] with y _ hy
      simp [psi, not_le.2 (mem_Iio.1 hy)]
    · simp [psi, not_le.2 hx]

lemma W_eq_psi_sum (a : ℕ → ℝ) (j : ℕ) {M : ℕ} {u : ℝ} (hu : u < M + 1) :
    W a j u = ∑ n ∈ Icc 1 M, a n * psi j (u - n) := by
  unfold W psi
  have hsub : Finset.Icc 1 ⌊u⌋₊ ⊆ Finset.Icc 1 M := by
    refine Finset.Icc_subset_Icc le_rfl ?_
    rcases lt_or_ge u 0 with h | h
    · simp [Nat.floor_eq_zero.2 (by linarith : u < 1)]
    · have : ⌊u⌋₊ < M + 1 := (Nat.floor_lt h).2 (by push_cast; exact hu)
      omega
  rw [← sum_subset hsub]
  · refine sum_congr rfl fun n hn => ?_
    have h1 := (mem_Icc.1 hn).2
    have hu0 : 0 ≤ u := by
      have : 1 ≤ ⌊u⌋₊ := le_trans (mem_Icc.1 hn).1 h1
      by_contra h; push Not at h
      simp [Nat.floor_eq_zero.2 (by linarith : u < 1)] at this
    have : (n : ℝ) ≤ u := (Nat.cast_le.2 h1).trans (Nat.floor_le hu0)
    rw [if_pos (by linarith)]
  · intro n hn hn'
    rw [if_neg, mul_zero]
    intro h0
    apply hn'
    refine mem_Icc.2 ⟨(mem_Icc.1 hn).1, ?_⟩
    exact Nat.le_floor (by linarith)

lemma W_mono (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (j : ℕ) : Monotone (W a j) := by
  intro x y hxy
  rcases lt_or_ge x 0 with hx | hx
  · rw [W_eq_zero_of_lt_one a j (by linarith)]
    unfold W
    refine sum_nonneg fun n hn => mul_nonneg (ha n) (pow_nonneg ?_ _)
    have h1 := (mem_Icc.1 hn).2
    have hy0 : 0 ≤ y := by
      have : 1 ≤ ⌊y⌋₊ := le_trans (mem_Icc.1 hn).1 h1
      by_contra h; push Not at h
      simp [Nat.floor_eq_zero.2 (by linarith : y < 1)] at this
    have : (n : ℝ) ≤ y := (Nat.cast_le.2 h1).trans (Nat.floor_le hy0)
    linarith
  · unfold W
    have hsub : Finset.Icc 1 ⌊x⌋₊ ⊆ Finset.Icc 1 ⌊y⌋₊ :=
      Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hxy)
    refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => ?_)
    · refine sum_le_sum fun n hn => mul_le_mul_of_nonneg_left ?_ (ha n)
      have : (n : ℝ) ≤ x := (Nat.cast_le.2 (mem_Icc.1 hn).2).trans (Nat.floor_le hx)
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    · have : (n : ℝ) ≤ y := (Nat.cast_le.2 (mem_Icc.1 hn).2).trans (Nat.floor_le (by linarith))
      exact mul_nonneg (ha n) (pow_nonneg (by linarith) _)

lemma W_rel (a : ℕ → ℝ) (j : ℕ) {h : ℝ} (hh : 0 ≤ h) (x : ℝ) :
    W a (j + 1) (x + h) - W a (j + 1) x = ((j : ℝ) + 1) * ∫ s in (0 : ℝ)..h, W a j (x + s) := by
  set M := ⌊|x| + h⌋₊ with hM
  have hlt : ∀ u, u ≤ x + h → u < M + 1 := by
    intro u hu
    have := Nat.lt_floor_add_one (|x| + h)
    linarith [le_abs_self x]
  rw [W_eq_psi_sum a (j + 1) (hlt _ le_rfl), W_eq_psi_sum a (j + 1) (hlt _ (by linarith)),
    ← sum_sub_distrib]
  have e : ∫ s in (0 : ℝ)..h, W a j (x + s) = ∫ s in (0 : ℝ)..h, ∑ n ∈ Icc 1 M, a n * psi j (x + s - n) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hh] at hs
    exact W_eq_psi_sum a j (hlt _ (by linarith [hs.2]))
  rw [e, intervalIntegral.integral_finset_sum (fun n _ => ?_), mul_sum]
  · refine sum_congr rfl fun n _ => ?_
    rw [← mul_sub, psi_ftc j (by linarith : x - n ≤ x + h - n), intervalIntegral.integral_const_mul]
    have := intervalIntegral.integral_comp_add_left (psi j) (x - n) (a := 0) (b := h)
    simp only [add_zero] at this
    rw [show x - n + h = x + h - n by ring] at this
    rw [← this]
    have e2 : (fun s => psi j (x - n + s)) = fun s => psi j (x + s - n) := by
      funext s; ring_nf
    rw [e2]; ring
  · have := (psi_intervalIntegrable j (x - n) (x - n + h)).comp_add_left (x - n)
    simp only [sub_self, add_sub_cancel_left] at this
    refine (this.const_mul (a n)).congr fun s _ => ?_
    ring_nf

/-- The main terms `M_j(x) = c x^{j+1}/(j+1)`. -/
noncomputable def Mf (c : ℝ) (j : ℕ) (x : ℝ) : ℝ := c * x ^ (j + 1) / ((j : ℝ) + 1)

lemma Mf_rel (c : ℝ) (j : ℕ) (h x : ℝ) :
    Mf c (j + 1) (x + h) - Mf c (j + 1) x = ((j : ℝ) + 1) * ∫ s in (0 : ℝ)..h, Mf c j (x + s) := by
  unfold Mf
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_add_left (fun u => u ^ (j + 1)), integral_pow]
  push_cast
  field_simp
  ring

/-! ### The descent -/

/-- **`k`-th order differencing**: saving `θ` at order `k` gives saving `θ/(k+1)` at order `0`. -/
theorem riesz_kdiff (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {c : ℝ} (hc : 0 ≤ c) (k : ℕ) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (H : RieszAsymp a c k θ) : RieszAsymp a c 0 (θ / (k + 1)) := by
  obtain ⟨C, hC⟩ := H
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set e : ℝ := 1 - θ / (k + 1) with he
  have hθk : θ / (k + 1) ≤ θ := div_le_self hθ0.le (by have := (Nat.cast_nonneg k : (0:ℝ) ≤ k); linarith)
  have he1 : e ≤ 1 := by have : 0 < θ / (k + 1) := by positivity
                         linarith
  set K : ℝ := c + 2 ^ (2 * k + 1) * |C| * ((k : ℝ) + 1) ^ k / (Nat.factorial k : ℝ) with hK
  have hK0 : 0 ≤ 2 ^ (2 * k + 1) * |C| * ((k : ℝ) + 1) ^ k / (Nat.factorial k : ℝ) := by positivity
  refine ⟨K, fun x hx => ?_⟩
  have hexp : ((0 : ℕ) : ℝ) + 1 - θ / ((k : ℝ) + 1) = e := by rw [he]; push_cast; ring
  rw [hexp]
  simp only [zero_add, pow_one, Nat.cast_zero, div_one]
  rcases lt_or_ge x 1 with hx1 | hx1
  · -- small `x`: `W_0 = 0`
    rw [W_eq_zero_of_lt_one a 0 hx1, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
    have : x ≤ x ^ e := by
      calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
        _ ≤ x ^ e := Real.rpow_le_rpow_of_exponent_ge hx hx1.le he1
    calc c * x ≤ c * x ^ e := mul_le_mul_of_nonneg_left this hc
      _ ≤ K * x ^ e := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · -- large `x`
    set h : ℝ := x ^ e / ((k : ℝ) + 1) with hh
    have hxe : x ^ e ≤ x := by
      calc x ^ e ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 he1
        _ = x := Real.rpow_one x
    have hxe0 : 0 < x ^ e := Real.rpow_pos_of_pos hx _
    have hh0 : 0 < h := by positivity
    have hkh : (k : ℝ) * h < x := by
      have : (k : ℝ) * h = (k : ℝ) / ((k : ℝ) + 1) * x ^ e := by rw [hh]; ring
      rw [this]
      have : (k : ℝ) / ((k : ℝ) + 1) < 1 := by rw [div_lt_one hk1]; linarith
      nlinarith
    -- the two families and their brackets
    have hW := bracket (W a) (fun j u v => (W_mono a ha j).intervalIntegrable) (W_mono a ha 0)
      hh0.le (fun j y => W_rel a j hh0.le y) k
    have hM := bracket (Mf c) (fun j u v => by unfold Mf; exact (by fun_prop : Continuous
      fun x : ℝ => c * x ^ (j + 1) / ((j : ℝ) + 1)).intervalIntegrable u v)
      (fun u v huv => by simp only [Mf, zero_add, pow_one, Nat.cast_zero, div_one]
                         exact mul_le_mul_of_nonneg_left huv hc)
      hh0.le (fun j y => Mf_rel c j h y) k
    -- error bound on `[0, 2x]`
    set B : ℝ := |C| * (2 * x) ^ ((k : ℝ) + 1 - θ) with hB
    have hEb : ∀ y ∈ Icc (x - k * h) (x + k * h), |W a k y - Mf c k y| ≤ B := by
      intro y hy
      have hy0 : 0 < y := by linarith [hy.1]
      have := hC y hy0
      have e1 : Mf c k y = c * y ^ (k + 1) / (k + 1) := rfl
      rw [e1]
      refine this.trans ?_
      calc C * y ^ ((k : ℝ) + 1 - θ) ≤ |C| * y ^ ((k : ℝ) + 1 - θ) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ B := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy0.le (by linarith [hy.2]) ?_)
            (abs_nonneg _)
          have := (Nat.cast_nonneg k : (0:ℝ) ≤ k); linarith
    have hErr : ∀ x₀ ∈ ({x, x - k * h} : Set ℝ),
        |Dk h k (W a k) x₀ - Dk h k (Mf c k) x₀| ≤ 2 ^ k * B := by
      intro x₀ hx₀
      rw [← Dk_sub]
      refine abs_Dk_le h hh0.le k _ x₀ B fun y hy => hEb y ⟨?_, ?_⟩
      · rcases hx₀ with rfl | rfl
        · have := hy.1; nlinarith [hh0.le, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
        · exact hy.1
      · rcases hx₀ with rfl | rfl
        · exact hy.2
        · have := hy.2; nlinarith [hh0.le, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have hE1 := hErr x (by simp)
    have hE2 := hErr (x - k * h) (by simp)
    obtain ⟨hWl, -⟩ := hW x
    obtain ⟨-, hWu⟩ := hW (x - k * h)
    obtain ⟨-, hMu⟩ := hM x
    obtain ⟨hMl, -⟩ := hM (x - k * h)
    simp only [Mf, zero_add, pow_one, Nat.cast_zero, div_one] at hMu hMl
    rw [sub_add_cancel] at hWu
    rw [abs_le] at hE1 hE2
    set P : ℝ := (Nat.factorial k : ℝ) * h ^ k with hP
    have hP0 : 0 < P := by positivity
    -- `P W₀(x) ≤ P c (x + kh) + 2^k B` and `P W₀(x) ≥ P c (x − kh) − 2^k B`
    have up : P * W a 0 x ≤ P * (c * (x + k * h)) + 2 ^ k * B := by
      have := hE1.2; nlinarith
    have lo : P * (c * (x - k * h)) - 2 ^ k * B ≤ P * W a 0 x := by
      have := hE2.1; nlinarith
    -- `2^k B / P ≤ (K − c) x^e`
    have hBP : 2 ^ k * B / P ≤ (2 ^ (2 * k + 1) * |C| * ((k : ℝ) + 1) ^ k /
        (Nat.factorial k : ℝ)) * x ^ e := by
      have h2x : (2 * x) ^ ((k : ℝ) + 1 - θ) ≤ 2 ^ (k + 1) * x ^ ((k : ℝ) + 1 - θ) := by
        rw [Real.mul_rpow (by norm_num) hx.le]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc (2 : ℝ) ^ ((k : ℝ) + 1 - θ) ≤ 2 ^ ((k : ℝ) + 1) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 ^ (k + 1) := by rw [← Real.rpow_natCast]; push_cast; ring_nf
      have hxk : x ^ ((k : ℝ) + 1 - θ) = x ^ e * (x ^ e) ^ k := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_add hx]
        congr 1; rw [he]; field_simp; ring
      have hhk : h ^ k = (x ^ e) ^ k / ((k : ℝ) + 1) ^ k := by rw [hh, div_pow]
      rw [div_le_iff₀ hP0, hP, hhk, hB]
      have hxek : 0 < (x ^ e) ^ k := by positivity
      have hfac : (0 : ℝ) < (Nat.factorial k : ℝ) := by positivity
      have hkk : (0 : ℝ) < ((k : ℝ) + 1) ^ k := by positivity
      calc 2 ^ k * (|C| * (2 * x) ^ ((k : ℝ) + 1 - θ))
          ≤ 2 ^ k * (|C| * (2 ^ (k + 1) * (x ^ e * (x ^ e) ^ k))) := by
            rw [← hxk]; gcongr
        _ = 2 ^ (2 * k + 1) * |C| * ((k : ℝ) + 1) ^ k / (Nat.factorial k : ℝ) * x ^ e *
            ((Nat.factorial k : ℝ) * ((x ^ e) ^ k / ((k : ℝ) + 1) ^ k)) := by
            field_simp; ring
    have hck : c * (k * h) ≤ c * x ^ e := by
      refine mul_le_mul_of_nonneg_left ?_ hc
      rw [hh]
      have : (k : ℝ) / ((k : ℝ) + 1) ≤ 1 := by rw [div_le_one hk1]; linarith
      calc (k : ℝ) * (x ^ e / ((k : ℝ) + 1)) = (k : ℝ) / ((k : ℝ) + 1) * x ^ e := by ring
        _ ≤ 1 * x ^ e := by gcongr
        _ = x ^ e := one_mul _
    have up' : W a 0 x ≤ c * (x + k * h) + 2 ^ k * B / P := by
      have := (le_div_iff₀ hP0).2 (by linarith [up] :
        W a 0 x * P ≤ P * (c * (x + k * h)) + 2 ^ k * B)
      rwa [add_div, mul_div_cancel_left₀ _ hP0.ne'] at this
    have lo' : c * (x - k * h) - 2 ^ k * B / P ≤ W a 0 x := by
      have := (div_le_iff₀ hP0).2 (by linarith [lo] :
        P * (c * (x - k * h)) - 2 ^ k * B ≤ W a 0 x * P)
      rwa [sub_div, mul_div_cancel_left₀ _ hP0.ne'] at this
    have e3 : c * (x + k * h) = c * x + c * (k * h) := by ring
    have e4 : c * (x - k * h) = c * x - c * (k * h) := by ring
    have e5 : K * x ^ e = c * x ^ e + (2 ^ (2 * k + 1) * |C| * ((k : ℝ) + 1) ^ k /
        (Nat.factorial k : ℝ)) * x ^ e := by rw [hK]; ring
    rw [abs_le, e5]
    constructor <;> linarith [hBP, hck, up', lo', e3, e4]

end RamanujanTau.RankinError

#print axioms RamanujanTau.RankinError.bracket
#print axioms RamanujanTau.RankinError.riesz_kdiff
