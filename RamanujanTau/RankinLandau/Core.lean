/-
# Landau's differencing method: the abstract real-variable core

Let `bₙ ≥ 0` and suppose the Riesz mean of order `k` has an exact *dual* expansion

    W_k(x) = ∑_{n ≤ x} bₙ (x − n)^k = c x^{k+1}/(k+1) + d x^k + ∑ₙ bₙ n^{−1−k} J_k(n x)   (x ≥ 1)

with kernels `J_1, …, J_k` linked by `J_{j+1}(u+v) − J_{j+1}(u) = (j+1) ∫₀^v J_j(u+w) dw`
(so `J_j = J_k^{(k−j)}/(k!/j!)`), and with the two kernel bounds

    |J_k(y)| ≤ A y^{k+σ},     |J_1(y)| ≤ A y^{1+α}      (y ≥ 1).

Then `∑_{n≤X} bₙ = c X + O(X^θ)` whenever (`ε > 0` with `∑ bₙ n^{−1−ε} < ∞`, `σ + ε ≤ 0`, `μ ≥ 0`)

    1 + α + μ(α+ε) ≤ 2θ,       k + σ + μ(σ+ε) ≤ (k+1)θ.

Proof (Landau 1915). With `Δ_h^k` the `k`-th forward difference, the bracket
`k! h^k B(x) ≤ Δ_h^k W_k(x) ≤ k! h^k B(x+kh)` (`RankinError.bracket`) reduces everything to
`Δ_h^k` of the dual sum. Termwise, for `n ≤ M` use `k − 1` integrations to reach `J_1`
(`Dk_family_bound`): `|Δ_h^k J_k(n·)| ≤ 2 k! h^{k−1} n^{k−1} sup|J_1(n·)|`; for `n > M` use
`|Δ_h^k f| ≤ 2^k sup |f|`. Rankin's trick `n^{α−1} ≤ M^{α+ε} n^{−1−ε}` (`n ≤ M`),
`n^{σ−1} ≤ M^{σ+ε} n^{−1−ε}` (`n > M`) avoids partial summation. Take `h ≍ X^θ`, `M = X^μ`.
-/
import RamanujanTau.RankinError.RieszK

set_option autoImplicit false

namespace RamanujanTau.RankinLandau

open Real MeasureTheory Set Filter Topology Finset
open RamanujanTau.RankinError

/-! ### Local versions of the difference-operator lemmas -/

lemma Dk_succ (h : ℝ) (k : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    Dk h (k + 1) f x = Dk h k (fun y => f (y + h) - f y) x := rfl

lemma Dk_congr_on (h : ℝ) (hh : 0 ≤ h) (k : ℕ) : ∀ (f g : ℝ → ℝ) (x : ℝ),
    (∀ y ∈ Icc x (x + k * h), f y = g y) → Dk h k f x = Dk h k g x := by
  induction k with
  | zero => intro f g x hfg; simpa [Dk] using hfg x ⟨le_rfl, by simp⟩
  | succ k ih =>
    intro f g x hfg
    simp only [Dk]
    apply ih
    intro y hy
    have h1 := hfg (y + h) ⟨by linarith [hy.1], by push_cast at hy ⊢; linarith [hy.2]⟩
    have h2 := hfg y ⟨hy.1, by push_cast at hy ⊢; nlinarith [hy.2]⟩
    rw [h1, h2]

lemma Dk_add (h : ℝ) (k : ℕ) : ∀ (f g : ℝ → ℝ) (x : ℝ),
    Dk h k (fun y => f y + g y) x = Dk h k f x + Dk h k g x := by
  induction k with
  | zero => intro f g x; rfl
  | succ k ih =>
    intro f g x
    simp only [Dk]
    rw [← ih]
    congr 1; funext y; ring

lemma Dk_tsum_on (h : ℝ) (hh : 0 ≤ h) (k : ℕ) : ∀ (f : ℕ → ℝ → ℝ) (x : ℝ),
    (∀ y ∈ Icc x (x + k * h), Summable fun n => f n y) →
    Dk h k (fun y => ∑' n, f n y) x = ∑' n, Dk h k (f n) x := by
  induction k with
  | zero => intro f x _; rfl
  | succ k ih =>
    intro f x hs
    simp only [Dk]
    have hc : ∀ y ∈ Icc x (x + k * h),
        (∑' n, f n (y + h)) - ∑' n, f n y = ∑' n, (f n (y + h) - f n y) := by
      intro y hy
      have h1 := hs (y + h) ⟨by linarith [hy.1], by push_cast at hy ⊢; linarith [hy.2]⟩
      have h2 := hs y ⟨hy.1, by push_cast at hy ⊢; nlinarith [hy.2]⟩
      exact (h1.tsum_sub h2).symm
    rw [Dk_congr_on h hh k _ _ x hc]
    refine ih (fun n y => f n (y + h) - f n y) x (fun y hy => ?_)
    have h1 := hs (y + h) ⟨by linarith [hy.1], by push_cast at hy ⊢; linarith [hy.2]⟩
    have h2 := hs y ⟨hy.1, by push_cast at hy ⊢; nlinarith [hy.2]⟩
    exact h1.sub h2

lemma intervalIntegrable_shift_of_continuousOn {g : ℝ → ℝ} (hg : ContinuousOn g (Ioi 0))
    {h : ℝ} (hh : 0 ≤ h) {y : ℝ} (hy : 0 < y) :
    IntervalIntegrable (fun s => g (y + s)) volume 0 h := by
  apply ContinuousOn.intervalIntegrable
  refine hg.comp (continuous_const.add continuous_id).continuousOn (fun s hs => ?_)
  rw [uIcc_of_le hh] at hs
  simp only [Set.mem_Ioi]; linarith [hs.1]

/-- `Δ^k` commutes with `∫₀^h · (·+s) ds`, for `g` continuous on `(0, ∞)`. -/
lemma Dk_integral_on (h : ℝ) (hh : 0 ≤ h) (k : ℕ) : ∀ (g : ℝ → ℝ), ContinuousOn g (Ioi 0) →
    ∀ x : ℝ, 0 < x →
    Dk h k (fun y => ∫ s in (0 : ℝ)..h, g (y + s)) x = ∫ s in (0 : ℝ)..h, Dk h k g (x + s) := by
  induction k with
  | zero => intro g _ x _; rfl
  | succ k ih =>
    intro g hg x hx
    simp only [Dk]
    have hc : ∀ y ∈ Icc x (x + k * h),
        (∫ s in (0 : ℝ)..h, g (y + h + s)) - (∫ s in (0 : ℝ)..h, g (y + s)) =
          ∫ s in (0 : ℝ)..h, (fun z => g (z + h) - g z) (y + s) := by
      intro y hy
      have hy0 : 0 < y := by linarith [hy.1]
      rw [← intervalIntegral.integral_sub
        (intervalIntegrable_shift_of_continuousOn hg hh (by linarith : 0 < y + h))
        (intervalIntegrable_shift_of_continuousOn hg hh hy0)]
      congr 1; funext s; simp only; ring_nf
    rw [Dk_congr_on h hh k _ _ x hc]
    have hg' : ContinuousOn (fun z => g (z + h) - g z) (Ioi 0) := by
      refine (hg.comp (continuous_add_right h).continuousOn (fun z hz => ?_)).sub hg
      simp only [Set.mem_Ioi] at hz ⊢; linarith
    exact ih (fun z => g (z + h) - g z) hg' x hx

/-- **`k − 1` integrations.** For a family with
`G_{j+1}(y+h) − G_{j+1}(y) = (j+1) ∫₀^h G_j(y+s) ds` (`1 ≤ j < K`), and `|G_1| ≤ B` on
`[x, x+(j+1)h]`: `|Δ_h^{j+1} G_{j+1}(x)| ≤ (j+1)! h^j · 2B`. -/
lemma Dk_family_bound (G : ℕ → ℝ → ℝ) (K : ℕ) {h : ℝ} (hh : 0 ≤ h)
    (hcont : ∀ j, ContinuousOn (G j) (Ioi 0))
    (hrel : ∀ j, 1 ≤ j → j < K → ∀ y, 0 < y →
      G (j + 1) (y + h) - G (j + 1) y = ((j : ℝ) + 1) * ∫ s in (0 : ℝ)..h, G j (y + s))
    {B : ℝ} :
    ∀ j, j + 1 ≤ K → ∀ x, 0 < x → (∀ y ∈ Icc x (x + ((j + 1 : ℕ) : ℝ) * h), |G 1 y| ≤ B) →
      |Dk h (j + 1) (G (j + 1)) x| ≤ (Nat.factorial (j + 1) : ℝ) * h ^ j * (2 * B) := by
  intro j
  induction j with
  | zero =>
    intro _ x hx hB
    simp only [Dk, zero_add, Nat.factorial_one, Nat.cast_one, pow_zero, one_mul]
    have h1 := hB (x + h) ⟨by linarith, by simp⟩
    have h2 := hB x ⟨le_rfl, by simp; linarith⟩
    calc |G 1 (x + h) - G 1 x| ≤ |G 1 (x + h)| + |G 1 x| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  | succ j ih =>
    intro hjK x hx hB
    rw [Dk_succ]
    have hc : ∀ y ∈ Icc x (x + ((j + 1 : ℕ) : ℝ) * h),
        G (j + 1 + 1) (y + h) - G (j + 1 + 1) y =
          (((j + 1 : ℕ) : ℝ) + 1) * ∫ s in (0 : ℝ)..h, G (j + 1) (y + s) := by
      intro y hy
      exact hrel (j + 1) (by omega) (by omega) y (by linarith [hy.1])
    rw [Dk_congr_on h hh (j + 1) _ _ x hc, Dk_const_mul,
      Dk_integral_on h hh (j + 1) _ (hcont _) x hx]
    set C : ℝ := (Nat.factorial (j + 1) : ℝ) * h ^ j * (2 * B) with hC
    have hI : ‖∫ s in (0 : ℝ)..h, Dk h (j + 1) (G (j + 1)) (x + s)‖ ≤ C * |h - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => ?_)
      rw [uIoc_of_le hh] at hs
      rw [Real.norm_eq_abs]
      refine ih (by omega) (x + s) (by linarith [hs.1]) (fun y hy => hB y ⟨?_, ?_⟩)
      · linarith [hy.1, hs.1]
      · have := hy.2; push_cast at this ⊢; nlinarith [hs.2]
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hh] at hI
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc (((j + 1 : ℕ) : ℝ) + 1) * |∫ s in (0 : ℝ)..h, Dk h (j + 1) (G (j + 1)) (x + s)|
        ≤ (((j + 1 : ℕ) : ℝ) + 1) * (C * h) := by gcongr
      _ = (Nat.factorial (j + 1 + 1) : ℝ) * h ^ (j + 1) * (2 * B) := by
          rw [hC, Nat.factorial_succ (j + 1)]; push_cast; ring

/-- `Δ_h^k y^k = k! h^k`. -/
lemma Dk_pow (h : ℝ) (hh : 0 ≤ h) (k : ℕ) (x : ℝ) :
    Dk h k (fun y => y ^ k) x = (Nat.factorial k : ℝ) * h ^ k := by
  have hrel : ∀ (j : ℕ) (x : ℝ), (fun j (y : ℝ) => y ^ j) (j + 1) (x + h) -
      (fun j (y : ℝ) => y ^ j) (j + 1) x =
      ((j : ℝ) + 1) * ∫ s in (0 : ℝ)..h, (fun j (y : ℝ) => y ^ j) j (x + s) := by
    intro j x
    simp only
    rw [intervalIntegral.integral_comp_add_left (fun y => y ^ j), integral_pow]
    have : (j : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring_nf
  have hb := bracket (fun j (y : ℝ) => y ^ j)
    (fun j u v => (continuous_pow j).intervalIntegrable u v)
    (fun u v _ => by simp) hh hrel k x
  simp only [pow_zero, mul_one] at hb
  exact le_antisymm hb.2 hb.1

/-! ### The hypotheses of Landau's method -/

/-- **Landau data**: nonnegative coefficients, an exact dual expansion of the Riesz mean of
order `k`, and the two kernel bounds. -/
structure LandauHyp (b : ℕ → ℝ) (k : ℕ) (J : ℕ → ℝ → ℝ) (c d A σ α ε : ℝ) : Prop where
  nonneg : ∀ n, 0 ≤ b n
  zero : b 0 = 0
  hk : 1 ≤ k
  hc : 0 ≤ c
  hA : 0 ≤ A
  hε : 0 < ε
  hα : 0 ≤ α
  hσ : σ + ε ≤ 0
  hkσ : 0 ≤ (k : ℝ) + σ
  summ : Summable fun n : ℕ => b n * (n : ℝ) ^ (-1 - ε)
  cont : ∀ j, ContinuousOn (J j) (Ioi 0)
  rel : ∀ j, 1 ≤ j → j < k → ∀ u, 0 < u → ∀ v, 0 ≤ v →
    J (j + 1) (u + v) - J (j + 1) u = ((j : ℝ) + 1) * ∫ w in (0 : ℝ)..v, J j (u + w)
  top : ∀ y, 1 ≤ y → |J k y| ≤ A * y ^ ((k : ℝ) + σ)
  one : ∀ y, 1 ≤ y → |J 1 y| ≤ A * y ^ (1 + α)
  rep : ∀ x, 1 ≤ x → W b k x = c * x ^ (k + 1) / ((k : ℝ) + 1) + d * x ^ k +
    ∑' n : ℕ, b n / (n : ℝ) ^ (k + 1) * J k (n * x)

section Core

variable {b : ℕ → ℝ} {k : ℕ} {J : ℕ → ℝ → ℝ} {c d A σ α ε : ℝ}

lemma rpow_div_self_eq {n : ℝ} (hn : 0 < n) (β ε : ℝ) :
    n ^ β / n = n ^ (-1 - ε) * n ^ (β + ε) := by
  rw [← Real.rpow_add hn, show -1 - ε + (β + ε) = β - 1 by ring, Real.rpow_sub_one hn.ne']

/-- The termwise estimate. -/
lemma term_bound (H : LandauHyp b k J c d A σ α ε) {x h M Y : ℝ} (hx : 1 ≤ x) (hh : 0 ≤ h)
    (hM : 0 < M) (hY : x + k * h ≤ Y) (n : ℕ) :
    |b n / (n : ℝ) ^ (k + 1) * Dk h k (fun y => J k (n * y)) x| ≤
      (2 * A * (Nat.factorial k : ℝ) * h ^ (k - 1) * Y ^ (1 + α) * M ^ (α + ε) +
        2 ^ k * A * Y ^ ((k : ℝ) + σ) * M ^ (σ + ε)) * (b n * (n : ℝ) ^ (-1 - ε)) := by
  have hA := H.hA
  have hbn := H.nonneg n
  have hY1 : 1 ≤ Y := by nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hY0 : 0 < Y := by linarith
  set P1 : ℝ := 2 * A * (Nat.factorial k : ℝ) * h ^ (k - 1) * Y ^ (1 + α) * M ^ (α + ε)
    with hP1
  set P2 : ℝ := 2 ^ k * A * Y ^ ((k : ℝ) + σ) * M ^ (σ + ε) with hP2
  have hP1n : 0 ≤ P1 := by positivity
  have hP2n : 0 ≤ P2 := by positivity
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [H.zero]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hS0 : 0 ≤ b n * (n : ℝ) ^ (-1 - ε) := by positivity
  have hpre : 0 ≤ b n / (n : ℝ) ^ (k + 1) := by positivity
  rw [abs_mul, abs_of_nonneg hpre]
  rcases le_or_gt (n : ℝ) M with hnM | hnM
  · -- small `n`: `k − 1` integrations down to `J₁`
    obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := H.hk; omega⟩
    set G : ℕ → ℝ → ℝ := fun j y => J j (n * y) / (n : ℝ) ^ j with hG
    have hGc : ∀ j, ContinuousOn (G j) (Ioi 0) := by
      intro j
      refine ((H.cont j).comp (continuous_const.mul continuous_id).continuousOn
        (fun y hy => ?_)).div_const _
      simp only [Set.mem_Ioi] at hy ⊢; exact mul_pos hn0 hy
    have hGr : ∀ j, 1 ≤ j → j < k → ∀ y, 0 < y →
        G (j + 1) (y + h) - G (j + 1) y = ((j : ℝ) + 1) * ∫ s in (0 : ℝ)..h, G j (y + s) := by
      intro j hj1 hjk y hy
      have hr := H.rel j hj1 hjk (n * y) (by positivity) (n * h) (by positivity)
      simp only [hG]
      have e1 : ∫ s in (0 : ℝ)..h, J j (n * (y + s)) / (n : ℝ) ^ j =
          ((n : ℝ) ^ j)⁻¹ * ((n : ℝ)⁻¹ * ∫ w in (0 : ℝ)..n * h, J j (n * y + w)) := by
        rw [intervalIntegral.integral_div]
        have := intervalIntegral.integral_comp_mul_left (fun w => J j (n * y + w))
          (a := 0) (b := h) hn0.ne'
        simp only [mul_zero, smul_eq_mul] at this
        rw [show (fun s => J j (n * (y + s))) = fun s => J j (n * y + n * s) by
          funext s; ring_nf, this]
        ring
      rw [e1, ← sub_div, mul_add, hr, pow_succ]
      field_simp
    have hDk : Dk h k (fun y => J k (n * y)) x = (n : ℝ) ^ k * Dk h k (G k) x := by
      rw [← Dk_const_mul]
      congr 1; funext y; simp only [hG]; field_simp
    have hGB : ∀ y ∈ Icc x (x + ((k' + 1 : ℕ) : ℝ) * h),
        |G 1 y| ≤ A * (n : ℝ) ^ α * Y ^ (1 + α) := by
      intro y hy
      have hy1 : 1 ≤ y := le_trans hx hy.1
      have hyY : y ≤ Y := by rw [← hk'] at hy; linarith [hy.2]
      simp only [hG, pow_one]
      rw [abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
      have hny : 1 ≤ (n : ℝ) * y := by nlinarith
      calc |J 1 (n * y)| ≤ A * ((n : ℝ) * y) ^ (1 + α) := H.one _ hny
        _ = A * ((n : ℝ) ^ α * n) * y ^ (1 + α) := by
            rw [Real.mul_rpow hn0.le (by linarith), Real.rpow_add hn0, Real.rpow_one]; ring
        _ ≤ A * ((n : ℝ) ^ α * n) * Y ^ (1 + α) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hyY (by linarith [H.hα]))
              (by positivity)
        _ = A * (n : ℝ) ^ α * Y ^ (1 + α) * n := by ring
    have hfb := Dk_family_bound G k hh hGc (fun j hj1 hjk y hy => hGr j hj1 hjk y hy)
      (B := A * (n : ℝ) ^ α * Y ^ (1 + α)) k' (by omega) x (by linarith) hGB
    rw [← hk'] at hfb
    have hk1 : k - 1 = k' := by omega
    rw [hDk, abs_mul, abs_of_pos (by positivity)]
    have hnM' : (n : ℝ) ^ (α + ε) ≤ M ^ (α + ε) :=
      Real.rpow_le_rpow hn0.le hnM (by linarith [H.hα, H.hε])
    calc b n / (n : ℝ) ^ (k + 1) * ((n : ℝ) ^ k * |Dk h k (G k) x|)
        ≤ b n / (n : ℝ) ^ (k + 1) * ((n : ℝ) ^ k *
          ((Nat.factorial k : ℝ) * h ^ k' * (2 * (A * (n : ℝ) ^ α * Y ^ (1 + α))))) := by
          gcongr
      _ = 2 * A * (Nat.factorial k : ℝ) * h ^ (k - 1) * Y ^ (1 + α) *
          (b n * ((n : ℝ) ^ α / n)) := by
          rw [hk1, pow_succ]; field_simp
      _ = 2 * A * (Nat.factorial k : ℝ) * h ^ (k - 1) * Y ^ (1 + α) *
          (b n * (n : ℝ) ^ (-1 - ε) * (n : ℝ) ^ (α + ε)) := by
          rw [rpow_div_self_eq hn0 α ε]; ring
      _ ≤ 2 * A * (Nat.factorial k : ℝ) * h ^ (k - 1) * Y ^ (1 + α) *
          (b n * (n : ℝ) ^ (-1 - ε) * M ^ (α + ε)) := by gcongr
      _ = P1 * (b n * (n : ℝ) ^ (-1 - ε)) := by rw [hP1]; ring
      _ ≤ (P1 + P2) * (b n * (n : ℝ) ^ (-1 - ε)) := by gcongr; linarith
  · -- large `n`: `|Δ^k f| ≤ 2^k sup |f|`
    have hsup : ∀ y ∈ Icc x (x + k * h), |J k (n * y)| ≤ A * ((n : ℝ) * Y) ^ ((k : ℝ) + σ) := by
      intro y hy
      have hy1 : 1 ≤ y := le_trans hx hy.1
      have hny : 1 ≤ (n : ℝ) * y := by nlinarith
      refine (H.top _ hny).trans ?_
      gcongr
      · exact H.hkσ
      · nlinarith [hy.2]
    have hd := abs_Dk_le h hh k _ x _ hsup
    have hnM' : (n : ℝ) ^ (σ + ε) ≤ M ^ (σ + ε) :=
      Real.rpow_le_rpow_of_nonpos hM hnM.le H.hσ
    calc b n / (n : ℝ) ^ (k + 1) * |Dk h k (fun y => J k (n * y)) x|
        ≤ b n / (n : ℝ) ^ (k + 1) * (2 ^ k * (A * ((n : ℝ) * Y) ^ ((k : ℝ) + σ))) := by gcongr
      _ = 2 ^ k * A * Y ^ ((k : ℝ) + σ) * (b n * ((n : ℝ) ^ σ / n)) := by
          rw [Real.mul_rpow hn0.le hY0.le, Real.rpow_add hn0, Real.rpow_natCast, pow_succ]
          field_simp
      _ = 2 ^ k * A * Y ^ ((k : ℝ) + σ) * (b n * (n : ℝ) ^ (-1 - ε) * (n : ℝ) ^ (σ + ε)) := by
          rw [rpow_div_self_eq hn0 σ ε]; ring
      _ ≤ 2 ^ k * A * Y ^ ((k : ℝ) + σ) * (b n * (n : ℝ) ^ (-1 - ε) * M ^ (σ + ε)) := by
          gcongr
      _ = P2 * (b n * (n : ℝ) ^ (-1 - ε)) := by rw [hP2]; ring
      _ ≤ (P1 + P2) * (b n * (n : ℝ) ^ (-1 - ε)) := by gcongr; linarith

/-- `Δ_h^k W_k(x) = Δ_h^k M_k(x) + d k! h^k + E` with `|E| ≤ Λ S`. -/
lemma Dk_W_bound (H : LandauHyp b k J c d A σ α ε) {x h M Y : ℝ} (hx : 1 ≤ x) (hh : 0 ≤ h)
    (hM : 0 < M) (hY : x + k * h ≤ Y) :
    |Dk h k (W b k) x - (Dk h k (Mf c k) x + d * ((Nat.factorial k : ℝ) * h ^ k))| ≤
      (2 * A * (Nat.factorial k : ℝ) * h ^ (k - 1) * Y ^ (1 + α) * M ^ (α + ε) +
        2 ^ k * A * Y ^ ((k : ℝ) + σ) * M ^ (σ + ε)) *
        ∑' n : ℕ, b n * (n : ℝ) ^ (-1 - ε) := by
  set f : ℕ → ℝ → ℝ := fun n y => b n / (n : ℝ) ^ (k + 1) * J k (n * y) with hf
  -- summability of the dual series at every `y ≥ 1`
  have hsum : ∀ y, 1 ≤ y → Summable fun n => f n y := by
    intro y hy
    refine Summable.of_norm_bounded (H.summ.mul_left (A * y ^ ((k : ℝ) + σ))) (fun n => ?_)
    rw [Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hf, H.zero]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hny : 1 ≤ (n : ℝ) * y := by nlinarith
    simp only [hf]
    rw [abs_mul, abs_of_nonneg (by have := H.nonneg n; positivity)]
    have hσn : (n : ℝ) ^ (σ + ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 H.hσ
    have hbn := H.nonneg n
    calc b n / (n : ℝ) ^ (k + 1) * |J k (n * y)|
        ≤ b n / (n : ℝ) ^ (k + 1) * (A * ((n : ℝ) * y) ^ ((k : ℝ) + σ)) := by
          gcongr; exact H.top _ hny
      _ = A * y ^ ((k : ℝ) + σ) * (b n * ((n : ℝ) ^ σ / n)) := by
          rw [Real.mul_rpow hn0.le (by linarith), Real.rpow_add hn0, Real.rpow_natCast,
            pow_succ]
          field_simp
      _ = A * y ^ ((k : ℝ) + σ) * (b n * (n : ℝ) ^ (-1 - ε) * (n : ℝ) ^ (σ + ε)) := by
          rw [rpow_div_self_eq hn0 σ ε]; ring
      _ ≤ A * y ^ ((k : ℝ) + σ) * (b n * (n : ℝ) ^ (-1 - ε) * 1) := by
          have := H.hA
          gcongr
      _ = A * y ^ ((k : ℝ) + σ) * (b n * (n : ℝ) ^ (-1 - ε)) := by ring
  have hrep : ∀ y ∈ Icc x (x + k * h), W b k y =
      (fun y => (fun y => Mf c k y + d * y ^ k) y + ∑' n, f n y) y := by
    intro y hy
    rw [H.rep y (le_trans hx hy.1)]
    simp only [Mf, hf]
  rw [Dk_congr_on h hh k _ _ x hrep, Dk_add, Dk_add, Dk_const_mul, Dk_pow h hh k x,
    Dk_tsum_on h hh k f x (fun y hy => hsum y (le_trans hx hy.1))]
  have e : ∀ n, Dk h k (f n) x = b n / (n : ℝ) ^ (k + 1) * Dk h k (fun y => J k (n * y)) x := by
    intro n; simp only [hf]; rw [Dk_const_mul]
  simp only [e, add_sub_cancel_left]
  rw [← Real.norm_eq_abs]
  refine tsum_of_norm_bounded (H.summ.hasSum.mul_left _) (fun n => ?_)
  rw [Real.norm_eq_abs]
  exact term_bound H hx hh hM hY n

set_option maxHeartbeats 1000000 in
/-- **Landau's theorem (abstract form).** -/
theorem landau_core (H : LandauHyp b k J c d A σ α ε) {θ μ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hμ : 0 ≤ μ) (h1 : 1 + α + μ * (α + ε) ≤ 2 * θ)
    (h2 : (k : ℝ) + σ + μ * (σ + ε) ≤ ((k : ℝ) + 1) * θ) :
    ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X → |W b 0 X - c * X| ≤ C * X ^ θ := by
  have hk := H.hk
  have hc := H.hc
  have hA := H.hA
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set S : ℝ := ∑' n : ℕ, b n * (n : ℝ) ^ (-1 - ε) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun n => by have := H.nonneg n; positivity
  set K1 : ℝ := 2 * A * 2 ^ (1 + α) * (4 * k) * S with hK1
  set K2 : ℝ := 2 ^ k * A * 2 ^ ((k : ℝ) + σ) * (4 * k) ^ k / (Nat.factorial k : ℝ) * S
    with hK2
  have hK10 : 0 ≤ K1 := by positivity
  have hK20 : 0 ≤ K2 := by positivity
  set C : ℝ := (W b 0 2 + 2 * c) + |d| + c + K1 + K2 with hCdef
  have hW2 : 0 ≤ W b 0 2 := by
    unfold W; exact Finset.sum_nonneg fun n _ => by have := H.nonneg n; positivity
  refine ⟨C, fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hXθ : 1 ≤ X ^ θ := Real.one_le_rpow hX hθ0.le
  rcases lt_or_ge X 2 with hX2 | hX2
  · -- small `X`
    have hWX : 0 ≤ W b 0 X := by
      unfold W; exact Finset.sum_nonneg fun n _ => by have := H.nonneg n; positivity
    have hWm : W b 0 X ≤ W b 0 2 := W_mono b H.nonneg 0 hX2.le
    have : |W b 0 X - c * X| ≤ W b 0 2 + 2 * c := by
      rw [abs_le]; constructor <;> nlinarith
    calc |W b 0 X - c * X| ≤ W b 0 2 + 2 * c := this
      _ ≤ C := by rw [hCdef]; nlinarith [abs_nonneg d]
      _ ≤ C * X ^ θ := le_mul_of_one_le_right (by rw [hCdef]; positivity) hXθ
  -- large `X`
  set h : ℝ := X ^ θ / (4 * k) with hh
  have hh0 : 0 < h := by positivity
  set M : ℝ := X ^ μ with hM
  have hM0 : 0 < M := by positivity
  have hXθX : X ^ θ ≤ X := by
    calc X ^ θ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX hθ1
      _ = X := Real.rpow_one X
  have hkh : (k : ℝ) * h = X ^ θ / 4 := by rw [hh]; field_simp
  have hx1 : 1 ≤ X - k * h := by rw [hkh]; linarith
  -- the bracket for `W` and for `M_k`
  have hWb := bracket (W b) (fun j u v => (W_mono b H.nonneg j).intervalIntegrable)
    (W_mono b H.nonneg 0) hh0.le (fun j y => W_rel b j hh0.le y) k
  have hMb := bracket (Mf c) (fun j u v => by unfold Mf; exact (by fun_prop : Continuous
      fun x : ℝ => c * x ^ (j + 1) / ((j : ℝ) + 1)).intervalIntegrable u v)
    (fun u v huv => by simp only [Mf, zero_add, pow_one, Nat.cast_zero, div_one]
                       exact mul_le_mul_of_nonneg_left huv hc)
    hh0.le (fun j y => Mf_rel c j h y) k
  set Λ : ℝ := (2 * A * (Nat.factorial k : ℝ) * h ^ (k - 1) * (2 * X) ^ (1 + α) * M ^ (α + ε) +
        2 ^ k * A * (2 * X) ^ ((k : ℝ) + σ) * M ^ (σ + ε)) * S with hΛ
  have hD1 := Dk_W_bound H (x := X) (Y := 2 * X) hX hh0.le hM0 (by rw [hkh]; linarith)
  have hD2 := Dk_W_bound H (x := X - k * h) (Y := 2 * X) hx1 hh0.le hM0 (by linarith)
  rw [← hΛ] at hD1 hD2
  obtain ⟨hWl, -⟩ := hWb X
  obtain ⟨-, hWu⟩ := hWb (X - k * h)
  rw [sub_add_cancel] at hWu
  obtain ⟨-, hMu⟩ := hMb X
  obtain ⟨hMl, -⟩ := hMb (X - k * h)
  simp only [Mf, zero_add, pow_one, Nat.cast_zero, div_one] at hMu hMl
  set P : ℝ := (Nat.factorial k : ℝ) * h ^ k with hP
  have hP0 : 0 < P := by positivity
  rw [abs_le] at hD1 hD2
  -- `|B(X) − cX − d| ≤ 2ckh + Λ/P`
  have hup : W b 0 X - c * X ≤ c * (k * h) + d + Λ / P := by
    have key : P * (W b 0 X - c * X) ≤ P * (c * (k * h) + d) + Λ := by
      have := hD1.2
      linarith
    calc W b 0 X - c * X = (P * (W b 0 X - c * X)) / P := (mul_div_cancel_left₀ _ hP0.ne').symm
      _ ≤ (P * (c * (k * h) + d) + Λ) / P := by gcongr
      _ = c * (k * h) + d + Λ / P := by rw [add_div, mul_div_cancel_left₀ _ hP0.ne']
  have hlow : c * X - W b 0 X ≤ c * (k * h) - d + Λ / P := by
    have key : P * (c * X - W b 0 X) ≤ P * (c * (k * h) - d) + Λ := by
      have := hD2.1
      linarith
    calc c * X - W b 0 X = (P * (c * X - W b 0 X)) / P := (mul_div_cancel_left₀ _ hP0.ne').symm
      _ ≤ (P * (c * (k * h) - d) + Λ) / P := by gcongr
      _ = c * (k * h) - d + Λ / P := by rw [add_div, mul_div_cancel_left₀ _ hP0.ne']
  -- `Λ / P ≤ (K1 + K2) X^θ`
  have hΛP : Λ / P ≤ (K1 + K2) * X ^ θ := by
    have hk1 : (k - 1 : ℕ) + 1 = k := by omega
    have hhk : h ^ k = h ^ (k - 1) * h := by rw [← pow_succ, hk1]
    have e1 : 2 * A * (Nat.factorial k : ℝ) * h ^ (k - 1) * (2 * X) ^ (1 + α) * M ^ (α + ε) *
        S / P = 2 * A * 2 ^ (1 + α) * (4 * k) * S * X ^ (1 + α + μ * (α + ε) - θ) := by
      rw [hP, hhk, Real.mul_rpow (by norm_num) hX0.le, hM, ← Real.rpow_mul hX0.le]
      rw [show 1 + α + μ * (α + ε) - θ = (1 + α) + μ * (α + ε) - θ by ring,
        Real.rpow_sub hX0, Real.rpow_add hX0, hh]
      have : (0 : ℝ) < (Nat.factorial k : ℝ) := by positivity
      have : (0 : ℝ) < X ^ θ := by positivity
      have : (0 : ℝ) < h ^ (k - 1) := by positivity
      field_simp
      simp only [Real.rpow_add hX0, Real.rpow_one]; ring
    have e2 : 2 ^ k * A * (2 * X) ^ ((k : ℝ) + σ) * M ^ (σ + ε) * S / P =
        2 ^ k * A * 2 ^ ((k : ℝ) + σ) * (4 * k) ^ k / (Nat.factorial k : ℝ) * S *
          X ^ ((k : ℝ) + σ + μ * (σ + ε) - k * θ) := by
      rw [hP, Real.mul_rpow (by norm_num) hX0.le, hM, ← Real.rpow_mul hX0.le,
        Real.rpow_sub hX0, Real.rpow_add hX0, hh, div_pow,
        show (X ^ θ) ^ k = X ^ ((k : ℝ) * θ) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le, mul_comm]]
      have : (0 : ℝ) < (Nat.factorial k : ℝ) := by positivity
      have : (0 : ℝ) < X ^ ((k : ℝ) * θ) := by positivity
      field_simp
      simp only [Real.rpow_add hX0, Real.rpow_natCast]; ring
    have hx1' : X ^ (1 + α + μ * (α + ε) - θ) ≤ X ^ θ :=
      Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    have hx2' : X ^ ((k : ℝ) + σ + μ * (σ + ε) - k * θ) ≤ X ^ θ :=
      Real.rpow_le_rpow_of_exponent_le hX (by nlinarith)
    rw [hΛ, add_mul, add_div, e1, e2, add_mul]
    gcongr
  have hckh : c * (k * h) ≤ c * X ^ θ := by
    rw [hkh]; exact mul_le_mul_of_nonneg_left (by linarith) hc
  have hd : |d| ≤ |d| * X ^ θ := le_mul_of_one_le_right (abs_nonneg _) hXθ
  have hW0 : 0 ≤ (W b 0 2 + 2 * c) * X ^ θ := by positivity
  rw [abs_le]
  constructor
  · have : -(W b 0 X - c * X) ≤ C * X ^ θ := by
      rw [neg_sub]
      calc c * X - W b 0 X ≤ c * (k * h) - d + Λ / P := hlow
        _ ≤ c * X ^ θ + |d| * X ^ θ + (K1 + K2) * X ^ θ := by
            linarith [neg_le_abs d]
        _ ≤ C * X ^ θ := by rw [hCdef]; nlinarith
    linarith
  · calc W b 0 X - c * X ≤ c * (k * h) + d + Λ / P := hup
      _ ≤ c * X ^ θ + |d| * X ^ θ + (K1 + K2) * X ^ θ := by linarith [le_abs_self d]
      _ ≤ C * X ^ θ := by rw [hCdef]; nlinarith

end Core

end RamanujanTau.RankinLandau

#print axioms RamanujanTau.RankinLandau.Dk_family_bound
#print axioms RamanujanTau.RankinLandau.Dk_W_bound
#print axioms RamanujanTau.RankinLandau.landau_core
