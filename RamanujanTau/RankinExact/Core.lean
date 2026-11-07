/-
# Landau's differencing method with no `ε`: the sharp abstract core

`RankinLandau.landau_core` proves `B(X) = cX + O(X^θ)` under
`1 + α + μ(α+ε) ≤ 2θ`, `k + σ + μ(σ+ε) ≤ (k+1)θ` with `ε > 0`: the `ε` comes from Rankin's
trick. Here (`landau_sharp`) the same conclusion holds under the **ε-free** constraints

    1 + α + μα ≤ 2θ,          k + σ + μσ ≤ (k+1)θ,

for `0 < α ≤ 1` and `σ ≤ −1`. Rankin's trick is replaced by exact partial summation
(`Summation.lean`), which needs a linear bound `∑_{n≤N} bₙ ≤ LN`. That bound is
bootstrapped from `landau_core` itself at `θ = 1`, `μ = 0`.
-/
import RamanujanTau.RankinExact.Summation
import RamanujanTau.RankinLandau.Core

set_option autoImplicit false

namespace RamanujanTau.RankinExact

open Real MeasureTheory Set Filter Topology Finset
open RamanujanTau.RankinError RamanujanTau.RankinLandau

variable {b : ℕ → ℝ} {k : ℕ} {J : ℕ → ℝ → ℝ} {c d A σ α ε : ℝ}

lemma sum_range_shift_eq_W (b : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ range N, b (i + 1) = W b 0 N := by
  unfold W
  rw [Nat.floor_natCast]
  simp only [pow_zero, mul_one]
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

/-- **The linear bound** `∑_{n≤N} bₙ ≤ LN`, from `landau_core` at `θ = 1`, `μ = 0`. -/
lemma linear_bound (H : LandauHyp b k J c d A σ α ε) (hα1 : α ≤ 1) (hσ1 : σ ≤ 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ N : ℕ, ∑ i ∈ range N, b (i + 1) ≤ L * N := by
  obtain ⟨C, hC⟩ := landau_core H (θ := 1) (μ := 0) one_pos le_rfl le_rfl (by linarith)
    (by linarith)
  refine ⟨c + |C|, by linarith [H.hc, abs_nonneg C], fun N => ?_⟩
  rw [sum_range_shift_eq_W]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [W]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h := hC N hN1
  rw [Real.rpow_one] at h
  have := (abs_le.1 h).2
  have : C * N ≤ |C| * N := mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  linarith

/-- The termwise estimate with the exact weights `wS`, `wL`. -/
lemma term_bound' (H : LandauHyp b k J c d A σ α ε) {x h M Y : ℝ} (hx : 1 ≤ x) (hh : 0 ≤ h)
    (hY : x + k * h ≤ Y) (n : ℕ) :
    |b n / (n : ℝ) ^ (k + 1) * Dk h k (fun y => J k (n * y)) x| ≤
      2 * A * (Nat.factorial k : ℝ) * h ^ (k - 1) * Y ^ (1 + α) * (b n * wS α M n) +
        2 ^ k * A * Y ^ ((k : ℝ) + σ) * (b n * wL σ M n) := by
  have hA := H.hA
  have hbn := H.nonneg n
  have hY1 : 1 ≤ Y := by nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hY0 : 0 < Y := by linarith
  set P1 : ℝ := 2 * A * (Nat.factorial k : ℝ) * h ^ (k - 1) * Y ^ (1 + α) with hP1
  set P2 : ℝ := 2 ^ k * A * Y ^ ((k : ℝ) + σ) with hP2
  have hP1n : 0 ≤ P1 := by positivity
  have hP2n : 0 ≤ P2 := by positivity
  have hS := mul_nonneg hP1n (mul_nonneg hbn (wS_nonneg α M n))
  have hL := mul_nonneg hP2n (mul_nonneg hbn (wL_nonneg σ M n))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [H.zero]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
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
    have hw : wS α M n = (n : ℝ) ^ α / n := by
      rw [wS, if_pos hnM, Real.rpow_sub_one hn0.ne']
    calc b n / (n : ℝ) ^ (k + 1) * ((n : ℝ) ^ k * |Dk h k (G k) x|)
        ≤ b n / (n : ℝ) ^ (k + 1) * ((n : ℝ) ^ k *
          ((Nat.factorial k : ℝ) * h ^ k' * (2 * (A * (n : ℝ) ^ α * Y ^ (1 + α))))) := by
          gcongr
      _ = 2 * A * (Nat.factorial k : ℝ) * h ^ (k - 1) * Y ^ (1 + α) *
          (b n * ((n : ℝ) ^ α / n)) := by
          rw [hk1, pow_succ]; field_simp
      _ = P1 * (b n * wS α M n) := by rw [hw, hP1]
      _ ≤ _ := by linarith
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
    have hw : wL σ M n = (n : ℝ) ^ σ / n := by
      rw [wL, if_neg (not_le.2 hnM), Real.rpow_sub_one hn0.ne']
    calc b n / (n : ℝ) ^ (k + 1) * |Dk h k (fun y => J k (n * y)) x|
        ≤ b n / (n : ℝ) ^ (k + 1) * (2 ^ k * (A * ((n : ℝ) * Y) ^ ((k : ℝ) + σ))) := by gcongr
      _ = 2 ^ k * A * Y ^ ((k : ℝ) + σ) * (b n * ((n : ℝ) ^ σ / n)) := by
          rw [Real.mul_rpow hn0.le hY0.le, Real.rpow_add hn0, Real.rpow_natCast, pow_succ]
          field_simp
      _ = P2 * (b n * wL σ M n) := by rw [hw, hP2]
      _ ≤ _ := by linarith

/-- `Δ_h^k W_k(x) = Δ_h^k M_k(x) + d k! h^k + E`, with `E` bounded by the two exact sums. -/
lemma Dk_W_bound' (H : LandauHyp b k J c d A σ α ε) {x h M Y : ℝ} (hx : 1 ≤ x) (hh : 0 ≤ h)
    (hM : 0 < M) (hY : x + k * h ≤ Y) (hs1 : Summable fun n => b n * wS α M n)
    (hs2 : Summable fun n => b n * wL σ M n) :
    |Dk h k (W b k) x - (Dk h k (Mf c k) x + d * ((Nat.factorial k : ℝ) * h ^ k))| ≤
      2 * A * (Nat.factorial k : ℝ) * h ^ (k - 1) * Y ^ (1 + α) * ∑' n, b n * wS α M n +
        2 ^ k * A * Y ^ ((k : ℝ) + σ) * ∑' n, b n * wL σ M n := by
  set f : ℕ → ℝ → ℝ := fun n y => b n / (n : ℝ) ^ (k + 1) * J k (n * y) with hf
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
  refine tsum_of_norm_bounded
    ((hs1.hasSum.mul_left (2 * A * (Nat.factorial k : ℝ) * h ^ (k - 1) * Y ^ (1 + α))).add
      (hs2.hasSum.mul_left (2 ^ k * A * Y ^ ((k : ℝ) + σ)))) (fun n => ?_)
  rw [Real.norm_eq_abs]
  exact term_bound' H (M := M) hx hh hY n

/-- The exact small-`n` sum: `∑ₙ bₙ wS(n) ≤ L M^α/α`. -/
lemma sumS_le (H : LandauHyp b k J c d A σ α ε) (hα0 : 0 < α) (hα1 : α ≤ 1) {L M : ℝ}
    (hL : ∀ N : ℕ, ∑ i ∈ range N, b (i + 1) ≤ L * N) (hL0 : 0 ≤ L) (hM : 0 ≤ M) (N : ℕ) :
    ∑ n ∈ range N, b n * wS α M n ≤ L * (M ^ α / α) := by
  have h0 : ∀ n, 0 ≤ b n * wS α M n := fun n => mul_nonneg (H.nonneg n) (wS_nonneg α M n)
  calc ∑ n ∈ range N, b n * wS α M n ≤ ∑ n ∈ range (N + 1), b n * wS α M n := by
        rw [sum_range_succ]; linarith [h0 N]
    _ = ∑ i ∈ range N, b (i + 1) * wS α M (i + 1) := by
        rw [sum_range_succ', H.zero]; simp
    _ ≤ L * ∑ i ∈ range N, wS α M (i + 1) :=
        majorize (fun i => wS_nonneg α M (i + 1)) (wS_anti hα1) hL N
    _ ≤ L * (M ^ α / α) := mul_le_mul_of_nonneg_left (sum_wS_le hα0 hα1 hM N) hL0

/-- The exact large-`n` sum: `∑ₙ bₙ wL(n) ≤ L (1 + 1/q) M^σ`. -/
lemma sumL_le (H : LandauHyp b k J c d A σ α ε) (hσ1 : σ ≤ -1) {L M : ℝ}
    (hL : ∀ N : ℕ, ∑ i ∈ range N, b (i + 1) ≤ L * N) (hL0 : 0 ≤ L) (hM : 0 < M) (N : ℕ) :
    ∑ n ∈ range N, b n * wL σ M n ≤ L * ((1 + 1 / -σ) * M ^ σ) := by
  have h0 : ∀ n, 0 ≤ b n * wL σ M n := fun n => mul_nonneg (H.nonneg n) (wL_nonneg σ M n)
  calc ∑ n ∈ range N, b n * wL σ M n ≤ ∑ n ∈ range (N + 1), b n * wL σ M n := by
        rw [sum_range_succ]; linarith [h0 N]
    _ = ∑ i ∈ range N, b (i + 1) * wL σ M (i + 1) := by
        rw [sum_range_succ', H.zero]; simp
    _ ≤ ∑ i ∈ range N, b (i + 1) * vT σ M (i + 1) :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (wL_le_vT hM.le _) (H.nonneg _)
    _ ≤ L * ∑ i ∈ range N, vT σ M (i + 1) :=
        majorize (fun i => vT_nonneg σ M (i + 1)) (vT_anti hσ1) hL N
    _ ≤ L * ((1 + 1 / -σ) * M ^ σ) := mul_le_mul_of_nonneg_left (sum_vT_le hσ1 hM N) hL0

set_option maxHeartbeats 1000000 in
/-- **Landau's theorem, sharp abstract form (no `ε`).** -/
theorem landau_sharp (H : LandauHyp b k J c d A σ α ε) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hσ1 : σ ≤ -1) {θ μ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hμ : 0 ≤ μ)
    (h1 : 1 + α + μ * α ≤ 2 * θ) (h2 : (k : ℝ) + σ + μ * σ ≤ ((k : ℝ) + 1) * θ) :
    ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X → |W b 0 X - c * X| ≤ C * X ^ θ := by
  have hk := H.hk
  have hc := H.hc
  have hA := H.hA
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨L, hL0, hL⟩ := linear_bound H hα1 (by linarith)
  have hq : 0 < 1 + 1 / -σ := by have : 0 < 1 / -σ := by apply div_pos one_pos; linarith
                                 linarith
  set S1 : ℝ := L / α with hS1
  set S2 : ℝ := L * (1 + 1 / -σ) with hS2
  have hS10 : 0 ≤ S1 := div_nonneg hL0 hα0.le
  have hS20 : 0 ≤ S2 := mul_nonneg hL0 hq.le
  set K1 : ℝ := 2 * A * 2 ^ (1 + α) * (4 * k) * S1 with hK1
  set K2 : ℝ := 2 ^ k * A * 2 ^ ((k : ℝ) + σ) * (4 * k) ^ k / (Nat.factorial k : ℝ) * S2
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
  have hWb := bracket (W b) (fun j u v => (W_mono b H.nonneg j).intervalIntegrable)
    (W_mono b H.nonneg 0) hh0.le (fun j y => W_rel b j hh0.le y) k
  have hMb := bracket (Mf c) (fun j u v => by unfold Mf; exact (by fun_prop : Continuous
      fun x : ℝ => c * x ^ (j + 1) / ((j : ℝ) + 1)).intervalIntegrable u v)
    (fun u v huv => by simp only [Mf, zero_add, pow_one, Nat.cast_zero, div_one]
                       exact mul_le_mul_of_nonneg_left huv hc)
    hh0.le (fun j y => Mf_rel c j h y) k
  -- the two exact sums
  have hs1 : Summable fun n => b n * wS α M n :=
    summable_of_sum_range_le (fun n => mul_nonneg (H.nonneg n) (wS_nonneg α M n))
      (sumS_le H hα0 hα1 hL hL0 hM0.le)
  have hs2 : Summable fun n => b n * wL σ M n :=
    summable_of_sum_range_le (fun n => mul_nonneg (H.nonneg n) (wL_nonneg σ M n))
      (sumL_le H hσ1 hL hL0 hM0)
  have hT1 : ∑' n, b n * wS α M n ≤ M ^ α * S1 := by
    refine Real.tsum_le_of_sum_range_le (fun n => mul_nonneg (H.nonneg n) (wS_nonneg α M n))
      (fun N => (sumS_le H hα0 hα1 hL hL0 hM0.le N).trans (le_of_eq ?_))
    rw [hS1]; ring
  have hT2 : ∑' n, b n * wL σ M n ≤ M ^ σ * S2 := by
    refine Real.tsum_le_of_sum_range_le (fun n => mul_nonneg (H.nonneg n) (wL_nonneg σ M n))
      (fun N => (sumL_le H hσ1 hL hL0 hM0 N).trans (le_of_eq ?_))
    rw [hS2]; ring
  set Λ : ℝ := 2 * A * (Nat.factorial k : ℝ) * h ^ (k - 1) * (2 * X) ^ (1 + α) * M ^ α * S1 +
        2 ^ k * A * (2 * X) ^ ((k : ℝ) + σ) * M ^ σ * S2 with hΛ
  have hPn1 : 0 ≤ 2 * A * (Nat.factorial k : ℝ) * h ^ (k - 1) * (2 * X) ^ (1 + α) := by positivity
  have hPn2 : 0 ≤ 2 ^ k * A * (2 * X) ^ ((k : ℝ) + σ) := by positivity
  have hEb : 2 * A * (Nat.factorial k : ℝ) * h ^ (k - 1) * (2 * X) ^ (1 + α) *
      ∑' n, b n * wS α M n + 2 ^ k * A * (2 * X) ^ ((k : ℝ) + σ) * ∑' n, b n * wL σ M n ≤ Λ := by
    have a1 := mul_le_mul_of_nonneg_left hT1 hPn1
    have a2 := mul_le_mul_of_nonneg_left hT2 hPn2
    rw [hΛ]; nlinarith
  have hD1 := (Dk_W_bound' H (x := X) (Y := 2 * X) hX hh0.le hM0 (by rw [hkh]; linarith)
    hs1 hs2).trans hEb
  have hD2 := (Dk_W_bound' H (x := X - k * h) (Y := 2 * X) hx1 hh0.le hM0 (by linarith)
    hs1 hs2).trans hEb
  obtain ⟨hWl, -⟩ := hWb X
  obtain ⟨-, hWu⟩ := hWb (X - k * h)
  rw [sub_add_cancel] at hWu
  obtain ⟨-, hMu⟩ := hMb X
  obtain ⟨hMl, -⟩ := hMb (X - k * h)
  simp only [Mf, zero_add, pow_one, Nat.cast_zero, div_one] at hMu hMl
  set P : ℝ := (Nat.factorial k : ℝ) * h ^ k with hP
  have hP0 : 0 < P := by positivity
  rw [abs_le] at hD1 hD2
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
  have hΛP : Λ / P ≤ (K1 + K2) * X ^ θ := by
    have hk1 : (k - 1 : ℕ) + 1 = k := by omega
    have hhk : h ^ k = h ^ (k - 1) * h := by rw [← pow_succ, hk1]
    have e1 : 2 * A * (Nat.factorial k : ℝ) * h ^ (k - 1) * (2 * X) ^ (1 + α) * M ^ α *
        S1 / P = 2 * A * 2 ^ (1 + α) * (4 * k) * S1 * X ^ (1 + α + μ * α - θ) := by
      rw [hP, hhk, Real.mul_rpow (by norm_num) hX0.le, hM, ← Real.rpow_mul hX0.le]
      rw [Real.rpow_sub hX0, Real.rpow_add hX0, hh]
      have : (0 : ℝ) < (Nat.factorial k : ℝ) := by positivity
      have : (0 : ℝ) < X ^ θ := by positivity
      have : (0 : ℝ) < h ^ (k - 1) := by positivity
      field_simp
      simp only [Real.rpow_add hX0, Real.rpow_one]; ring
    have e2 : 2 ^ k * A * (2 * X) ^ ((k : ℝ) + σ) * M ^ σ * S2 / P =
        2 ^ k * A * 2 ^ ((k : ℝ) + σ) * (4 * k) ^ k / (Nat.factorial k : ℝ) * S2 *
          X ^ ((k : ℝ) + σ + μ * σ - k * θ) := by
      rw [hP, Real.mul_rpow (by norm_num) hX0.le, hM, ← Real.rpow_mul hX0.le,
        Real.rpow_sub hX0, Real.rpow_add hX0, hh, div_pow,
        show (X ^ θ) ^ k = X ^ ((k : ℝ) * θ) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le, mul_comm]]
      have : (0 : ℝ) < (Nat.factorial k : ℝ) := by positivity
      have : (0 : ℝ) < X ^ ((k : ℝ) * θ) := by positivity
      field_simp
      simp only [Real.rpow_add hX0, Real.rpow_natCast]; ring
    have hx1' : X ^ (1 + α + μ * α - θ) ≤ X ^ θ :=
      Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    have hx2' : X ^ ((k : ℝ) + σ + μ * σ - k * θ) ≤ X ^ θ :=
      Real.rpow_le_rpow_of_exponent_le hX (by nlinarith)
    rw [hΛ, add_div, e1, e2, add_mul]
    gcongr
  have hckh : c * (k * h) ≤ c * X ^ θ := by
    rw [hkh]; exact mul_le_mul_of_nonneg_left (by linarith) hc
  have hd : |d| ≤ |d| * X ^ θ := le_mul_of_one_le_right (abs_nonneg _) hXθ
  have hW0 : 0 ≤ (W b 0 2 + 2 * c) * X ^ θ := by positivity
  have hCX : C * X ^ θ = (W b 0 2 + 2 * c) * X ^ θ +
      (c * X ^ θ + |d| * X ^ θ + (K1 + K2) * X ^ θ) := by rw [hCdef]; ring
  rw [abs_le]
  constructor
  · have : -(W b 0 X - c * X) ≤ C * X ^ θ := by
      rw [neg_sub]
      calc c * X - W b 0 X ≤ c * (k * h) - d + Λ / P := hlow
        _ ≤ c * X ^ θ + |d| * X ^ θ + (K1 + K2) * X ^ θ := by
            linarith [neg_le_abs d]
        _ ≤ C * X ^ θ := by rw [hCX]; linarith
    linarith
  · calc W b 0 X - c * X ≤ c * (k * h) + d + Λ / P := hup
      _ ≤ c * X ^ θ + |d| * X ^ θ + (K1 + K2) * X ^ θ := by linarith [le_abs_self d]
      _ ≤ C * X ^ θ := by rw [hCX]; linarith

end RamanujanTau.RankinExact
