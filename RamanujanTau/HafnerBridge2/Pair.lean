/-
# Item (c), part 3: evaluation of `MainTw(h, k)` for one pair

With `g = (h,k)`, `h₁ = h/g`, `k₁ = k/g`, `ℓ = [h,k]`, `n = h₁k₁` (`n · hk = ℓ²`):

* `fseq h k m = ι_k(m+1) ι_h(m+1)/(m+1)` has partial sums `(1/ℓ) A_{T(h₁,k₁)}(⌊N/ℓ⌋)` (`Sp_fseq`), hence a
  log asymptotic with `c/ℓ`, `(K − c log ℓ)/ℓ` (`logAsym_fseq`);
* `MainTw h k X H = 2√(hk) · Wint Φ` (`MainTw_eq`);
* `|Wint Φ − (2r₀/ℓ)(ρρ·I₁ + q₁·I₀)| ≤ Z (hk)⁵ (X+H)^{9/10}` (`pair_eval`), where
  `I₀ = Wint 1`, `I₁ = Wint ℓ(t)`, `q₁ = ρρ(γ_R/r₀ − ½ log n) + ρ₁ρ + ρρ₁` (the `Q¹` summand).
-/
import RamanujanTau.HafnerBridge2.Wint

set_option autoImplicit false

namespace RamanujanTau.HafnerBridge2

open MeasureTheory Set Filter Topology Complex Finset
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.GoodSecondTerm2 RamanujanTau.TwistedMoment
open RamanujanTau.HafnerBridge
open scoped Interval

lemma r0_pos : 0 < r0 := by
  unfold r0 RamanujanTau.GoodSecondTerm.c0 CriticalMeanSquareAsymp.rankinC
  have := RamanujanTau.RankinError.petNormSq_pos
  have hπ := Real.pi_pos
  positivity

lemma r0_gamR : r0 * gamR = gammaD := by
  unfold gamR; field_simp [r0_pos.ne']

/-! ### gcd/lcm bookkeeping -/

section
variable {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k)
include hh hk

lemma g_pos : 0 < Nat.gcd h k := Nat.gcd_pos_of_pos_left _ (by omega)

lemma lcm_eq_left : Nat.lcm h k = k * (h / Nat.gcd h k) := by
  obtain ⟨a, ha⟩ := Nat.gcd_dvd_left h k
  have hg := g_pos hh hk
  have h1 : h / Nat.gcd h k = a := Nat.div_eq_of_eq_mul_left hg (by rw [mul_comm]; exact ha)
  have h2 : h * k = (k * a) * Nat.gcd h k := by
    calc h * k = (Nat.gcd h k * a) * k := by rw [← ha]
      _ = _ := by ring
  rw [h1]
  exact Nat.div_eq_of_eq_mul_left hg h2

lemma lcm_eq_right : Nat.lcm h k = h * (k / Nat.gcd h k) := by
  have := lcm_eq_left hk hh
  rwa [Nat.lcm_comm, Nat.gcd_comm] at this

lemma lcm_pos : 0 < Nat.lcm h k := Nat.lcm_pos (by omega) (by omega)

lemma n_mul_eq : (h / Nat.gcd h k) * (k / Nat.gcd h k) * (h * k) = Nat.lcm h k ^ 2 := by
  rw [sq]
  nth_rewrite 1 [lcm_eq_left hh hk]
  rw [lcm_eq_right hh hk]; ring

lemma log_n_eq : Real.log (((h / Nat.gcd h k) * (k / Nat.gcd h k) : ℕ) : ℝ) =
    2 * Real.log (Nat.lcm h k : ℝ) - Real.log ((h * k : ℕ) : ℝ) := by
  have h1 := n_mul_eq hh hk
  have hn : 0 < (h / Nat.gcd h k) * (k / Nat.gcd h k) := Nat.mul_pos
    (Nat.div_pos (Nat.gcd_le_left _ (by omega)) (g_pos hh hk)) (Nat.div_pos (Nat.gcd_le_right _ (by omega)) (g_pos hh hk))
  have hhk : 0 < h * k := Nat.mul_pos (by omega) (by omega)
  have hn0 : (0 : ℝ) < (((h / Nat.gcd h k) * (k / Nat.gcd h k) : ℕ) : ℝ) := by exact_mod_cast hn
  have hhk0 : (0 : ℝ) < ((h * k : ℕ) : ℝ) := by exact_mod_cast hhk
  have hl0 : (0 : ℝ) < (Nat.lcm h k : ℝ) := by exact_mod_cast lcm_pos hh hk
  have e : (((h / Nat.gcd h k) * (k / Nat.gcd h k) : ℕ) : ℝ) * ((h * k : ℕ) : ℝ) = (Nat.lcm h k : ℝ) ^ 2 := by
    exact_mod_cast h1
  have e2 := congrArg Real.log e
  rw [Real.log_mul hn0.ne' hhk0.ne', Real.log_pow] at e2
  push_cast at e2 ⊢
  linarith

lemma iota_prod (x : ℕ) :
    iota k x * iota h x =
      if Nat.lcm h k ∣ x then T (h / Nat.gcd h k) (k / Nat.gcd h k) (x / Nat.lcm h k) else 0 := by
  have hl := lcm_pos hh hk
  unfold iota
  by_cases hd : Nat.lcm h k ∣ x
  · rw [if_pos hd, if_pos (dvd_trans (Nat.dvd_lcm_right h k) hd), if_pos (dvd_trans (Nat.dvd_lcm_left h k) hd)]
    obtain ⟨r, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left _ hl]
    have e1 : Nat.lcm h k * r / k = h / Nat.gcd h k * r := by
      rw [lcm_eq_left hh hk, mul_assoc, Nat.mul_div_cancel_left _ (by omega)]
    have e2 : Nat.lcm h k * r / h = k / Nat.gcd h k * r := by
      rw [lcm_eq_right hh hk, mul_assoc, Nat.mul_div_cancel_left _ (by omega)]
    rw [e1, e2]; rfl
  · rw [if_neg hd]
    by_cases h1 : k ∣ x
    · by_cases h2 : h ∣ x
      · exact absurd (Nat.lcm_dvd h2 h1) hd
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

end
/-- `f(m) = ι_k(m+1) ι_h(m+1) e^{−lg m}`, the `MainTw` coefficient. -/
noncomputable def fseq (h k : ℕ) (m : ℕ) : ℝ := iota k (m + 1) * iota h (m + 1) * Real.exp (-((lg m + lg m) / 2))

lemma sum_range_shift (F : ℕ → ℝ) (N : ℕ) : ∑ m ∈ range N, F (m + 1) = ∑ x ∈ Finset.Icc 1 N, F x := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

lemma Sp_fseq {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) (N : ℕ) :
    Sp (fseq h k) N = (1 / (Nat.lcm h k : ℝ)) * Asum (T (h / Nat.gcd h k) (k / Nat.gcd h k)) (N / Nat.lcm h k) := by
  have hl := lcm_pos hh hk
  have hl0 : (0 : ℝ) < Nat.lcm h k := by exact_mod_cast hl
  have he : ∀ m : ℕ, Real.exp (-((lg m + lg m) / 2)) = 1 / ((m + 1 : ℕ) : ℝ) := by
    intro m
    rw [show -((lg m + lg m) / 2) = -lg m by ring, Real.exp_neg, lg, Real.exp_log (by positivity)]
    push_cast; ring
  unfold Sp
  have e1 : ∑ m ∈ range N, fseq h k m =
      ∑ x ∈ Finset.Icc 1 N, (if Nat.lcm h k ∣ x then T (h / Nat.gcd h k) (k / Nat.gcd h k) (x / Nat.lcm h k) else 0) /
        (x : ℝ) := by
    rw [← sum_range_shift (fun x => (if Nat.lcm h k ∣ x then T (h / Nat.gcd h k) (k / Nat.gcd h k)
      (x / Nat.lcm h k) else 0) / (x : ℝ))]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [fseq]
    rw [iota_prod hh hk, he]; ring
  rw [e1]
  have hpt : ∀ x ∈ Finset.Icc 1 N, (if Nat.lcm h k ∣ x then T (h / Nat.gcd h k) (k / Nat.gcd h k) (x / Nat.lcm h k)
      else 0) / (x : ℝ) = if Nat.lcm h k ∣ x then (1 / (Nat.lcm h k : ℝ)) *
        (T (h / Nat.gcd h k) (k / Nat.gcd h k) (x / Nat.lcm h k) / ((x / Nat.lcm h k : ℕ) : ℝ)) else 0 := by
    intro x hx
    split_ifs with hd
    · obtain ⟨r, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left _ hl]
      rw [Finset.mem_Icc] at hx
      have hr : r ≠ 0 := by rintro rfl; simp at hx
      have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr
      push_cast; field_simp
    · simp
  rw [Finset.sum_congr rfl hpt, sum_dvd (by omega)
    (fun M => (1 / (Nat.lcm h k : ℝ)) * (T (h / Nat.gcd h k) (k / Nat.gcd h k) M / (M : ℝ))) N,
    Asum, Finset.mul_sum]

/-- The floor comparison `|A(⌊N/d⌋) − c log(N/d) − K| ≤ (2E + 2|c|)(N/d)^{−1/5}`. -/
lemma floor_asym {F : ℕ → ℝ} {c K E : ℝ}
    (hF : ∀ N : ℕ, 1 ≤ N → |Asum F N - c * Real.log N - K| ≤ E * (N : ℝ) ^ (-(1 / 5 : ℝ)))
    {N d : ℕ} (hd : 1 ≤ d) (hdN : d ≤ N) :
    |Asum F (N / d) - c * Real.log ((N : ℝ) / d) - K| ≤ (2 * E + 2 * |c|) * ((N : ℝ) / d) ^ (-(1 / 5 : ℝ)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set M := N / d with hMdef
  have hM1 : 1 ≤ M := Nat.div_pos hdN (by omega)
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  set y : ℝ := (N : ℝ) / d with hy
  have hMy : (M : ℝ) ≤ y := by rw [hy, hMdef]; exact Nat.cast_div_le
  have hyM : y < M + 1 := by
    rw [hy, div_lt_iff₀ hd0]
    have h := Nat.lt_div_mul_add (a := N) (b := d) (by omega)
    have : (N : ℝ) < (M : ℝ) * d + d := by rw [hMdef]; exact_mod_cast h
    linarith
  have hy1 : 1 ≤ y := le_trans hMr hMy
  have hy0 : 0 < y := by linarith
  have hA := hF M hM1
  have hlog1 : Real.log y - Real.log M ≤ 1 / M := by
    rw [← Real.log_div hy0.ne' (by linarith)]
    have := Real.log_le_sub_one_of_pos (x := y / M) (by positivity)
    have e : y / M - 1 ≤ 1 / M := by rw [div_sub_one (by linarith), div_le_div_iff_of_pos_right (by linarith)]; linarith
    linarith
  have hlog2 : Real.log M ≤ Real.log y := Real.log_le_log (by linarith) hMy
  have hM2 : y / 2 ≤ M := by linarith
  have hyp : 0 < y ^ (-(1 / 5 : ℝ)) := Real.rpow_pos_of_pos hy0 _
  have hMp : (M : ℝ) ^ (-(1 / 5 : ℝ)) ≤ 2 * y ^ (-(1 / 5 : ℝ)) := by
    calc (M : ℝ) ^ (-(1 / 5 : ℝ)) ≤ (y / 2) ^ (-(1 / 5 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hM2 (by norm_num)
      _ = 2 ^ (1 / 5 : ℝ) * y ^ (-(1 / 5 : ℝ)) := by
          rw [Real.div_rpow hy0.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
          field_simp
      _ ≤ 2 * y ^ (-(1 / 5 : ℝ)) := by
          gcongr
          calc (2 : ℝ) ^ (1 / 5 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  have hinvM : 1 / (M : ℝ) ≤ 2 * y ^ (-(1 / 5 : ℝ)) := by
    have h1 : 1 / (M : ℝ) ≤ 2 / y := by
      rw [div_le_div_iff₀ (by linarith) hy0]; linarith
    have h2 : 1 / y ≤ y ^ (-(1 / 5 : ℝ)) := by
      rw [one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
    calc 1 / (M : ℝ) ≤ 2 / y := h1
      _ = 2 * (1 / y) := by ring
      _ ≤ 2 * y ^ (-(1 / 5 : ℝ)) := by gcongr
  have e : Asum F M - c * Real.log y - K = (Asum F M - c * Real.log M - K) + c * (Real.log M - Real.log y) := by
    ring
  rw [e]
  have hc : |c * (Real.log M - Real.log y)| ≤ |c| * (1 / M) := by
    rw [abs_mul]; gcongr; rw [abs_le]; constructor <;> linarith
  have hE0 : 0 ≤ E := by
    have := (abs_nonneg _).trans hA
    have hp : 0 < (M : ℝ) ^ (-(1 / 5 : ℝ)) := by positivity
    by_contra hneg; push Not at hneg; nlinarith
  calc _ ≤ |Asum F M - c * Real.log M - K| + |c * (Real.log M - Real.log y)| := abs_add_le _ _
    _ ≤ E * (M : ℝ) ^ (-(1 / 5 : ℝ)) + |c| * (1 / M) := add_le_add hA hc
    _ ≤ E * (2 * y ^ (-(1 / 5 : ℝ))) + |c| * (2 * y ^ (-(1 / 5 : ℝ))) := by gcongr
    _ = _ := by ring

lemma logAsym_fseq {h k : ℕ} (hh : 1 ≤ h) (hk : 1 ≤ k) {E : ℝ} (hE : 0 ≤ E)
    (hT : TwAsym (h / Nat.gcd h k) (k / Nat.gcd h k) E) :
    LogAsym (fseq h k) (cT (h / Nat.gcd h k) (k / Nat.gcd h k) / Nat.lcm h k)
      ((KT (h / Nat.gcd h k) (k / Nat.gcd h k) - cT (h / Nat.gcd h k) (k / Nat.gcd h k) * Real.log (Nat.lcm h k)) /
        Nat.lcm h k)
      ((2 * E + 2 * |cT (h / Nat.gcd h k) (k / Nat.gcd h k)| + |KT (h / Nat.gcd h k) (k / Nat.gcd h k)|) *
        Nat.lcm h k) := by
  set c := cT (h / Nat.gcd h k) (k / Nat.gcd h k)
  set K := KT (h / Nat.gcd h k) (k / Nat.gcd h k)
  set ℓ := Nat.lcm h k with hℓ
  have hl := lcm_pos hh hk
  have hl1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hl
  have hl0 : (0 : ℝ) < ℓ := by linarith
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hc0 := abs_nonneg c
  have hK0 := abs_nonneg K
  have hNp : 0 < (N : ℝ) ^ (-(1 / 5 : ℝ)) := Real.rpow_pos_of_pos hN0 _
  rw [Sp_fseq hh hk]
  rcases le_or_gt ℓ N with hle | hgt
  · have hfl := floor_asym hT hl hle
    have hlogy : Real.log ((N : ℝ) / ℓ) = Real.log N - Real.log ℓ := Real.log_div hN0.ne' hl0.ne'
    rw [hlogy] at hfl
    have e : 1 / (ℓ : ℝ) * Asum (T (h / Nat.gcd h k) (k / Nat.gcd h k)) (N / ℓ) - c / ℓ * Real.log N -
        (K - c * Real.log ℓ) / ℓ = (1 / ℓ) * (Asum (T (h / Nat.gcd h k) (k / Nat.gcd h k)) (N / ℓ) -
          c * (Real.log N - Real.log ℓ) - K) := by field_simp; ring
    rw [e, abs_mul, abs_of_pos (by positivity)]
    have hy : ((N : ℝ) / ℓ) ^ (-(1 / 5 : ℝ)) = (N : ℝ) ^ (-(1 / 5 : ℝ)) * (ℓ : ℝ) ^ (1 / 5 : ℝ) := by
      rw [Real.div_rpow hN0.le hl0.le, Real.rpow_neg hl0.le, div_inv_eq_mul]
    rw [hy] at hfl
    have hl15 : (ℓ : ℝ) ^ (1 / 5 : ℝ) ≤ ℓ := by
      calc (ℓ : ℝ) ^ (1 / 5 : ℝ) ≤ (ℓ : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hl1 (by norm_num)
        _ = ℓ := Real.rpow_one _
    calc 1 / (ℓ : ℝ) * |Asum (T (h / Nat.gcd h k) (k / Nat.gcd h k)) (N / ℓ) - c * (Real.log N - Real.log ℓ) - K|
        ≤ 1 / (ℓ : ℝ) * ((2 * E + 2 * |c|) * ((N : ℝ) ^ (-(1 / 5 : ℝ)) * (ℓ : ℝ) ^ (1 / 5 : ℝ))) := by gcongr
      _ ≤ 1 / (ℓ : ℝ) * ((2 * E + 2 * |c|) * ((N : ℝ) ^ (-(1 / 5 : ℝ)) * ℓ)) := by gcongr
      _ = (2 * E + 2 * |c|) * (N : ℝ) ^ (-(1 / 5 : ℝ)) := by field_simp
      _ ≤ (2 * E + 2 * |c| + |K|) * ℓ * (N : ℝ) ^ (-(1 / 5 : ℝ)) := by
          have : 2 * E + 2 * |c| ≤ (2 * E + 2 * |c| + |K|) * ℓ := by nlinarith
          nlinarith
  · have h0 : N / ℓ = 0 := Nat.div_eq_of_lt hgt
    rw [h0, Asum_zero, mul_zero]
    have hlt : (N : ℝ) < ℓ := by exact_mod_cast hgt
    have hlogN : Real.log N ≤ Real.log ℓ := Real.log_le_log hN0 hlt.le
    have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
    have hlogl : Real.log ℓ ≤ ℓ := (Real.log_le_sub_one_of_pos hl0).trans (by linarith)
    have e : (0 : ℝ) - c / ℓ * Real.log N - (K - c * Real.log ℓ) / ℓ =
        (c * (Real.log ℓ - Real.log N) - K) / ℓ := by field_simp; ring
    rw [e, abs_div, abs_of_pos hl0, div_le_iff₀ hl0]
    have h1 : |c * (Real.log ℓ - Real.log N) - K| ≤ |c| * ℓ + |K| := by
      refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
      rw [abs_mul, abs_of_nonneg (show 0 ≤ Real.log ℓ - Real.log N by linarith)]
      exact mul_le_mul_of_nonneg_left (by linarith) hc0
    -- `ℓ N^{−1/5} ≥ 1`
    have hNl : (ℓ : ℝ) ^ (-(1 / 5 : ℝ)) ≤ (N : ℝ) ^ (-(1 / 5 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hN0 hlt.le (by norm_num)
    have hl45 : 1 ≤ (ℓ : ℝ) * (ℓ : ℝ) ^ (-(1 / 5 : ℝ)) := by
      rw [show (ℓ : ℝ) * (ℓ : ℝ) ^ (-(1 / 5 : ℝ)) = (ℓ : ℝ) ^ (4 / 5 : ℝ) by
        rw [← Real.rpow_one_add' hl0.le (by norm_num)]; norm_num]
      exact Real.one_le_rpow hl1 (by norm_num)
    have hlN : 1 ≤ (ℓ : ℝ) * (N : ℝ) ^ (-(1 / 5 : ℝ)) :=
      hl45.trans (mul_le_mul_of_nonneg_left hNl hl0.le)
    calc |c * (Real.log ℓ - Real.log N) - K| ≤ |c| * ℓ + |K| := h1
      _ ≤ (2 * E + 2 * |c| + |K|) * 1 * ℓ := by nlinarith [mul_nonneg hE hl0.le, mul_le_mul_of_nonneg_left hl1 hK0]
      _ ≤ (2 * E + 2 * |c| + |K|) * ((ℓ : ℝ) * (N : ℝ) ^ (-(1 / 5 : ℝ))) * ℓ := by gcongr
      _ = _ := by ring

/-! ### `MainTw` as a `Wint` -/

lemma MainTw_eq {h k : ℕ} {c K E : ℝ} (hE : 0 ≤ E) (hS : LogAsym (fseq h k) c K E) {X H : ℝ} (hX : 16 ≤ X)
    (hH : 0 < H) :
    MainTw h k X H = ((2 * Real.sqrt ((h * k : ℕ) : ℝ) * Wint X H (Phi (fseq h k) (Real.log ((h * k : ℕ) : ℝ))) : ℝ) : ℂ) := by
  unfold MainTw
  have hterm : ∀ m : ℕ, (((iota k (m + 1) * iota h (m + 1) * Real.exp (-((lg m + lg m) / 2)) : ℝ) : ℂ) *
      Ptil (lg m + lg m - Real.log ((h * k : ℕ) : ℝ)) (lg m - lg m) X H) =
      ((fseq h k m * Wint X H (fun t => V (2 * lg m - (Real.log ((h * k : ℕ) : ℝ) + 2 * ellT t))) : ℝ) : ℂ) := by
    intro m
    rw [sub_self, Ptil_zero]
    have hW : WV (lg m + lg m - Real.log ((h * k : ℕ) : ℝ)) =
        fun t => V (2 * lg m - (Real.log ((h * k : ℕ) : ℝ) + 2 * ellT t)) := by
      funext t; unfold WV
      rw [show lg m + lg m - Real.log ((h * k : ℕ) : ℝ) - 2 * ellT t =
        2 * lg m - (Real.log ((h * k : ℕ) : ℝ) + 2 * ellT t) by ring]
    rw [hW, ← Complex.ofReal_mul]; rfl
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum, (hasSum_Wint hE hS _ hX hH).tsum_eq]
  push_cast; ring

end RamanujanTau.HafnerBridge2
