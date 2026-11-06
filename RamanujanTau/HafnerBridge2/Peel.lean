/-
# One-prime peeling of a logarithmic partial-sum asymptotic

Let `A_F(N) = Σ_{r≤N} F(r)/r` satisfy `|A_F(N) − c log N − K| ≤ E N^{−1/5}`, and let
`f(r) = Σ_{p^j ∣ r} g_j F(r/p^j)` (`conv`). With `x = 1/p`, `q = p^{−4/5}`,

    G = Σ g_j x^j,   G₁ = Σ j log p · g_j x^j,   S = Σ (1 + j log p)|g_j| q^j < ∞,

we get (`peel_asymp`)

    |A_f(N) − cG log N − (KG − cG₁)| ≤ (2E + 3|c| + |K|) S N^{−1/5}.

Proof: `A_f(N) = Σ_j g_j x^j A_F(⌊N/p^j⌋)` (`Asum_conv`), then termwise comparison.
-/
import RamanujanTau.HafnerBridge2.Lam

set_option autoImplicit false

namespace RamanujanTau.HafnerBridge2

open Finset

/-- `A_F(N) = Σ_{r ≤ N} F(r)/r`. -/
noncomputable def Asum (F : ℕ → ℝ) (N : ℕ) : ℝ := ∑ r ∈ Icc 1 N, F r / r

/-- `f(r) = Σ_{p^j ∣ r} g_j F(r/p^j)`. -/
noncomputable def conv (p : ℕ) (g F : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ range (r + 1), if p ^ j ∣ r then g j * F (r / p ^ j) else 0

lemma Asum_zero (F : ℕ → ℝ) : Asum F 0 = 0 := by simp [Asum]

lemma Asum_conv {p : ℕ} (hp : 2 ≤ p) (g F : ℕ → ℝ) (N : ℕ) :
    Asum (conv p g F) N = ∑ j ∈ range (N + 1), g j * ((p : ℝ)⁻¹) ^ j * Asum F (N / p ^ j) := by
  unfold Asum conv
  have hext : ∀ r ∈ Icc 1 N, (∑ j ∈ range (r + 1), if p ^ j ∣ r then g j * F (r / p ^ j) else 0) =
      ∑ j ∈ range (N + 1), if p ^ j ∣ r then g j * F (r / p ^ j) else 0 := by
    intro r hr
    rw [mem_Icc] at hr
    refine Finset.sum_subset (range_subset_range.mpr (by omega)) (fun j hj hj' => ?_)
    rw [mem_range] at hj'
    rw [if_neg]
    intro hd
    have h1 := Nat.le_of_dvd (by omega) hd
    have h2 : j < p ^ j := Nat.lt_pow_self (by omega)
    omega
  rw [Finset.sum_congr rfl (fun r hr => by rw [hext r hr])]
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hpj : 1 ≤ p ^ j := Nat.one_le_pow _ _ (by omega)
  have hpt : ∀ r ∈ Icc 1 N, (if p ^ j ∣ r then g j * F (r / p ^ j) else 0) / (r : ℝ) =
      if p ^ j ∣ r then g j * ((p : ℝ)⁻¹) ^ j * (F (r / p ^ j) / ((r / p ^ j : ℕ) : ℝ)) else 0 := by
    intro r hr
    split_ifs with hd
    · obtain ⟨m, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left _ (by omega)]
      push_cast
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
      rw [mem_Icc] at hr
      have hm : m ≠ 0 := by rintro rfl; simp at hr
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      field_simp
      rw [one_div, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp0), mul_one]
    · simp
  rw [Finset.sum_congr rfl hpt,
    TwistedMoment.sum_dvd hpj (fun M => g j * ((p : ℝ)⁻¹) ^ j * (F M / (M : ℝ))) N, Finset.mul_sum]

/-- `q = p^{−4/5}`. -/
noncomputable def qp (p : ℕ) : ℝ := (p : ℝ) ^ (-(4 / 5 : ℝ))

lemma xpow_eq {p : ℕ} (hp : 2 ≤ p) (j : ℕ) : ((p : ℝ)⁻¹) ^ j = qp p ^ j * ((p : ℝ) ^ j) ^ (-(1 / 5 : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  unfold qp
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
    ← Real.rpow_mul hp0.le, ← Real.rpow_add hp0, ← Real.rpow_neg_one, ← Real.rpow_mul hp0.le]
  congr 1; ring

lemma qp_pos {p : ℕ} (hp : 2 ≤ p) : 0 < qp p := by
  unfold qp; exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < p by omega)) _

lemma xpow_le_qpow {p : ℕ} (hp : 2 ≤ p) (j : ℕ) : ((p : ℝ)⁻¹) ^ j ≤ qp p ^ j := by
  rw [xpow_eq hp]
  have h1 : ((p : ℝ) ^ j) ^ (-(1 / 5 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ (by exact_mod_cast (show 1 ≤ p by omega)))
      (by norm_num)
  have := pow_pos (qp_pos hp) j
  nlinarith

/-- The termwise bound. -/
lemma term_le {p : ℕ} (hp : 2 ≤ p) {F : ℕ → ℝ} {c K E : ℝ} (hE : 0 ≤ E)
    (hF : ∀ N : ℕ, 1 ≤ N → |Asum F N - c * Real.log N - K| ≤ E * (N : ℝ) ^ (-(1 / 5 : ℝ)))
    (gj : ℝ) {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    |gj * ((p : ℝ)⁻¹) ^ j * (Asum F (N / p ^ j) - c * (Real.log N - j * Real.log p) - K)| ≤
      (2 * E + 3 * |c| + |K|) * (N : ℝ) ^ (-(1 / 5 : ℝ)) * ((1 + j * Real.log p) * |gj| * qp p ^ j) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1.le
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hpj0 : (0 : ℝ) < (p : ℝ) ^ j := pow_pos hp0 j
  have hq := pow_pos (qp_pos hp) j
  have hNp : 0 < (N : ℝ) ^ (-(1 / 5 : ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hjl : 0 ≤ (j : ℝ) * Real.log p := by positivity
  have hlogpj : Real.log (((p : ℝ) ^ j)) = j * Real.log p := by rw [Real.log_pow]
  rw [abs_mul, abs_mul, abs_of_pos (pow_pos (inv_pos.mpr hp0) j)]
  set Z := 2 * E + 3 * |c| + |K| with hZ
  have hcK : 0 ≤ |c| := abs_nonneg c
  have hK0 : 0 ≤ |K| := abs_nonneg K
  -- the key bound: x^j |Δ| ≤ Z N^{-1/5} (1 + j log p) q^j
  suffices hkey : ((p : ℝ)⁻¹) ^ j * |Asum F (N / p ^ j) - c * (Real.log N - j * Real.log p) - K| ≤
      Z * (N : ℝ) ^ (-(1 / 5 : ℝ)) * ((1 + j * Real.log p) * qp p ^ j) by
    have := abs_nonneg gj
    calc |gj| * ((p : ℝ)⁻¹) ^ j * |Asum F (N / p ^ j) - c * (Real.log N - j * Real.log p) - K|
        = |gj| * (((p : ℝ)⁻¹) ^ j * |Asum F (N / p ^ j) - c * (Real.log N - j * Real.log p) - K|) := by
          ring
      _ ≤ |gj| * (Z * (N : ℝ) ^ (-(1 / 5 : ℝ)) * ((1 + j * Real.log p) * qp p ^ j)) := by gcongr
      _ = _ := by ring
  rcases le_or_gt (p ^ j) N with hle | hgt
  · -- p^j ≤ N
    set M := N / p ^ j with hMdef
    have hM1 : 1 ≤ M := Nat.div_pos hle (Nat.pos_of_ne_zero (by positivity))
    have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    set y : ℝ := (N : ℝ) / (p : ℝ) ^ j with hy
    have hMy : (M : ℝ) ≤ y := by
      rw [hy, hMdef]; have := Nat.cast_div_le (α := ℝ) (m := N) (n := p ^ j); push_cast at this; exact this
    have hyM : y < M + 1 := by
      rw [hy, div_lt_iff₀ hpj0]
      have h := Nat.lt_div_mul_add (a := N) (b := p ^ j) (by positivity)
      have : (N : ℝ) < (M : ℝ) * (p ^ j : ℕ) + (p ^ j : ℕ) := by
        rw [hMdef]; exact_mod_cast h
      push_cast at this; linarith
    have hy1 : 1 ≤ y := le_trans hMr hMy
    have hy0 : 0 < y := by linarith
    have hlogy : Real.log N - j * Real.log p = Real.log y := by
      rw [hy, Real.log_div hN0.ne' hpj0.ne', hlogpj]
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
    have hΔ : |Asum F M - c * (Real.log N - j * Real.log p) - K| ≤ (2 * E + 2 * |c|) * y ^ (-(1 / 5 : ℝ)) := by
      rw [hlogy]
      have e : Asum F M - c * Real.log y - K = (Asum F M - c * Real.log M - K) + c * (Real.log M - Real.log y) := by
        ring
      rw [e]
      have hc : |c * (Real.log M - Real.log y)| ≤ |c| * (1 / M) := by
        rw [abs_mul]; gcongr; rw [abs_le]; constructor <;> linarith
      calc _ ≤ |Asum F M - c * Real.log M - K| + |c * (Real.log M - Real.log y)| := abs_add_le _ _
        _ ≤ E * (M : ℝ) ^ (-(1 / 5 : ℝ)) + |c| * (1 / M) := add_le_add hA hc
        _ ≤ E * (2 * y ^ (-(1 / 5 : ℝ))) + |c| * (2 * y ^ (-(1 / 5 : ℝ))) := by gcongr
        _ = _ := by ring
    have hxy : ((p : ℝ)⁻¹) ^ j * y ^ (-(1 / 5 : ℝ)) = qp p ^ j * (N : ℝ) ^ (-(1 / 5 : ℝ)) := by
      rw [xpow_eq hp, hy, Real.div_rpow hN0.le hpj0.le]
      have : 0 < ((p : ℝ) ^ j) ^ (-(1 / 5 : ℝ)) := Real.rpow_pos_of_pos hpj0 _
      field_simp
    calc ((p : ℝ)⁻¹) ^ j * |Asum F M - c * (Real.log N - j * Real.log p) - K|
        ≤ ((p : ℝ)⁻¹) ^ j * ((2 * E + 2 * |c|) * y ^ (-(1 / 5 : ℝ))) := by gcongr
      _ = (2 * E + 2 * |c|) * (qp p ^ j * (N : ℝ) ^ (-(1 / 5 : ℝ))) := by rw [← hxy]; ring
      _ ≤ Z * (N : ℝ) ^ (-(1 / 5 : ℝ)) * ((1 + j * Real.log p) * qp p ^ j) := by
          have h1 : 2 * E + 2 * |c| ≤ Z * (1 + j * Real.log p) := by
            rw [hZ]; nlinarith [mul_nonneg (show 0 ≤ 2 * E + 3 * |c| + |K| by positivity) hjl]
          calc (2 * E + 2 * |c|) * (qp p ^ j * (N : ℝ) ^ (-(1 / 5 : ℝ)))
              ≤ Z * (1 + j * Real.log p) * (qp p ^ j * (N : ℝ) ^ (-(1 / 5 : ℝ))) := by gcongr
            _ = _ := by ring
  · -- p^j > N
    have h0 : N / p ^ j = 0 := Nat.div_eq_of_lt hgt
    rw [h0, Asum_zero]
    have hlogN : Real.log N ≤ j * Real.log p := by
      rw [← hlogpj]; exact Real.log_le_log hN0 (by exact_mod_cast hgt.le)
    have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hNr
    have hΔ : |0 - c * (Real.log N - j * Real.log p) - K| ≤ |c| * (j * Real.log p) + |K| := by
      calc |0 - c * (Real.log N - j * Real.log p) - K| ≤ |c * (Real.log N - j * Real.log p)| + |K| := by
            rw [show (0 : ℝ) - c * (Real.log N - j * Real.log p) - K =
              -(c * (Real.log N - j * Real.log p)) + -K by ring]
            refine (abs_add_le _ _).trans ?_; rw [abs_neg, abs_neg]
        _ ≤ |c| * (j * Real.log p) + |K| := by
            rw [abs_mul]; gcongr; rw [abs_le]; constructor <;> linarith
    have hx : ((p : ℝ)⁻¹) ^ j ≤ qp p ^ j * (N : ℝ) ^ (-(1 / 5 : ℝ)) := by
      rw [xpow_eq hp]
      refine mul_le_mul_of_nonneg_left ?_ hq.le
      exact Real.rpow_le_rpow_of_nonpos hN0 (show (N : ℝ) ≤ (p : ℝ) ^ j by exact_mod_cast hgt.le)
        (by norm_num)
    have hx0 : 0 ≤ ((p : ℝ)⁻¹) ^ j := by positivity
    calc ((p : ℝ)⁻¹) ^ j * |0 - c * (Real.log N - j * Real.log p) - K|
        ≤ (qp p ^ j * (N : ℝ) ^ (-(1 / 5 : ℝ))) * (|c| * (j * Real.log p) + |K|) :=
          mul_le_mul hx hΔ (abs_nonneg _) (by positivity)
      _ ≤ Z * (N : ℝ) ^ (-(1 / 5 : ℝ)) * ((1 + j * Real.log p) * qp p ^ j) := by
          have h1 : |c| * (j * Real.log p) + |K| ≤ Z * (1 + j * Real.log p) := by
            rw [hZ]; nlinarith [mul_nonneg (show 0 ≤ 2 * E + 2 * |c| + |K| by positivity) hjl, mul_nonneg hcK hjl]
          calc (qp p ^ j * (N : ℝ) ^ (-(1 / 5 : ℝ))) * (|c| * (j * Real.log p) + |K|)
              ≤ (qp p ^ j * (N : ℝ) ^ (-(1 / 5 : ℝ))) * (Z * (1 + j * Real.log p)) := by gcongr
            _ = _ := by ring

/-- `S = Σ (1 + j log p)|g_j| q^j`. -/
noncomputable def Sg (p : ℕ) (g : ℕ → ℝ) : ℝ := ∑' j : ℕ, (1 + j * Real.log p) * |g j| * qp p ^ j

noncomputable def Gg (p : ℕ) (g : ℕ → ℝ) : ℝ := ∑' j : ℕ, g j * ((p : ℝ)⁻¹) ^ j

noncomputable def G1g (p : ℕ) (g : ℕ → ℝ) : ℝ := ∑' j : ℕ, j * Real.log p * g j * ((p : ℝ)⁻¹) ^ j

lemma summable_G {p : ℕ} (hp : 2 ≤ p) {g : ℕ → ℝ}
    (hS : Summable fun j : ℕ => (1 + j * Real.log p) * |g j| * qp p ^ j) :
    Summable fun j : ℕ => g j * ((p : ℝ)⁻¹) ^ j := by
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  refine Summable.of_norm_bounded hS (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((p : ℝ)⁻¹) ^ j)]
  have h1 := xpow_le_qpow hp j
  have : 0 ≤ (j : ℝ) * Real.log p := by positivity
  have hq := pow_pos (qp_pos hp) j
  have hh : 0 ≤ (j : ℝ) * Real.log p * |g j| * qp p ^ j := by positivity
  have h3 := mul_le_mul_of_nonneg_left h1 (abs_nonneg (g j))
  linarith

lemma summable_G1 {p : ℕ} (hp : 2 ≤ p) {g : ℕ → ℝ}
    (hS : Summable fun j : ℕ => (1 + j * Real.log p) * |g j| * qp p ^ j) :
    Summable fun j : ℕ => j * Real.log p * g j * ((p : ℝ)⁻¹) ^ j := by
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  refine Summable.of_norm_bounded hS (fun j => ?_)
  have hjl : 0 ≤ (j : ℝ) * Real.log p := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hjl,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ((p : ℝ)⁻¹) ^ j)]
  have h1 := xpow_le_qpow hp j
  have := abs_nonneg (g j)
  have := pow_pos (qp_pos hp) j
  have h2 : (j : ℝ) * Real.log p * |g j| * ((p : ℝ)⁻¹) ^ j ≤ (j : ℝ) * Real.log p * |g j| * qp p ^ j :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith [mul_nonneg (abs_nonneg (g j)) this.le]

lemma abs_Gg_le {p : ℕ} (hp : 2 ≤ p) {g : ℕ → ℝ}
    (hS : Summable fun j : ℕ => (1 + j * Real.log p) * |g j| * qp p ^ j) : |Gg p g| ≤ Sg p g := by
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  rw [← Real.norm_eq_abs]
  refine tsum_of_norm_bounded hS.hasSum (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((p : ℝ)⁻¹) ^ j)]
  have h1 := xpow_le_qpow hp j
  have : 0 ≤ (j : ℝ) * Real.log p := by positivity
  have hq := pow_pos (qp_pos hp) j
  have hh : 0 ≤ (j : ℝ) * Real.log p * |g j| * qp p ^ j := by positivity
  have h3 := mul_le_mul_of_nonneg_left h1 (abs_nonneg (g j))
  linarith

lemma abs_G1g_le {p : ℕ} (hp : 2 ≤ p) {g : ℕ → ℝ}
    (hS : Summable fun j : ℕ => (1 + j * Real.log p) * |g j| * qp p ^ j) : |G1g p g| ≤ Sg p g := by
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  rw [← Real.norm_eq_abs]
  refine tsum_of_norm_bounded hS.hasSum (fun j => ?_)
  have hjl : 0 ≤ (j : ℝ) * Real.log p := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hjl,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ((p : ℝ)⁻¹) ^ j)]
  have h1 := xpow_le_qpow hp j
  have := abs_nonneg (g j)
  have := pow_pos (qp_pos hp) j
  have h2 : (j : ℝ) * Real.log p * |g j| * ((p : ℝ)⁻¹) ^ j ≤ (j : ℝ) * Real.log p * |g j| * qp p ^ j :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith [mul_nonneg (abs_nonneg (g j)) this.le]

lemma Sg_nonneg (p : ℕ) (hp : 2 ≤ p) (g : ℕ → ℝ) : 0 ≤ Sg p g := by
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  exact tsum_nonneg fun j => by have := qp_pos hp; positivity

/-- **One-prime peeling.** -/
theorem peel_asymp {p : ℕ} (hp : 2 ≤ p) {g F : ℕ → ℝ} {c K E : ℝ} (hE : 0 ≤ E)
    (hF : ∀ N : ℕ, 1 ≤ N → |Asum F N - c * Real.log N - K| ≤ E * (N : ℝ) ^ (-(1 / 5 : ℝ)))
    (hS : Summable fun j : ℕ => (1 + j * Real.log p) * |g j| * qp p ^ j) (N : ℕ) (hN : 1 ≤ N) :
    |Asum (conv p g F) N - c * Gg p g * Real.log N - (K * Gg p g - c * G1g p g)| ≤
      (2 * E + 3 * |c| + |K|) * Sg p g * (N : ℝ) ^ (-(1 / 5 : ℝ)) := by
  set x : ℝ := (p : ℝ)⁻¹ with hx
  set a : ℕ → ℝ := fun j => g j * x ^ j * Asum F (N / p ^ j) with ha
  have hsupp : ∀ j ∉ range (N + 1), a j = 0 := by
    intro j hj
    rw [mem_range, not_lt] at hj
    have : N < p ^ j := lt_of_lt_of_le (by omega) (Nat.lt_pow_self (by omega : 1 < p)).le
    simp only [ha, Nat.div_eq_of_lt this, Asum_zero, mul_zero]
  have hA : Asum (conv p g F) N = ∑' j, a j := by
    rw [Asum_conv hp, tsum_eq_sum (s := range (N + 1)) (fun j hj => hsupp j hj)]
  have has : Summable a := summable_of_ne_finset_zero (s := range (N + 1)) (fun j hj => hsupp j hj)
  have hG := summable_G hp hS
  have hG1 := summable_G1 hp hS
  set Δ : ℕ → ℝ := fun j => g j * x ^ j * (Asum F (N / p ^ j) - c * (Real.log N - j * Real.log p) - K)
    with hΔ
  have hΔeq : ∀ j, Δ j = a j - (c * Real.log N + K) * (g j * x ^ j) + c * (j * Real.log p * g j * x ^ j) := by
    intro j; simp only [hΔ, ha]; ring
  have hΔs : Summable Δ := by
    have := (has.sub (hG.mul_left (c * Real.log N + K))).add (hG1.mul_left c)
    exact this.congr (fun j => (hΔeq j).symm)
  have hsum : ∑' j, Δ j = Asum (conv p g F) N - c * Gg p g * Real.log N - (K * Gg p g - c * G1g p g) := by
    rw [tsum_congr hΔeq, Summable.tsum_add (has.sub (hG.mul_left _)) (hG1.mul_left c),
      Summable.tsum_sub has (hG.mul_left _),
      tsum_mul_left, tsum_mul_left, ← hA]
    unfold Gg G1g; rw [← hx]; ring
  rw [← hsum, ← Real.norm_eq_abs]
  have hb : ∀ j, ‖Δ j‖ ≤ (2 * E + 3 * |c| + |K|) * (N : ℝ) ^ (-(1 / 5 : ℝ)) *
      ((1 + j * Real.log p) * |g j| * qp p ^ j) := fun j => by
    rw [Real.norm_eq_abs]; exact term_le hp hE hF (g j) hN j
  refine (tsum_of_norm_bounded (hS.hasSum.mul_left _) hb).trans (le_of_eq ?_)
  unfold Sg; ring

end RamanujanTau.HafnerBridge2
