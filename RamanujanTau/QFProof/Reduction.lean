/-
# `QFHyp` from a common-divisor diagonalization, a two-variable factorization and Euler bounds

Let `K(h,k) = ρ(h₁)ρ(k₁)/[h,k]` (`Kq`) and `K₁` the companion kernel of `Q¹` (`Kq1`).  Suppose

* (`QDecomp`) `K(h,k) = Σ_{d|h} W(d) U(h,d) U(k,d)`, with `U(h,d) = 0` unless `d | h`;
* (`QDecomp1`) `K₁(h,k) = Σ_{d|h} [W₁(d) U(h,d)U(k,d) + W(d)(V(h,d)U(k,d) + U(h,d)V(k,d))]`;
* (`QFactor`) `α(n₁)α(n₂)U(n₁n₂,d) = Σ_{u₁|n₁,u₂|n₂} Γ_d(u₁,u₂) F(n₁/u₁) F(n₂/u₂)` with `F = fR/n`
  (and the same for `V` with `Γ'`);
* (`QEuler`) `Σ_{d≤y²} |W(d)| M_d(y)² ≪ (log y)^j`, `M_d(y) = Σ_{u₁,u₂≤y} |Γ_d(u₁,u₂)|`
  (`j = 1` for `(W,Γ)`, `j = 2` for `(W₁,Γ)`, `j = 3` for `(W,Γ')`).

Then `Q⁰(y) = Σ_d W(d) y_d²` with `y_d = (log y)^{−2} Σ_{u₁,u₂≤y} Γ_d(u₁,u₂) J(y/u₁) J(y/u₂)`
(`J = Isum fR`, exact), so by `J_bound` `|y_d| ≤ K²(1+log y)(log y)^{−2} M_d(y)`, whence
`Q⁰ ≪ 1/log y` and `Q¹ ≪ 1`: **`QFHyp`** (`qfHyp_of`).

The hypotheses are exact identities (`QDecomp*`, `QFactor`) and non-negative Euler-product size
bounds (`QEuler`); none mentions `y`-dependent cancellation.  The cancellation is entirely in
`J_bound` (level 1).
-/
import RamanujanTau.QFProof.Comb
import RamanujanTau.HafnerBridge.QF

set_option autoImplicit false

namespace RamanujanTau.QFProof

open Finset
open RamanujanTau.SelbergDelange2 (Isum)
open RamanujanTau.SelbergDelange3 (fR)
open RamanujanTau.HafnerBridge
open RamanujanTau.SelbergCoeffs (alpha)
open RamanujanTau.HafnerMV2 (βSel)

/-- The kernel of `Q⁰`. -/
noncomputable def Kq (h k : ℕ) : ℝ :=
  rho (h / Nat.gcd h k) * rho (k / Nat.gcd h k) / (Nat.lcm h k : ℝ)

/-- The kernel of `Q¹`. -/
noncomputable def Kq1 (h k : ℕ) : ℝ :=
  (rho (h / Nat.gcd h k) * rho (k / Nat.gcd h k) *
      (gamR - 1 / 2 * Real.log ((h / Nat.gcd h k * (k / Nat.gcd h k) : ℕ) : ℝ)) +
    rho1 (h / Nat.gcd h k) * rho (k / Nat.gcd h k) + rho (h / Nat.gcd h k) * rho1 (k / Nat.gcd h k)) /
    (Nat.lcm h k : ℝ)

/-- Common-divisor diagonalization of `Kq`. -/
def QDecomp (W : ℕ → ℝ) (U : ℕ → ℕ → ℝ) : Prop :=
  (∀ h d, ¬ d ∣ h → U h d = 0) ∧
    ∀ h k, 0 < h → 0 < k → Kq h k = ∑ d ∈ h.divisors, W d * U h d * U k d

/-- The derivative (companion) decomposition of `Kq1`. -/
def QDecomp1 (W W₁ : ℕ → ℝ) (U V : ℕ → ℕ → ℝ) : Prop :=
  (∀ h d, ¬ d ∣ h → V h d = 0) ∧
    ∀ h k, 0 < h → 0 < k → Kq1 h k =
      ∑ d ∈ h.divisors, (W₁ d * U h d * U k d + W d * (V h d * U k d + U h d * V k d))

/-- Two-variable factorization through `F = fR/n`. -/
def QFactor (U : ℕ → ℕ → ℝ) (Γ : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ d n₁ n₂, 0 < n₁ → 0 < n₂ → alpha n₁ * alpha n₂ * U (n₁ * n₂) d =
    ∑ u₁ ∈ n₁.divisors, ∑ u₂ ∈ n₂.divisors, Γ d u₁ u₂ * Fm (n₁ / u₁) * Fm (n₂ / u₂)

/-- `M_d(y) = Σ_{u₁,u₂≤y} |Γ_d(u₁,u₂)|`. -/
noncomputable def Mass (Γ : ℕ → ℕ → ℕ → ℝ) (y d : ℕ) : ℝ :=
  ∑ u₁ ∈ Ioc 0 y, ∑ u₂ ∈ Ioc 0 y, |Γ d u₁ u₂|

/-- The Euler-product size bound `Σ_{d≤y²} |W(d)| M_d(y)² ≪ (log y)^j`. -/
def QEuler (W : ℕ → ℝ) (Γ : ℕ → ℕ → ℕ → ℝ) (j : ℕ) : Prop :=
  ∃ A : ℝ, ∀ y : ℕ, 3 ≤ y → ∑ d ∈ Icc 1 (y ^ 2), |W d| * Mass Γ y d ^ 2 ≤ A * Real.log y ^ j

/-- `y_d = Σ_{h≤y²} c(h) U(h,d)`. -/
noncomputable def yv (y : ℕ) (U : ℕ → ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ h ∈ Icc 1 (y ^ 2), cS y h * U h d

lemma Icc_one_eq (N : ℕ) : Icc 1 N = Ioc 0 N := by
  ext a; simp only [mem_Icc, mem_Ioc]; omega

lemma βSel_out {y n : ℕ} (h : ¬ (1 ≤ n ∧ n ≤ y)) : βSel y n = 0 := by
  unfold βSel; rw [if_neg h]

lemma βSel_in {y n : ℕ} (hy : 1 < y) (hn : n ∈ Ioc 0 y) :
    βSel y n = alpha n * (Real.log ((y : ℝ) / n) / Real.log y) := by
  have h1 := mem_Ioc.1 hn
  unfold βSel
  rw [if_pos ⟨h1.1, h1.2⟩]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h1.1
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (lt_of_lt_of_le h1.1 h1.2)
  rw [Real.log_div hy0.ne' hn0.ne']
  have hl : Real.log y ≠ 0 := (Real.log_pos (by exact_mod_cast hy)).ne'
  field_simp

/-- `y_d` as a double sum over `n₁, n₂ ≤ y`. -/
lemma yv_eq (y : ℕ) (U : ℕ → ℕ → ℝ) (d : ℕ) :
    yv y U d = ∑ n₁ ∈ Ioc 0 y, ∑ n₂ ∈ Ioc 0 y, βSel y n₁ * βSel y n₂ * U (n₁ * n₂) d := by
  unfold yv
  rw [Icc_one_eq]
  have h1 : ∀ h ∈ Ioc 0 (y ^ 2), cS y h * U h d =
      ∑ x ∈ h.divisorsAntidiagonal, βSel y x.1 * βSel y x.2 * U (x.1 * x.2) d := by
    intro h _
    unfold cS
    rw [← Nat.sum_divisorsAntidiagonal (fun i j => βSel y i * βSel y j), sum_mul]
    refine sum_congr rfl fun x hx => ?_
    rw [(Nat.mem_divisorsAntidiagonal.1 hx).1]
  rw [sum_congr rfl h1, sum_antidiag_reindex (fun a b => βSel y a * βSel y b * U (a * b) d)]
  have hsub : Ioc 0 y ⊆ Ioc 0 (y ^ 2) := by
    intro n hn
    have := mem_Ioc.1 hn
    refine mem_Ioc.2 ⟨this.1, this.2.trans ?_⟩
    rcases Nat.eq_zero_or_pos y with h0 | h0
    · simp [h0]
    · nlinarith
  symm
  rw [← sum_subset hsub ?_]
  · refine sum_congr rfl fun n₁ hn₁ => ?_
    have h1 := mem_Ioc.1 hn₁
    have hs2 : Ioc 0 y ⊆ Ioc 0 (y ^ 2 / n₁) := by
      refine Ioc_subset_Ioc_right ?_
      rw [Nat.le_div_iff_mul_le h1.1, pow_two]
      exact Nat.mul_le_mul_left y h1.2
    refine sum_subset hs2 fun n₂ hn₂ hn₂' => ?_
    have : ¬ (1 ≤ n₂ ∧ n₂ ≤ y) := fun h => hn₂' (mem_Ioc.2 ⟨h.1, h.2⟩)
    rw [βSel_out this]; ring
  · intro n₁ _ hn₁
    have : ¬ (1 ≤ n₁ ∧ n₁ ≤ y) := fun h => hn₁ (mem_Ioc.2 ⟨h.1, h.2⟩)
    refine sum_eq_zero fun n₂ _ => ?_
    rw [βSel_out this]; ring

/-- **Exact formula**: `y_d = (log y)^{−2} Σ_{u₁,u₂≤y} Γ_d(u₁,u₂) J(y/u₁) J(y/u₂)`. -/
lemma yv_smooth {U : ℕ → ℕ → ℝ} {Γ : ℕ → ℕ → ℕ → ℝ} (hF : QFactor U Γ) {y : ℕ} (hy : 1 < y) (d : ℕ) :
    yv y U d = (∑ u₁ ∈ Ioc 0 y, ∑ u₂ ∈ Ioc 0 y,
      Γ d u₁ u₂ * Isum fR ((y : ℝ) / u₁) * Isum fR ((y : ℝ) / u₂)) / Real.log y ^ 2 := by
  rw [yv_eq, ← smooth_two y (Γ d), sum_div]
  refine sum_congr rfl fun n₁ hn₁ => ?_
  rw [sum_div]
  refine sum_congr rfl fun n₂ hn₂ => ?_
  rw [βSel_in hy hn₁, βSel_in hy hn₂, ← hF d n₁ n₂ (mem_Ioc.1 hn₁).1 (mem_Ioc.1 hn₂).1]
  ring

/-- `|y_d| ≤ K²(1 + log y)(log y)^{−2} M_d(y)`. -/
lemma abs_yv_le {U : ℕ → ℕ → ℝ} {Γ : ℕ → ℕ → ℕ → ℝ} (hF : QFactor U Γ) {K : ℝ} (hK : 0 ≤ K)
    (hJ : ∀ x : ℝ, 1 ≤ x → |Isum fR x| ≤ K * (1 + Real.log x) ^ (1 / 2 : ℝ)) {y : ℕ} (hy : 1 < y)
    (d : ℕ) :
    |yv y U d| ≤ K ^ 2 * (1 + Real.log y) / Real.log y ^ 2 * Mass Γ y d := by
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy.le
  have hL0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hJu : ∀ u ∈ Ioc 0 y, |Isum fR ((y : ℝ) / u)| ≤ K * (1 + Real.log y) ^ (1 / 2 : ℝ) := by
    intro u hu
    have h1 := mem_Ioc.1 hu
    have hu0 : (0 : ℝ) < u := by exact_mod_cast h1.1
    have hyu : (u : ℝ) ≤ y := by exact_mod_cast h1.2
    have hx1 : 1 ≤ (y : ℝ) / u := by rw [le_div_iff₀ hu0]; linarith
    refine (hJ _ hx1).trans ?_
    have hl : Real.log ((y : ℝ) / u) ≤ Real.log y :=
      Real.log_le_log (by linarith) (div_le_self (by linarith) (by exact_mod_cast h1.1))
    have hl0 : 0 ≤ Real.log ((y : ℝ) / u) := Real.log_nonneg hx1
    gcongr
  have hsq : (1 + Real.log y) ^ (1 / 2 : ℝ) * (1 + Real.log y) ^ (1 / 2 : ℝ) = 1 + Real.log y := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have hp : 0 ≤ (1 + Real.log y) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have key : |∑ u₁ ∈ Ioc 0 y, ∑ u₂ ∈ Ioc 0 y,
      Γ d u₁ u₂ * Isum fR ((y : ℝ) / u₁) * Isum fR ((y : ℝ) / u₂)| ≤
      K ^ 2 * (1 + Real.log y) * Mass Γ y d := by
    rw [Mass, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun u₁ hu₁ => ?_)
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun u₂ hu₂ => ?_)
    rw [abs_mul, abs_mul]
    calc |Γ d u₁ u₂| * |Isum fR ((y : ℝ) / u₁)| * |Isum fR ((y : ℝ) / u₂)|
        ≤ |Γ d u₁ u₂| * (K * (1 + Real.log y) ^ (1 / 2 : ℝ)) *
            (K * (1 + Real.log y) ^ (1 / 2 : ℝ)) := by
          gcongr
          · exact hJu u₁ hu₁
          · exact hJu u₂ hu₂
      _ = K ^ 2 * ((1 + Real.log y) ^ (1 / 2 : ℝ) * (1 + Real.log y) ^ (1 / 2 : ℝ)) *
            |Γ d u₁ u₂| := by ring
      _ = K ^ 2 * (1 + Real.log y) * |Γ d u₁ u₂| := by rw [hsq]
  rw [yv_smooth hF hy, abs_div, abs_of_nonneg (sq_nonneg (Real.log (y : ℝ)))]
  calc _ ≤ K ^ 2 * (1 + Real.log y) * Mass Γ y d / Real.log y ^ 2 :=
        div_le_div_of_nonneg_right key (sq_nonneg _)
    _ = _ := by ring

/-- Bilinear rearrangement. -/
lemma bilin (S D : Finset ℕ) (x c : ℕ → ℝ) (f g : ℕ → ℕ → ℝ) :
    ∑ h ∈ S, ∑ k ∈ S, x h * x k * ∑ d ∈ D, c d * f h d * g k d =
      ∑ d ∈ D, c d * (∑ h ∈ S, x h * f h d) * (∑ k ∈ S, x k * g k d) := by
  have e : ∀ h k, x h * x k * ∑ d ∈ D, c d * f h d * g k d =
      ∑ d ∈ D, c d * (x h * f h d) * (x k * g k d) := by
    intro h k; rw [mul_sum]; exact sum_congr rfl fun d _ => by ring
  simp_rw [e]
  rw [sum_congr rfl fun h _ => (sum_comm : ∑ k ∈ S, ∑ d ∈ D, c d * (x h * f h d) * (x k * g k d) =
    ∑ d ∈ D, ∑ k ∈ S, c d * (x h * f h d) * (x k * g k d))]
  rw [sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [mul_assoc, sum_mul_sum, mul_sum]
  exact sum_congr rfl fun h _ => by rw [mul_sum]; exact sum_congr rfl fun k _ => by ring

lemma divisors_sub {h N : ℕ} (hh : h ∈ Icc 1 N) : h.divisors ⊆ Icc 1 N := by
  intro d hd
  have h1 := mem_Icc.1 hh
  have hd' := Nat.mem_divisors.1 hd
  have := Nat.le_of_dvd (by omega) hd'.1
  have := Nat.pos_of_dvd_of_pos hd'.1 (by omega)
  exact mem_Icc.2 ⟨by omega, by omega⟩

/-- **`Q⁰ = Σ_d W(d) y_d²`.** -/
lemma Q0_diag {W : ℕ → ℝ} {U : ℕ → ℕ → ℝ} (hD : QDecomp W U) (y : ℕ) :
    Q0 y = ∑ d ∈ Icc 1 (y ^ 2), W d * yv y U d ^ 2 := by
  have hK : ∀ h ∈ Icc 1 (y ^ 2), ∀ k ∈ Icc 1 (y ^ 2), cS y h * cS y k / (Nat.lcm h k : ℝ) *
      (rho (h / Nat.gcd h k) * rho (k / Nat.gcd h k)) =
      cS y h * cS y k * ∑ d ∈ Icc 1 (y ^ 2), W d * U h d * U k d := by
    intro h hh k hk
    have e : cS y h * cS y k / (Nat.lcm h k : ℝ) * (rho (h / Nat.gcd h k) * rho (k / Nat.gcd h k)) =
        cS y h * cS y k * Kq h k := by unfold Kq; ring
    rw [e, hD.2 h k (by have := (mem_Icc.1 hh).1; omega) (by have := (mem_Icc.1 hk).1; omega)]
    congr 1
    refine sum_subset (divisors_sub hh) fun d _ hd => ?_
    have hh0 : h ≠ 0 := by have := (mem_Icc.1 hh).1; omega
    have : ¬ d ∣ h := fun hdv => hd (Nat.mem_divisors.2 ⟨hdv, hh0⟩)
    rw [hD.1 h d this]; ring
  unfold Q0
  rw [sum_congr rfl fun h hh => sum_congr rfl fun k hk => hK h hh k hk, bilin]
  refine sum_congr rfl fun d _ => ?_
  unfold yv; ring

/-- **`Q¹ = Σ_d [W₁(d) y_d² + 2 W(d) y_d z_d]`.** -/
lemma Q1_diag {W W₁ : ℕ → ℝ} {U V : ℕ → ℕ → ℝ} (hD : QDecomp W U) (hD1 : QDecomp1 W W₁ U V) (y : ℕ) :
    Q1 y = ∑ d ∈ Icc 1 (y ^ 2), (W₁ d * yv y U d ^ 2 + 2 * W d * yv y U d * yv y V d) := by
  have hK : ∀ h ∈ Icc 1 (y ^ 2), ∀ k ∈ Icc 1 (y ^ 2), cS y h * cS y k / (Nat.lcm h k : ℝ) *
      (rho (h / Nat.gcd h k) * rho (k / Nat.gcd h k) *
          (gamR - 1 / 2 * Real.log ((h / Nat.gcd h k * (k / Nat.gcd h k) : ℕ) : ℝ)) +
        rho1 (h / Nat.gcd h k) * rho (k / Nat.gcd h k) + rho (h / Nat.gcd h k) * rho1 (k / Nat.gcd h k)) =
      cS y h * cS y k * ∑ d ∈ Icc 1 (y ^ 2), W₁ d * U h d * U k d +
      cS y h * cS y k * ∑ d ∈ Icc 1 (y ^ 2), W d * V h d * U k d +
      cS y h * cS y k * ∑ d ∈ Icc 1 (y ^ 2), W d * U h d * V k d := by
    intro h hh k hk
    have e : cS y h * cS y k / (Nat.lcm h k : ℝ) *
      (rho (h / Nat.gcd h k) * rho (k / Nat.gcd h k) *
          (gamR - 1 / 2 * Real.log ((h / Nat.gcd h k * (k / Nat.gcd h k) : ℕ) : ℝ)) +
        rho1 (h / Nat.gcd h k) * rho (k / Nat.gcd h k) + rho (h / Nat.gcd h k) * rho1 (k / Nat.gcd h k)) =
        cS y h * cS y k * Kq1 h k := by unfold Kq1; ring
    rw [e, hD1.2 h k (by have := (mem_Icc.1 hh).1; omega) (by have := (mem_Icc.1 hk).1; omega)]
    have hh0 : h ≠ 0 := by have := (mem_Icc.1 hh).1; omega
    have hsub := divisors_sub hh
    have hext : ∀ (φ : ℕ → ℝ), (∀ d, ¬ d ∣ h → φ d = 0) →
        ∑ d ∈ h.divisors, φ d = ∑ d ∈ Icc 1 (y ^ 2), φ d := fun φ hφ =>
      sum_subset hsub fun d _ hd => hφ d fun hdv => hd (Nat.mem_divisors.2 ⟨hdv, hh0⟩)
    rw [hext (fun d => W₁ d * U h d * U k d + W d * (V h d * U k d + U h d * V k d))
      (fun d hd => by simp only [hD.1 h d hd, hD1.1 h d hd]; ring)]
    rw [← mul_add, ← mul_add, ← sum_add_distrib, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun d _ => ?_
    ring
  unfold Q1
  rw [sum_congr rfl fun h hh => sum_congr rfl fun k hk => hK h hh k hk]
  conv_lhs => simp only [sum_add_distrib]; rw [bilin, bilin, bilin]
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun d _ => ?_
  unfold yv; ring

lemma log_three_gt_one : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9; linarith

lemma one_le_log {y : ℕ} (hy : 3 ≤ y) : 1 ≤ Real.log y := by
  have : Real.log 3 ≤ Real.log y := Real.log_le_log (by norm_num) (by exact_mod_cast hy)
  linarith [log_three_gt_one]

/-- `c(y) = K²(1+L)/L² ≤ 2K²/L` for `L ≥ 1`. -/
lemma cfac_le {K L : ℝ} (hL : 1 ≤ L) : K ^ 2 * (1 + L) / L ^ 2 ≤ 2 * K ^ 2 / L := by
  have hL0 : 0 < L := by linarith
  rw [div_le_div_iff₀ (by positivity) hL0]
  have := mul_le_mul_of_nonneg_left (show 1 + L ≤ 2 * L by linarith)
    (by positivity : 0 ≤ K ^ 2 * L)
  nlinarith

/-- **`Q⁰ ≪ 1/log y`** from the three hypotheses. -/
theorem Q0_bound_of {W : ℕ → ℝ} {U : ℕ → ℕ → ℝ} {Γ : ℕ → ℕ → ℕ → ℝ}
    (hD : QDecomp W U) (hF : QFactor U Γ) (hE : QEuler W Γ 1) :
    ∃ B : ℝ, ∀ y : ℕ, 3 ≤ y → |Q0 y| ≤ B / Real.log y := by
  obtain ⟨K, hK, hJ⟩ := J_bound
  obtain ⟨A, hA⟩ := hE
  refine ⟨4 * K ^ 4 * |A|, fun y hy => ?_⟩
  have hL := one_le_log hy
  have hL0 : 0 < Real.log y := by linarith
  set c : ℝ := K ^ 2 * (1 + Real.log y) / Real.log y ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hcle : c ≤ 2 * K ^ 2 / Real.log y := cfac_le hL
  have hyv : ∀ d, yv y U d ^ 2 ≤ c ^ 2 * Mass Γ y d ^ 2 := by
    intro d
    have h := abs_yv_le hF hK hJ (y := y) (by omega) d
    rw [← sq_abs, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [Q0_diag hD]
  calc |∑ d ∈ Icc 1 (y ^ 2), W d * yv y U d ^ 2|
      ≤ ∑ d ∈ Icc 1 (y ^ 2), |W d| * (c ^ 2 * Mass Γ y d ^ 2) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => ?_)
        rw [abs_mul, abs_of_nonneg (sq_nonneg (yv y U d))]
        exact mul_le_mul_of_nonneg_left (hyv d) (abs_nonneg _)
    _ = c ^ 2 * ∑ d ∈ Icc 1 (y ^ 2), |W d| * Mass Γ y d ^ 2 := by
        rw [mul_sum]; refine sum_congr rfl fun d _ => ?_; ring
    _ ≤ c ^ 2 * (|A| * Real.log y) := by
        gcongr
        refine (hA y hy).trans ?_
        rw [pow_one]; gcongr; exact le_abs_self A
    _ ≤ (2 * K ^ 2 / Real.log y) ^ 2 * (|A| * Real.log y) := by gcongr
    _ = 4 * K ^ 4 * |A| / Real.log y := by field_simp; ring

/-- **`Q¹ ≪ 1`** from the hypotheses. -/
theorem Q1_bound_of {W W₁ : ℕ → ℝ} {U V : ℕ → ℕ → ℝ} {Γ Γ' : ℕ → ℕ → ℕ → ℝ}
    (hD : QDecomp W U) (hD1 : QDecomp1 W W₁ U V) (hF : QFactor U Γ) (hF1 : QFactor V Γ')
    (hE : QEuler W Γ 1) (hE1 : QEuler W₁ Γ 2) (hE2 : QEuler W Γ' 3) :
    ∃ B : ℝ, ∀ y : ℕ, 3 ≤ y → |Q1 y| ≤ B := by
  obtain ⟨K, hK, hJ⟩ := J_bound
  obtain ⟨A₀, hA₀⟩ := hE
  obtain ⟨A₁, hA₁⟩ := hE1
  obtain ⟨A₂, hA₂⟩ := hE2
  refine ⟨4 * K ^ 4 * (|A₀| + |A₁| + |A₂|), fun y hy => ?_⟩
  have hL := one_le_log hy
  set L := Real.log y with hLdef
  have hL0 : 0 < L := by linarith
  set c : ℝ := K ^ 2 * (1 + L) / L ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hcle : c ≤ 2 * K ^ 2 / L := cfac_le hL
  have hy1 := fun d => abs_yv_le hF hK hJ (show 1 < y by omega) d
  have hy2 := fun d => abs_yv_le hF1 hK hJ (show 1 < y by omega) d
  have hM0 : ∀ d, 0 ≤ Mass Γ y d := fun d => sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  have hM1 : ∀ d, 0 ≤ Mass Γ' y d := fun d => sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  have hterm : ∀ d, |W₁ d * yv y U d ^ 2 + 2 * W d * yv y U d * yv y V d| ≤
      c ^ 2 * (|W₁ d| * Mass Γ y d ^ 2 +
        |W d| * (L * Mass Γ y d ^ 2 + Mass Γ' y d ^ 2 / L)) := by
    intro d
    have a1 : |yv y U d| ≤ c * Mass Γ y d := hy1 d
    have a2 : |yv y V d| ≤ c * Mass Γ' y d := hy2 d
    have amgm : 2 * (Mass Γ y d * Mass Γ' y d) ≤ L * Mass Γ y d ^ 2 + Mass Γ' y d ^ 2 / L := by
      have : 0 ≤ (L * Mass Γ y d - Mass Γ' y d) ^ 2 / L := by positivity
      have e : (L * Mass Γ y d - Mass Γ' y d) ^ 2 / L =
          L * Mass Γ y d ^ 2 + Mass Γ' y d ^ 2 / L - 2 * (Mass Γ y d * Mass Γ' y d) := by
        field_simp; ring
      linarith
    have b1 : |W₁ d * yv y U d ^ 2| ≤ |W₁ d| * (c ^ 2 * Mass Γ y d ^ 2) := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg (yv y U d))]
      gcongr
      rw [← sq_abs, ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) a1 2
    have b2 : |2 * W d * yv y U d * yv y V d| ≤ |W d| * (c ^ 2 * (2 * (Mass Γ y d * Mass Γ' y d))) := by
      rw [abs_mul, abs_mul, abs_mul]
      have : |(2 : ℝ)| = 2 := by norm_num
      rw [this]
      have p1 : 0 ≤ c * Mass Γ y d := mul_nonneg hc0 (hM0 d)
      calc 2 * |W d| * |yv y U d| * |yv y V d| ≤ 2 * |W d| * (c * Mass Γ y d) * (c * Mass Γ' y d) := by
            gcongr
        _ = |W d| * (c ^ 2 * (2 * (Mass Γ y d * Mass Γ' y d))) := by ring
    calc _ ≤ |W₁ d * yv y U d ^ 2| + |2 * W d * yv y U d * yv y V d| := abs_add_le _ _
      _ ≤ |W₁ d| * (c ^ 2 * Mass Γ y d ^ 2) + |W d| * (c ^ 2 * (2 * (Mass Γ y d * Mass Γ' y d))) :=
          add_le_add b1 b2
      _ ≤ |W₁ d| * (c ^ 2 * Mass Γ y d ^ 2) +
            |W d| * (c ^ 2 * (L * Mass Γ y d ^ 2 + Mass Γ' y d ^ 2 / L)) := by gcongr
      _ = _ := by ring
  rw [Q1_diag hD hD1]
  have S0 := hA₀ y hy
  have S1 := hA₁ y hy
  have S2 := hA₂ y hy
  rw [← hLdef] at S0 S1 S2
  have hsum : ∑ d ∈ Icc 1 (y ^ 2), (|W₁ d| * Mass Γ y d ^ 2 +
        |W d| * (L * Mass Γ y d ^ 2 + Mass Γ' y d ^ 2 / L)) =
      (∑ d ∈ Icc 1 (y ^ 2), |W₁ d| * Mass Γ y d ^ 2) +
        L * (∑ d ∈ Icc 1 (y ^ 2), |W d| * Mass Γ y d ^ 2) +
        (∑ d ∈ Icc 1 (y ^ 2), |W d| * Mass Γ' y d ^ 2) / L := by
    rw [mul_sum, sum_div, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun d _ => ?_
    ring
  have hbig : (∑ d ∈ Icc 1 (y ^ 2), |W₁ d| * Mass Γ y d ^ 2) +
        L * (∑ d ∈ Icc 1 (y ^ 2), |W d| * Mass Γ y d ^ 2) +
        (∑ d ∈ Icc 1 (y ^ 2), |W d| * Mass Γ' y d ^ 2) / L ≤ (|A₀| + |A₁| + |A₂|) * L ^ 2 := by
    have t1 : A₁ * L ^ 2 ≤ |A₁| * L ^ 2 := by gcongr; exact le_abs_self _
    have t0 : L * (∑ d ∈ Icc 1 (y ^ 2), |W d| * Mass Γ y d ^ 2) ≤ |A₀| * L ^ 2 := by
      calc _ ≤ L * (A₀ * L ^ 1) := by gcongr
        _ ≤ L * (|A₀| * L) := by rw [pow_one]; gcongr; exact le_abs_self _
        _ = |A₀| * L ^ 2 := by ring
    have t2 : (∑ d ∈ Icc 1 (y ^ 2), |W d| * Mass Γ' y d ^ 2) / L ≤ |A₂| * L ^ 2 := by
      rw [div_le_iff₀ hL0]
      calc _ ≤ A₂ * L ^ 3 := S2
        _ ≤ |A₂| * L ^ 3 := by gcongr; exact le_abs_self _
        _ = |A₂| * L ^ 2 * L := by ring
    linarith
  calc |∑ d ∈ Icc 1 (y ^ 2), (W₁ d * yv y U d ^ 2 + 2 * W d * yv y U d * yv y V d)|
      ≤ ∑ d ∈ Icc 1 (y ^ 2), c ^ 2 * (|W₁ d| * Mass Γ y d ^ 2 +
          |W d| * (L * Mass Γ y d ^ 2 + Mass Γ' y d ^ 2 / L)) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => hterm d)
    _ = c ^ 2 * ((∑ d ∈ Icc 1 (y ^ 2), |W₁ d| * Mass Γ y d ^ 2) +
        L * (∑ d ∈ Icc 1 (y ^ 2), |W d| * Mass Γ y d ^ 2) +
        (∑ d ∈ Icc 1 (y ^ 2), |W d| * Mass Γ' y d ^ 2) / L) := by rw [← mul_sum, hsum]
    _ ≤ (2 * K ^ 2 / L) ^ 2 * ((|A₀| + |A₁| + |A₂|) * L ^ 2) := by gcongr
    _ = 4 * K ^ 4 * (|A₀| + |A₁| + |A₂|) := by field_simp; ring

/-- **`QFHyp` from the diagonalization, factorization and Euler hypotheses.** -/
theorem qfHyp_of {W W₁ : ℕ → ℝ} {U V : ℕ → ℕ → ℝ} {Γ Γ' : ℕ → ℕ → ℕ → ℝ}
    (hD : QDecomp W U) (hD1 : QDecomp1 W W₁ U V) (hF : QFactor U Γ) (hF1 : QFactor V Γ')
    (hE : QEuler W Γ 1) (hE1 : QEuler W₁ Γ 2) (hE2 : QEuler W Γ' 3) : QFHyp := by
  obtain ⟨B₀, h₀⟩ := Q0_bound_of hD hF hE
  obtain ⟨B₁, h₁⟩ := Q1_bound_of hD hD1 hF hF1 hE hE1 hE2
  refine ⟨max B₀ B₁, 3, fun y hy => ?_⟩
  have hy' : 3 ≤ y := by exact_mod_cast hy
  have hL := one_le_log hy'
  refine ⟨(h₀ y hy').trans ?_, (h₁ y hy').trans (le_max_right _ _)⟩
  gcongr
  exact le_max_left _ _

end RamanujanTau.QFProof
