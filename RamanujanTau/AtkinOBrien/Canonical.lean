/-
# The canonical subgroup of a formal group (Katz 3.10.7 / Lubin), abstractly

Let `F` be a commutative formal group over a ring `R` with `ι : R → K` into an ultrametric normed field and
`‖ι r‖ ≤ 1`. Put `ε = ‖p‖`, `α = ‖a‖` (`a` = coefficient of `T^p` in `[p]`), and suppose the coefficient
of `T^{p²}` has norm `1` (height `≤ 2`) and the break condition `ε^p < α^{p+1}` holds (`v < p/(p+1)`).
If `[p](T)/T = P(T)·U(T)` with `P = ∏ (X − rᵢ)` split of degree `p² − 1` and `U` a unit (Weierstrass
preparation), then **exactly `p − 1` of the `rᵢ` are small, and their norms multiply to `ε/α`**. That is, the
nonzero canonical points have total valuation `1 − v`.

Inputs proved in this repository:
* `FGL.p_dvd_coeff_nmul` and `FGL.mem_ideal_coeff_nmul` give the shape of `[p]`;
* `Newton.dominant` gives the root count;
* `dominance_transfer` (below) passes from `P·U` to `P`.
-/
import RamanujanTau.AtkinOBrien.Newton
import RamanujanTau.FormalGroupLayer.HeightTwo

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace FGL
open MvPowerSeries

variable {R : Type*} [CommRing R] (F : FormalGroup R)

/-- `[n](T) = nT + O(T²)`. -/
lemma coeff_one_nmul (n : ℕ) : coeff (Finsupp.single () 1) (nmul F n) = n := by
  have key : ∀ f : MvPowerSeries Unit R, coeff (Finsupp.single () 1) f = constantCoeff (pd () f) := by
    intro f; rw [← coeff_zero_eq_constantCoeff_apply, coeff_pd, zero_add]; simp
  induction n with
  | zero => simp [nmul]
  | succ n ih =>
    show coeff _ (ev F T (nmul F n)) = _
    rw [key, pd_ev F _ _ cc_T (cc_nmul F n), pd_X', if_pos rfl, mul_one, map_add, map_mul,
      cc_subst _ (cc_vec2 cc_T (cc_nmul F n)), cc_subst _ (cc_vec2 cc_T (cc_nmul F n)), ← key, ih]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pd, ← coeff_zero_eq_constantCoeff_apply, coeff_pd]
    simp [F.lin_coeff_X, F.lin_coeff_Y, add_comm]

end FGL

namespace AtkinOBrien.Canonical
open Polynomial Finset

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **dominance transfer** through a unit factor. If `h = P·U`, `‖U₀‖ = 1`, `‖U_k‖ρ^k < 1` for `k ≥ 1`,
and `h` has a strictly dominant term at `m` at radius `ρ`, then so does `P`, with `‖P_m‖ = ‖h_m‖` and
`‖P₀‖ = ‖h₀‖`. -/
theorem dominance_transfer (P : K[X]) (U : PowerSeries K) (ρ : ℝ) (hρ : 0 < ρ)
    (hU0 : ‖PowerSeries.constantCoeff U‖ = 1) (hU : ∀ k, 1 ≤ k → ‖PowerSeries.coeff k U‖ * ρ ^ k < 1)
    (m : ℕ) (hdom : ∀ k, k ≠ m → ‖PowerSeries.coeff k ((P : PowerSeries K) * U)‖ * ρ ^ k <
      ‖PowerSeries.coeff m ((P : PowerSeries K) * U)‖ * ρ ^ m) :
    (∀ j, j ≠ m → ‖P.coeff j‖ * ρ ^ j < ‖P.coeff m‖ * ρ ^ m) ∧
      ‖P.coeff m‖ = ‖PowerSeries.coeff m ((P : PowerSeries K) * U)‖ ∧
      ‖P.coeff 0‖ = ‖PowerSeries.coeff 0 ((P : PowerSeries K) * U)‖ := by
  set h := (P : PowerSeries K) * U with hh
  have hU0' : ‖PowerSeries.coeff 0 U‖ = 1 := by rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hUle : ∀ k, ‖PowerSeries.coeff k U‖ * ρ ^ k ≤ 1 := fun k => by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [pow_zero, mul_one, hU0']
    · exact (hU k hk).le
  -- `P ≠ 0`
  have hmpos : 0 < ‖PowerSeries.coeff m h‖ * ρ ^ m := by
    have := hdom (m + 1) (by omega)
    exact lt_of_le_of_lt (by positivity) this
  have hP0 : P ≠ 0 := by
    rintro rfl; simp [hh] at hmpos
  -- the maximum of `‖P_i‖ρ^i`
  set S := range (P.natDegree + 1)
  have hS : S.Nonempty := ⟨0, by simp [S]⟩
  set w : ℕ → ℝ := fun i => ‖P.coeff i‖ * ρ ^ i
  set Mx := S.sup' hS w
  have hle : ∀ i, w i ≤ Mx := fun i => by
    by_cases hi : i ∈ S
    · exact le_sup' w hi
    · have : P.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by simp [S] at hi; omega)
      simp only [w, this, norm_zero, zero_mul]
      exact le_trans (by positivity) (le_sup' w (mem_range.mpr (Nat.succ_pos _)))
  have hMx : 0 < Mx := by
    obtain ⟨i, hi⟩ : ∃ i, P.coeff i ≠ 0 := by
      by_contra hc; push_neg at hc; exact hP0 (Polynomial.ext fun i => by simp [hc i])
    exact lt_of_lt_of_le (by simp only [w]; positivity) (hle i)
  set J := S.filter fun i => w i = Mx
  have hJ : J.Nonempty := by
    obtain ⟨i, hi, hi'⟩ := exists_mem_eq_sup' hS w
    exact ⟨i, mem_filter.mpr ⟨hi, hi'.symm⟩⟩
  have hnotJ : ∀ i, i ∉ J → w i < Mx := fun i hi => by
    by_cases hiS : i ∈ S
    · exact lt_of_le_of_ne (hle i) fun e => hi (mem_filter.mpr ⟨hiS, e⟩)
    · have : P.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by simp [S] at hiS; omega)
      simp only [w, this, norm_zero, zero_mul]; exact hMx
  -- coefficient of the product
  have hcoeff : ∀ k, PowerSeries.coeff k h = ∑ x ∈ antidiagonal k, P.coeff x.1 * PowerSeries.coeff x.2 U := by
    intro k; rw [hh, PowerSeries.coeff_mul]
    exact sum_congr rfl fun x _ => by rw [Polynomial.coeff_coe]
  have hterm : ∀ x : ℕ × ℕ, ‖P.coeff x.1 * PowerSeries.coeff x.2 U‖ * ρ ^ (x.1 + x.2) =
      w x.1 * (‖PowerSeries.coeff x.2 U‖ * ρ ^ x.2) := fun x => by
    simp only [w, norm_mul, pow_add]; ring
  -- every scaled coefficient of `h` is at most `Mx`
  have hhle : ∀ k, ‖PowerSeries.coeff k h‖ * ρ ^ k ≤ Mx := fun k => by
    rw [hcoeff]
    rcases (antidiagonal k).eq_empty_or_nonempty with he | hne
    · rw [he, sum_empty, norm_zero, zero_mul]; exact hMx.le
    obtain ⟨x, hx, hxle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
      (fun x => P.coeff x.1 * PowerSeries.coeff x.2 U)
    have hk := mem_antidiagonal.mp hx
    calc _ ≤ ‖P.coeff x.1 * PowerSeries.coeff x.2 U‖ * ρ ^ k :=
          mul_le_mul_of_nonneg_right hxle (pow_nonneg hρ.le _)
      _ = w x.1 * (‖PowerSeries.coeff x.2 U‖ * ρ ^ x.2) := by rw [← hk, hterm]
      _ ≤ Mx * 1 := mul_le_mul (hle _) (hUle _) (by positivity) hMx.le
      _ = Mx := mul_one _
  -- value at an index `j` with a unique maximal term
  have hval : ∀ j, (∀ x ∈ antidiagonal j, x ≠ (j, 0) →
      ‖P.coeff x.1 * PowerSeries.coeff x.2 U‖ * ρ ^ j < Mx) → j ∈ J →
      ‖PowerSeries.coeff j h‖ * ρ ^ j = Mx := by
    intro j hlt hjJ
    have hjw : w j = Mx := (mem_filter.mp hjJ).2
    have hρj := pow_pos hρ j
    have hmain : ‖P.coeff j * PowerSeries.coeff 0 U‖ * ρ ^ j = Mx := by
      rw [norm_mul, hU0', mul_one]; exact hjw
    rw [hcoeff]
    have hpos : 0 < ‖P.coeff j * PowerSeries.coeff 0 U‖ := by
      rw [← mul_lt_mul_iff_left₀ hρj, zero_mul, hmain]; exact hMx
    rw [Newton.norm_sum_eq_of_unique_max _ _ (j, 0) (mem_antidiagonal.mpr (add_zero j)) hpos
      fun x hx hne => ?_, hmain]
    have := hlt x hx hne
    rw [← hmain] at this
    exact lt_of_mul_lt_mul_right this hρj.le
  -- the lowest and highest maximizers
  set jlo := J.min' hJ
  set jhi := J.max' hJ
  have hlo : ‖PowerSeries.coeff jlo h‖ * ρ ^ jlo = Mx := by
    refine hval jlo (fun x hx hne => ?_) (min'_mem J hJ)
    have hk := mem_antidiagonal.mp hx
    have hx1 : x.1 < jlo := by
      rcases Nat.lt_or_ge x.1 jlo with h1 | h1
      · exact h1
      · exfalso; apply hne; ext <;> simp <;> omega
    have hxJ : x.1 ∉ J := fun hm => absurd (min'_le J _ hm) (not_le.mpr hx1)
    rw [← hk, hterm]
    calc w x.1 * (‖PowerSeries.coeff x.2 U‖ * ρ ^ x.2) ≤ w x.1 * 1 :=
          mul_le_mul_of_nonneg_left (hUle _) (by simp only [w]; positivity)
      _ < Mx := by rw [mul_one]; exact hnotJ _ hxJ
  have hhi : ‖PowerSeries.coeff jhi h‖ * ρ ^ jhi = Mx := by
    refine hval jhi (fun x hx hne => ?_) (max'_mem J hJ)
    have hk := mem_antidiagonal.mp hx
    have hx2 : 1 ≤ x.2 := by
      rcases Nat.eq_zero_or_pos x.2 with h2 | h2
      · exfalso; apply hne; ext <;> simp <;> omega
      · exact h2
    rw [← hk, hterm]
    calc w x.1 * (‖PowerSeries.coeff x.2 U‖ * ρ ^ x.2) < Mx * 1 := by
          rcases eq_or_lt_of_le (show 0 ≤ w x.1 by simp only [w]; positivity) with h0 | h0
          · rw [← h0, zero_mul, mul_one]; exact hMx
          · exact mul_lt_mul' (hle _) (hU _ hx2) (by positivity) hMx
      _ = Mx := mul_one _
  have hmMx : ‖PowerSeries.coeff m h‖ * ρ ^ m ≤ Mx := hhle m
  have hlo_m : jlo = m := by
    by_contra hne; have := hdom jlo hne; linarith
  have hhi_m : jhi = m := by
    by_contra hne; have := hdom jhi hne; linarith
  have hmJ : m ∈ J := hlo_m ▸ min'_mem J hJ
  have hwm : w m = Mx := (mem_filter.mp hmJ).2
  refine ⟨fun j hj => ?_, ?_, ?_⟩
  · by_cases hjJ : j ∈ J
    · exfalso
      have h1 := min'_le J j hjJ
      have h2 := le_max' J j hjJ
      exact hj (by omega)
    · have := hnotJ j hjJ; simp only [w] at this hwm; rw [hwm]; exact this
  · have := hlo_m ▸ hlo
    have h' : ‖P.coeff m‖ * ρ ^ m = ‖PowerSeries.coeff m h‖ * ρ ^ m := by
      simp only [w] at hwm; rw [hwm, this]
    exact mul_right_cancel₀ (pow_pos hρ m).ne' h'
  · rw [hcoeff 0, antidiagonal_zero, sum_singleton, norm_mul, hU0', mul_one]

/-- choice of the radius (the break condition). -/
lemma exists_rho (m N : ℕ) (hm0 : 0 < m) (hmN : m < N) (ε α : ℝ) (hε : 0 < ε) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hbreak : ε ^ (N - m) < α ^ N) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ε < α * ρ ^ m ∧ ρ ^ (N - m) < α ∧ 0 < α := by
  set d := N - m with hd
  have hd0 : 0 < d := by omega
  have hα0 : 0 < α := by
    rcases eq_or_lt_of_le hα with h | h
    · rw [← h, zero_pow (by omega)] at hbreak; linarith [pow_pos hε d]
    · exact h
  set L := (ε / α) ^ ((1 : ℝ) / m)
  set U := α ^ ((1 : ℝ) / d)
  have hL0 : 0 ≤ L := Real.rpow_nonneg (div_pos hε hα0).le _
  have hLm : L ^ m = ε / α := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hε hα0).le]
    rw [one_div_mul_cancel (by exact_mod_cast hm0.ne'), Real.rpow_one]
  have hUd : U ^ d = α := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hα0.le]
    rw [one_div_mul_cancel (by exact_mod_cast hd0.ne'), Real.rpow_one]
  have hU1 : U ≤ 1 := Real.rpow_le_one hα0.le hα1 (by positivity)
  have hLU : L < U := by
    by_contra h; push_neg at h
    have h1 : U ^ (m * d) ≤ L ^ (m * d) := pow_le_pow_left₀ (Real.rpow_nonneg hα0.le _) h _
    have hU' : U ^ (m * d) = α ^ m := by rw [mul_comm, pow_mul, hUd]
    have hL' : L ^ (m * d) = ε ^ d / α ^ d := by rw [pow_mul, hLm, div_pow]
    rw [hU', hL'] at h1
    have hN : α ^ N = α ^ m * α ^ d := by rw [← pow_add]; congr 1; omega
    rw [le_div_iff₀ (pow_pos hα0 d), ← hN] at h1
    linarith
  set ρ := (L + U) / 2
  have hρ0 : 0 < ρ := by
    have : 0 < U := Real.rpow_pos_of_pos hα0 _
    positivity
  have hρL : L < ρ := by rw [show ρ = (L + U) / 2 from rfl]; linarith
  have hρU : ρ < U := by rw [show ρ = (L + U) / 2 from rfl]; linarith
  refine ⟨ρ, hρ0, lt_of_lt_of_le hρU hU1, ?_, hUd ▸ pow_lt_pow_left₀ hρU hρ0.le hd0.ne', hα0⟩
  have : ε / α < ρ ^ m := hLm ▸ pow_lt_pow_left₀ hρL hL0 hm0.ne'
  rwa [div_lt_iff₀ hα0, mul_comm] at this

open MvPowerSeries in
/-- **The canonical subgroup** of a height-`≤ 2` formal group with `v(a) < p/(p+1)`. -/
theorem canonical_subgroup {R : Type*} [CommRing R] (ι : R →+* K) (hι : ∀ r, ‖ι r‖ ≤ 1) (p : ℕ)
    [hp : Fact p.Prime] (F : FormalGroup R) [F.IsComm]
    (hu : ‖ι (coeff (Finsupp.single () (p ^ 2)) (FGL.nmul F p))‖ = 1)
    (hε : 0 < ‖(p : K)‖)
    (hbreak : ‖(p : K)‖ ^ p < ‖ι (coeff (Finsupp.single () p) (FGL.nmul F p))‖ ^ (p + 1))
    {κ : Type*} [Fintype κ] [DecidableEq κ] (r : κ → K) (hcard : Fintype.card κ = p ^ 2 - 1)
    (U : PowerSeries K) (hU0 : ‖PowerSeries.constantCoeff U‖ = 1) (hU : ∀ k, ‖PowerSeries.coeff k U‖ ≤ 1)
    (hW : ((∏ i, (Polynomial.X - Polynomial.C (r i)) : K[X]) : PowerSeries K) * U =
      PowerSeries.mk fun k => ι (coeff (Finsupp.single () (k + 1)) (FGL.nmul F p))) :
    ∃ ρ : ℝ, 0 < ρ ∧ #(univ.filter fun i => ‖r i‖ < ρ) = p - 1 ∧ (∀ i, ‖r i‖ ≠ ρ) ∧
      ‖ι (coeff (Finsupp.single () p) (FGL.nmul F p))‖ * ∏ i ∈ univ.filter (fun i => ‖r i‖ < ρ), ‖r i‖ =
        ‖(p : K)‖ := by
  have hp2 := hp.out.two_le
  set a := coeff (Finsupp.single () p) (FGL.nmul F p)
  set ε := ‖(p : K)‖
  set α := ‖ι a‖
  set N := p ^ 2 - 1 with hN
  set m := p - 1 with hm
  have hm0 : 0 < m := by omega
  have hpp : p ≤ p ^ 2 := by nlinarith
  have hpp2 : p < p ^ 2 := by nlinarith
  have hmN : m < N := by rw [hm, hN]; omega
  have hα1 : α ≤ 1 := hι a
  -- the break in the form `ε^{N−m} < α^N`
  have hbreak' : ε ^ (N - m) < α ^ N := by
    have e1 : N - m = p * (p - 1) := by
      rw [hN, hm]; have : p ^ 2 = p * p := sq p; rw [this, Nat.mul_sub, mul_one]; omega
    have e2 : N = (p + 1) * (p - 1) := by
      rw [hN]; have : p ^ 2 = p * p := sq p; rw [this]
      zify [Nat.one_le_iff_ne_zero.mpr (by omega : p ≠ 0), (by nlinarith : 1 ≤ p * p)]; ring
    rw [e1, e2, pow_mul, pow_mul]
    exact pow_lt_pow_left₀ hbreak (by positivity) (by omega)
  obtain ⟨ρ, hρ0, hρ1, hρm, hρd, hα0⟩ := exists_rho m N hm0 hmN ε α hε (norm_nonneg _) hα1 hbreak'
  have hεα : ε < α := by
    have h1 : ε < α * ρ ^ m := hρm
    have : α * ρ ^ m ≤ α := mul_le_of_le_one_right hα0.le (pow_le_one₀ hρ0.le hρ1.le)
    linarith
  -- coefficients of `h = [p](T)/T`
  set h := PowerSeries.mk fun k => ι (coeff (Finsupp.single () (k + 1)) (FGL.nmul F p)) with hh
  have hc : ∀ k, PowerSeries.coeff k h = ι (coeff (Finsupp.single () (k + 1)) (FGL.nmul F p)) := fun k => by
    rw [hh, PowerSeries.coeff_mk]
  have hnorm_p : ∀ x : R, (p : R) ∣ x → ‖ι x‖ ≤ ε := by
    rintro x ⟨s, rfl⟩; rw [map_mul, norm_mul, map_natCast]
    exact mul_le_of_le_one_right (norm_nonneg _) (hι s)
  have hnorm_pa : ∀ x : R, x ∈ Ideal.span {(p : R), a} → ‖ι x‖ ≤ α := by
    intro x hx
    obtain ⟨s, t, rfl⟩ := Ideal.mem_span_pair.mp hx
    rw [map_add, map_mul, map_mul, map_natCast]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
    · rw [norm_mul]; exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (hι s)) hεα.le
    · rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (hι t)
  have hc0 : ‖PowerSeries.coeff 0 h‖ = ε := by
    rw [hc, zero_add, FGL.coeff_one_nmul, map_natCast]
  have hcm : ‖PowerSeries.coeff m h‖ = α := by
    rw [hc, show m + 1 = p by omega]
  have hdom : ∀ k, k ≠ m → ‖PowerSeries.coeff k h‖ * ρ ^ k < ‖PowerSeries.coeff m h‖ * ρ ^ m := by
    intro k hk
    rw [hcm]
    rcases lt_trichotomy k m with hlt | heq | hgt
    · -- `k + 1 < p`, so `p ∤ k + 1`
      have hnd : ¬ p ∣ k + 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      have := hnorm_p _ (FGL.p_dvd_coeff_nmul F p (k + 1) hnd)
      rw [← hc] at this
      calc ‖PowerSeries.coeff k h‖ * ρ ^ k ≤ ε * 1 :=
            mul_le_mul this (pow_le_one₀ hρ0.le hρ1.le) (by positivity) hε.le
        _ < α * ρ ^ m := by rw [mul_one]; exact hρm
    · exact absurd heq hk
    · rcases Nat.lt_or_ge k N with hkN | hkN
      · have hnd : ¬ p ^ 2 ∣ k + 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
        have := hnorm_pa _ (FGL.mem_ideal_coeff_nmul p F (k + 1) hnd)
        rw [← hc] at this
        calc ‖PowerSeries.coeff k h‖ * ρ ^ k ≤ α * ρ ^ k := mul_le_mul_of_nonneg_right this (by positivity)
          _ < α * ρ ^ m := mul_lt_mul_of_pos_left (pow_lt_pow_right_of_lt_one₀ hρ0 hρ1 hgt) hα0
      · have h1 : ‖PowerSeries.coeff k h‖ ≤ 1 := by rw [hc]; exact hι _
        have hρN : ρ ^ N = ρ ^ m * ρ ^ (N - m) := by rw [← pow_add]; congr 1; omega
        calc ‖PowerSeries.coeff k h‖ * ρ ^ k ≤ 1 * ρ ^ N :=
              mul_le_mul h1 (pow_le_pow_of_le_one hρ0.le hρ1.le hkN) (by positivity) zero_le_one
          _ = ρ ^ m * ρ ^ (N - m) := by rw [one_mul, hρN]
          _ < ρ ^ m * α := mul_lt_mul_of_pos_left hρd (pow_pos hρ0 m)
          _ = α * ρ ^ m := mul_comm _ _
  have hUlt : ∀ k, 1 ≤ k → ‖PowerSeries.coeff k U‖ * ρ ^ k < 1 := fun k hk =>
    calc ‖PowerSeries.coeff k U‖ * ρ ^ k ≤ 1 * ρ ^ k := mul_le_mul_of_nonneg_right (hU k) (by positivity)
      _ < 1 := by rw [one_mul]; exact pow_lt_one₀ hρ0.le hρ1 (by omega)
  rw [← hW] at hdom hc0 hcm
  obtain ⟨hPdom, hPm, hP0⟩ := dominance_transfer _ U ρ hρ0 hU0 hUlt m hdom
  rw [hcm] at hPm; rw [hc0] at hP0
  obtain ⟨hcount, hne, hprod⟩ := Newton.dominant r ρ hρ0 m (by omega) fun j _ hj => hPdom j hj
  refine ⟨ρ, hρ0, hcount, hne, ?_⟩
  rw [← hPm, ← hprod, hP0]

end AtkinOBrien.Canonical
