/-
# The `τ(p)` form: `∑_{p<N} τ(p) log p = o(N^{13/2})`

Partial summation (`abel_identity`, then `weighted_littleO`): if `∑_{n<N} a(n) = o(N)` then
`∑_{n<N} a(n) n^{11/2} = o(N^{13/2})`.  Applied to `a(p) = λ(p) log p` with
`τ(p) = λ(p) p^{11/2}`.
-/
import RamanujanTau.TauPNT.WienerIkehara

set_option autoImplicit false

namespace RamanujanTau.TauPNT

open Filter Topology
open RamanujanTau.EdgeNonvanishing

/-- Abel's identity: `∑_{n<N} a(n)w(n) = S(N)w(N) − ∑_{n<N} S(n+1)(w(n+1) − w(n))`,
`S(n) = ∑_{m<n} a(m)`. -/
lemma abel_identity (a w : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, a n * w n =
      (∑ m ∈ Finset.range N, a m) * w N -
        ∑ n ∈ Finset.range N, (∑ m ∈ Finset.range (n + 1), a m) * (w (n + 1) - w n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun n => _ * (w (n + 1) - w n)),
      Finset.sum_range_succ a N]
    ring

/-- **Partial summation**: `∑_{n<N} a(n) = o(N)` implies `∑_{n<N} a(n) n^{11/2} = o(N^{13/2})`. -/
lemma weighted_littleO {a : ℕ → ℝ}
    (ha : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, a n) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, a n * (n : ℝ) ^ (11 / 2 : ℝ)) /
      (N : ℝ) ^ (13 / 2 : ℝ)) atTop (𝓝 0) := by
  set S : ℕ → ℝ := fun n => ∑ m ∈ Finset.range n, a m
  set w : ℕ → ℝ := fun n => (n : ℝ) ^ (11 / 2 : ℝ)
  have hw0 : w 0 = 0 := by simp [w]
  have hwmono : ∀ n, w n ≤ w (n + 1) := fun n => by
    simp only [w]; exact Real.rpow_le_rpow (by positivity) (by push_cast; linarith) (by norm_num)
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set ε := δ / 8
  have hε : 0 < ε := by positivity
  obtain ⟨m0, hm0⟩ := Metric.tendsto_atTop.mp ha ε hε
  set B : ℝ := ∑ j ∈ Finset.range (m0 + 1), |S j|
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hSb : ∀ m : ℕ, |S m| ≤ ε * m + B := by
    intro m
    rcases lt_or_ge m (m0 + 1) with hm | hm
    · have := Finset.single_le_sum (f := fun j => |S j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr hm)
      have : 0 ≤ ε * m := by positivity
      simp only at *; linarith
    · have h := hm0 m (by omega)
      rw [Real.dist_eq, sub_zero] at h
      have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      rw [abs_div, Nat.abs_cast, div_lt_iff₀ hmpos] at h
      linarith
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, 4 * B / δ < N1 := exists_nat_gt _
  refine ⟨max N1 1, fun N hN => ?_⟩
  have hN1' : (N1 : ℝ) ≤ N := by exact_mod_cast (le_max_left _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [Real.dist_eq, sub_zero]
  -- `|T(N)| ≤ 2(εN + B) w(N)`
  have hT : |∑ n ∈ Finset.range N, a n * w n| ≤ 2 * (ε * N + B) * w N := by
    rw [abel_identity a w N]
    have h1 : |S N * w N| ≤ (ε * N + B) * w N := by
      rw [abs_mul, abs_of_nonneg (by simp only [w]; positivity : 0 ≤ w N)]
      exact mul_le_mul_of_nonneg_right (hSb N) (by simp only [w]; positivity)
    have h2 : |∑ n ∈ Finset.range N, S (n + 1) * (w (n + 1) - w n)| ≤ (ε * N + B) * w N := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ n ∈ Finset.range N, |S (n + 1) * (w (n + 1) - w n)|
          ≤ ∑ n ∈ Finset.range N, (ε * N + B) * (w (n + 1) - w n) := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hd : 0 ≤ w (n + 1) - w n := sub_nonneg.mpr (hwmono n)
            rw [abs_mul, abs_of_nonneg hd]
            refine mul_le_mul_of_nonneg_right ((hSb (n + 1)).trans ?_) hd
            have : ((n + 1 : ℕ) : ℝ) ≤ N := by
              exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hn)
            nlinarith
        _ = (ε * N + B) * w N := by
            rw [← Finset.mul_sum, Finset.sum_range_sub (fun n => w n), hw0, sub_zero]
    have := abs_sub (S N * w N) (∑ n ∈ Finset.range N, S (n + 1) * (w (n + 1) - w n))
    simp only [S] at h1 h2 this ⊢
    linarith
  have hN132 : (N : ℝ) ^ (13 / 2 : ℝ) = N * w N := by
    simp only [w]
    rw [show (13 / 2 : ℝ) = 1 + 11 / 2 by norm_num, Real.rpow_add hNpos, Real.rpow_one]
  have hwpos : 0 < w N := by simp only [w]; positivity
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) ^ (13 / 2 : ℝ)), hN132,
    div_lt_iff₀ (by positivity)]
  have hBN : B < δ / 4 * N := by
    rw [div_lt_iff₀ hδ] at hN1
    nlinarith
  calc |∑ n ∈ Finset.range N, a n * w n| ≤ 2 * (ε * N + B) * w N := hT
    _ < δ * (N * w N) := by
      have : 2 * (ε * N + B) < δ * N := by simp only [ε]; nlinarith
      nlinarith

/-- `τ(p) = λ(p) p^{11/2}`. -/
lemma tau_eq_lam_mul {p : ℕ} (hp : p.Prime) : ((tau p : ℤ) : ℝ) = lam p * (p : ℝ) ^ (11 / 2 : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  simp only [lam, uu, pow_one, rr]
  rw [mul_assoc, ← Real.rpow_add hp0]; simp

/-- **The prime number theorem for `τ`, `τ(p)` form** (conditional on `WienerIkeharaHyp` and
`DeligneBound`): `∑_{p<N} τ(p) log p = o(N^{13/2})`. -/
theorem tau_PNT_tau [DeligneBound] (hWI : WienerIkeharaHyp) :
    Tendsto (fun N : ℕ => (∑ p ∈ Finset.range N with p.Prime, ((tau p : ℤ) : ℝ) * Real.log p) /
      (N : ℝ) ^ (13 / 2 : ℝ)) atTop (𝓝 0) := by
  set a : ℕ → ℝ := fun n => if n.Prime then lam n * Real.log n else 0
  have ha : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, a n) / N) atTop (𝓝 0) := by
    refine (tau_PNT hWI).congr fun N => ?_
    simp only [a]; rw [Finset.sum_filter]
  refine (weighted_littleO ha).congr fun N => ?_
  simp only [a]
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs with h
  · rw [tau_eq_lam_mul h]; ring
  · simp

end RamanujanTau.TauPNT
