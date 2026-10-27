/-
# Rademacher's formula in closed form

`Σ_m y^m/(m!Γ(m+5/2)) = 4(u cosh u − sinh u)/(√π u³)` with `u = 2√y`, so

  `p(n) = lim_{N→∞} Σ_{k≤N} A_k(n) · (π/12k)^{3/2} · 2π · 4(u_k cosh u_k − sinh u_k)/(√π u_k³ k)`,

`u_k = (π/k)√((2/3)(n − 1/24))`. This is Rademacher's
`p(n) = (1/(π√2)) Σ_k A_k(n) √k · d/dn [sinh((π/k)√((2/3)(n−1/24)))/√(n−1/24)]`.
-/
import RamanujanTau.Rademacher.Assembly

set_option autoImplicit false

namespace Rademacher
open Real Filter
open scoped Nat Topology

noncomputable section

lemma Gamma_m52 (m : ℕ) : Real.Gamma (m + 5 / 2) = (2 * m + 3)! * √π / (2 ^ (2 * m + 3) * (m + 1)!) := by
  induction m with
  | zero =>
    have h := Real.Gamma_nat_add_one_add_half 1
    norm_num [Nat.doubleFactorial] at h
    simp only [Nat.cast_zero, zero_add]
    rw [h]
    norm_num [Nat.factorial]
    ring
  | succ m ih =>
    rw [show ((m + 1 : ℕ) : ℝ) + 5 / 2 = (m + 5 / 2) + 1 by push_cast; ring,
      Real.Gamma_add_one (by positivity), ih]
    have f1 : (2 * (m + 1) + 3)! = (2 * m + 5) * ((2 * m + 4) * (2 * m + 3)!) := by
      rw [show 2 * (m + 1) + 3 = (2 * m + 3) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    have f2 : (m + 1 + 1)! = (m + 2) * (m + 1)! := Nat.factorial_succ _
    rw [f1, f2]
    push_cast
    field_simp
    ring

/-- `bco y m = 8(m+1)u^{2m}/((2m+3)!√π)` with `u² = 4y`. -/
lemma bco_eq {y u : ℝ} (hu : u ^ 2 = 4 * y) (m : ℕ) :
    bco y m = 8 * (m + 1) * u ^ (2 * m) / ((2 * m + 3)! * √π) := by
  rw [bco, Gamma_m52]
  have hy : y = u ^ 2 / 4 := by linarith
  rw [hy, div_pow, ← pow_mul, show (2 : ℕ) * m = 2 * m from rfl]
  have hpi : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  rw [Nat.factorial_succ m]
  push_cast
  field_simp
  rw [show (4 : ℝ) ^ m = 2 ^ (2 * m) by rw [pow_mul]; norm_num]
  ring

/-- `Σ (m+1)u^{2m}/(2m+3)! = (u cosh u − sinh u)/(2u³)`. -/
lemma hasSum_aux {u : ℝ} (hu : u ≠ 0) :
    HasSum (fun m : ℕ => (m + 1) * u ^ (2 * m) / (2 * m + 3)!) ((u * Real.cosh u - Real.sinh u) / (2 * u ^ 3)) := by
  have hc := (Real.hasSum_cosh u).mul_left u
  have hs := Real.hasSum_sinh u
  have hd := hc.sub hs
  -- the `j`-th term is `2j u^{2j+1}/(2j+1)!`
  have e : ∀ j : ℕ, u * (u ^ (2 * j) / (2 * j)!) - u ^ (2 * j + 1) / (2 * j + 1)! =
      2 * j * u ^ (2 * j + 1) / (2 * j + 1)! := by
    intro j
    rw [Nat.factorial_succ (2 * j)]
    push_cast
    field_simp
    ring
  simp only [e] at hd
  rw [← hasSum_nat_add_iff' 1] at hd
  simp at hd
  have hd2 := hd.div_const (2 * u ^ 3)
  convert hd2 using 1
  funext m
  rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring]
  field_simp
  ring

/-- **the closed form of the Bessel series**. -/
theorem tsum_bco {y : ℝ} (hy : 0 < y) :
    ∑' m, bco y m = 4 * (2 * √y * Real.cosh (2 * √y) - Real.sinh (2 * √y)) / (√π * (2 * √y) ^ 3) := by
  set u := 2 * √y with huu
  have hu2 : u ^ 2 = 4 * y := by rw [huu, mul_pow, Real.sq_sqrt hy.le]; norm_num
  have hu0 : u ≠ 0 := by rw [huu]; have := Real.sqrt_pos.mpr hy; positivity
  have h := (hasSum_aux hu0).mul_left (8 / √π)
  rw [show (fun m => bco y m) = fun m : ℕ => 8 / √π * ((m + 1) * u ^ (2 * m) / (2 * m + 3)!) by
    funext m; rw [bco_eq hu2]; field_simp]
  rw [h.tsum_eq]
  field_simp
  ring

/-- `u_k = (π/k)√((2/3)(n − 1/24))`. -/
def uk (k n : ℕ) : ℝ := π / k * √((2 / 3) * ((n : ℝ) - 1 / 24))

/-- the `k`-th Rademacher term (without `A_k`): `(π/12k)^{3/2}·2π·4(u cosh u − sinh u)/(√π u³)/k`. -/
def radTerm (k n : ℕ) : ℝ :=
  (π / (12 * k)) ^ (3 / 2 : ℝ) * (2 * π) * (4 * (uk k n * Real.cosh (uk k n) - Real.sinh (uk k n)) /
    (√π * uk k n ^ 3)) / k

lemma two_sqrt_yk {k n : ℕ} (hk : 0 < k) (hn : 1 ≤ n) : 2 * √(yk k n) = uk k n := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ (n : ℝ) - 1 / 24 := by linarith
  have hy : 0 ≤ yk k n := by unfold yk; positivity
  have h1 : 0 ≤ 2 * √(yk k n) := by positivity
  have h2 : 0 ≤ uk k n := by unfold uk; positivity
  refine (pow_left_inj₀ h1 h2 two_ne_zero).mp ?_
  rw [mul_pow, Real.sq_sqrt hy, uk, mul_pow, Real.sq_sqrt (by positivity), yk]
  field_simp
  ring

lemma FL_eq {k n : ℕ} (hk : 0 < k) (hn : 1 ≤ n) : FL k n / k = (radTerm k n : ℂ) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hy : 0 < yk k n := by
    unfold yk
    have : (0 : ℝ) < (n : ℝ) - 1 / 24 := by linarith
    positivity
  rw [FL, fullLine hk hn, ← Complex.ofReal_tsum, tsum_bco hy, two_sqrt_yk hk hn, radTerm]
  push_cast
  ring

/-- **Rademacher's formula** (1937):
`p(n) = Σ_{k≥1} A_k(n) · (π/12k)^{3/2} · 2π · 4(u_k cosh u_k − sinh u_k)/(√π u_k³ k)`,
`u_k = (π/k)√((2/3)(n − 1/24))`, `A_k(n) = Σ_{h mod k, (h,k)=1} ω_{h,k} e^{−2πinh/k}`. -/
theorem rademacher (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, Ak k n * (radTerm k n : ℂ)) atTop (𝓝 (HardyRamanujan.p n : ℂ)) := by
  refine (rademacher_tendsto n hn).congr fun N => Finset.sum_congr rfl fun k hk => ?_
  rw [FL_eq (by have := (Finset.mem_Icc.mp hk).1; omega) hn]

end

end Rademacher
