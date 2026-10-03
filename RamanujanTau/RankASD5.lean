/-
# Atkin–Swinnerton-Dyer rank equalities mod 5

From Ramanujan's Lost Notebook dissection (`lost_notebook_rank_mod5`):
`R₁ = ψ(·)` has no `ζ`, and `R₂ = t_ζ · ψ(·)` with `t_ζ = ζ + ζ⁴`. Since the minimal polynomial of `ζ₅` is `Φ₅`, an
integer relation `Σ c_k ζ₅^k = 0` forces `c₀ = … = c₄`. This gives
`N(1,5,5n+1) = N(2,5,5n+1)` and `N(0,5,5n+2) = N(2,5,5n+2)`.
-/
import RamanujanTau.RankR03

set_option autoImplicit false

namespace CrankProof
open PowerSeries Finset
open MockTheta5.JTP (ω5 ω5_prim ω5_pow5 eQ)

local notation "ψ" => MockTheta5.JTP.ψC

/-- an integer relation among the powers of `ζ₅` has all coefficients equal. -/
lemma cyc_equalZ (c0 c1 c2 c3 c4 : ℤ)
    (h : (c0 : ℂ) + c1 * ω5 + c2 * ω5 ^ 2 + c3 * ω5 ^ 3 + c4 * ω5 ^ 4 = 0) :
    c0 = c4 ∧ c1 = c4 ∧ c2 = c4 ∧ c3 = c4 := by
  set q : Polynomial ℚ := Polynomial.C ((c0 : ℚ) - c4) + Polynomial.C ((c1 : ℚ) - c4) * Polynomial.X
    + Polynomial.C ((c2 : ℚ) - c4) * Polynomial.X ^ 2 + Polynomial.C ((c3 : ℚ) - c4) * Polynomial.X ^ 3 with hq
  have hphi := MockTheta5.JTP.phi_of_prim ω5_prim
  have hev : Polynomial.aeval ω5 q = 0 := by
    simp only [hq, map_add, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, eq_ratCast]
    push_cast
    linear_combination h - (c4 : ℂ) * hphi
  have hdvd : minpoly ℚ ω5 ∣ q := minpoly.dvd ℚ ω5 hev
  rw [← Polynomial.cyclotomic_eq_minpoly_rat ω5_prim (by norm_num)] at hdvd
  have hdeg : q.degree < (Polynomial.cyclotomic 5 ℚ).degree := by
    rw [Polynomial.degree_cyclotomic, Nat.totient_prime Nat.prime_five]
    refine lt_of_le_of_lt (b := ((3 : ℕ) : WithBot ℕ)) ?_ (by decide)
    rw [hq]; compute_degree
    all_goals norm_num
  have hq0 := Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hdeg
  have e0 := congrArg (Polynomial.coeff · 0) hq0
  have e1 := congrArg (Polynomial.coeff · 1) hq0
  have e2 := congrArg (Polynomial.coeff · 2) hq0
  have e3 := congrArg (Polynomial.coeff · 3) hq0
  simp only [hq, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_C, Polynomial.coeff_zero] at e0 e1 e2 e3
  norm_num [sub_eq_zero] at e0 e1 e2 e3
  exact ⟨by exact_mod_cast e0, by exact_mod_cast e1, by exact_mod_cast e2, by exact_mod_cast e3⟩

/-- `Σ_{λ ⊢ 5n+r} ζ₅^{rank λ}` is the `n`-th coefficient of `R_r`. -/
lemma rank_sum_Rk (n r : ℕ) :
    ∑ k ∈ range 5, (rankCount (5 * n + r) k : ℂ) * ω5 ^ k = coeff n (Rk r) := by
  rw [← rank_sum_grouped, rank_durfee (ω5_prim.ne_zero (by norm_num)), Rk, dis5C, coeff_mk]

/-- **Atkin–Swinnerton-Dyer (1954), rank mod 5.** `N(1,5n+1) = N(2,5n+1)` and `N(0,5n+2) = N(2,5n+2)`
(together with `N(k,·) = N(5−k,·)` and `rank_equidistribution_mod5` for `5n+4`). -/
theorem rank_mod5_ASD (n : ℕ) :
    rankCount (5 * n + 1) 1 = rankCount (5 * n + 1) 2 ∧
    rankCount (5 * n + 2) 0 = rankCount (5 * n + 2) 2 := by
  obtain ⟨-, h1, h2, -, -⟩ := lost_notebook_rank_mod5
  constructor
  · have h := rank_sum_Rk n 1
    rw [h1, MockTheta5.JTP.ψC, coeff_map] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one, pow_one] at h
    set a := coeff n (eQ ^ 2 * Ring.inverse (Jab 5 1))
    obtain ⟨-, e1, e2, -⟩ := cyc_equalZ ((rankCount (5 * n + 1) 0 : ℤ) - a) (rankCount (5 * n + 1) 1)
      (rankCount (5 * n + 1) 2) (rankCount (5 * n + 1) 3) (rankCount (5 * n + 1) 4)
      (by push_cast; rw [← sub_eq_zero.mpr h]; simp; ring)
    omega
  · have h := rank_sum_Rk n 2
    rw [h2, MockTheta5.JTP.ψC, coeff_C_mul, coeff_map] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one, pow_one] at h
    set b := coeff n (eQ ^ 2 * Ring.inverse (Jab 5 2))
    obtain ⟨e0, -, e2, -⟩ := cyc_equalZ (rankCount (5 * n + 2) 0) ((rankCount (5 * n + 2) 1 : ℤ) - b)
      (rankCount (5 * n + 2) 2) (rankCount (5 * n + 2) 3) ((rankCount (5 * n + 2) 4 : ℤ) - b)
      (by push_cast; rw [← sub_eq_zero.mpr h]; simp [tζ]; ring)
    omega

end CrankProof
