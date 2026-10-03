/-
# Rank-difference generating functions mod 5 (Atkin–Swinnerton-Dyer / Ramanujan's Lost Notebook)

Writing `N(k, m)` for the number of partitions of `m` with rank `≡ k (mod 5)`, the Lost Notebook dissection
`lost_notebook_rank_mod5` gives every rank difference explicitly. Two of them are Ramanujan's fifth-order mock theta
functions `φ(q) = Σ q^{5n²}/((q;q⁵)_{n+1}(q⁴;q⁵)_n) − 1` and `ψ(q) = Σ q^{5n²}/((q²;q⁵)_{n+1}(q³;q⁵)_n) − 1`:
  `Σ (N(1,5n) − N(2,5n)) qⁿ = φ(q)`,   `Σ (N(0,5n+3) − N(2,5n+3)) qⁿ⁺¹ = −ψ(q)`.
-/
import RamanujanTau.RankASD5
import RamanujanTau.SptFinal

set_option autoImplicit false

namespace CrankProof
open PowerSeries Finset
open MockTheta5.JTP (ω5 ω5_prim ω5_pow5 eQ)

local notation "ψ" => MockTheta5.JTP.ψC

/-- if `Σ N_k ζ₅^k = a₀ + a₁ζ₅ + … + a₄ζ₅⁴` with integers `a_k`, then all `N_k − a_k` are equal. -/
lemma cyc_shift5 (N : ℕ → ℕ) (a0 a1 a2 a3 a4 : ℤ)
    (h : ∑ k ∈ range 5, (N k : ℂ) * ω5 ^ k = a0 + a1 * ω5 + a2 * ω5 ^ 2 + a3 * ω5 ^ 3 + a4 * ω5 ^ 4) :
    (N 0 : ℤ) - a0 = N 4 - a4 ∧ (N 1 : ℤ) - a1 = N 4 - a4 ∧ (N 2 : ℤ) - a2 = N 4 - a4 ∧
      (N 3 : ℤ) - a3 = N 4 - a4 := by
  let c : ℕ → ℤ := fun i => (N i : ℤ) - (if i = 0 then a0 else if i = 1 then a1 else if i = 2 then a2
    else if i = 3 then a3 else a4)
  have hc : ∑ k ∈ range 5, (c k : ℂ) * ω5 ^ k = 0 := by
    simp only [c, sum_range_succ, sum_range_zero] at h ⊢
    simp
    linear_combination h
  exact ⟨cycZ5 c hc (k := 0) (by norm_num), cycZ5 c hc (k := 1) (by norm_num), cycZ5 c hc (k := 2) (by norm_num),
    cycZ5 c hc (k := 3) (by norm_num)⟩

lemma tζ_eq : tζ = ω5 + ω5 ^ 4 := rfl
lemma sζ_eq : sζ = ω5 ^ 2 + ω5 ^ 3 := rfl

/-- **Rank-difference generating functions mod 5.** -/
theorem rank_diff_mod5 (n : ℕ) :
    ((rankCount (5 * n + 0) 1 : ℤ) - rankCount (5 * n + 0) 2 = coeff n (RankProof.Phi 1 - 1)) ∧
    ((rankCount (5 * n + 0) 0 : ℤ) - rankCount (5 * n + 0) 2
      = coeff n (eQ ^ 2 * Jab 5 2 * Ring.inverse (Jab 5 1) ^ 2) - 2 * coeff n (RankProof.Phi 1 - 1)) ∧
    ((rankCount (5 * n + 1) 1 : ℤ) = rankCount (5 * n + 1) 2) ∧
    ((rankCount (5 * n + 1) 0 : ℤ) - rankCount (5 * n + 1) 2 = coeff n (eQ ^ 2 * Ring.inverse (Jab 5 1))) ∧
    ((rankCount (5 * n + 2) 0 : ℤ) = rankCount (5 * n + 2) 2) ∧
    ((rankCount (5 * n + 2) 1 : ℤ) - rankCount (5 * n + 2) 2 = coeff n (eQ ^ 2 * Ring.inverse (Jab 5 2))) ∧
    ((rankCount (5 * n + 3) 0 : ℤ) - rankCount (5 * n + 3) 2 = -coeff (n + 1) (RankProof.Phi 2 - 1)) ∧
    ((rankCount (5 * n + 3) 1 : ℤ) - rankCount (5 * n + 3) 2
      = -2 * coeff (n + 1) (RankProof.Phi 2 - 1) - coeff n (eQ ^ 2 * Jab 5 1 * Ring.inverse (Jab 5 2) ^ 2)) := by
  obtain ⟨h0, h1, h2, h3, -⟩ := lost_notebook_rank_mod5
  -- class 0
  have c0 := rank_sum_Rk n 0
  rw [h0, map_add, coeff_C_mul, MockTheta5.JTP.ψC, coeff_map, coeff_map, tζ_eq] at c0
  set P := coeff n (eQ ^ 2 * Jab 5 2 * Ring.inverse (Jab 5 1) ^ 2)
  set φn := coeff n (RankProof.Phi 1 - 1)
  have e0 := cyc_shift5 (rankCount (5 * n + 0)) (P - 2 * φn) (φn) (0) (0) (φn)
    (by rw [c0]; simp only [eq_intCast]; push_cast; ring)
  -- class 1
  have c1 := rank_sum_Rk n 1
  rw [h1, MockTheta5.JTP.ψC, coeff_map] at c1
  set P1 := coeff n (eQ ^ 2 * Ring.inverse (Jab 5 1))
  have e1 := cyc_shift5 (rankCount (5 * n + 1)) (P1) (0) (0) (0) (0)
    (by rw [c1]; simp only [eq_intCast]; push_cast; ring)
  -- class 2
  have c2 := rank_sum_Rk n 2
  rw [h2, coeff_C_mul, MockTheta5.JTP.ψC, coeff_map, tζ_eq] at c2
  set P2 := coeff n (eQ ^ 2 * Ring.inverse (Jab 5 2))
  have e2 := cyc_shift5 (rankCount (5 * n + 2)) (0) (P2) (0) (0) (P2)
    (by rw [c2]; simp only [eq_intCast]; push_cast; ring)
  -- class 3
  have c3 := rank_sum_Rk n 3
  have h3' := congrArg (coeff (n + 1)) h3
  rw [coeff_succ_X_mul, map_add, coeff_C_mul, mul_assoc, coeff_C_mul, coeff_succ_X_mul, MockTheta5.JTP.ψC,
    coeff_map, coeff_map, sζ_eq, tζ_eq] at h3'
  rw [h3'] at c3
  set a := coeff (n + 1) (RankProof.Phi 2 - 1)
  set P3 := coeff n (eQ ^ 2 * Jab 5 1 * Ring.inverse (Jab 5 2) ^ 2)
  have e3 := cyc_shift5 (rankCount (5 * n + 3)) (P3) (-a) (a + P3) (a + P3) (-a)
    (by rw [c3]; simp only [eq_intCast]; push_cast; ring)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a0, a1, a2, a3⟩ := e0; linarith
  · obtain ⟨a0, a1, a2, a3⟩ := e0; linarith
  · obtain ⟨a0, a1, a2, a3⟩ := e1; linarith
  · obtain ⟨a0, a1, a2, a3⟩ := e1; linarith
  · obtain ⟨a0, a1, a2, a3⟩ := e2; linarith
  · obtain ⟨a0, a1, a2, a3⟩ := e2; linarith
  · obtain ⟨a0, a1, a2, a3⟩ := e3; linarith
  · obtain ⟨a0, a1, a2, a3⟩ := e3; linarith

end CrankProof
