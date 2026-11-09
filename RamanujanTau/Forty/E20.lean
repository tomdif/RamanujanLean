/-
# Entry 3.20: `G(q)H(−q) + G(−q)H(q) = 2/χ²(−q²)` (Watson 1933)

Watson's second proof (Berndt et al. §23):
`{G(q)H(−q)+G(−q)H(q)}² = {G(q)H(−q)−G(−q)H(q)}² + 4G(q)H(q)G(−q)H(−q)`.
It uses Entry 3.21, `GH = f(−q⁵)/f(−q)`, and Lemma 23.1, `ψ(q)² − qψ(q⁵)² = f(q,q⁴)f(q²,q³)`. Lemma 23.1 is proved
here by the exact cover `B = (1 2; −2 1)` of `f(1,q)²` (`L23_1`, `P23_1`). The square root is fixed by the constant
term.
-/
import RamanujanTau.Forty.E21

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm1 : 1 ≤ 1 := by norm_num
private lemma hm5 : 1 ≤ 5 := by norm_num

/-- Entry 23.1: `B = (1 2; -2 1)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B23_1 : ECS where
  b11 := 1
  b12 := 2
  b21 := (-2)
  b22 := 1
  r1 := 1
  r2 := 0
  I := {(-2), (-1), 0, 1, 2}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 3 * n - (-2)) % 5 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 3 * n - (-2)) % 5 + (-2))) - 2 * (n - 0 * ((1 * m + 3 * n - (-2)) % 5 + (-2)))) / 5), ((1 * (n - 0 * ((1 * m + 3 * n - (-2)) % 5 + (-2))) - (-2) * (m - 1 * ((1 * m + 3 * n - (-2)) % 5 + (-2)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L23_1 : θ hm1 0 (-1) * θ hm1 0 (-1) = 2 * (θ hm5 1 (-1) * θ hm5 2 (-1)) + 2 * (θ hm5 2 (-1) * θ hm5 1 (-1)) + (mono 1 1 * (θ hm5 0 (-1) * θ hm5 0 (-1))) := by
  have h := θθ_lattice hm1 hm1 hm5 hm5 0 0 (by norm_num : (-1 : ℂ) ≠ 0) (by norm_num : (-1 : ℂ) ≠ 0) B23_1 rfl rfl
    (by norm_num [B23_1]) (by norm_num [B23_1]) (by norm_num [B23_1])
  simp only [B23_1] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [c2] at h
  simp only [θ_nfrm hm5 1 (-1) (-1) 1 (e := (-1)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm5 1 0 0 1 (e := 4) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm5 2 0 0 1 (e := 3) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm5 0 1 (by norm_num : (-1 : ℂ) ≠ 0) 0 1 (e := 5) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm5 2 (-1) (by norm_num : (-1 : ℂ) ≠ 0) (-3) 1 (e := (-3)) (by norm_num) (by norm_num [c2]) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- **Lemma 23.1** (product form): `ψ(q)² − qψ(q⁵)² = f(q,q⁴)f(q²,q³)`, with `ψ(q)(q;q²) = (q²;q²)` cleared. -/
theorem P23_1 : Pinf 2 2 ^ 2 * (Pinf 5 10 ^ 2 * (J 1 5 * J 2 5)) =
    PowerSeries.X * Pinf 10 10 ^ 2 * (Pinf 1 2 ^ 2 * (J 1 5 * J 2 5))
      + (J 2 10 * J 5 10) * (J 4 10 * J 5 10) * (Pinf 1 2 ^ 2 * Pinf 5 10 ^ 2) := by
  have four_ne : (4 : PowerSeries ℤ) ≠ 0 := by
    intro h; have := congrArg PowerSeries.constantCoeff h; rw [map_ofNat, map_zero] at this; norm_num at this
  apply mul_left_cancel₀ four_ne
  apply ι_inj
  have L := L23_1
  have hA := θ_bar0 (N := 1) hm1
  have hC := θ_bar0 (N := 5) hm5
  have h1 := θ_bar hm5 1 le_rfl (by norm_num)
  have h2 := θ_bar hm5 2 (by norm_num) (by norm_num)
  norm_num at hA hC h1 h2
  simp only [map_mul, map_add, map_pow, map_ofNat, ι_X] at hA hC h1 h2 ⊢
  linear_combination (ι (Pinf 1 2) ^ 2 * ι (Pinf 5 10) ^ 2 * ι (J 1 5) * ι (J 2 5)) * L
    - (ι (Pinf 5 10) ^ 2 * ι (J 1 5) * ι (J 2 5) * (θ hm1 0 (-1) * ι (Pinf 1 2) + 2 * ι (Pinf 2 2))) * hA
    + (mono 1 1 * ι (Pinf 1 2) ^ 2 * ι (J 1 5) * ι (J 2 5) * (θ hm5 0 (-1) * ι (Pinf 5 10) + 2 * ι (Pinf 10 10))) * hC
    + (4 * ι (Pinf 1 2) ^ 2 * ι (Pinf 5 10) ^ 2 * (ι (J 4 10) * ι (J 5 10))) * h1
    + (4 * ι (Pinf 1 2) ^ 2 * ι (Pinf 5 10) ^ 2 * (θ hm5 1 (-1) * ι (J 1 5))) * h2

/-- Lemma 23.1 at `q²`, rearranged for Entry 3.20. -/
lemma Q20 : (PowerSeries.X ^ 2 * Pinf 20 20 ^ 2 * Pinf 1 1 * Pinf 2 4 * Pinf 5 10
      + Pinf 5 5 * Pinf 10 10 * Pinf 10 20 ^ 3 * Pinf 2 2 * Pinf 1 2) * Pinf 2 4 ^ 4 =
    Pinf 2 2 ^ 2 * Pinf 1 1 * Pinf 2 4 * Pinf 5 10 * Pinf 10 20 ^ 2 := by
  apply mul_left_cancel₀ (Pinf_ne 20 20 (by norm_num) (by norm_num))
  have h := congrArg (S 2) P23_1
  simp only [map_mul, map_add, map_pow, show (S 2) PowerSeries.X = PowerSeries.X ^ 2 from RankProof.Ea_X 2 _,
    S_J 2 1 5 le_rfl (by norm_num), S_J 2 2 5 (by norm_num) (by norm_num), S_J 2 2 10 (by norm_num) (by norm_num),
    S_J 2 5 10 (by norm_num) (by norm_num), S_J 2 4 10 (by norm_num) (by norm_num),
    S_Pinf 2 2 2 (by norm_num) (by norm_num), S_Pinf 2 5 10 (by norm_num) (by norm_num),
    S_Pinf 2 10 10 (by norm_num) (by norm_num), S_Pinf 2 1 2 le_rfl (by norm_num)] at h
  simp only [J, Nat.reduceMul, Nat.reduceSub] at h ⊢
  simp (disch := norm_num) only [atom _ _ 40] at h ⊢
  simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
    add_zero, mul_one] at h ⊢
  linear_combination (-(Pinf 1 40 * Pinf 11 40 * Pinf 13 40 * Pinf 17 40 * Pinf 19 40 * Pinf 21 40 * Pinf 23 40 * Pinf 27 40 * Pinf 29 40 * Pinf 3 40 * Pinf 31 40 * Pinf 33 40 * Pinf 37 40 * Pinf 39 40 * Pinf 7 40 * Pinf 9 40 * Pinf 10 40 ^ 2 * Pinf 14 40 ^ 3 * Pinf 15 40 ^ 2 * Pinf 18 40 ^ 3 * Pinf 2 40 ^ 3 * Pinf 22 40 ^ 3 * Pinf 25 40 ^ 2 * Pinf 26 40 ^ 3 * Pinf 30 40 ^ 2 * Pinf 34 40 ^ 3 * Pinf 35 40 ^ 2 * Pinf 38 40 ^ 3 * Pinf 5 40 ^ 2 * Pinf 6 40 ^ 3)) * h

lemma cc_H : PowerSeries.constantCoeff H = 1 := by
  have h := congrArg PowerSeries.constantCoeff H_mul_vv
  rw [map_mul, vv, map_mul, cc_Pinf 2 5 (by norm_num) (by norm_num), cc_Pinf 3 5 (by norm_num) (by norm_num), map_one] at h
  simpa using h

/-- **Entry 3.20** (Watson 1933): `G(q)H(−q) + G(−q)H(q) = 2/χ²(−q²)`. -/
theorem entry_3_20 : G * Ng H + Ng G * H = 2 * Ring.inverse (chim 2 ^ 2) := by
  have hT0 := entry_3_21
  have hE2 : IsUnit (Pinf 2 2) := isUnit_Pinf 2 2 (by norm_num) (by norm_num)
  have hT : (G * Ng H - Ng G * H) * Pinf 2 2 = 2 * PowerSeries.X * S 10 (RamanujanTau.Septic.ramF 1 3) := by
    rw [hT0, fm, mul_assoc, Ring.inverse_mul_cancel _ hE2, mul_one]
  have hGH := GH_E
  have hGH' : Ng G * Ng H * (Pinf 2 2 * chip 1) = Pinf 10 10 * chip 5 := by
    have h := congrArg Ng hGH
    simp only [map_mul, Ng_E1, Ng_E5] at h
    exact h
  have hc1 := chip_mul 1
  have hc5 := chip_mul 5
  norm_num at hc1 hc5
  have hψ : S 10 (RamanujanTau.Septic.ramF 1 3) * Pinf 10 20 = Pinf 20 20 := by
    have h := congrArg (S 10) psi_mul
    rw [map_mul, S_Pinf 10 1 2 le_rfl (by norm_num), S_Pinf 10 2 2 (by norm_num) (by norm_num)] at h
    exact h
  have hc0 : chip 1 ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hc1; exact Pinf_ne 2 4 (by norm_num) (by norm_num) hc1.symm
  have Q' : (PowerSeries.X ^ 2 * S 10 (RamanujanTau.Septic.ramF 1 3) ^ 2 * Pinf 1 1 * chip 1
      + Pinf 5 5 * Pinf 10 10 * chip 5 * Pinf 2 2) * Pinf 2 4 ^ 4 = Pinf 2 2 ^ 2 * Pinf 1 1 * chip 1 := by
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (Pinf_ne 1 2 le_rfl (by norm_num)) (Pinf_ne 5 10 (by norm_num) (by norm_num)))
      (pow_ne_zero 2 (Pinf_ne 10 20 (by norm_num) (by norm_num))))
    linear_combination Q20
      + PowerSeries.X ^ 2 * Pinf 1 1 * Pinf 5 10 * Pinf 2 4 ^ 4 *
        ((S 10 (RamanujanTau.Septic.ramF 1 3) * Pinf 10 20) ^ 2 * hc1
          + Pinf 2 4 * (S 10 (RamanujanTau.Septic.ramF 1 3) * Pinf 10 20 + Pinf 20 20) * hψ)
      + Pinf 5 5 * Pinf 10 10 * Pinf 10 20 ^ 2 * Pinf 2 2 * Pinf 1 2 * Pinf 2 4 ^ 4 * hc5
      - Pinf 2 2 ^ 2 * Pinf 1 1 * Pinf 5 10 * Pinf 10 20 ^ 2 * hc1
  have hsq : ((G * Ng H + Ng G * H) * Pinf 2 4 ^ 2) ^ 2 = 4 := by
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 (Pinf_ne 2 2 (by norm_num) (by norm_num)))
      (Pinf_ne 1 1 le_rfl le_rfl)) hc0)
    linear_combination (Pinf 1 1 * chip 1 * Pinf 2 2 * Pinf 2 4 ^ 4 *
        ((G * Ng H - Ng G * H) * Pinf 2 2 + 2 * PowerSeries.X * S 10 (RamanujanTau.Septic.ramF 1 3))) * hT
      + 4 * Pinf 2 2 ^ 2 * Pinf 2 4 ^ 4 * (Ng G * Ng H * (Pinf 2 2 * chip 1)) * hGH
      + 4 * Pinf 2 2 ^ 2 * Pinf 2 4 ^ 4 * Pinf 5 5 * hGH' + 4 * Pinf 2 2 * Q'
  have hfac : ((G * Ng H + Ng G * H) * Pinf 2 4 ^ 2 - 2) * ((G * Ng H + Ng G * H) * Pinf 2 4 ^ 2 + 2) = 0 := by
    linear_combination hsq
  have hu : IsUnit (chim 2 ^ 2) := (isUnit_Pinf 2 4 (by norm_num) (by norm_num)).pow 2
  rcases mul_eq_zero.mp hfac with h | h
  · exact eq_mul_inv_of hu (by simp only [chim]; norm_num; linear_combination h)
  · exfalso
    have := congrArg PowerSeries.constantCoeff h
    simp only [map_add, map_mul, map_pow, map_ofNat, cc_Ng, cc_G, cc_H, cc_Pinf 2 4 (by norm_num) (by norm_num),
      map_zero] at this
    norm_num at this

end Forty
