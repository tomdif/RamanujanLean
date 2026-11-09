/-
# Entry 3.17 (`q ↦ q²` form)

`4q{G(q²)G(q³⁸) + q⁸H(q²)H(q³⁸)} = χ²(q)χ²(q¹⁹) − χ²(−q)χ²(−q¹⁹) − 4q⁵/(χ²(−q²)χ²(−q³⁸))`.

This is Ramanujan's Entry 3.17 with `q` replaced by `q²`, which clears the `q^{1/2}`. Cao's proof: the form
`4x²+2xy+5y²+4x+y` with sign `(−1)^y` has exact covers of determinants 5 and 4 (`L3_17`, Cao (80), (81)). The
2-dissection `φ(q) = φ(q⁴) + 2qψ(q⁸)` (`MTC.dissect2`) then gives Cao (83).
-/
import RamanujanTau.Forty.E16

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm8 : 1 ≤ 8 := by norm_num
private lemma hm10 : 1 ≤ 10 := by norm_num
private lemma hm152 : 1 ≤ 152 := by norm_num
private lemma hm190 : 1 ≤ 190 := by norm_num

/-- Entry 3.17, side a: `B = (0 -5; 1 1)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B3_17a : ECS where
  b11 := 0
  b12 := (-5)
  b21 := 1
  b22 := 1
  r1 := 1
  r2 := 0
  I := {(-2), (-1), 0, 1, 2}
  det_ne := by norm_num
  cover := fun m n => ⟨((1 * m + 0 * n - (-2)) % 5 + (-2)), by simp only [mem_insert, mem_singleton]; omega,
    ((1 * (m - 1 * ((1 * m + 0 * n - (-2)) % 5 + (-2))) - (-5) * (n - 0 * ((1 * m + 0 * n - (-2)) % 5 + (-2)))) / 5), ((0 * (n - 0 * ((1 * m + 0 * n - (-2)) % 5 + (-2))) - 1 * (m - 1 * ((1 * m + 0 * n - (-2)) % 5 + (-2)))) / 5), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

/-- Entry 3.17, side b: `B = (1 -1; 0 4)`, shifts `i (0, 1)`, `i ∈ {(-1), 0, 1, 2}`. -/
def B3_17b : ECS where
  b11 := 1
  b12 := (-1)
  b21 := 0
  b22 := 4
  r1 := 0
  r2 := 1
  I := {(-1), 0, 1, 2}
  det_ne := by norm_num
  cover := fun m n => ⟨((0 * m + 1 * n - (-1)) % 4 + (-1)), by simp only [mem_insert, mem_singleton]; omega,
    ((4 * (m - 0 * ((0 * m + 1 * n - (-1)) % 4 + (-1))) - (-1) * (n - 1 * ((0 * m + 1 * n - (-1)) % 4 + (-1)))) / 4), ((1 * (n - 1 * ((0 * m + 1 * n - (-1)) % 4 + (-1))) - 0 * (m - 0 * ((0 * m + 1 * n - (-1)) % 4 + (-1)))) / 4), by omega, by omega⟩
  uniq := by
    intro i hi j hj u v u' v' h1 h2
    simp only [mem_insert, mem_singleton] at hi hj
    omega

theorem L3_17 : 2 * (θ hm10 4 1 * θ hm190 76 1) + 2 * (mono 8 1 * (θ hm10 2 1 * θ hm190 38 1)) = (θ hm8 0 (-1) * θ hm152 76 (-1)) - 2 * (mono 4 1 * (θ hm8 2 (-1) * θ hm152 38 (-1))) + (mono 18 1 * (θ hm8 4 (-1) * θ hm152 0 (-1))) := by
  have h := qf_two 4 1 5 4 1 0 1 B3_17a B3_17b
    hm10 hm190 hm8 hm152 (by norm_num [B3_17a]) (by norm_num [B3_17a]) (by norm_num [B3_17a])
    (by norm_num [B3_17b]) (by norm_num [B3_17b]) (by norm_num [B3_17b])
  simp only [B3_17a, B3_17b] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [qf0, qf1, qf2, c2] at h
  simp only [θ_nfr1 hm10 2 0 0 1 (e := 8) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm10 4 0 0 1 (e := 6) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm190 38 0 0 1 (e := 152) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfr1 hm190 76 0 0 1 (e := 114) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm152 38 0 0 1 (e := 114) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm8 2 0 0 1 (e := 6) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm152 0 1 (by norm_num : (-1 : ℂ) ≠ 0) 0 1 (e := 152) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm8 0 1 (by norm_num : (-1 : ℂ) ≠ 0) 0 1 (e := 8) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm8 2 1 (by norm_num : (-1 : ℂ) ≠ 0) (-2) 1 (e := 10) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm8 4 1 (by norm_num : (-1 : ℂ) ≠ 0) (-4) 1 (e := 12) (by norm_num) (by norm_num [c2]) (by norm_num), θz' hm10 1 (e := 10) (by norm_num), θz' hm190 0 (e := 0) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


private lemma hm2 : 1 ≤ 2 := by norm_num
private lemma hm38 : 1 ≤ 38 := by norm_num

/-- the 2-dissection `θ_N(e,c) = θ_{4N}(N+2e, −c²) + t^{N−e}(−c⁻¹) θ_{4N}(2e−N, −c²)`, numerals normalised. -/
lemma dis2 {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) (hMN : M = N * 2 * 2) (e : ℤ) {c : ℂ} (hc : c ≠ 0)
    (a b E : ℤ) (c' C : ℂ) (ha : a = N + 2 * e) (hb : b = 2 * e - N) (hE : E = N - e) (hc' : c' = -c ^ 2)
    (hC : C = -c⁻¹) : θ hN e c = θ hM a c' + mono E C * θ hM b c' := by
  rw [dissect2 hN e hc, θ_N' hMN.symm _ hM, θ_N' hMN.symm _ hM, ha, hb, hE, hc', hC]
  rw [show (mono 0 1 : L) = 1 from rfl, one_mul]

/-- Cao (79), in `ℂ((t))`. -/
theorem M3_17 : 4 * mono 1 1 * (θ hm10 4 1 * θ hm190 76 1 + mono 8 1 * (θ hm10 2 1 * θ hm190 38 1)) =
    θ hm2 1 (-1) * θ hm38 19 (-1) - θ hm2 1 1 * θ hm38 19 1 - 4 * mono 5 1 * (θ hm8 2 (-1) * θ hm152 38 (-1)) := by
  have hLat := L3_17
  have d1 := dis2 hm2 hm8 rfl 1 (by norm_num : (-1 : ℂ) ≠ 0) 4 0 1 (-1) 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have d2 := dis2 hm2 hm8 rfl 1 one_ne_zero 4 0 1 (-1) (-1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have d3 := dis2 hm38 hm152 rfl 19 (by norm_num : (-1 : ℂ) ≠ 0) 76 0 19 (-1) 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have d4 := dis2 hm38 hm152 rfl 19 one_ne_zero 76 0 19 (-1) (-1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [d1, d2, d3, d4, mono_neg1, mono_neg1]
  have m1 : (mono 1 1 : L) * mono 18 1 = mono 19 1 := by rw [mono_mul]; norm_num
  have m2 : (mono 1 1 : L) * mono 4 1 = mono 5 1 := by rw [mono_mul]; norm_num
  linear_combination (2 * mono 1 1) * hLat
    + (2 * θ hm8 4 (-1) * θ hm152 0 (-1)) * m1 - (4 * θ hm8 2 (-1) * θ hm152 38 (-1)) * m2

private lemma J_ne17 (e N : ℕ) (h1 : 1 ≤ e) (h2 : e < N) : J e N ≠ 0 :=
  mul_ne_zero (mul_ne_zero (Pinf_ne e N h1 (by omega)) (Pinf_ne (N - e) N (by omega) (by omega)))
    (Pinf_ne N N (by omega) (by omega))

private lemma ι_ne {f : PowerSeries ℤ} (h : f ≠ 0) : ι f ≠ 0 := fun h0 => h (ι_inj (h0.trans (map_zero ι).symm))

local notation "φ" => RamanujanTau.Septic.phi

lemma S19_chip1 : S 19 (chip 1) = chip 19 := by rw [chip, S_one]; rfl

/-- the product form of `M3_17`. -/
theorem P3_17 : 4 * PowerSeries.X * (J 4 10 * J 76 190 + PowerSeries.X ^ 8 * (J 2 10 * J 38 190)) * (J 2 8 * J 38 152) =
    (φ * S 19 φ - J 1 2 * J 19 38) * (J 2 8 * J 38 152)
      - 4 * PowerSeries.X ^ 5 * ((J 4 16 * J 8 16) * (J 76 304 * J 152 304)) := by
  apply ι_inj
  have h := M3_17
  have hA := θ_bar hm2 1 le_rfl (by norm_num)
  have hB := θ_bar hm38 19 (by norm_num) (by norm_num)
  have hC := θ_bar hm8 2 (by norm_num) (by norm_num)
  have hD := θ_bar hm152 38 (by norm_num) (by norm_num)
  norm_num at hA hB hC hD
  have pA := congrArg ι phi_J
  have pB0 := congrArg (S 19) phi_J
  rw [map_mul, map_mul, S_J' 19 1 2 le_rfl (by norm_num) (rfl : 19 = 19 * 1) (rfl : 38 = 19 * 2),
    S_J' 19 2 4 (by norm_num) (by norm_num) (rfl : 38 = 19 * 2) (rfl : 76 = 19 * 4)] at pB0
  have pB := congrArg ι pB0
  simp only [map_mul] at hA hB hC hD pA pB
  have iA : θ hm2 1 (-1) = ι φ := by
    apply mul_right_cancel₀ (ι_ne (J_ne17 1 2 le_rfl (by norm_num)))
    rw [hA, pA]
  have iB : θ hm38 19 (-1) = ι (S 19 φ) := by
    apply mul_right_cancel₀ (ι_ne (J_ne17 19 38 (by norm_num) (by norm_num)))
    rw [hB, pB]
  rw [iA, iB, θu' hm2 1 (e' := 1) (by norm_num) le_rfl (by norm_num),
    θu' hm38 19 (e' := 19) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 4 (e' := 4) (by norm_num) (by norm_num) (by norm_num),
    θu' hm10 2 (e' := 2) (by norm_num) (by norm_num) (by norm_num),
    θu' hm190 76 (e' := 76) (by norm_num) (by norm_num) (by norm_num),
    θu' hm190 38 (e' := 38) (by norm_num) (by norm_num) (by norm_num)] at h
  simp only [map_mul, map_sub, map_add, map_pow, map_ofNat, ι_X, ι_Xpow] at h ⊢
  push_cast at h ⊢
  have m5 : (mono 1 1 : L) ^ 5 = mono 5 1 := by rw [mono, single_pow]; norm_num
  have m9 : (mono 1 1 : L) * mono 8 1 = mono 1 1 ^ 9 := by rw [mono, mono, single_pow, mono_mul]; norm_num
  linear_combination (ι (J 2 8) * ι (J 38 152)) * h
    - 4 * mono 5 1 * (θ hm152 38 (-1) * ι (J 38 152)) * hC
    - 4 * mono 5 1 * (ι (J 4 16) * ι (J 8 16)) * hD
    + 4 * (ι (J 4 16) * ι (J 8 16) * ι (J 76 304) * ι (J 152 304)) * m5
    - 4 * (ι (J 2 10) * ι (J 38 190) * ι (J 2 8) * ι (J 38 152)) * m9

/-- **Entry 3.17** (Bressoud; with `q ↦ q²` to clear `q^{1/2}`):
`4q{G(q²)G(q³⁸) + q⁸H(q²)H(q³⁸)} = χ²(q)χ²(q¹⁹) − χ²(−q)χ²(−q¹⁹) − 4q⁵/(χ²(−q²)χ²(−q³⁸))`. -/
theorem entry_3_17 : 4 * PowerSeries.X * (S 2 G * S 38 G + PowerSeries.X ^ 8 * S 2 H * S 38 H) =
    chip 1 ^ 2 * chip 19 ^ 2 - chim 1 ^ 2 * chim 19 ^ 2
      - 4 * PowerSeries.X ^ 5 * Ring.inverse (chim 2 ^ 2 * chim 38 ^ 2) := by
  have e1 := SG_E 2
  have e2 := SH_E 2
  have e3 := SG_E 38
  have e4 := SH_E 38
  norm_num at e1 e2 e3 e4
  have hL : (S 2 G * S 38 G + PowerSeries.X ^ 8 * S 2 H * S 38 H) * (Pinf 2 2 * Pinf 38 38) =
      J 4 10 * J 76 190 + PowerSeries.X ^ 8 * (J 2 10 * J 38 190) := by
    linear_combination (S 38 G * Pinf 38 38) * e1 + J 4 10 * e3 + PowerSeries.X ^ 8 * (S 38 H * Pinf 38 38) * e2
      + PowerSeries.X ^ 8 * J 2 10 * e4
  have hφ := phi_chip
  have hφ19 := congrArg (S 19) phi_chip
  rw [map_mul, map_pow, S19_chip1, S_P' 19 2 2 (by norm_num) (by norm_num) (rfl : 38 = 19 * 2) (rfl : 38 = 19 * 2)] at hφ19
  have hJ1 : J 1 2 = chim 1 ^ 2 * Pinf 2 2 := by simp only [J, chim, Nat.reduceMul, Nat.reduceSub]; ring
  have hJ19 : J 19 38 = chim 19 ^ 2 * Pinf 38 38 := by simp only [J, chim, Nat.reduceMul, Nat.reduceSub]; ring
  have K1 : (Pinf 2 4 ^ 2 * Pinf 38 76 ^ 2) * ((J 4 16 * J 8 16) * (J 76 304 * J 152 304)) =
      (Pinf 2 2 * Pinf 38 38) * (J 2 8 * J 38 152) := by
    have k1 : J 4 16 * J 8 16 * Pinf 2 4 = Pinf 4 4 * J 2 8 := by
      simp only [J, Nat.reduceSub]
      simp (disch := norm_num) only [atom _ _ 16]
      simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
        add_zero, mul_one]
      ring
    have k2 := congrArg (S 19) k1
    simp only [map_mul, S_J' 19 4 16 (by norm_num) (by norm_num) (rfl : 76 = 19 * 4) (rfl : 304 = 19 * 16),
      S_J' 19 8 16 (by norm_num) (by norm_num) (rfl : 152 = 19 * 8) (rfl : 304 = 19 * 16),
      S_J' 19 2 8 (by norm_num) (by norm_num) (rfl : 38 = 19 * 2) (rfl : 152 = 19 * 8),
      S_P' 19 2 4 (by norm_num) (by norm_num) (rfl : 38 = 19 * 2) (rfl : 76 = 19 * 4),
      S_P' 19 4 4 (by norm_num) (by norm_num) (rfl : 76 = 19 * 4) (rfl : 76 = 19 * 4)] at k2
    have a2 := atom 2 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have a38 := atom 38 38 76 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simp only [prod_range_succ, prod_range_zero, one_mul] at a2 a38
    norm_num at a2 a38
    rw [a2, a38]
    linear_combination (Pinf 2 4 * Pinf 38 76 * (Pinf 38 76 * J 76 304 * J 152 304)) * k1
      + (Pinf 2 4 * Pinf 38 76 * Pinf 4 4 * J 2 8) * k2
  have hW : IsUnit (chim 2 ^ 2 * chim 38 ^ 2) :=
    ((isUnit_Pinf 2 4 (by norm_num) (by norm_num)).pow 2).mul ((isUnit_Pinf 38 76 (by norm_num) (by norm_num)).pow 2)
  have hinv := Ring.inverse_mul_cancel _ hW
  simp only [chim, Nat.reduceMul] at hinv hJ1 hJ19 ⊢
  have P := P3_17
  have hK : (Pinf 2 2 * Pinf 38 38) * (Pinf 2 4 ^ 2 * Pinf 38 76 ^ 2) * (J 2 8 * J 38 152) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (Pinf_ne 2 2 (by norm_num) (by norm_num)) (Pinf_ne 38 38 (by norm_num) (by norm_num)))
      (mul_ne_zero (pow_ne_zero 2 (Pinf_ne 2 4 (by norm_num) (by norm_num))) (pow_ne_zero 2 (Pinf_ne 38 76 (by norm_num) (by norm_num)))))
      (mul_ne_zero (J_ne17 2 8 (by norm_num) (by norm_num)) (J_ne17 38 152 (by norm_num) (by norm_num)))
  apply mul_left_cancel₀ hK
  rw [hφ19, hφ, hJ1, hJ19] at P
  linear_combination (4 * PowerSeries.X * (Pinf 2 4 ^ 2 * Pinf 38 76 ^ 2) * (J 2 8 * J 38 152)) * hL
    + (Pinf 2 4 ^ 2 * Pinf 38 76 ^ 2) * P
    - 4 * PowerSeries.X ^ 5 * K1
    + 4 * PowerSeries.X ^ 5 * (Pinf 2 2 * Pinf 38 38) * (J 2 8 * J 38 152) * hinv

end Forty
