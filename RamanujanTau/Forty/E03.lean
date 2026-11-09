/-
# Entry 3.3: `G(q)G(q⁴) − qH(q)H(q⁴) = φ(q⁵)/f(−q²)` (Watson 1933)

* Lemma 7.1 of Berndt et al.: `φ(q)² − φ(q⁵)² = 4q f(q,q⁹) f(q³,q⁷)`, here from the matrix exact cover
  `B = (1 2; −2 1)` of `φ(q)² = Σ_{x,y} q^{x²+y²}` (`L7_1`), turned into the product identity
  `(φ² − φ(q⁵)²) f(−q) f(−q⁴) = 4q f(−q²)² f(−q⁵) f(−q²⁰)` (`lemma71`).
* Watson's argument: `(GG₄ − qHH₄)² = (GG₄ + qHH₄)² − 4q GHG₄H₄`, Entry 3.2, `GH = f(−q⁵)/f(−q)`; the square root
  is fixed by the constant term.
-/
import RamanujanTau.Forty.E02
import RamanujanTau.Septic.ProductForm

set_option autoImplicit false

namespace Forty
open ALz HahnSeries Finset MTC
open RankProof (Pinf isUnit_Pinf)

private lemma hm2 : 1 ≤ 2 := by norm_num
private lemma hm10 : 1 ≤ 10 := by norm_num

/-- Entry 7.1: `B = (1 2; -2 1)`, shifts `i (1, 0)`, `i ∈ {(-2), (-1), 0, 1, 2}`. -/
def B7_1 : ECS where
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

theorem L7_1 : θ hm2 1 (-1) * θ hm2 1 (-1) = (θ hm10 5 (-1) * θ hm10 5 (-1)) + 2 * (mono 1 1 * (θ hm10 1 (-1) * θ hm10 3 (-1))) + 2 * (mono 1 1 * (θ hm10 3 (-1) * θ hm10 1 (-1))) := by
  have h := θθ_lattice hm2 hm2 hm10 hm10 1 1 (by norm_num : (-1 : ℂ) ≠ 0) (by norm_num : (-1 : ℂ) ≠ 0) B7_1 rfl rfl
    (by norm_num [B7_1]) (by norm_num [B7_1]) (by norm_num [B7_1])
  simp only [B7_1] at h
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton] at h
  norm_num [c2] at h
  simp only [θ_nfrm hm10 1 0 0 1 (e := 9) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm10 3 (-1) (-3) 1 (e := (-3)) (by norm_num) (by norm_num [c2]) (by norm_num), θ_nfrm hm10 3 0 0 1 (e := 7) (by norm_num) (by norm_num [c2]) (by norm_num), θ_sh hm10 3 1 (by norm_num : (-1 : ℂ) ≠ 0) (-3) 1 (e := 13) (by norm_num) (by norm_num [c2]) (by norm_num)] at h
  try simp only [← HahnSeries.single_neg, mul_assoc, θ_mono_comm, θ_mono_comm', mono_mono, mul_zero, zero_mul, add_zero, zero_add] at h
  try norm_num at h
  try simp only [mono_neg1] at h
  linear_combination h


/-- `L7_1` as a product identity (barred thetas cleared by `θ_bar`). -/
theorem P7_1 : (J 2 4 * J 2 4) ^ 2 * (J 5 10 ^ 2 * (J 1 10 * J 3 10))
      - (J 10 20 * J 10 20) ^ 2 * (J 1 2 ^ 2 * (J 1 10 * J 3 10))
      = 4 * PowerSeries.X * ((J 2 20 * J 10 20) * (J 6 20 * J 10 20)) * (J 1 2 ^ 2 * J 5 10 ^ 2) := by
  apply ι_inj
  have L := L7_1
  have hA := θ_bar hm2 1 le_rfl (by norm_num)
  have h5 := θ_bar hm10 5 (by norm_num) (by norm_num)
  have h1 := θ_bar hm10 1 le_rfl (by norm_num)
  have h3 := θ_bar hm10 3 (by norm_num) (by norm_num)
  norm_num at hA h5 h1 h3
  simp only [map_mul, map_sub, map_pow, map_ofNat, ι_X] at hA h5 h1 h3 ⊢
  linear_combination (ι (J 1 2) ^ 2 * ι (J 5 10) ^ 2 * ι (J 1 10) * ι (J 3 10)) * L
    - (ι (J 5 10) ^ 2 * ι (J 1 10) * ι (J 3 10) * (θ hm2 1 (-1) * ι (J 1 2) + ι (J 2 4) * ι (J 2 4))) * hA
    + (ι (J 1 2) ^ 2 * ι (J 1 10) * ι (J 3 10) * (θ hm10 5 (-1) * ι (J 5 10) + ι (J 10 20) * ι (J 10 20))) * h5
    + (4 * mono 1 1 * ι (J 1 2) ^ 2 * ι (J 5 10) ^ 2 * (ι (J 6 20) * ι (J 10 20))) * h1
    + (4 * mono 1 1 * ι (J 1 2) ^ 2 * ι (J 5 10) ^ 2 * (θ hm10 1 (-1) * ι (J 1 10))) * h3

lemma S_one (f : PowerSeries ℤ) : S 1 f = f := by
  simp only [S, RankProof.Ea]
  exact PowerSeries.expand_one_apply f

lemma Ng_Pfin22 (M : ℕ) : Ng (RankProof.Pfin 2 2 M) = RankProof.Pfin 2 2 M := by
  simp only [RankProof.Pfin, map_prod]
  refine prod_congr rfl fun i _ => ?_
  rw [map_sub, map_one, map_pow, Ng, PowerSeries.rescale_X, mul_pow, ← map_pow,
    show 2 + 2 * i = 2 * (1 + i) by ring, pow_mul]
  norm_num

lemma Ng_P22 : Ng (Pinf 2 2) = Pinf 2 2 := by
  refine RankProof.Pinf_ext (by norm_num) (by norm_num) fun N => ?_
  rw [← Ng_Pfin22 N, ← map_sub]
  exact Ng_X_pow_dvd (RankProof.X_pow_dvd_Pinf_sub 2 2 (by norm_num) (by norm_num) N)

/-- `φ(q) = χ(q)² f(−q²)`. -/
lemma phi_chip : RamanujanTau.Septic.phi = chip 1 ^ 2 * Pinf 2 2 := by
  rw [RamanujanTau.Septic.septic_product_forms.1]
  change Ng _ = _
  rw [map_mul, map_mul, Ng_P22, chip, S_one]
  ring

/-- `φ(q) J_{1,2} = J_{2,4}²`. -/
lemma phi_J : RamanujanTau.Septic.phi * J 1 2 = J 2 4 * J 2 4 := by
  rw [phi_chip]
  have hc := chip_mul 1
  norm_num at hc
  have a := atom 2 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [prod_range_succ, prod_range_zero, one_mul] at a
  norm_num at a
  simp only [J, Nat.reduceSub]
  rw [a]
  linear_combination (Pinf 2 4 ^ 2 * Pinf 4 4 ^ 2 * (chip 1 * Pinf 1 2 + Pinf 2 4)) * hc

/-- `φ(q⁵) J_{5,10} = J_{10,20}²`. -/
lemma phi5_J : S 5 RamanujanTau.Septic.phi * J 5 10 = J 10 20 * J 10 20 := by
  have h := congrArg (S 5) phi_J
  rw [map_mul, map_mul, S_J 5 1 2 le_rfl (by norm_num), S_J 5 2 4 (by norm_num) (by norm_num)] at h
  exact h

/-- **Lemma 7.1** of Berndt et al. (product form): `(φ(q)² − φ(q⁵)²) f(−q) f(−q⁴) = 4q f(−q²)² f(−q⁵) f(−q²⁰)`,
i.e. `φ² − φ(q⁵)² = 4q f²(−q¹⁰) χ(q)/χ(q⁵)`. -/
theorem lemma71 : (RamanujanTau.Septic.phi ^ 2 - S 5 RamanujanTau.Septic.phi ^ 2) * Pinf 1 1 * Pinf 4 4 =
    4 * PowerSeries.X * Pinf 2 2 ^ 2 * Pinf 5 5 * Pinf 20 20 := by
  have hK : J 1 2 ^ 2 * J 5 10 ^ 2 * (J 1 10 * J 3 10) ≠ 0 := by
    simp only [J]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)) (mul_ne_zero ?_ ?_) <;>
      exact mul_ne_zero (mul_ne_zero (Pinf_ne _ _ (by norm_num) (by norm_num)) (Pinf_ne _ _ (by norm_num) (by norm_num)))
        (Pinf_ne _ _ (by norm_num) (by norm_num))
  apply mul_left_cancel₀ hK
  have pJ := phi_J
  have p5 := phi5_J
  have P := P7_1
  have k : (J 2 20 * J 10 20) * (J 6 20 * J 10 20) * (Pinf 1 1 * Pinf 4 4) =
      J 1 10 * J 3 10 * (Pinf 2 2 ^ 2 * Pinf 5 5 * Pinf 20 20) := by
    simp only [J, Nat.reduceSub]
    simp (disch := norm_num) only [atom _ _ 20]
    simp only [prod_range_succ, prod_range_zero, one_mul, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, mul_zero,
      add_zero, mul_one]
    ring
  linear_combination (J 5 10 ^ 2 * J 1 10 * J 3 10 * Pinf 1 1 * Pinf 4 4 *
      (RamanujanTau.Septic.phi * J 1 2 + J 2 4 * J 2 4)) * pJ
    - (J 1 2 ^ 2 * J 1 10 * J 3 10 * Pinf 1 1 * Pinf 4 4 *
      (S 5 RamanujanTau.Septic.phi * J 5 10 + J 10 20 * J 10 20)) * p5
    + (Pinf 1 1 * Pinf 4 4) * P + (4 * PowerSeries.X * J 1 2 ^ 2 * J 5 10 ^ 2) * k

lemma GH_E : G * H * Pinf 1 1 = Pinf 5 5 := by
  have h1 := G_E
  have h2 := H_mul_vv
  simp only [J, vv, Nat.reduceSub] at h1 h2
  linear_combination H * h1 + Pinf 5 5 * h2

lemma SGH_E (a : ℕ) [NeZero a] : S a G * S a H * Pinf a a = Pinf (5 * a) (5 * a) := by
  have h := congrArg (S a) GH_E
  rw [map_mul, map_mul, S_Pinf a 1 1 le_rfl le_rfl, S_Pinf a 5 5 (by norm_num) (by norm_num), mul_one] at h
  rw [h, mul_comm a 5]

lemma cc_Pinf (b a : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a) : PowerSeries.constantCoeff (Pinf b a) = 1 := by
  have := (PowerSeries.X_pow_dvd_iff.mp (RankProof.X_pow_dvd_Pinf_sub b a hb ha 0)) 0 (by omega)
  rw [map_sub, sub_eq_zero, RankProof.Pfin] at this
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, this]
  simp

lemma cc_S (a : ℕ) [NeZero a] (f : PowerSeries ℤ) : PowerSeries.constantCoeff (S a f) = PowerSeries.constantCoeff f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [S, RankProof.coeff_Ea, dvd_zero, if_true, Nat.zero_div]

lemma cc_Ng (f : PowerSeries ℤ) : PowerSeries.constantCoeff (Ng f) = PowerSeries.constantCoeff f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Ng,
    PowerSeries.coeff_rescale]
  simp

lemma cc_G : PowerSeries.constantCoeff G = 1 := by
  have h := congrArg PowerSeries.constantCoeff G_mul_uu
  rw [map_mul, uu, map_mul, cc_Pinf 1 5 le_rfl (by norm_num), cc_Pinf 4 5 (by norm_num) (by norm_num), map_one] at h
  simpa using h

lemma cc_phi : PowerSeries.constantCoeff RamanujanTau.Septic.phi = 1 := by
  rw [phi_chip, map_mul, map_pow, chip, cc_S, cc_Ng, cc_Pinf 1 2 le_rfl (by norm_num), cc_Pinf 2 2 (by norm_num) (by norm_num)]
  norm_num

/-- **Entry 3.3** (Watson 1933): `G(q)G(q⁴) − qH(q)H(q⁴) = φ(q⁵)/f(−q²)`, with `φ(q) = Σ_{n∈ℤ} q^{n²}`. -/
theorem entry_3_3 : G * S 4 G - PowerSeries.X * H * S 4 H =
    S 5 RamanujanTau.Septic.phi * Ring.inverse (fm 2) := by
  have hb := entry_3_2
  have hphi := phi_chip
  have hGH := GH_E
  have hGH4 := SGH_E 4
  norm_num at hGH4
  have L := lemma71
  have hsq : ((G * S 4 G - PowerSeries.X * H * S 4 H) * Pinf 2 2) ^ 2 = (S 5 RamanujanTau.Septic.phi) ^ 2 := by
    apply mul_left_cancel₀ (mul_ne_zero (Pinf_ne 1 1 le_rfl le_rfl) (Pinf_ne 4 4 (by norm_num) (by norm_num)))
    linear_combination (Pinf 1 1 * Pinf 4 4 * Pinf 2 2 ^ 2 * (G * S 4 G + PowerSeries.X * H * S 4 H + chip 1 ^ 2)) * hb
      - (4 * PowerSeries.X * Pinf 2 2 ^ 2 * (S 4 G * S 4 H * Pinf 4 4)) * hGH
      - (4 * PowerSeries.X * Pinf 2 2 ^ 2 * Pinf 5 5) * hGH4
      - (Pinf 1 1 * Pinf 4 4 * (RamanujanTau.Septic.phi + chip 1 ^ 2 * Pinf 2 2)) * hphi + L
  have hfac : ((G * S 4 G - PowerSeries.X * H * S 4 H) * Pinf 2 2 - S 5 RamanujanTau.Septic.phi) *
      ((G * S 4 G - PowerSeries.X * H * S 4 H) * Pinf 2 2 + S 5 RamanujanTau.Septic.phi) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exact eq_mul_inv_of (isUnit_Pinf 2 2 (by norm_num) (by norm_num)) (by simp only [fm]; linear_combination h)
  · exfalso
    have := congrArg PowerSeries.constantCoeff h
    simp only [map_add, map_mul, map_sub, map_zero, cc_S, cc_G, cc_phi, cc_Pinf 2 2 (by norm_num) (by norm_num),
      PowerSeries.constantCoeff_X] at this
    norm_num at this

end Forty
