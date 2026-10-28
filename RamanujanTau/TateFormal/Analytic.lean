import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import RamanujanTau.TateFormal.Regroup

/-!
# The Weierstrass `℘`-function of the lattice `ℤτ + ℤ` as a `q`-series

For `0 < Im z < Im τ`, with `u = e^{2πiz}`, `q = e^{2πiτ}`, `S_j(w) = Σ_{d ≥ 0} d^j w^d`:
* `℘(z) = (2πi)² (S₁(u) + 1/12 + Σ_{k ≥ 1} (S₁(u qᵏ) + S₁(u⁻¹ qᵏ) − 2 S₁(qᵏ)))`,
* `℘'(z) = (2πi)³ (S₂(u) + Σ_{k ≥ 1} (S₂(u qᵏ) − S₂(u⁻¹ qᵏ)))`,
* `g₂ = (2πi)⁴ E₄ / 12`, `g₃ = −(2πi)⁶ E₆ / 216`.
-/

set_option autoImplicit false

noncomputable section

namespace TateFormal

open Complex PeriodPair Real
open scoped Nat ArithmeticFunction.sigma

/-- `S j w = Σ_{d ≥ 0} d^j w^d`. -/
def S (j : ℕ) (w : ℂ) : ℂ := ∑' d : ℕ, (d : ℂ) ^ j * w ^ d

/-- `e w = exp(2πi w)`. -/
abbrev e (w : ℂ) : ℂ := cexp (2 * π * I * w)

lemma row (k : ℕ) (hk : 1 ≤ k) (w : ℂ) (hw : 0 < w.im) :
    HasSum (fun n : ℤ => 1 / (w + n) ^ (k + 1)) (((-2 * π * I) ^ (k + 1) / k !) * S k (e w)) := by
  have h := EisensteinSeries.qExpansion_identity hk ⟨w, hw⟩
  have hs : Summable (fun n : ℤ => 1 / (w + n) ^ (k + 1)) := by
    have := EisensteinSeries.linear_right_summable w 1 (k := ((k + 1 : ℕ) : ℤ)) (by omega)
    refine this.congr fun n => ?_
    rw [one_div, Int.cast_one, one_mul, zpow_natCast]
  convert hs.hasSum using 1
  rw [h]; rfl

lemma row_neg (k : ℕ) (hk : 1 ≤ k) (w : ℂ) (hw : 0 < w.im) :
    HasSum (fun n : ℤ => 1 / (w - n) ^ (k + 1)) (((-2 * π * I) ^ (k + 1) / k !) * S k (e w)) := by
  have := (Equiv.neg ℤ).hasSum_iff.mpr (row k hk w hw)
  convert this using 2 with n
  simp [sub_eq_add_neg]

lemma indep (τ : UpperHalfPlane) : LinearIndependent ℝ ![(τ : ℂ), 1] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  have hs : s = 0 := by
    rcases him with h | h
    · exact h
    · exact absurd h τ.im_pos.ne'
  subst hs
  simp at hre
  exact ⟨rfl, hre⟩

/-- the lattice `ℤτ + ℤ`. -/
def Lτ (τ : UpperHalfPlane) : PeriodPair := ⟨τ, 1, indep τ⟩

variable (τ : UpperHalfPlane) (z : ℂ)

lemma hasSum_wp :
    HasSum (fun x : ℤ × ℤ => 1 / (z - (x.1 * (τ : ℂ) + x.2)) ^ 2 - 1 / (x.1 * (τ : ℂ) + x.2) ^ 2)
      (℘[Lτ τ] z) := by
  have h := (Lτ τ).hasSum_weierstrassP z
  have := ((Lτ τ).latticeEquivProd.symm.toEquiv.hasSum_iff).mpr h
  convert this using 2 with x
  simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, latticeEquiv_symm_apply]
  simp [Lτ]

lemma hasSum_dwp :
    HasSum (fun x : ℤ × ℤ => -2 / (z - (x.1 * (τ : ℂ) + x.2)) ^ 3) (℘'[Lτ τ] z) := by
  have h := (Lτ τ).hasSum_derivWeierstrassP z
  have := ((Lτ τ).latticeEquivProd.symm.toEquiv.hasSum_iff).mpr h
  convert this using 2 with x
  simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, latticeEquiv_symm_apply]
  simp [Lτ]

/-- `K j = (-2πi)^(j+1)/j!`. -/
abbrev K (j : ℕ) : ℂ := (-2 * π * I) ^ (j + 1) / j !

/-- the row sums of `1/(z - l)²`. -/
def Arow (m : ℤ) : ℂ := if 0 < m then K 1 * S 1 (e (m * τ - z)) else K 1 * S 1 (e (z - m * τ))

lemma im_mul_tau (m : ℤ) : ((m : ℂ) * τ).im = m * τ.im := by simp

variable {z}

lemma hasSum_Arow (hz0 : 0 < z.im) (hz1 : z.im < τ.im) (m : ℤ) :
    HasSum (fun n : ℤ => 1 / (z - (m * (τ : ℂ) + n)) ^ 2) (Arow τ z m) := by
  rw [Arow]
  split_ifs with hm
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hw : 0 < ((m : ℂ) * τ - z).im := by
      rw [Complex.sub_im, im_mul_tau]; nlinarith [τ.im_pos]
    convert row 1 le_rfl _ hw using 2 with n
    ring
  · have hm1 : (m : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp hm
    have hw : 0 < (z - (m : ℂ) * τ).im := by
      rw [Complex.sub_im, im_mul_tau]; nlinarith [τ.im_pos]
    convert row_neg 1 le_rfl _ hw using 2 with n
    ring

/-- the row sums of `1/l²`. -/
def Brow (m : ℤ) : ℂ := if m = 0 then π ^ 2 / 3 else K 1 * S 1 (e (m.natAbs * τ))

lemma hasSum_Brow (m : ℤ) : HasSum (fun n : ℤ => 1 / (m * (τ : ℂ) + n) ^ 2) (Brow τ m) := by
  rw [Brow]
  split_ifs with hm
  · subst hm
    have hs := EisensteinSeries.linear_right_summable (0 : ℂ) 1 (k := 2) le_rfl
    have h2 := two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (k := 2) le_rfl even_two
    push_cast at h2
    rw [riemannZeta_two] at h2
    have : HasSum (fun n : ℤ => ((n : ℂ) ^ 2)⁻¹) (π ^ 2 / 3) := by
      have hs' : Summable (fun n : ℤ => ((n : ℂ) ^ 2)⁻¹) := hs.congr fun n => by simp [zpow_two, sq]
      convert hs'.hasSum using 1
      rw [← h2]; ring
    simpa [one_div] using this
  · rcases lt_or_gt_of_ne hm with hm | hm
    · have hc : ((m.natAbs : ℕ) : ℂ) = -(m : ℂ) := by
        rw [Nat.cast_natAbs, abs_of_neg hm, Int.cast_neg]
      have hm1 : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
      have hw : 0 < ((m.natAbs : ℂ) * τ).im := by
        rw [hc, neg_mul, Complex.neg_im, im_mul_tau]; nlinarith [τ.im_pos]
      convert row_neg 1 le_rfl _ hw using 2 with n
      rw [hc]; ring
    · have hc : ((m.natAbs : ℕ) : ℂ) = (m : ℂ) := by
        rw [Nat.cast_natAbs, abs_of_pos hm]
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hw : 0 < ((m.natAbs : ℂ) * τ).im := by
        rw [hc, im_mul_tau]; nlinarith [τ.im_pos]
      convert row 1 le_rfl _ hw using 2 with n
      rw [hc]

lemma hasSum_rows (hz0 : 0 < z.im) (hz1 : z.im < τ.im) :
    HasSum (fun m : ℤ => Arow τ z m - Brow τ m) (℘[Lτ τ] z) :=
  (hasSum_wp τ z).prod_fiberwise fun m => (hasSum_Arow τ hz0 hz1 m).sub (hasSum_Brow τ m)

lemma norm_e (w : ℂ) : ‖e w‖ = Real.exp (-2 * π * w.im) := by
  rw [e, Complex.norm_exp]; congr 1; simp

lemma e_add_nat (k : ℕ) (w : ℂ) : e (w + k * τ) = e w * e τ ^ k := by
  rw [e, e, e, ← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; ring

lemma e_nat_mul (k : ℕ) : e (k * τ) = e τ ^ k := by
  rw [e, e, ← Complex.exp_nat_mul]; congr 1; ring

lemma e_nat_sub (k : ℕ) (w : ℂ) : e (k * τ - w) = e τ ^ k * (e w)⁻¹ := by
  rw [e, e, e, ← Complex.exp_nat_mul, ← Complex.exp_neg, ← Complex.exp_add]; congr 1; ring

/-- `T j w = Σ_{k ≥ 0} S_j(w q^{k+1})`. -/
def T (j : ℕ) (w : ℂ) : ℂ := ∑' k : ℕ, ∑' d : ℕ, (d : ℂ) ^ j * (w * e τ ^ (k + 1)) ^ d

lemma nu_pos : 0 < ‖e z‖ := by rw [norm_e]; exact Real.exp_pos _

lemma nu_lt (hz0 : 0 < z.im) : ‖e z‖ < 1 := by
  rw [norm_e, ← Real.exp_zero]; apply Real.exp_lt_exp.mpr; nlinarith [Real.pi_pos]

lemma nq_lt_nu (hz1 : z.im < τ.im) : ‖e τ‖ < ‖e z‖ := by
  rw [norm_e, norm_e, UpperHalfPlane.coe_im]; apply Real.exp_lt_exp.mpr; nlinarith [Real.pi_pos]

lemma r_lt (hz1 : z.im < τ.im) : ‖e τ‖ / ‖e z‖ < 1 := (div_lt_one nu_pos).mpr (nq_lt_nu τ hz1)

lemma hq_le (hz0 : 0 < z.im) : ‖e τ‖ ≤ ‖e τ‖ / ‖e z‖ :=
  le_div_self (norm_nonneg _) nu_pos (nu_lt hz0).le

lemma hasSum_T (hz0 : 0 < z.im) (hz1 : z.im < τ.im) (j : ℕ) (hj : 1 ≤ j) (w : ℂ)
    (hw : ‖w‖ * ‖e τ‖ ≤ ‖e τ‖ / ‖e z‖) :
    HasSum (fun k : ℕ => S j (w * e τ ^ (k + 1))) (T τ j w) :=
  hasSum_k j hj (r_lt τ hz1) (hq_le τ hz0) hw

lemma hw_u (hz0 : 0 < z.im) : ‖e z‖ * ‖e τ‖ ≤ ‖e τ‖ / ‖e z‖ :=
  (mul_le_of_le_one_left (norm_nonneg _) (nu_lt hz0).le).trans (hq_le τ hz0)

lemma hw_inv : ‖(e z)⁻¹‖ * ‖e τ‖ ≤ ‖e τ‖ / ‖e z‖ := by
  rw [norm_inv, inv_mul_eq_div]

lemma hw_one (hz0 : 0 < z.im) : ‖(1 : ℂ)‖ * ‖e τ‖ ≤ ‖e τ‖ / ‖e z‖ := by
  rw [norm_one, one_mul]; exact hq_le τ hz0

/-- **`℘` as a `q`-series**. -/
theorem wp_formula (hz0 : 0 < z.im) (hz1 : z.im < τ.im) :
    ℘[Lτ τ] z = K 1 * (S 1 (e z) + T τ 1 (e z) + T τ 1 (e z)⁻¹ - 2 * T τ 1 1) - π ^ 2 / 3 := by
  -- the `A`-rows
  have hA1 : HasSum (fun k : ℕ => Arow τ z (-(k : ℤ))) (K 1 * (S 1 (e z) + T τ 1 (e z))) := by
    have h := (hasSum_T τ hz0 hz1 1 le_rfl (e z) (hw_u τ hz0)).mul_left (K 1)
    rw [← hasSum_nat_add_iff' 1]
    convert h using 1
    · funext k
      simp only [Arow]
      rw [if_neg (by omega)]
      congr 2
      rw [← e_add_nat]; congr 1; push_cast; ring
    · simp [Arow]; ring
  have hA2 : HasSum (fun k : ℕ => Arow τ z (-(-((k : ℤ) + 1)))) (K 1 * T τ 1 (e z)⁻¹) := by
    have h := (hasSum_T τ hz0 hz1 1 le_rfl (e z)⁻¹ (hw_inv τ)).mul_left (K 1)
    convert h using 1
    funext k
    simp only [Arow, neg_neg]
    rw [if_pos (by omega)]
    congr 2
    rw [show (((k : ℤ) + 1 : ℤ) : ℂ) = ((k + 1 : ℕ) : ℂ) by push_cast; ring, e_nat_sub]; ring
  have hA : HasSum (Arow τ z) (K 1 * (S 1 (e z) + T τ 1 (e z)) + K 1 * T τ 1 (e z)⁻¹) := by
    have := HasSum.of_nat_of_neg_add_one (f := fun m : ℤ => Arow τ z (-m)) hA1 hA2
    have := (Equiv.neg ℤ).hasSum_iff.mpr this
    simpa [Function.comp_def] using this
  -- the `B`-rows
  have hB1 : HasSum (fun k : ℕ => Brow τ (k : ℤ)) (π ^ 2 / 3 + K 1 * T τ 1 1) := by
    have h := (hasSum_T τ hz0 hz1 1 le_rfl 1 (hw_one τ hz0)).mul_left (K 1)
    rw [← hasSum_nat_add_iff' 1]
    convert h using 1
    · funext k
      simp only [Brow]
      rw [if_neg (by omega)]
      congr 2
      rw [one_mul, show (((k + 1 : ℕ) : ℤ)).natAbs = k + 1 from rfl, e_nat_mul]
    · simp [Brow]
  have hB2 : HasSum (fun k : ℕ => Brow τ (-((k : ℤ) + 1))) (K 1 * T τ 1 1) := by
    have h := (hasSum_T τ hz0 hz1 1 le_rfl 1 (hw_one τ hz0)).mul_left (K 1)
    convert h using 1
    funext k
    simp only [Brow]
    rw [if_neg (by omega)]
    congr 2
    rw [one_mul, Int.natAbs_neg, show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; rfl,
      show (((k + 1 : ℕ) : ℤ)).natAbs = k + 1 from rfl, e_nat_mul]
  have hB := HasSum.of_nat_of_neg_add_one hB1 hB2
  have := (hasSum_rows τ hz0 hz1).unique (hA.sub hB)
  rw [this]; ring

/-- the row sums of `-2/(z - l)³`. -/
def A'row (z : ℂ) (m : ℤ) : ℂ :=
  if 0 < m then 2 * K 2 * S 2 (e (m * τ - z)) else -2 * K 2 * S 2 (e (z - m * τ))

lemma hasSum_A'row (hz0 : 0 < z.im) (hz1 : z.im < τ.im) (m : ℤ) :
    HasSum (fun n : ℤ => -2 / (z - (m * (τ : ℂ) + n)) ^ 3) (A'row τ z m) := by
  rw [A'row]
  split_ifs with hm
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hw : 0 < ((m : ℂ) * τ - z).im := by
      rw [Complex.sub_im, im_mul_tau]; nlinarith [τ.im_pos]
    convert (row 2 (by norm_num) _ hw).mul_left 2 using 1
    · funext n
      rw [show z - ((m : ℂ) * τ + n) = -((m : ℂ) * τ - z + n) by ring, Odd.neg_pow (by decide),
        div_neg]
      ring
    · ring
  · have hm1 : (m : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp hm
    have hw : 0 < (z - (m : ℂ) * τ).im := by
      rw [Complex.sub_im, im_mul_tau]; nlinarith [τ.im_pos]
    convert (row_neg 2 (by norm_num) _ hw).mul_left (-2) using 1
    · funext n
      rw [show z - ((m : ℂ) * τ + n) = (z - (m : ℂ) * τ - n) by ring]
      ring
    · ring

/-- **`℘'` as a `q`-series**. -/
theorem dwp_formula (hz0 : 0 < z.im) (hz1 : z.im < τ.im) :
    ℘'[Lτ τ] z = -2 * K 2 * (S 2 (e z) + T τ 2 (e z) - T τ 2 (e z)⁻¹) := by
  have hA1 : HasSum (fun k : ℕ => A'row τ z (-(k : ℤ))) (-2 * K 2 * (S 2 (e z) + T τ 2 (e z))) := by
    have h := (hasSum_T τ hz0 hz1 2 (by norm_num) (e z) (hw_u τ hz0)).mul_left (-2 * K 2)
    rw [← hasSum_nat_add_iff' 1]
    convert h using 1
    · funext k
      simp only [A'row]
      rw [if_neg (by omega)]
      congr 2
      rw [← e_add_nat]; congr 1; push_cast; ring
    · simp [A'row]; ring
  have hA2 : HasSum (fun k : ℕ => A'row τ z (-(-((k : ℤ) + 1)))) (2 * K 2 * T τ 2 (e z)⁻¹) := by
    have h := (hasSum_T τ hz0 hz1 2 (by norm_num) (e z)⁻¹ (hw_inv τ)).mul_left (2 * K 2)
    convert h using 1
    funext k
    simp only [A'row, neg_neg]
    rw [if_pos (by omega)]
    congr 2
    rw [show (((k : ℤ) + 1 : ℤ) : ℂ) = ((k + 1 : ℕ) : ℂ) by push_cast; ring, e_nat_sub]; ring
  have hA : HasSum (A'row τ z) (-2 * K 2 * (S 2 (e z) + T τ 2 (e z)) + 2 * K 2 * T τ 2 (e z)⁻¹) := by
    have := HasSum.of_nat_of_neg_add_one (f := fun m : ℤ => A'row τ z (-m)) hA1 hA2
    have := (Equiv.neg ℤ).hasSum_iff.mpr this
    simpa [Function.comp_def] using this
  have := ((hasSum_dwp τ z).prod_fiberwise fun m => hasSum_A'row τ hz0 hz1 m).unique hA
  rw [this]; ring

/-- the lattice sums `G_k` as `q`-series. -/
lemma G_eq (k : ℕ) (hk : 3 ≤ k) (hk2 : Even k) :
    (Lτ τ).G k = 2 * riemannZeta k + 2 * ((-2 * π * I) ^ k / (k - 1)!) *
      ∑' n : ℕ+, (σ (k - 1) n : ℂ) * e τ ^ (n : ℕ) := by
  rw [← tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow hk hk2 τ, PeriodPair.G,
    ← (Lτ τ).latticeEquivProd.symm.toEquiv.tsum_eq, ← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  congr 1; funext v
  simp only [LinearEquiv.coe_toEquiv, latticeEquiv_symm_apply, EisensteinSeries.eisSummand,
    finTwoArrowEquiv_symm_apply]
  simp [Lτ, zpow_neg, zpow_natCast]

lemma not_mem_lattice (hz0 : 0 < z.im) (hz1 : z.im < τ.im) : z ∉ (Lτ τ).lattice := by
  rw [mem_lattice]
  rintro ⟨m, n, h⟩
  have him := congrArg Complex.im h
  simp [Lτ] at him
  rw [← him] at hz0 hz1
  have h1 : (0 : ℝ) < m := by
    by_contra hc; rw [not_lt] at hc; nlinarith [τ.im_pos]
  have h2 : (m : ℝ) < 1 := by
    by_contra hc; rw [not_lt] at hc; nlinarith [τ.im_pos]
  have h1' : (0 : ℤ) < m := by exact_mod_cast h1
  have h2' : m < (1 : ℤ) := by exact_mod_cast h2
  omega

lemma bernoulli_six' : bernoulli 6 = 1 / 42 := by decide +kernel

lemma zeta_six : riemannZeta 6 = π ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  push_cast at h
  rw [show (2 : ℂ) * 3 = 6 by norm_num, bernoulli_six'] at h
  rw [h]; norm_num [Nat.factorial]; ring

lemma K1_eq : K 1 = -4 * π ^ 2 := by
  simp only [K]; norm_num; linear_combination (4 * (π : ℂ) ^ 2) * I_sq
lemma K2_eq : K 2 = 4 * π ^ 3 * I := by
  simp only [K]; norm_num [Nat.factorial]; linear_combination (-4 * (π : ℂ) ^ 3 * I) * I_sq
lemma c4_eq : (-2 * π * I : ℂ) ^ 4 = 16 * π ^ 4 := by
  linear_combination (16 * (π : ℂ) ^ 4 * (I ^ 2 - 1)) * I_sq
lemma c6_eq : (-2 * π * I : ℂ) ^ 6 = -64 * π ^ 6 := by
  linear_combination (64 * (π : ℂ) ^ 6 * (I ^ 4 - I ^ 2 + 1)) * I_sq

/-- **the Weierstrass equation for the `q`-series** (`0 < Im z < Im τ`, `u = e z`, `q = e τ`):
`Q² = 4X³ + X² − 20 s₃ X − (5 s₃ + 7 s₅)/3` with `X = ℘/(2πi)² − 1/12`, `Q = ℘'/(2πi)³`. -/
theorem weierstrass_q (hz0 : 0 < z.im) (hz1 : z.im < τ.im) :
    (S 2 (e z) + T τ 2 (e z) - T τ 2 (e z)⁻¹) ^ 2 =
      4 * (S 1 (e z) + T τ 1 (e z) + T τ 1 (e z)⁻¹ - 2 * T τ 1 1) ^ 3 +
      (S 1 (e z) + T τ 1 (e z) + T τ 1 (e z)⁻¹ - 2 * T τ 1 1) ^ 2 -
      20 * (∑' n : ℕ+, (σ 3 n : ℂ) * e τ ^ (n : ℕ)) *
        (S 1 (e z) + T τ 1 (e z) + T τ 1 (e z)⁻¹ - 2 * T τ 1 1) -
      (5 * (∑' n : ℕ+, (σ 3 n : ℂ) * e τ ^ (n : ℕ)) + 7 * (∑' n : ℕ+, (σ 5 n : ℂ) * e τ ^ (n : ℕ))) / 3 := by
  have h := (Lτ τ).derivWeierstrassP_sq z (not_mem_lattice τ hz0 hz1)
  rw [wp_formula τ hz0 hz1, dwp_formula τ hz0 hz1, PeriodPair.g₂, PeriodPair.g₃,
    G_eq τ 4 (by norm_num) (by decide), G_eq τ 6 (by norm_num) (by decide), K1_eq, K2_eq] at h
  push_cast at h
  rw [riemannZeta_four, zeta_six, c4_eq, c6_eq] at h
  norm_num [Nat.factorial] at h
  set X := S 1 (e z) + T τ 1 (e z) + T τ 1 (e z)⁻¹ - 2 * T τ 1 1
  set Q := S 2 (e z) + T τ 2 (e z) - T τ 2 (e z)⁻¹
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  apply mul_left_cancel₀ (pow_ne_zero 6 hπ)
  linear_combination (-1 / 64 : ℂ) * h + (π ^ 6 * Q ^ 2) * I_sq

end TateFormal
