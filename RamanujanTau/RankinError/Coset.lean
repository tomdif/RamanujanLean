/-
# The lattice theta function as a sum over `Γ∞\SL₂(ℤ)`

* `tsum_strip_eq`: for `T`-invariant `H ≥ 0`,
  `∑_{γ ∈ SL₂(ℤ)} 1_{[0,1)}(Re γz) H(γz) = ∑_{(a,c) coprime} H(M(a,c)⁻¹ z)`
  (`HoroUnfold.slEquiv` applied to `γ⁻¹`; exactly one translate `T^{−k}w` lies in the strip);
* `tsum_theta_split`: `ℤ² ∖ 0 = ℕ₊ × {coprime}`, so
  `∑_{(m,n)} e^{−πtQ(m,n)} = 1 + ∑_{g ≥ 1} ∑_{(a,c)} e^{−πt g² Q(−c,a)}`;
* `theta_coset`: `Θ_z(t) = 1 + ∑_γ 1_{strip}(γz) h_t(Im γz)`, `h_t(v) = ∑_{g≥1} e^{−πtg²/v}`.
-/
import RamanujanTau.RankinError.HMeasure

set_option autoImplicit false

namespace RamanujanTau.RankinError

open Real Filter Topology MeasureTheory Set ModularGroup
open RamanujanTau.RankinSelberg RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal

/-- The strip `0 ≤ Re w < 1`. -/
def strip : Set ℍ := {w | 0 ≤ w.re ∧ w.re < 1}

lemma measurableSet_strip : MeasurableSet strip :=
  (measurableSet_le measurable_const measurable_re_H).inter
    (measurableSet_lt measurable_re_H measurable_const)

lemma re_T_zpow_smul (k : ℤ) (w : ℍ) : (T ^ k • w).re = k + w.re := by
  rw [modular_T_zpow_smul, UpperHalfPlane.vadd_re]

lemma im_T_zpow_smul (k : ℤ) (w : ℍ) : (T ^ k • w).im = w.im := by
  rw [modular_T_zpow_smul, UpperHalfPlane.vadd_im]

lemma tsum_strip (w : ℍ) : ∑' k : ℤ, strip.indicator (1 : ℍ → ℝ≥0∞) (T ^ (-k) • w) = 1 := by
  have hmem : ∀ k : ℤ, T ^ (-k) • w ∈ strip ↔ k = ⌊w.re⌋ := by
    intro k
    simp only [strip, mem_setOf_eq, re_T_zpow_smul]
    rw [eq_comm, Int.floor_eq_iff]
    push_cast
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [tsum_eq_single ⌊w.re⌋ (fun k hk => indicator_of_notMem (fun h => hk ((hmem k).1 h)) _)]
  rw [indicator_of_mem ((hmem _).2 rfl)]
  rfl

/-- **Coset sum.** -/
theorem tsum_strip_eq (H : ℍ → ℝ≥0∞) (hH : ∀ (k : ℤ) (w : ℍ), H (T ^ k • w) = H w) (z : ℍ) :
    ∑' γ : SL(2, ℤ), strip.indicator (1 : ℍ → ℝ≥0∞) (γ • z) * H (γ • z) =
      ∑' p : copSet, H ((mat p)⁻¹ • z) := by
  rw [← (Equiv.inv (SL(2, ℤ))).tsum_eq
    (fun γ => strip.indicator (1 : ℍ → ℝ≥0∞) (γ • z) * H (γ • z))]
  rw [← slEquiv.symm.tsum_eq, ENNReal.tsum_prod']
  refine tsum_congr fun p => ?_
  have e : ∀ k : ℤ, (Equiv.inv (SL(2, ℤ))) (slEquiv.symm (p, k)) = T ^ (-k) * (mat p)⁻¹ := by
    intro k
    simp [slEquiv, mul_inv_rev, zpow_neg]
  simp_rw [e, mul_smul, hH]
  rw [ENNReal.tsum_mul_right, tsum_strip, one_mul]

lemma inv_mat_10 (p : copSet) : ((mat p)⁻¹ : SL(2, ℤ)) 1 0 = -p.1.2 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [mat]

lemma inv_mat_11 (p : copSet) : ((mat p)⁻¹ : SL(2, ℤ)) 1 1 = p.1.1 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [mat]

lemma Qf_eq_normSq (z : ℍ) (m n : ℤ) :
    Qf z.re z.im (m, n) = Complex.normSq ((m : ℂ) * z + n) / z.im := by
  have hy := z.im_pos
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    Complex.add_im, Complex.mul_im, zero_mul, sub_zero, add_zero]
  unfold Qf
  simp only [UpperHalfPlane.re, UpperHalfPlane.im] at hy ⊢
  field_simp
  ring

lemma im_inv_mat_smul (p : copSet) (z : ℍ) :
    ((mat p)⁻¹ • z).im = 1 / Qf z.re z.im (-p.1.2, p.1.1) := by
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply, inv_mat_10, inv_mat_11,
    Qf_eq_normSq]
  have hN : Complex.normSq ((((-p.1.2 : ℤ)) : ℂ) * z + (p.1.1 : ℤ)) ≠ 0 := by
    rw [Ne, Complex.normSq_eq_zero]
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
      add_zero, Complex.zero_im] at him
    have hc : p.1.2 = 0 := by
      have := z.im_pos
      have h2 : ((-p.1.2 : ℤ) : ℝ) = 0 := by
        rcases mul_eq_zero.1 him with h | h
        · exact h
        · exact absurd h (ne_of_gt this)
      exact_mod_cast neg_eq_zero.1 (by exact_mod_cast h2)
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul,
      sub_zero, Complex.zero_re, hc, Int.cast_zero, neg_zero, zero_add] at hre
    have ha : p.1.1 = 0 := by exact_mod_cast hre
    have h1 : Int.gcd p.1.1 p.1.2 = 1 := p.2
    rw [ha, hc] at h1
    simp at h1
  push_cast
  field_simp

/-! ### `ℤ² ∖ 0 = ℕ₊ × {coprime}` -/

/-- `(g, (a,c)) ↦ ((g+1)(−c), (g+1)a)`. -/
def latMap (q : ℕ × copSet) : ℤ × ℤ := (((q.1 : ℤ) + 1) * (-q.2.1.2), ((q.1 : ℤ) + 1) * q.2.1.1)

lemma gcd_latMap (q : ℕ × copSet) : Int.gcd (latMap q).2 (latMap q).1 = q.1 + 1 := by
  simp only [latMap]
  rw [Int.gcd_mul_left, Int.gcd_neg]
  have h : Int.gcd q.2.1.1 q.2.1.2 = 1 := q.2.2
  rw [h, mul_one]
  omega

lemma latMap_injective : Function.Injective latMap := by
  intro q q' h
  have hg : q.1 = q'.1 := by
    have h1 := gcd_latMap q
    rw [h] at h1
    have h2 := gcd_latMap q'
    omega
  obtain ⟨g, p⟩ := q
  obtain ⟨g', p'⟩ := q'
  simp only at hg
  subst hg
  simp only [latMap, Prod.mk.injEq] at h
  have hn : ((g : ℤ) + 1) ≠ 0 := by omega
  have h1 := mul_left_cancel₀ hn h.1
  have h2 := mul_left_cancel₀ hn h.2
  refine Prod.ext rfl (Subtype.ext (Prod.ext h2 (by linarith)))

lemma range_latMap : Set.range latMap = {p : ℤ × ℤ | p ≠ 0} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩ h
    have := gcd_latMap q
    rw [h] at this
    simp at this
  · intro hp
    have hd : Int.gcd p.2 p.1 ≠ 0 := by
      intro h0
      rw [Int.gcd_eq_zero_iff] at h0
      exact hp (Prod.ext h0.2 h0.1)
    set d := Int.gcd p.2 p.1 with hd'
    have hcop : Int.gcd (p.2 / d) (-(p.1 / d)) = 1 := by
      rw [Int.gcd_neg]; exact Int.gcd_div_gcd_div_gcd (Nat.pos_of_ne_zero hd)
    refine ⟨(d - 1, ⟨(p.2 / d, -(p.1 / d)), hcop⟩), ?_⟩
    have hd1 : (((d - 1 : ℕ) : ℤ) + 1) = (d : ℤ) := by
      have : 1 ≤ d := Nat.pos_of_ne_zero hd
      omega
    simp only [latMap, hd1, neg_neg]
    refine Prod.ext ?_ ?_
    · exact Int.mul_ediv_cancel' (Int.gcd_dvd_right p.2 p.1)
    · exact Int.mul_ediv_cancel' (Int.gcd_dvd_left p.2 p.1)

lemma Qf_smul (x y : ℝ) (n : ℤ) (p : ℤ × ℤ) :
    Qf x y (n * p.1, n * p.2) = (n : ℝ) ^ 2 * Qf x y p := by
  unfold Qf; push_cast; ring

/-- **Splitting the lattice sum.** -/
theorem tsum_theta_split (x y t : ℝ) :
    ∑' p : ℤ × ℤ, ENNReal.ofReal (rexp (-π * t * Qf x y p)) =
      1 + ∑' g : ℕ, ∑' q : copSet,
        ENNReal.ofReal (rexp (-π * t * (((g : ℝ) + 1) ^ 2 * Qf x y (-q.1.2, q.1.1)))) := by
  rw [ENNReal.tsum_eq_add_tsum_ite (0 : ℤ × ℤ)]
  have h0 : Qf x y 0 = 0 := by simp [Qf]
  rw [h0, mul_zero, Real.exp_zero, ENNReal.ofReal_one]
  congr 1
  refine (latMap_injective.tsum_eq ?_).symm.trans ?_
  · intro p hp
    rw [range_latMap]
    intro h0
    exact hp (by simp [h0])
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun g => tsum_congr fun q => ?_
  have hne : latMap (g, q) ≠ 0 := by
    have : latMap (g, q) ∈ Set.range latMap := ⟨_, rfl⟩
    rw [range_latMap] at this; exact this
  simp only [if_neg hne]
  congr 3
  have := Qf_smul x y ((g : ℤ) + 1) (-q.1.2, q.1.1)
  simp only at this
  rw [show latMap (g, q) = (((g : ℤ) + 1) * (-q.1.2), ((g : ℤ) + 1) * q.1.1) from rfl, this]
  push_cast; ring

/-- `h_t(v) = ∑_{g ≥ 1} e^{−π t g²/v}`. -/
noncomputable def hfun (t v : ℝ) : ℝ≥0∞ := ∑' g : ℕ, ENNReal.ofReal (rexp (-π * t * ((g : ℝ) + 1) ^ 2 / v))

/-- **The theta function over `Γ∞\SL₂(ℤ)`.** -/
theorem theta_coset (z : ℍ) (t : ℝ) :
    ∑' p : ℤ × ℤ, ENNReal.ofReal (rexp (-π * t * Qf z.re z.im p)) =
      1 + ∑' γ : SL(2, ℤ), strip.indicator (1 : ℍ → ℝ≥0∞) (γ • z) * hfun t (γ • z).im := by
  rw [tsum_theta_split, tsum_strip_eq (fun w => hfun t w.im) (fun k w => by
    simp only [im_T_zpow_smul])]
  congr 1
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun q => ?_
  unfold hfun
  refine tsum_congr fun g => ?_
  rw [im_inv_mat_smul]
  congr 2
  field_simp

end RamanujanTau.RankinError

#print axioms RamanujanTau.RankinError.tsum_strip_eq
#print axioms RamanujanTau.RankinError.theta_coset
