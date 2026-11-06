/-
# The test function and its incomplete Poincaré series

`ff(z,w) = 1[Y ≤ Im z ≤ Y(1+ε)] · 1[rel(z,w) ∈ B] · e(h Re z)`, `B = {|Re ζ − θ| ≤ ε, |Im ζ − 1| ≤ ε}`,
`ft = 1_{strip}(Re z) · ff`, `Pt = Σ_γ ft ∘ γ`.

* `norm_ff_le`, `ff_T` (period `1`), `ff_aff` (`ff(z+t, w+t) = e(ht) ff(z,w)`);
* `count_le`: on `supp ft`, `Σ_γ ‖ft(γp)‖ ≤ N₀ = (2K+5)(2K+1)`, `K = ⌈1/Y⌉` (local finiteness);
* `lintegral_ft_le`: `∫⁻ ‖ft‖ ≤ 16 ε³ / Y`.
-/
import RamanujanTau.SCSProof.Measures
import RamanujanTau.RankinError.Coset

set_option autoImplicit false

namespace RamanujanTau.SCSProof

open MeasureTheory Set Complex
open UpperHalfPlane hiding I
open RamanujanTau.RankinError RamanujanTau.EisensteinReal RamanujanTau.EisensteinReal.Horo
open scoped MatrixGroups ENNReal Real

/-- Parameters of the test function. -/
structure Par where
  h : ℕ
  Y : ℝ
  ε : ℝ
  θ : ℝ
  hY : 0 < Y
  hY1 : Y ≤ 1
  hε : 0 < ε
  hε1 : ε ≤ 1 / 2

variable (P : Par)

/-- The `y`-window. -/
def inI (y : ℝ) : Prop := P.Y ≤ y ∧ y ≤ P.Y * (1 + P.ε)

/-- The box `B`. -/
def inB (ζ : ℂ) : Prop := |ζ.re - P.θ| ≤ P.ε ∧ |ζ.im - 1| ≤ P.ε

/-- The support of `ff`. -/
def suppF : Set (ℍ × ℍ) := {p | inI P p.1.im ∧ inB P (rel p.1 p.2)}

open Classical in
/-- The test function. -/
noncomputable def ff (p : ℍ × ℍ) : ℂ :=
  if p ∈ suppF P then cexp (2 * π * I * P.h * p.1.re) else 0

open Classical in
/-- Strip-restricted test function. -/
noncomputable def ft (p : ℍ × ℍ) : ℂ := if p.1 ∈ strip then ff P p else 0

/-- The incomplete Poincaré series. -/
noncomputable def Pt (p : ℍ × ℍ) : ℂ := ∑' γ : SL(2, ℤ), ft P (dsmul γ p)

/-! ### Measurability -/

lemma continuous_rel : Continuous fun p : ℍ × ℍ => rel p.1 p.2 := by
  unfold rel
  refine Continuous.div ?_ ?_ ?_
  · exact (UpperHalfPlane.continuous_coe.comp continuous_snd).sub
      (Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_re.comp continuous_fst))
  · exact Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_im.comp continuous_fst)
  · intro p; exact_mod_cast p.1.im_pos.ne'

lemma measurableSet_suppF : MeasurableSet (suppF P) := by
  have hr := continuous_rel.measurable
  have him : Measurable fun p : ℍ × ℍ => p.1.im := measurable_im_H.comp measurable_fst
  simp only [suppF, inI, inB, Set.setOf_and]
  refine ((measurableSet_le measurable_const him).inter
    (measurableSet_le him measurable_const)).inter
    ((measurableSet_le ?_ measurable_const).inter (measurableSet_le ?_ measurable_const))
  · exact ((Complex.measurable_re.comp hr).sub measurable_const).abs
  · exact ((Complex.measurable_im.comp hr).sub measurable_const).abs

lemma measurable_ff : Measurable (ff P) := by
  unfold ff
  refine Measurable.ite (measurableSet_suppF P) ?_ measurable_const
  exact (Complex.measurable_exp.comp (measurable_const.mul
    (Complex.measurable_ofReal.comp (measurable_re_H.comp measurable_fst))))

lemma measurable_ft : Measurable (ft P) := by
  unfold ft
  exact Measurable.ite (measurableSet_strip.preimage measurable_fst) (measurable_ff P)
    measurable_const

/-! ### Size and periodicity -/

lemma norm_exp_two_pi_I (t : ℝ) : ‖cexp (2 * π * I * t)‖ = 1 := by
  rw [Complex.norm_exp]; simp [Complex.mul_re]

lemma norm_ff (p : ℍ × ℍ) : ‖ff P p‖ = (suppF P).indicator 1 p := by
  unfold ff
  split_ifs with h
  · rw [indicator_of_mem h, mul_assoc, ← Complex.ofReal_natCast, ← Complex.ofReal_mul]
    simpa using norm_exp_two_pi_I (P.h * p.1.re)
  · rw [indicator_of_notMem h]; simp

lemma norm_ff_le (p : ℍ × ℍ) : ‖ff P p‖ ≤ 1 := by
  rw [norm_ff]; unfold indicator; split_ifs <;> simp

lemma norm_ft_le (p : ℍ × ℍ) : ‖ft P p‖ ≤ 1 := by
  unfold ft; split_ifs
  · exact norm_ff_le P p
  · simp

lemma ft_ne_zero {p : ℍ × ℍ} (hp : ft P p ≠ 0) : p.1 ∈ strip ∧ p ∈ suppF P := by
  unfold ft at hp
  split_ifs at hp with h1
  · refine ⟨h1, ?_⟩
    unfold ff at hp
    split_ifs at hp with h2
    · exact h2
    · exact absurd rfl hp
  · exact absurd rfl hp

lemma enorm_ft_le_ind (p : ℍ × ℍ) :
    ‖ft P p‖ₑ ≤ (strip.indicator (1 : ℍ → ℝ≥0∞) p.1) *
      ({u : ℍ | P.Y ≤ u.im}.indicator (1 : ℍ → ℝ≥0∞) p.1) := by
  by_cases h : ft P p = 0
  · simp [h]
  obtain ⟨h1, h2⟩ := ft_ne_zero P h
  have h3 : p.1 ∈ {u : ℍ | P.Y ≤ u.im} := h2.1.1
  rw [indicator_of_mem h1, indicator_of_mem h3]
  simp only [Pi.one_apply, mul_one]
  have := norm_ft_le P p
  rw [← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_one.2 this

/-! ### Local finiteness: the counting bound -/

/-- `K = ⌈1/Y⌉`. -/
noncomputable def Kc : ℕ := ⌈1 / P.Y⌉₊

/-- The number `N₀ = (2K+5)(2K+1)`. -/
noncomputable def N0 : ℕ := (2 * Kc P + 5) * (2 * Kc P + 1)

lemma count_pairs (z : ℍ) (hx : z ∈ strip) (hy1 : P.Y ≤ z.im) (hy2 : z.im ≤ 2 * P.Y) :
    ∑' q : copSet, ({u : ℍ | P.Y ≤ u.im}.indicator (1 : ℍ → ℝ≥0∞)) ((mat q)⁻¹ • z) ≤ N0 P := by
  classical
  set K := Kc P
  set S : Finset (ℤ × ℤ) := Finset.Icc (-(K : ℤ) - 2) (K + 2) ×ˢ Finset.Icc (-(K : ℤ)) K
  have hcard : (S.card : ℝ≥0∞) = N0 P := by
    simp only [S, Finset.card_product, Int.card_Icc, N0]
    push_cast
    congr 1
    · have : ((K : ℤ) + 2 + 1 - (-(K : ℤ) - 2)).toNat = 2 * K + 5 := by omega
      rw [this]; push_cast; ring
    · have : ((K : ℤ) + 1 - (-(K : ℤ))).toNat = 2 * K + 1 := by omega
      rw [this]; push_cast; ring
  have hY := P.hY
  have hsub : ∀ q : copSet, ({u : ℍ | P.Y ≤ u.im}.indicator (1 : ℍ → ℝ≥0∞)) ((mat q)⁻¹ • z) ≠ 0 →
      q.1 ∈ S := by
    intro q hq
    have hmem : P.Y ≤ ((mat q)⁻¹ • z).im := by
      by_contra hc
      exact hq (indicator_of_notMem (show (mat q)⁻¹ • z ∉ {u : ℍ | P.Y ≤ u.im} from hc) _)
    rw [im_inv_mat_smul] at hmem
    unfold Qf at hmem
    set a := q.1.1
    set c := q.1.2
    have hyp := z.im_pos
    have hQpos : 0 < ((a : ℝ) + ((-c : ℤ) : ℝ) * z.re) ^ 2 / z.im + ((-c : ℤ) : ℝ) ^ 2 * z.im := by
      by_contra hneg
      push Not at hneg
      have : 1 / (((a : ℝ) + ((-c : ℤ) : ℝ) * z.re) ^ 2 / z.im + ((-c : ℤ) : ℝ) ^ 2 * z.im) ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos zero_le_one hneg
      linarith
    have hQ : ((a : ℝ) + ((-c : ℤ) : ℝ) * z.re) ^ 2 / z.im + ((-c : ℤ) : ℝ) ^ 2 * z.im ≤ 1 / P.Y := by
      rw [le_div_iff₀ hY]
      rw [le_div_iff₀ hQpos] at hmem
      linarith
    have h1 : ((c : ℝ)) ^ 2 * z.im ≤ 1 / P.Y := by
      have : 0 ≤ ((a : ℝ) + ((-c : ℤ) : ℝ) * z.re) ^ 2 / z.im := by positivity
      push_cast at hQ this; nlinarith
    have h2 : ((a : ℝ) - c * z.re) ^ 2 ≤ 2 := by
      have : 0 ≤ ((-c : ℤ) : ℝ) ^ 2 * z.im := by positivity
      have h3 : ((a : ℝ) + ((-c : ℤ) : ℝ) * z.re) ^ 2 / z.im ≤ 1 / P.Y := by linarith
      rw [div_le_iff₀ hyp] at h3
      have : 1 / P.Y * z.im ≤ 2 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hY]; linarith
      push_cast at h3; nlinarith
    have hcK : |(c : ℝ)| ≤ K := by
      have hK : 1 / P.Y ≤ K := Nat.le_ceil _
      have hc2 : (c : ℝ) ^ 2 ≤ (1 / P.Y) ^ 2 := by
        have : (c : ℝ) ^ 2 * P.Y ≤ (c : ℝ) ^ 2 * z.im := by gcongr
        have h4 : (c : ℝ) ^ 2 * P.Y ≤ 1 / P.Y := le_trans this h1
        rw [div_pow, one_pow, le_div_iff₀ (by positivity)]
        calc (c : ℝ) ^ 2 * P.Y ^ 2 = ((c : ℝ) ^ 2 * P.Y) * P.Y := by ring
          _ ≤ (1 / P.Y) * P.Y := by gcongr
          _ = 1 := by field_simp
      have : |(c : ℝ)| ≤ 1 / P.Y := by
        rw [← abs_of_pos (by positivity : (0 : ℝ) < 1 / P.Y)]
        exact sq_le_sq.1 hc2
      linarith
    have haK : |(a : ℝ)| ≤ K + 2 := by
      have hx0 : 0 ≤ z.re := hx.1
      have hx1 : z.re < 1 := hx.2
      have h5 : |(a : ℝ) - c * z.re| ≤ 2 := by
        rw [abs_le]; constructor <;> nlinarith
      have h6 : |(c : ℝ) * z.re| ≤ K := by
        rw [abs_mul, abs_of_nonneg hx0]
        calc |(c : ℝ)| * z.re ≤ |(c : ℝ)| * 1 := by gcongr
          _ ≤ K := by linarith
      calc |(a : ℝ)| = |((a : ℝ) - c * z.re) + c * z.re| := by ring_nf
        _ ≤ |(a : ℝ) - c * z.re| + |(c : ℝ) * z.re| := abs_add_le _ _
        _ ≤ 2 + K := by linarith
        _ = K + 2 := by ring
    simp only [S, Finset.mem_product, Finset.mem_Icc]
    have hc' : |c| ≤ (K : ℤ) := by exact_mod_cast hcK
    have ha' : |a| ≤ (K : ℤ) + 2 := by exact_mod_cast haK
    rw [abs_le] at hc' ha'
    exact ⟨⟨by linarith [ha'.1], ha'.2⟩, ⟨hc'.1, hc'.2⟩⟩
  calc ∑' q : copSet, ({u : ℍ | P.Y ≤ u.im}.indicator (1 : ℍ → ℝ≥0∞)) ((mat q)⁻¹ • z)
      ≤ ∑' q : copSet, (S : Set (ℤ × ℤ)).indicator (1 : ℤ × ℤ → ℝ≥0∞) q.1 := by
        refine ENNReal.tsum_le_tsum fun q => ?_
        by_cases h0 : ({u : ℍ | P.Y ≤ u.im}.indicator (1 : ℍ → ℝ≥0∞)) ((mat q)⁻¹ • z) = 0
        · rw [h0]; exact bot_le
        · rw [indicator_of_mem (Finset.mem_coe.2 (hsub q h0))]
          unfold indicator; split_ifs <;> simp
    _ ≤ ∑' r : ℤ × ℤ, (S : Set (ℤ × ℤ)).indicator (1 : ℤ × ℤ → ℝ≥0∞) r :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
    _ = S.card := by
        rw [tsum_eq_sum (s := S) (fun r hr => indicator_of_notMem (by simpa using hr) _)]
        rw [Finset.sum_congr rfl (fun r hr => indicator_of_mem (Finset.mem_coe.2 hr) _)]
        simp
    _ = N0 P := hcard

/-- **Local finiteness.** For `p` with `Re z ∈ [0,1)`, `Y ≤ Im z ≤ 2Y`: `Σ_γ ‖ft(γp)‖ ≤ N₀`. -/
theorem count_le (p : ℍ × ℍ) (hx : p.1 ∈ strip) (hy1 : P.Y ≤ p.1.im) (hy2 : p.1.im ≤ 2 * P.Y) :
    ∑' γ : SL(2, ℤ), ‖ft P (dsmul γ p)‖ₑ ≤ N0 P := by
  calc ∑' γ : SL(2, ℤ), ‖ft P (dsmul γ p)‖ₑ
      ≤ ∑' γ : SL(2, ℤ), strip.indicator (1 : ℍ → ℝ≥0∞) (γ • p.1) *
          ({u : ℍ | P.Y ≤ u.im}.indicator (1 : ℍ → ℝ≥0∞) (γ • p.1)) :=
        ENNReal.tsum_le_tsum fun γ => enorm_ft_le_ind P (dsmul γ p)
    _ = ∑' q : copSet, ({u : ℍ | P.Y ≤ u.im}.indicator (1 : ℍ → ℝ≥0∞)) ((mat q)⁻¹ • p.1) := by
        refine tsum_strip_eq _ (fun k w => ?_) p.1
        simp only [indicator, mem_setOf_eq, im_T_zpow_smul, Pi.one_apply]
    _ ≤ N0 P := count_pairs P p.1 hx hy1 hy2

end RamanujanTau.SCSProof
