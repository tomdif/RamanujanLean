/-
# Expanding `|L(6+iu) M(6+iu)²|²` into twisted moments

For a real coefficient sequence `β` and `M = Mc (β : ℂ) y`:

    |M(6+iu)²|² = Σ_{p,q ∈ [1,y]²} κ(p,q) ((h_p/h_q)^{iu} + (h_q/h_p)^{iu}),

with `h_p = p.1 p.2` and `κ(p,q) = ½ β(p₁)β(p₂)β(q₁)β(q₂)(h_p h_q)^{−1/2}`.
So the `u`-average of `|LM²|²` is `Σ κ · TwAv(h_p, h_q)` (`Av_LM2`).
-/
import RamanujanTau.TwistedMoment.Main
import RamanujanTau.SelbergCoeffs.Mollifier

set_option autoImplicit false

namespace RamanujanTau.HafnerMV2

open Complex MeasureTheory Set Filter
open RamanujanTau.HafnerProportion RamanujanTau.HeckeL RamanujanTau.TwistedMoment RamanujanTau.GoodSecondTerm
open scoped ComplexConjugate

/-- Pairs `(n₁, n₂) ∈ [1, y]²`. -/
def PS (y : ℕ) : Finset (ℕ × ℕ) := Finset.Icc 1 y ×ˢ Finset.Icc 1 y

def hP (p : ℕ × ℕ) : ℕ := p.1 * p.2

noncomputable def LP (p : ℕ × ℕ) : ℝ := Real.log (hP p : ℝ)

noncomputable def cP (β : ℕ → ℝ) (p : ℕ × ℕ) : ℝ := β p.1 * β p.2

/-- The quadratic coefficient. -/
noncomputable def κ (β : ℕ → ℝ) (p q : ℕ × ℕ) : ℝ := 1 / 2 * (cP β p * cP β q * Real.exp (-((LP p + LP q) / 2)))

lemma hP_pos {y : ℕ} {p : ℕ × ℕ} (hp : p ∈ PS y) : 1 ≤ hP p := by
  simp only [PS, Finset.mem_product, Finset.mem_Icc] at hp
  unfold hP; exact Nat.one_le_iff_ne_zero.mpr (by have := hp.1.1; have := hp.2.1; positivity)

lemma LP_eq {y : ℕ} {p : ℕ × ℕ} (hp : p ∈ PS y) : LP p = Real.log p.1 + Real.log p.2 := by
  simp only [PS, Finset.mem_product, Finset.mem_Icc] at hp
  unfold LP hP
  push_cast
  exact Real.log_mul (by have : (1 : ℝ) ≤ p.1 := by exact_mod_cast hp.1.1
                         positivity) (by have : (1 : ℝ) ≤ p.2 := by exact_mod_cast hp.2.1
                                         positivity)

lemma cpow_line {n : ℕ} (hn : 1 ≤ n) (u : ℝ) :
    (n : ℂ) ^ ((11 / 2 : ℂ) - (6 + u * I)) =
      ((Real.exp (-(Real.log n / 2)) : ℝ) : ℂ) * cexp (-((u * Real.log n : ℝ) : ℂ) * I) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hn0, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_log (Nat.cast_nonneg _), Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- `M(6+iu)²` as a sum over pairs. -/
lemma Mc_sq (β : ℕ → ℝ) (y : ℕ) (u : ℝ) :
    Mc (fun n => (β n : ℂ)) y (6 + u * I) ^ 2 =
      ∑ p ∈ PS y, ((cP β p * Real.exp (-(LP p / 2)) : ℝ) : ℂ) * cexp (-((u * LP p : ℝ) : ℂ) * I) := by
  unfold Mc
  rw [sq, Finset.sum_mul_sum, PS, Finset.sum_product]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  have ha1 := (Finset.mem_Icc.1 ha).1
  have hb1 := (Finset.mem_Icc.1 hb).1
  rw [cpow_line ha1, cpow_line hb1, LP_eq (y := y) (Finset.mem_product.2 ⟨ha, hb⟩)]
  unfold cP
  simp only
  have e1 : Real.exp (-((Real.log a + Real.log b) / 2)) = Real.exp (-(Real.log a / 2)) * Real.exp (-(Real.log b / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : cexp (-((u * (Real.log a + Real.log b) : ℝ) : ℂ) * I) =
      cexp (-((u * Real.log a : ℝ) : ℂ) * I) * cexp (-((u * Real.log b : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e1, e2]; push_cast; ring

/-- The twist used in `TwistedMoment`. -/
lemma ph_eq (h k : ℕ) (u : ℝ) : ph h k u = cexp (u * I * ((Real.log h - Real.log k : ℝ) : ℂ)) := rfl

lemma conj_term (r v : ℝ) : conj (((r : ℝ) : ℂ) * cexp (-((v : ℝ) : ℂ) * I)) = (r : ℂ) * cexp (((v : ℝ) : ℂ) * I) := by
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I]

/-- **`|M²|²` as a symmetric twisted sum.** -/
theorem normSq_Mc_sq (β : ℕ → ℝ) (y : ℕ) (u : ℝ) :
    ((‖Mc (fun n => (β n : ℂ)) y (6 + u * I) ^ 2‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ PS y, ∑ q ∈ PS y, (κ β p q : ℂ) * (ph (hP p) (hP q) u + ph (hP q) (hP p) u) := by
  set z := Mc (fun n => (β n : ℂ)) y (6 + u * I) ^ 2 with hz
  have h1 : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h1, hz, Mc_sq, map_sum, Finset.sum_mul_sum]
  set f : ℕ × ℕ → ℕ × ℕ → ℂ := fun p q => ((cP β p * cP β q * Real.exp (-((LP p + LP q) / 2)) : ℝ) : ℂ) *
    ph (hP q) (hP p) u with hf
  have hterm : ∀ p q, ((cP β p * Real.exp (-(LP p / 2)) : ℝ) : ℂ) * cexp (-((u * LP p : ℝ) : ℂ) * I) *
      conj (((cP β q * Real.exp (-(LP q / 2)) : ℝ) : ℂ) * cexp (-((u * LP q : ℝ) : ℂ) * I)) = f p q := by
    intro p q
    rw [conj_term]
    simp only [hf, ph_eq]
    unfold LP
    have e1 : Real.exp (-((Real.log (hP p : ℝ) + Real.log (hP q : ℝ)) / 2)) =
        Real.exp (-(Real.log (hP p : ℝ) / 2)) * Real.exp (-(Real.log (hP q : ℝ) / 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : cexp (u * I * ((Real.log (hP q : ℝ) - Real.log (hP p : ℝ) : ℝ) : ℂ)) =
        cexp (-((u * Real.log (hP p : ℝ) : ℝ) : ℂ) * I) * cexp (((u * Real.log (hP q : ℝ) : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e1, e2]
    push_cast
    ring
  simp_rw [hterm]
  -- symmetrise
  have hsym : ∑ p ∈ PS y, ∑ q ∈ PS y, f p q = ∑ p ∈ PS y, ∑ q ∈ PS y, f q p := Finset.sum_comm
  have hfs : ∀ p q, f q p = ((cP β p * cP β q * Real.exp (-((LP p + LP q) / 2)) : ℝ) : ℂ) *
      ph (hP p) (hP q) u := by
    intro p q; simp only [hf]; congr 2; ring_nf
  calc ∑ p ∈ PS y, ∑ q ∈ PS y, f p q
      = (1 / 2 : ℂ) * (∑ p ∈ PS y, ∑ q ∈ PS y, f p q + ∑ p ∈ PS y, ∑ q ∈ PS y, f q p) := by
        rw [← hsym]; ring
    _ = _ := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hfs p q]; simp only [hf]; unfold κ; push_cast; ring

/-- The averaging operator commutes with finite sums. -/
lemma Av_sum {ι : Type*} {X H : ℝ} (hX : 16 ≤ X) (hH : 0 < H) (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, ContinuousOn (f i) (Icc 16 (X + H))) :
    Av X H (fun t => ∑ i ∈ s, f i t) = ∑ i ∈ s, Av X H (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Av]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [Av_add (F := f a) (G := fun t => ∑ i ∈ s, f i t) hX hH (hf a (Finset.mem_insert_self a s))
      (continuousOn_finset_sum _ fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

lemma continuous_twist (h k : ℕ) :
    Continuous fun t : ℝ => ((‖tauL (6 + t * I)‖ ^ 2 : ℝ) : ℂ) * (ph h k t + ph k h t) := by
  have h1 := continuous_zsqD
  unfold zsqD at h1
  exact (Complex.continuous_ofReal.comp h1).mul ((continuous_ph h k).add (continuous_ph k h))

/-- **The average of `|LM²|²` is a combination of twisted moments.** -/
theorem Av_LM2 (β : ℕ → ℝ) (y : ℕ) {X H : ℝ} (hX : 16 ≤ X) (hH : 0 < H) :
    Av X H (fun u => ((‖tauL (6 + u * I) * Mc (fun n => (β n : ℂ)) y (6 + u * I) ^ 2‖ ^ 2 : ℝ) : ℂ)) =
      ∑ p ∈ PS y, ∑ q ∈ PS y, (κ β p q : ℂ) * TwAv (hP p) (hP q) X H := by
  have e : (fun u : ℝ => ((‖tauL (6 + u * I) * Mc (fun n => (β n : ℂ)) y (6 + u * I) ^ 2‖ ^ 2 : ℝ) : ℂ)) =
      fun u : ℝ => ∑ p ∈ PS y, ∑ q ∈ PS y, (κ β p q : ℂ) *
        (((‖tauL (6 + u * I)‖ ^ 2 : ℝ) : ℂ) * (ph (hP p) (hP q) u + ph (hP q) (hP p) u)) := by
    funext u
    rw [norm_mul, mul_pow, Complex.ofReal_mul, normSq_Mc_sq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [e]
  have hc : ∀ p q, ContinuousOn (fun u : ℝ => (κ β p q : ℂ) *
      (((‖tauL (6 + u * I)‖ ^ 2 : ℝ) : ℂ) * (ph (hP p) (hP q) u + ph (hP q) (hP p) u))) (Icc 16 (X + H)) :=
    fun p q => (continuous_const.mul (continuous_twist _ _)).continuousOn
  rw [Av_sum hX hH (PS y) _ (fun p _ => continuousOn_finset_sum _ fun q _ => hc p q)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Av_sum hX hH (PS y) _ (fun q _ => hc p q)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Av_smul]; rfl

end RamanujanTau.HafnerMV2
