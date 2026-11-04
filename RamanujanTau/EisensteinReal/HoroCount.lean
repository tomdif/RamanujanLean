/-
# The horocycle mean of a rectangle count, as a sum over `c`

`R = rect α β A = {α ≤ Re w < β, A ≤ Im w}`, `cnt z = #{γ : γz ∈ R}`, `horo = ∫₀¹ cnt(x+iy) dx`.

* `horo_eq_two_tsum`: for `y < A`, `horo = 2 ∑_{c ≥ 1} G(c)`, where
  `G(c) = ∫_ℝ #{a coprime to c : c(α+ρ) ≤ a < c(β+ρ)} · 1[A ≤ η] dx`,
  `ρ = x/(c²(x²+y²))`, `η = y/(c²(x²+y²))`.
* `Gc_le`, `Gc_ge`: `G(c) = c(β−α)ν(c)λ_c + O(d(c)λ_c)`, `λ_c = 2√(y/(Ac²) − y²)`.
-/
import RamanujanTau.EisensteinReal.HoroUnfold

set_option autoImplicit false

namespace RamanujanTau.EisensteinReal.Horo

open Finset Real Filter Topology MeasureTheory ModularGroup Matrix
open RamanujanTau.RankinSelberg
open UpperHalfPlane hiding I
open scoped MatrixGroups ENNReal

/-- The rectangle `α ≤ Re w < β`, `A ≤ Im w`. -/
def rect (α β A : ℝ) : Set ℍ := {w | α ≤ w.re ∧ w.re < β ∧ A ≤ w.im}

lemma measurableSet_rect (α β A : ℝ) : MeasurableSet (rect α β A) := by
  have hre : Measurable (fun w : ℍ => w.re) := UpperHalfPlane.continuous_re.measurable
  have him : Measurable (fun w : ℍ => w.im) := UpperHalfPlane.continuous_im.measurable
  exact (measurableSet_le measurable_const hre).inter
    ((measurableSet_lt hre measurable_const).inter (measurableSet_le measurable_const him))

/-- Indicator of the rectangle. -/
noncomputable def ind (α β A : ℝ) (w : ℍ) : ℝ≥0∞ := (rect α β A).indicator 1 w

lemma measurable_ind (α β A : ℝ) : Measurable (ind α β A) :=
  measurable_one.indicator (measurableSet_rect α β A)

/-- `N_R(z) = #{γ ∈ SL₂(ℤ) : γz ∈ R}` (each coset of `±1` counted twice). -/
noncomputable def cnt (α β A : ℝ) (z : ℍ) : ℝ≥0∞ := ∑' γ : SL(2, ℤ), ind α β A (γ • z)

/-- The horocycle mean `∫₀¹ N_R(x + iy) dx`. -/
noncomputable def horo (α β A : ℝ) {y : ℝ} (hy : 0 < y) : ℝ≥0∞ :=
  ∫⁻ x in Set.Ioc (0 : ℝ) 1, cnt α β A (hp hy x)

lemma horo_eq_tsum (α β A : ℝ) {y : ℝ} (hy : 0 < y) :
    horo α β A hy = ∑' p : copSet, ∫⁻ x, ind α β A (mat p • hp hy x) :=
  lintegral_unfold hy (measurable_ind α β A)

/-! ### The point `M(a,c)(x + iy)` after the shift -/

lemma coe_mat_smul_shift {y : ℝ} (hy : 0 < y) (p : copSet) (hc : p.1.2 ≠ 0) (x : ℝ) :
    ((mat p • hp hy (x - (Int.gcdA p.1.1 p.1.2 : ℝ) / (p.1.2 : ℝ)) : ℍ) : ℂ) =
      (p.1.1 : ℂ) / p.1.2 - 1 / ((p.1.2 : ℂ) ^ 2 * ((x : ℂ) + y * Complex.I)) := by
  rw [coe_specialLinearGroup_apply, hp_coe]
  simp only [mat_apply_00, mat_apply_01, mat_apply_10, mat_apply_11, algebraMap_int_eq,
    eq_intCast]
  have h := Int.gcd_eq_gcd_ab p.1.1 p.1.2
  rw [show Int.gcd p.1.1 p.1.2 = 1 from p.2] at h
  have hC : (1 : ℂ) = (p.1.1 : ℂ) * (Int.gcdA p.1.1 p.1.2 : ℂ) +
      (p.1.2 : ℂ) * (Int.gcdB p.1.1 p.1.2 : ℂ) := by exact_mod_cast h
  have hc' : (p.1.2 : ℂ) ≠ 0 := by exact_mod_cast hc
  have hw : ((x : ℂ) + y * Complex.I) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  push_cast
  have hden : (p.1.2 : ℂ) * ((x : ℂ) - (Int.gcdA p.1.1 p.1.2 : ℂ) / (p.1.2 : ℂ) + y * Complex.I)
      + (Int.gcdA p.1.1 p.1.2 : ℂ) = (p.1.2 : ℂ) * ((x : ℂ) + y * Complex.I) := by
    field_simp; ring
  rw [hden, div_eq_iff (mul_ne_zero hc' hw)]
  have e1 : ((p.1.1 : ℂ) / p.1.2 - 1 / ((p.1.2 : ℂ) ^ 2 * ((x : ℂ) + y * Complex.I))) *
      ((p.1.2 : ℂ) * ((x : ℂ) + y * Complex.I)) =
      (p.1.1 : ℂ) * ((x : ℂ) + y * Complex.I) - 1 / (p.1.2 : ℂ) := by
    field_simp
  have e2 : (1 : ℂ) / (p.1.2 : ℂ) = (p.1.1 : ℂ) * (Int.gcdA p.1.1 p.1.2 : ℂ) / (p.1.2 : ℂ) +
      (Int.gcdB p.1.1 p.1.2 : ℂ) := by
    rw [hC]; field_simp
  rw [e1, e2]
  ring

lemma re_im_formula {x y q c2 : ℝ} (hy : 0 < y) (hc2 : c2 ≠ 0) :
    ((q : ℂ) - 1 / ((c2 : ℂ) * ((x : ℂ) + y * Complex.I))).re =
        q - x / (c2 * (x ^ 2 + y ^ 2)) ∧
      ((q : ℂ) - 1 / ((c2 : ℂ) * ((x : ℂ) + y * Complex.I))).im =
        y / (c2 * (x ^ 2 + y ^ 2)) := by
  have hxy : x ^ 2 + y ^ 2 ≠ 0 := by positivity
  constructor
  · simp [Complex.div_re, Complex.normSq_apply]
    field_simp
  · simp [Complex.div_im, Complex.normSq_apply]
    field_simp

/-- The integrand after the shift: `1[α ≤ q − ρ < β, A ≤ η]`. -/
noncomputable def Xi (α β A y q c2 x : ℝ) : ℝ≥0∞ :=
  if α ≤ q - x / (c2 * (x ^ 2 + y ^ 2)) ∧ q - x / (c2 * (x ^ 2 + y ^ 2)) < β ∧
    A ≤ y / (c2 * (x ^ 2 + y ^ 2)) then 1 else 0

lemma measurable_Xi (α β A y q c2 : ℝ) : Measurable (Xi α β A y q c2) := by
  have h1 : Measurable fun x : ℝ => q - x / (c2 * (x ^ 2 + y ^ 2)) := by fun_prop
  have h2 : Measurable fun x : ℝ => y / (c2 * (x ^ 2 + y ^ 2)) := by fun_prop
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_le measurable_const h1).inter
    ((measurableSet_lt h1 measurable_const).inter (measurableSet_le measurable_const h2))

lemma ind_mat_shift {α β A y : ℝ} (hy : 0 < y) (p : copSet) (hc : p.1.2 ≠ 0) (x : ℝ) :
    ind α β A (mat p • hp hy (x - (Int.gcdA p.1.1 p.1.2 : ℝ) / (p.1.2 : ℝ))) =
      Xi α β A y ((p.1.1 : ℝ) / p.1.2) ((p.1.2 : ℝ) ^ 2) x := by
  have hc2 : ((p.1.2 : ℝ) ^ 2) ≠ 0 := by positivity
  obtain ⟨hre, him⟩ := re_im_formula (x := x) (q := (p.1.1 : ℝ) / p.1.2) hy hc2
  have hco := coe_mat_smul_shift hy p hc x
  have ere : (mat p • hp hy (x - (Int.gcdA p.1.1 p.1.2 : ℝ) / (p.1.2 : ℝ))).re =
      (p.1.1 : ℝ) / p.1.2 - x / ((p.1.2 : ℝ) ^ 2 * (x ^ 2 + y ^ 2)) := by
    rw [← hre, UpperHalfPlane.re, hco]; push_cast; rfl
  have eim : (mat p • hp hy (x - (Int.gcdA p.1.1 p.1.2 : ℝ) / (p.1.2 : ℝ))).im =
      y / ((p.1.2 : ℝ) ^ 2 * (x ^ 2 + y ^ 2)) := by
    rw [← him, UpperHalfPlane.im, hco]; push_cast; rfl
  unfold ind Xi
  simp only [Set.indicator, rect, Set.mem_setOf_eq, ere, eim, Pi.one_apply]

lemma lintegral_ind_mat {α β A y : ℝ} (hy : 0 < y) (p : copSet) (hc : p.1.2 ≠ 0) :
    ∫⁻ x, ind α β A (mat p • hp hy x) =
      ∫⁻ x, Xi α β A y ((p.1.1 : ℝ) / p.1.2) ((p.1.2 : ℝ) ^ 2) x := by
  rw [← lintegral_add_right_eq_self (μ := volume) _ (-((Int.gcdA p.1.1 p.1.2 : ℝ) / (p.1.2 : ℝ)))]
  congr 1
  funext x
  rw [← sub_eq_add_neg, ind_mat_shift hy p hc x]

/-- The `c = 0` cosets contribute nothing below height `A`. -/
lemma ind_mat_c_zero {α β A y : ℝ} (hy : 0 < y) (hyA : y < A) (p : copSet) (hc : p.1.2 = 0)
    (x : ℝ) : ind α β A (mat p • hp hy x) = 0 := by
  have him := ModularGroup.im_smul_eq_div_normSq (mat p) (hp hy x)
  have hd : (mat p) 1 1 ^ 2 = 1 := by
    have h := (mat p).det_coe
    rw [Matrix.det_fin_two, mat_apply_10, hc, mul_zero, sub_zero] at h
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2] <;> norm_num
  have hden : Complex.normSq (UpperHalfPlane.denom (mat p) (hp hy x)) = 1 := by
    rw [ModularGroup.denom_apply]
    simp only [mat_apply_10, hc]
    simp only [Int.cast_zero, Complex.ofReal_zero, zero_mul, zero_add]
    rw [Complex.normSq_apply]
    simp only [Complex.ofReal_intCast, Complex.intCast_re, Complex.intCast_im, mul_zero,
      add_zero]
    have : ((mat p) 1 1 : ℝ) ^ 2 = 1 := by exact_mod_cast hd
    nlinarith
  rw [hden, div_one, hp_im] at him
  unfold ind
  rw [Set.indicator_of_notMem]
  intro hmem
  have := hmem.2.2
  linarith

/-! ### Splitting by `c` -/

/-- `Ψ(a,c) = ∫ Xi(a/c, c²)` for `c ≠ 0`, and `0` for `c = 0`. -/
noncomputable def Psi (α β A y : ℝ) (q : ℤ × ℤ) : ℝ≥0∞ :=
  if q.2 = 0 then 0 else ∫⁻ x, Xi α β A y ((q.1 : ℝ) / q.2) ((q.2 : ℝ) ^ 2) x

/-- `G(c) = ∑_{a coprime to c} Ψ(a,c)`. -/
noncomputable def Gc (α β A y : ℝ) (c : ℤ) : ℝ≥0∞ :=
  ∑' a : ℤ, copSet.indicator (Psi α β A y) (a, c)

lemma horo_eq_tsum_Gc {α β A y : ℝ} (hy : 0 < y) (hyA : y < A) :
    horo α β A hy = ∑' c : ℤ, Gc α β A y c := by
  rw [horo_eq_tsum]
  have : ∀ p : copSet, ∫⁻ x, ind α β A (mat p • hp hy x) = Psi α β A y p.1 := by
    intro p
    by_cases hc : p.1.2 = 0
    · simp only [Psi, hc, if_true]
      simp only [ind_mat_c_zero hy hyA p hc, lintegral_zero]
    · simp only [Psi, hc, if_false]
      exact lintegral_ind_mat hy p hc
  rw [tsum_congr this, tsum_subtype copSet (Psi α β A y), ENNReal.tsum_prod', ENNReal.tsum_comm]
  rfl

lemma Gc_zero (α β A y : ℝ) : Gc α β A y 0 = 0 := by
  simp [Gc, Psi, Set.indicator]

lemma Gc_neg (α β A y : ℝ) (c : ℤ) : Gc α β A y (-c) = Gc α β A y c := by
  unfold Gc
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun a => ?_
  simp only [Equiv.neg_apply, Set.indicator, copSet, Set.mem_setOf_eq, Int.neg_gcd,
    Int.gcd_neg, Psi, neg_eq_zero]
  push_cast
  rw [neg_div_neg_eq, neg_sq]

lemma horo_eq_two {α β A y : ℝ} (hy : 0 < y) (hyA : y < A) :
    horo α β A hy = 2 * ∑' n : ℕ, Gc α β A y ((n : ℤ) + 1) := by
  rw [horo_eq_tsum_Gc hy hyA, tsum_of_add_one_of_neg_add_one ENNReal.summable ENNReal.summable,
    Gc_zero, add_zero]
  simp only [Gc_neg]
  rw [two_mul]

/-! ### `G(c)` as an integral of a coprime count -/

lemma Xi_eq {α β A y : ℝ} {c : ℕ} (hc : 0 < c) (a : ℤ) (x : ℝ) :
    Xi α β A y ((a : ℝ) / (c : ℤ)) (((c : ℤ) : ℝ) ^ 2) x =
      if (c * (α + x / ((c : ℝ) ^ 2 * (x ^ 2 + y ^ 2))) ≤ a ∧
          (a : ℝ) < c * (β + x / ((c : ℝ) ^ 2 * (x ^ 2 + y ^ 2)))) ∧
          A ≤ y / ((c : ℝ) ^ 2 * (x ^ 2 + y ^ 2)) then 1 else 0 := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  unfold Xi
  push_cast
  congr 1
  apply propext
  rw [le_sub_iff_add_le, sub_lt_iff_lt_add, le_div_iff₀ hc', div_lt_iff₀ hc']
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by linarith, by linarith⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by linarith, by linarith, h3⟩

/-- `ρ_c(x) = x/(c²(x²+y²))`. -/
noncomputable def rho (y : ℝ) (c : ℕ) (x : ℝ) : ℝ := x / ((c : ℝ) ^ 2 * (x ^ 2 + y ^ 2))

/-- `η_c(x) = y/(c²(x²+y²))`. -/
noncomputable def eta (y : ℝ) (c : ℕ) (x : ℝ) : ℝ := y / ((c : ℝ) ^ 2 * (x ^ 2 + y ^ 2))

lemma tsum_coprime_Xi {α β A y : ℝ} {c : ℕ} (hc : 0 < c) (x : ℝ) :
    ∑' a : ℤ, (if Int.gcd a c = 1 then Xi α β A y ((a : ℝ) / (c : ℤ)) (((c : ℤ) : ℝ) ^ 2) x
      else 0) =
      if A ≤ eta y c x then
        ((coprimeSet c (c * (α + rho y c x)) (c * (β + rho y c x))).card : ℝ≥0∞) else 0 := by
  simp only [Xi_eq hc]
  split_ifs with hA
  · rw [tsum_eq_sum (s := coprimeSet c (c * (α + rho y c x)) (c * (β + rho y c x)))]
    · rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [mem_coprimeSet] at ha
      simp only [rho, eta] at ha hA
      simp [ha.2, ha.1.1, ha.1.2, hA]
    · intro a ha
      rw [mem_coprimeSet] at ha
      simp only [rho, eta] at ha
      split_ifs with h1 h2 <;> try rfl
      exact absurd ⟨h2.1, h1⟩ ha
  · have : ¬ A ≤ y / ((c : ℝ) ^ 2 * (x ^ 2 + y ^ 2)) := hA
    simp [this]

lemma measurable_eta (y : ℝ) (c : ℕ) : Measurable (eta y c) := by unfold eta; fun_prop
lemma measurable_rho (y : ℝ) (c : ℕ) : Measurable (rho y c) := by unfold rho; fun_prop

lemma Gc_eq {α β A y : ℝ} {c : ℕ} (hc : 0 < c) :
    Gc α β A y (c : ℤ) = ∫⁻ x, if A ≤ eta y c x then
        ((coprimeSet c (c * (α + rho y c x)) (c * (β + rho y c x))).card : ℝ≥0∞) else 0 := by
  have hc0 : ((c : ℤ)) ≠ 0 := by exact_mod_cast hc.ne'
  unfold Gc
  have h1 : ∀ a : ℤ, copSet.indicator (Psi α β A y) (a, (c : ℤ)) =
      ∫⁻ x, (if Int.gcd a c = 1 then Xi α β A y ((a : ℝ) / (c : ℤ)) (((c : ℤ) : ℝ) ^ 2) x
        else 0) := by
    intro a
    simp only [Set.indicator, copSet, Set.mem_setOf_eq, Psi, hc0, if_false]
    split_ifs <;> simp
  rw [tsum_congr h1, ← lintegral_tsum]
  · exact lintegral_congr fun x => tsum_coprime_Xi hc x
  · intro a
    exact (Measurable.ite (MeasurableSet.const _) (measurable_Xi _ _ _ _ _ _)
      measurable_const).aemeasurable

/-- `λ_c = |{x : A ≤ η_c(x)}| = 2√(y/(Ac²) − y²)`. -/
lemma volume_eta {A y : ℝ} (hA : 0 < A) (hy : 0 < y) {c : ℕ} (hc : 0 < c) :
    volume {x : ℝ | A ≤ eta y c x} =
      ENNReal.ofReal (2 * Real.sqrt (y / (A * (c : ℝ) ^ 2) - y ^ 2)) := by
  have hc' : (0 : ℝ) < (c : ℝ) ^ 2 := by positivity
  set R := y / (A * (c : ℝ) ^ 2) - y ^ 2 with hR
  have key : ∀ x : ℝ, A ≤ eta y c x ↔ x ^ 2 ≤ R := by
    intro x
    unfold eta
    rw [le_div_iff₀ (by positivity), hR, le_sub_iff_add_le, le_div_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  rcases lt_or_ge R 0 with hneg | hpos
  · have : {x : ℝ | A ≤ eta y c x} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, key]
      nlinarith [sq_nonneg x]
    rw [this, Real.sqrt_eq_zero'.mpr hneg.le]
    simp
  · have : {x : ℝ | A ≤ eta y c x} = Set.Icc (-Real.sqrt R) (Real.sqrt R) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_Icc, key, ← abs_le]
      rw [← Real.sqrt_sq_eq_abs, Real.sqrt_le_sqrt_iff hpos]
    rw [this, Real.volume_Icc]
    congr 1
    ring

lemma measurableSet_eta (A y : ℝ) (c : ℕ) : MeasurableSet {x : ℝ | A ≤ eta y c x} :=
  measurableSet_le measurable_const (measurable_eta y c)

lemma Gc_eq_indicator {α β A y : ℝ} {c : ℕ} (hc : 0 < c) :
    Gc α β A y (c : ℤ) = ∫⁻ x, {x : ℝ | A ≤ eta y c x}.indicator
        (fun x => ((coprimeSet c (c * (α + rho y c x)) (c * (β + rho y c x))).card : ℝ≥0∞)) x := by
  rw [Gc_eq hc]
  rfl

/-- **Upper bound:** `G(c) ≤ (c(β−α)ν(c) + d(c)) λ_c`. -/
theorem Gc_le {α β A y : ℝ} (hαβ : α ≤ β) (hA : 0 < A) (hy : 0 < y) {c : ℕ} (hc : 0 < c) :
    Gc α β A y (c : ℤ) ≤ ENNReal.ofReal (c * (β - α) * nu c + c.divisors.card) *
      ENNReal.ofReal (2 * Real.sqrt (y / (A * (c : ℝ) ^ 2) - y ^ 2)) := by
  rw [Gc_eq_indicator hc, ← volume_eta hA hy hc, ← lintegral_indicator_const (measurableSet_eta A y c)]
  refine lintegral_mono fun x => ?_
  refine Set.indicator_le_indicator ?_
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have huv : (c : ℝ) * (α + rho y c x) ≤ c * (β + rho y c x) := by nlinarith
  have hb := coprimeCount_bound (c := c) hc.ne' huv
  rw [← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  have e : (c : ℝ) * (β + rho y c x) - c * (α + rho y c x) = c * (β - α) := by ring
  rw [e] at hb
  linarith [(abs_le.1 hb).2]

/-- **Lower bound:** `G(c) ≥ (c(β−α)ν(c) − d(c)) λ_c`. -/
theorem Gc_ge {α β A y : ℝ} (hαβ : α ≤ β) (hA : 0 < A) (hy : 0 < y) {c : ℕ} (hc : 0 < c) :
    ENNReal.ofReal (c * (β - α) * nu c - c.divisors.card) *
      ENNReal.ofReal (2 * Real.sqrt (y / (A * (c : ℝ) ^ 2) - y ^ 2)) ≤ Gc α β A y (c : ℤ) := by
  rw [Gc_eq_indicator hc, ← volume_eta hA hy hc, ← lintegral_indicator_const (measurableSet_eta A y c)]
  refine lintegral_mono fun x => ?_
  refine Set.indicator_le_indicator ?_
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have huv : (c : ℝ) * (α + rho y c x) ≤ c * (β + rho y c x) := by nlinarith
  have hb := coprimeCount_bound (c := c) hc.ne' huv
  rw [← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  have e : (c : ℝ) * (β + rho y c x) - c * (α + rho y c x) = c * (β - α) := by ring
  rw [e] at hb
  linarith [(abs_le.1 hb).1]

end RamanujanTau.EisensteinReal.Horo
