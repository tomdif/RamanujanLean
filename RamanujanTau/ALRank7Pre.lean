/-
# Dyson's rank mod 7: preliminaries (base, orbit, class-5 calculus, `Θ_g`)

From `newform` and the `m`-level 7-split of the two Appell–Lerch sums, `R(ζ;q)` is a sum of class-pure mock
pieces (the only class-5 pair cancels, `orbit7`) and a theta part equal to the explicit `Θ_g`
(by the 38 level-21 identities of `ALCore7`), which has no class-5 exponents.
-/
import RamanujanTau.ALNewForm
import RamanujanTau.ALClass7
import RamanujanTau.ALCore7

set_option autoImplicit false

namespace ALz
open HahnSeries

/-- base `q^{147}` in `t`-units (`N = 3·7·7`). -/
lemma hP : (1 : ℕ) ≤ 3 * 7 * 7 := by norm_num

/-- the class-5 mock pair: `m(q^{-49}, q^{140}) = q^{49} m(q^{49}, q^{7})` at base `q^{147}`. -/
theorem orbit7 :
    Ab hP (a := -49) (β := 140) (by norm_num) (by norm_num) 1 1 / θ hP 140 1 =
      mono 49 1 * (Ab hP (a := 49) (β := 7) (by norm_num) (by norm_num) 1 1 / θ hP 7 1) := by
  have hi := Ab_inv hP (a := 49) (β := -140) (by norm_num) (by norm_num) one_ne_zero one_ne_zero
    (mono_ne_one_of (Or.inl (by norm_num)))
  have hz := Ab_zshift hP (a := 49) (β := -140) (by norm_num) (by norm_num) one_ne_zero one_ne_zero
  have hr := θ_reflect hP 7 (one_ne_zero (α := ℂ))
  simp only [inv_one, mul_one] at hi hz hr
  have e1 : Ab hP (a := -49) (β := 140) (by norm_num) (by norm_num) 1 1 =
      -mono (49 - -140) 1 * Ab hP (a := 49) (β := -140) (by norm_num) (by norm_num) 1 1 := by
    convert hi using 2
  have e2 : Ab hP (a := 49) (β := 7) (by norm_num) (by norm_num) 1 1 =
      -mono (- -140) 1 * Ab hP (a := 49) (β := -140) (by norm_num) (by norm_num) 1 1 := by
    convert hz using 2
  have e3 : θ hP 140 1 = θ hP 7 1 := by convert hr using 2
  rw [e1, e2, e3]
  have hm : mono (49 - -140) (1 : ℂ) = mono 49 1 * mono (- -140) 1 := by rw [mono_mul]; norm_num
  rw [hm]; ring

lemma No5.cls0_mul {f g : L} (hf : InCls 0 f) (hg : No5 g) : No5 (f * g) := by
  intro n hn
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [Finset.mem_addAntidiagonal] at hij
  obtain ⟨hi, -, rfl⟩ := hij
  have := hf ij.1 hi
  rw [hg ij.2 (by omega), mul_zero]

lemma Ab_congr {N : ℕ} (hN : 1 ≤ N) {a a' β β' : ℤ} {cx cx' cp cp' : ℂ} (ha : a = a') (hb : β = β')
    (hx : cx = cx') (hp : cp = cp') (h1 : -N < a + β) (h2 : a + β < N) (h1' : -N < a' + β') (h2' : a' + β' < N) :
    Ab hN h1 h2 cx cp = Ab hN h1' h2' cx' cp' := by
  subst ha hb hx hp; rfl


noncomputable def ThetaG (ζ : ℂ) : L :=
  mono 0 (1 : ℂ) * (mono 0 (-1 : ℂ) * (θ hP 14 1) * ((-hs (kF hP 0))) / (((θ hP 7 1) ^ 2) * (θ hP 63 1)) + mono 0 (3 : ℂ) * ((-hs (kF hP 0))) * (mono 7 (1:ℂ)) / ((θ hP 21 1) * (θ hP 49 1)) + mono 0 (1 : ℂ) * (θ hP 14 1) * ((-hs (kF hP 0))) * (mono 0 ζ) / (((θ hP 7 1) ^ 2) * (θ hP 63 1)) + mono 0 (1 : ℂ) * ((-hs (kF hP 0))) * (mono 7 (1:ℂ)) * ((mono 0 ζ) ^ 2) / ((θ hP 21 1) * (θ hP 49 1)) + mono 0 (1 : ℂ) * ((-hs (kF hP 0))) * (mono 7 (1:ℂ)) * ((mono 0 ζ) ^ 3) / ((θ hP 21 1) * (θ hP 49 1)) + mono 0 (1 : ℂ) * ((-hs (kF hP 0))) * (mono 7 (1:ℂ)) * ((mono 0 ζ) ^ 4) / ((θ hP 21 1) * (θ hP 49 1)) + mono 0 (1 : ℂ) * ((-hs (kF hP 0))) * (mono 7 (1:ℂ)) * ((mono 0 ζ) ^ 5) / ((θ hP 21 1) * (θ hP 49 1)) + mono 0 (-3 : ℂ) * (θ hP 14 1) * (θ hP 56 1) * ((-hs (kF hP 0))) / ((θ hP 7 1) * (θ hP 21 1) * (θ hP 35 1) * (θ hP 49 1)) + mono 0 (3 : ℂ) * (θ hP 28 1) * (θ hP 56 1) * ((-hs (kF hP 0))) / ((θ hP 7 1) * (θ hP 70 1) * (θ hP 21 1) * (θ hP 49 1)) + mono 0 (1 : ℂ) * (θ hP 28 1) * (θ hP 56 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 2) / ((θ hP 7 1) * (θ hP 70 1) * (θ hP 21 1) * (θ hP 49 1)) + mono 0 (1 : ℂ) * (θ hP 28 1) * (θ hP 56 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 3) / ((θ hP 7 1) * (θ hP 70 1) * (θ hP 21 1) * (θ hP 49 1)) + mono 0 (1 : ℂ) * (θ hP 28 1) * (θ hP 56 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 4) / ((θ hP 7 1) * (θ hP 70 1) * (θ hP 21 1) * (θ hP 49 1)) + mono 0 (1 : ℂ) * (θ hP 28 1) * (θ hP 56 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 5) / ((θ hP 7 1) * (θ hP 70 1) * (θ hP 21 1) * (θ hP 49 1)) + mono 0 (-1 : ℂ) * (θ hP 14 1) * (θ hP 56 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 2) / ((θ hP 7 1) * (θ hP 21 1) * (θ hP 35 1) * (θ hP 49 1)) + mono 0 (-1 : ℂ) * (θ hP 14 1) * (θ hP 56 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 3) / ((θ hP 7 1) * (θ hP 21 1) * (θ hP 35 1) * (θ hP 49 1)) + mono 0 (-1 : ℂ) * (θ hP 14 1) * (θ hP 56 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 4) / ((θ hP 7 1) * (θ hP 21 1) * (θ hP 35 1) * (θ hP 49 1)) + mono 0 (-1 : ℂ) * (θ hP 14 1) * (θ hP 56 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 5) / ((θ hP 7 1) * (θ hP 21 1) * (θ hP 35 1) * (θ hP 49 1)) + mono 0 (-2 : ℂ) * (θ hP 70 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 49 1) * ((-hs (kF hP 0))) / ((θ hP 7 1) * (θ hP 14 1) * (θ hP 35 1) * (θ hP 42 1) * (θ hP 56 1) * (θ hP 63 1)) + mono 0 (-1 : ℂ) * (θ hP 70 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 49 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 2) / ((θ hP 7 1) * (θ hP 14 1) * (θ hP 35 1) * (θ hP 42 1) * (θ hP 56 1) * (θ hP 63 1)) + mono 0 (-1 : ℂ) * (θ hP 70 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 49 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 3) / ((θ hP 7 1) * (θ hP 14 1) * (θ hP 35 1) * (θ hP 42 1) * (θ hP 56 1) * (θ hP 63 1)) + mono 0 (-1 : ℂ) * (θ hP 70 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 49 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 4) / ((θ hP 7 1) * (θ hP 14 1) * (θ hP 35 1) * (θ hP 42 1) * (θ hP 56 1) * (θ hP 63 1)) + mono 0 (-1 : ℂ) * (θ hP 70 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 49 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 5) / ((θ hP 7 1) * (θ hP 14 1) * (θ hP 35 1) * (θ hP 42 1) * (θ hP 56 1) * (θ hP 63 1))) +
  mono 1 (1 : ℂ) * (mono 0 (1 : ℂ) * (θ hP 49 1) * ((-hs (kF hP 0))) / ((θ hP 7 1) * (θ hP 42 1) * (θ hP 56 1))) +
  mono 2 (1 : ℂ) * (mono 0 (-1 : ℂ) * ((-hs (kF hP 0))) * ((mono 7 (1:ℂ)) ^ 2) / ((θ hP 49 1) * (θ hP 63 1)) + mono 0 (1 : ℂ) * (θ hP 56 1) * ((-hs (kF hP 0))) / ((θ hP 7 1) * (θ hP 49 1) * (θ hP 63 1)) + mono 0 (-1 : ℂ) * ((-hs (kF hP 0))) * ((mono 7 (1:ℂ)) ^ 2) * ((mono 0 ζ) ^ 3) / ((θ hP 49 1) * (θ hP 63 1)) + mono 0 (-1 : ℂ) * ((-hs (kF hP 0))) * ((mono 7 (1:ℂ)) ^ 2) * ((mono 0 ζ) ^ 4) / ((θ hP 49 1) * (θ hP 63 1)) + mono 0 (-2 : ℂ) * ((-hs (kF hP 0))) * ((mono 7 (1:ℂ)) ^ 2) * ((mono 0 ζ) ^ 2) / ((θ hP 49 1) * (θ hP 63 1)) + mono 0 (-2 : ℂ) * ((-hs (kF hP 0))) * ((mono 7 (1:ℂ)) ^ 2) * ((mono 0 ζ) ^ 5) / ((θ hP 49 1) * (θ hP 63 1)) + mono 0 (1 : ℂ) * (θ hP 56 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 3) / ((θ hP 7 1) * (θ hP 49 1) * (θ hP 63 1)) + mono 0 (1 : ℂ) * (θ hP 56 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 4) / ((θ hP 7 1) * (θ hP 49 1) * (θ hP 63 1)) + mono 0 (2 : ℂ) * (θ hP 56 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 2) / ((θ hP 7 1) * (θ hP 49 1) * (θ hP 63 1)) + mono 0 (2 : ℂ) * (θ hP 56 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 5) / ((θ hP 7 1) * (θ hP 49 1) * (θ hP 63 1)) + mono 0 (1 : ℂ) * (θ hP 70 1) * (θ hP 42 1) * ((-hs (kF hP 0))) / ((θ hP 7 1) * (θ hP 21 1) * (θ hP 49 1) * (θ hP 63 1) * (mono 7 (1:ℂ))) + mono 0 (1 : ℂ) * (θ hP 70 1) * (θ hP 42 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 3) / ((θ hP 7 1) * (θ hP 21 1) * (θ hP 49 1) * (θ hP 63 1) * (mono 7 (1:ℂ))) + mono 0 (1 : ℂ) * (θ hP 70 1) * (θ hP 42 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 4) / ((θ hP 7 1) * (θ hP 21 1) * (θ hP 49 1) * (θ hP 63 1) * (mono 7 (1:ℂ))) + mono 0 (2 : ℂ) * (θ hP 70 1) * (θ hP 42 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 2) / ((θ hP 7 1) * (θ hP 21 1) * (θ hP 49 1) * (θ hP 63 1) * (mono 7 (1:ℂ))) + mono 0 (2 : ℂ) * (θ hP 70 1) * (θ hP 42 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 5) / ((θ hP 7 1) * (θ hP 21 1) * (θ hP 49 1) * (θ hP 63 1) * (mono 7 (1:ℂ))) + mono 0 (-1 : ℂ) * (θ hP 14 1) * (θ hP 35 1) * (θ hP 49 1) * (θ hP 63 1) * ((-hs (kF hP 0))) / ((θ hP 7 1) * (θ hP 70 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 56 1)) + mono 0 (-1 : ℂ) * (θ hP 14 1) * (θ hP 35 1) * (θ hP 49 1) * (θ hP 63 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 2) / ((θ hP 7 1) * (θ hP 70 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 56 1)) + mono 0 (-1 : ℂ) * (θ hP 14 1) * (θ hP 35 1) * (θ hP 49 1) * (θ hP 63 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 3) / ((θ hP 7 1) * (θ hP 70 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 56 1)) + mono 0 (-1 : ℂ) * (θ hP 14 1) * (θ hP 35 1) * (θ hP 49 1) * (θ hP 63 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 4) / ((θ hP 7 1) * (θ hP 70 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 56 1)) + mono 0 (-1 : ℂ) * (θ hP 14 1) * (θ hP 35 1) * (θ hP 49 1) * (θ hP 63 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 5) / ((θ hP 7 1) * (θ hP 70 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 42 1) * (θ hP 56 1))) +
  mono 3 (1 : ℂ) * (mono 0 (1 : ℂ) * (θ hP 49 1) * ((-hs (kF hP 0))) / ((θ hP 14 1) * (θ hP 35 1) * (θ hP 63 1)) + mono 0 (1 : ℂ) * (θ hP 49 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 2) / ((θ hP 14 1) * (θ hP 35 1) * (θ hP 63 1)) + mono 0 (1 : ℂ) * (θ hP 49 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 5) / ((θ hP 14 1) * (θ hP 35 1) * (θ hP 63 1))) +
  mono 4 (1 : ℂ) * (mono 0 (-1 : ℂ) * (θ hP 49 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 2) / ((θ hP 70 1) * (θ hP 21 1) * (θ hP 28 1)) + mono 0 (-1 : ℂ) * (θ hP 49 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 5) / ((θ hP 70 1) * (θ hP 21 1) * (θ hP 28 1))) +
  mono 6 (1 : ℂ) * (mono 0 (1 : ℂ) * ((-hs (kF hP 0))) * (mono 7 (1:ℂ)) * ((mono 0 ζ) ^ 2) / ((θ hP 42 1) * (θ hP 49 1)) + mono 0 (1 : ℂ) * ((-hs (kF hP 0))) * (mono 7 (1:ℂ)) * ((mono 0 ζ) ^ 5) / ((θ hP 42 1) * (θ hP 49 1)) + mono 0 (-1 : ℂ) * ((-hs (kF hP 0))) * (mono 7 (1:ℂ)) * ((mono 0 ζ) ^ 3) / ((θ hP 42 1) * (θ hP 49 1)) + mono 0 (-1 : ℂ) * ((-hs (kF hP 0))) * (mono 7 (1:ℂ)) * ((mono 0 ζ) ^ 4) / ((θ hP 42 1) * (θ hP 49 1)) + mono 0 (1 : ℂ) * (θ hP 35 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 3) / ((θ hP 7 1) * (θ hP 49 1) * (θ hP 63 1)) + mono 0 (1 : ℂ) * (θ hP 35 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 4) / ((θ hP 7 1) * (θ hP 49 1) * (θ hP 63 1)) + mono 0 (-1 : ℂ) * (θ hP 35 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 2) / ((θ hP 7 1) * (θ hP 49 1) * (θ hP 63 1)) + mono 0 (-1 : ℂ) * (θ hP 35 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 5) / ((θ hP 7 1) * (θ hP 49 1) * (θ hP 63 1)) + mono 0 (1 : ℂ) * (θ hP 35 1) * (θ hP 56 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 3) / ((θ hP 7 1) * (θ hP 14 1) * (θ hP 42 1) * (θ hP 49 1) * ((mono 7 (1:ℂ)) ^ 2)) + mono 0 (1 : ℂ) * (θ hP 35 1) * (θ hP 56 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 4) / ((θ hP 7 1) * (θ hP 14 1) * (θ hP 42 1) * (θ hP 49 1) * ((mono 7 (1:ℂ)) ^ 2)) + mono 0 (-1 : ℂ) * (θ hP 35 1) * (θ hP 56 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 2) / ((θ hP 7 1) * (θ hP 14 1) * (θ hP 42 1) * (θ hP 49 1) * ((mono 7 (1:ℂ)) ^ 2)) + mono 0 (-1 : ℂ) * (θ hP 35 1) * (θ hP 56 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 5) / ((θ hP 7 1) * (θ hP 14 1) * (θ hP 42 1) * (θ hP 49 1) * ((mono 7 (1:ℂ)) ^ 2)) + mono 0 (-1 : ℂ) * (θ hP 7 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 56 1) * ((-hs (kF hP 0))) / ((θ hP 70 1) * (θ hP 14 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 35 1) * (θ hP 63 1)) + mono 0 (-1 : ℂ) * (θ hP 7 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 56 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 3) / ((θ hP 70 1) * (θ hP 14 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 35 1) * (θ hP 63 1)) + mono 0 (-1 : ℂ) * (θ hP 7 1) * (θ hP 42 1) * (θ hP 49 1) * (θ hP 56 1) * ((-hs (kF hP 0))) * ((mono 0 ζ) ^ 4) / ((θ hP 70 1) * (θ hP 14 1) * (θ hP 21 1) * (θ hP 28 1) * (θ hP 35 1) * (θ hP 63 1)))


/-! ## Class-0 closure and the class-5 vanishing of the pieces -/

lemma c0_add {f g : L} (hf : InCls 0 f) (hg : InCls 0 g) : InCls 0 (f + g) := hf.add hg
lemma c0_sub {f g : L} (hf : InCls 0 f) (hg : InCls 0 g) : InCls 0 (f - g) := hf.sub hg
lemma c0_neg {f : L} (hf : InCls 0 f) : InCls 0 (-f) := hf.neg
lemma c0_mul {f g : L} (hf : InCls 0 f) (hg : InCls 0 g) : InCls 0 (f * g) := by
  simpa using hf.mul hg
lemma c0_inv {f : L} (hf : InCls 0 f) : InCls 0 f⁻¹ := hf.inv
lemma c0_div {f g : L} (hf : InCls 0 f) (hg : InCls 0 g) : InCls 0 (f / g) := by
  rw [div_eq_mul_inv]; exact c0_mul hf hg.inv
lemma c0_pow {f : L} (hf : InCls 0 f) (k : ℕ) : InCls 0 (f ^ k) := by
  induction k with
  | zero => simpa using InCls.one
  | succ k ih => rw [pow_succ]; exact c0_mul ih hf
lemma c0_mono {e : ℤ} (he : (7 : ℤ) ∣ e) (c : ℂ) : InCls 0 (mono e c) := by
  have := InCls.of_mono e c; rwa [Int.emod_eq_zero_of_dvd he] at this
lemma c0_θ {e : ℤ} (he : (7 : ℤ) ∣ e) : InCls 0 (θ hP e 1) := InCls.θ hP (by norm_num) he 1
lemma c0_k : InCls 0 (hs (kF hP 0)) := by
  refine InCls.hsum _ fun rj => ?_
  rw [kF_apply]
  split_ifs
  · exact c0_mono (Dvd.dvd.mul_right (by norm_num) _) _
  · exact InCls.zero 0

macro "cls0" : tactic => `(tactic| repeat' (first
  | exact c0_k | with_reducible apply c0_add | with_reducible apply c0_sub | with_reducible apply c0_neg
  | with_reducible apply c0_div | with_reducible apply c0_mul | with_reducible apply c0_inv
  | with_reducible apply c0_pow | (with_reducible apply c0_θ; norm_num) | (with_reducible apply c0_mono; norm_num)))

lemma no5_mono_mul {c : ℤ} {f : L} (hf : InCls 0 f) (hc : c % 7 ≠ 5) : No5 (mono c 1 * f) :=
  No5.of_cls (InCls.mono_mul hf c 1) hc

set_option maxHeartbeats 2000000 in
/-- `Θ_g` has no exponent `≡ 5 (mod 7)`. -/
theorem ThetaG_no5 (ζ : ℂ) : No5 (ThetaG ζ) := by
  unfold ThetaG
  repeat' apply No5.add
  all_goals refine no5_mono_mul ?_ (by norm_num)
  all_goals cls0

/-- a class-pure mock summand off class 5. -/
lemma summand_no5 {a β : ℤ} (ha : (7 : ℤ) ∣ a) (hb : (7 : ℤ) ∣ β) (h1 : -((3 * 7 * 7 : ℕ) : ℤ) < a + β)
    (h2 : a + β < ((3 * 7 * 7 : ℕ) : ℤ)) {cx : ℂ} (hx : cx ≠ 0) (e : ℤ) (c : ℂ) (he : e % 7 ≠ 5) :
    No5 (mono e c * (Ab hP h1 h2 cx 1 / θ hP β 1)) :=
  No5.of_cls (InCls.mono_mul (c0_div (InCls.Ab hP (by norm_num) ha hb h1 h2 hx one_ne_zero) (c0_θ hb)) e c) he

/-- the class-5 pair cancels (`orbit7`). -/
lemma pair_cancel {ζ : ℂ} (h7 : ζ ^ 7 = 1) {a2 β2 a1 β1 : ℤ} {h1 : -((3 * 7 * 7 : ℕ) : ℤ) < a2 + β2}
    {h2 : a2 + β2 < ((3 * 7 * 7 : ℕ) : ℤ)} {h1' : -((3 * 7 * 7 : ℕ) : ℤ) < a1 + β1}
    {h2' : a1 + β1 < ((3 * 7 * 7 : ℕ) : ℤ)} {cx : ℂ} {e2 e1 : ℤ} {k2 k1 : ℂ}
    (ha2 : a2 = -49) (hb2 : β2 = 140) (ha1 : a1 = 49) (hb1 : β1 = 7) (hcx : cx = 1)
    (he2 : e2 = -51) (he1 : e1 = -2) (hk2 : k2 = ζ ^ 3) (hk1 : k1 = -ζ ^ 4) :
    mono e2 k2 * (Ab hP h1 h2 cx 1 / θ hP β2 1) +
      mono 0 (ζ ^ 6) * (mono e1 k1 * (Ab hP h1' h2' cx 1 / θ hP β1 1)) = 0 := by
  subst ha2 hb2 ha1 hb1 hcx he2 he1 hk2 hk1
  rw [orbit7]
  have hm : mono (-51) (ζ ^ 3) * mono 49 1 + mono 0 (ζ ^ 6) * mono (-2) (-ζ ^ 4) = 0 := by
    simp only [mono_mul]
    rw [show (-51 : ℤ) + 49 = 0 + -2 by norm_num, mono, mono, ← single_add, single_eq_zero_iff]
    have : ζ ^ 10 = ζ ^ 3 := by rw [show 10 = 7 + 3 by rfl, _root_.pow_add, h7, one_mul]
    linear_combination -this
  linear_combination (Ab hP (a := 49) (β := 7) (by norm_num) (by norm_num) 1 1 / θ hP 7 1) * hm


set_option maxHeartbeats 1000000 in
/-- the mock part `1 − m₂ − ζ⁶ m₁` has no exponent `≡ 5 (mod 7)`: twelve class-pure summands off class 5,
and the class-5 pair cancels. -/
theorem mock_no5 {ζ : ℂ} (h7 : ζ ^ 7 = 1) (h0 : ζ ≠ 0) :
    No5 (1 - msum h3 7 (by norm_num) 2 (ζ ^ 4) ![7, 7, 7, 7, 140, 140, 140] (fun _ => 1)
      (by intro s; fin_cases s <;> simp [spA, c2]) (by intro s; fin_cases s <;> simp [spA, c2]) -
      mono 0 (ζ ^ 6) * msum h3 7 (by norm_num) 1 (ζ ^ 4) ![7, 7, 7, 7, 140, 140, 140] (fun _ => 1)
      (by intro s; fin_cases s <;> simp [spA, c2]) (by intro s; fin_cases s <;> simp [spA, c2])) := by
  have p7 : ∀ k : ℕ, (ζ ^ k) ^ 7 = 1 := fun k => by rw [← pow_mul, mul_comm, pow_mul, h7, one_pow]
  have hx : spCX 7 (ζ ^ 4) ≠ 0 := by simp [spCX, h0]
  have hcx : spCX 7 (ζ ^ 4) = 1 := by rw [spCX, p7]; norm_num
  have z46 : (ζ ^ 4) ^ 6 = ζ ^ 3 := by
    rw [← pow_mul, show 4 * 6 = 7 * 3 + 3 by rfl, _root_.pow_add, pow_mul, h7, one_pow, one_mul]
  have hk6 : (-1 : ℂ) ^ (((6 : Fin 7) : ℕ) : ℤ) * (ζ ^ 4) ^ (((6 : Fin 7) : ℕ) : ℤ) = ζ ^ 3 := by
    show (-1 : ℂ) ^ ((6 : ℕ) : ℤ) * (ζ ^ 4) ^ ((6 : ℕ) : ℤ) = ζ ^ 3
    rw [zpow_natCast, zpow_natCast, z46]; norm_num
  unfold msum
  simp only [Fin.sum_univ_seven]
  have e : ∀ x0 x1 x2 x3 x4 x5 x6 y0 y1 y2 y3 y4 y5 y6 Z : L,
      1 - (x0 + x1 + x2 + x3 + x4 + x5 + x6) - Z * (y0 + y1 + y2 + y3 + y4 + y5 + y6) =
      ((1 - x0 - x1 - x2 - x3 - x4 - x5) - Z * (y0 + y2 + y3 + y4 + y5 + y6)) - (x6 + Z * y1) := by
    intros; ring
  rw [e]
  refine No5.sub (No5.sub ?_ (No5.cls0_mul (c0_mono (dvd_zero 7) _) ?_)) ?_
  · repeat' with_reducible apply No5.sub
    · exact No5.of_cls InCls.one (by norm_num)
    all_goals refine summand_no5 ?_ ?_ _ _ hx _ _ ?_
    all_goals simp [spA, c2]
  · repeat' with_reducible apply No5.add
    all_goals refine summand_no5 ?_ ?_ _ _ hx _ _ ?_
    all_goals simp [spA, c2]
  · convert No5.zero using 1
    with_reducible apply pair_cancel h7
    all_goals first | rfl | (simp [spA, c2]; done) | (norm_num [spA, c2]; done) | exact hcx | exact hk6

end ALz
