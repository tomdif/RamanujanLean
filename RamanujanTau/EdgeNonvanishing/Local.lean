/-
# Local positivity for the edge non-vanishing of `L(Δ,s)`

Pure algebra, one prime at a time.  With Satake parameters `α, β` (`αβ = 1`, `α + β` real),
a unit `e` with inverse `e'` (`e + e'` real), and `0 ≤ x` small, the 25-parameter local factor

  `(1−x)⁻¹ · [(1−αex)(1−βex)]⁻² · [(1−αe'x)(1−βe'x)]⁻² · [(1−x)²(1−α²x)(1−β²x)]⁻²`
  `· [(1−e²x)²(1−α²e²x)(1−β²e²x)]⁻¹ · [(1−e'²x)²(1−α²e'²x)(1−β²e'²x)]⁻¹`

is `exp ℓ` with `ℓ = ∑_k (1 + A_k E_k)² x^k / k ≥ 0`, `A_k = α^k + β^k`, `E_k = e^k + e'^k`
(real).  This is the local form of `L(Π × Π̃, s)` for `Π = 1 ⊞ f|·|^{it} ⊞ f|·|^{−it}`.
No bound on `α` beyond `‖α‖² x < 1` is used (no Deligne).
-/
import Mathlib

set_option autoImplicit false

namespace RamanujanTau.EdgeNonvanishing

open Complex

/-- The real sequence `s₀ = 2, s₁ = r, s_{k+2} = r s_{k+1} − s_k` (power sums of a reciprocal pair). -/
noncomputable def pseq (r : ℝ) : ℕ → ℝ
  | 0 => 2
  | 1 => r
  | (k + 2) => r * pseq r (k + 1) - pseq r k

lemma pow_add_pow_eq_pseq {x y : ℂ} {r : ℝ} (hs : x + y = r) (hp : x * y = 1) :
    ∀ k, x ^ k + y ^ k = pseq r k := by
  have key : ∀ k, x ^ k + y ^ k = pseq r k ∧ x ^ (k + 1) + y ^ (k + 1) = pseq r (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨by simp [pseq]; norm_num, by simpa [pseq] using hs⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h2 : pseq r (k + 1 + 1) = r * pseq r (k + 1) - pseq r k := rfl
      rw [h2]; push_cast
      rw [← ih.1, ← ih.2, ← hs]
      linear_combination (-(x ^ k) - y ^ k) * hp
  exact fun k => (key k).1

/-- `∏ (1 − z)⁻¹ = exp (∑ −log(1−z))` and `∑_k (∑ z^k)/k` sums to `∑ −log(1−z)` on the unit disk. -/
lemma list_log (l : List ℂ) (hl : ∀ z ∈ l, ‖z‖ < 1) :
    HasSum (fun k : ℕ => (l.map (fun z => z ^ k)).sum / k) (l.map (fun z => -log (1 - z))).sum ∧
    ((l.map (fun z => 1 - z)).prod)⁻¹ = exp (l.map (fun z => -log (1 - z))).sum := by
  induction l with
  | nil => simp
  | cons z l ih =>
    have hz : ‖z‖ < 1 := hl z (by simp)
    obtain ⟨ih1, ih2⟩ := ih fun w hw => hl w (by simp [hw])
    have hz1 : 1 - z ≠ 0 := by
      intro h
      have : z = 1 := by linear_combination -h
      rw [this] at hz; simp at hz
    simp only [List.map_cons, List.sum_cons, List.prod_cons, add_div]
    refine ⟨(hasSum_taylorSeries_neg_log hz).add ih1, ?_⟩
    rw [mul_inv, ih2, Complex.exp_add, Complex.exp_neg, Complex.exp_log hz1]

/-- The 25 Satake parameters of `Π × Π̃`. -/
def gammas (α β e e' : ℂ) : List ℂ :=
  [1, α * e, β * e, α * e, β * e, α * e', β * e', α * e', β * e',
   1, 1, α ^ 2, β ^ 2, 1, 1, α ^ 2, β ^ 2,
   e ^ 2, e ^ 2, α ^ 2 * e ^ 2, β ^ 2 * e ^ 2,
   e' ^ 2, e' ^ 2, α ^ 2 * e' ^ 2, β ^ 2 * e' ^ 2]

/-- The block form of the local polynomial (reciprocal of the local factor). -/
def localD (α β e e' X : ℂ) : ℂ :=
  (1 - X) * ((1 - α * e * X) * (1 - β * e * X)) ^ 2 * ((1 - α * e' * X) * (1 - β * e' * X)) ^ 2 *
    ((1 - X) ^ 2 * (1 - α ^ 2 * X) * (1 - β ^ 2 * X)) ^ 2 *
    ((1 - e ^ 2 * X) ^ 2 * (1 - α ^ 2 * e ^ 2 * X) * (1 - β ^ 2 * e ^ 2 * X)) *
    ((1 - e' ^ 2 * X) ^ 2 * (1 - α ^ 2 * e' ^ 2 * X) * (1 - β ^ 2 * e' ^ 2 * X))

lemma localD_eq (α β e e' X : ℂ) :
    localD α β e e' X = (((gammas α β e e').map (fun γ => γ * X)).map (fun z => 1 - z)).prod := by
  simp only [localD, gammas, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, one_mul,
    mul_one, sq]
  ac_rfl

/-- Power sums of the 25 parameters: `∑ γ^k = (1 + A_k E_k)²`. -/
lemma gammas_powsum (α β e e' : ℂ) (k : ℕ) (hab : α * β = 1) (hee : e * e' = 1) :
    ((gammas α β e e').map (fun γ => γ ^ k)).sum =
      (1 + (α ^ k + β ^ k) * (e ^ k + e' ^ k)) ^ 2 := by
  have hab' : α ^ k * β ^ k = 1 := by rw [← mul_pow, hab, one_pow]
  have hee' : e ^ k * e' ^ k = 1 := by rw [← mul_pow, hee, one_pow]
  have p2 : ∀ z : ℂ, (z ^ 2) ^ k = (z ^ k) ^ 2 := fun z => by rw [← pow_mul, mul_comm, pow_mul]
  simp only [gammas, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mul_pow, p2,
    one_pow]
  linear_combination (-2 * ((e ^ k) ^ 2 + (e' ^ k) ^ 2) - 4 * (e ^ k * e' ^ k)) * hab' +
    (-2 * ((α ^ k) ^ 2 + (β ^ k) ^ 2) - 4) * hee'

/-- **Local positivity.** -/
theorem localD_inv_eq_exp (α β e e' : ℂ) (r μ x : ℝ) (hx : 0 ≤ x) (hab : α * β = 1)
    (hs : α + β = r) (hee : e * e' = 1) (he : e + e' = μ) (hα1 : 1 ≤ ‖α‖) (hβ : ‖β‖ ≤ 1)
    (he1 : ‖e‖ = 1) (he1' : ‖e'‖ = 1) (hαx : ‖α‖ ^ 2 * x < 1) :
    ∃ ℓ : ℝ, 0 ≤ ℓ ∧ (localD α β e e' (x : ℂ))⁻¹ = ((Real.exp ℓ : ℝ) : ℂ) := by
  set l := (gammas α β e e').map (fun γ => γ * (x : ℂ))
  have hA : 1 ≤ ‖α‖ ^ 2 := by nlinarith
  have hbound : ∀ γ ∈ gammas α β e e', ‖γ‖ ≤ ‖α‖ ^ 2 := by
    intro γ hγ
    have hβ2 : ‖β‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg β]
    have hα2 : ‖α‖ ≤ ‖α‖ ^ 2 := by nlinarith
    simp only [gammas, List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h <;> subst h <;>
      simp only [norm_mul, norm_pow, he1, he1', one_pow, mul_one, norm_one] <;> nlinarith
  have hl : ∀ z ∈ l, ‖z‖ < 1 := by
    intro z hz
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hz
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
    calc ‖γ‖ * x ≤ ‖α‖ ^ 2 * x := mul_le_mul_of_nonneg_right (hbound γ hγ) hx
      _ < 1 := hαx
  obtain ⟨h1, h2⟩ := list_log l hl
  set ℓC := (l.map (fun z => -log (1 - z))).sum
  -- the coefficients are real and nonnegative
  set c : ℕ → ℝ := fun k => (1 + pseq r k * pseq μ k) ^ 2 * x ^ k / k
  have hc : ∀ k, (l.map (fun z => z ^ k)).sum / k = (c k : ℂ) := by
    intro k
    have : (l.map (fun z => z ^ k)).sum = ((gammas α β e e').map (fun γ => γ ^ k)).sum * (x : ℂ) ^ k := by
      simp only [l, List.map_map]
      rw [← List.sum_map_mul_right]
      congr 1
      apply List.map_congr_left
      intro γ _
      simp [mul_pow]
    rw [this, gammas_powsum α β e e' k hab hee, pow_add_pow_eq_pseq hs hab,
      pow_add_pow_eq_pseq he hee]
    simp only [c]; push_cast; ring
  simp_rw [hc] at h1
  have hsum : Summable c := Complex.summable_ofReal.mp h1.summable
  have hℓ : ℓC = ((∑' k, c k : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; exact h1.tsum_eq.symm
  refine ⟨∑' k, c k, tsum_nonneg fun k => by positivity, ?_⟩
  rw [localD_eq, h2, hℓ, Complex.ofReal_exp]

end RamanujanTau.EdgeNonvanishing
