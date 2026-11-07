/-
# Seventh pass, basic inputs for `QuadOffHyp`

* `D_le`: `(1 + 4π² m n / T²)^{−A} ≤ (T²/(mn))^s` for `0 ≤ s ≤ A`.
* `abs_tau_mul_rpow`: `|τ(m)τ(n)|(mn)^{−6} = |λ(m)λ(n)|(mn)^{−1/2}`.
* `sum_lam_sq_rpow_le`: `Σ_{m<N} λ(m)² m^{−σ} ≤ S_σ` (Rankin–Selberg, `σ > 1`).
* `sum_rpow_le`: `Σ_{n<N} n^{−σ} ≤ Z_σ`.
* `gl`, `sum_gl_le`: `g(ℓ) = |ℓ|^{−3/2}` summed along any injective map into `ℤ` is `≤ G₀`.
Level 1.
-/
import RamanujanTau.SelbergKey6.RSMajor

set_option autoImplicit false

namespace RamanujanTau.SelbergKey7

open Finset RamanujanTau.SubconvexityCond
open scoped Real

lemma one_le_four_pi_sq : (1 : ℝ) ≤ 4 * π ^ 2 := by
  have := Real.pi_gt_three; nlinarith

/-- **Decay of the weight**: `(1 + 4π² m n/T²)^{−A} ≤ (T²/(mn))^s` for `0 ≤ s ≤ A`. -/
lemma D_le {T m n A s : ℝ} (hT : 0 < T) (hm : 0 < m) (hn : 0 < n) (hs : 0 ≤ s) (hsA : s ≤ A) :
    (1 + 4 * π ^ 2 * m * n / T ^ 2) ^ (-A) ≤ (T ^ 2 / (m * n)) ^ s := by
  set z := m * n / T ^ 2 with hz
  have hz0 : 0 < z := by positivity
  have h4 : z ≤ 4 * π ^ 2 * m * n / T ^ 2 := by
    have e4 : 4 * π ^ 2 * m * n / T ^ 2 = 4 * π ^ 2 * z := by rw [hz]; ring
    rw [e4]
    nlinarith [one_le_four_pi_sq]
  have e : T ^ 2 / (m * n) = z⁻¹ := by rw [hz, inv_div]
  rw [e]
  rcases le_total z 1 with h | h
  · have h1 : (1 + 4 * π ^ 2 * m * n / T ^ 2) ^ (-A) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have h2 : 1 ≤ z⁻¹ ^ s := Real.one_le_rpow (one_le_inv_iff₀.2 ⟨hz0, h⟩) hs
    linarith
  · have h1 : (1 + 4 * π ^ 2 * m * n / T ^ 2) ^ (-A) ≤ z ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos hz0 (by linarith) (by linarith)
    have h2 : z ^ (-A) ≤ z ^ (-s) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
    have e2 : z ^ (-s) = z⁻¹ ^ s := by rw [Real.rpow_neg hz0.le, Real.inv_rpow hz0.le]
    linarith

lemma abs_lam (m : ℕ) : |lam m| = |(tau m : ℝ)| * (m : ℝ) ^ (-(11 / 2 : ℝ)) := by
  unfold lam
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

/-- `|τ(m)τ(n)|(mn)^{−6} = |λ(m)λ(n)|(mn)^{−1/2}`. -/
lemma abs_tau_mul_rpow {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    |(tau m : ℝ)| * |(tau n : ℝ)| * ((m : ℝ) * n) ^ (-6 : ℝ) =
      |lam m| * |lam n| * ((m : ℝ) * n) ^ (-(1 / 2) : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_lam, abs_lam, Real.mul_rpow hm0.le hn0.le, Real.mul_rpow hm0.le hn0.le]
  have e1 : (m : ℝ) ^ (-6 : ℝ) = (m : ℝ) ^ (-(11 / 2 : ℝ)) * (m : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add hm0]; norm_num
  have e2 : (n : ℝ) ^ (-6 : ℝ) = (n : ℝ) ^ (-(11 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add hn0]; norm_num
  rw [e1, e2]; ring

/-- `Σ_{n<N} n^{−σ} ≤ Z_σ`. -/
lemma sum_rpow_le {σ : ℝ} (hσ : 1 < σ) : ∃ Z : ℝ, 0 ≤ Z ∧ ∀ N : ℕ,
    ∑ n ∈ range N, (n : ℝ) ^ (-σ) ≤ Z := by
  have hs : Summable fun n : ℕ => (n : ℝ) ^ (-σ) := Real.summable_nat_rpow.2 (by linarith)
  refine ⟨∑' n : ℕ, (n : ℝ) ^ (-σ), tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _,
    fun N => hs.sum_le_tsum _ fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _⟩

/-- **Rankin–Selberg**: `Σ_{m<N} λ(m)² m^{−σ} ≤ S_σ` for `σ > 1`. -/
lemma sum_lam_sq_rpow_le {σ : ℝ} (hσ : 1 < σ) : ∃ S : ℝ, 0 ≤ S ∧ ∀ N : ℕ,
    ∑ m ∈ range N, lam m ^ 2 * (m : ℝ) ^ (-σ) ≤ S := by
  obtain ⟨A, hA0, hA⟩ := RamanujanTau.SelbergKey6.sum_lam_sq_mul_le
  obtain ⟨Z, hZ0, hZ⟩ := sum_rpow_le hσ
  refine ⟨A * Z, mul_nonneg hA0 hZ0, fun N => ?_⟩
  set G : ℕ → ℝ := fun m => ((max m 1 : ℕ) : ℝ) ^ (-σ)
  have hG0 : ∀ m, 0 ≤ G m := fun m => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hGm : ∀ m, G (m + 1) ≤ G m := by
    intro m
    simp only [G]
    apply Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast (by omega)) (by linarith)
  have hG1 : ∀ i : ℕ, G (i + 1) = ((i + 1 : ℕ) : ℝ) ^ (-σ) := by
    intro i; simp only [G]; congr 2; omega
  cases N with
  | zero => simp; positivity
  | succ N =>
    rw [sum_range_succ']
    have h0 : lam 0 ^ 2 * ((0 : ℕ) : ℝ) ^ (-σ) = 0 := by
      rw [Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero]
    rw [h0, add_zero]
    have h1 := hA G N hG0 hGm
    simp only [hG1] at h1
    have h2 : ∑ i ∈ range N, ((i + 1 : ℕ) : ℝ) ^ (-σ) ≤ Z := by
      have := hZ (N + 1)
      rw [sum_range_succ', Nat.cast_zero, Real.zero_rpow (by linarith), add_zero] at this
      exact this
    calc ∑ i ∈ range N, lam (i + 1) ^ 2 * ((i + 1 : ℕ) : ℝ) ^ (-σ)
        ≤ A * ∑ i ∈ range N, ((i + 1 : ℕ) : ℝ) ^ (-σ) := h1
      _ ≤ A * Z := mul_le_mul_of_nonneg_left h2 hA0

/-- The weight `g(ℓ) = |ℓ|^{−3/2}` on `ℤ`. -/
noncomputable def gl (ℓ : ℤ) : ℝ := |(ℓ : ℝ)| ^ (-(3 / 2 : ℝ))

lemma gl_nonneg (ℓ : ℤ) : 0 ≤ gl ℓ := Real.rpow_nonneg (abs_nonneg _) _

lemma summable_gl : Summable gl := Real.summable_abs_int_rpow (b := 3 / 2) (by norm_num)

/-- `g` summed along an injective map is `≤ G₀`. -/
lemma sum_gl_le : ∃ G₀ : ℝ, 0 ≤ G₀ ∧ ∀ (s : Finset ℕ) (f : ℕ → ℤ), Set.InjOn f s →
    ∑ i ∈ s, gl (f i) ≤ G₀ := by
  classical
  refine ⟨∑' ℓ : ℤ, gl ℓ, tsum_nonneg gl_nonneg, fun s f hf => ?_⟩
  rw [← Finset.sum_image hf]
  exact summable_gl.sum_le_tsum _ fun ℓ _ => gl_nonneg ℓ

/-- `ℓ^{−2} ≤ g(ℓ)` for `ℓ ≠ 0`. -/
lemma inv_sq_le_gl {ℓ : ℤ} (hℓ : ℓ ≠ 0) : 1 / (ℓ : ℝ) ^ 2 ≤ gl ℓ := by
  unfold gl
  have h1 : (1 : ℝ) ≤ |(ℓ : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hℓ
  have h0 : (0 : ℝ) < |(ℓ : ℝ)| := by linarith
  rw [← sq_abs, ← Real.rpow_natCast, one_div, ← Real.rpow_neg h0.le]
  exact Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)

/-- `ℓ^{−2} ≤ L^{−1/2} g(ℓ)` for `|ℓ| ≥ L > 0`. -/
lemma inv_sq_le_gl_mul {ℓ : ℤ} {L : ℝ} (hL : 0 < L) (hℓ : L ≤ |(ℓ : ℝ)|) :
    1 / (ℓ : ℝ) ^ 2 ≤ L ^ (-(1 / 2 : ℝ)) * gl ℓ := by
  unfold gl
  have h0 : (0 : ℝ) < |(ℓ : ℝ)| := by linarith
  rw [← sq_abs, ← Real.rpow_natCast, one_div, ← Real.rpow_neg h0.le]
  have : |(ℓ : ℝ)| ^ (-((2 : ℕ) : ℝ)) = |(ℓ : ℝ)| ^ (-(1 / 2 : ℝ)) * |(ℓ : ℝ)| ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add h0]; norm_num
  rw [this]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg h0.le _)
  exact Real.rpow_le_rpow_of_nonpos hL hℓ (by norm_num)

end RamanujanTau.SelbergKey7
