/-
# Selberg's quadratic form: diagonalization and exact mollification

* `selberg_diag`: for any real `x` on `[1, Y]`,

      Σ_{h,k≤Y} x_h x_k / [h,k] = Σ_{d≤Y} φ(d) (Σ_{h≤Y, d|h} x_h / h)²

  (`1/[h,k] = (h,k)/(hk)`, `(h,k) = Σ_{d|(h,k)} φ(d)`), so the form is positive semidefinite
  (`selberg_form_nonneg`).  This is the form `Σ_{h,k} c(h)c(k)/[h,k]` of the diagonal of the
  twisted second moment (see `docs/SELBERG_COEFFS.md` §3), before the Rankin–Selberg weights.
* `lamN_mul_trunc_mul_trunc`: for the *unsmoothed* truncation `b₀ = α·1_{[1,y]}`,
  `(λ ∗ b₀ ∗ b₀)(N) = δ(N)` for every `N ≤ y` — the mollifier `M² = Σ (b₀∗b₀)(n)n^{−s}` inverts
  `L` exactly up to length `y`.
-/
import RamanujanTau.SelbergCoeffs.Global

set_option autoImplicit false

namespace RamanujanTau.SelbergCoeffs

open Finset ArithmeticFunction

noncomputable section

lemma inv_lcm_eq (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    (1 : ℝ) / (Nat.lcm h k) = (Nat.gcd h k : ℝ) / ((h : ℝ) * k) := by
  have e : (Nat.gcd h k : ℝ) * (Nat.lcm h k) = (h : ℝ) * k := by
    exact_mod_cast Nat.gcd_mul_lcm h k
  have hl : (0 : ℝ) < Nat.lcm h k := by exact_mod_cast Nat.lcm_pos hh hk
  have hhk : (0 : ℝ) < (h : ℝ) * k := by positivity
  rw [div_eq_div_iff hl.ne' hhk.ne', one_mul, ← e]

lemma gcd_eq_sum_totient (Y h k : ℕ) (hh : 1 ≤ h) (hY : h ≤ Y) (_hk : 1 ≤ k) :
    (Nat.gcd h k : ℝ) = ∑ d ∈ Icc 1 Y, if d ∣ h ∧ d ∣ k then (Nat.totient d : ℝ) else 0 := by
  rw [← Finset.sum_filter]
  have hg : 0 < Nat.gcd h k := Nat.gcd_pos_of_pos_left _ hh
  have hset : (Icc 1 Y).filter (fun d => d ∣ h ∧ d ∣ k) = (Nat.gcd h k).divisors := by
    ext d
    simp only [mem_filter, mem_Icc, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨_, hd⟩; exact ⟨hd, hg.ne'⟩
    · rintro ⟨hd, -⟩
      refine ⟨⟨Nat.pos_of_dvd_of_pos hd.1 hh, (Nat.le_of_dvd hh hd.1).trans hY⟩, hd⟩
  rw [hset]
  exact_mod_cast (Nat.sum_totient (Nat.gcd h k)).symm

/-- **Selberg's diagonalization** of `Σ x_h x_k/[h,k]`. -/
theorem selberg_diag (Y : ℕ) (x : ℕ → ℝ) :
    ∑ h ∈ Icc 1 Y, ∑ k ∈ Icc 1 Y, x h * x k / (Nat.lcm h k) =
      ∑ d ∈ Icc 1 Y, (Nat.totient d : ℝ) *
        (∑ h ∈ Icc 1 Y, if d ∣ h then x h / h else 0) ^ 2 := by
  have step : ∀ h ∈ Icc 1 Y, ∀ k ∈ Icc 1 Y, x h * x k / (Nat.lcm h k) =
      ∑ d ∈ Icc 1 Y, (Nat.totient d : ℝ) *
        ((if d ∣ h then x h / h else 0) * (if d ∣ k then x k / k else 0)) := by
    intro h hh k hk
    rw [mem_Icc] at hh hk
    rw [div_eq_mul_one_div, inv_lcm_eq h k (by omega) (by omega),
      gcd_eq_sum_totient Y h k hh.1 hh.2 hk.1, mul_div_assoc', Finset.mul_sum, Finset.sum_div]
    refine sum_congr rfl fun d _ => ?_
    by_cases h1 : d ∣ h <;> by_cases h2 : d ∣ k <;> simp [h1, h2] <;> ring
  rw [sum_congr rfl fun h hh => sum_congr rfl fun k hk => step h hh k hk]
  rw [sum_congr rfl fun h _ => sum_comm, sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [sq, sum_mul_sum, mul_sum]
  refine sum_congr rfl fun h _ => ?_
  rw [mul_sum]

/-- The form `Σ x_h x_k/[h,k]` is positive semidefinite. -/
theorem selberg_form_nonneg (Y : ℕ) (x : ℕ → ℝ) :
    0 ≤ ∑ h ∈ Icc 1 Y, ∑ k ∈ Icc 1 Y, x h * x k / (Nat.lcm h k) := by
  rw [selberg_diag]
  exact sum_nonneg fun d _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- Dirichlet convolution at `n` only sees values at `m ≤ n`. -/
lemma mul_apply_congr_le {f f' g g' : ArithmeticFunction ℝ} {M : ℕ}
    (hf : ∀ m, m ≤ M → f m = f' m) (hg : ∀ m, m ≤ M → g m = g' m) :
    ∀ n, n ≤ M → (f * g) n = (f' * g') n := by
  intro n hn
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  rw [mul_apply, mul_apply]
  refine sum_congr rfl fun x hx => ?_
  have h1 := Nat.fst_mem_divisors_of_mem_antidiagonal hx
  have h2 := Nat.snd_mem_divisors_of_mem_antidiagonal hx
  rw [Nat.mem_divisors] at h1 h2
  rw [hf _ ((Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h1.1).trans hn),
    hg _ ((Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h2.1).trans hn)]

/-- The unsmoothed truncation `b₀ = α · 1_{[1,y]}`. -/
def alphaTrunc (y : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≤ y then alpha n else 0, by simp⟩

/-- **Exact mollification up to `y`**: `(λ ∗ b₀ ∗ b₀)(N) = δ(N)` for all `N ≤ y`. -/
theorem lamN_mul_trunc_mul_trunc (y N : ℕ) (hN : N ≤ y) :
    (lamN * alphaTrunc y * alphaTrunc y) N = (1 : ArithmeticFunction ℝ) N := by
  have ht : ∀ m, m ≤ y → alphaTrunc y m = alpha m := fun m hm => by
    simp [alphaTrunc, hm]
  have h1 : ∀ m, m ≤ y → (lamN * alphaTrunc y) m = (lamN * alpha) m :=
    mul_apply_congr_le (fun _ _ => rfl) ht
  rw [mul_apply_congr_le h1 ht N hN, lamN_mul_alpha_mul_alpha]

end

end RamanujanTau.SelbergCoeffs
