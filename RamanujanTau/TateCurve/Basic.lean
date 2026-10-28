import RamanujanTau.TauModular

/-!
# The Tate curve over `ℤ⟦q⟧` and its discriminant

`Tate : y² + xy = x³ + a₄(q)x + a₆(q)`, `a₄ = −5s₃`, `a₆ = −(5s₃ + 7s₅)/12` (integral), with
`c₄ = E₄ = 1 + 240s₃`, `c₆ = −E₆ = −(1 − 504s₅)` and `Δ = q∏(1 − qⁿ)²⁴` (from the repo's
`discriminant_formal_identity : 1728·q(q;q)²⁴ = E₄³ − E₆²`).
-/

set_option autoImplicit false

namespace TateCurve
open PowerSeries
open scoped ArithmeticFunction.sigma

/-- `s k = ∑_{n ≥ 1} σ_k(n) qⁿ` (the `n = 0` coefficient is `σ_k 0 = 0`). -/
noncomputable def s (k : ℕ) : PowerSeries ℤ := mk fun n => (σ k n : ℤ)

lemma coeff_s (k n : ℕ) : coeff n (s k) = (σ k n : ℤ) := coeff_mk _ _

lemma s3_eq : s 3 = RamanujanTau.Mod691.sig3 := rfl
lemma s5_eq : s 5 = RamanujanTau.Mod691.sig5 := rfl

lemma twelve_dvd (d : ℤ) : (12 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
  have key : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (5 * d ^ 3 + 7 * d ^ 5) 12).mp
  push_cast at h
  exact_mod_cast h (key _)

/-- The integer `(5 σ₃(n) + 7 σ₅(n)) / 12`, written divisor-wise. -/
def a6coeff (n : ℕ) : ℤ := ∑ d ∈ n.divisors, (5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) / 12

lemma twelve_mul_a6coeff (n : ℕ) : 12 * a6coeff n = 5 * (σ 3 n : ℤ) + 7 * (σ 5 n : ℤ) := by
  rw [a6coeff, Finset.mul_sum, ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Int.mul_ediv_cancel' (twelve_dvd d)]

/-- `a₄(q) = −5 s₃(q)`. -/
noncomputable def a4 : PowerSeries ℤ := -5 * s 3

/-- `a₆(q) = −(5 s₃(q) + 7 s₅(q))/12`, with integral coefficients. -/
noncomputable def a6 : PowerSeries ℤ := mk fun n => -a6coeff n

lemma coeff_ofInt_mul (k : ℤ) (f : PowerSeries ℤ) (n : ℕ) :
    coeff n ((k : PowerSeries ℤ) * f) = k * coeff n f := by
  rw [← zsmul_eq_mul, map_smul, smul_eq_mul]

theorem twelve_mul_a6 : 12 * a6 = -(5 * s 3 + 7 * s 5) := by
  ext n
  have h12 : (12 : PowerSeries ℤ) = ((12 : ℤ) : PowerSeries ℤ) := by norm_cast
  have h5 : (5 : PowerSeries ℤ) = ((5 : ℤ) : PowerSeries ℤ) := by norm_cast
  have h7 : (7 : PowerSeries ℤ) = ((7 : ℤ) : PowerSeries ℤ) := by norm_cast
  rw [h12, h5, h7, coeff_ofInt_mul, map_neg, map_add, coeff_ofInt_mul, coeff_ofInt_mul, a6, coeff_mk,
    coeff_s, coeff_s, mul_neg, twelve_mul_a6coeff]

/-- **The Tate curve** `y² + xy = x³ + a₄(q) x + a₆(q)` over `ℤ⟦q⟧`. -/
noncomputable def Tate : WeierstrassCurve (PowerSeries ℤ) where
  a₁ := 1
  a₂ := 0
  a₃ := 0
  a₄ := a4
  a₆ := a6

/-- `c₄(Tate) = E₄(q) = 1 + 240 s₃(q)`. -/
theorem c₄_Tate : Tate.c₄ = 1 + 240 * s 3 := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, Tate, a4]
  ring

/-- `c₆(Tate) = −E₆(q) = −(1 − 504 s₅(q))`. -/
theorem c₆_Tate : Tate.c₆ = -(1 - 504 * s 5) := by
  simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, Tate,
    a4]
  linear_combination (-72 : PowerSeries ℤ) * twelve_mul_a6

theorem c₄_Tate_eq_p4 : Tate.c₄ = RamanujanTau.Mod691.p4 := c₄_Tate
theorem c₆_Tate_eq_neg_p6 : Tate.c₆ = -RamanujanTau.Mod691.p6 := c₆_Tate

/-- **The discriminant of the Tate curve**: `Δ(Tate) = q ∏_{n ≥ 1} (1 − qⁿ)²⁴`. -/
theorem Δ_Tate : Tate.Δ = X * MockTheta5.JTP.qfacInf ^ 24 := by
  have h1728 : (1728 : PowerSeries ℤ) ≠ 0 := by
    intro h
    have := congrArg (coeff 0) h
    rw [show (1728 : PowerSeries ℤ) = C (1728 : ℤ) by simp, coeff_C] at this
    simp at this
  apply mul_left_cancel₀ h1728
  rw [WeierstrassCurve.c_relation, c₄_Tate_eq_p4, c₆_Tate_eq_neg_p6, neg_sq,
    RamanujanTau.TauModular.discriminant_formal_identity]

/-- Coefficientwise: `[qⁿ] Δ(Tate) = τ(n)`. -/
theorem coeff_Δ_Tate (n : ℕ) : coeff n Tate.Δ = TauCong.tauPS n := by
  rw [Δ_Tate]; rfl

end TateCurve
