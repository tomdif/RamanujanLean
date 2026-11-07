/-
# Integer-coefficient instances: `Δ·E₄`, `Δ·E₆`, `Δ·E₈`, `Δ·E₁₀`, `Δ·E₁₄`

`BoylanWebb.IntForm k a` says the integer series `a` is the q-expansion of a level-one modular form
of weight `k`; it contains `Δ = q∏(1−qⁿ)²⁴`, `E₄ = p4`, `E₆ = p6` and is closed under products.
`rankinSelberg_intForm`: for such `a` with `a(0) = 0`, `a ≠ 0`, there is a cusp form `F` with
q-expansion `a` and

    (1/N) ∑_{n≤N} a(n)²/n^{k−1} → c_F = (3/π)(4π)^k ‖F‖²/(k−1)! > 0.

`deltaE a b = Δ·E₄ᵃE₆ᵇ` has weight `12 + 4a + 6b`; the one-dimensional spaces `S_k`,
`k = 16, 18, 20, 22, 26`, are spanned by `ΔE₄, ΔE₆, ΔE₄², ΔE₄E₆, ΔE₄²E₆` (`E₈ = E₄²`,
`E₁₀ = E₄E₆`, `E₁₄ = E₄²E₆`); these series are normalized (`a(1) = 1`).
-/
import RamanujanTau.RankinSelbergGeneral.Positive
import RamanujanTau.BoylanWebb.Forms

set_option autoImplicit false

namespace RamanujanTau.RankinSelbergGeneral

open Finset Real Filter Topology
open ModularForm BoylanWebb
open RamanujanTau.Mod691 (p4 p6 sig3 sig5)
open UpperHalfPlane hiding I
open scoped MatrixGroups

/-- **Rankin–Selberg for an integral cusp form given by its integer q-expansion.** -/
theorem rankinSelberg_intForm {k : ℕ} (hk : 1 ≤ k) {a : PowerSeries ℤ} (ha : IntForm (k : ℤ) a)
    (h0 : PowerSeries.coeff 0 a = 0) (hne : a ≠ 0) :
    ∃ F : CuspForm 𝒮ℒ (k : ℤ), qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) a ∧
      0 < rsConst F ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ((PowerSeries.coeff n a : ℤ) : ℝ) ^ 2 /
        (n : ℝ) ^ (k - 1)) / N) atTop (𝓝 (rsConst F)) := by
  obtain ⟨F, hF⟩ := ha
  have hc0 : (qExpansion 1 F).coeff 0 = 0 := by
    rw [hF, PowerSeries.coeff_map, h0, map_zero]
  set f := ModularForm.toCuspForm F hc0
  have hqf : qExpansion 1 f = qExpansion 1 F := rfl
  have hf : f ≠ 0 := by
    intro h
    apply hne
    have hz : qExpansion 1 f = 0 := by
      rw [h]; exact qExpansion_zero 1
    rw [hqf, hF] at hz
    exact map_injC (by rw [hz, map_zero])
  refine ⟨f, hqf.trans hF, rsConst_pos f hf, ?_⟩
  refine (tendsto_S f hk).congr fun N => ?_
  unfold S coeffSq
  congr 1
  refine sum_congr rfl fun n _ => ?_
  rw [hqf, hF, PowerSeries.coeff_map, eq_intCast, Complex.norm_intCast, sq_abs]

/-- `Δ·E₄ᵃ·E₆ᵇ` as an integer q-series. -/
noncomputable def deltaE (a b : ℕ) : PowerSeries ℤ :=
  (PowerSeries.X * MockTheta5.JTP.qfacInf ^ 24) * (p4 ^ a * p6 ^ b)

lemma intForm_deltaE (a b : ℕ) : IntForm ((12 + 4 * a + 6 * b : ℕ) : ℤ) (deltaE a b) :=
  (IntForm.disc.mul (IntForm.mono a b)).cast (by push_cast; ring)

lemma coeff_zero_deltaE (a b : ℕ) : PowerSeries.coeff 0 (deltaE a b) = 0 := by
  rw [deltaE, mul_assoc, PowerSeries.coeff_zero_X_mul]

lemma constantCoeff_p4 : PowerSeries.constantCoeff p4 = 1 := by
  rw [p4, map_add, map_one, map_mul, sig3, PowerSeries.constantCoeff_mk]
  simp

lemma constantCoeff_p6 : PowerSeries.constantCoeff p6 = 1 := by
  rw [p6, map_sub, map_one, map_mul, sig5, PowerSeries.constantCoeff_mk]
  simp

lemma coeff_one_deltaE (a b : ℕ) : PowerSeries.coeff 1 (deltaE a b) = 1 := by
  rw [deltaE, mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_mul, map_mul, map_pow, map_pow, map_pow, constantCoeff_p4, constantCoeff_p6,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, MockTheta5.JTP.coeff_zero_qfacInf]
  simp

lemma deltaE_ne_zero (a b : ℕ) : deltaE a b ≠ 0 := by
  intro h
  have := coeff_one_deltaE a b
  rw [h, map_zero] at this
  exact zero_ne_one this

/-- **Rankin–Selberg for `Δ·E₄ᵃE₆ᵇ`**, weight `k = 12 + 4a + 6b`, in its integer coefficients. -/
theorem rankinSelberg_deltaE (a b : ℕ) :
    ∃ F : CuspForm 𝒮ℒ ((12 + 4 * a + 6 * b : ℕ) : ℤ),
      qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) (deltaE a b) ∧ 0 < rsConst F ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ((PowerSeries.coeff n (deltaE a b) : ℤ) : ℝ) ^ 2 /
        (n : ℝ) ^ (12 + 4 * a + 6 * b - 1)) / N) atTop (𝓝 (rsConst F)) :=
  rankinSelberg_intForm (by omega) (intForm_deltaE a b) (coeff_zero_deltaE a b) (deltaE_ne_zero a b)

/-- Weight 16: `f = ΔE₄`, `(1/N)∑ a(n)²/n¹⁵ → c_f > 0`. -/
theorem rankinSelberg_weight16 :
    ∃ F : CuspForm 𝒮ℒ ((16 : ℕ) : ℤ),
      qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) (deltaE 1 0) ∧ 0 < rsConst F ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ((PowerSeries.coeff n (deltaE 1 0) : ℤ) : ℝ) ^ 2 /
        (n : ℝ) ^ 15) / N) atTop (𝓝 (rsConst F)) :=
  rankinSelberg_deltaE 1 0

/-- Weight 18: `f = ΔE₆`. -/
theorem rankinSelberg_weight18 :
    ∃ F : CuspForm 𝒮ℒ ((18 : ℕ) : ℤ),
      qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) (deltaE 0 1) ∧ 0 < rsConst F ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ((PowerSeries.coeff n (deltaE 0 1) : ℤ) : ℝ) ^ 2 /
        (n : ℝ) ^ 17) / N) atTop (𝓝 (rsConst F)) :=
  rankinSelberg_deltaE 0 1

/-- Weight 20: `f = ΔE₈ = ΔE₄²`. -/
theorem rankinSelberg_weight20 :
    ∃ F : CuspForm 𝒮ℒ ((20 : ℕ) : ℤ),
      qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) (deltaE 2 0) ∧ 0 < rsConst F ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ((PowerSeries.coeff n (deltaE 2 0) : ℤ) : ℝ) ^ 2 /
        (n : ℝ) ^ 19) / N) atTop (𝓝 (rsConst F)) :=
  rankinSelberg_deltaE 2 0

/-- Weight 22: `f = ΔE₁₀ = ΔE₄E₆`. -/
theorem rankinSelberg_weight22 :
    ∃ F : CuspForm 𝒮ℒ ((22 : ℕ) : ℤ),
      qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) (deltaE 1 1) ∧ 0 < rsConst F ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ((PowerSeries.coeff n (deltaE 1 1) : ℤ) : ℝ) ^ 2 /
        (n : ℝ) ^ 21) / N) atTop (𝓝 (rsConst F)) :=
  rankinSelberg_deltaE 1 1

/-- Weight 26: `f = ΔE₁₄ = ΔE₄²E₆`. -/
theorem rankinSelberg_weight26 :
    ∃ F : CuspForm 𝒮ℒ ((26 : ℕ) : ℤ),
      qExpansion 1 F = PowerSeries.map (Int.castRingHom ℂ) (deltaE 2 1) ∧ 0 < rsConst F ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ((PowerSeries.coeff n (deltaE 2 1) : ℤ) : ℝ) ^ 2 /
        (n : ℝ) ^ 25) / N) atTop (𝓝 (rsConst F)) :=
  rankinSelberg_deltaE 2 1

end RamanujanTau.RankinSelbergGeneral

#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_intForm
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_deltaE
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_weight16
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_weight18
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_weight20
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_weight22
#print axioms RamanujanTau.RankinSelbergGeneral.rankinSelberg_weight26
