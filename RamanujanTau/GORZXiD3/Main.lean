/-
# GORZ Theorem 2, `d = 3`, for Riemann's `Ξ` (Dimitrov–Lucas): reduction to the Turán-defect Lipschitz property

`γ = gammaMathlib` (GORZ normalization, from Mathlib's `completedRiemannZeta`).

* **`gamma_pos`** (unconditional): `γ(n) > 0` for every `n`, from `GORZXiEff.gamma_eq_mom`.
* **`jensen3_gamma_of_hot`** (unconditional reduction): the higher-order Turán inequality
  `4(γ₁²−γ₀γ₂)(γ₂²−γ₁γ₃) ≥ (γ₁γ₂−γ₀γ₃)²` at shift `n` implies `J^{3,n}_γ` hyperbolic.
* **`DLHyp`** (named hypothesis): for every `n`, the Turán defect `a_n = 1 − γ(n)γ(n+2)/γ(n+1)²` is `> 0`, and
  `|a_{n+1}^{-1/2} − a_n^{-1/2}| ≤ 1`.
* **`jensen3_gamma`**: `J^{3,n}_γ` is hyperbolic for **every** `n ≥ 0`, conditional on `DLHyp`.
* **`dlHyp_iff`**: `DLHyp ⟺ ∀ n, (γ(n)γ(n+2) < γ(n+1)² ∧ HOT(n) ≥ 0)`, i.e. the hypothesis is *exactly* the strict
  Turán inequalities together with the Dimitrov–Lucas higher-order Turán inequalities (no hidden strength).
* **`dlHyp_of_mono`**: the sufficient split "defect positive, nonincreasing, and
  `a_n ≤ a_{n+1}(1+√a_n)²`" implies `DLHyp`.
-/
import RamanujanTau.GORZXiD3.Lipschitz
import RamanujanTau.GORZXiEff.Main

set_option autoImplicit false

namespace GORZXiD3

open Real GORZXi GORZXiEff JensenThreshold

/-- `γ(n) > 0` for every `n` (unconditional). -/
theorem gamma_pos (n : ℕ) : 0 < gammaMathlib n := by
  rw [gamma_eq_mom]
  exact mul_pos (mul_pos (by norm_num) (fq_pos n)) (mom_pos kernelMom_PhiR _)

/-- **HOT ⇒ `J^{3,n}_γ` hyperbolic** (unconditional reduction). -/
theorem jensen3_gamma_of_hot {n : ℕ} (h : 0 ≤ hot gammaMathlib n) :
    Hyperbolic (jensenSeq gammaMathlib 3 n) :=
  jensen3_of_hot (gamma_pos _) h

/-- **Named hypothesis**: the Turán defect `a_n = 1 − γ(n)γ(n+2)/γ(n+1)²` of `Ξ` is positive and
`n ↦ a_n^{-1/2}` is `1`-Lipschitz.  Numerically (level 4, `scripts/gorzxi_d3/hot_numerics.py`, `n ≤ 3000`):
`a_n^{-1/2}` is strictly increasing with increments in `[0.0103, 0.326]`. -/
def DLHyp : Prop :=
  ∀ n : ℕ, 0 < tdef gammaMathlib n ∧ |lam gammaMathlib (n + 1) - lam gammaMathlib n| ≤ 1

/-- the Dimitrov–Lucas higher-order Turán inequalities for `Ξ`, conditional on `DLHyp`. -/
theorem hot_gamma (h : DLHyp) (n : ℕ) : 0 ≤ hot gammaMathlib n :=
  (hot_nonneg_iff_lip gamma_pos (h n).1 (h (n + 1)).1).2 (h n).2

/-- **GORZ Theorem 2, `d = 3`**: `J^{3,n}_γ` is hyperbolic for every `n ≥ 0`, conditional on `DLHyp`. -/
theorem jensen3_gamma (h : DLHyp) (n : ℕ) : Hyperbolic (jensenSeq gammaMathlib 3 n) :=
  jensen3_gamma_of_hot (hot_gamma h n)

lemma tdef_pos_iff (n : ℕ) :
    0 < tdef gammaMathlib n ↔ gammaMathlib n * gammaMathlib (n + 2) < gammaMathlib (n + 1) ^ 2 := by
  have h1 : 0 < gammaMathlib (n + 1) ^ 2 := pow_pos (gamma_pos _) 2
  unfold tdef
  rw [sub_pos, div_lt_one h1]

/-- `DLHyp` is *equivalent* to strict Turán + higher-order Turán for all `n`. -/
theorem dlHyp_iff : DLHyp ↔ ∀ n : ℕ,
    gammaMathlib n * gammaMathlib (n + 2) < gammaMathlib (n + 1) ^ 2 ∧ 0 ≤ hot gammaMathlib n := by
  constructor
  · intro h n
    exact ⟨(tdef_pos_iff n).1 (h n).1, hot_gamma h n⟩
  · intro h n
    have hA := (tdef_pos_iff n).2 (h n).1
    have hB := (tdef_pos_iff (n + 1)).2 (h (n + 1)).1
    exact ⟨hA, (hot_nonneg_iff_lip gamma_pos hA hB).1 (h n).2⟩

/-- sufficient split of `DLHyp`: positive, nonincreasing, slowly collapsing Turán defect. -/
theorem dlHyp_of_mono (hpos : ∀ n, 0 < tdef gammaMathlib n)
    (hmono : ∀ n, tdef gammaMathlib (n + 1) ≤ tdef gammaMathlib n)
    (hslow : ∀ n, tdef gammaMathlib n ≤
      tdef gammaMathlib (n + 1) * (1 + Real.sqrt (tdef gammaMathlib n)) ^ 2) : DLHyp :=
  fun n => ⟨hpos n, lip_of_mono (hpos (n + 1)) (hmono n) (hslow n)⟩

end GORZXiD3

#print axioms GORZXiD3.hyperbolic_cubic
#print axioms GORZXiD3.jensen3_of_hot
#print axioms GORZXiD3.hot_nonneg_iff_lip
#print axioms GORZXiD3.gamma_pos
#print axioms GORZXiD3.jensen3_gamma_of_hot
#print axioms GORZXiD3.hot_gamma
#print axioms GORZXiD3.jensen3_gamma
#print axioms GORZXiD3.dlHyp_iff
#print axioms GORZXiD3.dlHyp_of_mono
