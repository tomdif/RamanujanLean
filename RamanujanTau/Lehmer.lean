import RamanujanTau.TauBridge

/-! # Lehmer's conjecture for `τ`

**Lehmer's conjecture** (D. H. Lehmer, 1947): `τ(n) ≠ 0` for every `n ≥ 1`.

It is *open*. No proof and no counterexample is known; it has been verified by
computation for all `n` below very large bounds (e.g. `n < 10^{22}` and beyond),
but a general proof is not in reach — so, following this repo's discipline, the
full statement is exposed as a hypothesis class, never an `axiom`.

What we *can* contribute is honest, kernel-owned partial progress: certify the
conjecture on an initial range by direct computation of `τ`. By multiplicativity
(`TauMultiplicative`) and the Hecke recurrence, non-vanishing reduces to the
prime-power case `τ(p^k) ≠ 0`; the finite check below confirms there is no zero
in the verified window, which is exactly the kind of statement the kernel owns
outright (a bounded, decidable computation) even when the universal one is open.
-/

namespace RamanujanTau

/-- **Lehmer's conjecture** (OPEN): `τ(n) ≠ 0` for all `n ≥ 1`. Stated as a class so
downstream results may assume it explicitly; it is never asserted as an axiom. -/
class LehmerConjecture : Prop where
  tau_ne_zero : ∀ n, 1 ≤ n → τ n ≠ 0

/-- `q·∏_{k≤D}(1−qᵏ)²⁴` truncated at degree `D`, computed once. -/
def tauList (D : ℕ) : List ℤ := shiftList 1 (truncPowList D (eulerProductTrunc D D) 24)

/-- one truncation serves every `n ≤ D`. -/
theorem tau_eq_coeffList_tauList {n D : ℕ} (h : n ≤ D) : τ n = coeffList (tauList D) n := by
  rw [tau_eq_tauPS]
  have hq : FourSquares.π (D + 1) (MockTheta5.Bailey.qfac D) = FourSquares.π (D + 1) MockTheta5.JTP.qfacInf := by
    rw [← FourSquares.π_qfac (show D + 1 ≤ D + 1 from le_rfl), FourSquares.qfac_succ', map_mul, map_sub, map_one,
      FourSquares.π_X_pow le_rfl, sub_zero, mul_one]
  have h' : FourSquares.π (D + 1) (toPS (tauList D)) = FourSquares.π (D + 1) (PowerSeries.X * MockTheta5.JTP.qfacInf ^ 24) := by
    rw [tauList, toPS_shiftList_one, map_mul, π_truncPow, π_euler, hq, map_mul, map_pow]
  have hc := FourSquares.coeff_eq_of_dvd (FourSquares.π_eq_iff.mp h') (Nat.lt_succ_of_le h)
  rw [toPS, PowerSeries.coeff_mk] at hc
  rw [hc]; rfl

/-- the kernel check: no zero among the first 100 coefficients. -/
theorem tauList_ne_zero : (List.range 100).all (fun n => coeffList (tauList 100) (n + 1) != 0) = true := by
  decide +kernel

/-- Kernel-verified finite evidence for Lehmer: `τ(n) ≠ 0` for every `1 ≤ n ≤ 100`. The kernel computes
one truncated product (`tauList 100`); `tau_eq_coeffList_tauList` identifies its coefficients with `τ`.
This does **not** prove the conjecture — it certifies the initial range. -/
theorem lehmer_below_101 : ∀ n, n < 101 → 1 ≤ n → τ n ≠ 0 := by
  intro n h1 h2
  have := List.all_eq_true.mp tauList_ne_zero (n - 1) (List.mem_range.mpr (by omega))
  rw [show n - 1 + 1 = n by omega] at this
  rw [tau_eq_coeffList_tauList (show n ≤ 100 by omega)]
  simpa using this

/-- Restated against the lower bound for convenience: no zero of `τ` in `[1, 100]`. -/
theorem tau_ne_zero_of_le_100 {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 100) : τ n ≠ 0 :=
  lehmer_below_101 n (by omega) h1

end RamanujanTau
