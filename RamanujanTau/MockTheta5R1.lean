/-
# Ramanujan's fifth-order mock-theta relation R1 — infinite statement (scoping)

`MockTheta5.lean` verifies **R1** `χ₀ = 2F₀ − φ₀(−q)` only to order `q⁴⁸` via `native_decide` ("rung 2",
compiler trust). This file lifts the fifth-order mock-theta functions to genuine **infinite** power series
`PowerSeries ℤ` (via coefficient stabilization), so R1 can be stated — and eventually proved — as a
kernel theorem ("rung 3"). The functions reuse the q-series library built in this campaign
(`oddFac = (q;q²)_n`, `negOddFac = (−q;q²)_n`).

**R1 target:** `chi0 = 2 • F0 − phi0neg` in `PowerSeries ℤ` (with `phi0neg = φ₀(−q)`).

**Scoping finding (engine reachability).** The `φ₀`-side pieces are *exactly* Bailey-transform inputs —
`phi0 = tsumQsq negOddFac` and `phi0neg = tsumQsq (fun n => (−1)ⁿ (q;q²)_n)` hold *by `rfl`* (both are
`Σ q^{n²}·βₙ`, the shape `bailey_transform` consumes). `F0` carries the base-`q²` weight `q^{2n²}` (the `E2`
image), and `χ0` carries a **linear** weight `q^n` — a different structure and the genuine crux for R1.
No `sorry`.
-/
import RamanujanTau.MockTheta5DistinctSplit
import RamanujanTau.MockTheta5BaileyTransform

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- generic stabilized mock-theta sum `Σ_{n≥0} q^{e n}·(t n)`; well-defined whenever `n ≤ e n`
(so the `n`-th term has `q`-order `≥ n`, and only finitely many touch each coefficient). -/
noncomputable def mtSum (e : ℕ → ℕ) (t : ℕ → PowerSeries ℤ) : PowerSeries ℤ :=
  mk fun m => coeff m (∑ n ∈ Finset.range (m + 1), X ^ (e n) * t n)

lemma coeff_mtSum (e : ℕ → ℕ) (t : ℕ → PowerSeries ℤ) (he : ∀ n, n ≤ e n) {m M : ℕ}
    (hM : m + 1 ≤ M) : coeff m (mtSum e t) = ∑ n ∈ Finset.range M, coeff m (X ^ (e n) * t n) := by
  rw [mtSum, coeff_mk, map_sum]
  refine Finset.sum_subset (fun x hx => Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hx) hM)) (fun n _ hn => ?_)
  simp only [Finset.mem_range, not_lt] at hn
  rw [PowerSeries.coeff_X_pow_mul', if_neg (by have := he n; omega)]

/-- `(q^{n+1};q)_n = ∏_{k<n}(1 − q^{n+1+k})` — the Pochhammer appearing in `χ₀`. -/
noncomputable def chiPoch (n : ℕ) : PowerSeries ℤ := ∏ k ∈ Finset.range n, (1 - X ^ (n + 1 + k))

/-- `F₀(q) = Σ_{n≥0} q^{2n²}/(q;q²)_n` (fifth-order mock theta). -/
noncomputable def F0 : PowerSeries ℤ := mtSum (fun n => 2 * n ^ 2) (fun n => Ring.inverse (oddFac n))

/-- `φ₀(q) = Σ_{n≥0} q^{n²}(−q;q²)_n` (fifth-order mock theta). -/
noncomputable def phi0 : PowerSeries ℤ := mtSum (fun n => n ^ 2) (fun n => negOddFac n)

/-- `φ₀(−q) = Σ_{n≥0} (−1)ⁿ q^{n²}(q;q²)_n`. -/
noncomputable def phi0neg : PowerSeries ℤ := mtSum (fun n => n ^ 2) (fun n => (-1) ^ n * oddFac n)

/-- `χ₀(q) = Σ_{n≥0} q^n/(q^{n+1};q)_n` (fifth-order mock theta). -/
noncomputable def chi0 : PowerSeries ℤ := mtSum (fun n => n) (fun n => Ring.inverse (chiPoch n))

/-- **`φ₀` is a Bailey-transform input**: `φ₀ = Σ q^{n²}·(−q;q²)_n = tsumQsq negOddFac`. -/
lemma phi0_eq_tsumQsq : phi0 = tsumQsq negOddFac := rfl

/-- **`φ₀(−q)` is a Bailey-transform input**: `= tsumQsq (fun n => (−1)ⁿ (q;q²)_n)`. -/
lemma phi0neg_eq_tsumQsq : phi0neg = tsumQsq (fun n => (-1) ^ n * oddFac n) := rfl

end MockTheta5.JTP
