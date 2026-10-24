/-
# Andrews' Bailey pair for the fifth-order mock theta function `f₀`

Rung L1 of the Mock Theta Conjectures campaign (`MTC_GAP_MAP.md`). Relative to `a = 1`,

  `βₙ = 1/(−q;q)ₙ`,   `α₀ = 1`,   `αₙ = q^{(3n²+n)/2} Sₙ − q^{(3n²−n)/2} S_{n−1}`,   `Sₙ = Σ_{|j|≤n} (−1)ʲ q^{−j²}`

is a Bailey pair (`isBaileyPair_f0`; Andrews, Trans. AMS 293 (1986)). Here `q^{m²}Sₘ` is the polynomial
`V m = Σ_{|j|≤m} (−1)ʲ q^{m²−j²}`, defined by `V (m+1) = q^{2m+1} V m + 2(−1)^{m+1}`, so
`αₙ = q^{T(n)} V n − q^{T(n)+n−1} V (n−1)` with `T(n) = n(n+1)/2`.

The partial theta sum makes `αₙ` non-hypergeometric. The proof is still a first-order creative telescoping,
with a certificate linear in `V`:

  `G(n,s) = qⁿ/((q;q)_{n−s−1}(q;q)_{n+s}) · ((1−qⁿ) q^{T(s)+s} V s − 2(−1)^{s+1} q^{T(s)})`,

  `(1−qⁿ)((1+qⁿ)F(n,r) − F(n−1,r)) = G(n,r) − G(n,r−1)` for `1 ≤ r < n`,

with boundary rows `r = 0` (`= G(n,0)`) and `r = n` (`= −G(n,n−1)`). Telescoping gives
`(1+qⁿ)S(n) = S(n−1)` after cancelling `1 − qⁿ` in the domain `ℤ⟦q⟧`. The certificate was found by a sympy
ansatz (`scripts/mtc_gap/`). No `sorry`.
-/
import RamanujanTau.MockTheta5BaileyQPairA
import RamanujanTau.MockTheta5BaileyTransform

set_option autoImplicit false

namespace MockTheta5.Bailey
open PowerSeries

/-- `T(m) = m(m+1)/2`, recursively (no ℕ-division). -/
def triF : ℕ → ℕ
  | 0 => 0
  | m + 1 => triF m + m + 1

/-- `V m = Σ_{|j|≤m} (−1)ʲ q^{m²−j²}`, via `V (m+1) = q^{2m+1} V m + 2(−1)^{m+1}`. -/
noncomputable def Vth : ℕ → PowerSeries ℤ
  | 0 => 1
  | m + 1 => X ^ (2 * m + 1) * Vth m + 2 * (-1) ^ (m + 1)

/-- Andrews' `α` for `f₀`. -/
noncomputable def alphaF0 : ℕ → PowerSeries ℤ
  | 0 => 1
  | s + 1 => X ^ triF (s + 1) * Vth (s + 1) - X ^ (triF (s + 1) + s) * Vth s

/-- `(−q;q)ₙ = ∏_{k<n} (1 + q^{k+1})`. -/
noncomputable def mqfac (n : ℕ) : PowerSeries ℤ := ∏ k ∈ Finset.range n, (1 + X ^ (k + 1))

lemma mqfac_succ (n : ℕ) : mqfac (n + 1) = mqfac n * (1 + X ^ (n + 1)) := by
  rw [mqfac, Finset.prod_range_succ, ← mqfac]

lemma isUnit_mqfac (n : ℕ) : IsUnit (mqfac n) := by
  rw [isUnit_iff_constantCoeff, mqfac, map_prod,
      Finset.prod_eq_one (fun x _ => by
        rw [map_add, map_one, map_pow, constantCoeff_X, zero_pow (by omega), add_zero])]
  exact isUnit_one

/-- the Bailey summand `αᵣ/((q;q)_{n−r}(q;q)_{n+r})`. -/
noncomputable def F0term (n r : ℕ) : PowerSeries ℤ :=
  alphaF0 r * Ring.inverse (qfac (n - r)) * Ring.inverse (qfac (n + r))

/-- the certificate `G(n,s)`. -/
noncomputable def G0term (n s : ℕ) : PowerSeries ℤ :=
  X ^ n * Ring.inverse (qfac (n - s - 1)) * Ring.inverse (qfac (n + s))
    * ((1 - X ^ n) * X ^ (triF s + s) * Vth s - 2 * (-1) ^ (s + 1) * X ^ triF s)

/-- row `r = 0`. -/
lemma lem0 (d : ℕ) :
    (1 - X ^ (d + 1)) * ((1 + X ^ (d + 1)) * F0term (d + 1) 0 - F0term d 0) = G0term (d + 1) 0 := by
  simp only [F0term, G0term, alphaF0, Vth, triF, Nat.sub_zero, Nat.add_zero, Nat.add_sub_cancel]
  rw [inv_qfac_succ d]
  ring

/-- interior rows `r = s+1`, `n = s+2+d`. -/
lemma lemA0 (s d : ℕ) :
    (1 - X ^ (s + 2 + d)) * ((1 + X ^ (s + 2 + d)) * F0term (s + 2 + d) (s + 1) - F0term (s + 1 + d) (s + 1))
      = G0term (s + 2 + d) (s + 1) - G0term (s + 2 + d) s := by
  simp only [F0term, G0term, alphaF0, Vth, triF]
  simp only [show s + 2 + d - (s + 1) = d + 1 from by omega, show s + 2 + d + (s + 1) = 2 * s + 3 + d from by omega,
      show s + 1 + d - (s + 1) = d from by omega, show s + 1 + d + (s + 1) = 2 * s + 2 + d from by omega,
      show d + 1 - 1 = d from by omega, show s + 2 + d - s - 1 = d + 1 from by omega,
      show s + 2 + d + s = 2 * s + 2 + d from by omega]
  rw [inv_qfac_succ d, inv_qfac_succ (2 * s + 2 + d),
      show 2 * s + 2 + d + 1 = 2 * s + 3 + d from by omega]
  simp only [two_mul, pow_add, pow_succ]
  ring

/-- top row `r = n = s+1`. -/
lemma lemB0 (s : ℕ) :
    (1 - X ^ (s + 1)) * ((1 + X ^ (s + 1)) * F0term (s + 1) (s + 1)) = - G0term (s + 1) s := by
  simp only [F0term, G0term, alphaF0, Vth, triF]
  simp only [show s + 1 - (s + 1) = 0 from by omega, show s + 1 + (s + 1) = 2 * s + 1 + 1 from by omega,
      show s + 1 - s - 1 = 0 from by omega, show s + 1 + s = 2 * s + 1 from by omega]
  rw [inv_qfac_succ (2 * s + 1)]
  simp only [two_mul, pow_add, pow_succ, qfac_zero, Ring.inverse_one]
  ring

/-- `S(n) = Σ_{r≤n} αᵣ/((q;q)_{n−r}(q;q)_{n+r})`. -/
noncomputable def S0sum (n : ℕ) : PowerSeries ℤ := ∑ r ∈ Finset.range (n + 1), F0term n r

/-- the telescoped recurrence, before cancelling `1 − q^{m+1}`. -/
lemma S0sum_rec_mul (m : ℕ) :
    (1 - X ^ (m + 1)) * ((1 + X ^ (m + 1)) * S0sum (m + 1) - S0sum m) = 0 := by
  have hrow : ∀ r ∈ Finset.range (m + 1),
      (1 - X ^ (m + 1)) * ((1 + X ^ (m + 1)) * F0term (m + 1) r - F0term m r)
        = (if r = 0 then G0term (m + 1) 0 else G0term (m + 1) r - G0term (m + 1) (r - 1)) := by
    intro r hr
    rw [Finset.mem_range] at hr
    rcases r with _ | s
    · simpa using lem0 m
    · have h := lemA0 s (m - s - 1)
      rw [show s + 2 + (m - s - 1) = m + 1 from by omega,
          show s + 1 + (m - s - 1) = m from by omega] at h
      simpa using h
  have hsplit : (1 - X ^ (m + 1)) * ((1 + X ^ (m + 1)) * S0sum (m + 1) - S0sum m)
      = ∑ r ∈ Finset.range (m + 1),
          (1 - X ^ (m + 1)) * ((1 + X ^ (m + 1)) * F0term (m + 1) r - F0term m r)
        + (1 - X ^ (m + 1)) * ((1 + X ^ (m + 1)) * F0term (m + 1) (m + 1)) := by
    rw [S0sum, S0sum, Finset.sum_range_succ _ (m + 1)]
    simp only [mul_add, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  rw [hsplit, Finset.sum_congr rfl hrow, lemB0 m]
  -- the row values telescope: G(0) + Σ_{1≤r≤m} (G(r) − G(r−1)) = G(m)
  have htel : ∀ k, k ≤ m → ∑ r ∈ Finset.range (k + 1),
      (if r = 0 then G0term (m + 1) 0 else G0term (m + 1) r - G0term (m + 1) (r - 1)) = G0term (m + 1) k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih (by omega), if_neg (by omega), Nat.add_sub_cancel]; ring
  rw [htel m le_rfl]; ring

lemma one_sub_X_pow_ne_zero (m : ℕ) : (1 - X ^ (m + 1) : PowerSeries ℤ) ≠ 0 := by
  intro h
  have := congrArg (coeff (m + 1)) h
  rw [map_sub, coeff_one, coeff_X_pow, if_pos rfl, if_neg (by omega), map_zero] at this
  norm_num at this

/-- `(1 + q^{m+1}) S(m+1) = S(m)`. -/
lemma S0sum_rec (m : ℕ) : (1 + X ^ (m + 1)) * S0sum (m + 1) = S0sum m := by
  have h := S0sum_rec_mul m
  rcases mul_eq_zero.mp h with h0 | h1
  · exact absurd h0 (one_sub_X_pow_ne_zero m)
  · exact sub_eq_zero.mp h1

/-- `S(n) = 1/(−q;q)ₙ`. -/
lemma S0sum_eq (n : ℕ) : S0sum n = Ring.inverse (mqfac n) := by
  induction n with
  | zero => simp [S0sum, F0term, alphaF0, mqfac]
  | succ m ih =>
      have hrec := S0sum_rec m
      rw [ih] at hrec
      have hunit : mqfac (m + 1) * S0sum (m + 1) = 1 := by
        rw [mqfac_succ, mul_assoc, hrec, Ring.mul_inverse_cancel _ (isUnit_mqfac m)]
      calc S0sum (m + 1)
          = Ring.inverse (mqfac (m + 1)) * (mqfac (m + 1) * S0sum (m + 1)) := by
            rw [← mul_assoc, Ring.inverse_mul_cancel _ (isUnit_mqfac (m + 1)), one_mul]
        _ = Ring.inverse (mqfac (m + 1)) := by rw [hunit, mul_one]

/-- **Andrews' Bailey pair for `f₀`** (relative to `a = 1`): `(alphaF0, 1/(−q;q)ₙ)`. -/
theorem isBaileyPair_f0 : IsBaileyPair alphaF0 (fun n => Ring.inverse (mqfac n)) := by
  intro n
  show Ring.inverse (mqfac n) = _
  rw [← S0sum_eq n, S0sum]
  rfl

end MockTheta5.Bailey

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- Ramanujan's fifth-order mock theta function `f₀(q) = Σ_{n≥0} q^{n²}/(−q;q)ₙ`. -/
noncomputable def f0 : PowerSeries ℤ := tsumQsq fun n => Ring.inverse (mqfac n)

/-- **Andrews' Hecke-side identity for `f₀`** (via `isBaileyPair_f0` and `bailey_transform`):
`(q;q)_∞ · f₀(q) = Σ_{n≥0} q^{n²} αₙ`, i.e. HM (0.3)
`(q)_∞ f₀ = Σ_{n≥0} Σ_{|j|≤n} (−1)ʲ q^{n(5n+1)/2 − j²}(1 − q^{4n+2})` before regrouping. -/
theorem qfacInf_mul_f0 : qfacInf * f0 = tsumQsq alphaF0 := by
  rw [f0, bailey_transform isBaileyPair_f0, partitionGF, ← mul_assoc,
      Ring.mul_inverse_cancel _ isUnit_qfacInf, one_mul]

end MockTheta5.JTP

namespace MockTheta5.Bailey
open PowerSeries

/-- `V n = q^{n²} + 2 Σ_{1≤j≤n} (−1)ʲ q^{n²−j²}`, i.e. `Σ_{|j|≤n} (−1)ʲ q^{n²−j²}`. -/
lemma Vth_eq_sum (n : ℕ) :
    Vth n = X ^ (n ^ 2) + 2 * ∑ j ∈ Finset.range n, (-1) ^ (j + 1) * X ^ (n ^ 2 - (j + 1) ^ 2) := by
  induction n with
  | zero => simp [Vth]
  | succ n ih =>
      have hsum : ∑ j ∈ Finset.range n, X ^ (2 * n + 1) * ((-1) ^ (j + 1) * X ^ (n ^ 2 - (j + 1) ^ 2))
          = ∑ j ∈ Finset.range n, ((-1) ^ (j + 1) * X ^ ((n + 1) ^ 2 - (j + 1) ^ 2) : PowerSeries ℤ) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        have h1 : (j + 1) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (by omega) 2
        rw [show (n + 1) ^ 2 - (j + 1) ^ 2 = (2 * n + 1) + (n ^ 2 - (j + 1) ^ 2) from by
          zify [h1, show (j + 1) ^ 2 ≤ (n + 1) ^ 2 from Nat.pow_le_pow_left (by omega) 2]; ring, pow_add]
        ring
      rw [Vth, ih, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, ← hsum, ← Finset.mul_sum,
        show (n + 1) ^ 2 = (2 * n + 1) + n ^ 2 from by ring, pow_add]
      ring

/-- Andrews' `n`-th Hecke term `Σ_{|j|≤n} (−1)ʲ (q^{n(5n+1)/2−j²} − q^{n(5n+9)/2+2−j²})`
`= q^{n²+T(n)} V n (1 − q^{4n+2})`. -/
noncomputable def heckeF0 (n : ℕ) : PowerSeries ℤ := X ^ (n ^ 2 + triF n) * Vth n * (1 - X ^ (4 * n + 2))

/-- the "second half" `B_m = q^{m²+T(m)+4m+2} V m`. -/
noncomputable def BF0 (m : ℕ) : PowerSeries ℤ := X ^ (m ^ 2 + triF m + 4 * m + 2) * Vth m

lemma triF_succ (m : ℕ) : triF (m + 1) = triF m + m + 1 := rfl

/-- `q^{n²}αₙ = Aₙ − B_{n−1}` with `heckeF0 n = Aₙ − Bₙ`. -/
lemma sq_alpha_telescope (K : ℕ) :
    ∑ n ∈ Finset.range (K + 1), X ^ (n ^ 2) * alphaF0 n
      = ∑ n ∈ Finset.range (K + 1), heckeF0 n + BF0 K := by
  induction K with
  | zero => simp [alphaF0, heckeF0, BF0, Vth, triF]
  | succ K ih =>
      have key : X ^ ((K + 1) ^ 2) * alphaF0 (K + 1) + BF0 K = heckeF0 (K + 1) + BF0 (K + 1) := by
        simp only [alphaF0, heckeF0, BF0, triF_succ]
        rw [show (K + 1) ^ 2 = K ^ 2 + 2 * K + 1 from by ring]
        simp only [pow_add, pow_succ, mul_add, mul_one]
        ring
      rw [Finset.sum_range_succ _ (K + 1), ih, Finset.sum_range_succ heckeF0 (K + 1)]
      linear_combination key

end MockTheta5.Bailey

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- Andrews' Hecke-type double sum `Σ_{n≥0} Σ_{|j|≤n} (−1)ʲ q^{n(5n+1)/2−j²}(1−q^{4n+2})`. -/
noncomputable def heckeSumF0 : PowerSeries ℤ :=
  mk fun k => coeff k (∑ n ∈ Finset.range (k + 1), heckeF0 n)

/-- **Andrews' Hecke-type identity for `f₀`** (Trans. AMS 1986; HM (0.3)):
`(q;q)_∞ f₀(q) = Σ_{n≥0} Σ_{|j|≤n} (−1)ʲ q^{n(5n+1)/2−j²}(1 − q^{4n+2})`. -/
theorem qfacInf_mul_f0_hecke : qfacInf * f0 = heckeSumF0 := by
  rw [qfacInf_mul_f0]
  ext k
  rw [tsumQsq, heckeSumF0, coeff_mk, coeff_mk, sq_alpha_telescope k, map_add, BF0,
    PowerSeries.coeff_X_pow_mul', if_neg (by nlinarith), add_zero]

end MockTheta5.JTP
