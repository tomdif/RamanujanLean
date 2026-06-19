/-
# Jacobi triple product campaign, toward L7: the finite Durfee rectangle (free from F_eq_one)

The bilateralization (JTP step L7) reduces to the **Durfee rectangle identity** (`Q = q²`):
`Σ_{j≥0} Q^{j(j+n)} / ((Q;Q)_{j+n}(Q;Q)_j) = 1/(Q;Q)_∞` for all `n ≥ 0`. A route scout flagged the general-`n`
case as needing a "genuinely new finite identity proven by induction on m". Cross-checking against what we
have shows that is **not** needed: cleared of denominators, that finite identity is
`Σ_{j≤m} q^{j(j+n)}·[m,j]_q·(q^{n+j+1};q)_{m-j} = 1`, which is exactly `F_eq_one m n` — already proved (the
general-`b` statement behind `bailey_inner` / the q-Chu–Vandermonde core). So the finite rectangle in inverse
form comes free, exactly as `inner_inv` did for `b = 2r`.

  **`inner_inv_gen`:** `Σ_{j≤m} q^{j²+nj}·(q;q)_j⁻¹·(q;q)_{m-j}⁻¹·(q;q)_{n+j}⁻¹ = (q;q)_m⁻¹·(q;q)_{n+m}⁻¹`.

This is the finite Durfee rectangle (inverse form). The remaining steps to the full Durfee rectangle identity:
take `m → ∞` (coefficient stabilization — `(q;q)_{m-j}, (q;q)_m, (q;q)_{n+m} → (q;q)_∞`, needs an inverse-
stabilization lemma), cancel one unit `(q;q)_∞`, and apply the base change `E2` (`q ↦ q²`). No `sorry`.
-/
import RamanujanTau.MockTheta5BaileyChain

namespace MockTheta5.Bailey
open PowerSeries

/-- **The finite Durfee rectangle (inverse form)**, for all `n, m`:
`Σ_{j≤m} q^{j²+nj}·(q;q)_j⁻¹·(q;q)_{m-j}⁻¹·(q;q)_{n+j}⁻¹ = (q;q)_m⁻¹·(q;q)_{n+m}⁻¹`.
Obtained free from `F_eq_one m n` (the general-`b` q-Chu–Vandermonde), generalizing `inner_inv` from `2r` to
arbitrary `n` — no new induction. -/
lemma inner_inv_gen (m n : ℕ) :
    (∑ j ∈ Finset.range (m + 1),
        X ^ (j ^ 2 + n * j) * Ring.inverse (qfac j) * Ring.inverse (qfac (m - j))
          * Ring.inverse (qfac (n + j)))
      = Ring.inverse (qfac m) * Ring.inverse (qfac (n + m)) := by
  have hb := F_eq_one m n
  rw [F] at hb
  have hrw : (∑ j ∈ Finset.range (m + 1), X ^ (j ^ 2 + n * j) * gaussBinom m j * rfac (n + j) (m - j))
      = (qfac m * qfac (n + m)) * (∑ j ∈ Finset.range (m + 1),
          X ^ (j ^ 2 + n * j) * Ring.inverse (qfac j) * Ring.inverse (qfac (m - j))
            * Ring.inverse (qfac (n + j))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [gaussBinom_eq_inv m j (by omega), rfac_eq_inv, show n + j + (m - j) = n + m from by omega]
    ring
  rw [hrw] at hb
  have heq : (qfac m * qfac (n + m)) * (Ring.inverse (qfac m) * Ring.inverse (qfac (n + m))) = 1 := by
    rw [show (qfac m * qfac (n + m)) * (Ring.inverse (qfac m) * Ring.inverse (qfac (n + m)))
          = (qfac m * Ring.inverse (qfac m)) * (qfac (n + m) * Ring.inverse (qfac (n + m))) from by ring,
        Ring.mul_inverse_cancel (qfac m) (isUnit_qfac m),
        Ring.mul_inverse_cancel (qfac (n + m)) (isUnit_qfac (n + m)), mul_one]
  exact mul_left_cancel₀ (((isUnit_qfac m).mul (isUnit_qfac (n + m))).ne_zero) (hb.trans heq.symm)

end MockTheta5.Bailey
