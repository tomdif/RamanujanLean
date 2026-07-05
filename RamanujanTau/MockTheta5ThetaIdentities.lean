/-
# Relations among Ramanujan's theta functions

The classical identity linking `φ(q) = Σ q^{n²}` and `φ(−q)`, proved from the product forms and the
even/odd (base-`q²`) dilation algebra:

  * **`phi_mul_phiNeg`:**  `φ(q) · φ(−q) = φ(−q²)²`   (`φ(−q²) = E2 φ(−q)`).

Here `(q²;q²)_∞ = qfac2Inf`, `(−q;q²)_∞ = negOddPochInf`, `(q;q²)_∞ = oddPochInf`. No `sorry`.
-/
import RamanujanTau.MockTheta5PsiSeries

namespace MockTheta5.JTP
open PowerSeries MockTheta5.Bailey

/-- `(q²;q²)_∞ = (q⁴;q⁴)_∞ · (q²;q⁴)_∞` (even/odd split at level `q²`). -/
lemma qfac2Inf_split : qfac2Inf = E2 qfac2Inf * E2 oddPochInf := by
  rw [← map_mul, qfac2Inf_mul_oddPochInf]; rfl

/-- **`φ(q) · φ(−q) = φ(−q²)²`.** (`φ(−q²) = E2 φ(−q)`.) -/
theorem phi_mul_phiNeg : phi * phiNeg = E2 phiNeg ^ 2 := by
  rw [phi_product, phiNeg_product, map_mul, map_pow,
      show (qfac2Inf * negOddPochInf ^ 2) * (qfac2Inf * oddPochInf ^ 2)
        = qfac2Inf ^ 2 * (negOddPochInf * oddPochInf) ^ 2 from by ring,
      negOddPochInf_mul_oddPochInf]
  nth_rewrite 1 [qfac2Inf_split]
  ring

end MockTheta5.JTP
