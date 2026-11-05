/-
# `Subconvexity`: GL(2) inputs toward a t-aspect subconvexity bound for `L(Δ, s)`

Subconvexity `|L(Δ,6+it)| ≪ |t|^{1/2−δ}` itself is **not** proved here; see
`docs/SUBCONVEXITY.md` for the feasibility analysis and the remaining map.  This directory proves,
unconditionally, the inputs that Jutila's route (and the simple-δ-method routes) take from the
modularity of `Δ`:

* `wilton_bound` (Wilton 1929): `‖∑_{n≤M} τ(n) e(nα)‖ ≤ C M⁶ log(1+2M)` uniformly in `α ∈ ℝ`.
* `twF_inv`: for `a ā − b q = 1`, `Δ(−ā/q + i/(qt)) = t¹² Δ(a/q + it/q)`.
* `twLambda_entire`, **`twLambda_functional_equation`**: the completed additive twists
  `Λ(x,s) = ∫₀^∞ Δ(x+it/q) t^{s−1} dt` are entire and `Λ(−ā/q, 12−s) = Λ(a/q, s)`.
* `twLambda_eq`: `Λ(x,s) = (2π/q)^{−s} Γ(s) ∑ τ(n) e(nx) n^{−s}` for `Re s > 7`.
* `smooth_twist_decay`: `‖∑ τ(n) e(an/q) e^{−2πny}‖ ≤ A (qy)^{−12} e^{−2π/(q²y)}` once
  `1/(q²y) ≥ Y`, i.e. smooth sums of length `X` twisted by `e(an/q)` with `q ≤ X^{1/2−ε}` are
  `O(X^{−∞})` (normalized), uniformly in `a`.
* `hasSum_shifted_parseval`: `∫₀¹ Δ conj(Δ) 𝕢^{−h} dx = ∑ τ(n)τ(n+h) e^{−4πny}` — the `h`-th
  horocycle Fourier coefficient of `y¹²|Δ|²` is a shifted convolution sum (route (b)).
-/
import RamanujanTau.Subconvexity.Wilton
import RamanujanTau.Subconvexity.TwistedFE
import RamanujanTau.Subconvexity.Shifted

#print axioms RamanujanTau.Subconvexity.tau_twist_integral
#print axioms RamanujanTau.Subconvexity.wilton_bound
#print axioms RamanujanTau.Subconvexity.twF_inv
#print axioms RamanujanTau.Subconvexity.twLambda_entire
#print axioms RamanujanTau.Subconvexity.twLambda_functional_equation
#print axioms RamanujanTau.Subconvexity.twLambda_eq
#print axioms RamanujanTau.Subconvexity.smooth_twist_decay
#print axioms RamanujanTau.Subconvexity.hasSum_shifted_parseval
