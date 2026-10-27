# Rademacher's exact formula for p(n): plan

Target (Rademacher 1937):

  p(n) = (1/(π√2)) Σ_{k≥1} A_k(n) √k · d/dn [ sinh((π/k)√((2/3)(n − 1/24))) / √(n − 1/24) ],
  A_k(n) = Σ_{0≤h<k, (h,k)=1} ω_{h,k} e^{−2πinh/k},  ω_{h,k} = e^{πi s(h,k)}.

Route: Apostol, *Modular Functions and Dirichlet Series*, Ch. 5 (Ford circles). Built on `HardyRamanujan/`.

1. **η for all of SL₂(ℤ)** (`Rademacher/EtaGeneral`): η(γτ) = ε_γ √(cτ+d) η(τ) with ε_γ²⁴ = 1. The proof uses
   logarithmic derivatives and Mathlib's `E2_slash_action`, as Mathlib does for `S`. Then the `F` form at
   τ = (h+iz)/k: F(e^{2πi(h+iz)/k}) = ω_{h,k} √z e^{π(1/z−z)/(12k)} F(e^{2πi(h'+i/z)/k}).
2. **Dedekind sums**: ω_{h,k} = e^{πi s(h,k)} (reciprocity + the S/T composition). It is needed only for the
   classical form of A_k(n). Before it, A_k(n) is stated with the abstract multiplier.
3. **Farey / Ford circles**: the path from i to i+1 along Ford-circle arcs of order N; chord/arc bounds.
4. **The Bessel integral**: (1/2πi)∫_{c−i∞}^{c+i∞} w^{−5/2} e^{w + a/w} dw = Σ_m a^m/(m! Γ(m+5/2)), by the
   Laplace transform of x^{m+3/2} and Fourier inversion, in closed form via sinh/cosh.
5. **Assembly**: p(n) = Σ_{k≤N} (main terms) + O(N^{−1/2}); let N → ∞.

## Status (2026-10-27): DONE except the Dedekind-sum identification

`Rademacher.rademacher` is proved and axiom-clean, with `A_k(n)` built from the canonical η-multiplier `ω_{h,k}`.
Steps 1, 3, 4 and 5 are done; for step 4 the inversion went via the Laplace transform plus Fourier inversion.
The route differs from Apostol in two ways:
* an explicit primitive replaces path deformation;
* the paths are vertical segments in `w = 1/z`.

Remaining step 2 is `ω_{h,k} = e^{πi s(h,k)}` (Dedekind sums). It has been checked numerically: with this `ω`, the partial sums give `p(1), p(5), p(10), p(20)` to `≤ 10⁻³` at `k < 40`.
