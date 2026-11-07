# Proof map: modularity of the Shimura lifts

Created 2026-10-30. [Theorem A boundary](THEOREM_A.md)

**Status: complete.** `ThetaLift.aadRaisedModularity` proves
`AADRaisedModularity` for every prime ℓ ≥ 5, and `ThetaLift.theoremA_unconditional` follows for ℓ ≥ 13.
The route follows Ahlgren–Andersen–Dicks, [arXiv:2307.07438](https://arxiv.org/abs/2307.07438), §§4–5, with
the changes marked below. The proof is machine-checked and has not been reviewed by a human expert.

Notation: F(z) = G(tz)/η(tz)^j, with G a level-one cusp form of weight k′ and t squarefree,
t ≡ −j (mod 24). N = t, ψ = (·/t), λ = (ℓ−3)/2. F has coefficients a(n) at q^{tn/24}, in integers.

## Proved

| Step | Result | Source |
|---|---|---|
| Reduction | Theorem A from `AADModularity` | `theoremA_of_modularity` |
| Level lowering | a form on Γ₀(Mt) in powers of q^t comes from Γ₀(M) | `LevelLowering.exists_lowered` |
| Raised form | `AADRaisedModularity` implies `AADModularity` | `aadModularity_of_raised` |
| L8 core | ∫₀^∞ x^(µ−2) H_µ(x) exp(−x²/2 − c²/(2x²)) dx = √(π/2) c^(µ−1) e^(−c), for every µ and c > 0 | `HermiteIntegral.hermite_integral` |
| Petersson's formula | η(γz) = (d/c) e(((a+d)c − bd(c²−1) − 3c)/24) √(cz+d) η(z), for c > 0 odd | `EtaMultiplier.etaLaw_odd` |
| L8 collapse | The Hermite sum in the Fourier expansion is (1+ε)^λ times one exponential, for ε = ±1, so opposite-sign terms vanish | `HermiteIntegral.kernel_sum` |
| L1, L2 | Θ(τ,ζ) = Σ χ₁₂(x) e(x²τ/24 + xζ): translation, inversion, and Θ(γτ, ζ/j)/η(γτ) = e(6cζ²/j) Θ(τ,ζ)/η(τ) on all of SL₂(ℤ) | `ChiTheta.chiTheta_inversion`, `ChiTheta.thetaLaw` |
| L5 core | With the generating exponential, Σ_b Σ_c χ₁₂(Nb) T(a,b,c) = χ₁₂(N) √(π/κ) √z e(−1/8) Σ_m T̂(a,m) at fixed a, and each T̂(a,m) is the translate 𝔾_g(γz; σ/j) η(z)/η(γz) | `KernelPoisson.poisson_c`, `exponent_identity`, `KernelTerms.lattice_a`, `KData.pTerm_eq` |
| L4 | The kernel y^(−2λ) Σ kTerm has weight 2λ in w on Γ₀(6N), via the bijection of ℤ³ preserving ψ(a), χ₁₂(Nb), and the discriminant | `KernelCovariance.kernel_covariant` |
| L5 summability | The lattice terms and their Poisson duals are dominated uniformly in σ by one family on ℤ³ | `KernelSummable.summable_latTerm`, `KernelUniform.norm_latTerm_le`, `norm_dualF_le` |
| L1′ | The σⁿ coefficient of the seed is the Hermite theta series; the σⁿ coefficient of the lattice sum is the kernel with Qⁿ; each (a,m) term is a translate at γz. The identity holds on all of ℤ³, including (a,m) = (0,0) | `SeedTaylor.seed_iteratedDeriv`, `KernelGen.kernel_expand`, `KData.dF_taylor` |
| L6, L7 measure core | The coset translates of 𝒟 are a fundamental domain for the image of Γ₀(N) in Perm ℍ, the strip is exact for the translations, and ∫_strip f = ∫_F Σ_{A\H} f(ρz) | `ModularDomain.isFundamentalDomain_domainOf`, `exactDomain_strip`, `Unfolding.unfold_integral` |
| L3 | Z = η(tz)^j η(z) satisfies Z(γz) = (d/t)(cz+d)^w Z(z) for all γ with t ∣ c, when t is prime to six, t + j ≡ 0 (mod 24), j + 1 = 2w | `EtaProduct.zLaw` |

## The final layers

| Step | Result | Source |
|---|---|---|
| Hecke bound | G²⁴/Δ^j is a level-one cusp form, so \|G/η^j\| ≪ v^(−k/2), and the coefficients of G·E^(−j) grow polynomially | `HeckeHalf.hecke_half`, `HalfExpansion.qExp_hP`, `norm_cA_le` |
| Fourier in u | Integrating conj 𝔽 against e(x²u/24) selects the coefficient with x² = N(24m−j) | `FourierU.fourier_u` |
| Integral in v | The Hermite integral vanishes when xg < 0, and is an exact exponential when xg > 0 | `VIntegral.vTerm_integral`, `StripClosed.W_pos`, `W_neg` |
| Strip | Integrability, the sum over g, and the closed form of the integral over the strip | `StripG.strip_total`, `StripValue.strip_value`, `StripClosed.strip_closed` |
| Automorphy | v^(λ+½) conj 𝔽 transforms by (η(z)/η(γz)) j^(−λ) (d/N), which cancels the character | `Automorphy.autom` |
| Cosets | (r, g) ↦ (−gd, gc/N) is a bijection onto lattice points with a prime to N | `CosetBridge.bMap_inj`, `bMap_surj` |
| Folding | The kernel integrand equals y^(1−λ) χ₁₂(N) e(−1/8) Σ_r fTot(ρz), and y cancels after unfolding | `KernelFold.phiI_eq`, `phi_value`, `lamSum_covariant` |
| q-series | The double sum is Σ b(n) e(Nnw), with b(n) the lift coefficients | `LamSeries.lamSum_eq` |
| Modular form | A polynomially bounded series with covariance is a modular form; moderate growth and the removable singularity theorem give boundedness at every cusp | `AbstractForm.bdd_of_moderate`, `slash_bdd`, `exists_form` |
| t ≠ 1 | The lift is modular | `LiftForm.raised_of_ne_one` |
| t = 1 | See below | `KernelOne.alpha_cross`, `KernelCR.alpha_not_diff`, `defect_one`, `Final.raised_of_one` |

## Changes from the published proof

**No Laplacian or Mellin step (L8 replaces AAD Lemma 5.3 and §5.1's Mellin argument).** At general
w the Poincaré terms need all µ, not only even µ. The odd terms vanish at ξ = 0, which is why AAD can
omit them on the imaginary axis. Numerically
([kernel_test.py](../scripts/frontier/pattern/kernel_test.py)), lattice and Poincaré sides then have
constant ratio in ξ: about −5.000 for λ = 2, N = 5 and about −18.5 for λ = 3, N = 7, consistent with
(−N)^(λ/2). `kernel_sum` shows that the integrated terms with xg > 0 give (1+1)^λ and those with xg < 0
give (1−1)^λ = 0, so the expansion should be holomorphic directly. The formal proof is `vTerm_integral`.

**Closed form of the kernel.** With Q = 6Naw̄² + Nbw̄ + c, κ = πṽ/(6Ny²), z̃ = −1/(Nz), Z = conj z̃,

  ϑ_λ(z,w) = N^(−λ/2−1/4) (−iz)^(−λ−1/2) ṽ^(1/2) y^(−2λ)
    Σ ψ(a) χ₁₂(Nb) Q^λ exp(−κ|Q|²) e((Nb²/24 − ac) Z).

**Generating parameter.** Replace Q^λ by exp(sQ) with s = iσ/(Nzy). Poisson summation in c is then a pure
Gaussian, the b-sum is Θ(−1/z, ·), and each pair (a,m) gives exactly

  𝔊_g(γz; σ/j) η(z),   𝔊_g(z;σ) = exp(6gyσ/v − 3σ²/(2πv) − 6πg²y²/v) Θ(z, gξ + σ/(2πi)) / η(z),

with (gc, gd) = (Nm, −a). [gen_test.py](../scripts/frontier/pattern/gen_test.py) confirms this term by term
(ratio 1 to about 11–19 digits, N = 5 and 7). The coefficient of σ^λ/λ! in 𝔾_g = 𝔊_g η is
(3/π)^(λ/2) v^(−λ/2) exp(−6πg²y²/v) Σ χ₁₂(x) He_λ(√(πv/3)x + 6gy√(π/(3v))) e(x²z/24) e(xgξ).

**t = 1.** For N = 1, ψ(0) = 1, so the pair (a,m) = (0,0) survives and is not a Poincaré term. That term
does not depend on w, so it contributes E(z) y^(1−λ) to the kernel, and E need not be known to be integrable.
Eliminating E between two points gives T(γw) − j^(2λ) T(w) = κ (y′^(1−λ) − j^(2λ) y^(1−λ)) for one constant κ.
The left side is holomorphic. Cauchy–Riemann along the two lines through w₀ = −1/6 + i, with γ = [1,0;6,1], gives
(λ−1)(36^(λ−1) + (6i)^(2λ)) = 0 if κ ≠ 0, which is false for λ ≥ 2. So κ = 0.

**No integral bound at the other cusps.** Boundedness of the lift at cusps other than ∞ uses only polynomial growth of
its coefficients, covariance, and the removable singularity theorem.

**No explicit multiplier in the kernel (L2).** The automorphy factor can be written as η(γz)/η(z),
so the Poincaré-type sum in L5 is invariant in z by construction. `zLaw` supplies the one explicit
character.

**Petersson's formula needs only odd c.** Both the eta-product factor and (·/t) are multiplicative on
Γ₀(t), and `γ [1 0; t 1]` has odd lower-left entry when that of γ is even.

## Not usable as a shortcut

- Boylan–Swati ([arXiv:2505.01018](https://arxiv.org/abs/2505.01018)) give S₁(ηg) = g(z)g(6z) − g(2z)g(3z)
  from Hecke relations. Their eigenbasis can be replaced by a kernel in V⊗V with coefficients
  Σ_{y|(s,m)} χ(y) y^{k−1} a(sm/y²), but this reaches only t = r. For t > r, F/η(tz) has poles.
  Knowing only t = r would leave eigenforms with a(r) = 0, a central-value nonvanishing problem.
- Yang's original proof needs the Eichler–Selberg and Shimura trace formulas.
