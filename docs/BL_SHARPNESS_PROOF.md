# Boylan–Webb sharpness and FKO rank attainment for ℓ ≥ 29 — research draft

> **Status (2026-10-29): proposed general-prime paper arguments, not a Lean proof of
> every claim below.** The labels [P] and [P*] describe arguments in this draft;
> they do not certify a declaration in the kernel. G4–G6 and the higher-precision
> rank claims retain their stated qualifications.
>
> **2026-11-01 rank update:** independent finite computations at 607 find an
> additional generator modulo 607²; see §5.4. The proposed precision-independent
> rank formula in the earlier §6.2 is therefore not a suitable proof target
> without resolving this discrepancy. The numerical partition comparison is
> not yet certified in Lean. Rank monotonicity and propagation of attainment
> from any precision are now proved in `BLBound/RankGrowth.lean`. The subsequent
> reconstruction bound is proved in `FiniteArithmetic/EnvelopePrecision.lean`;
> an independent exact-integer replay confirms the numerical witness.
>
> Prime 29 has a separate, kernel-verified all-power recurrence and exact
> starting threshold. That construction uses the divided error `12·23^n`;
> it does not depend on identifying the experimental Θ matrix below.
> The full build and axiom audit passed; see [verification status](STATUS.md)
> and [the finite-arithmetic proof guide](FINITE_ARITHMETIC.md).
>
> The [Theorem A formalization](THEOREM_A.md) now proves, unconditionally for every prime
> ℓ ≥ 13, the integer-weight statement in §3 (with the eigenvalues of §3.2 step 5 derived from
> the Atkin–Lehner signs) and the dictionary of §2 items 1–2 for X̄ on V. Injectivity of
> U_{ℓ²} and of X̄|_V is proved unconditionally, with a formal proof of modularity of the explicit
> lifts (Ahlgren–Andersen–Dicks, Theorem 1.1). This Lean route does not use Yang's theorem. `BLBound.bEll_le` and `BLBound.dEll_eq_zero` prove b_ℓ(m) ≤ 2m−1 and d_ℓ = 0 for every ℓ ≥ 13. That proof does not use Boylan–Webb's Theorem 1.2, or the Fitting decomposition of §4.1: with χ monic killing X̄ on V, it iterates χ(X)X, each round gaining one power of ℓ because D̄ has image in V. `BLBound.rank_Xbar_pow`, `BLBound.map_Dbar_Sbar` and `BLBound.rEll_le` prove rank X̄^k = rank D̄|_{S̄} = R and r_ℓ(m) ≤ R.

Notation follows `docs/BL_PATTERN.md` and Boylan–Webb (BW, Trans. AMS 365, 2013). D(f) = U(Φf) with
Φ = η(ℓ²z)/η(z), and X = D∘U (U first, f|X = f|U|D). L(0) = 1, L(b) = D L(b−1) for b odd and
U L(b−1) for b even. ℓ ≥ 13 is prime throughout.

Fixed integers:

| symbol | value | meaning |
|---|---|---|
| j | ℓ mod 24 ∈ {1,5,7,11,13,17,19,23} | |
| t | (ℓ − j)/24 = ⌊ℓ/24⌋ | |
| ρ | (jℓ − 1)/24 | δ = (ℓ²−1)/24 = ℓt + ρ, and ℓρ + t = jδ |
| k′ | (ℓ + j − 2)/2 = ℓ − 1 − 12t | |
| λ | (ℓ − 3)/2 | |
| d | dim S_{ℓ−1}(SL₂ℤ) | |
| R | ⌊(ℓ+12)/24⌋ | FKO bound |

Mod-ℓ spaces: S̄ = S_{ℓ−1}(𝔽_ℓ), M̄ = M_{ℓ−1}(𝔽_ℓ) = 𝔽_ℓ·1 ⊕ S̄ (since E_{ℓ−1} ≡ 1), and
**V := Δ^t·S_{k′}(𝔽_ℓ) ⊂ S̄.** Ū, D̄, X̄ are the reductions of U, D, X on q-expansions mod ℓ.

**Status legend.** [P] paper argument from standard results (cited). [P*] proposed paper argument whose
external inputs or applications still need review. Neither label means Lean-verified. [N] numerical only. [O] open.

---------------------------------------------------------------------------------------------------------

## 0. Summary

1. **Key lemma (Theorem A) [P*]: for every prime ℓ ≥ 13, X̄ restricted to V is invertible.** Under the
   dictionary of §2, X̄|_V *is* the half-integral-weight Hecke operator T_{ℓ²} mod ℓ on
   S_{λ+1/2}(SL₂ℤ, ν_η^{−ℓ}). Consequences:
   * rank D̄|_{S̄} = rank D̄|_{M̄} = rank X̄ = R = ⌈d/2⌉;
   * S̄ = V ⊕ ker X̄, so X̄ is semisimple at 0 and rank X̄^k = R for all k;
   * BW's invariant d_ℓ is 0, which is the Belmont–Lee–Musat–Trebat-Leder conjecture in the partition case;
   * hence, by BW Thm 1.2, **b_ℓ(m) ≤ 2m − 1 holds unconditionally for every ℓ ≥ 13**. BW verified
     d_ℓ = 0 only by computer, for ℓ < 1300.

   The cited input is Yifan Yang's Shimura-type isomorphism (Nagoya Math. J. 215 (2014) 1–66, Theorem 1, with
   r = 24 − (ℓ mod 24) and s = (ℓ − r − 2)/2). It was verified against the source; see §G1 below. We use it in the form
   S_{λ+1/2}(1, ν_η^{−ℓ}) ≅ S^{new}_{2λ}(Γ₀(6))^{w₂ = −(2/ℓ), w₃ = −(3/ℓ)}, with T_{p²} ↔ (12/p)·T_p.
   The sign class and the twist were checked numerically mod ℓ, by comparing characteristic polynomials, for
   13 primes covering all 8 classes of ℓ mod 24 (§3.4). The proof also uses one fact about a single newform:
   6.6.a.a has w₃ = +1. This sign is what rules out every ℓ, even the non-ordinary primes of 6.6.a.a such as
   ℓ = 859.
2. **Rank attainment (b) is FALSE as stated.** ℓ = 607 is a counterexample; see §5. The correct statement:
   * the unit-root part always has rank exactly R (by Theorem A);
   * **if** L̄(1) is a cyclic vector for T_{ℓ²} on S_{λ+1/2}(1, ν_η^{−ℓ}) ⊗ 𝔽_ℓ, then the stable module
     ℤ_ℓ[X]·e_Y L(1) mod ℓ^m is free of rank R for every m. This follows from Nakayama.
   * The converse (non-cyclic mod ℓ ⇒ deficit at every m) is **not** automatic and needs a lattice argument
     (gap G6). For example, A = diag(1, 1+ℓ) with y = (1,1) generates a rank-2 lattice whose image mod ℓ is
     1-dimensional.
   * At precision one, rank failure is characterized by **failure of L̄(1) to generate the space**.
     Extending that characterization to every precision is the separate G6 obligation. These failures are *not*
     characterized by repeated eigenvalues: non-cyclicity can occur with distinct eigenvalues, and an operator
     with a repeated eigenvalue can still have a cyclic vector.

   At ℓ = 607 the obstruction is a 2-dimensional eigenspace of −367 (geometric multiplicity 2). That is a
   *sufficient* obstruction: no vector is cyclic, and the Krylov rank is 24 = R − 1 mod ℓ (§5.2). BW's deficit
   at all m is reported in their paper, but the computation ranges listed in BW §6.1 cover 607 only at
   m = 1. This draft does not infer the higher-precision claim from that computation. Heuristically it
   fails with probability ≍ 1/ℓ, which suggests infinitely many
   but sparse exceptions (§5.3).
3. **Lower bound b_ℓ(m) ≥ 2m − 1 [reduced; O].**
   * b_ℓ(m) = 2m − 1 for all m is *equivalent* to the non-vanishing Θ^k ū₀ ≠ 0 for all k. Here Θ is an
     explicit second-order operator on K̄ = ker D̄ (dimension ⌊d/2⌋) and ū₀ ∈ K̄ is an explicit vector (§4).
   * This holds whenever Θ is invertible and ū₀ ≠ 0.
   * Both are checked numerically for small ℓ.
   * We see no general proof. Like (b), it is a non-vanishing statement about one specific vector.
4. **Corrected conjecture** (§6): for ℓ ≥ 29, b_ℓ(m) = 2m − 1 [conjectural, but no counterexample known], and
   the stable rank equals R − (defect of cyclicity of L̄(1)), which is R for "most" ℓ but not all.

---------------------------------------------------------------------------------------------------------

## 1. Mod-ℓ filtration lemmas [P]

Standard facts, valid for mod-ℓ modular forms on Γ₁(N) with ℓ ∤ N and ℓ ≥ 5. References: Serre (Antwerp III);
Swinnerton-Dyer (Antwerp III); Katz, "A result on modular forms in characteristic p" (LNM 601, 1977);
Jochnowitz, Trans. AMS 270 (1982).

More precisely, [Katz's original paper](https://web.math.princeton.edu/~nmk/old/modformcharp.pdf),
§II, theorem (1)–(2), supplies the θ operator and the exact filtration increase when ℓ does not divide
the filtration. Corollary (1) sends holomorphic forms to cusp forms. The operator acts as q·d/dq at
every cusp, and the Hasse invariant has q-expansion one at every cusp (§I). Thus lowering by Hasse
factors preserves cuspidality. These statements still require a formal construction in Lean.

* (F1) w(θf) ≤ w(f) + ℓ + 1, with equality iff ℓ ∤ w(f). In general w(θf) = w(f) + ℓ + 1 − s(ℓ−1) with s ≥ 0.
* (F2) For k ≥ 2, U ≡ T_ℓ on M_k mod ℓ, and w(f|U) ≤ ℓ + (w(f) − 1)/ℓ.
* (F3) f|U = 0 ⟺ θ^{ℓ−1}f = f, because f − θ^{ℓ−1}f = (f|U)|V.
* (F4) Weights in one filtration class are congruent mod ℓ−1. A nonzero form of filtration 0 is a constant,
  and θ kills constants.

**Lemma T (low point of a θ-cycle).** Let 5 ≤ k ≤ ℓ − 1 and let f ≠ 0 be a mod-ℓ form with w(f) = k and
f|U = 0. Then w(θ^{ℓ+1−k} f) = ℓ + 3 − k.

*Proof.*
1. Put a_i = w(θ^i f). By (F3), θ^{ℓ−1}f = f, so a_{ℓ−1} = a_0 = k. By (F1) the total drop over the cycle is
   Σ s_i = ℓ + 1. Drops occur only where ℓ | a_i, and no θ^i f vanishes (otherwise f = 0).
2. Since k + i ≢ 0 (mod ℓ) for 0 ≤ i < ℓ − k, we get a_i = k + i(ℓ+1) for i ≤ ℓ − k. Then
   a_{ℓ−k} = ℓ(ℓ+1−k), which is divisible by ℓ.
3. With s the first drop, a_{ℓ−k+1} = ℓ(ℓ+2−k) + 1 − s(ℓ−1) ≡ 1 + s (mod ℓ).
   * After this step the filtrations rise by ℓ+1 per step. The next index with ℓ | a_i is i = 2ℓ − k − s.
   * The cycle closes at i = ℓ − 1, so a second drop is possible only if s ≥ ℓ − k + 2.
   * A single drop of size ℓ+1 would make a_{ℓ−k+1} negative.
   * Hence s ≥ ℓ − k + 2.
4. Positivity gives s ≤ ℓ − k + 2: with s = ℓ − k + 3 we would get a = 4 − k ≤ 0, so θ^{ℓ−k+1}f would be a
   constant in the image of θ, i.e. 0. Therefore s = ℓ − k + 2 and a_{ℓ+1−k} = ℓ + 3 − k. ∎

**Lemma 1 (Ū is invertible on S̄).** For ℓ ≥ 7, U = T_ℓ is invertible on S_{ℓ−1}(𝔽_ℓ).

*Proof.*
* A nonzero f ∈ S̄ has w(f) = ℓ − 1. The only smaller weight in its class is 0, and a constant is not a cusp
  form.
* If f|U = 0, Lemma T with k = ℓ − 1 gives w(θ²f) = 4. So θ²f = cE₄, because M₄(SL₂ℤ) = ℂE₄.
* θ²f has constant term 0 while E₄ has constant term 1, so c = 0. Then θ²f = 0 and f = θ^{ℓ−3}θ²f = 0. ∎

[N] Matches the column "rank U = d" for every ℓ ≤ 229 in `structure_*.log`.

**Lemma 2 (image of D̄).** For ℓ ≥ 13, D̄(M̄) ⊆ V = Δ^t S_{k′}(𝔽_ℓ). Hence dim D̄(M̄) ≤ dim V = R.

*Proof.*
1. Mod ℓ, Φ ≡ Δ^δ = Δ^{ℓt}Δ^ρ = V(Δ^t)·Δ^ρ. Since U(V(A)·B) = A·U(B), we get
   D̄f = Δ^t · U(Δ^ρ f).
2. The weight of Δ^ρ f is 12ρ + ℓ − 1. By (F2), w(U(Δ^ρ f)) ≤ ℓ + (12ρ + ℓ − 2)/ℓ < ℓ + (j+2)/2.
3. The class of this filtration mod ℓ−1 is 12ρ ≡ (ℓ+j−2)/2 = k′. The next weight in the class,
   k′ + ℓ − 1 = (3ℓ+j−4)/2, exceeds ℓ + (j+2)/2 once ℓ > 6. So w ≤ k′.
4. The constant term of U(F) is a₀(F) = 0, because ord Δ^ρ f ≥ ρ ≥ 1. So U(Δ^ρ f) ∈ S_{k′}. This also
   covers f = 1. ∎

**Lemma 0 (dimensions).** dim S_{k′} = R = ⌈d/2⌉ for all ℓ ≥ 13.
*Proof.* Check case by case on j − 1 ∈ {0,4,6,10,12,16,18,22}:
* d = dim S_{24t+j−1} equals 2t for j ≤ 11 and 2t+1 for j ≥ 13;
* dim S_{12t+j−1} equals t for j ≤ 11 and t+1 for j ≥ 13;
* ⌊(ℓ+12)/24⌋ equals the same values. ∎

This is the FKO bound, recovered in one line: the odd L(b) mod ℓ lie in D̄(M̄) ⊆ V. BW Thm 4.3/Lemma 4.4
state the same with the vanishing order ord ≥ t + 1 = ⌈ℓ/24⌉.

---------------------------------------------------------------------------------------------------------

## 2. The half-integral-weight dictionary [P]

Let 𝒮 := S_{λ+1/2}(SL₂ℤ, ν_η^{−ℓ}). Here ν_η^{−ℓ} = ν_η^{−j}, since ν_η^{24} = 1.

1. **h ↦ η^ℓ h.** Dividing by η^j is an isomorphism S_{k′} → 𝒮: weight k′ − j/2 = λ + 1/2, and G ∈ S_{k′}
   has ord ≥ 1 > j/24. Since η^ℓ = Δ^t η^j, we get **V = η^ℓ·𝒮 ≡ η(ℓz)·𝒮 (mod ℓ)**.
2. **X̄ on V is U_{ℓ²}.** For F = Δ^t G ∈ V:
   * D̄ŪF = Δ^t·U(Δ^ρ U(Δ^t G)) = Δ^t·U²(Δ^{ℓρ+t} G) = Δ^t·U²(Δ^{jδ} G);
   * and U²(Δ^{jδ}G) ≡ U²(V_{ℓ²}(η^j)·G/η^j) = η^j·U_{ℓ²}(G/η^j).

   So in the coordinate h = G/η^j ∈ 𝒮, **X̄|_V = U_{ℓ²}**. Exponents of h lie in −ℓ/24 + ℤ, and U_{ℓ²}
   preserves that class because ℓ² ≡ 1 (mod 24). Hence X̄(S̄) ⊆ V and X̄(V) ⊆ V.
3. **U_{ℓ²} ≡ T_{ℓ²}.** On h(24z) ∈ S_{λ+1/2}(Γ₀(576), χ),
   T_{ℓ²} = U_{ℓ²} + χ*(ℓ)ℓ^{λ−1}(·/ℓ) + ℓ^{2λ−1}V_{ℓ²}. For λ ≥ 2 (ℓ ≥ 7) this gives T_{ℓ²} ≡ U_{ℓ²}
   (mod ℓ). T_{ℓ²} is integral and 𝒮(ℤ) ⊗ 𝔽_ℓ = 𝒮(𝔽_ℓ) (Miller basis of S_{k′}).
4. **Odd/even split.** Write S̄ = η·𝒯, with 𝒯 = S_{ℓ−3/2}(1, ν_η^{−1}).
   * D̄(ηg) = η(ℓz)·U_ℓ(g), and this holds exactly, not only mod ℓ: Φη = η(ℓ²z).
   * Ū(η(ℓz)h) = η·U_ℓ(h).

   So D̄ and Ū|_V are the two halves U_ℓ: 𝒯 → 𝒮 and U_ℓ: 𝒮 → 𝒯 of U_{ℓ²} = U_ℓ∘U_ℓ.
5. **The vector L̄(1).** L̄(1) = D̄(1) = η(ℓz)·U_ℓ(1/η). In the coordinates W(G) = (coefficients 1..R of
   G·∏(1−qⁿ)^{−j}), it is
   (p(ℓn − ρ) mod ℓ)_{n=1..R}.

   In these coordinates, X̄|_V has entries W(ΞG)_n = coeff_{ℓ²n − jδ}(G∏(1−qⁿ)^{−j}). This is implemented in
   `scripts/frontier/pattern/halfint.py`. It needs q-expansions only to ℓ²R terms, about 9·10⁶ at ℓ = 607.

[N] For every ℓ in 29..113, the characteristic polynomial of Ξ = X̄|_V from `halfint.py` agrees *factor by
factor* with the nonzero part of charpoly(X̄|S̄) computed independently in Katz coordinates
(`structure_13_60.log`, `structure_61_230.log`).

---------------------------------------------------------------------------------------------------------

## 3. Theorem A: X̄|_V is invertible for every ℓ ≥ 13 [P*]

**Theorem A (proposed paper theorem).** For every prime ℓ ≥ 13, det(T_{ℓ²} | 𝒮) is an ℓ-adic unit.
Equivalently, U_{ℓ²} is invertible mod ℓ on S_{(ℓ−2)/2}(SL₂ℤ, ν_η^{−ℓ}), or X̄|_V is invertible.
The integral-weight statement used to establish it is: every newform in
S^{new}_{ℓ−3}(Γ₀(6))^{(−(2/ℓ),−(3/ℓ))} is ordinary at every prime above ℓ.

**Corollary A.** For ℓ ≥ 13:
1. D̄(M̄) = D̄(S̄) = V, so rank D̄ = R = ⌈d/2⌉. Indeed V = X̄(V) ⊆ D̄(S̄) ⊆ D̄(M̄) ⊆ V.
2. ker X̄ = Ū^{−1}(ker D̄) has dimension d − R = ⌊d/2⌋, and S̄ = V ⊕ ker X̄. So X̄ is semisimple at 0 and
   rank X̄^k = R for all k ≥ 1.
3. BW's largest X̄-invertible subspace is V_inv = im X̄^d = V ⊇ D̄(M̄). Hence **d_ℓ = 0** (BW (5.1)). This is the
   BLMT conjecture (Monatsh. 2014, §5) for the partition function.
4. **b_ℓ(m) ≤ 2m − 1 for all m**, by BW Thm 1.2. §4.1 gives an independent proof from the envelope lemmas.
5. The unit-root subspace Y of X (on the odd overconvergent space) has rank exactly R, and Ȳ = V. Equivalently,
   X has exactly R Newton slopes equal to 0.

### 3.1 Input: Yang's isomorphism [cited; verified against the source, §G1]
Yifan Yang (Nagoya Math. J. 215 (2014), Theorem 1, with r = 24 − (ℓ mod 24), s = (ℓ − r − 2)/2) constructs a Hecke-equivariant isomorphism (Shimura lift):

  𝒮 = S_{λ+1/2}(SL₂ℤ, ν_η^{−ℓ}) ≅ S^{new}_{2λ}(Γ₀(6))^{(w₂, w₃)}, with T_{p²} ↔ (12/p)·T_p for p ≥ 5.

The relevant sign class is (w₂, w₃) = (−(2/ℓ), −(3/ℓ)), using pari's Atkin–Lehner eigenvalue convention
a_p = −w_p p^{k/2−1}. This form of the statement is what Ahlgren–Allen–Tang and Ahlgren–Beckwith–Raum use.
The published Theorem 1 and the sign normalization have been checked against the source; see §G1.
§3.4 also checks the statement numerically. This is a characteristic-zero correspondence. The
determinant argument uses integral Hecke lattices and does not assume that Yang's isomorphism itself
is integral.

Consequence: det(T_{ℓ²}|𝒮) = ±∏_F a_ℓ(F), the product running over the newforms F in that class.

### 3.2 Proof of Theorem A
1. Suppose some newform F of weight k = ℓ − 3 in the class has a_ℓ(F) ≡ 0 (mod 𝔩).
2. Its reduction F̄ is a nonzero mod-𝔩 eigenform on Γ₀(6) with F̄|U = 0. Its filtration is ℓ − 3, since the
   only smaller weight in the class is −2 < 0.
3. Since 5 ≤ ℓ−3 ≤ ℓ−1, **Lemma T** gives w(θ⁴F̄) = 6. So G̃ := θ⁴F̄ is a nonzero mod-𝔩 cuspidal eigenform
   in S₆(Γ₀(6)) ⊗ 𝔽̄_ℓ, with eigenvalues
   * p⁴a_p(F) for T_p, p ∤ 6ℓ;
   * 16a₂(F) for U₂ and 81a₃(F) for U₃. Use a_{pn}(θ⁴F) = p⁴n⁴a_{pn}(F).
4. Use the operator polynomial on the three-dimensional S₆(Γ₀(6)):

   **(U₃ + 9I)(U₂² + 6U₂ + 32I) = 0.**

   It follows from the rational old/new decomposition:
   * the newform 6.6.a.a = q + 4q² − 9q³ + …, with (w₂, w₃) = (−1, +1);
   * the two U₂-eigen oldforms from 3.6.a.a = q − 6q² + 9q³ + …, with U₂ eigenvalues the roots of
     x² + 6x + 32 and U₃ = 9.

   (S₆(Γ₀(2)) = S₆(SL₂ℤ) = 0.) The polynomial kills the new line through its first factor and the
   old space through its second factor. An identity over the fraction field holds on any stable
   integral lattice and hence its reduction. The comparison of that reduction with the weight-six
   mod-ℓ space must be justified; no integral splitting of the old/new decomposition is needed.
   This replaces Deligne–Serre lifting and requires no semisimplicity in characteristic ℓ.
   `scripts/frontier/pattern/weight_six.gp` independently recomputes the exact rational matrices.
   `TheoremA/WeightSixIdentity.lean` now proves this identity on the actual
   classical cusp space. The proof constructs eta quotient cusp forms, proves
   their coefficients through q⁹, and uses the three-coefficient bound to
   identify the Hecke action on a spanning set. It assumes no old/new splitting.
   The identity also descends to every embedded coefficient ring and its
   residue rings. The comparison with characteristic-ℓ modular forms remains
   an input, recorded explicitly in `LiftedOrdinarity.lean`. See the
   [formalization guide](THEOREM_A.md#the-finite-analytic-certificate).
5. The newform F has a₂(F) = −w₂(F)·2^{(ℓ−5)/2} = (2/ℓ)·2^{(ℓ−5)/2} ≡ 2^{−2} and
   a₃(F) = (3/ℓ)·3^{(ℓ−5)/2} ≡ 3^{−2}, using 2^{(ℓ−1)/2} ≡ (2/ℓ). So G̃ has U₂ = 4 and U₃ = 9.
   Applying the polynomial to G̃ gives **18·72·G̃ = 1296·G̃ = 0**. Since ℓ ≥ 13 and G̃ ≠ 0,
   this is impossible. Both the Euler-criterion calculation and the scalar contradiction are
   formalized over arbitrary residue fields of characteristic ℓ, not only over 𝔽_ℓ.
6. This is a contradiction, so every a_ℓ(F) is a unit. ∎

*Remark (why the sign matters).*
* 6.6.a.a is **non-ordinary at ℓ = 859**: a₈₅₉ = −33566284 = −859·39076. This came from a pari scan of
  ℓ ≤ 3·10⁵, interrupted after 859 was found; we did not establish whether 859 is the smallest.
* For that ℓ, θ^{ℓ−5}(6.6.a.a) is a non-ordinary eigenform of weight ℓ − 3. Its class is
  (w₂, w₃) = (−(2/ℓ), +(3/ℓ)), which is the *wrong* class.
* If Yang's class were (·, +(3/ℓ)), Theorem A would fail at ℓ = 859, and BW's computation d_ℓ = 0 for
  ℓ < 1300 would be contradicted. So BW's data and §3.4 independently confirm the sign.
* **The direct computation at ℓ = 859 has been run, and it confirms Theorem A.** Script
  `scripts/frontier/pattern/l859_compose.py`, log `l859_compose.log`. Results:
  * det(X̄|_V) = 318 ≠ 0 mod 859, so rank = R = 36;
  * rank D̄ = 36 on both S̄ and M̄ (Eisenstein direction included);
  * rank X̄^k = 36 for k ≤ 72, so X̄ is semisimple at 0;
  * d₈₅₉ = 0 by the exact test rank[X̄^d | D_M] = rank X̄^d;
  * Krylov rank of L̄(1) = 36, so rank attainment holds;
  * the charpoly of X̄|_V is squarefree.

  This is exactly the case where 6.6.a.a is non-ordinary. The method composes D̄∘Ū with re-expansion in the
  basis Δ^iE₄^aE₆^b, so it needs only O(ℓ·d) q-coefficients (~7·10⁴ terms, 7 s, 280 MB). That makes BW-range
  checks (ℓ < 1300) cheap. It was validated against ℓ = 29, 47, 71, 113 and 607; the ℓ = 607 run reproduces
  the (x+367)² anomaly exactly.

### 3.3 Proof of Corollary A, item 5
* The number of zero slopes of X on the odd overconvergent space equals the dimension of the generalized
  nonzero eigenspace of X̄ on the mod-ℓ reduction of an X-stable lattice.
* In the envelope lattice A₁ (see §4), X̄ factors through the block-1 reduction ρ: A₁ → S̄. Its nonzero
  generalized eigenspace is therefore that of X̄|_{S̄}, which is V, of dimension R. ∎

### 3.4 Numerical evidence for Theorem A and the sign class [N]
* `halfint.py`, ℓ = 29..113: det Ξ ≠ 0 and rank Ξ = R. These are all the primes in that range; 29 was checked
  separately.
* `yang.gp` (scripts/frontier/pattern) computed T_ℓ mod ℓ on S^{new}_{ℓ−3}(Γ₀(6)) split by (w₂, w₃). For
  **ℓ = 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 83** (every class of ℓ mod 24), the class
  (−(2/ℓ), −(3/ℓ)) is the one whose charpoly, after the substitution x ↦ (12/ℓ)x, equals charpoly(Ξ) exactly.
  Examples:
  * ℓ = 29: Ξ = x+26, class (1,1) has x+3, and (12/29) = −1;
  * ℓ = 47: x²+18x+19 in both;
  * ℓ = 71: x³+18x²+2x+2 in both.

  The class dimensions also match R.
* ℓ = 607: det Ξ ≠ 0 and rank 25 = R (§5.2).

---------------------------------------------------------------------------------------------------------

## 4. b_ℓ(m) versus 2m − 1

### 4.0 Exact reduction of b_ℓ(m) to valuations [P]
1. Let Y ⊕ Z be the Riesz decomposition of X on the odd space, with Y the unit-root part and Z the part of
   positive slope.
2. Let e_Y = lim X^{n!}. It is integral on every X-stable lattice: X|_Y ∈ GL_R(ℤ_ℓ) has finite order mod ℓ^k,
   and X^{n!} → 0 on Z.
3. Write L(1) = y + z with y = e_Y L(1).
4. q-expansion integrality is equivalent to integrality of the Katz coordinates. Then:
   * the odd chain is stable at b = 2k+1 mod ℓ^m ⟺ v(X^k z) ≥ m;
   * the even chain is stable at 2k+2 ⟺ v(U X^k z) ≥ m.

   Proof of "⟸": span{X^i y : i ≥ k} = ℤ_ℓ[X]y, since X|_Y is invertible and X^{−1}|_Y is a polynomial in X.
   Proof of "⟹": project the stable span with e_Z, which is integral.
5. Hence

   **b_ℓ(m) = min(2k_o + 1, 2k_e + 2), with k_o = min{k : v(X^k z) ≥ m} and k_e = min{k : v(UX^k z) ≥ m}.**

   **b_ℓ(m) ≤ 2m−1 ∀m ⟺ v(X^k z) ≥ k+1 ∀k.**
   **b_ℓ(m) = 2m−1 ∀m ⟺ in addition v(U X^k z) = k+1 ∀k.**

### 4.1 Upper bound from Theorem A [P, given AO envelope lemmas]
This is independent of BW's d_ℓ machinery. It uses the envelopes A_c(α), A_c(β) of
`docs/ATKIN_OBRIEN_PROOF.md`, Step 2: U(A₂(β)) ⊆ A₁(α), D(A₂(α)) ⊆ A₁(β), and both preserve A₁. These are
proved for every p ≥ 13 (Lean `Envelope.lean`, independent of d), from inputs (I1)–(I3).

1. A₁ = B₁ ⊕ ℓE₂ and ℓA₂ = ℓB₁ ⊕ ℓE₂. So the reduction ρ: A₁ → S̄ (block 1 mod ℓ) has kernel ℓA₂. Since
   T(ℓA₂) ⊆ ℓA₁, ρ is X-equivariant: ρ(Xx) = X̄_S ρ(x).
2. If x ∈ Z ∩ A₁, then X^n x → 0, so X̄_S^n ρ(x) = 0. Hence ρ(x) lies in the generalized kernel, which is
   ker X̄_S by Corollary A.
3. **Induction.** w_k := X^k z/ℓ^{k+1} ∈ A₂ ∩ Z for all k.
   * Base: ρ(z) ∈ ker X̄_S ∩ (Im D̄ + Im X̄_S) = ker ∩ V = 0. (ρ(y) = lim X̄^{n!}ρ(L(1)) ∈ V.) So z ∈ ℓA₂.
   * Step: x = Xw_k ∈ A₁ ∩ Z has ρ(x) = D̄ ρ_α(Uw_k) ∈ V ∩ ker X̄_S = 0. So x ∈ ℓA₂.
4. So v(X^k z) ≥ k + 1, and b_ℓ(m) ≤ 2m − 1. ∎

For d = 1 one has ker X̄_S = 0, and the same argument runs one T-step at a time. That is the Atkin–O'Brien
proof.

### 4.2 Lower bound: the second-order operator Θ [P for the reduction; O for non-vanishing]
1. Let u_k := U w_k ∈ A₁(α), with ū_k := ρ(u_k) ∈ S̄. By 4.0, the lower bound for all m is equivalent to
   ū_k ≠ 0 for all k.
2. By 4.1, D̄ū_k = ρ(Xw_k) = 0, so ū_k ∈ K̄ := ker D̄|_{S̄} (dimension ⌊d/2⌋). Put
   S̄ = Ū(V) ⊕ K̄ (Corollary A) and let π_K be the projection along Ū(V).
3. **Definition.** Θ: K̄ → K̄, Θ(ū) := π_K ρ(U(Dũ/ℓ)), for any lift ũ ∈ A₁(α) of ū.
   * Dũ ≡ D̄ū = 0, so Dũ/ℓ ∈ A₂.
   * Changing the lift by ℓa with a ∈ A₂ changes the value by ŪD̄(ā) ∈ Ū(V), by Lemma 2 applied to small
     filtrations. So Θ is well defined.
4. **Proposition.** ū_{k+1} = Θ(ū_k). Hence **b_ℓ(m) = 2m − 1 for all m ⟺ Θ^k ū₀ ≠ 0 for all k**, with
   ū₀ = ρ(U z/ℓ). A sufficient condition is that Θ is invertible and ū₀ ≠ 0.
   *Proof.* ū_{k+1} = ρ(U D u_k/ℓ). It lies in K̄ by 4.1, so ū_{k+1} = π_K(ū_{k+1}) = Θ(ū_k). ∎
5. In half-integral terms, ũ = ηg̃ with g̃ ∈ 𝒯 a lift of a form in ker U_ℓ, and
   Θ(ū) = π_K[(U_{ℓ²}g̃)/ℓ − U_{ℓ²}(e₁ g̃)], where E_{ℓ−1} = 1 + ℓe₁. The first term is the slope-1 part of
   T_{ℓ²} on the classical weight-(ℓ − 3/2) space. The second is a weight-derivative correction.
6. Expected: Θ is invertible ⟺ X has exactly ⌊d/2⌋ slopes equal to 1 (BL_PATTERN) and Θ̄ ≡ (X/ℓ) on the
   slope-1 part. The ⟸ direction is not proved here.

**One sufficient route to a proof.**
* (i) Θ invertible: an exact slope-1 count. Via Ramsey/Coleman this is plausibly the ordinary part of a
  θ-twisted space of weight ℓ − 5 and level 6, but this is not worked out.
* (ii) ū₀ ≠ 0: a non-vanishing statement for one explicit vector. Like (b), we expect this can only be checked
  ℓ by ℓ.

**A weaker and exact target (2026-11-01).** Put `s=dim K̄`. Once the
arithmetic realization in items 1–4 is established, it is enough, and is
necessary, to prove the single finite condition `Θ^s ū₀ != 0`. The general
linear-algebra equivalence is already kernel-checked as
`FiniteArithmetic.orbit_nonzero_iff` in `FiniteArithmetic/Orbit.lean`.
The increasing kernels of the powers stabilize by dimension s, so a vector
that ever dies must die by that step. In the Fitting decomposition of K̄,
the condition says exactly that ū₀ has a nonzero component in the invertible
summand. It does not require the whole operator to be invertible.

For example, `Θ=diag(0,1)` and `ū₀=(1,1)` give `Θ^n ū₀=(0,1)` for every
`n>=1`. A zero eigenvalue kills one component but leaves the orbit alive.
The same singular matrix with `ū₀=(1,0)` has a dying orbit. Thus the operator
alone cannot decide sharpness. Another sufficient certificate is a left
eigenvector functional `f` with `f∘Θ=a f`, `a!=0`, and `f(ū₀)!=0`;
then `f(Θ^n ū₀)=a^n f(ū₀)` never vanishes.

This changes the useful research target: identify the actual Θ model and
certify survival of its specific seed, even at a prime where one slope-one
direction is lost. The algebraic survival theorem is proved; the all-prime
arithmetic realization and seed nonvanishing are not.

Asymptotically: if (i) holds, then b_ℓ(m) ≥ 2m − C_ℓ for all m iff the slope-1 projection of L(1) is nonzero.

[N]
* b_ℓ(m) = 2m − 1 exactly for all 41 primes 29 ≤ ℓ ≤ 229, for m ≤ 16 / 9 / 7 (`bstab.py`, `bigstab.py`). This
  means Θ^kū₀ ≠ 0 for those k.
* `theta2.py` computes Θ and ū_k directly: see §4.3.

### 4.3 Θ numerics [N]
`theta2.py` (Katz model PR = 3, N = 6) computes Θ on K̄ and ū₀, ū₁ directly from L(1):

| ℓ | dim K̄ | Θ (eigenvalue) | ū₀ | ū₁ | Θū₀ |
|---|---|---|---|---|---|
| 29 | 1 | 23 | 8 | 10 | 10 |
| 31 | 1 | 2 | 5 | 10 | 10 |
| 37 | 1 | 20 | 9 | 32 | 32 |
| 41 | 1 | 31 | 26 | 27 | 27 |
| 43 | 1 | 31 | 40 | 36 | 36 |
| 47 | 1 | 17 | 19 | 41 | 41 |

* The Proposition ū₁ = Θū₀ is confirmed in every case.
* **Θ agrees with the slope-1 eigenvalue.** The eigenvalue of Θ equals μ = λ_{slope 1}/ℓ mod ℓ, read off from
  the Newton polygon of charpoly(X) in the Katz model (μ ≡ (e_{r+1}/ℓ)/e_r). The values are 23, 2, 20, 31, 31, 17,
  matching the table exactly. This supports "Θ = reduction of X/ℓ on the slope-1 part".
* For **ℓ = 53..113** (all 15 primes, dim K̄ = 2, 3, 4), Θ has full rank dim K̄ and a squarefree charpoly,
  and ū₀ ≠ 0. Examples:
  * ℓ = 53: (x+18)(x+28);
  * ℓ = 79: an irreducible cubic;
  * ℓ = 113: an irreducible quartic.

  So for every prime 29 ≤ ℓ ≤ 113 the sufficient condition "Θ invertible and ū₀ ≠ 0" holds, and with it
  **b_ℓ(m) = 2m − 1 for ALL m**. This is a proof for each such ℓ individually, given 4.0–4.2, Corollary A, and
  the validity of the truncated Katz model (PR = 3, N = 6). Θ mod ℓ only sees Katz blocks i with α(i), β(i) ≤ 2, by the envelope bounds, so N = 6 suffices. This routine check should still be written out. (2026-11-03: for ℓ = 37, 41, 43, 47 the conclusion b_ℓ(m) = 2m − 1 for all m is now proved in Lean by a different finite route, without the truncated Katz model: `Rank2At37.bEll_37`, …; and for ℓ = 53, 59 with the 2×2 Θ above: `RankSAt53.bEll_53`, `RankSAt59.bEll_59`; and for every prime 61 ≤ ℓ ≤ 113 by an order-r recurrence: `RankRAt61.bEll_61`, …, `RankRAt113.bEll_113`. The certified Θ matches the T_ℓ prediction of §4.4 at every prime 29–113, and the certified odd recurrence matches (12/ℓ)T_ℓ on S^new_{ℓ−3}(Γ₀(6)) in the same class at every prime 37–113; see [RESULTS](RESULTS.md).)

### 4.4 Θ in weight ℓ−5 [N for the identification; the lift identity is `BLBound.rc_lift`]

**Numerical identification [N].** For all 21 primes 29 ≤ ℓ ≤ 113,

charpoly(Θ on K̄) = charpoly((12/ℓ)·(1/5)·T_ℓ on S^new_{ℓ−5}(Γ₀(6)) with w₂ = −(2/ℓ), w₃ = −(3/ℓ)),

and that space has dimension ⌊d/2⌋. The constant was fitted on ℓ = 29..47; ℓ = 53..113 then matched the
existing `theta2.py` logs exactly (`theta_charpoly_pred.gp`). `theta_twist_table.gp` shows the mechanism: slope-1
newforms f of weight 2ℓ−4 satisfy a_p(f) ≡ p·a_p(g) for a form g of weight ℓ−5, with w_p(f) = (p/ℓ)·w_p(g), and
a_ℓ(f)/ℓ ≡ −a_ℓ(g)/5. Each table has one slope-1 form with no such g; none lies in the class that gives Θ.

**Lift identity [proved in Lean: `BLBound.rc_lift`; also checked by `rc_lift_check.py`].** Let g have weight k, E = E_{ℓ−1} = 1 + ℓe, and
F = [g, E]₁ = k g θE − (ℓ−1) E θg, of weight k + ℓ + 1. Then F ≡ θg (mod ℓ), and

(UF)/ℓ ≡ (1/k)·θ(Ug) + ((k−1)/k)·(∂(Ug) − U(∂g)) (mod ℓ), where ∂ = θ − (k/12)E₂.

The derivation uses θe ≡ (E₂ − VE₂)/12, U(a·Vb) = b·Ua, and U∘θ ≡ 0. The second term lies in weight k + 2. So with
k = ℓ−5, modulo weight ℓ−3, T_ℓ/ℓ acts on θ(S_{ℓ−5}) as (1/k)·T_ℓ, which explains the constant −1/5.
It was checked on 46 coefficients at (ℓ, k) = (17, 12) and (29, 24).

**Consequences, not yet proved.**
* Non-invertibility of Θ should come from a U-kernel in weight ℓ−5. By Lemma T its low point has weight 8, in the class
  w₂ = w₃ = −1. Unlike weight 6, this class is occupied: 6.8.a.a has a₂ = 8, a₃ = 27. So the sign argument of §3 does
  not apply, and the expected statement is **Θ is singular ⟺ ℓ ∣ a_ℓ(6.8.a.a)**. No such prime exists below 60000
  (`nonordinary_wt8.gp`; the same scan recovers 859 for 6.6.a.a).
* Missing: the dictionary from the integer-weight statement to Θ on K̄ (half-integral weight ℓ − 3/2), and G5.

### 4.5 Conjectural slope law for X [N, not proved]

Let ε = (12/ℓ) and let the class be w₂ = −(2/ℓ), w₃ = −(3/ℓ). In the Katz model, the slope-j part of X appears to have residual characteristic polynomial equal to that of

(ε/C(2j+3, j)) · T_ℓ on S^new_{ℓ−3−2j}(Γ₀(6)) in the class, together with (ε/C(2j+3, j)) · a_ℓ(h)⁻¹ for each newform h of level 6, weight 2j+4 and signs w₂ = w₃ = −1.

Evidence (`slope_law_test.py`): all 23 primes 29 ≤ ℓ ≤ 131, 132 slope segments match, reaching j = 9 at ℓ = 29, 31 and j = 2 at ℓ = 127, 131. The constants were fitted at j = 0, 1, 3 and the extra term at j = 2. The weight-12 and weight-16 extras (j = 4, 6) and the constants C(11,4) = 330 and C(15,6) = 5005 were then correct without further fitting.
12 further segments disagree. Each is the last segment read at its prime and has fewer eigenvalues than predicted, so I read them as truncation. That reading is not independently verified.

**Exceptional prime.** h and its partner of weight ℓ+3−(2j+4) lie on one θ-cycle. So ℓ ∣ a_ℓ(h) should merge slopes j−1 and j. The weight-12 form (a₂ = 32, a₃ = 243) has 37 ∣ a₃₇, the only such prime up to 2000 for that form, and X at ℓ = 37 has slope 3.5 with multiplicity 2 in place of slopes 3 and 4.

**Correction to the proposed consequence for §6.3 (2026-11-01).** If
ℓ ∣ a_ℓ(6.8.a.a), a slope-one and a slope-two direction are expected to
merge to slope 3/2. This does **not** imply that the entire contracting
error gains more than one digit per cycle: other slope-one directions can
remain, and the partition seed can have a nonzero component there. Under
the realization in §4.2, failure of exact sharpness requires
`Θ^(dim K̄) ū₀=0`, not merely `det Θ=0`. The earlier inference that these
primes should be excluded from the all-prime sharpness conjecture was
unjustified. Singularity remains a useful place to test the seed criterion.
An exact PARI scan of 6.8.a.a finds no such prime among the 22,042 primes
`5 <= ℓ <= 250000`; see `docs/verification/weight8_nonordinary.json`.
This is bounded evidence only. The informal heuristic `Σ 1/ℓ` is not a
proof that any exceptional primes exist or that their number is infinite.

**Also checked numerically (`d_closed_form_check.py`).** With A = (q;q)^ℓ/(q^ℓ;q^ℓ), one has A² ≡ E_{ℓ−1} and D(F) ≡ A⁻¹·U(Δ^δ F) modulo ℓ².

**What a proof can use.** X is conjugate to U_{ℓ²} on F/η(ℓz), exactly, since D(F) = η(ℓz)·U(F/η). So by Ramsey's overconvergent Shimura theory the law concerns U_ℓ in p-adic weight −2. The Smith form of X (computed for eight primes 29 ≤ ℓ ≤ 61) has multiplicities such as 1, 2, 0, 2, 1, 2 at ℓ = 29, against the law's 1, 1, 1, 1, 2, 1. The Newton polygon touches the Smith polygon only through slope 1. So j = 0, 1 reduce to determinants on the Smith graded pieces, but j ≥ 2 needs a lower bound that the Smith form does not provide, which is the hard part of ghost-type theorems.

**Proved in Lean toward j = 1.** `ThetaLift.gen_modular`: the explicit lift of G/η^j is a modular form of weight 2λ on Γ₀(6), for every j < 24 prime to 6, every even weight k′ = λ + (j+1)/2 with λ ≥ 2, and every squarefree t ≡ −j (mod 24), with no prime ℓ in the statement. `ThetaLift.genLift_U_dvd`: the lift carries the U-kernel to the U-kernel. `TheoremA.dvd_coeff_hEight_of_binary_kernel`: a nonzero series of weight p−5 in the sign class with U_p f = 0 forces p ∣ a_p(h₈), where h₈ = q + 8q² + 27q³ + ⋯. With `BLBound.rc_lift` these are four links of the j = 1 chain. Not proved: the U-kernel in weight 2p−4 is θ of weight p−5 in the binary model; the bad-prime eigenvalues of the general lift; and the identification with Θ on K̄ with its dimension count.

**The next link is not a theta-cycle port.** For F of filtration 2p−4 with U_p F = 0, the numerical cycle gives the predecessor θ^{p−2}F filtration p(p−5), not p−5, which fits θ^{p−2}θg = g − (Ug)^p. So F = θg does not follow from filtrations. `ker_u_structure.py` measures, for p = 29, 31, 37, 41, 43, 47 at level 6: U has rank p−2 from weight 2p−4 and ker U has dimension p−1. It contains θ(M_{p−5}), of dimension p−4, with a quotient Q of dimension 3. On Q, (U₂, U₃) never has the eigenpair (1/4, 1/9) (it has (1/4, −1/9) and two pairs with U₃ = 1/9, where these lie in 𝔽_p). `ku.py` also found, for eight primes through 61, that ker U and θ(M_{p−5}) have the same (1/4, 1/9)-eigenspace. So the claim needed is numerically true. Proposed paper proof, not checked: with u a hauptmodul of X₀(6), U is the Cartier operator on P¹ for a rank-one log connection with residue −5 at the supersingular points, and Q is H¹(P¹, O(−4)). Formalizing that needs Cartier invariance under the change of coordinate q ↦ u, which the repo does not have.

**Identification of Q [N].** The eigenpairs on Q are those of θ^{p−5} on S₆(Γ₀(6)): (2⁻⁴·4, 3⁻⁴·(−9)) from 6.6.a.a, and (2⁻⁴α, 3⁻⁴·9) with α² + 6α + 32 = 0 from 3.6.a.a. `ker_u_identify.py`: ker U = θ(M_{p−5}) + θ^{p−5}(M₆) at 14 of 15 primes 13 ≤ p ≤ 73. It fails at p = 67, where the span has dimension 64 and ker U has 66; the reason is not understood (none of the weight-6 newforms is non-ordinary at 67). The form of the claim that a proof needs does hold at p = 67 too: with P(A, B) = (A−1)(A−32)(B+9)(A²+6A+32), `ker_u_pi_test.py` finds Π = P(16U₂, 81U₃) sends ker U into θ(M_{p−5}) at all 10 primes tested in 13 ≤ p ≤ 73 (coefficients up to D/48). Since P(4, 9) = −108864 ≠ 0, this gives the sign-class statement, and it is the same pair (4, 9) that Theorem A excludes in weight 6. Not proved. A proof would need the three functionals on ker U and their Hecke action, presumably through a residue pairing with weight 6.

**Relation to known work.** Buzzard's slope conjecture and the Bergdall–Pollack ghost conjecture predict integer slopes in the regular case at integer weight. This law may be a case of that framework at p-adic weight −2 after a Shimura lift; I have not checked. It does not give ū₀ ≠ 0 (G5).

### 4.6 The constant in the slope law: Rankin–Cohen brackets [formula N; derivation heuristic; none of it in Lean]

**General law [N].** Let w = k + 2j + s(ℓ−1) with 3 ≤ k ≤ ℓ+1, and put u = C(s,j)/C(k+j−1,j) = ∏_{i<j} (s−i)/(k+i). The slope-j part of T_ℓ on S_w(SL₂(ℤ)) appears to have residual characteristic polynomial equal to that of

u·T_ℓ on S_k, together with u·T_ℓ⁻¹ on M_{ℓ+1−k}.

Evidence (`rc_full_law_level1.py`, weights up to about 4(ℓ−1) to 5(ℓ−1), j ≥ 1): 1068 of 1116 integer-slope segments match, for ℓ = 29, 31, 37, 41 (562/586) and 43, 47, 53, 59 (506/530), with no degrees to spare. The constant was derived before these runs, not fitted. The 48 misses and 12 half-integer segments have two visible sources:
* k = ℓ+1 (36 misses). There the class also contains k = 2, and the prediction is not worked out; the multiplicities are also larger than k = 2 alone explains.
* ℓ = 59 with k = 16 or its partner 46 = ℓ+3−16 (12 misses, plus all 12 half-integer segments). 59 ∣ a₅₉ in weight 16 (checked), so this is the merging described in §4.5. It is the only such prime in these runs.

Segments where a binomial vanishes mod ℓ were skipped (34), as were those with a non-ordinary companion (12).

**Relation to §4.5.** s = −1 and k = ℓ−3−2j give u = (−1)^j / ((−1)^j C(2j+3,j)) = 1/C(2j+3,j), which is exactly the constant fitted there. The factor ε is not explained here and presumably comes from the half-integral Hecke normalization. Since s = −1 is not a classical weight, this step is an extrapolation in the ℓ-adic weight. The formula also explains the sign difference between −1/5 at weight 2ℓ−4 (s = 1) and +1/5 at weight −2 (s = −1). It predicts u = 0 for 0 ≤ s < j, meaning that piece does not occur at slope j in such a weight.

**Exact identity [P, elementary].** For the bracket [g, W]_j = Σ_r (−1)^r C(k+j−1, j−r) C(l+j−1, r) θ^r g · θ^{j−r} W,

U[g, VW]_j = ℓ^j [Ug, W]_j,

using Uθ = ℓθU, θV = ℓVθ and U(a·Vb) = b·Ua. Note this gives ratio 1, not u, for the level-ℓ form [g, VW]_j. It is not an eigenvalue statement: U[g, W]_j and U[g, VW]_j differ through terms that lie in lower classes only modulo higher filtration.

**Where the binomial comes from [heuristic].** Take W with θ log W = sℓ(P − VP), P = E₂/12, for example W = A^{2s} with A = η^ℓ/η(ℓz). This is exact for A^{2s}, whereas E^s_{ℓ−1} agrees with it only to first order, which is not yet handled. Expand θ^b W/W as a Bell polynomial and extract V-parts through U(a·Vb) = b·Ua. Counting ℓ-orders, only the monomials made entirely of VP reach order ℓ^b in the θ^b(Ug) direction, and they sum to

ℓ^b · Ug · θ^b(η^{−2s})/η^{−2s},

where η^{−2s} has weight −s and is killed by the Serre derivative. So its top P-coefficient is the rising factorial (−s)_b, while θ^b h = (k)_b P^b h + ⋯ for h of weight k. Hence

U(g θ^b W) has θ^b(Ug)-coefficient ρ_b = (−1)^b C(s,b)/C(k+b−1,b).

The denominator is the depth symbol of θ^b, and this is the origin of the binomial. Integrating by parts in the bracket gives

κ_j = Σ_r (−1)^r C(k+j−1,j−r) C(−s+j−1,r) Σ_i (−1)^i C(r,i) ρ_{j−r+i} = C(s,j)²/C(k+j−1,j),

checked symbolically in k, s for j ≤ 8 (`rc_kappa_identity.py`), not proved for all j. Since [h, W]_j ≡ C(s,j) θ^j h (mod ℓ), the ratio is κ_j/C(s,j) = u. For j = 1 this reproduces the algebra of `BLBound.rc_lift`, whose stated case is s = 1.

**Bracket statement [N].** `rc_quotient_test.py`: with Λ the saturated slope-<j sublattice of M_w(1) and F_j(g) = [g, E^s_{ℓ−1}]_j,

T_ℓ F_j(g) ≡ ℓ^j u F_j(T_ℓ g) (mod Λ + ℓ^{j+1} M_w).

It holds for all 30 basis forms at ℓ = 29, s = 2, 3, 1 ≤ j ≤ s, k = 12, 16, 20. The control u+1 fails in all 30, and F_j(T_ℓ g) ∉ Λ + ℓ^{j+1} M_w, so the test is not vacuous. For j ≥ 2 the same statement fails if Λ is replaced by brackets alone, even after saturation (`rc_tri_test.py`). So the companion forms are genuinely needed in the lower part.

**What is missing for a proof.**
1. The lower terms of the expansion must be shown to lie in Λ. In overconvergent forms a depth-0 "lower term" can absorb anything (g ↦ gW is onto), so the top coefficient only means something once the lower terms are bounded in filtration. This is the main gap.
2. The Newton polygon itself: a lower bound on slopes, and multiplicities. The bracket statement gives a slope-j eigenvalue only if the piece is known to have that slope.
3. The companion term u·T_ℓ⁻¹ on M_{ℓ+1−k} has no derivation. At j = 1, level 6, it matches θ^{p−5}M₆ inside ker U (§4.5).
4. W = E^s versus A^{2s} beyond first order, and k = ℓ+1.
5. The transfer to s = −1, level 6 and half-integral weight, including ε.

This does not give ū₀ ≠ 0 (G5), and it does not by itself prove G4.

**Literature.** Pollack's θ-cycle examples show slopes rising by 1 along a cycle, which is the qualitative pattern here. Two searches did not find the constant u, but that is not a novelty check.

### 4.7 A proposed proof of the first term, conditional on Hodge–Newton [NOT a proof as written: see §4.9]

This supersedes items 1 and 4 of the list above. It does not address items 3 and 5 except where stated.

**Setup.** Fix a class a with 3 ≤ a ≤ ℓ+1 and an integer weight w = a + s(ℓ−1), where s may be negative. Put Fil^t = E^{s−t}·M_{a+t(ℓ−1)}, L the q-integral Katz lattice ∪_t Fil^t (completed), and gr^t = Fil^t/Fil^{t−1} mod ℓ. Basis vectors x_t = b_t E^{s−t}, with b_t in a complement of E·M_{a+(t−1)(ℓ−1)}.

**Lemma H (sharp matrix bound).** The entry of U from index j to index t has valuation at least ⌈(ℓ(t−1) + a − 1 − j)/(ℓ+1)⌉. So it is ≥ t when t + j < a, and ≥ t − 1 just past that. There is no dependence on s.

*Sketch.* Tr(f dlog q) = (Uf) dlog q for f of weight 2, and residue duality on a supersingular annulus gives |Tr η|_{ℓρ} ≤ |η|_ρ in the dlog norm. For weight w write f = V(η^{2(w−2)})·f₀. On the circle of radius ρ < 1/(ℓ+1), |E| = |A²| = ℓ^{−ρ}, so |Vη²| = ℓ^{ρ}. Converting between dt and dlog t costs ℓ^{(ℓ−1)ρ}. Together, |Uf|_{ℓρ} ≤ |f|_ρ · ℓ^{(ℓ+1−w)ρ}. Comparing with |x_t|_{ℓρ} = ℓ^{(t−s)ℓρ} and letting ρ → 1/(ℓ+1) gives the bound, s cancelling.

Not yet written carefully: the elliptic supersingular points j = 0, 1728, and the passage from circle norms to Katz coefficients for t = 0. The repo's cited form (Katz/Wan/Vonk, `AtkinOBrien/Envelope.lean`) is ⌈(ℓt − j)/(ℓ+1)⌉ − 1, which is weaker in the relevant range.

Evidence (`rc_sharp_bound.py`): no violations in about 4,000 entries over 17 pairs (a, s) at ℓ = 29, 31, 37, 41, including s = −1, 0, 1, 2. The bound is often attained. I first conjectured it without the a-term and it failed at small a. The form above was then derived and predicts the observed threshold t + j ≥ a, the independence from s, and the cutoff a ≥ 2s+2 below. It was not fitted to them, but it was found after seeing them.

**Consequences for classical weights [N].** `rc_smith_vs_newton.py`, ℓ = 29, 1 ≤ s ≤ 3, even 4 ≤ a ≤ 30: Smith form = Newton polygon in 41 of 42 weights, and both equal the Katz blocks dim gr^t whenever a ≥ 2s+2. The Smith/Newton mismatch in §4.5 concerns X, a product of two operators. For T_ℓ itself the difficulty noted there does not appear in this range.

**Hodge–Newton hypothesis HN_j(w).** The residual operators R_i(w) below are invertible on gr^i(w) for all i < j.

Given Lemma H and HN_j, the standard block argument gives a decomposition L = Λ_j ⊕ Λ^{≥j}, stable under U, with Λ_j reducing to Fil^{j−1} mod ℓ and U(Λ^{≥j}) ⊂ ℓ^j Λ^{≥j}. Define R_j := ℓ^{−j}U on Λ^{≥j} mod ℓ ≅ L̄/F̄il^{j−1}. Its image lies in gr^j, and its characteristic polynomial on gr^j is the residual polynomial of the slope-j segment. Entries with t + j ≥ a do occur in tails of Λ^{≥j}; they carry compensating powers of ℓ, but this bookkeeping still needs to be written out.

**Exact identity [P, elementary].** Let P = E₂/12, P* = P − ℓVP, R = P*/(ℓ−1), ∂_K = θ − KP, and D_K = ∂_K − KR on weight K. Then D_K ≡ θ (mod ℓ), and

U D_K = ℓ ∂_K U − ℓK U R.

*Proof.* Uθ = ℓθU and U(a·VP) = P·Ua give U∂_K = ℓ∂_K U − K U P*. Since U P* = (ℓ−1) U R, we get U D_K = U∂_K − K U R = ℓ∂_K U − K(ℓ−1) U R − K U R. ∎

Here R = (ℓ/(ℓ−1))·(P − VP) − P is a holomorphic weight-2 form of level ℓ, of index 1 in the norm sense on the canonical locus, and D_K A^{2s} = 0 (weights match since θ log A² = ℓ(P − VP)).

**Theorem (recursion).** Assume Lemma H, HN_j(w), HN_{j−1}(w−2). Put K = w − 2, W₀ = a − 2 + (j−1)(ℓ−1), and suppose ℓ ∤ W₀. Then on gr^{j−1}(K),

R_j(w) ∘ θ = c_j · θ ∘ R_{j−1}(K), c_j = (W₀ − K)/W₀ ≡ (s − j + 1)/(k + j − 1), where k = a − 2j.

*Proof.* Take y ∈ Λ^{≥j−1}(K) with class z, so Uy = ℓ^{j−1} y′. Apply the identity:

U D_K y = ℓ^j ∂_K y′ − ℓK U(Ry).

Project to Λ^{≥j}(w). By Lemma H, the projection of U(Ry) lies in ℓ^j, so the last term is ≡ 0 mod ℓ^{j+1}. Since D_K y ≡ θz, this gives R_j[θz] = [∂_K z′], where [z′] = R_{j−1}[z]. Changing z′ by F̄il^{j−2} does nothing, as ∂ preserves the index. Now z′ has filtration W₀, so ∂_{W₀} z′ ∈ F̄il^{j−1}(w), i.e. θz′ ≡ W₀ P z′ in gr^j. Therefore ∂_K z′ = θz′ − K P z′ ≡ (1 − K/W₀) θz′. Reducing mod ℓ with K ≡ a − 2 − s and W₀ ≡ a − 2 − (j − 1) gives c_j. ∎

**Corollary (first term of the law).** Under the same hypotheses for all weights w − 2i, i ≤ j, and with k + i prime to ℓ for i < j, R_j(θ^j g) = u · θ^j(T_ℓ g) for g ∈ M_k, where u = ∏_{i<j}(s−i)/(k+i) = C(s,j)/C(k+j−1,j). Induct from R₀ = T_ℓ on M̄_k. θ^j is injective on M̄_k in this range by filtration. This applies at s = −1 and at tame level N, compatibly with U₂, U₃; nothing in the argument uses s ≥ 0.

**Evidence for the recursion [N].** `rc_recursion_test.py`, on all of gr^{j−1} including the companion part: 192 non-trivial cases at ℓ = 29, 80 at ℓ = 31, none failing. The constant c_j + 1 passes none of them. `rc_weight_minus2.py`: the full law, including companions, holds directly at integer weights −2, −4, −6, level 1, in all 30 segments for ℓ = 29, 31, 37, 41 (j ≤ 2), so s = −1 no longer rests on extrapolation numerically. The recursion itself was tested only for s ≥ 1.

**The recursion does not prove the following.**
1. **HN itself.** Invertibility of R_i on all of gr^i needs the companion part, and the companion part at j = 1 has no derivation. The recursion gives c_j-scaled transfer from j−1 to j on all of gr^{j−1}, which fits the observation that the companion term has the same u at j ≥ 2 once j = 1 is known. So what remains is one case: R₁ on gr¹(w)/θM̄_k ≅ M̄_{ℓ+1−k} should be (s/k)·T_ℓ⁻¹. This is the remaining core of the law. A residue pairing involving V seems the natural tool, but it is untried.
2. **Half-integral weight.** This section works at integer weight. Transfer to X, ε, and the sign class (Ramsey's overconvergent Shimura lift, §4.5) is not done, and G4 is about Θ on K̄.
3. **Lemma H's details**, and the tail bookkeeping above.
4. **k = ℓ+1 and ℓ ∣ W₀**, the boundary and critical cases.
5. **G5**, ū₀ ≠ 0, which this does not touch.

If item 1 is settled, HN would follow by induction for every prime and class where T_ℓ is invertible on the relevant low-weight spaces, which is Buzzard's regular case. That would be a strong statement, and Buzzard-type slope conjectures are known to be hard, so a gap in this argument should be suspected first. Whether Lemma H or the recursion is already in the literature has not been checked beyond the searches above.

### 4.8 The companion term by descent from classical weight [NOT a proof as written: see §4.9]

This addresses item 1 of §4.7 at s = −1, the case the partition problem needs.

**Only vertices are needed.** The proof of the recursion in §4.7 uses just the decomposition L = Λ_j ⊕ Λ^{≥j} at weight w and at index j−1 in weight w−2. So HN can be weakened to: the Newton polygon touches the Hodge polygon at that block boundary. It need not touch at earlier boundaries. Indices are kept formal: a = k + 2j may exceed ℓ+1, and Lemma H gives the same number in formal and reduced indices.

**The chain.** Fix k + k′ = ℓ+1 and h′ ∈ M_{k′} with T_ℓ h′ = αh′, α a unit. Put z = θ^k h′ ∈ gr¹(4−k′). Here 4 − k′ = (k+2) − (ℓ−1), so s = −1. For i = 0, …, k′−2 set w_i = 4 − k′ + 2i and j_i = 1 + i. All have s = −1 with the same k. The filtration of θ^{i−1}z is W₀ ≡ k + i (mod ℓ) and K = w_i − 2 ≡ k + 1 + 2i, so

c_i = (W₀ − K)/W₀ = −(i+1)/(k+i),

and W₀ ≢ 0 for 1 ≤ i ≤ k′−2. By Wilson's theorem,

Π := ∏_{i=1}^{k′−2} c_i = (−1)^{k′}(k′−1)!·k!/(ℓ−1)! = −k.

**The endpoint is classical.** θ^{k′−2}z = θ^{ℓ−1}h′ ≡ h′ − αVh′, the reduction of the critical stabilization h_β, with U h_β = βh_β and β = ℓ^{k′−1}/α. So R_{k′−1}(k′)[h_β] = α⁻¹[h_β]. The rest of gr^{k′−1}(k′) is θ^{k′−1}M̄_k, the Bol image from weight 2−k′, where U scales exactly by ℓ^{k′−1}. There R = T_ℓ exactly.

**Conclusion.** θ^{k′−2}: gr¹(4−k′) → gr^{k′−1}(k′) is injective, since W₀ ≢ 0. So R₁(4−k′) = Π⁻¹ · (R_{k′−1}(k′) pulled back), which gives:

* on θM̄_k: −(1/k)·T_ℓ, the first term of the law with u = s/k at s = −1;
* on the quotient: −(1/k)·T_ℓ⁻¹ on M̄_{k′}, the companion term with the same u.

Combined with the recursion this is the full law at s = −1.

**A consistency check that is not numerics.** The first-term formula at s = −1, j = k′−1 gives u = ∏_{m<k′−1} (−1−m)/(k+m) = 1 by Wilson. This must hold, because θ^{k′−1} from weight 2−k′ is the Bol operator, for which the eigenvalue is exactly ℓ^{k′−1}a_ℓ. So the general formula reproduces this exact fact, which played no part in its derivation.

**Vertices, by induction on k′.** For w ≤ 2 in the chain, the vertex at j needs R_t invertible for t < j. By the recursion, R_t at weight w is conjugate to a scaled R₁ at weight w − 2(t−1), with k̃ = k + 2(j−1−t+1) > k, hence smaller k̃′. So induction on k′ applies, given T_ℓ invertible on all M_κ with κ ≤ ℓ+1 (the regular case). For w > 2 the classical part is known: by Coleman, slopes below w−1 are classical, namely the ordinary forms and the ℓ-new forms at slope (w−2)/2. This is expected to give a vertex at reduced index w−2, with the remaining indices handled as above. The vertex at w > 2 has not been written out in detail.

**Evidence [N].**
* `rc_endpoint.py`, chain at ℓ = 13, 17, 19, 23, k′ = 4, 6, 8: 41 of 43 segments reached match. The other two have one eigenvalue where two are predicted. At ℓ = 17 the second needs valuation 18 against precision 15; ℓ = 19 persisted with larger N and is presumed the same, not separately computed. Higher segments were out of reach.
* The endpoint with u = 1 is confirmed at k′ = 4 (all four primes) and k′ = 6 (ℓ = 13). It is not reached for other cases.
* The classical picture appears directly: weight 4 has slopes 0, 1, 3, with slope 1 of multiplicity dim S₄^new(Γ₀(ℓ)); weight 2 and weight 0 are crossed without any change in the pattern.
* `rc_B_operator.py`: for general s the expected form is R₁(s) = s·B with B[x] = Ū(e·x) on ker Ū, e = (E−1)/ℓ. Linearity in s follows from U(E^s x) = E^s U(Φ^s x), and R₁(0) = 0 is expected but not proved. Characteristic polynomial of B = (1/k)T_ℓ|S_k · (1/k)T_ℓ⁻¹|M_{k′}: all 12 even k with 4 ≤ k ≤ 26 at ℓ = 29, with no spare degrees.

**Status of the integer-weight law at s = −1, level 1, regular ℓ.** Everything above is a paper argument resting on: Lemma H (sketch only), Coleman's classicality theorem, the vertex bookkeeping at w > 2, and tail estimates. If those hold, the slope-j law holds in the range where the chain is valid, at small j relative to ℓ.

**In Lean (`RamanujanTau/BLBound/SlopeRecursion.lean`).** For arbitrary power series, with the three standard axioms: `U_bracket_expand`, `U_serreD`, `serreD_sub_theta`, `serreD_mul_flat`, `serre_filtration`, `bol_product`, `chain_product`, and `recursion_step`. The last takes the consequence of Lemma H as an explicit hypothesis on the projection π. The products need no Wilson's theorem: with k + n = ℓ, reversing the order gives k + m ≡ −1 − (n−1−m). Not in Lean: Lemma H, the slope decomposition, the classical endpoint, Coleman's theorem, the vertices, so none of the conclusions of §4.7–4.8 are machine-checked.

**Not addressed.** Half-integral weight, ε and the sign class (so G4 is not proved); level 6, where the argument should apply on Atkin–Lehner eigenspaces but has not been checked; s ≠ −1 for the companion term beyond the linearity above; ℓ dividing a_ℓ of a low-weight form, where the mechanism predicts merging rather than the law; G5.

### 4.9 Corrections from an independent read, and the known case j = 1

An independent read of §4.6–4.8 (by another AI instance, not a human expert) found the following. Items 1, 3 and 5 I confirmed directly; items 2 and 4, and the repair in item 1, are its derivations and I have not rechecked them.

1. **The decomposition in §4.7 is false on the stated lattice.** U∘V = id, so U is surjective on the q-integral lattice L, while L = Λ_j ⊕ Λ^{≥j} with U(Λ^{≥j}) ⊂ ℓ^j Λ^{≥j} would force U(L) ⊂ Λ_j + ℓ^j Λ^{≥j}. So R_j is not defined on L̄/F̄il^{j−1}, and classes mod ℓ do not determine it: "tail bookkeeping" was the central issue, not a detail. Proposed repair: the lattice with v(c_r) ≥ (ℓ/(ℓ+1))(r − J) for r > J = k + j − 2, on which U is reported stable exactly for k ≥ 3, tails die under R_j, and ∂_K, D_K, and multiplication by R map the (K, j−1) lattice to the (w, j) lattice. R_j then lives on Fil^J/Fil^{j−1}. **The recursion is therefore unproved until this is written out.**
2. **Vertices at w > 2 are the second real gap.** The chain needs vertices at or above the critical slope, where Coleman says nothing, and "R_t conjugate to R₁" fails below critical since R_t does not exist on the plateau. Proposed route: the classical count gives the vertex at formal index w−1 (§4.8's "reduced index w−2" appears mis-indexed); t = w−1 from Hida, Bol and critical forms; t > w−1 by recursion. Hodge and Newton counts at that vertex reportedly match for 13 ≤ ℓ < 200. Smith = Hodge at the vertex still needs proof, and depends on item 1.
3. **gr¹/θM̄_k ≅ M̄_{k′} is false.** θE_k ∝ θ^k E_{k′} (from nσ_{k−1}(n) ≡ n^k σ_{k′−1}(n)), so the count is off by one; the correct count is dim gr¹ = dim S_k + dim M_{k′}. There are further deficits at k = k′ = (ℓ+1)/2 (ℓ = 23, 31, 47, 59, 71, 79, 83 in a partial scan, reportedly of size (h(−ℓ)−1)/2, read as dihedral self-companions such as Δ at ℓ = 23). So eigenvector statements fail and only characteristic polynomials should be claimed, obtained by counting slope k′−1 in characteristic 0 at weight k′, then using injectivity of θ^{k′−2} and equal dimensions.
4. **Projection step in §4.7.** Bounding rows t ≥ j of U(Ry) is not enough. Rows t < j must be divisible by ℓ^t, so that the low part does not feed the high projection through the graph map of Λ_j.
5. **Scope.** "Full law at s = −1" means at most j ≤ k′−1, since ℓ ∣ W₀ at j = k′. So `chain_product` and `bol_product` are correct but cover only that range.

The same read found Lemma H's norm accounting sound as a sketch, with t = 0 vacuous and elliptic points handled by passing to Γ₁(N), re-derived the exact identity, Π = −k and the θ-cycle filtrations, and found no contradiction with irregular primes, weight 2 or the data. The Lean theorems are unaffected: `recursion_step` takes its key input as a hypothesis, and nothing in Lean depends on the false decomposition.

**j = 1 is known in Galois form.** Bhattacharya–Ghate–Rozensztajn, *Reductions of Galois representations of slope 1* (arXiv:1504.03838), Theorem 1.1 (read directly): for p > 3, k ≥ 2p + 2, r = k − 2 ≡ b mod (p−1), v(a_p) = 1 and 3 ≤ b ≤ p−1, the reduction is μ_λ ω^b ⊕ μ_{λ⁻¹} ω with λ = (b/(b−r))·(a_p/p) if p ∤ r − b, and irreducible if p ∣ r − b. With b = k and b − r ≡ s this reads a_ℓ/ℓ ≡ (s/k)·λ, which is the constant u at j = 1. Both terms of the law fit: λ = a_ℓ(g) for g of weight k, and λ = 1/α for h′ of weight k′, since ω^k ⊗ ρ̄_{h′} has that shape. p ∣ r − b is u = 0, and the b = 2 trichotomy there is the likely explanation of the misses at k ≡ 2 in §4.6. So **u at j = 1, classical weights, is not new.** That theorem is local and covers classical k ≥ 2p + 2, so it says nothing directly about s < 0 or about multiplicities. Its introduction says that, as far as those authors knew, the shape was not known at other positive integral slopes for all weights (the paper is from 2015–2018; later work was not surveyed). Related, as reported and not read by me: Liu–Truong–Xiao–Zhao, arXiv:2302.07697, Thm 1.3 (slopes, p ≥ 11, 2 ≤ a ≤ p−5, r̄ absolutely irreducible), which may discharge vertices; Ghate–Kumar, arXiv:1906.10364; Bergdall–Pollack, arXiv:2110.07973. Whether u at j ≥ 2 is known remains open after only a few searches.

### 4.10 The repaired argument at s = −1, level 1 [paper proof, no human expert review; not in Lean except where stated]

This replaces §4.7–4.8 in the setting below. It answers items 1, 2, 3 and 4 of §4.9. One independent AI read of this section found three errors, which are repaired in the text below and listed at the end.

**Theorem (slope law, s = −1).** Let ℓ ≥ 5 be a regular prime (T_ℓ invertible mod ℓ on M_κ(SL₂(ℤ)) for all κ ≤ ℓ+1). Let k ≥ 4 and k′ ≥ 2 be even with k + k′ = ℓ+1, let 1 ≤ j ≤ k′−1, and put w = k + 2j − (ℓ−1). Then U on overconvergent forms of tame level 1 and weight w has exactly dim S_k + dim M_{k′} slopes equal to j, and the residual characteristic polynomial of that segment is that of

u·T_ℓ on S_k, together with u·T_ℓ⁻¹ on M_{k′}, where u = ∏_{i<j} (−1−i)/(k+i).

**Notation.** a = k + 2j, formal index r, x_r = b_r E^{s−r} with b_r in a complement of E·M_{a+(r−1)(ℓ−1)} in M_{a+r(ℓ−1)}. O = ℤ_ℓ[π], π^{ℓ+1} = ℓ, with v normalized by v(ℓ) = 1.

**Step 0: Katz norms.** For 0 < ρ < ℓ/(ℓ+1) and a ≥ 2, integral sections on the formal model of X_ρ are exactly Σ g_t (π_ρ/E)^t with g_t of weight a + t(ℓ−1) (Katz §2; vanishing of H¹ after adding Γ₁(N) structure and averaging). So for f = E^s Σ c_t b_t E^{−t}, one has ‖f E^{−s}‖_ρ = max_t |c_t| ℓ^{tρ}.

**Step 1: Lemma H.** For ρ < 1/(ℓ+1) and η = g dt/t on a circle of radius ρ in a supersingular annulus, let Φ be the canonical quotient map, of degree ℓ and with v(Φ*t) = ℓ v(t). The nth coefficient of Tr η is Res(Φ*(t^{−n}) η), so |Tr η|_{ℓρ} ≤ |η|_ρ in the dlog norm. Tr(f dlog q) = (Uf) dlog q in weight 2. Kodaira–Spencer turns a weight-2 form f into f̃ dt with |f̃| = |f|, which costs |t|_ρ = ℓ^{−ρ} in the dlog norm. Hence |Uf|_{ℓρ} ≤ |f|_ρ ℓ^{(ℓ−1)ρ}. In weight w write f = V(h)·f₀ on each supersingular disc, with h a local power of a 12th root of Δ, which is a unit of norm 1 there, and use U(Vh·f₀) = h·Uf₀ and |Vη²|_ρ = 1/|A²|_ρ = ℓ^{ρ}. (Globally, work at level Γ(12).) Then |Uf|_{ℓρ} ≤ |f|_ρ ℓ^{(ℓ+1−w)ρ} on the supersingular circles. The Shilov boundary of X_{ℓρ} also contains the ordinary component, where the only bound is |U x_r E^{−s}| ≤ 1. So with Step 0, the entry M_{tr} of U satisfies

v(M_{tr}) ≥ min(tℓ, ℓ(t−1) + a − 1 − r)/(ℓ+1), and M_{tr} is integral.

Write μ(t,r) = (ℓ(t−1) + a − 1 − r)/(ℓ+1). The minimum is μ when a ≤ ℓ+1+r. It cannot be dropped: row 0 holds the ordinary part, and M₀₀ is a unit at ℓ = 13, a = 20, where μ = 3/7. So the form of Lemma H in §4.7 is false in row 0 for a > ℓ+1+r. Since tℓ/(ℓ+1) > t−1 for t ≤ ℓ and j < ℓ, the branch tℓ/(ℓ+1) rounds up to at least t, and all of Step 3 survives it.

**Step 2: Decay of R (new).** 12(ℓ−1)R dlog q = dlog(Δ/VΔ), since θ log Δ = 12P and θ log VΔ = 12ℓVP. So R dlog q is the logarithmic differential of a modular unit on X₀(ℓ). On a supersingular annulus such a unit is c·t^m(1+h) with |h| < 1, so its dlog has dlog norm ≤ 1, and |R|_ρ ≤ ℓ^{ρ} for every ρ < ℓ/(ℓ+1). By Step 0 the Katz coefficients of R in class 2 satisfy v(ρ_t) ≥ (ℓ/(ℓ+1))(t−1), and they are integral by the q-expansion principle. This is checked at ℓ = 13, 17, 23, 29 for t ≤ 10 (`rc_tail_lattice.py`, T1); the bound is sharp at t = 1, where ρ₁ is a unit since R ≡ −E_{ℓ+1}/12.

**Step 3: The lattice.** Put J = k + j − 2, fix c′ with (ℓ−1)/(ℓ+1) < c′ < ℓ/(ℓ+1), and put λ(r) = c′·max(r−J, 0), and 𝓛(a,j) = {Σ c_r x_r : c_r ∈ O, v(c_r) ≥ λ(r), v(c_r) − λ(r) → ∞}, over a ramified O containing the needed powers. c′ = ℓ/(ℓ+1) must not be used: scaled columns of U then do not tend to 0, since there is no canonical subgroup at that radius. With c′ below it, 𝓛 is essentially the Banach space of radius c′, and U is compact with Coleman's Fredholm series. 𝓛 does not depend on the complements. Substitution in the bound of Step 1, using that M_{tr} is integral to round up, gives, for k ≥ 3, in the scaled entries M_{tr}·ℓ^{λ(r)−λ(t)}:

* rows t < j: valuation ≥ t in columns r ≤ J, and > t in tail columns r > J;
* rows t ≥ j: valuation ≥ j;
* rows t > j and tail rows: valuation > j. For tail rows and r ≤ J this reads ℓ(J−1−j) + 1 > 0, that is k ≥ 3;
* row j, tail columns r = J+n: > j. Here μ = j − (ℓ−1+n)/(ℓ+1). At n = 1, integrality gives v ≥ j, so v + λ ≥ j + c′. At n ≥ 2, μ + c′n > j because 2c′ > 1. Low rows t < j in tail columns have margin (j−t)/(ℓ+1) − (ℓ/(ℓ+1) − c′) > 0 at n = 1, which is what forces c′ > (ℓ−1)/(ℓ+1).

So in blocks (low: r < j; high: r ≥ j), U = [[ΔA′, ΔB′], [ℓ^jC′, ℓ^jD′]] with Δ = diag(ℓ^t) and integral A′, B′, C′, D′.

**Step 4: Vertices are a Newton-polygon condition.** Put d = dim Fil^{j−1}, H = Σ_{t<j} t·dim gr^t. Every principal d-minor of U other than det(ΔA′) has a high row in place of a low one, so it has valuation > H. Hence

v(c_d) = H ⟺ A′ is invertible mod π,

where c_d is the Fredholm coefficient. Call this condition V(w,j). It says only that the Newton polygon of weight w passes through (d, H).

**Step 5: Decomposition.** Assume V(w,j). The equation A′G + B′ = ℓ^jΔ⁻¹G(C′G + D′) is a contraction, because ℓ^jΔ⁻¹ ≡ 0 mod ℓ. So it has a unique integral solution G, and Λ^{≥j} = graph(G: high → low) is U-stable with U = ℓ^jN on it, where N ≡ D′ − C′A′⁻¹B′ mod π. Likewise Λ_j = graph(G′: low → high), with G′ ≡ 0 mod π, is stable with slopes ≤ j−1. Then 𝓛 = Λ_j ⊕ Λ^{≥j}, which is what fails on the q-integral lattice (§4.9, item 1). Define R_j = N mod π. By Step 3 it lands in row j and kills tail columns, so it is a map F̄il^J/F̄il^{j−1} → gr^j of reductions as q-series (E ≡ 1). The unit part of its gr^j → gr^j block is the residual polynomial of the slope-j segment. The low rows enter only through the Schur complement, which is item 4 of §4.9.

**Step 6: Recursion.** Suppose V(w,j) and V(w−2,j−1), ℓ ∤ W₀ = a − 2 + (j−1)(ℓ−1), and put K = w−2. Then on F̄il^{J−1}(K)/F̄il^{j−2},

R_j[θz] = c_j [θ R_{j−1} z], c_j = (s−j+1)/(k+j−1).

*Proof.* (K, j−1) has the same k and J−1 in place of J. So ∂_K, which raises the index by 1 and is integral, maps 𝓛(a−2,j−1) into 𝓛(a,j). Multiplication by R does too: index r goes to r+t with coefficient of valuation ≥ (ℓ/(ℓ+1))(t−1) by Step 2, and λ_w(r+t) ≤ λ_K(r) + c′·max(t−1, 0), with room to spare since c′ < ℓ/(ℓ+1). For y ∈ Λ^{≥j−1}(K) with Uy = ℓ^{j−1}y′, the exact identity gives

U D_K y = ℓ^j ∂_K y′ − ℓK U(Ry).

Apply the projection p to Λ^{≥j}(w), which commutes with U. Since U = ℓ^jN there, p U(Ry) = ℓ^j N p(Ry). Dividing by ℓ^j,

N p D_K y = p ∂_K y′ − ℓK N p(Ry),

so N p D_K y ≡ p ∂_K y′ mod ℓ. Now D_K y ≡ θy as q-series, because P + R = (ℓ/(ℓ−1))(P − VP). Two elements of 𝓛 with equal q-expansions mod π differ by tails, which R_j kills. The class of y′ lies in F̄il^{j−1}(K), so as a q-series it is z′ ∈ M̄_{W₀}. Since ∂_{W₀} z′ ∈ F̄il^{j−1}(w), we get θz′ ≡ W₀Pz′ in gr^j, and ∂_K z′ ≡ (1 − K/W₀)θz′ as in §4.7. ∎

Neither the bound on low rows nor a separate estimate of U(Ry) is needed: it is enough that Ry ∈ 𝓛(a,j).

**Step 7: Dimensions.** `rc_vertex_counts.py` also tests these directly at all primes 13 ≤ ℓ < 400, with no failures:

* D1 (867,444 cases): dim gr^{j−1}(a−2) = dim gr^j(a) for 2 ≤ j ≤ k′−1. With ℓ ∤ W₀ and Jochnowitz's w(θf) = w(f) + ℓ + 1, θ: gr^{j−1}(a−2) → gr^j(a) is an isomorphism;
* D2 (6,820 cases): dim gr^{k′−1}(a) = dim S_k + dim M_{k′} at w = k′;
* D3 (433,722 cases): for w > 2 the list below (zeros for M_w, (w−2)/2 for S_w^new(Γ₀(ℓ)), w−1 for S_w, t + w − 1 for the part of class ℓ+1−w below j″ = j−w+1) has count d and height H at formal index j;
* D4 (440,542 cases): dim gr^t(a) = dim S_{a−2t} + dim M_{ℓ+1−a+2t}.

Proofs: D1, D2 and D4 are `gr_succ_eq`, `gr_law` in `RamanujanTau/BLBound/SlopeCounts.lean`, for every prime ℓ ≥ 5 (standard axioms only, not yet wired into the build). D3 follows by induction on j″. Going from j″ to j″+1 for j″ ≥ 1 adds gr^j(a) on the Hodge side and gr^{j″}(a″) on the other, and these agree by D1 since a − a″ = 2(j − j″) (their heights both carry the factor j = j″ + w − 1). Going from j″ = 0 to 1 is `gr_law` with dim S_w + dim M_k. The base j″ = 0 reads dim M_{a+(j−1)(ℓ−1)} = dim M_w + dim S_w^new(Γ₀(ℓ)) and Σ_{1≤t≤w−2} t·gr^t(a) = ((w−2)/2)·dim S_w^new(Γ₀(ℓ)). On each class of (ℓ mod 12, w mod 12) both sides are polynomial, of degree ≤ 1 in ℓ and ≤ 2 in w. So the check `rc_vertex_base.py`, over a grid with at least 33 values of ℓ and 16 of w in each of the 24 classes (12,936 points, no failures), is a proof.

**Step 8: The induction.** Induct on k′. Assume the Theorem, with V(w_t, t) and V(w_t, t+1) at index t, for every larger k.

*Vertices with a ≤ ℓ+1 (w ≤ 2).* V(w,1) is regularity. For j ≥ 2, V(w,j) is V(w,(j−1)+1) for k̃ = k+2 > k, which the induction hypothesis supplies (t = j−1 satisfies t ≤ k̃′−1 since 2j ≤ k′).

*Vertices with a > ℓ+1 (w > 2).* Coleman: char series of U on M_w^† is that of ℓ^{w−1}U on M_{2−w}^† times the classical factors: zeros for M_w, slope (w−2)/2 for S_w^new(Γ₀(ℓ)), and slope w−1 for S_w (regularity is used for the first and third). Bol preserves k: (w, j) goes to (2−w, j″), with j″ = j−w+1 ≥ 0 exactly when j ≤ k′−1, a″ = ℓ+1−w = k + 2j″ and the same k. V(2−w, j″) is the previous case, and D3 then gives V(w,j).

*Chain.* By Step 6 and D1, for 2 ≤ j ≤ k′−1, R_j|gr^j(w_j) = c_j θ R_{j−1}|gr^{j−1}(w_{j−1}) θ⁻¹, with c_j = −j/(k+j−1) ≠ 0.

*Endpoint, k′ ≥ 4.* At j = k′−1, w = k′ the slope k′−1 part is the critical stabilizations of S_{k′}, with residual α⁻¹, and the Bol image of the ordinary part of weight 2−k′ in class k, with residual T_ℓ on M̄_k. That is dim S_{k′} + dim M_k = dim S_k + dim M_{k′} = dim gr^{k′−1} by D2. So the block is invertible, with the stated charpoly and u = 1 by Wilson (`bol_product`). Only characteristic polynomials are claimed, so the Eisenstein coincidence and the dihedral self-companions in §4.9, item 3 do not matter.

*Endpoint, k′ = 2.* Here k = ℓ−1, w = 2, j = 1, and the count above is wrong: θ on M_0^† kills the constant 1, which is the Eisenstein member of the ordinary part in class ℓ−1. Slope 0 is S₂(Γ₀(ℓ)) with E₂*, of multiplicity dim M_{ℓ+1} (V(2,1)), and slope 1 is the θ-image of the ordinary part modulo constants, of multiplicity dim S_{ℓ−1} = dim gr¹ and residual T_ℓ on S_{ℓ−1}. Since u = −1/(ℓ−1) ≡ 1, this is the law. At w > 2, θ^{w−1} is injective, so this occurs only here.

*Descent.* Dividing by ∏c_i gives the law at every 1 ≤ j ≤ k′−1. In particular R_j is invertible, which by the Schur determinant gives invertibility of the next A′, that is V(w_j, j+1) when k ≥ 6. (At k = 4 the next index has k = 2, where Steps 3 and 4 do not apply; the induction uses only k̃ ≥ 6 there, so nothing is lost.) ∎

**Evidence on actual matrices.** `rc_chain_sweep.py`, every even k and 1 ≤ j ≤ k′−1 at ℓ = 13, 17, 19, 23, weights above 2 included: the vertex holds and the charpoly of R_j|gr^j equals the law in all 220 cases reached, and the recursion holds in all 2,734 tests on the whole of F̄il^{J−1}, tails of the filtration included (2,440 non-trivial; the wrong constant c_j + 1 passes none). No block violates Step 3 in this test, which was run at c′ = ℓ/(ℓ+1) on truncated matrices, not at a c′ below it. 18 high-j cases at ℓ = 19, 23 exceed the script's precision and were skipped. The reader's separate code confirms the law in every (k, j) at ℓ = 5, 7, 11, 13, 17, 19 (159 cases), and at k = k′ = 12, ℓ = 23 (11 more).

**Inputs taken from the literature.** Katz's description of integral overconvergent sections (Step 0); the Katz–Lubin canonical subgroup, for the degree and radius of Φ; A² as a lift of the Hasse invariant up to ρ < ℓ/(ℓ+1); Coleman's control theorem and the Bol factorization, including tame level 1 via Γ₁(N); Jochnowitz's filtration rule.

**The independent read.** Errors it found, all repaired above: Lemma H fails in row 0 for a > ℓ+1+r (the ordinary component had been ignored); the endpoint count fails at k′ = 2; the lattice with c′ = ℓ/(ℓ+1) appears not to be U-stable (numerics plus a structural reason). It re-derived Steps 0–6 and the logic of Step 8 and found them correct, and tested the slope multiplicities against its own implementation of the ghost series for all primes 11 ≤ ℓ < 120 (28,349 cases, no mismatch, after fixing a zero convention at weight 2 once it had seen the result, unchecked against Bergdall–Pollack). It read none of the cited papers, and neither have I at the level of exact statements. Still to pin down against the sources: Coleman at tame level 1 for M^† including Eisenstein series, Hida control at negative weight, and the Γ₁(N) or X(N) reduction in Step 0 (Γ₁(N) is not normal in SL₂(ℤ), so use a trace of index prime to ℓ or X(N)).

**Scope.** Level 1 and s = −1 only, regular ℓ, and only the first k′−1 slopes for each k. It says nothing at j ≥ k′ (ℓ ∣ W₀ there). No level 6, no half-integral weight, no ε, so **it does not yet prove G4 or G5**. The same steps should apply on Atkin–Lehner eigenspaces at level 6, but D1–D4 and the classical list must be redone there.

---------------------------------------------------------------------------------------------------------

### 4.11 G4: Θ is invertible unless ℓ ∣ a_ℓ(h₈) [paper proof, no human expert review; supporting Lean links listed below]

**Theorem.** Let ℓ ≥ 13 be prime and h₈ = 6.8.a.a = q + 8q² + 27q³ + ⋯. If ℓ ∤ a_ℓ(h₈), then Θ is invertible on K̄ (§4.2).

No prime ℓ with ℓ ∣ a_ℓ(h₈) exists below 60000 (`nonordinary_wt8.gp`). Together with §4.2 this gives: for such ℓ, **b_ℓ(m) = 2m−1 for all m ⟺ ū₀ ≠ 0**. So the lower bound for the partition function at ℓ reduces to one explicit non-vanishing, G5, and that one remains open. Since `bstab.py` and `bigstab.py` found b_ℓ(m) = 2m−1 at m ≥ 2 for all 41 primes 29 ≤ ℓ ≤ 229 (§4.2), which gives ū₀ ≠ 0 there, this theorem would extend b_ℓ(m) = 2m−1 to every m at those primes.

This argument does not use §4.10, Coleman, the slope decomposition, or an overconvergent Shimura lift. It uses only classical weights and q-series. Write k = ℓ−5, a = ℓ−3, E = E_{ℓ−1} = 1 + ℓe₁, λ = ℓ−2, and M̄_κ = M_κ(Γ₀(6)) mod ℓ as q-series.

**Step 1: The lift.** For t ≡ −1 (mod 24) squarefree, and a series with coordinates A[m] = a(24m−1), put

Sh_t^{(λ)}(A) = Σ_n Σ_{de=n} (d/t) d^{λ−1} χ₁₂(e) a(te²) qⁿ (`ThetaLift.genLift`, j = 1).

* For a classical form of weight λ + 1/2, this is modular of weight 2λ on Γ₀(6) (`ThetaLift.gen_modular`).
* Since χ₁₂(e) = 0 for gcd(e, 6) > 1, every term of the coefficient at qn (q = 2, 3) has q ∣ d. So U_q Sh_t = (q/t) q^{λ−1} Sh_t exactly, and (2/t) = (3/t) = 1. This settles the bad-prime eigenvalues listed as missing in §4.5.
* Formally, on any series, Sh_t(a)[ℓn] = ε·Sh_t(U_{ℓ²}a)[n] + (ℓ/t) ℓ^{λ−1} Σ_{d′e=n, ℓ∤e} ψ(d′)χ₁₂(e)a(te²), with ε = χ₁₂(ℓ) = (12/ℓ) and ψ(d) = (d/t)d^{λ−1}. This covers ℓ ∣ t too: then (ℓ/t) = 0 and a(te²) ≡ 0 on K̄, so such t contribute Sh_t(g) ≡ 0 harmlessly.
* If Sh_t(a) ≡ 0 for all t, then a ≡ 0: every index 24m−1 is uniquely te² with t squarefree, and the term d = 1 has coefficient 1, so induction on n gives a(te²) ≡ 0 (for gcd(e, 6) = 1, which is all that occurs).
* If U_ℓ a ≡ 0 then U_ℓ Sh_t(a) ≡ 0 (`ThetaLift.genLift_U_dvd`).

**Step 2: The structure of ker Ū (Claim K).** For ℓ ≥ 13, in the class (U₂, U₃) = (1/4, 1/9), ker(Ū | M̄_{2ℓ−4}) = θ(M̄_k) in the class (1/8, 1/27).

State this for joint eigenvectors. Its only use is for f̄, which is an exact eigenvector.

*Proof.* On X = X₀(6) ≅ P¹ over 𝔽_ℓ (no elliptic points, including in characteristic ℓ) put L = ω^k. θ: L → ω^{k+ℓ+1} = L ⊗ Ω¹(log(C + SS)) is a log connection: Ω¹(log C) = ω², ω^{ℓ−1} = O(SS) via the Hasse invariant. At a supersingular point it has residue ±k ≡ ∓5 ≠ 0 mod ℓ. Locally at SS, t^i e ↦ (i+r)t^i e dt/t, with kernel the orders ≡ 5 mod ℓ, and the log Cartier isomorphism gives im θ = ker U as sheaves. The kernel sheaf is 𝓕 = {h^ℓ Ā⁵ : h a section of ω^{−4}}, since k = ℓ·(−4) + 5(ℓ−1). So

0 → 𝓕 → L → ker U → 0,

and with H⁰(𝓕) = 0 and H¹(L) = 0,

ker Ū / θM̄_k ≅ H¹(X, ω^{−4}),

of dimension 3. By Serre duality, with Ω¹ = ω²(−C), it is dual to S₆(Γ₀(6)). Hecke action: U_q(h^ℓ Ā⁵) = (U_q h)^ℓ Ā⁵ on 𝓕, and U_q θ = q θ U_q on the connecting map, so U_q acts on the quotient as q·U_q on H¹(ω^{−4}). That has the eigenvalues of q⁻⁵·(adjoint of U_q on S₆), which has the same characteristic polynomial as U_q. In total U_q acts on the quotient with the eigenvalues of q⁻⁴ U_q on S₆(Γ₀(6)). The eigenpairs on S₆(Γ₀(6)) are (4, −9) and (α, 9) with α² + 6α + 32 = 0, by the operator polynomial of §3.2. The class (1/4, 1/9) would need the pair (4, 9) mod ℓ, which forces 18 ≡ 0 or 72 ≡ 0. So the quotient has no such part. ∎

The sequence continues as 0 → 𝓕 → L → L⊗Ω¹(log) → ω^{ℓ−3} → 0, with last map Ū, so Ū is surjective and ker Ū has dimension ℓ−1. Hecke action, to be written out in full: U_q is a correspondence through X₀(6q) whose projections ramify only at cusps, the isogeny pullback is invertible on ω, and Ā is isogeny-invariant. The identification with H¹ is ℓ-semilinear, which leaves characteristic polynomials over 𝔽_ℓ unchanged. This explains the measurements in §4.5, including ℓ = 67: the quotient always has dimension 3 and the stated eigenvalues, while the map θ^{ℓ−5}: S₆ → ker Ū/θM̄_k need not be injective. The reader's own computation at 16 primes 13 ≤ ℓ ≤ 97, ℓ = 67 included, confirms rank Ū = ℓ−2, quotient dimension 3, charpoly(U₂) = (x−¼)(x²+⅜x+⅛), charpoly(U₃) = (x+1/9)(x−1/9)², and rejects the alternative normalization.

**Step 3: The contraction identity.** Let z ∈ M̄_k and let z̃ be a lift, s ∈ {1, 3}, y = z̃ E^s of weight K = k + s(ℓ−1), w = K + 2. If F is a classical form of weight w with q-series F ≡ θz (mod ℓ), then

(UF)/ℓ ≡ (s/k)·θ(Ūz) (mod M̄_{ℓ−3}). (★)

*Proof.* Put F′ = −[z̃, E^s]₁/(s(ℓ−1)) = E^s θz̃ − (k/(ℓ−1)) z̃ E^{s−1} θE. It is classical of weight w and ℓ-integral (clear denominators prime to ℓ), and F′ ≡ θz̃ + ℓ(s·e₁θz̃ + k·z̃θe₁) mod ℓ². Using Uθ = ℓθU, θe₁ ≡ P − VP and U(a·Vb) = b·Ua,

UF′/ℓ ≡ ∂_kŪz − Ū∂_kz + s·Ū(e₁θz).

Also Ū(e₁θz) = −Ū(zθe₁), since Ūθ ≡ 0, and Ū(zθe₁) = Ū(zP) − PŪz gives Ū(e₁θz) = (1/k)(θŪz − ∂_kŪz + Ū∂_kz). So UF′/ℓ ≡ (s/k)θŪz + (1 − s/k)(∂_kŪz − Ū∂_kz). The second bracket lies in M̄_{k+2} = M̄_{ℓ−3}, because ∂_kŪz ∈ M̄_{k+2} and Ū∂_kz ∈ M̄_{k+2}, by Ū(M̄_{ℓ−3}) ⊂ M̄_{ℓ−3}. For general F, (F − F′)/ℓ is a classical form of weight w with ℓ-integral coefficients, and Serre's bound w(Uf) ≤ ℓ + (w−1)/ℓ < 2ℓ−4, with the congruence of filtrations mod ℓ−1, puts its Ū-image in M̄_{ℓ−3}. ∎

This extends `BLBound.rc_lift` from s = 1 to every s, and makes §4.11 independent of §4.10: neither Lemma H nor the decay of R is used, and these were stated only at level 1.

**Step 4: Linearity in s.** Let g ∈ 𝒯̄ with ū = ηg ∈ K̄, so U_ℓ g ≡ 0, with lift g̃ = ũ/η. Put λ_m = λ + m(ℓ−1), and F_{(m)} = Sh_t^{(λ_m)}(g̃ E^m), classical of weight w_m = 2ℓ−4 + 2m(ℓ−1), s = 1 + 2m. Then modulo ℓ², with d^{m(ℓ−1)} ≡ 1 + mℓ·q_ℓ(d) for ℓ ∤ d (Fermat quotient), and terms with ℓ ∣ d vanish,

F_{(m)} ≡ F_{(0)} + mℓ·Ψ, Ψ = Sh_t(e₁ g) + Fer, Fer = Σ_{de=n} q_ℓ(d)(d/t) d^{λ−1} χ₁₂(e) a(te²) qⁿ.

The coefficient of Fer at ℓn has either ℓ ∣ e, so a(tℓ²e′²) ≡ 0 because U_{ℓ²}g ≡ 0, or ℓ ∣ d, which has been dropped. So Ū Fer ≡ 0. Hence, up to the unit ε of Step 1,

U F_{(m)}/ℓ ≡ U F_{(0)}/ℓ + m Ū Sh_t(e₁ g).

**Step 5: The theorem.** Suppose Θū = 0 with ū ≠ 0, and put w̄ = ρ(U_{ℓ²}g̃/ℓ − U_{ℓ²}(e₁g̃)), as in §4.2 item 5. Fix t, and put f̄ = Sh_t^{(λ)}(g), which lies in ker Ū in the class (1/4, 1/9) by Step 1. By Claim K, f̄ = θz with z ∈ M̄_k. Since θ is injective on M̄_k (k < ℓ) and U_qθ = qθU_q, and f̄ is an exact eigenvector, z is an exact eigenvector, U₂z = z/8 and U₃z = z/27. Apply (★) to F_{(0)} (s = 1) and F_{(1)} (s = 3). Both have F ≡ f̄ = θz, since the weights agree mod ℓ−1 and E ≡ 1. Subtracting, by Step 4,

Ū Sh_t(e₁g) ≡ (2/k) θŪz (mod M̄_{ℓ−3}).

So by Step 1,

Sh_t(w̄) ≡ ε[(1/k) − (2/k)] θŪz = −(ε/k) θŪz ≡ (ε/5) θŪz (mod M̄_{ℓ−3}). (★★)

On the other hand, Θū = 0 means w̄ ∈ Ū(V) in 𝒯̄-coordinates. X̄ is invertible on V (Theorem A), so w̄ = U_{ℓ²} w′ with w′ ∈ 𝒯̄, and Sh_t(w̄) = ε Ū Sh_t(w′) ∈ Ū(M̄_{2ℓ−4}) ⊂ M̄_{ℓ−3}. (Ū(M̄_{2ℓ−4}) ⊂ M̄_{ℓ−3} is Serre's bound.) Thus θŪz ∈ M̄_{ℓ−3}. If Ūz ≠ 0, it has filtration k″ ≤ k < ℓ, so θŪz has filtration k″ + ℓ + 1 > ℓ−3, a contradiction. So Ūz = 0. If z ≠ 0, then z is a nonzero element of weight ℓ−5 in the class (1/8, 1/27) with Ūz = 0, and `TheoremA.dvd_coeff_hEight_of_binary_kernel` gives ℓ ∣ a_ℓ(h₈), which is excluded. So z = 0 and f̄ = 0. This holds for every t, so g = 0 by Step 1, contradicting ū ≠ 0. ∎

**Consequence.** (★★) and the filtration argument give the exact intertwining z_t(Θg) = (ε/5)·Ū z_t(g). So Θ is (ε/5)Ū transported into weight ℓ−5.

**Direct tests.**
* `rc_theta_sh.py`, which builds ū ∈ K̄, the lift and w̄ from actual series, and solves for c in Sh_t(w̄) ≡ c θŪz: at ℓ = 29, 31, 37, 41, 43, t = 23, f̄ ∈ θ(M̄_{ℓ−5}), θŪz ≢ 0 mod M̄_{ℓ−3}, and c = ε/5 in all five, as predicted before the runs.
* An independent read, with its own code sharing nothing with that script, at every prime 29 ≤ ℓ ≤ 151 with t = 23, 47, 71, 95 (fewer t at ℓ ≤ 37): w̄ in 𝒯̄, f̄ ∈ θM̄_k, z exact in the class (1/8, 1/27), (★★), the intertwining, dim class = dim K̄, charpoly Θ = charpoly (ε/5)Ū, no failures. det Θ agrees with §4.3. (★) directly for random z and F at ℓ = 13, 17, 29, s = 1, 3, with a wrong constant failing. Step 4 on series at ℓ = 29. No ℓ ∣ a_ℓ(h₈) below 60001.

**Status of the proof.** One independent AI read found no mathematical error, and suggested the elementary Step 3 above. No human expert has read it. The Katz, Jochnowitz and Serre inputs were not checked against the sources at the level of exact statements; the log-Cartier step in Claim K rests on a derivation plus numerics. Theorem A's paper form, Yang and the §4.0–4.1 machinery are taken as given, and lift-independence of Θ (§4.2 item 3) was not reproved in that read.

**In Lean.** Have: `gen_modular`, `genLift_U_dvd`, `U_serreD`, `rc_lift` (s = 1), `dvd_coeff_hEight_of_binary_kernel` with `binaryRep_of_reduced_modularForm`, and Theorem A. Not in Lean: the ε identity, U₂/U₃ eigenvalues and injectivity for `genLift` (an analogue exists for `liftSeries`: `U_lift`, `psi_two_eq`); (★) for general s; Step 4; Claim K; the assembly. Θ is not yet defined in Lean in the form used here.

**Not addressed.** G5 (ū₀ ≠ 0).

### 4.12 Certified data and the remaining gaps (2026-11-03) [L for the per-prime results; N for the patterns]

**Proved in Lean, per prime.** b_ℓ(m) = 2m−1 for every m at every prime 29 ≤ ℓ ≤ 139
(`Exact29`, `Exact31`, `Rank2At*`, `RankSAt*`, `RankRAt*`), by the finite route of RESULTS: a recurrence of
order r = d − s on the odd chain, s observations, the error vector moved by Θ. Each file checks the
finite hypotheses of the generic theorem `RankR.Data2.bEll_eq`.

**Patterns on the certified tables [N, PARI].**
* charpoly(Θ) = charpoly((12/ℓ)/5 · T_ℓ on S^new_{ℓ−5}(Γ₀(6))^{(−(2/ℓ),−(3/ℓ))}) at every prime 29 ≤ ℓ ≤ 139 (§4.4).
* The order-r recurrence polynomial (the unit part of charpoly X̄) equals charpoly((12/ℓ) · T_ℓ on
  S^new_{ℓ−3}(Γ₀(6))^{(−(2/ℓ),−(3/ℓ))}) at every prime 37 ≤ ℓ ≤ 113; no other weight in ℓ−7, …, ℓ+3, sign class or
  scalar matches. This is the integral-weight form of Theorem A (§3) on certified data.
* s = ⌊(ℓ²−1)/(24ℓ)⌋ = dim of that weight-(ℓ−5) class, for every prime 29 ≤ ℓ ≤ 233; no T_ℓ eigenvalue there
  is 0 mod ℓ.

**Finite hypotheses beyond the kernel's reach [N].** `scripts/boylanwebb/gen_rankR.py` (exact FFT products) checks,
at each prime, d = s + r, the order-r Cayley–Hamilton relation, det₀ ≠ 0, det C ≠ 0, Θ invertible and ū₀ ≠ 0.
All hold at every prime 149 ≤ ℓ ≤ 257 (see RESULTS). With the generic Lean theorem this is a numerical, not
formal, proof of b_ℓ(m) = 2m−1 for every m there; only memory (about 20 GB at 127) stops the kernel check.

**G4's hypothesis [N].** No prime 5 ≤ ℓ ≤ 2·10⁶ divides a_ℓ(h₈) (`nonordinary_wt8.gp` extended; previously 6·10⁴).

**G5, reformulated.** Since the unit-root part of X̄ is cyclic on the odd orbit, L(1) ∈ Λ^odd(3, 2) iff L(1) is
congruent mod ℓ² to an element of the ordinary (unit-root) part. So **G5 ⟺ the non-ordinary part of
L(1) = U(Φ) is nonzero mod ℓ²**, the ℓ²-analogue of Ahlgren–Boylan's U(Δ^δ) ≢ 0 mod ℓ. Through §4.11 its
components lie along the slope-1 forms tied to the weight-(ℓ−5) class, where Waldspurger–Kohnen type formulas
make them twisted central L-values; no uniform non-vanishing mod ℓ of such values is known. Tests: ū₀ is a
cyclic vector for Θ at every 53 ≤ ℓ ≤ 113 (weak evidence, a random vector passes about 80% of the time); no
θʲ-twist of L(1) or L(2) reproduces ū₀ consistently.

**What a uniform proof still needs.** (1) G5 for every ℓ (open mathematics). (2) Claim K of §4.11 in Lean (log
Cartier on X₀(6)). (3) ℓ ∤ a_ℓ(h₈) for every ℓ, an ordinarity statement for one fixed form, also open. (4) The
dictionary from the generic Lean theorem's coordinates to Θ on K̄ for every ℓ, which the per-prime files bypass.

## 5. Rank attainment (b)

### 5.1 Exact criterion [P]
Assume Theorem A. Then Y has rank R and the stable module is Ω(m) = ℤ_ℓ[X]y mod ℓ^m.
* ⟸ [P, Nakayama]: if ȳ = L̄(1) is a cyclic vector of X̄|_V ≅ T_{ℓ²}|𝒮 ⊗ 𝔽_ℓ, then Ω(m) is free of rank R for all m.
* ⟹ [O, gap G6]: needs a lattice argument. Non-cyclicity mod ℓ does not by itself force a deficit at higher
  precision (counter-pattern A = diag(1,1+ℓ), y = (1,1)).
* Since z̄ = 0, we have ȳ = L̄(1) = η(ℓz)·U_ℓ(1/η).
* "Cyclic" means the Krylov span of (p(ℓn − ρ))_{n ≤ R} under Ξ is all of 𝔽_ℓ^R.
* Cyclicity of L̄(1) needs (i) T_{ℓ²} mod ℓ to be cyclic (minimal polynomial = characteristic polynomial),
  and (ii) L̄(1) to have a nonzero component in each primary component.
* Exceptions are defined by failure of cyclicity of L̄(1). Repeated eigenvalues are neither necessary nor
  sufficient for this in general; a geometric multiplicity ≥ 2 is a sufficient obstruction.

The mod-ℓ rank r_ℓ(1) equals the Krylov rank of L̄(1).

### 5.2 ℓ = 607 (BW §6.1 rank deficit) [N, decisive]
Computed with `halfint.py 607 607` (exact over 𝔽₆₀₇, q-expansions to ℓ²R ≈ 9.2·10⁶ terms, about 30 min):
* d = 50 and R = r = 25.
* **rank Ξ = 25, det Ξ ≠ 0.** So Theorem A holds at 607: d₆₀₇ = 0, rank D̄ = 25, X̄ is semisimple at 0, and the
  unit-root rank is 25.
* charpoly(Ξ) = (deg-22 irreducible)·(x + 201)·**(x + 367)²**. The characteristic polynomial is *not squarefree*:
  T_{607²} has the repeated eigenvalue −367 mod 607. Under Yang's isomorphism this means two weight-604 level-6
  newforms in the class have congruent a₆₀₇ mod 607.
* **Krylov rank of L̄(1) = 24 = R − 1.** This verifies the deficit at precision one.
  It does not verify BW's reported deficit at every precision; §5.4 gives evidence against that extension.
* **Geometric multiplicity of −367 is 2**: dim ker(Ξ + 367) = 2. So T_{607²} mod 607 has a 2-dimensional
  eigenspace and **no vector of 𝒮 ⊗ 𝔽₆₀₇ is cyclic**. The deficit is forced by the Hecke module itself and does
  not depend on the partition vector. Every orbit has dimension ≤ 24, and L̄(1) attains 24.

So the cause is an eigenvalue coincidence in T_{ℓ²}, not a failure of d_ℓ = 0 (cf. LIT_CHECK point 3).
d₆₀₇ = 0 and r₆₀₇ = R − 1 are both correct and consistent.

### 5.3 Heuristic
* A random monic polynomial over 𝔽_ℓ fails to be squarefree with probability exactly 1/ℓ.
* A fixed vector fails to be cyclic for a regular matrix with probability ≈ (number of primary components)/ℓ^{deg},
  which is also ≲ 1/ℓ.
* So the model predicts that rank attainment fails at ℓ with probability ≍ 1/ℓ:
  * about Σ_{29≤ℓ≤1300} 1/ℓ ≈ 0.8 failures below 1300. BW found exactly one, ℓ = 607;
  * infinitely many failures in total (Σ 1/ℓ diverges), but of density zero.

So conjecture (b) "for all ℓ" is false. The natural replacement is "for all ℓ outside a sparse exceptional set
𝓔 ∋ 607". The membership condition for 𝓔 is explicit and computable (5.1).

### 5.4 The missing direction at 607 appears at precision two [N; 2026-11-01]

The pre-existing `g6_sharp_607.log` already recorded Smith lengths
`[2 × 24, 1]` at precision two. This means 25 generators, although only 24
summands have full length. A fresh run of `g6_sharp.py 607 607 4 4` gives
`[m × 24, m−1]` for `m = 2, 3, 4`, and `[1 × 24]` for `m = 1`.
The computed starting thresholds remain `1, 3, 5, 7`.

An independent implementation, `scripts/frontier/pattern/rank_lift_check.py`,
uses the single-weight basis `Δ^t E₄^a E₆^b / E₆₀₆^N`, without importing the
Katz-coordinate implementation or its Smith routine. At `N = 2, 3, 4` it
computes 27 odd iterates beginning with `L(3)` modulo 607². Each run checks
880 extra coefficients not used to solve for coordinates. The saved first
80 coefficients of all 27 iterates agree across cutoffs. FLINT's integer
Smith form gives 24 valuation-zero factors and one valuation-one factor;
the next two orbit vectors do not enlarge the finite module.

There is a compact witness. Take coefficients `q²⁶` through `q⁵⁰` of
`L(3), L(5), …, L(51)` as the rows and columns of a 25-by-25 matrix `C`.
The leading 24-by-24 minor has determinant `112 (mod 607)`, and

`det C / 607 = 504 (mod 607)`.

Solving for the last column on the first 24 rows leaves residual coefficient
`607 · 308` in row `q⁵⁰`; `112 · 308 = 504 (mod 607)`. Thus the image of
this finite matrix is `(ℤ/607²)^24 ⊕ ℤ/607`. The standard-library checker
`check_rank_lift_witness.py` verifies the determinants by integer Bareiss
elimination and checks the residual directly, independently of FLINT/SymPy.
The matrices and relations are in `docs/verification/rank607-uniform-n{2,3,4}.json`.

**Reconstruction bound proved (2026-11-01).** The earlier truncation concern
has now been resolved at the structural level. The new Lean modules
`FiniteArithmetic.FormalSturm` and `FiniteArithmetic.EnvelopePrecision` prove:

1. Over any commutative ring in which 1728 is a unit, a homogeneous polynomial
   of weight `k` in E₄ and E₆ is determined by its coefficients through
   `q^{floor(k/12)}`. The proof removes successive discriminant factors; it
   works over prime-power rings with zero divisors.
2. If the Katz envelope forces all digits beyond `N` to vanish modulo `p^m`,
   then `E_{p−1}^N F` is a homogeneous form of weight `N(p−1)` modulo `p^m`.
3. For every prime `p ≥ 13`, both envelopes are at least 3 from index 3 on.
   Every positive partition iterate satisfies the appropriate envelope, so
   `E_{p−1}² L_p(b)` has weight `2(p−1)` modulo `p²`.
4. `partition_two_eq_of_coeff_prefix` identifies an actual partition iterate
   with any candidate of this form having the same required prefix.

At 607 the weight is 1212, so the required prefix is exactly `q^0,…,q^101`.
The triangular basis is `Δ^t E₄^{303−3t}/E₆₀₆²`, `0 ≤ t ≤ 101`.
Consequently reconstructing after each U or D step is valid, rather than an
assumption justified by holdout checks. Each step requires coefficients only
through `q^{607·101}=q^61307` of its input (or of Φ times its input).

**Independent exact replay.** `verify_rank607_series.py` uses only Python's
standard library. It computes products by carry-free packing into integers
with base `2^64`, checking the coefficient bounds before multiplication.
It imports neither the generator nor FLINT/SymPy. Euler's pentagonal identity
gives η; because `61308 < 607²`, the required Φ prefix is exactly
`q^15352 / ∏(1−q^n)`. Von Staudt–Clausen gives

`E₆₀₆ ≡ 1 − 2·607 Σ σ₆₀₅(n)q^n (mod 607²)`,

so its inverse square is `1 + 4·607 Σ σ₆₀₅(n)q^n`.
Starting from `L(0)=1`, the program reconstructs 55 alternating steps and
matches all 2,160 saved coefficients and the entire determinant witness.
It also verifies the mod-607 dependence of `L(51)` on the preceding 24
odd iterates in all 102 basis coordinates, with a unit first coefficient 36.
Together with the unit 24-by-24 minor, this gives the computational rank 24
at precision one. The replay and all intermediate coordinates are saved in
`docs/verification/rank607-integer-replay.json`.

**The recovered direction matches the repeated eigenvalue.** Let `c_j` be
the saved lifting relation and put
`w = (L(51) − Σ_{j=0}^{23} c_j L(3+2j))/607 (mod 607)`.
The numerator vanishes modulo 607 in every reconstruction coordinate, so
division is well-defined modulo 607 from its value modulo 607². The 24
original vectors together with `w` have rank 25. Applying X to the same
relation, dividing, and reducing gives

`Xw ≡ 240w (mod span{L(3),…,L(49)})`.

The standard-library checker `check_rank607_hidden_direction.py` verifies
this in all 102 coordinates, and saves the explicit correction coefficients
in `docs/verification/rank607-hidden-direction.json`. Thus the extra quotient
has precisely the eigenvalue `240 = −367 mod 607` identified in §5.2.
This is an arithmetic connection to the original collision, not a proof of
the all-precision Smith profile or a computation of lifted eigenvalues.

The mathematical argument for the precision-two lower bound is short:
if the stable module had at most 24 generators, the 25-by-25 coefficient
matrix would factor through 24 columns, forcing its determinant to vanish.
The observed nonzero determinant excludes that, even over `ℤ/607²`.
This does not incorrectly infer linear independence from a nonunit determinant.
`FiniteArithmetic.DeterminantRank` proves that argument over arbitrary
commutative rings. Its `rank607Matrix` is defined using the actual infinite
partition series, and `rank607_eq_of_det` proves `rEll 607 m = 25` for every
`m ≥ 2`, conditional only on that matrix having nonzero determinant.

**Formal boundary (updated 2026-11-01).** The reconstruction theorem and the
saved numerical matrix's nonzero determinant are now kernel-checked.
`FiniteArithmetic.Rank607Witness` verifies an exact triangular reduction and
proves `actual_rank_of_entries`: entrywise agreement with `rank607Matrix`
implies `rEll 607 m = 25` for every m≥2.

**Update, unconditional (2026-11-01).** `FiniteArithmetic.Rank607Final.rEll_607` removes
that hypothesis: `rEll 607 m = 25` for every m≥2, with only the three standard axioms.
One kernel evaluation computes all series. Modulo 607², the 102 basis series and their
products with Φ supply the coefficients at multiples of 607. Coordinates of L(1),…,L(51)
are untrusted data, and each step is checked against those rows and then promoted to an
identity of full series by `partition_two_eq_of_coeff_prefix`. Python replaying the
program's rows matched all 625 entries, by a route independent of the earlier generator.

Boylan–Webb §6.1 report r₆₀₇(m)=24 for all m≥1 but do not define rank for a non-free module. `rEll` is the least number of generators, so the two statements conflict only under that reading. At precision two, `Rank607Structure.lamEquiv` proves Λ^odd(3, 2) ≅ (ℤ/607²)²⁴ ⊕ ℤ/607: 25 generators, 24 of them free (invariant factors 1²⁴, 607). So BW's 24 is right at m=2 if their rank counts free summands, and wrong if it counts generators. At m=1, `Rank607One.lamEquiv1` proves Λ^odd(1, 1) ≅ (ℤ/607)²⁴ and `rEll_607_one` gives r₆₀₇(1)=24, agreeing with BW under either reading. The profile `[m×24, m−1]` for m≥3 is computed but not proved in Lean.

**Module structure at precision two (2026-11-02).** `FiniteArithmetic.Rank607Structure`
proves `lamEquiv : ((Fin 24 → ℤ/607²) × (ℤ/607² ⧸ (607))) ≃ₗ Λ^odd(3, 2)`. The proof
extends the kernel check through L(53) and then checks four untrusted certificates:
L(53) = Σ rel_j L(2j+3) in all 102 coordinates, so L(3), …, L(51) span Λ (X-stability);
w = L(51) − Σ_{j<24} t_j L(2j+3) satisfies 607w = 0 in all coordinates; and an
elimination matrix P gives P·G = diag(1, …, 1, 607·308) on coefficients q²⁶ … q⁵⁰
of the generators, with 308 a unit. The only relations among V₀, …, V₂₃, w are therefore
multiples of 607w. This is the precision-two case of the profile `[m×24, m−1]`.

`FiniteArithmetic.Rank607One` reduces the same data modulo 607. L(51) ≡ Σ t_j L(2j+3)
and L(1) ≡ Σ rel1_j L(2j+3) hold in all coordinates modulo 607, so L(3), …, L(49) span
Λ^odd(1, 1); an explicit inverse modulo 607 of the leading 24-by-24 block of the minor
gives independence. Hence `lamEquiv1 : (ℤ/607)²⁴ ≃ₗ Λ^odd(1, 1)` and `rEll 607 1 = 24`.

`FiniteArithmetic.Rank607Threshold` proves `bEll 607 2 = 3`, the conjectured value 2m−1
at m=2, on actual partition data. A functional on the 102 reconstruction coordinates
vanishes on L(3), …, L(51) and not on L(1); coordinates are well defined because the
basis is X^k times units. So L(1) ∉ Λ^odd(3, 2), the module Λ^odd(1, 2) is strictly
larger than the finite Λ^odd(3, 2), and X cannot map it bijectively onto Λ^odd(3, 2).
Exact values at m≥3 are not proved.

Higher-precision experiments alone are not being used to infer an infinite theorem.

The denominator in the independent replay now has an unconditional general
Lean identification. In `FiniteArithmetic.PrecisionSquare`,
`map_E_square_general` and `map_Einv_square_squared_general` prove

```text
E_(p−1) ≡ 1 − 2p S,     E_(p−1)^(-2) ≡ 1 + 4p S  (mod p²),
S = Σ_(n≥0) σ_(p−2)(n) q^n,     p prime, p≥5.
```

The proof uses the p-adic von Staudt–Clausen estimate for
`p B_(p−1)+1`, then the square-zero identity for p in `ZMod (p²)`.
It concerns the full series and avoids an explicit calculation of B₆₀₆.
This removes the denominator formula as an arithmetic prerequisite for
the replay; the finite coefficient calculations and their identification
with the actual iterates remain to be checked in Lean. See the
[follow-up verification record](verification/four_family.json).

**Why this would settle all higher ranks.** `BLBound.rEll_mono` now proves
`rEll ℓ m ≤ rEll ℓ n` for `1 ≤ m ≤ n`, for actual partition modules.
Combined with `rEll_le`, `rEll_eq_bound_of_le` proves that attaining the FKO
bound at one precision forces attainment at every higher precision. Therefore
the single missing certificate would imply `r₆₀₇(m) = 25` for every `m ≥ 2`.

**The correct lattice question.** Under the lattice identification in §4.0,
write the orbit lattice inside the free ordinary lattice in Smith form with
exponents `e₁,…,e_s ≥ 0`. Then

`Ω(m) ≅ ⊕ᵢ ℤ/ℓ^{max(m−eᵢ,0)}`, and `r_ℓ(m) = #{i : eᵢ < m}`.

This is the elementary-divisor theorem, conditional on that identification.
The free-summand count is `#{i : eᵢ = 0}`; it need not equal the generator
count. Precision-independent generator rank requires all finite exponents to
be zero, equivalently saturation in the orbit's rational span. The 607 data
suggest exponents `0` repeated 24 times and `1` once. They do not establish
that all-precision Smith profile by themselves.

The published Boylan–Webb §6.1, p. 2203, reports `r₆₀₇(m)=24` at every
precision ([source](https://people.math.sc.edu/boylan/reprints/partition.pdf)).
The arithmetic is now certified in Lean. The discrepancy still needs expert review before
being described as a correction to that paper, because the paper does not define rank
for a non-free module. In particular, the first-digit
eigenvalue coincidence alone cannot justify a persistent generator deficit.

Reproduce the independent arithmetic with:

```sh
python3 scripts/frontier/pattern/rank_lift_check.py --prime 607 --cutoff 3 --output /tmp/rank607-n3.json
python3 scripts/frontier/pattern/check_rank_lift_witness.py docs/verification/rank607-uniform-n2.json docs/verification/rank607-uniform-n3.json docs/verification/rank607-uniform-n4.json
python3 scripts/frontier/pattern/verify_rank607_series.py docs/verification/rank607-uniform-n2.json --output /tmp/rank607-integer-replay.json
python3 scripts/frontier/pattern/check_rank607_hidden_direction.py /tmp/rank607-integer-replay.json docs/verification/rank607-uniform-n2.json --output /tmp/rank607-hidden-direction.json
```

### 5.5 Predicting the precision of rank growth [proved algebra; conditional arithmetic application, 2026-11-01]

There is a general prediction theorem, but it depends on the operator and
partition seed, not just on the prime's residue class. The following gives a
precise sufficient criterion, an exact first-lift test, and counterexamples
to an eigenvalue-only rule. These are consequences of standard module theory;
no novelty claim is made for Smith normal form or the lifting algorithm.

**One missing generator theorem.** Let `O = Z_p`, let `Y` be free of rank
`r+1`, let `T ∈ End_O(Y)`, and let `y ∈ Y`. Suppose that, for some `d ≥ 1`,

`T^r y − Σ_{i=0}^{r−1} c_i T^i y = p^d w`,

and that `y, Ty, …, T^{r−1}y, w` is an O-basis of Y. Put `W = O[T]y` and
`Ω(m) = image(W → Y/p^mY)`; this is the image in the ambient quotient,
**not** `W/p^mW`. Then

`W = O y ⊕ O Ty ⊕ … ⊕ O T^{r−1}y ⊕ p^d O w`,

`Ω(m) ≅ (O/p^m)^r ⊕ O/p^{max(m−d,0)}`.

Thus its minimum number of generators is `r` for `1 ≤ m ≤ d` and `r+1`
for `m ≥ d+1`. The missing direction first appears at exactly precision
`d+1`; it cannot appear and subsequently disappear.

*Proof.* Let H be the displayed lattice on the right. The first `r` iterates
and the relation show `H ⊆ W`. Also `p^dY ⊆ H`. Applying T to the old
iterates stays in H by the relation, and `T(p^d w) ∈ p^dY ⊆ H`. Hence H is
T-invariant and contains y, so `W ⊆ H`. Reduction of the basis expression
gives the direct sum. Its number of nonzero cyclic summands is the minimum
generator count, by reduction modulo the maximal ideal (Nakayama). ∎

The lattice identity is kernel-checked in
`FiniteArithmetic.orbit_span_eq_of_divided_relation`, over any
commutative ring and with `p^d` replaced by an arbitrary scalar. The same
file proves `relation_visible_iff`: the determinant of the original vectors
is nonzero modulo `p^m` exactly when `d < m`, provided replacing the last
vector by the divided remainder gives a unit determinant. The theorem
`card_le_of_lifted_relation` converts that into a generator lower bound.
The displayed module decomposition and Nakayama step above are paper proofs;
there is no new unconditional numerical theorem about 607 in that file.

**General first-lift test.** For a matrix `A` over O, set `A₀=A mod p` and
`r=rank A₀`. There is a well-defined linear map

`β_A : ker A₀ → coker A₀,  v ↦ [A ṽ / p mod p]`.

Changing the lift ṽ adds an element of `im A₀`, so its class is independent
of the lift. If `s=rank β_A`, then

`image(A mod p²) ≅ (O/p²)^r ⊕ (O/p)^s`.

In particular the next generator count is exactly `r+s`. A zero obstruction
means no jump at precision two; it does not imply there will never be a jump.

*Proof.* Unit row and column operations over `O/p²` transform A to a block
matrix `diag(I_r,pB)`. The reduction of B represents β_A. Row and column
operations over the residue field put B into rank-s normal form; their lifts
give `diag(I_r,pI_s,0)` over `O/p²`. This proves the assertion. ∎

For a cyclic orbit, the residue-field relations are generated by its minimal
polynomial P. One may therefore obtain the image of β by taking
`w=P(T)y/p`, following its T-orbit modulo p, and factoring out the old orbit.
For a rigorous application use enough Krylov columns to generate the full
O-orbit (the ambient rank suffices by Cayley–Hamilton), or separately certify
closure. This qualification prevents a prefix-only rank from being mistaken
for the stable rank. At 607 the saved coefficient matrix gives `r=24,s=1`.

**Spectral-gap corollary, with explicit hypotheses.** Suppose T has an
*integral eigenbasis*, all coordinates of y in that basis are units, exactly
one pair of eigenvalues agree modulo p, and all other pairwise differences
are units. If the exceptional difference has valuation d, the Smith
exponents of the orbit matrix are `0` repeated `R−1` times and d once.
Thus the extra generator first appears modulo `p^{d+1}`.

*Proof.* In that basis the Krylov matrix is a diagonal unit matrix times a
Vandermonde matrix. Modulo p its rank is `R−1`; its determinant has valuation
d by the Vandermonde product. The first `R−1` Smith exponents are zero and
their total sum is d, forcing the last exponent to be d. ∎

This corollary has **not** been verified as the mechanism at 607: we have not
constructed an integral eigenbasis or measured the two lifted eigenvalues.
The divided-relation criterion applies without diagonalizing T. In a rank-two
block `T=λI+p^d B`, a primitive y with `det(y,By)` a unit gives the same
threshold, even when B has no eigenvalues in the residue field.

**Checks and limits.** `scripts/frontier/pattern/predict_rank_lifts.py`
implements the divided Schur-block test without calling Smith normal form
in the predictor, then compares its results against FLINT's integer Smith
form. The 400 random rectangular/square cases pass. Nine reconstructed
partition cases at `p=13,29,31,47,71,113,197,607,859` also agree: 607 has
the single jump `24 → 25`, and the other sampled primes already attain their
bound at precision one. These are computation checks, not proofs for
untested primes or numerical Lean certificates.

Controls over `Z_5` give:

| Operator and seed | Smith exponents | Generator counts at m=1,2,3,4,5 |
|---|---|---|
| `diag(1,1+5)`, `(1,1)` | `0,1` | `1,2,2,2,2` |
| `diag(1,1+5²)`, `(1,1)` | `0,2` | `1,1,2,2,2` |
| `diag(1,1+5³)`, `(1,1)` | `0,3` | `1,1,1,2,2` |
| Identity, `(1,1)` | `0,∞` | `1,1,1,1,1` |
| `diag(1,6)`, `(1,0)` | `0,∞` | `1,1,1,1,1` |
| `[[1,1],[0,1]]`, `(0,1)` | `0,0` | `2,2,2,2,2` |
| `[[1,10],[5,1]]`, `(1,0)` | `0,1` | `1,2,2,2,2` |
| `diag(1,6,31)`, `(1,1,1)` | `0,1,3` | `1,2,2,3,3` |

The last example warns against using only the largest pairwise eigenvalue
congruence depth: it is 2 here, but the third generator arrives at precision
4. Multiple collisions require the full module invariant. Repeated
eigenvalues alone neither force a rank deficit nor predict its duration.

Reproduce with:

```sh
python3 scripts/frontier/pattern/predict_rank_lifts.py --output /tmp/rank-lifting-prediction.json
```

Saved data: `docs/verification/rank_lifting_prediction.json`. The algebraic
background is established: [Lübeck's EDIM documentation](https://www.math.rwth-aachen.de/~Frank.Luebeck/gap/EDIM/doc/chap1.html)
describes p-adic elementary-divisor algorithms and references his 2002 paper;
[Elsheikh's 2017 thesis](https://uwspace.uwaterloo.ca/items/32d2d4c1-8cc4-46e9-86af-05390b5ef62b)
studies local Smith forms and Krylov methods. The potential contribution here
is the partition-orbit application and its formal certification. No formula
classifying all exceptional primes, or guaranteeing that every deficit lifts
at precision two, has been established.

---------------------------------------------------------------------------------------------------------

## 6. Corrected statements

1. **Theorem (P*, all ℓ ≥ 13).** rank D̄ = rank X̄ = R; X̄ is semisimple at 0; d_ℓ = 0; b_ℓ(m) ≤ 2m − 1;
   X has exactly R unit roots.
2. **Revised rank target (2026-11-01).** At precision one the rank is the Krylov
   rank of L̄(1). At higher precision, determine the orbit lattice's Smith
   exponents (§5.4). The former proposal that the rank is always equal to its
   precision-one value conflicts with the independently reproduced 607 data.
   Cyclicity at precision one remains sufficient for attainment at all precisions;
   it need not be necessary for attainment at a later precision.
3. **Conjecture (O).** For ℓ ≥ 29, b_ℓ(m) = 2m − 1. Equivalently Θ^kū₀ ≠ 0 for all k, which is expected
   from: Θ invertible (slope-1 count = ⌊d/2⌋) and ū₀ ≠ 0.
   **Proved at ℓ = 29, 31 (2026-11-02):** `Exact29.bEll_29` and `Exact31.bEll_31` give
   b_ℓ(m) = 2m − 1 for every m ≥ 1, for BW's literal invariant `BLBound.bEll`.
   The argument, in [BLBound/Threshold](../RamanujanTau/BLBound/Threshold.lean), runs as follows.
   If L(2k+1) ∉ Λ^odd(2k+3, m), then X : Λ^odd(2k+1, m) → Λ^odd(2k+3, m) is not a bijection.
   An injective X would embed the larger module into the smaller one, and both are finite, because a high iterate of X embeds them in the stable module.
   Non-membership holds for k ≤ m − 2 whenever L(2n+3) − κL(2n+1) = ℓ^{n+1}G_n and one functional sees L(2n+1) and U G_n but not U L(2n+1) modulo ℓ.
   The certificates behind `Complete29`/`Complete31` supply exactly these inputs.

## 7. Gaps
* G1: The statement and signs of Yang's published Theorem 1 have been checked (§G1). Its use in the
  integral determinant argument still needs a complete formal implementation; numerical checks do not supply it.
* G2: Katz §II theorem (1)–(2) and corollary (1) supply the precise θ and cuspidality references.
  §3.2 now uses an operator polynomial instead of Deligne–Serre. The level-six filtration construction,
  Hecke identity on actual forms, and integral reduction/base-change comparison remain formalization obligations.
* G3: §4.1 uses the AO envelope lemmas, i.e. inputs (I1)–(I3) of ATKIN_OBRIEN_PROOF.md. These are standard
  but not fully refereed. BW Thm 1.2 gives the same conclusion without them.
* G4: The actual arithmetic identification of Θ remains open. §4.4 gives a numerical identification and an expected invertibility criterion. Full invertibility is sufficient, but the weaker seed-survival test in §4.2 is the exact sharpness target.
* G5: Survival of ū₀ under Θ and cyclicity of L̄(1) under X̄ are distinct arithmetic seed questions. Neither has an all-prime proof here. The latter fails at ℓ = 607; that does not itself refute the sharpness conjecture.
* G6: The generator count at 607 is proved (`Rank607Final.rEll_607`), and so is the
  module at m=2, Λ ≅ (ℤ/607²)²⁴ ⊕ ℤ/607 (`Rank607Structure.lamEquiv`), and at m=1,
  (ℤ/607)²⁴ (`Rank607One.lamEquiv1`). Identify the
  orbit lattice's Smith exponents for all m at 607, and in general (§5.4). The old precision-independent rank target has
  contrary numerical evidence. Monotonicity and propagation of attainment
  are now proved in Lean, independently of the 607 calculation.

## G1 verification

(2026-10-28: preprint checked. 2026-10-29: the published Theorem 1, p. 5, also checked in
[Nagoya Math. J. 215 (2014), 1–66](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/A54F3A98B24022EB47D0FBBA2FAB37B4/S0027763000010916a.pdf/modular_forms_of_halfintegral_weights_on_sl2.pdf),
doi:10.1215/00277630-2684452.)

**Verdict: verified, with adjustments to the citation only. The mathematics of Theorem A is unchanged.**

**Paper.** The author is **Yifan Yang** (NCTU, Hsinchu), not Tonghai Yang. The title is "Modular forms of
half-integral weights on SL(2, ℤ)". The result used is **Theorem 1**. Theorem 2 is the analogue for 3 | r and is
not needed.

**Statement (Thm 1).**
* Hypotheses: r ∈ ℤ with (r, 6) = 1 and 0 < r < 24; s a nonnegative even integer.
* Space: S_{r,s} = {η(24τ)^r f(24τ) : f ∈ M_s(1)} ⊂ S_{r/2+s}(576, (12/·)).
* Conclusion: the Shimura correspondence gives an isomorphism of Hecke modules
  S_{r,s} ≅ S^{new}_{r+2s−1}(6, −(8/r), −(12/r)) ⊗ (12/·).
* Atkin–Lehner convention: ε₂ and ε₃ are the eigenvalues of W₂ and W₃. Yang ties this convention to Atkin–Lehner
  [Math. Ann. 185, Thm 3] and to the Guo–Ono form G_ℓ = q + (8/r)2^{(ℓ−5)/2}q² + (12/r)3^{(ℓ−5)/2}q³ + ⋯, which
  lies in the class (−(8/r), −(12/r)). So a_p = −ε_p p^{k/2−1}, the same convention as pari's.
* Hecke operators: T_{n²} is defined only for (n, 6) = 1 (Def. 10; Remark 12 says the other operators vanish).
  Prop. 11 shows T_{p²} is Shimura's operator on S_{k+1/2}(576, (12/·)) with k = (r−1)/2 + s.
* Corollary 1: multiplicity one holds on S_{r,s}.
* Proof method: comparison of Shimura trace formulas.

**Comparison with §3.1.**
1. *Dictionary.* Take r := 24 − j, so r ≡ −ℓ (mod 24), and s := 12t + j − 13 = (ℓ − r − 2)/2.
   * Then ν_η^{−ℓ} = ν_η^r.
   * By Yang's Prop. 6, S_{r,s}(1) = η^r M_s(1), and this space is all of 𝒮. It agrees with §2.1 because
     G/η^j = η^r·(G/Δ).
   * The map h ↦ h(24τ) gives S_{r,s}.
2. *Weights.*
   * Half-integral side: k = (r−1)/2 + s = (ℓ−3)/2 = λ, so the weight is λ + 1/2 = (ℓ−2)/2. ✓
   * Integral side: r + 2s − 1 = ℓ − 3 = 2λ. ✓
3. *Hypotheses for every prime ℓ ≥ 13.* (r, 6) = 1 and 0 < r < 24 hold. s = 12t + j − 13 is even, and it is ≥ 0
   exactly when ℓ ≥ 13: for t = 0 we have j = ℓ ≥ 13. Both ℓ mod 24 and the sign class enter only through
   r = 24 − j.
4. *Signs.* Yang's class is (−(8/r), −(12/r)).
   * (8/·) and (12/·) are even characters, so (8/r) = (8/ℓ) = (2/ℓ) and (12/r) = (12/ℓ) = (3/ℓ).
   * Hence the class is (−(2/ℓ), −(3/ℓ)), exactly as used, in the a_p = −w_p p^{k/2−1} convention.
   * In particular a₂(F) = (2/ℓ)2^{(ℓ−5)/2} and a₃(F) = (3/ℓ)3^{(ℓ−5)/2}, which matches §3.2 step 5.
5. *Isomorphism.* The map is onto the *whole* newform eigenspace of that sign class. It is not onto a subspace,
   and there are no oldforms.
6. *Hecke.* The twist ⊗(12/·) means T_{p²} ↔ (12/p)·T_p for p ∤ 6. This holds at p = ℓ, which is all
   Theorem A needs. Yang's T_{ℓ²} (Prop. 11, coefficients in q^{n/24}) is the operator of §2.3, whose middle term
   is (12/ℓ)((−1)^λ n/ℓ)ℓ^{λ−1}.
   * Since the modules are isomorphic, the characteristic polynomials over ℚ agree.
   * So det(T_{ℓ²}|𝒮) = (12/ℓ)^R·∏_F a_ℓ(F), where the product runs over all embeddings of newforms in the
     class. This is "±∏ a_ℓ(F)", and its ℓ-adic unit status is what transfers.

**Adjustments (citation only).**
* §0 and §3.1: replace "T. Yang … Thm 1.x" with "Yifan Yang, Nagoya Math. J. 215 (2014), Thm 1 (with
  r = 24 − (ℓ mod 24), s = (ℓ − r − 2)/2)".
* The statement in §3.1 can drop the asterisk on the sign normalization.
* The claim that Ahlgren–Allen–Tang and Ahlgren–Beckwith–Raum use this form was not checked here.

**yang.gp convention.** `yang.gp` keys the classes by pari's `mfatkineigenvalues`. Taking the first embedding is
harmless, because AL eigenvalues are rational.
* A check in the scratchpad confirmed that every newform in S^{new}_{ℓ−3}(Γ₀(6)) satisfies
  a₂ = −w₂2^{(ℓ−5)/2} and a₃ = −w₃3^{(ℓ−5)/2}, with 0 violations. It ran for all 20 primes ℓ ∈ {13, …, 103}
  except 79 and 89.
* For each of those primes, Yang's class (−(8/r), −(12/r)) equals the class (−(2/ℓ), −(3/ℓ)) used in the doc.
* The class has dimension dim M_s(1) = R.
* So pari's convention, yang.gp's keys and Yang's ε₂, ε₃ all agree.
* The sign question raised in the §3.2 Remark (ℓ = 859) is settled by the theorem itself: the class is
  (·, −(3/ℓ)), not (·, +(3/ℓ)).

## External review 2 (2026-10-29)
* **Yang.** Independently confirmed: Theorem 1 (p. 5) with r = 24 − j and s = (ℓ+j−26)/2 gives the
  identification, with signs −(2/ℓ), −(3/ℓ) and the twist. Prop. 11 (p. 10) gives the Hecke normalization.
* **ℓ = 859.** Independently recomputed by the brute-force ℓ²R method: ~2.6·10⁷ coefficients, 4.5 min,
  3.5 GB. Results:
  * dim 36, rank 36, **det 318 mod 859**, Krylov rank 36, squarefree charpoly. All agree with our O(ℓd)
    composition method.
  * Before the run, the optimized code was checked against the original script's full matrices at 15 smaller
    primes.
* **Θ.** Reproduced for all 21 primes 29 ≤ ℓ ≤ 113.
  * Sharpness **for every m** still depends on the operator reduction and the truncation justification (§4.3),
    which are not yet written out.
* **Corrections applied** (§0 item 2, §5.1):
  * exceptions are characterized by non-cyclicity, not by repeated eigenvalues;
  * the mod-ℓ ⇒ all-precision deduction needs a lattice argument (G6), with counter-pattern diag(1,1+ℓ).
* **Assessment.** Theorem A and the d_ℓ = 0 argument are substantially more credible and warrant specialist
  review as a proposed paper proof. The higher-precision rank and the all-m sharpness claims keep their
  separate qualifications.


### 2026-11-01 follow-up: checked finite seed models

`FiniteArithmetic.SeedSurvival.cubic_idempotent_lift` proves the standard
correction `P=3P₀²−2P₀³` in any ring when `(P₀²−P₀)²=0`. The new scan
constructs P₀ using Bezout separation of the zero and unit factors of the
characteristic polynomial modulo p, avoiding large group-exponent powers.

At p=233,257,307,401,607, Katz depths 3 and 4 give identical Θ matrices and
seeds. The respective kernel dimensions are 9,10,12,16,25. Every matrix is
invertible and every seed is nonzero. `FiniteArithmetic.SeedModels` checks
left inverses and seeds in Lean, then proves survival for all iterations in
each saved finite model. The [saved data](verification/seed_survival_extended.json)
and [verification record](verification/four_directions.json) identify the checks.

These are finite-model theorems. They do not discharge the arithmetic
identification of Θ, the remainder bounds in that identification, or G5 at
all primes. Exact all-prime stabilization therefore remains open.
