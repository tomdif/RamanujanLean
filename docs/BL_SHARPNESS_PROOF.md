# Boylan–Webb sharpness and FKO rank attainment for ℓ ≥ 29 (2026-10-28, draft, not committed)

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

**Status legend.** [P] proved here from standard results (cited). [P*] proved here modulo a cited theorem
whose exact statement still has to be checked against the source. [N] numerical only. [O] open.

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
   * The exceptional primes are characterized by **failure of L̄(1) to generate the space**. They are *not*
     characterized by repeated eigenvalues: non-cyclicity can occur with distinct eigenvalues, and an operator
     with a repeated eigenvalue can still have a cyclic vector.

   At ℓ = 607 the obstruction is a 2-dimensional eigenspace of −367 (geometric multiplicity 2). That is a
   *sufficient* obstruction: no vector is cyclic, and the Krylov rank is 24 = R − 1 mod ℓ (§5.2). BW's deficit
   at all m is their computation. Heuristically it fails with probability ≍ 1/ℓ, which means infinitely many
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

**Theorem A.** For every prime ℓ ≥ 13, det(T_{ℓ²} | 𝒮) is an ℓ-adic unit. Equivalently, X̄|_V is invertible.

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
*The exact theorem number and sign normalization still have to be checked against the source; the
literature agent has the PDFs.* §3.4 checks the statement numerically.

Consequence: det(T_{ℓ²}|𝒮) = ±∏_F a_ℓ(F), the product running over the newforms F in that class.

### 3.2 Proof of Theorem A
1. Suppose some newform F of weight k = ℓ − 3 in the class has a_ℓ(F) ≡ 0 (mod 𝔩).
2. Its reduction F̄ is a nonzero mod-𝔩 eigenform on Γ₀(6) with F̄|U = 0. Its filtration is ℓ − 3, since the
   only smaller weight in the class is −2 < 0.
3. Since 5 ≤ ℓ−3 ≤ ℓ−1, **Lemma T** gives w(θ⁴F̄) = 6. So G̃ := θ⁴F̄ is a nonzero mod-𝔩 cuspidal eigenform
   in S₆(Γ₀(6)) ⊗ 𝔽̄_ℓ, with eigenvalues
   * p⁴a_p(F) for T_p, p ∤ 6ℓ;
   * 16a₂(F) for U₂ and 81a₃(F) for U₃. Use a_{pn}(θ⁴F) = p⁴n⁴a_{pn}(F).
4. By the Deligne–Serre lifting lemma, these eigenvalues are the reduction of the T_p, U₂, U₃ eigenvalues of
   some eigenform of S₆(Γ₀(6)). That space is 3-dimensional:
   * the newform 6.6.a.a = q + 4q² − 9q³ + …, with (w₂, w₃) = (−1, +1);
   * the two U₂-eigen oldforms from 3.6.a.a = q − 6q² + 9q³ + …, with U₂ eigenvalues the roots of
     x² + 6x + 32 and U₃ = 9.

   (S₆(Γ₀(2)) = S₆(SL₂ℤ) = 0.) These were checked in pari: `mfatkineigenvalues`, `mfcoefs`.
5. The newform F has a₂(F) = −w₂(F)·2^{(ℓ−5)/2} = (2/ℓ)·2^{(ℓ−5)/2} ≡ 2^{−2} and
   a₃(F) = (3/ℓ)·3^{(ℓ−5)/2} ≡ 3^{−2}, using 2^{(ℓ−1)/2} ≡ (2/ℓ). So G̃ has U₂ = 4 and U₃ = 9.
   * **6.6.a.a has U₃ = −9.** Then 9 ≡ −9 would force ℓ | 18. Impossible.
   * **Oldforms:** U₂ = 4 would need 16 + 24 + 32 = 72 ≡ 0 (mod ℓ). Impossible for ℓ ≥ 5.
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

**What would be needed for a proof.**
* (i) Θ invertible: an exact slope-1 count. Via Ramsey/Coleman this is plausibly the ordinary part of a
  θ-twisted space of weight ℓ − 5 and level 6, but this is not worked out.
* (ii) ū₀ ≠ 0: a non-vanishing statement for one explicit vector. Like (b), we expect this can only be checked
  ℓ by ℓ.

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
  the validity of the truncated Katz model (PR = 3, N = 6). Θ mod ℓ only sees Katz blocks i with α(i), β(i) ≤ 2, by the envelope bounds, so N = 6 suffices. This routine check should still be written out.

---------------------------------------------------------------------------------------------------------

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
* **Krylov rank of L̄(1) = 24 = R − 1.** This is exactly BW's deficit r₆₀₇(m) = R₆₀₇ − 1.
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

---------------------------------------------------------------------------------------------------------

## 6. Corrected statements

1. **Theorem (P*, all ℓ ≥ 13).** rank D̄ = rank X̄ = R; X̄ is semisimple at 0; d_ℓ = 0; b_ℓ(m) ≤ 2m − 1;
   X has exactly R unit roots.
2. **Theorem (P*).** The stable rank is r_ℓ(m) = dim_{𝔽_ℓ} 𝔽_ℓ[T_{ℓ²}]·U_ℓ(1/η) for every m, i.e. the
   Krylov rank of L̄(1) in 𝒮 ⊗ 𝔽_ℓ. So the FKO bound is attained iff this vector is cyclic.
3. **Conjecture (O).** For ℓ ≥ 29, b_ℓ(m) = 2m − 1. Equivalently Θ^kū₀ ≠ 0 for all k, which is expected
   from: Θ invertible (slope-1 count = ⌊d/2⌋) and ū₀ ≠ 0.

## 7. Gaps
* G1: Exact statement, sign convention and theorem number of Yang's isomorphism. It is checked numerically for
  13 primes; Theorem A depends on it.
* G2: Lemma T and Deligne–Serre for Γ₀(6) are standard, but the level-N θ-filtration theory (Katz 1977) should
  be cited at the precise statement (Jochnowitz 1982 §; Edixhoven, Invent. Math. 109 (1992), §3).
* G3: §4.1 uses the AO envelope lemmas, i.e. inputs (I1)–(I3) of ATKIN_OBRIEN_PROOF.md. These are standard
  but not fully refereed. BW Thm 1.2 gives the same conclusion without them.
* G4: Θ invertibility (the exact slope-1 count) is open.
* G5: ū₀ ≠ 0 and cyclicity of L̄(1) are arithmetic non-vanishing statements, checkable ℓ by ℓ. No general proof
  is expected, and (b) is false at ℓ = 607.
* G6: Statement (6.2) for m ≥ 2 needs the Riesz/lattice argument of 5.1. It is written out only in outline.

## G1 verification

(2026-10-28. Source read: arXiv:1110.1810v1, the preprint of the Nagoya paper. The published version,
Nagoya Math. J. 215 (2014) 1–66, doi:10.1215/00277630-2684452, was not opened; its abstract on Cambridge Core
matches.)

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
