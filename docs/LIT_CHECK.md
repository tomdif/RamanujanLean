# Literature check: l-adic properties of p(n) (2026-10-28)

This is a dated literature record. For the later prime-29 formalization and the
verification boundary of the general-prime draft, see [Current status](STATUS.md).

Primary source read in full: Boylan–Webb, "The partition function modulo prime powers",
Trans. AMS 365 (2013) 2169–2206 (people.math.sc.edu/boylan/reprints/partition.pdf).

## BW definitions
- Phi_l = eta(l^2 z)/eta(z); f|D = (Phi f)|U(l); X = D∘U as a composition of maps (f|X := f|U|D, i.e. apply U first, then D); Y = U∘D.
- L(0)=1, L(b)=L(b-1)|D (b odd), |U (b even). L(b)=eta(lz)P(b) (b odd), eta(z)P(b) (b even).
- Lambda^odd(b,m) = Z/l^m-span{L(beta): beta>=b odd}. Thm 1.4: nested chain constant for 2b+1 >= b_l(m);
  Remark 1: b_l(m) = smallest b with X: Lambda^odd(b,m) -> Lambda^odd(b+2,m) an isomorphism (odd chain).
- r_l(m) = rank Omega^odd(m) <= R_l = floor((l+12)/24)   (1.13).
- d_l (5.1) = min t>=0 : for all f in M_{l-1}, f|D|X^t in S, S = largest F_l-subspace of S_{l-1} on which X is iso.
  d_l <= dim S_{l-1}. d_l=0 computed for all 5<=l<1300.
- Thm 1.2: d_l=0 => b_l(m) <= 2m-1. Thm 5.1: b_l(m) <= 2(d_l+1)m - 1 is the bound the proof in Sec 5.2 actually establishes. Do NOT simplify it to 2d_l+2m-1; the two differ for d_l > 0 and m > 1. (An earlier version of these notes wrongly called this a typo.)
- Remark after Thm 1.2: "sharp for all computed cases with l >= 29".

## BW computations (Sec. 6.1)
- Bases computed: m=1, 13<=l<1300; m=2, 13<=l<=89; m=3, 13<=l<=29; m=4, l=13.
- Lean (proved 2026-11-03; committed and included in the full build): b_l(m)=2m-1 for all m at l=37,41,43,47 (`Rank2At37.bEll_37`, ...), beyond BW's computed range m<=2.
- Lean (proved 2026-11-03; committed and included in the full build): b_l(m)=2m-1 for all m at every prime 61<=l<=139 (`RankRAt61.bEll_61`, ...; order-r recurrence).
- Lean (proved 2026-11-03; committed and included in the full build): b_l(m)=2m-1 for all m at l=53,59 (`RankSAt53.bEll_53`, `RankSAt59.bEll_59`; dim K=2, 2x2 error matrix).
- b_29(1,2,3)=1,3,5; b_53(1,2)=1,3; b_89(1,2)=1,3; b_1297(1)=1. b_7(m)=2m-2 (Watson), b_5=b_11=m.
- r_l(1)=R_l for all l<=1297 EXCEPT l=607. The paper reports r_607(m)=R_607-1 for all m;
  this higher-precision assertion is in tension with the independent computations
  added on 2026-11-01 in [the research draft, §5.4](BL_SHARPNESS_PROOF.md#54-the-missing-direction-at-607-appears-at-precision-two-n-2026-11-01).
  Those computations give 25 generators modulo 607² and 24 full-length summands.
  `Rank607Final.rEll_607` now proves in Lean that the least generator count is 25 for
  every m≥2. BW write only `rank_{Z/l^m Z}` and do not define it for a non-free module, and
  their Lemma 4.1 uses a matrix in GL_r(A), which presumes freeness. The results conflict
  only if their rank means generator count. `Rank607Structure.lamEquiv` proves
  Λ ≅ (ℤ/607²)²⁴ ⊕ ℤ/607 at m=2, so the free-summand count there is 24, matching BW.
  At m=1 the module is free of rank 24 (`Rank607One.lamEquiv1`), also matching BW.
  The infinite-series reconstruction bound is now proved in Lean; the numerical
  arithmetic and its identification with the actual matrix still need kernel certification.
  (Sec 6.2: d_l > 0 forces a rank deficit, but the converse is NOT asserted. So the rank drop at 607 does not contradict d_607 = 0. The invertible subspace V_inv and the span of the partition orbit are different objects, and their dimensions must be computed separately. There is no internal inconsistency.)
- No table of b_l(m) for 13<=l<=23 is printed. Lean now proves (2026-11-02, `SmallThreshold`) that b_l(m) <= 2*floor(m/2)+1 for all m and b_l(2)=b_l(3)=3 for l=13,17,19,23, and (`SmallThresholdFive`) b_l(4)=b_l(5)=5; `AtkinExact` (2026-11-02) proves b_l(m)=2*floor(m/2)+1 for all m, from exactness of the Atkin-O'Brien index b=m at every b. So BW's bound 2m-1 is not sharp there for m>=3, consistent with the remark that sharpness holds for computed l>=29.

## Other sources
- FKO, Adv. Math. 229 (2012) 1586-1609, Thm 1.1/1.2 (+ Ramsey appendix Thm 7.1: Omega = ordinary part of U(l^2)
  on overconvergent half-integral weight forms; answers Mazur's question).
- Atkin–O'Brien, Trans. AMS 126 (1967): P(13^{a+2}N) == K_a P(13^a N) mod 13^a (restated Thm 1.1 of Garvan–Shomanov
  arXiv 2504.10824, 2025); Hecke conjecture mod 13^a proved by Garvan–Shomanov.
- Belmont–Lee–Musat–Trebat-Leder, Monatsh. Math. 173 (2014) 1-34 (arXiv 1510.01202): "The question of resolving
  when d_l(r) is zero is an open problem"; Sec. 5: "We conjecture that d_l(r) = 0 for all l >= r+5."
- Webb thesis (USC 2011), El-Guindy–Ghazy arXiv 2408.04462 (l-regular analogue): no sharpness/attainment results found.

## Corrections and clarifications (after external review, 2026-10-29)
* **The target of d_ℓ = 0 includes the Eisenstein direction.** d_ℓ = 0 ⟺ D̄(M̄_{ℓ−1}) ⊆ V_inv, where V_inv is
  the largest subspace of S̄_{ℓ−1} on which X̄ is invertible. The test must run on the whole modular-form space
  M_{ℓ−1} (dim d+1), not only on S_{ℓ−1}.
* **An exact computational test.** On the d-dimensional cusp space, V_inv = im(X̄^d). So
  d_ℓ = 0 ⟺ rank[X̄^d | D_M] = rank(X̄^d), where D_M is D̄ on all of M_{ℓ−1}. This needs no semisimplicity
  assumption. Semisimplicity at 0 can be checked separately via rank X̄² = rank X̄.
* **d_ℓ = 0 gives only an upper bound.** Proving it settles the upper bound b_ℓ(m) ≤ 2m−1 for all ℓ; it does
  not give sharpness. Sharpness needs the separate lower-bound argument on the contracting (slope-1) component.
* **Scope.** The proposed argument targets the r = 1 (ordinary partition) case of BLMT's conjecture
  d_ℓ(r) = 0 for ℓ ≥ r+5, not the full coloured-partition conjecture.
* **Conventions.** BW's Thm 1.4 treats both parity chains; the characterization after it emphasizes the odd
  chain. Our primary theorem is the partition congruence, and a write-up should translate it explicitly to
  their threshold.
* **Novelty of ℓ = 17, 19, 23.** Still "appears new, pending specialist review".

## Audit of the d_ℓ = 0 claim (2026-10-31)

**Boylan–Webb definitions, compared with the published text.** `BoylanWebb.Φ`, `U`, `L` and `BLBound.Xm`, `Lam`, `bEll`, `dEll`,
`Vinv` agree with BW (1.5)–(1.11), Remark 1 after Theorem 1.4, and (5.1). The theorems are not vacuous: `mem_bSet` shows
the bijection itself at b = 2m−1, `dEll_eq_zero` shows 0 lies in the defining set, and `Vinv_eq` with `finrank_Vbar` shows V_inv has dimension R.

**BLMT convention.** Read literally, BLMT §5 makes S^odd(r) the space where Y_r = D_r|U is an isomorphism and S^even(r) the space
for X_r = U|D_r. That contradicts their maps D_r: S^even → S^odd and U: S^odd → S^even, and literal d_ℓ(1) would not exist at
ℓ = 29: D̄(M₂₈) is the line of f, the Y-invariant line is that of g = Uf, and X̄ keeps f on its own line. BLMT report d_ℓ(r) = 0 there.
So X and Y appear swapped in that sentence. With them swapped, d_ℓ(1) is BW's d_ℓ. A write-up should state this.

**Formal gaps, none affecting the truth of `dEll_eq_zero` as stated.**
* M̄_{ℓ−1} is defined as polynomials in E₄, E₆ over 𝔽_ℓ (`FormBar`). Its equality with reductions of M_{ℓ−1} ∩ ℤ_(ℓ)⟦q⟧ is standard
  (Swinnerton-Dyer) but not stated in Lean.
* Lean covers ℓ ≥ 13. The cases ℓ = 5, 7, 11 of the conjecture (S_{ℓ−1} = 0) are not formalized.
* `Complete29` and `Complete31` state the scalar threshold. The bridge to BW's invariant is now proved (2026-11-02): `Exact29.bEll_29` and `Exact31.bEll_31` give `bEll 29 m = bEll 31 m = 2m−1` for every m ≥ 1 ([ExactThreshold](../RamanujanTau/FiniteArithmetic/ExactThreshold.lean)). This extends BW's computed b₂₉(1,2,3) = 1,3,5 to every m.
* BW's rank and BLMT's d′_ℓ(r) are not treated.

**Literature checked for overlap** (full text searched for Boylan, Webb and for ordinarity or injectivity statements): FKO 2012 and the
Ono survey ("work and numerics suggest that one can generically take" 2m−1), BLMT 2014 (open), Ahlgren–Beckwith–Raum (arXiv 2006.07645),
Ahlgren–Andersen–Dicks (arXiv 2307.07438v3), Dicks (arXiv 2603.06997), Garvan–Shomanov (arXiv 2504.10824; its remark that b_ℓ(α) = 2α−1
concerns 5 ≤ ℓ ≤ 31, where BW's d_ℓ = 0 is computed), El-Guindy–Ghazy (arXiv 2408.04462; in 2024 the analogous bounds still carry d_ℓ as a parameter).
None proves d_ℓ = 0 for all ℓ. OpenAlex citation lists for BW, BLMT and FKO were scanned by title only and are incomplete. Not read: "Congruences for
colored partition functions" (Ramanujan J. 2025, cites BW; text not located), which is the first paper to get. This is evidence, not proof of novelty.

**What is actually new, if confirmed.** BW already give b_ℓ(m) ≤ 2m−1 for every ℓ < 1300 by computation, so the new content is the removal of that condition for all primes,
together with the uniform unit statement for T_ℓ in weight ℓ−3, level 6.
