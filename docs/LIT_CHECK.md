# Literature check: l-adic properties of p(n) (2026-10-28)

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
- b_29(1,2,3)=1,3,5; b_53(1,2)=1,3; b_89(1,2)=1,3; b_1297(1)=1. b_7(m)=2m-2 (Watson), b_5=b_11=m.
- r_l(1)=R_l for all l<=1297 EXCEPT l=607: r_607(m)=R_607-1 for all m.
  (Sec 6.2: d_l > 0 forces a rank deficit, but the converse is NOT asserted. So the rank drop at 607 does not contradict d_607 = 0. The invertible subspace V_inv and the span of the partition orbit are different objects, and their dimensions must be computed separately. There is no internal inconsistency.)
- No table of b_l(m) for 13<=l<=23 is printed.

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
