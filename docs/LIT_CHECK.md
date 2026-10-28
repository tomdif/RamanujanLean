# Literature check: l-adic properties of p(n) (2026-10-28)

Primary source read in full: Boylan–Webb, "The partition function modulo prime powers",
Trans. AMS 365 (2013) 2169–2206 (people.math.sc.edu/boylan/reprints/partition.pdf).

## BW definitions
- Phi_l = eta(l^2 z)/eta(z); f|D = (Phi f)|U(l); X = U∘D (f|X := f|U|D, i.e. U first), Y = D∘U.
- L(0)=1, L(b)=L(b-1)|D (b odd), |U (b even). L(b)=eta(lz)P(b) (b odd), eta(z)P(b) (b even).
- Lambda^odd(b,m) = Z/l^m-span{L(beta): beta>=b odd}. Thm 1.4: nested chain constant for 2b+1 >= b_l(m);
  Remark 1: b_l(m) = smallest b with X: Lambda^odd(b,m) -> Lambda^odd(b+2,m) an isomorphism (odd chain).
- r_l(m) = rank Omega^odd(m) <= R_l = floor((l+12)/24)   (1.13).
- d_l (5.1) = min t>=0 : for all f in M_{l-1}, f|D|X^t in S, S = largest F_l-subspace of S_{l-1} on which X is iso.
  d_l <= dim S_{l-1}. d_l=0 computed for all 5<=l<1300.
- Thm 1.2: d_l=0 => b_l(m) <= 2m-1. Thm 5.1: b_l(m) <= 2 d_l + 2m - 1 (printed as "2(d_l+1)m-1 = 2d_l+2m-1").
- Remark after Thm 1.2: "sharp for all computed cases with l >= 29".

## BW computations (Sec. 6.1)
- Bases computed: m=1, 13<=l<1300; m=2, 13<=l<=89; m=3, 13<=l<=29; m=4, l=13.
- b_29(1,2,3)=1,3,5; b_53(1,2)=1,3; b_89(1,2)=1,3; b_1297(1)=1. b_7(m)=2m-2 (Watson), b_5=b_11=m.
- r_l(1)=R_l for all l<=1297 EXCEPT l=607: r_607(m)=R_607-1 for all m.
  (Sec 6.2 says rank drop happens when d_l>0, while also claiming d_l=0 for all l<1300: internal tension.)
- No table of b_l(m) for 13<=l<=23 is printed.

## Other sources
- FKO, Adv. Math. 229 (2012) 1586-1609, Thm 1.1/1.2 (+ Ramsey appendix Thm 7.1: Omega = ordinary part of U(l^2)
  on overconvergent half-integral weight forms; answers Mazur's question).
- Atkin–O'Brien, Trans. AMS 126 (1967): P(13^{a+2}N) == K_a P(13^a N) mod 13^a (restated Thm 1.1 of Garvan–Shomanov
  arXiv 2504.10824, 2025); Hecke conjecture mod 13^a proved by Garvan–Shomanov.
- Belmont–Lee–Musat–Trebat-Leder, Monatsh. Math. 173 (2014) 1-34 (arXiv 1510.01202): "The question of resolving
  when d_l(r) is zero is an open problem"; Sec. 5: "We conjecture that d_l(r) = 0 for all l >= r+5."
- Webb thesis (USC 2011), El-Guindy–Ghazy arXiv 2408.04462 (l-regular analogue): no sharpness/attainment results found.
