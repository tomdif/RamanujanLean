# Atkin's twisted mod-13 class: every prime Q < 500

2026-11-04. Lean: `RamanujanTau/AtkinTwisted/` (Core, Group1–4, All; 749 lines, Groups generated).
Scripts: `scripts/atkintwisted/` (`scan.py`, `crosscheck.py`, `exact_large.py`, `gen.py`, `make_table.py`,
`audit.lean`, outputs `scan500.json`, `crosscheck.json`, `exact_large.txt`, `audit.out`, `table.md`).
Imports `AtkinSporadic/`, `GaussSign/` without modifying them. Not added to the root import.

## Results and evidence levels

| Statement | Level |
|---|---|
| `AtkinTwisted.eigen_all`: for **every** prime `5 ≤ Q < 500`, `Q ≠ 13`, `F̄ = Σ_{((24N−1)/13)=−1} p(N)qᴺ (mod 13)` satisfies `T(Q²)F̄ = μ(Q)F̄` | **(1) Lean, axiom-clean** |
| 9 Atkin-type families (Q = 11, 37, 89, 167, 193, 271, 349, 401, 479), class + explicit progression | **(1)** |
| 7 Ono-type families (Q = 103, 181, 233, 311, 337, 389, 467), class + explicit progression | **(1)** |
| Every family against exact p(N) mod 13 (N ≤ 1.2·10⁷ sieve; plus FLINT's exact p(N) at the first two progression terms, N up to 6.2·10¹¹) | (4), 0 failures |

`#print axioms` (`scripts/atkintwisted/audit.lean`, 42 declarations): all `[propext, Classical.choice, Quot.sound]`.
No `sorry`, no `native_decide`, no new axiom. Kernel negative controls in the audit: the certificate is
false for the wrong eigenvalue μ = 4 at Q = 11 and at Q = 37.

## Criterion (from `Atkin13.EB`, `vanish_of_eigen`)

`T(Q²)` in weight 167 + 1/2 on the N-coordinate:
`b(N) = F(Q²N − d) + s·((24N−1)/Q)·Q¹⁶⁶·F(N) + Q³³³·F((N+d)/Q²)`, `d = (Q²−1)/24`, `s = (12/Q)((−1)/Q)`.
If `T(Q²)F̄ = μF̄`, then for `24N − 1 = Q²m`:
* `Q ∤ m`: `F(N) = (μ − s(m/Q)Q¹⁶⁶)·F(N')`, `24N'−1 = m`. **Atkin type**: `μ ≡ s ε Q¹⁶⁶ = s ε Q⁻² (mod 13)` kills the class `(m/Q) = ε`.
* `m = Qn`, `Q ∤ n`: the middle and last terms vanish, `F(N) = μ F(N')`. **Ono type**: `μ ≡ 0` kills `24N−1 = Q³n`, `Q ∤ n`.

`F(N) = p(N)` exactly when `((24N−1)/13) = −1`, which gives the `(m/13) = −1` resp. `(Qn/13) = −1` condition.

**Eigen-ness**: since `EtaHecke Q 168 1` holds for every prime Q ≥ 5 (`GaussSign.etaHecke_all`),
`T(Q²)F̄ − μF̄ = D/η` with `D ∈ S₁₆₈`, so the 15 Sturm coefficients decide it. In the scan, `F̄` is an
eigenform for **all** 93 primes `5 ≤ Q < 500`, `Q ≠ 13`. (It also holds numerically on every coefficient
the 1.2·10⁷ sieve reaches, between 49 and 480,001 coefficients per Q.) So although `η⁻¹S₁₆₈` is 14-dimensional,
the twisted series is a mod-13 Hecke eigenform. The 7-dimensional space is not an obstruction.
Atkin type occurs exactly when `μ = ±3` (9 primes), Ono type when `μ = 0` (7 primes).

## Method

`Core.lean`:
* `eigen_of_coeffs`: the Sturm step from `Atkin13.twisted_hecke`, with the prefix abstracted.
* `allOk` / `eigen_of_allOk`: one long kernel-certified prefix of `p(n) mod 13` (`PartitionPrefix.pgfPrefixG`,
  Newton inverse with packed lanes, as in `OnoWeaverMore/Core`) checked against a list of `(Q, μ)`.
  The `EtaHeckeMod` input comes from `etaHeckeMod := (GaussSign.etaHecke_all Q hQ5 168 _).toMod 13`.
* `vanish_ono`: the Ono-type corollary (new). The Atkin type reuses `Atkin13.vanish_of_eigen`.

The prefix has to reach `14Q² − d`. The groups and their kernel costs (whole-file build, M-series Mac) are:

| file | Q range | primes | prefix length | build | peak footprint |
|---|---|---|---|---|---|
| `Group1` | 5–109 | 26 | 166,335 | ~30 s | not measured |
| `Group2` | 113–241 | 24 | 813,135 | 48 s | not measured |
| `Group3` | 251–359 | 19 | 1,804,335 | 81 s | not measured |
| `Group4` | 367–499 | 23 | 3,486,015 | ~190 s | ~6 GB (footprint) |

`All.lean`: `allPairs_cover` (kernel `decide`: every prime 5 ≤ Q < 500, Q ≠ 13, is in the list) and `eigen_all`.

## Table of congruences proved (all level (1))

Progression: Atkin type `p(13Q³n + r)` from `m = 312Q·n + m₀`. Ono type `p(13Q⁴n + r)` from `n' = 312Q·n + n₀`.
"Control nonzero" counts nonzero values in the complementary class (`(m/Q) = −ε`, resp. `(Qn/13) = +1`).

| Q | μ | s | type | class (13 ∣ p(N)) | progression | Lean (class / progression) | class N≤1.2e7 checked (fail) | control nonzero | exact p at n=0,1 |
|---|---|---|---|---|---|---|---|---|---|
| 11 | 3 | -1 | Atkin ε=+1 | 24N−1 = 11²m, (m/11)=+1, (m/13)=−1 | p(17303n+237) | `G1.atkin_13_11_class` / `G1.atkin_13_11` | 20804 (0) | 19248/20808 | 0, 0 |
| 37 | 3 | +1 | Atkin ε=−1 | 24N−1 = 37²m, (m/37)=−1, (m/13)=−1 | p(658489n+6788) | `G1.atkin_13_37_class` / `G1.atkin_13_37` | 1969 (0) | 1820/1968 | 0, 0 |
| 89 | 10 | -1 | Atkin ε=−1 | 24N−1 = 89²m, (m/89)=−1, (m/13)=−1 | p(9164597n+39275) | `G1.atkin_13_89_class` / `G1.atkin_13_89` | 341 (0) | 331/351 | 0, 0 |
| 103 | 0 | +1 | Ono (μ=0) | 24N−1 = 103³n, 103∤n, (103n/13)=−1 | p(1463161453n+1866742) | `G1.ono_13_103_class` / `G1.ono_13_103` | 4 (0) | 6/7 | 0, 0 |
| 167 | 3 | -1 | Atkin ε=+1 | 24N−1 = 167²m, (m/167)=+1, (m/13)=−1 | p(60547019n+54616) | `G2.atkin_13_167_class` / `G2.atkin_13_167` | 94 (0) | 95/101 | 0, 0 |
| 181 | 0 | +1 | Ono (μ=0) | 24N−1 = 181³n, 181∤n, (181n/13)=−1 | p(13952680573n+2717798) | `G2.ono_13_181_class` / `G2.ono_13_181` | 1 (0) | 1/1 | 0, 0 |
| 193 | 3 | +1 | Atkin ε=−1 | 24N−1 = 193²m, (m/193)=−1, (m/13)=−1 | p(93457741n+72946) | `G2.atkin_13_193_class` / `G2.atkin_13_193` | 78 (0) | 68/71 | 0, 0 |
| 233 | 0 | -1 | Ono (μ=0) | 24N−1 = 233³n, 233∤n, (233n/13)=−1 | p(38314841773n+3689390) | `G2.ono_13_233_class` / `G2.ono_13_233` | 1 (0) | 0/0 | 0, 0 |
| 271 | 10 | +1 | Atkin ε=+1 | 24N−1 = 271²m, (m/271)=+1, (m/13)=−1 | p(258732643n+364145) | `G3.atkin_13_271_class` / `G3.atkin_13_271` | 36 (0) | 39/40 | 0, 0 |
| 311 | 0 | -1 | Ono (μ=0) | 24N−1 = 311³n, 311∤n, (311n/13)=−1 | p(121614373933n+91494036) | `G3.ono_13_311_class` / `G3.ono_13_311` | 0 (0) | 0/1 | 0, 0 |
| 337 | 0 | +1 | Ono (μ=0) | 24N−1 = 337³n, 337∤n, (337n/13)=−1 | p(167672930893n+74950808) | `G3.ono_13_337_class` / `G3.ono_13_337` | 0 (0) | 0/0 | 0, 0 |
| 349 | 3 | +1 | Atkin ε=−1 | 24N−1 = 349²m, (m/349)=−1, (m/13)=−1 | p(552611137n+238527) | `G3.atkin_13_349_class` / `G3.atkin_13_349` | 26 (0) | 18/20 | 0, 0 |
| 389 | 0 | -1 | Ono (μ=0) | 24N−1 = 389³n, 389∤n, (389n/13)=−1 | p(297674585533n+46600563) | `G4.ono_13_389_class` / `G4.ono_13_389` | 0 (0) | 0/0 | 0, 0 |
| 401 | 10 | -1 | Atkin ε=−1 | 24N−1 = 401²m, (m/401)=−1, (m/13)=−1 | p(838255613n+475703) | `G4.atkin_13_401_class` / `G4.atkin_13_401` | 22 (0) | 13/13 | 0, 0 |
| 467 | 0 | -1 | Ono (μ=0) | 24N−1 = 467³n, 467∤n, (467n/13)=−1 | p(618316554973n+157014993) | `G4.ono_13_467_class` / `G4.ono_13_467` | 0 (0) | 0/0 | 0, 0 |
| 479 | 3 | -1 | Atkin ε=+1 | 24N−1 = 479²m, (m/479)=+1, (m/13)=−1 | p(1428729107n+678763) | `G4.atkin_13_479_class` / `G4.atkin_13_479` | 13 (0) | 10/10 | 0, 0 |

All eigenvalues μ(Q) (T(Q²)F̄ = μF̄ mod 13), every prime 5 ≤ Q < 500, Q ≠ 13:

5:6, 7:7, 11:3, 17:7, 19:11, 23:7, 29:1, 31:6, 37:3, 41:9, 43:7, 47:4, 53:11, 59:6, 61:12, 67:9, 71:2, 73:4, 79:11, 83:7, 89:10, 97:2, 101:6, 103:0, 107:12, 109:7, 113:1, 127:6, 131:2, 137:7, 139:1, 149:11, 151:9, 157:2, 163:7, 167:3, 173:7, 179:7, 181:0, 191:12, 193:3, 197:9, 199:7, 211:1, 223:9, 227:2, 229:4, 233:0, 239:7, 241:6, 251:6, 257:6, 263:12, 269:1, 271:10, 277:6, 281:9, 283:6, 293:7, 307:9, 311:0, 313:2, 317:6, 331:11, 337:0, 347:12, 349:3, 353:9, 359:4, 367:1, 373:12, 379:9, 383:2, 389:0, 397:6, 401:10, 409:2, 419:12, 421:7, 431:4, 433:6, 439:6, 443:2, 449:7, 457:4, 461:11, 463:9, 467:0, 479:3, 487:11, 491:7, 499:6

Headline statement shapes (namespace `RamanujanTau.AtkinTwisted`):
```
theorem eigen_all (Q : ℕ) [Fact Q.Prime] (hQ5 : 5 ≤ Q) (hQ500 : Q < 500) (hQ13 : Q ≠ 13) :
    ∃ μ : ZMod 13, TT Q = C μ * Ψ 13 twPGF
theorem G4.atkin_13_479_class (N m : ℕ) (hm : 24 * N = 479 ^ 2 * m + 1) (hQ : legendreSym 479 m = 1)
    (h13 : legendreSym 13 m = -1) : 13 ∣ Fintype.card (Nat.Partition N)
theorem G4.atkin_13_479 (n : ℕ) : 13 ∣ Fintype.card (Nat.Partition (1428729107 * n + 678763))
theorem G1.ono_13_103_class (N n : ℕ) (hm : 24 * N = 103 ^ 3 * n + 1) (hQn : ¬ 103 ∣ n)
    (h13 : legendreSym 13 ((103 : ℕ) * (n : ℤ)) = -1) : 13 ∣ Fintype.card (Nat.Partition N)
theorem G1.ono_13_103 (n : ℕ) : 13 ∣ Fintype.card (Nat.Partition (1463161453 * n + 1866742))
```
`G1.atkin_13_11` reproves Atkin's `13 ∣ p(17303n+237)` through the generic path.

Build: `nice -n 10 lake build RamanujanTau.AtkinTwisted.All`, then
`nice -n 10 lake env lean scripts/atkintwisted/audit.lean`.
Numerics: `python3 scan.py p12M.bin 500 scan500.json`, `python3 crosscheck.py p12M.bin scan500.json crosscheck.json`,
`python3 exact_large.py crosscheck.json 2`. Here `p12M.bin` is `pmodM.c 12000000` from `scripts/onoweavermore/`.

## Scope and gaps

* These are the twisted-class `((24N−1)/13) = −1` analogues of the Ono–Weaver families in `OnoWeaverMore/Instances13`.
  That file covers the class `13 ∣ 24N−1` and its own Q list (59, 73, 97, …). The two families are disjoint.
* Literature: Atkin (1968) lists the twisted mod-13 congruences for Q = 11 (and others; from memory, not
  re-read). I have not checked which of Q = 89, …, 479 appear in Atkin's tables or in later lists
  (e.g. Weaver 2001, Johansson 2012 computed many such congruences). Treat "new" as unverified.
* Q ≥ 500: the method is the same. The prefix grows as 14Q², and the kernel limit `k·2^d ≤ 2^20` pentagonal
  pairs allows N up to about 1.6·10¹². Memory is the practical limit: about 6 GB at 3.5·10⁶, which
  suggests about Q ≲ 700 per file. Splitting a file by coefficient does not help, because one prefix
  must cover `14Q²`.
* A structural explanation of `μ(Q)` (the mod-13 Galois representation attached to `F̄`) was not attempted.
