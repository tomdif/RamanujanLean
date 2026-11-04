# Ono–Weaver extensions: Atkin-type primes, all `Q < 500`, and ℓ = 29, 31

Added 2026-11-04. Lean directory: `RamanujanTau/OnoWeaverMore/` (entry point `All.lean`).
Scripts: `scripts/onoweavermore/`. Builds on `RamanujanTau/AtkinSporadic/` (imported, not modified);
read `docs/ATKIN_SPORADIC_CONGRUENCES.md` first.

## Summary

* **81 congruence families proved in Lean, unconditionally, axiom-clean** (only `propext`,
  `Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`, no new axiom), for
  ℓ ∈ {13, 17, 19, 23, 29, 31} and every prime `5 ≤ Q < 500` (`Q ≠ ℓ`) for which `T(Q²)` acts on
  `G_ℓ = Σ p(ℓN − δ_ℓ) q^N` modulo ℓ by `0` (Ono type) or by `±s·Q^(λ−1)` (Atkin type).
  70 of them are new to the repo (the 11 Ono pairs of `AtkinSporadic.WeaverUnconditional` are
  re-proved inside the same framework).
  * **Ono type** `(ℓ, Q, 0)`: `ℓ ∣ p((ℓQ³n+1)/24)` for `Q ∤ n` — 30 pairs (19 new).
  * **Atkin type** `(ℓ, Q, ε)`, `ε = ±1`: `ℓ ∣ p((ℓQ²m+1)/24)` whenever `24 ∣ ℓQ²m+1` and
    `(m/Q) = ε` — 51 pairs (all new). These are progressions with modulus `ℓQ³`
    ((Q−1)/2 residue classes each), against `ℓQ⁴` for Ono's form; e.g.
    `19 ∣ p(41743n + 669)` (ℓ=19, Q=13), `17 ∣ p(206839n + 2623)` (ℓ=17, Q=23),
    `29 ∣ p(142477n + 31778)` (ℓ=29, Q=17).
* **ℓ = 29 and 31 done unconditionally** (25 pairs). The "two-dimensional" obstacle disappears:
  although `S_{ℓ−1}` is 2-dimensional, the half-integral space carrying `G_ℓ` is
  `η^(−j) S_{k'}`, `j = ℓ − 24 ∈ {5, 7}`, `k' = 16, 18`, which is **one-dimensional**
  (`S_16 = ℂΔE₄`, `S_18 = ℂΔE₆`), and the Shimura-lift eigenspace `W ⊂ M_{ℓ−3}(Γ₀(6))` is also
  one-dimensional over ℚ (PARI: `wdim.gp`; Lean: kernel certificates `DimOne40.dimOne_29/31`).
  So no 2×2 Hecke matrix is needed; the dim-1 argument of `AtkinSporadic.EigenLift` generalizes.
  (Mod ℓ, W̄ has dimension 2 at 29 and 3 at 31 — irrelevant, since the argument is in
  characteristic 0.)
* Every Q < 500 was found to be a `T(Q²)`-eigenvalue of `G_ℓ` mod ℓ (0 failures among all
  tested coefficients), as the dimension-one theory predicts.
* Literature: Weaver (Ramanujan J. 5 (2001) 53–63) treats exactly m ∈ {13,17,19,23,29,31} and
  lists 76,065 congruences as tuples `(m, ℓ, ε)`, `ε ∈ {−1,0,1}`, with modulus `mℓ^(4−|ε|)`
  (description in F. Johansson, arXiv:1205.5991, §5, which also gives Weaver's test as a single
  evaluation `p(m r_m(ℓ²−1)/24 + δ_m)` — the same coefficient `q¹` test as `okQ` here). So the
  Atkin-type families are Weaver's `ε = ±1` tuples and the Ono-type ones her `ε = 0` tuples.
  **Not checked**: the individual rows of Weaver's tables (paper not re-read); the families here
  were found and verified independently.

## Evidence levels

| Statement | Level |
|---|---|
| The 81 families in the table (`L<ℓ>.ono_ℓ_Q`, `L<ℓ>.atkin_ℓ_Q`) and 6 explicit progressions (`…_progression`) | **(1) Lean, unconditional, axiom-clean** (audit: `scripts/onoweavermore/audit.lean`, 98 `#print axioms`) |
| `T(Q²)G_ℓ ≡ νG_ℓ (mod ℓ)` for **every** prime `Q ≥ 5`, ℓ = 29, 31 (`eigen_29`, `eigen_31`) | **(1)** |
| `DimOneProp 29`, `DimOneProp 31` (W detected by `b(1)`, weights 26, 28) | **(1)** kernel certificate, 27×27 / 29×29 integer matrices |
| Formal Hecke equivariance of the lift in index `j = ℓ mod 24`, all ℓ ≥ 13 (`EquivarianceJ.lift_heckeHalfJ`) and char-0 eigen relation (`EigenLiftJ.eigen_char0J`) | **(1)** |
| Completeness of the list (no other `Q < 500` of either type at these ℓ) | (4) numerical (`scan.py`, exact p(n) mod ℓ, n ≤ 1.2·10⁷) |
| Every congruence against actual `p(n)`: direct check of the progression classes (7,850 values, 0 failures) and of the eigen-relation on all available coefficients (0 failures) | (4) numerical |

Negative controls (in the audit, kernel-checked): the certificate is **false** for the wrong
sign (ℓ=17, Q=23, ε=+1; ℓ=29, Q=17, ε=+1) and for non-hit primes (ℓ=17, Q=43; ℓ=31, Q=43), and
true with the same prefix parameters for the correct sign.

## Mechanism

Let `G = Σ_N p(ℓN − δ) q^N`, `λ = (ℓ−1) − (ℓ+1)/2 = (ℓ−3)/2`, `s = (12/Q)((−1)^λ/Q)`, and
`T(Q²)` on the N-coordinate (`heckeHalf Q ℓ λ s`):
`b(N) = a(Q²N − d) + s·((24N−ℓ)/Q)·Q^(λ−1)·a(N) + Q^(2λ−1)·a((N+d)/Q²)`, `d = (Q²−1)ℓ/24`.

1. **Eigen-relation.** `T(Q²)G ≡ μG (mod ℓ)`.
   * ℓ ≤ 23: from `EtaHeckeMod ℓ Q (ℓ−1) ℓ` (= `EigenLift.etaHeckeMod_ℓ`, all Q) the image is
     `Ψ(f'P^ℓ)`; with one coefficient identity `b(1) = μ a(1)`, the difference
     `f' − μf ∈ S_{ℓ−1}` has vanishing `q⁰, q¹` coefficients, so is ≡ 0 by Sturm
     (`Core.eigen_of_etaHecke`).
   * ℓ = 29, 31: `G ≡ c·Δ²E·P^ℓ = c·X·coordOf ℓ (ΔE)` (seeds `Cert29.seed`, `Cert31.seed`,
     `Δ·P²⁴ = X`). In characteristic 0, `T(Q²)` in index `j = ℓ − 24` is exactly scalar on
     `coordOf ℓ (ΔE)` (`eigen_char0J`: all lifts `S_t` lie in the one-dimensional `W`, `T_Q` is
     scalar on `W`, equivariance + triangularity; `a(1) = 1`), and `X·` intertwines index `j`
     with index `j+24 = ℓ` (`heckeHalf_X_mul`). Then the eigenvalue is read off at `N₀ = 2`
     (the first nonzero coefficient of G) (`eigen_of_exists`).
2. **Certificate.** `okQ` evaluates `b(N₀)` and `ε·s·Q^(λ−1)·a(N₀)` from a packed prefix of
   `p(n) mod ℓ` (`PartitionPrefix.pgfPrefixG`, pentagonal series + certified Newton inverse) with
   Legendre symbols by Euler's criterion; `allOk` checks a whole list of pairs against **one**
   prefix per ℓ (sizes: 1,367,087 at 13; 929,634 at 17; 735,305 at 19; 169,857 at 23;
   4,505,551 at 29; 4,707,187 at 31). `allOk_sound` turns it into the coefficient identity.
   Each `Instances<ℓ>.lean` compiles in under a minute.
3. **Reading coefficients** (`Core.vanish_core`). For `24N − ℓ = m`, `Q² ∤ m`:
   `a(Q²N − d) = (μ − s(m/Q)Q^(λ−1))·a(N)`, and `ℓ(Q²N−d) − δ = (ℓQ²m+1)/24`. Atkin type:
   `μ = εsQ^(λ−1)` kills `(m/Q) = ε` (`atkin_of_eigen`); Ono type: `μ = 0`, `m = Qn`
   (`ono_of_eigen`).

## Lean modules (`RamanujanTau/OnoWeaverMore/`)

| file | content |
|---|---|
| `Core.lean` | `TT`, `muE`, `vanish_core`, **`atkin_of_eigen`**, **`ono_of_eigen`**, `eigen_of_etaHecke`, certificate `gv/Wc/Wt/okQ/allOk`, `allOk_sound` |
| `LiftEquivJ.lean` | `EquivarianceJ.lift_heckeHalfJ`: `S_t(T(Q²)A) = χ₁₂(Q)T_Q(S_tA)` with index `jj ℓ`, every ℓ ≥ 13 |
| `LevelSix40.lean` | weight-two series A, B, C certified through `q⁴⁰`; `evenSeries_coeff40` |
| `DimOne40.lean` | `DimCert` at precision 40, soundness ⇒ `AtkinSporadic.DimOne.DimOneProp` |
| `DimOneData2931.lean` (generated, `gen_dimone2931.py`) | **`dimOne_29`, `dimOne_31`** |
| `EigenLiftJ.lean` | `eigen_char0J` (char-0 eigen relation, reference lift `t₀ = 24 − jj ℓ`) |
| `Eigen2931.lean` | `heckeHalf_X_mul`, `eigen_big`, **`eigen_29`, `eigen_31`**, `eigen_of_exists` |
| `Instances13/17/19/23/29/31.lean` (generated, `gen_instances.py`) | `allℓ` kernel certificate; one theorem per pair; explicit progressions |
| `All.lean` | imports all instances |

Headline statements (namespace `RamanujanTau.OnoWeaverMore`):
```
theorem L19.atkin_19_13 (m : ℕ) (hm : 24 ∣ 19 * 13 ^ 2 * m + 1) (hQm : legendreSym 13 m = (-1)) :
    19 ∣ Fintype.card (Nat.Partition ((19 * 13 ^ 2 * m + 1) / 24))
theorem L19.atkin_19_13_progression (n : ℕ) : 19 ∣ Fintype.card (Nat.Partition (41743 * n + 669))
theorem L29.atkin_29_17_progression (n : ℕ) : 29 ∣ Fintype.card (Nat.Partition (142477 * n + 31778))
theorem L29.ono_29_331 (n : ℕ) (hn : ¬ 331 ∣ n) (h : 24 ∣ 29 * 331 ^ 3 * n + 1) :
    29 ∣ Fintype.card (Nat.Partition ((29 * 331 ^ 3 * n + 1) / 24))
theorem eigen_29 (Q : ℕ) [Fact Q.Prime] (hQ5 : 5 ≤ Q) :
    ∃ ν : ZMod 29, TT 29 Q (Ψ 29 (Pser 29 1)) = C ν * Ψ 29 (Pser 29 1)
```

Build and audit:
```
nice -n 10 lake build RamanujanTau.OnoWeaverMore.All
nice -n 10 lake env lean scripts/onoweavermore/audit.lean     # 98 × [propext, Classical.choice, Quot.sound]
```
Numerics: `cc -O3 -o pmodM scripts/onoweavermore/pmodM.c && ./pmodM 12000000 p.bin` (~1 min),
`python3 scan.py p.bin 500 scan500.json`, `python3 crosscheck.py p.bin scan500.json`,
`gp -q wdim.gp` (dim W), `python3 dimcert2931.py`.

## Table of congruences proved

ε = 0: Ono type, `ℓ ∣ p((ℓQ³n+1)/24)` for `Q ∤ n` (needs `24 ∣ ℓQ³n+1`). ε = ±1: Atkin type.
"eigen coeffs checked": number of coefficients N on which `T(Q²)G ≡ μG` was verified on actual
p(n) mod ℓ (n ≤ 1.2·10⁷). "direct checks": number of n ≤ 1.2·10⁷ in the congruence classes
themselves (0 for large Q, where ℓQ³ > 2.9·10⁸; those rest on the eigen-relation check and the
Lean proof).

| ℓ | Q | ε | statement | Lean theorem | new? | eigen coeffs checked | direct p(n) checks (fail) |
|---|---|---|---|---|---|---|---|
| 13 | 59 | +0 | 13 ∣ p((13·59³n+1)/24), 59∤n | `L13.ono_13_59` | existing | 266 | 5 (0) |
| 13 | 73 | +0 | 13 ∣ p((13·73³n+1)/24), 73∤n | `L13.ono_13_73` | existing | 174 | 2 (0) |
| 13 | 97 | +1 | 13 ∣ p((13·97²m+1)/24), (m/97)=+1 | `L13.atkin_13_97` | new | 99 | 49 (0) |
| 13 | 103 | -1 | 13 ∣ p((13·103²m+1)/24), (m/103)=-1 | `L13.atkin_13_103` | new | 88 | 45 (0) |
| 13 | 109 | +1 | 13 ∣ p((13·109²m+1)/24), (m/109)=+1 | `L13.atkin_13_109` | new | 79 | 41 (0) |
| 13 | 131 | +0 | 13 ∣ p((13·131³n+1)/24), 131∤n | `L13.ono_13_131` | new | 55 | 1 (0) |
| 13 | 167 | +0 | 13 ∣ p((13·167³n+1)/24), 167∤n | `L13.ono_13_167` | new | 34 | 0 (0) |
| 13 | 191 | -1 | 13 ∣ p((13·191²m+1)/24), (m/191)=-1 | `L13.atkin_13_191` | new | 26 | 13 (0) |
| 13 | 241 | -1 | 13 ∣ p((13·241²m+1)/24), (m/241)=-1 | `L13.atkin_13_241` | new | 17 | 9 (0) |
| 13 | 251 | -1 | 13 ∣ p((13·251²m+1)/24), (m/251)=-1 | `L13.atkin_13_251` | new | 16 | 7 (0) |
| 13 | 283 | -1 | 13 ∣ p((13·283²m+1)/24), (m/283)=-1 | `L13.atkin_13_283` | new | 13 | 3 (0) |
| 13 | 389 | +0 | 13 ∣ p((13·389³n+1)/24), 389∤n | `L13.ono_13_389` | new | 7 | 0 (0) |
| 13 | 397 | +1 | 13 ∣ p((13·397²m+1)/24), (m/397)=+1 | `L13.atkin_13_397` | new | 7 | 5 (0) |
| 13 | 409 | -1 | 13 ∣ p((13·409²m+1)/24), (m/409)=-1 | `L13.atkin_13_409` | new | 7 | 4 (0) |
| 13 | 433 | +0 | 13 ∣ p((13·433³n+1)/24), 433∤n | `L13.ono_13_433` | new | 6 | 0 (0) |
| 13 | 439 | -1 | 13 ∣ p((13·439²m+1)/24), (m/439)=-1 | `L13.atkin_13_439` | new | 6 | 2 (0) |
| 13 | 463 | +1 | 13 ∣ p((13·463²m+1)/24), (m/463)=+1 | `L13.atkin_13_463` | new | 5 | 2 (0) |
| 13 | 479 | +0 | 13 ∣ p((13·479³n+1)/24), 479∤n | `L13.ono_13_479` | new | 5 | 0 (0) |
| 17 | 23 | -1 | 17 ∣ p((17·23²m+1)/24), (m/23)=-1 | `L17.atkin_17_23` | new | 1336 | 639 (0) |
| 17 | 41 | +0 | 17 ∣ p((17·41³n+1)/24), 41∤n | `L17.ono_17_41` | existing | 421 | 10 (0) |
| 17 | 67 | +1 | 17 ∣ p((17·67²m+1)/24), (m/67)=+1 | `L17.atkin_17_67` | new | 158 | 74 (0) |
| 17 | 89 | +0 | 17 ∣ p((17·89³n+1)/24), 89∤n | `L17.ono_17_89` | existing | 90 | 1 (0) |
| 17 | 103 | +0 | 17 ∣ p((17·103³n+1)/24), 103∤n | `L17.ono_17_103` | existing | 68 | 1 (0) |
| 17 | 107 | -1 | 17 ∣ p((17·107²m+1)/24), (m/107)=-1 | `L17.atkin_17_107` | new | 63 | 33 (0) |
| 17 | 127 | -1 | 17 ∣ p((17·127²m+1)/24), (m/127)=-1 | `L17.atkin_17_127` | new | 45 | 26 (0) |
| 17 | 151 | -1 | 17 ∣ p((17·151²m+1)/24), (m/151)=-1 | `L17.atkin_17_151` | new | 32 | 17 (0) |
| 17 | 191 | -1 | 17 ∣ p((17·191²m+1)/24), (m/191)=-1 | `L17.atkin_17_191` | new | 21 | 11 (0) |
| 17 | 293 | -1 | 17 ∣ p((17·293²m+1)/24), (m/293)=-1 | `L17.atkin_17_293` | new | 9 | 6 (0) |
| 17 | 359 | -1 | 17 ∣ p((17·359²m+1)/24), (m/359)=-1 | `L17.atkin_17_359` | new | 7 | 3 (0) |
| 17 | 373 | +1 | 17 ∣ p((17·373²m+1)/24), (m/373)=+1 | `L17.atkin_17_373` | new | 6 | 4 (0) |
| 17 | 433 | +0 | 17 ∣ p((17·433³n+1)/24), 433∤n | `L17.ono_17_433` | new | 5 | 0 (0) |
| 19 | 13 | -1 | 19 ∣ p((19·13²m+1)/24), (m/13)=-1 | `L19.atkin_19_13` | new | 3738 | 1724 (0) |
| 19 | 23 | -1 | 19 ∣ p((19·23²m+1)/24), (m/23)=-1 | `L19.atkin_19_23` | new | 1195 | 572 (0) |
| 19 | 61 | +1 | 19 ∣ p((19·61²m+1)/24), (m/61)=+1 | `L19.atkin_19_61` | new | 171 | 84 (0) |
| 19 | 97 | -1 | 19 ∣ p((19·97²m+1)/24), (m/97)=-1 | `L19.atkin_19_97` | new | 68 | 33 (0) |
| 19 | 101 | +0 | 19 ∣ p((19·101³n+1)/24), 101∤n | `L19.ono_19_101` | existing | 63 | 1 (0) |
| 19 | 103 | +1 | 19 ∣ p((19·103²m+1)/24), (m/103)=+1 | `L19.atkin_19_103` | new | 61 | 32 (0) |
| 19 | 109 | +1 | 19 ∣ p((19·109²m+1)/24), (m/109)=+1 | `L19.atkin_19_109` | new | 54 | 29 (0) |
| 19 | 137 | +1 | 19 ∣ p((19·137²m+1)/24), (m/137)=+1 | `L19.atkin_19_137` | new | 35 | 19 (0) |
| 19 | 191 | +0 | 19 ∣ p((19·191³n+1)/24), 191∤n | `L19.ono_19_191` | new | 19 | 0 (0) |
| 19 | 193 | +1 | 19 ∣ p((19·193²m+1)/24), (m/193)=+1 | `L19.atkin_19_193` | new | 18 | 7 (0) |
| 19 | 211 | +0 | 19 ∣ p((19·211³n+1)/24), 211∤n | `L19.ono_19_211` | new | 15 | 0 (0) |
| 19 | 269 | -1 | 19 ∣ p((19·269²m+1)/24), (m/269)=-1 | `L19.atkin_19_269` | new | 10 | 4 (0) |
| 19 | 271 | +1 | 19 ∣ p((19·271²m+1)/24), (m/271)=+1 | `L19.atkin_19_271` | new | 10 | 4 (0) |
| 19 | 337 | +0 | 19 ∣ p((19·337³n+1)/24), 337∤n | `L19.ono_19_337` | new | 7 | 0 (0) |
| 19 | 349 | +0 | 19 ∣ p((19·349³n+1)/24), 349∤n | `L19.ono_19_349` | new | 6 | 0 (0) |
| 19 | 431 | -1 | 19 ∣ p((19·431²m+1)/24), (m/431)=-1 | `L19.atkin_19_431` | new | 5 | 1 (0) |
| 23 | 5 | +0 | 23 ∣ p((23·5³n+1)/24), 5∤n | `L23.ono_23_5` | existing | 20871 | 3339 (0) |
| 23 | 19 | +0 | 23 ∣ p((23·19³n+1)/24), 19∤n | `L23.ono_23_19` | existing | 1447 | 72 (0) |
| 23 | 37 | +0 | 23 ∣ p((23·37³n+1)/24), 37∤n | `L23.ono_23_37` | existing | 383 | 9 (0) |
| 23 | 47 | +0 | 23 ∣ p((23·47³n+1)/24), 47∤n | `L23.ono_23_47` | existing | 238 | 4 (0) |
| 23 | 67 | +0 | 23 ∣ p((23·67³n+1)/24), 67∤n | `L23.ono_23_67` | existing | 118 | 1 (0) |
| 23 | 107 | -1 | 23 ∣ p((23·107²m+1)/24), (m/107)=-1 | `L23.atkin_23_107` | new | 47 | 19 (0) |
| 23 | 179 | +0 | 23 ∣ p((23·179³n+1)/24), 179∤n | `L23.ono_23_179` | new | 18 | 0 (0) |
| 23 | 239 | +0 | 23 ∣ p((23·239³n+1)/24), 239∤n | `L23.ono_23_239` | new | 11 | 0 (0) |
| 23 | 353 | +0 | 23 ∣ p((23·353³n+1)/24), 353∤n | `L23.ono_23_353` | new | 6 | 0 (0) |
| 23 | 421 | -1 | 23 ∣ p((23·421²m+1)/24), (m/421)=-1 | `L23.atkin_23_421` | new | 4 | 0 (0) |
| 29 | 17 | -1 | 29 ∣ p((29·17²m+1)/24), (m/17)=-1 | `L29.atkin_29_17` | new | 1434 | 673 (0) |
| 29 | 41 | +1 | 29 ∣ p((29·41²m+1)/24), (m/41)=+1 | `L29.atkin_29_41` | new | 248 | 120 (0) |
| 29 | 137 | +1 | 29 ∣ p((29·137²m+1)/24), (m/137)=+1 | `L29.atkin_29_137` | new | 24 | 15 (0) |
| 29 | 139 | +1 | 29 ∣ p((29·139²m+1)/24), (m/139)=+1 | `L29.atkin_29_139` | new | 23 | 10 (0) |
| 29 | 193 | +1 | 29 ∣ p((29·193²m+1)/24), (m/193)=+1 | `L29.atkin_29_193` | new | 13 | 6 (0) |
| 29 | 227 | +1 | 29 ∣ p((29·227²m+1)/24), (m/227)=+1 | `L29.atkin_29_227` | new | 10 | 3 (0) |
| 29 | 229 | -1 | 29 ∣ p((29·229²m+1)/24), (m/229)=-1 | `L29.atkin_29_229` | new | 10 | 4 (0) |
| 29 | 331 | +0 | 29 ∣ p((29·331³n+1)/24), 331∤n | `L29.ono_29_331` | new | 5 | 0 (0) |
| 29 | 347 | +1 | 29 ∣ p((29·347²m+1)/24), (m/347)=+1 | `L29.atkin_29_347` | new | 5 | 2 (0) |
| 29 | 367 | -1 | 29 ∣ p((29·367²m+1)/24), (m/367)=-1 | `L29.atkin_29_367` | new | 5 | 2 (0) |
| 29 | 431 | +1 | 29 ∣ p((29·431²m+1)/24), (m/431)=+1 | `L29.atkin_29_431` | new | 4 | 1 (0) |
| 29 | 439 | -1 | 29 ∣ p((29·439²m+1)/24), (m/439)=-1 | `L29.atkin_29_439` | new | 4 | 1 (0) |
| 29 | 443 | -1 | 29 ∣ p((29·443²m+1)/24), (m/443)=-1 | `L29.atkin_29_443` | new | 4 | 2 (0) |
| 31 | 101 | -1 | 31 ∣ p((31·101²m+1)/24), (m/101)=-1 | `L31.atkin_31_101` | new | 40 | 19 (0) |
| 31 | 107 | +0 | 31 ∣ p((31·107³n+1)/24), 107∤n | `L31.ono_31_107` | new | 36 | 0 (0) |
| 31 | 179 | -1 | 31 ∣ p((31·179²m+1)/24), (m/179)=-1 | `L31.atkin_31_179` | new | 14 | 8 (0) |
| 31 | 181 | -1 | 31 ∣ p((31·181²m+1)/24), (m/181)=-1 | `L31.atkin_31_181` | new | 14 | 6 (0) |
| 31 | 193 | +1 | 31 ∣ p((31·193²m+1)/24), (m/193)=+1 | `L31.atkin_31_193` | new | 12 | 5 (0) |
| 31 | 229 | +0 | 31 ∣ p((31·229³n+1)/24), 229∤n | `L31.ono_31_229` | new | 9 | 0 (0) |
| 31 | 239 | -1 | 31 ∣ p((31·239²m+1)/24), (m/239)=-1 | `L31.atkin_31_239` | new | 9 | 4 (0) |
| 31 | 271 | -1 | 31 ∣ p((31·271²m+1)/24), (m/271)=-1 | `L31.atkin_31_271` | new | 7 | 2 (0) |
| 31 | 283 | +0 | 31 ∣ p((31·283³n+1)/24), 283∤n | `L31.ono_31_283` | new | 7 | 0 (0) |
| 31 | 383 | +0 | 31 ∣ p((31·383³n+1)/24), 383∤n | `L31.ono_31_383` | new | 4 | 0 (0) |
| 31 | 463 | +0 | 31 ∣ p((31·463³n+1)/24), 463∤n | `L31.ono_31_463` | new | 4 | 0 (0) |

## Scope notes / not done

* Q ≥ 500 not scanned; the method is the same (one longer prefix per ℓ: index ≈ 6Q² at ℓ = 13,
  ≈ 23Q² at ℓ = 29).
* ℓ = 37, 41, … : `S_{k'}` and `W` become higher-dimensional; not attempted.
* Atkin's twisted j = 1 case (`AtkinSporadic.atkin_13`, `EtaHeckeMod 13 11 168 1`) is untouched.
* The root `RamanujanTau.lean`, README, STATUS, RESULTS were not edited (per instructions).
