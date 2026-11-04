> **Update (2026-11-04):** `atkin_13` is now unconditional: `Atkin13.atkin_13_unconditional`, from `HalfHecke.etaHecke_11_168` (explicit T(Q²) on η⁻¹S_k; see [HALF_INTEGRAL_HECKE](HALF_INTEGRAL_HECKE.md)). The Ono–Weaver families are extended in [ONO_WEAVER_EXTENSIONS](ONO_WEAVER_EXTENSIONS.md).

# Atkin's sporadic congruence modulo 13 and the Ono–Weaver congruences

Updated 2026-11-03 (third pass: Ono–Weaver now unconditional). Lean directory: `RamanujanTau/AtkinSporadic/`. Scripts: `scripts/atkinsporadic/`.

## Summary of evidence levels

| Statement | Level |
|---|---|
| `Σ_{((24N−1)/13)=−1} p(N) qᴺ ≡ g·Σp(n)qⁿ (mod 13)` with `g ∈ S₁₆₈(SL₂ℤ)` integral (`Twist13.twisted_eq`) | **(1) Lean, axiom-clean, unconditional** |
| `Σ_m p(ℓm−δ_ℓ) qᵐ ≡ c_ℓ f_ℓ·(Σp(n)qⁿ)^ℓ (mod ℓ)`, ℓ = 13,17,19,23 (`Weaver.Pser_eq` + existing `BoylanWebb.CertX.eigen`) | **(1) Lean, unconditional** |
| Kernel certificates `chk11`, `chk37`, `chk_ℓ_Q` (first coefficients of `T(Q²)F − μF` vanish mod ℓ) | **(1) Lean, unconditional** (kernel `decide`) |
| **Atkin: `13 ∣ p(17303n + 237)` for all n** (`Atkin13.atkin_13`) | **(2) Lean, conditional on `EtaHeckeMod 13 11 168 1`** |
| `13 ∣ p(N)` whenever `24N−1 = 11²m`, `(m/11)=1`, `(m/13)=−1` (30 classes mod 17303) (`atkin_13_class`) | (2), same hypothesis |
| `13 ∣ p(N)` whenever `24N−1 = 37²m`, `(m/37)=−1`, `(m/13)=−1` (`atkin_13_Q37_class`) | (2), `EtaHecke 37 168 1` |
| Ono: `13 ∣ p(13·59⁴n + 111247)` (`Weaver.ono_13_unconditional`), and `p((13·Q³n+1)/24) ≡ 0` for Q = 59, 73, `Q ∤ n` | **(1) Lean, axiom-clean, unconditional** (third pass) |
| Weaver: `17 ∣ p(48037937n + 1122838)` (`Weaver.weaver_17_unconditional`); `p((17Q³n+1)/24) ≡ 0 (mod 17)` for Q = 41, 89, 103 | **(1) unconditional** |
| `p((19·101³n+1)/24) ≡ 0 (mod 19)`, `101 ∤ n` (`ono_19_101_unconditional`) | **(1) unconditional** |
| `p((23Q³n+1)/24) ≡ 0 (mod 23)` for Q = 5, 19, 37, 47, 67, `Q ∤ n` (`ono_23_Q_unconditional`); e.g. `23 ∣ p(14375s + r)`, r ∈ {3474, 6349, 9224, 12099} | **(1) unconditional** |
| `EtaHeckeMod ℓ Q (ℓ−1) ℓ` for ℓ ∈ {13,17,19,23} and **every** prime Q ≥ 5 (`EigenLift.etaHeckeMod_ℓ`); char-0 form `a(1)·T(Q²)(a/η^ℓ) = ν·(a/η^ℓ)` (`EigenLift.eigen_char0`) | **(1) Lean, axiom-clean** |
| `EtaHecke`/`EtaHeckeMod` for the twisted Atkin case (k=168, j=1) | **(3) classical theorem, not formalized**; (4) checked numerically |
| All congruences above against actual `p(N) mod ℓ`, N ≤ 3·10⁶ | (4) numerical, 0 failures |

All 23 audited declarations depend only on `propext`, `Classical.choice`, `Quot.sound`
(`scripts/atkinsporadic/audit.lean`); no `sorry`, no new axiom, no `native_decide`.
Negative controls in the audit: the certificates are *false* for a wrong eigenvalue (μ = 4 at
Q = 11, 37) and for non-vanishing primes (ℓ = 13, Q = 61; ℓ = 17, Q = 43).

## Statement check (before formalizing)

`scripts/atkinsporadic/verify_atkin13.py`, `verify_all.py` (C helper `pmod.c`, exact p(N) mod ℓ):

* `p(17303n + 237) ≡ 0 (mod 13)`: all 173 terms with N ≤ 3·10⁶ vanish. `24·237 − 1 = 5687 = 11²·47`,
  `47 ≡ 3 (mod 11)` (a square), `47 ≡ 8 (mod 13)` (a non-square). The progression is **not** in the
  class `13 ∣ 24N − 1`; it lies in the twisted class `((24N−1)/13) = −1`.
* Full class: for `24N − 1 = 121m`, `11 ∤ m`, p(N) ≡ 0 mod 13 in all 5,200 cases with
  `(m/11)=1, (m/13)=−1`; the other three sign classes are nonzero ~93% of the time (control).
* Each Ono–Weaver instance: 0 failures (e.g. ℓ=23, Q=5: 835 cases; ℓ=13, Q=37 twisted: 488 cases).

## Mechanism

**Twisted class (Atkin).** Write `P = Σp(n)qⁿ`, `E = ∏(1−qⁿ)`. Euler's criterion gives the twist as
`τ(N) = 7((24N−1)¹² − (24N−1)⁶)` in 𝔽₁₃. Since `P·E¹⁶⁹ = E¹⁶⁸` and `E¹⁶⁹ ≡ E(q¹⁶⁹)` is supported on
multiples of 13, the twist commutes with `E¹⁶⁹`; on `q⁷E¹⁶⁸ = Δ⁷` it equals
`7(24¹²θ¹² − 24⁶θ⁶)`, because `24·7 ≡ −1`. By the repo's mod-ℓ theta operator on level-one forms
(`FormBar.theta_iter`), this is a reduced form of weight 252; it vanishes to order 8 (the `q⁷`
term is killed since `(−1/13) = +1`), so it is `Δ⁸·K` with K of weight 156 (`div_Delta_pow`), lifted
to ℤ (`lift_iso`). Hence `twPGF ≡ q E²³ K = (ΔK)·P`: the twisted series is the reduction of
`G/η`, `G = ΔK ∈ S₁₆₈` — Ahlgren–Ono's half-integral weight form, here at level one. (Numerically
the filtration of K is 72, so G could be taken in S₈₄.)

Weight-167/2 Hecke operator `T(Q²)` on `G/η` (index `m = 24N − 1`):
`b(m) = a(Q²m) + χ₁₂(Q)((−1)^λ m/Q)Q^{λ−1}a(m) + Q^{2λ−1}a(m/Q²)`, λ = 167. Given that `T(Q²)` maps
`η^{−1}S₁₆₈` into itself (`EtaHecke Q 168 1`), `T(Q²)F − μF = D/η` with D ∈ S₁₆₈; Sturm's bound mod 13
(`BoylanWebb.sturm`, 15 coefficients) and a kernel computation of `p(N) mod 13` for N < 1700
(`PartitionPrefix.pgfPrefix`) give `D ≡ 0`, i.e. `T(121)F ≡ 3F`. For `11 ∤ m` this reads
`a(121m) ≡ (3 + 10·(m/11)) a(m)`, which vanishes when `(m/11) = 1`. Same at Q = 37 with μ = 3 and
`(m/37) = −1` (Atkin-type, sign reversed).

**Class 13 ∣ 24N−1 etc. (Ono, Weaver).** `U_ℓ(Δ^δ) ≡ c f_ℓ` (existing unconditional certificates)
gives `Σ p(ℓm−δ)qᵐ ≡ c f_ℓ P^ℓ`, i.e. the reduction of `f_ℓ/η^ℓ ∈ S_{(ℓ−2)/2}(SL₂ℤ, ν_η^{−ℓ})`
(η¹¹, η⁷E₄, η⁵E₆, ηE₄E₆). Given `EtaHecke Q (ℓ−1) ℓ`, Sturm (2 coefficients) and one partition value
mod ℓ show `T(Q²)` kills it mod ℓ; then `a(Q³n) ≡ 0` for `Q ∤ n`, Ono's form.

## Lean modules and headline theorems

* `AtkinSporadic/HalfHecke.lean`: `heckeHalf` (the operator on q-series over any ring),
  `map_heckeHalf`, `heckeSign`, **`EtaHecke`** (the hypothesis), `legendreSym_val` (Euler's criterion).
* `AtkinSporadic/Twist13.lean`: `twPGF`, `tau_eq`, `tw_mul_of_support`, `X7_tw`, **`twisted_eq`**.
* `AtkinSporadic/Atkin13.lean`: `chk`, `twisted_hecke`, `vanish_of_eigen` (generic in Q).
* `AtkinSporadic/Atkin13Main.lean`: `chk11`, `eigen11`, **`atkin_13`**, `atkin_13_class`,
  `chk37`, `atkin_13_Q37_class`.
* `AtkinSporadic/Weaver.lean`: `Pser_eq`, `wchk`, `weaver_index` (generic in ℓ ≤ 23, Q).
* `AtkinSporadic/WeaverMain.lean` (generated by `gen_weaver_main.py`): `ono_ℓ_Q` for 11 pairs,
  **`ono_13`**, **`weaver_17`**.

Exact headline statement:
```
theorem atkin_13 (H : EtaHecke 11 168 1) (n : ℕ) :
    13 ∣ Fintype.card (Nat.Partition (17303 * n + 237))
```
`EtaHecke Q k j` says: for every integer q-series `a` that is the q-expansion of a level-one
cusp form of weight k (`BoylanWebb.IntForm k a`, constant term 0) there is another such `a'` with
`heckeHalf Q j λ s (a·P^j) = a'·P^j`, λ = k − (j+1)/2, s = (12/Q)((−1)^λ/Q).

Builds: each module via `lake build RamanujanTau.AtkinSporadic.<File>`; kernel certificates take
seconds (largest prefix: 52,604 partition numbers mod 17). Not added to the root import.

## The gap: `EtaHecke`

`EtaHecke` is the statement that `T(Q²)` preserves `S_{k−j/2}(SL₂(ℤ), ν_η^{−j}) = η^{−j}S_k` with
integral q-expansions. It is classical (Shimura's theory of half-integral weight Hecke operators,
applied to `F(24z)` on Γ₀(576) with character χ₁₂; for η-multipliers on SL₂(ℤ) see Yang, Nagoya
Math. J. 215 (2014), and Knopp, *Modular Functions in Analytic Number Theory*, Ch. 4), and is the
input used by Atkin, Ono and Weaver. It is **not** formalized: Mathlib has no half-integral weight
forms and the repo only has the explicit Shimura *lift* (`ThetaLift.gen_modular`), not the Hecke
operator. Numerical support (`hecke_check.gp`, `hecke_check_modp.gp`): the coefficient formula and
sign were checked exactly for `η²³` (Q = 5, 7, 11) and for the 7-dimensional `η^{−1}S₈₄` at Q = 11
(17 coefficients each, opposite sign fails), and modulo a 61-bit prime for (k=22, j=23, Q=5)
(41 coefficients, consistent). The mod-p run (`hecke_check_modp.gp`, 12 min) also confirmed
(k=168, j=1, Q=11: dim 14, 31 coefficients), (k=168, j=1, Q=37: dim 14, 21 coefficients),
(k=12, j=13, Q=59) and (k=16, j=17, Q=41) (9 coefficients each): all consistent. The remaining
instances used ((13,73), (17,89), (17,103), (19,101), (23,19..67)) were not run.

What finishing would take: a Lean construction of `T(Q²)` on functions with the η-multiplier
system (double coset `Γ diag(1,Q²) Γ` with explicit multiplier values, which needs the general
η-transformation formula — the repo has `ThetaLift/EtaMultiplier.lean` for part of it — and the
quadratic Gauss sum evaluation that produces the `(m/Q)` term), plus the q-expansion formula.
Estimated: a substantial project (weeks), independent of the finite parts done here. A possible
shortcut is a Hecke-equivariance argument through the already-formalized Shimura lift, but that
needs a converse (lifts in a T_Q-eigenspace ⇒ the form is a T(Q²)-eigenform), which is not
available either.

## Scope notes

* For 17 ≤ ℓ ≤ 23 the *twisted* class `((24N−1)/ℓ) = −(−1/ℓ)` is **not** a Hecke eigenform mod ℓ
  (`scan_primes.py`: no single μ), so Atkin's twisted mechanism is special to 13 here; the
  Ono–Weaver class works for 13 ≤ ℓ ≤ 23 because `S_{ℓ−1}` is one-dimensional. ℓ = 29, 31 were not
  attempted (two-dimensional S_{ℓ−1}; would need a 2×2 Hecke computation and a new certificate shape).
* `scan_primes.py` / `weaver_scan.gp` also list Atkin-type primes in the Ono–Weaver class
  (ℓ=17: Q=23, 67, 107; ℓ=19: Q=13, 23, 61, …), not formalized; they would need the `(m/Q)` variant
  of `weaver_index`.
* Literature (from memory, matched numerically, not re-read): Atkin, Proc. LMS (3) 18 (1968) 563–576;
  Ono, Ann. Math. 151 (2000) 293–307 (the 59⁴·13 example); Weaver, Ramanujan J. 5 (2001) 53–63
  (the 17·41⁴ example); Ahlgren–Ono, PNAS 98 (2001). Whether the ℓ = 23, Q = 5 congruence
  (modulus 14375) appears in Weaver's/Atkin's tables was not checked.

## Update: weaker hypothesis, and the Shimura-lift route (2026-11-03, second pass)

**Weaker hypothesis now used.** All congruence theorems take `EtaHeckeMod ℓ Q k j` (stability of
`η^{−j}S_k` under `T(Q²)` only modulo ℓ, only for the instance used), not `EtaHecke`.
`EtaHecke.toMod` (axiom-clean) shows the classical statement implies it. E.g.
`atkin_13 : EtaHeckeMod 13 11 168 1 → ∀ n, 13 ∣ p(17303n+237)`;
`ono_13 : EtaHeckeMod 13 59 12 13 → …`; `weaver_17 : EtaHeckeMod 17 41 16 17 → …`.

**Numerical confirmation of every instance used** (level (4)):
* Twisted class, mod a 61-bit prime: `(Q,k,j) = (11,168,1)` (dim 14, 31 coefficients) and
  `(37,168,1)` (dim 14, 21 coefficients): consistent. Mod 13, on actual partitions: `T(121)F̄ = 3F̄`
  and `T(37²)F̄ = 3F̄` for all tested N ≤ 2·10⁵ (`eigen_mod.py`).
* Ono–Weaver class, mod ℓ on actual partitions (`check_instances_modl.py`, p(N) for N ≤ 4·10⁶):
  `T(Q²)` kills `Σp(ℓm−δ)qᵐ` on every tested coefficient for all 11 pairs (between 21 coefficients at
  (19,101) and 6,957 at (23,5); 0 failures). Since `η^{−ℓ}S_{ℓ−1}` is one-dimensional, this is the
  mod-ℓ content of each `EtaHeckeMod ℓ Q (ℓ−1) ℓ`. Also mod a 61-bit prime: (13,59), (17,41), (23,5).

**Shimura-lift route: assessment.**

1. *Formal Hecke equivariance holds exactly*: with the repo's lift
   `genLift j λ t` (`A_t(n) = Σ_{de=n} (d/t) d^{λ−1} χ₁₂(e) a(te²)`), for every integer sequence `a`,
   every squarefree `t ≡ −j (24)` (including `Q ∣ t`) and prime `Q ≥ 5`:
   `S_t(T(Q²)a) = χ₁₂(Q) · T_Q(S_t a)`, `T_Q A(n) = A(Qn) + Q^{2λ−1}A(n/Q)`.
   Checked on random sequences (`lift_equivariance_check.py`; it fails without the χ₁₂(Q) factor).
   This is a formal Dirichlet-convolution identity and is provable in Lean without modular forms.
2. *Lifts satisfy* `A(2n) = (2/t)2^{λ−1}A(n)`, `A(3n) = (3/t)3^{λ−1}A(n)` formally (`psi_mul`).
3. *Dimension of the target* `W = {f ∈ M_{2λ}(Γ₀(6)) : those two relations}` (`lift_space_dim.gp`):

   | case | weight 2λ | dim M | dim W over ℚ | dim mod ℓ |
   |---|---|---|---|---|
   | j = ℓ = 13 | 10 | 11 | **1** | 1 |
   | j = ℓ = 17 | 14 | 15 | **1** | 2 |
   | j = ℓ = 19 | 16 | 17 | **1** | – |
   | j = ℓ = 23 | 20 | 21 | **1** | – |
   | j = 1 (Atkin, g ∈ S₈₄) | 166 | 167 | **7** | 71 (70 with U₁₃ f ≡ 0) |

**Conclusion for Ono–Weaver (j = ℓ): the route works, unconditionally, in characteristic 0.**
Since dim W = 1, every lift `S_t(F)` of `F = f_ℓ/η^ℓ` is a rational multiple of one form h.
`T_Q h ∈ M_{2λ}(Γ₀(6))` (`TheoremA.GoodHecke.heckeT`, with Bézout `CosetData Q 6`) satisfies the
same relations, so `T_Q h = μ'h`. By (1), `S_t(T(Q²)F − χ₁₂(Q)μ'F) = 0` for every t, and
triangularity (`A_t(e) = χ₁₂(e)a(te²) + (terms with smaller e)`, every index m ≡ −ℓ (24) being te²
with gcd(e,6) = 1) gives `T(Q²)F = χ₁₂(Q)μ'F` exactly. That is the needed `EtaHeckeMod` instance
(with `f' = χ₁₂(Q)μ'·f`). Lean pieces: (a) the equivariance identity, (b) the 2/3 relations,
(c) a finite ℚ-linear-algebra certificate on the explicit level-six basis
(`EvenWeightCoordinates`, `firstCoefficients_injective`; coefficients up to about 3·(2λ+1) ≤ 63),
(d) the T_Q step via `qExpansion_heckeT`, (e) triangularity, (f) `gen_modular` applied to
`CertX.f`. Not yet built. Estimate: about 1,000–1,500 lines, several agent-days. The hard
analytic input (modularity of the lift) is already in the repo.

**Conclusion for Atkin (j = 1): the route does not work cheaply.** `F = g/η` is not an eigenform
in characteristic 0 (it lies in a 7-dimensional space and W has dimension 7). Modulo 13, W̄ has
dimension 71, or 70 with the extra `U₁₃f ≡ 0` that lifts of the twisted series satisfy. So no
dimension argument pins the lifts to one T_Q-eigenline. Concluding `T(121)F ≡ 3F` from lifts would
need the converse direction: a series all of whose lifts lie in a T_Q-stable W is in `η^{−1}S_k`,
or Yang's Hecke isomorphism. That is the half-integral weight theory itself.
Honest estimate for building T(Q²) on η-multiplier forms in Lean: the double-coset operator for
`Γ diag(1,Q²) Γ` on functions with multiplier `ν_η^{−j}`; explicit multiplier values on the Q²+Q
coset representatives (needs Rademacher/Petersson's general η-transformation formula with Dedekind
sums or the Jacobi-symbol form — `ThetaLift/EtaMultiplier.lean` has only part); quadratic Gauss
sums mod Q (producing the `(m/Q)Q^{λ−1}` term); holomorphy at the cusp; then the q-expansion
formula. Roughly 3–6 weeks of focused formalization; I see no shortcut through the existing lift
infrastructure for the j = 1 case.

## Update: the Ono–Weaver hypotheses discharged (2026-11-03, third pass)

All 11 `EtaHeckeMod ℓ Q (ℓ−1) ℓ` instances used in `WeaverMain.lean` are now **proved**, so
`ono_13`, `weaver_17` and every `ono_ℓ_Q` hold unconditionally (level (1), axiom-clean: only
`propext`, `Classical.choice`, `Quot.sound`; audit `scripts/atkinsporadic/audit_unconditional.lean`).
In fact `EtaHeckeMod ℓ Q (ℓ−1) ℓ` is proved for ℓ ∈ {13,17,19,23} and *every* prime `Q ≥ 5`.
Atkin's twisted j = 1 case (`atkin_13`, `EtaHeckeMod 13 11 168 1`) is unchanged: still level (2).

Headline statements (namespace `RamanujanTau.AtkinSporadic`):
```
theorem Weaver.ono_13_unconditional (n : ℕ) :
    13 ∣ Fintype.card (Nat.Partition (157525693 * n + 111247))
theorem Weaver.weaver_17_unconditional (n : ℕ) :
    17 ∣ Fintype.card (Nat.Partition (48037937 * n + 1122838))
theorem Weaver.ono_ℓ_Q_unconditional (n : ℕ) (hn : ¬ Q ∣ n) (h : 24 ∣ ℓ * Q^3 * n + 1) :
    ℓ ∣ Fintype.card (Nat.Partition ((ℓ * Q^3 * n + 1) / 24))
  -- (ℓ,Q) ∈ (13,59) (13,73) (17,41) (17,89) (17,103) (19,101) (23,5) (23,19) (23,37) (23,47) (23,67)
theorem EigenLift.etaHeckeMod_13 {Q : ℕ} [Fact Q.Prime] (hQ5 : 5 ≤ Q) : EtaHeckeMod 13 Q (13 - 1) 13
  -- likewise etaHeckeMod_17, _19, _23
theorem EigenLift.eigen_char0 (h13 : 13 ≤ ℓ) (h24 : ℓ < 24) {Q} [Fact Q.Prime] (hQ5 : 5 ≤ Q)
    (D : DimOneProp ℓ) {a} (ha : a ∈ intLattice ℓ) (hα : (coordOf ℓ a).coeff 1 ≠ 0) :
    ∃ ν : ℤ, (coordOf ℓ a).coeff 1 • heckeHalf Q ℓ (halfWt ℓ) (heckeSign Q (halfWt ℓ)) (coordOf ℓ a)
      = ν • coordOf ℓ a
theorem Equivariance.lift_heckeHalf ... (A : PowerSeries ℤ) :
    liftSeries ℓ t (heckeHalf Q ℓ (halfWt ℓ) (heckeSign Q (halfWt ℓ)) A) =
      chi12 Q • HeckeQExp.Tq Q ((Q : ℤ) ^ (2 * halfWt ℓ - 1)) (liftSeries ℓ t A)
```

New modules (all in `RamanujanTau/AtkinSporadic/`, not in the root import):

| file | content |
|---|---|
| `LiftEquivariance.lean` | (1) formal Hecke equivariance `S_t(T(Q²)A) = χ₁₂(Q)T_Q(S_tA)` for every integer sequence, prime `Q ≥ 5`, squarefree `t ≡ −ℓ (24)`: pointwise relation (quadratic reciprocity + parity `(−1/t) = (−1)^λ`), then `conv_hecke` (Dirichlet-convolution identity for completely multiplicative ψ) |
| `LevelSixPrecision.lean` | weight-two series A,B,C certified through q²⁸ (eta-product list certificate), basis lists `basisL`, `evenSeries_coeff28` |
| `DimOne.lean` | `DimOneProp ℓ` and the certificate shape `DimCert` with soundness proof `DimCert.sound` |
| `DimOneData.lean` (generated, `gen_dimone_data.py`) | (3) `dimOne_13/17/19/23`: kernel-checked `K·L = d·I` on 11/15/17/21 relation rows (coefficient 1, `U₂` at m ≤ 14, `U₃` at m ≤ 9) |
| `EigenLift.lean` | (2) lifts in W (`aadModularity`, `U_lift`), (4) `T_Q` preserves W (`GoodHecke.heckeT`, `qExpansion_heckeT`, `dataGood Q`), (5) triangularity (`chi_coeff_dvd`, `exists_index`), `eigen_char0` |
| `EtaHeckeProof.lean` | reduction mod ℓ (`etaHeckeMod_of_dimOne`; Sturm bound 2 when `a(1) ≡ 0`), the four `etaHeckeMod_ℓ` |
| `WeaverUnconditional.lean` (generated, `gen_weaver_unconditional.py`) | the 13 unconditional corollaries |

Argument, as formalized. Let `A = a·P^ℓ` (`P = Σp(n)qⁿ`), `L_t = S_t A`, `t₀ = 24 − ℓ`
(∈ {11, 7, 5, 1}, squarefree), `h₀ = L_{t₀}`, `α = A(1) = h₀(1)`. Every `L_t` lies in
`W = {b ∈ M_{ℓ−3}(Γ₀(6)) integral : U₂b = ε₂b, U₃b = ε₃b}` and so does `T_Q b` for `b ∈ W`.
`DimOneProp`: `b ∈ W, b(1) = 0 ⇒ b = 0`. Hence `α·L_t = L_t(1)·h₀`, `α·T_Q h₀ = μ·h₀`
(`μ = (T_Q h₀)(1)`), so `α·T_Q L_t = μ·L_t` for all t. By equivariance
`S_t(α·T(Q²)A − χ₁₂(Q)μ·A) = 0` for all t, and triangularity gives `α·T(Q²)A = χ₁₂(Q)μ·A` exactly
(index 0 handled separately: `Q² ∤ (Q²−1)ℓ/24`). Mod ℓ: if `a(1) ≢ 0` divide by it; else `a ≡ 0`
by Sturm. The eigenvalue μ is never computed: `EtaHeckeMod` is existential, and the vanishing of
`T(Q²)` mod ℓ is still supplied by the existing kernel certificates `wchk`.

Note that no dimension-one statement for the half-integral space itself is used; the only
"dimension" input is the level-six eigenspace certificate (3), which needs basis coefficients only
through q²⁸ (much less than the ~63 estimated in the second pass: the relation rows are chosen
greedily, `dimone_cert.py`).

Build (each ≲ 30 s; deps already built):
```
nice -n 10 lake build RamanujanTau.AtkinSporadic.WeaverUnconditional
nice -n 10 lake env lean scripts/atkinsporadic/audit_unconditional.lean   # 25 #print axioms
```
Kernel checks: `w2c_certificate` (eta products to q²⁸), `certℓ_basis/rows/inv` (largest: 21×21
integer matrices with entries up to 46 digits), all `decide +kernel`; the whole of `DimOneData`
compiles in ~30 s.

What remains open in this track: Atkin's twisted j = 1 case (`atkin_13`, `atkin_13_class`,
`atkin_13_Q37_class` still take `EtaHeckeMod 13 Q 168 1`); see the second-pass assessment above —
W has dimension 7 there, so this route does not apply. ℓ = 29, 31 (two-dimensional `S_{ℓ−1}`) were
not attempted; `eigen_char0`'s argument would need `dim W = 2` and a 2×2 Hecke computation.
