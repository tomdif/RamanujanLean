# All ten fifth-order mock theta identities (Lost Notebook), in Lean

**Status (2026-11-09): all ten are proved unconditionally and axiom-clean.**
Every headline depends only on `[propext, Classical.choice, Quot.sound]`; see `scripts/audit/mock_theta5_all.lean`.
There is no `sorry`, no `native_decide`, no new axiom, and no named hypothesis left open.

Lean: `RamanujanTau/MockTheta5All/` (`Defs`, `Rel`, `B1`, `Theta`, `Common`, `F0`, `F1`, `All`).

## Notation

Everything lives in `ℤ⟦q⟧` (`q = X`):
- `Pinf r M = (q^r; q^M)_∞`, and `Ring.inverse` is `1/·` on units.
- `Φ = RankProof.Phi 1` and `Ψ = RankProof.Phi 2`. Andrews–Garvan's mock theta functions are
  - `Φ_AG(q) = Φ − 1 = −1 + Σ_{n≥0} q^{5n²}/((q;q⁵)_{n+1}(q⁴;q⁵)_n)`,
  - `Ψ_AG(q) = Ψ − 1 = −1 + Σ_{n≥0} q^{5n²}/((q²;q⁵)_{n+1}(q³;q⁵)_n)`.
- `expand 2` is `q ↦ q²`, and `negQ` (`PowerSeries.rescale (−1)`) is `q ↦ −q`.
- `ϑ₄(q) = (q;q)_∞/(−q;q)_∞`, `ψ(q²) = (q⁴;q⁴)_∞/(q²;q⁴)_∞`, `G = 1/((q;q⁵)(q⁴;q⁵))`, `H = 1/((q²;q⁵)(q³;q⁵))`.

### The ten functions

| function | series | Lean |
|---|---|---|
| f₀ | `Σ q^{n²}/(−q;q)_n` | `MockTheta5.JTP.f0` (= `Watson.f0w`) |
| f₁ | `Σ q^{n²+n}/(−q;q)_n` | `MockTheta5.JTP.f1` (= `f1w`, `f1w_eq`) |
| F₀ | `Σ q^{2n²}/(q;q²)_n` | `Watson.F0w` |
| F₁ | `Σ q^{2n²+2n}/(q;q²)_{n+1}` | `F1w` |
| φ₀ | `Σ q^{n²}(−q;q²)_n` | `phi0w` (`negQ phi0w = Watson.P0w`) |
| φ₁ | `Σ q^{(n+1)²}(−q;q²)_n` | `phi1w` (`negQ phi1w = P1w`) |
| ψ₀ | `Σ q^{(n+1)(n+2)/2}(−q;q)_n` | `psi0w` |
| ψ₁ | `Σ q^{n(n+1)/2}(−q;q)_n` | `psi1w` |
| χ₀ | `Σ qⁿ/(q^{n+1};q)_n` | `MockTheta5.Formal.chi0` (= `Watson.chiA`) |
| χ₁ | `Σ qⁿ/(q^{n+1};q)_{n+1}` | `chi1w` |

The new definitions are `osum`s of locally finite families (Watson toolkit). The `LF_*` lemmas in `Defs.lean` show
these are honest sums.

## The ten identities (`MockTheta5All/All.lean`)

| # | theorem | statement (Andrews–Garvan form) |
|---|---|---|
| 1 | `mock_theta_f0` | `f₀(q) = ϑ₄(q⁵)G(q) − 2Φ_AG(q²)` (MTC₀) |
| 2 | `mock_theta_f1` | `q f₁(q) = q ϑ₄(q⁵)H(q) − 2Ψ_AG(q²)` (MTC₁) |
| 3 | `mock_theta_F0` | `F₀(q) − 1 = Φ_AG(q) − q (q¹⁰;q¹⁰)/((q⁴;q¹⁰)(q⁵;q¹⁰)(q⁶;q¹⁰))` |
| 4 | `mock_theta_F1` | `q F₁(q) = Ψ_AG(q) + q (q¹⁰;q¹⁰)/((q²;q¹⁰)(q⁵;q¹⁰)(q⁸;q¹⁰))` |
| 5 | `mock_theta_phi0` | `φ₀(−q) = −Φ_AG(q) + (q⁴,q⁵,q⁶,q¹⁰;q¹⁰)/((q²;q¹⁰)²(q³;q¹⁰)(q⁷;q¹⁰)(q⁸;q¹⁰)²)` |
| 6 | `mock_theta_phi1` | `φ₁(−q) = Ψ_AG(q) − q (q²,q⁵,q⁸,q¹⁰;q¹⁰)/((q;q¹⁰)(q⁴;q¹⁰)²(q⁶;q¹⁰)²(q⁹;q¹⁰))` |
| 7 | `mock_theta_psi0` | `ψ₀(q) = Φ_AG(q²) + q (q,q⁹,q¹⁰;q¹⁰)/((q²,q³,q⁷,q⁸;q¹⁰))` |
| 8 | `mock_theta_psi1` | `q ψ₁(q) = Ψ_AG(q²) + q (q³,q⁷,q¹⁰;q¹⁰)/((q,q⁴,q⁶,q⁹;q¹⁰))` |
| 9 | `mock_theta_chi0` | `χ₀(q) − 2 = 3Φ_AG(q) − (q⁵;q⁵)²J_{5,2}/J_{5,1}²` |
| 10 | `mock_theta_chi1` | `q χ₁(q) = 3Ψ_AG(q) + q (q,q⁴,q⁵;q⁵)/((q²;q⁵)²(q³;q⁵)²)` |

Identities (2), (4), (6), (8) and (10) carry a factor `q` because the `f₁`-group statements have a `q⁻¹` in
Andrews–Garvan's form. Before any proof, every product was found and checked numerically to at least `q¹⁵⁰` by
`scripts/mtc_gap/search.py` and `scripts/mock_theta5_all/chk.py`. Identities (1), (2), (9) were already in the repo:
- (1) is `MTC.mock_theta_conjecture_f0`;
- (2) is `MTC.mock_theta_conjecture_f1`;
- (9) is `Watson.chi0_identity`.

`All.lean` also exports Ramanujan's two relations:
- (B₀) `χ₀ = 2F₀ − φ₀(−q)`, as `ramanujan_B0`;
- (B₁) `qχ₁ = 2qF₁ + φ₁(−q)`, as `ramanujan_B1`.

## Reduction chain

The chain follows Andrews–Garvan (1989): each group reduces to its MTC through Watson's linear relations and
theta-function identities. The Watson relations come from Watson 1937, §3, and are all proved here as q-series
identities (Euler's two expansions, Fubini, parity splits).

**f₀ group** (from MTC₀):
- F₀ uses (3₀) `f₀ − ϑ₄G = 2qψ(q²)H(q⁴) − 2(F₀(q²) − 1)` (`Watson.watson_3_0`, already in the repo), MTC₀ and `theta_F0`.
  The identity is proved at `q²` and pulled back with `expand_injective`.
- φ₀ uses (2₀) `f₀ + ϑ₄G = 2φ₀(−q²)` (`Watson.watson_2_0`, already in the repo), MTC₀ and `theta_phi0`.
- ψ₀ uses (1₀) `ψ₀ = qψ(q²)H(q⁴) + F₀(q²) − 1` (**new**, `watson_1_0`), F₀ at `q²` and `theta_psi0`.
- χ₀ was already in the repo, via (B₀).

**f₁ group** (from MTC₁):
- F₁ uses (3₁) `f₁ + ϑ₄H = 2ψ(q²)G(q⁴) − 2qF₁(q²)` (**new**, `watson_3_1`), MTC₁ and `theta_F1`.
- φ₁ uses (2₁) `q(f₁ − ϑ₄H) = −2φ₁(−q²)` (**new**, `watson_2_1`), MTC₁ and `theta_phi1`.
- ψ₁ uses (1₁) `ψ₁ = ψ(q²)G(q⁴) + qF₁(q²)` (**new**, `watson_1_1`), F₁ at `q²` and `theta_psi1`.
- χ₁ uses (B₁) `qχ₁ = 2qF₁ + φ₁(−q)` (**new**, `watson_B1`), the F₁ and φ₁ identities, and `theta_chi1`.

### Watson relations (`Rel.lean`, `B1.lean`)

(1₀), (1₁), (3₁) and (3₀) all reduce to one kernel,

  `K_{σ,δ} = (q⁴;q⁴)_∞ Σ_n σⁿ q^{(n+δ)²}/((q²;q²)_n (q^{2n+2};q⁴)_∞)`.

A parity split (`kern_split`, built on Watson's `u7`/`u8`) evaluates it as
- `K_{σ,1} = qψ(q²)H(q⁴) + σ(F₀(q²) − 1)`,
- `K_{σ,0} = ψ(q²)G(q⁴) + σ·qF₁(q²)`.

Each relation reaches the kernel in two steps:
- (1₀) and (1₁) expand `(−q;q)_n = (q²;q²)_n/(q)_n`, apply Euler twice, and take `σ = 1`.
- (3₁) is Watson's `f₀ ± ϑ₄G` computation with `q^{n²}` replaced by `q^{n²+n}` (`f1_pm`), and lands on `σ = −1, δ = 0`.

(2₁) follows the same route as (2₀) and ends with Watson's `u5`.

(B₁) follows Watson's proof of (B₀) with odd parts in place of even parts:
- The odd part of Euler, `(y;q²)_∞ Σ yⁿ/(q)_{2n+1} = Σ q^{p(2p+1)} y^p/(q)_{2p+1}`, is proved as `euler_odd`.
- The even-`m` half gives `2F₁`.
- The odd-`m` half gives `χ₁` back, plus `q⁻¹φ₁(−q)`.

No second series form of χ₁ is needed.

### Theta identities (`Theta.lean`, generated)

| name | identity in `ℂ((q))` | HM (1.4b) instances `M(N; e₁,c₁; e₂,c₂)` |
|---|---|---|
| `theta_phi0` | `(ϑ₄(q⁵)+ϑ₄(q))G(q) = 2E_{φ₀}(q²)` | `M(5;1,−;2,−)`, `M(5;1,+;2,+)` |
| `theta_F0` | `2qψ(q²)H(q⁴) − (ϑ₄(q⁵)−ϑ₄(q))G(q) + 2q²E_{F₀}(q²) = 0` | `M(10;1,−;3,+)`, `M(5;1,−;2,−)`, `M(5;1,+;2,+)` |
| `theta_psi0` | `ψ(q²)H(q⁴) − qE_{F₀}(q²) = E_{ψ₀}(q)` | `M(10;1,+;3,−)` |
| `theta_phi1` | `(ϑ₄(q⁵)−ϑ₄(q))H(q) = 2qE_{φ₁}(q²)` | `M(5;1,−;2,−)`, `M(5;1,+;2,+)` |
| `theta_F1` | `2ψ(q²)G(q⁴) − (ϑ₄(q⁵)+ϑ₄(q))H(q) = 2qE_{F₁}(q²)` | `M(10;3,+;5,−)`, `M(10;3,−;5,+)`, `M(5;1,+;1,+)` |
| `theta_psi1` | `ψ(q²)G(q⁴) + qE_{F₁}(q²) = E_{ψ₁}(q)` | `M(10;1,−;3,+)` |
| `theta_chi1` | `2E_{F₁} − E_{φ₁} = E_{χ₁}` | `M(5;1,+;2,−)`, `M(5;1,−;2,+)` |

Here `E_•` is the eta quotient in identity `•`. The certificate engine is the one that produced `Watson/Star.lean`:
- every theta function and every product is written in the atoms `(q^r;q^{80})_∞`;
- each relation is scaled by a monomial in the atoms;
- the combination is checked by `linear_combination (norm := (field_simp; ring))`.

Certificates come from an exact linear solve (sympy) over the M-relations (`scripts/mock_theta5_all/gen_theta.py`,
which reuses `small.py`/`atoms.py` from `scripts/watson/`). To regenerate, run this from `scripts/mock_theta5_all/`:

```
WHICH="phi0 F0 psi0 phi1 F1 psi1 chi1" OUT=Theta.lean python3 gen_theta.py
```

The output is byte-identical to the committed `Theta.lean`.

### Assembly (`F0.lean`, `F1.lean`)

Each identity is mapped by `ιq : ℤ⟦q⟧ → ℂ((q))`. `ιq` is injective, and so is `expand 2`. The Watson relation,
the MTC and the theta identity then close the goal by `linear_combination`; F₀, φ₀, F₁, φ₁ use the doubled form
(`eq_of_two_mul`). The `IsUnit` side conditions of `Ring.inverse` are discharged by `unit_tac`.

## Build

```
nice -n 10 lake build RamanujanTau.MockTheta5All.All
nice -n 10 lake env lean scripts/audit/mock_theta5_all.lean
```

`Theta.lean` is the slowest file, at about 2 minutes. The others take seconds each, plus import loading.
`MockTheta5All.All` is included in the `RamanujanTau.lean` import graph.

## Remaining named Props

None.
