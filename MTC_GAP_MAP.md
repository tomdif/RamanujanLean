# Mock Theta Conjectures — gap map (2026-10-23)

Target: a kernel-checked, axiom-clean proof of Ramanujan's **Mock Theta Conjectures** (Hickerson 1988),
starting with the `f₀` conjecture, using the Hickerson–Mortenson (HM, arXiv:1208.1421, Proc. LMS 2014)
route: **Eulerian form → Hecke-type double sum → Appell–Lerch sums → theta identity.**

Every identity below was checked with exact integer/rational arithmetic, using the scripts in
`scripts/mtc_gap/`, to order q¹²⁰ or q¹⁶⁰. The Appell–Lerch evaluator was checked against a
wrong-sign control, which disagrees in 113 coefficients.

## 1. The statements

Conventions: `(a;q)_n`, `j(x;q) = (x)_∞(q/x)_∞(q)_∞`, `J_{a,m} = j(q^a;q^m)`, `J_m = (q^m;q^m)_∞`,
`m(x,q,z) = j(z;q)⁻¹ Σ_r (−1)^r q^{r(r−1)/2} z^r / (1 − q^{r−1}xz)` (HM Def. 0.1).
Ramanujan's `Φ(q) = −1 + Σ q^{5n²}/((q;q⁵)_{n+1}(q⁴;q⁵)_n)` is `RankProof.Phi 1 − 1` (RankSpec.lean).
Similarly, `Ψ` is `RankProof.Phi 2 − 1`. Also `Φ(q) = q·g(q;q⁵)`, with g the universal mock theta function.

**MTC₀ (HM 4.11):** `f₀(q) = J_{5,10}J_{2,5}/J₁ − 2Φ(q²)`, where `f₀ = Σ q^{n²}/(−q;q)_n`.

The search script `search.py` recovers all ten Lost-Notebook identities of the form
"mock theta function ± c·Φ or Ψ = eta product", with the eta exponents periodic mod 5 or 10:

| function | relation found (to q¹⁶⁰) |
|---|---|
| f₀ | f₀ + 2Φ(q²) = ∏ |
| f₁ | f₁ + 2q⁻¹Ψ(q²) = q·∏ |
| ψ₀ | ψ₀ − Φ(q²) = q·∏ |
| ψ₁ | ψ₁ − q⁻¹Ψ(q²) = q·∏ |
| φ₀ | φ₀(−q) + Φ(q) = ∏ |
| φ₁ | φ₁(−q) − Ψ(q) = −q·∏ |
| F₀ | F₀ − Φ − 1 = −q·∏ |
| F₁ | F₁ − q⁻¹Ψ = q·∏ |
| χ₀ | **χ₀ − 2 = 3Φ − J₅²J_{5,2}/J_{5,1}²** |
| χ₁ | χ₁ − 3q⁻¹Ψ = q·∏ |

`pairs.py` finds the theta-only "Watson relations" (no Φ), for example `f₀ + 2F₀(q²) − 2 = ∏` and
`f₀ + 2ψ₀(−q) = ∏`. By Andrews–Garvan, all ten identities reduce to two of them: MTC₀ for the
0-family and MTC₁ for the 1-family.

### Payoff already wired in the repo
`rank_diff_mod5` (RankDiff5.lean) gives `N(1,5n) − N(0,5n) = 3[qⁿ]Φ − [qⁿ](J₅²J_{5,2}/J_{5,1}²)`.
Combined with the χ₀ row, this is exactly the **Andrews–Garvan combinatorial Mock Theta Conjecture**:

  `N(1,5,5n) − N(0,5,5n) = [qⁿ]χ₀` for n ≥ 1.

Here `[qⁿ]χ₀` counts partitions of n whose smallest part k is unique and whose other parts lie in
(k, 2k]. Once the χ₀ identity is proved, this corollary is a few lines of Lean.

## 2. The chain for MTC₀ and its Lean status

| # | Link | Numerics | In repo | Missing work | Size |
|---|---|---|---|---|---|
| L0 | Definitions: `f₀`, `f₁`, `ψ₀`, `ψ₁` as `PowerSeries ℤ` | ✓ | `F0`, `chi0`, `phi0` exist, defined twice (MockTheta5Defs and MockTheta5.JTP in R1); Φ, Ψ exist (RankSpec) | define f₀ etc. with `mtSum`; prove the two F0/chi0/phi0 copies equal | S |
| L1 ✅ (core) | **Andrews' Hecke form:** `J₁f₀ = Σ_{n≥0} Σ_{\|j\|≤n} (−1)^j q^{(5n²+n)/2−j²}(1−q^{4n+2})` (HM 0.3) | ✓ q¹²⁰ | `bailey_transform` (a=1) ✓; creative-telescoping pipeline ✓ (QPairA/B, al_pair) | **DONE:** `isBaileyPair_f0`, `qfacInf_mul_f0 : (q;q)_∞·f₀ = Σ q^{n²}αₙ` (MockTheta5F0Pair.lean, axiom-clean). Remaining: regroup into the double-sum shape L2 consumes, once L2 fixes it | S |
| L2 | **Hecke → Appell–Lerch** for those `f_{3,7,3}` specializations: `J₁f₀ = 2J₁m(q¹⁴,q³⁰,−1) + 2q⁻²J₁m(q⁴,q³⁰,−1) − Θ` (HM Cor. 8.4, Thm 0.11 n=3) | ✓ (the end result, 4.11) | **nothing on `f_{a,b,c}`**. The m/θ machinery over `ℂ((t))` exists (ALBase, ALChangeZ, ALSplit, ALWeier0) | the crux; see §3 | L |
| L3 | Change of z (HM Thm 2.3): `m(x,q,−1) → m(x,q,q⁴)` | (in 4.11) | `ALz.change_of_z` at monomial points ✓ | instantiate; check side conditions | S |
| L4 | Theta clean-up: HM (8.16)/(8.17), one Prop 1.1 (Riemann/Weierstrass) instance, `J₁J₅ = J_{1,5}J_{2,5}` | — | `weierstrass0`, ALCore7-style theta automation ✓ | 2–3 theta identities | S–M |
| L5 | **Φ as Appell–Lerch:** `Φ(q²) = q²g(q²,q¹⁰) = −m(q¹⁴,q³⁰,q⁴) − q⁻²m(q⁴,q³⁰,q⁴)` (HM Prop 3.2) | ✓ q¹²⁰ | `rank_AL` gives `(q)_∞R(z;q)` as a Lambert sum, but only for **constant** `z ∈ ℂ`; `spec_coeff` covers z = q^k for the Hecke–Rogers form | redo `rank_AL` at `z = q` in base `q⁵` (finite `al_pair` is field-generic), then partial fractions into two m's | M |
| L6 | Plumbing between `ℤ⟦q⟧` and `HahnSeries ℤ ℂ` (the m's live in ℂ((t)), the Eulerian forms in ℤ⟦q⟧) | — | rank mod 5/7 crossed this boundary; check what is reusable | embedding lemmas | S–M |

**L1 Bailey pair (new; verified for n ≤ 8 to q¹²⁰, `bailey_f0_pair.py`):** relative to a = 1,

  `βₙ = 1/(−q;q)ₙ`,  `α₀ = 1`,  `αₙ = q^{(3n²+n)/2}Sₙ − q^{(3n²−n)/2}S_{n−1}`,  `Sₙ = Σ_{|j|≤n}(−1)^j q^{−j²}`.

Each αₙ is a polynomial, since (3n²−n)/2 ≥ n². Feeding the pair into `bailey_transform` gives
`(q)_∞f₀ = Σ q^{n²}αₙ`, which is (0.3) after shifting n in the second term.

**Proved 2026-10-23** (`RamanujanTau/MockTheta5F0Pair.lean`). Write `V m = q^{m²}Sₘ`, the polynomial
defined by `V(m+1) = q^{2m+1}V m + 2(−1)^{m+1}`. No hypergeometric certificate exists, because αₙ
is not hypergeometric, but a certificate *linear in V* does. A sympy ansatz finds it, and it needs an
extra factor (1−qⁿ):
`G(n,s) = qⁿ/((q)_{n−s−1}(q)_{n+s})·((1−qⁿ)q^{T(s)+s}V s − 2(−1)^{s+1}q^{T(s)})`, with
`(1−qⁿ)((1+qⁿ)F(n,r) − F(n−1,r)) = G(n,r) − G(n,r−1)` for interior r, plus separate rows r = 0 and r = n.
After telescoping, the factor 1−qⁿ cancels because ℤ⟦q⟧ is a domain.

## 3. The crux: L2 (Hecke-type double sums → Appell–Lerch sums)

`f_{a,b,c}(x,y,q) = Σ_{sg r = sg s} sg(r)(−1)^{r+s} x^r y^s q^{a·C(r,2) + brs + c·C(s,2)}` (HM 0.4).
HM prove the general expansion from functional equations in x and y, a partial-theta / Appell–Lerch
link, and a theta-function zero argument at generic x, y. Two possible formal strategies:

1. **Formalize HM Thm 0.11, or the simpler Thm 0.3 family, generically.** This needs a two-variable formal
   setting, Laurent in x and y over ℂ((t)). It is the reusable option: the same machinery would give the
   7th-order conjectures (Cor 0.8), the 6th-order identities (Thm 0.6), and others.
2. **Prove only the two needed specializations at monomial points**, imitating the repo's `change_of_z`
   method: build a bilateral series obeying `F_{k+2} = q^k x F_k`, show it has enough zeros, and conclude
   `F ≡ 0` from the leading term of a determinant. This is cheaper but one-off.

Before choosing, read HM §5–6, the proof of Thm 0.3 and the analogous Thm 0.11, and list exactly
which analytic steps (generic x, poles and zeros) need formal replacements.

There is a lighter alternative for the 0-family. HM Thm 0.10 with n = 1 (`f_{1,4,1}`, a single m term
per side) yields the Appell–Lerch forms of φ₀ and ψ₀, and ψ₀'s form (4.13) is verified above. But
ψ₀'s Hecke form (Andrews 1986) is **not yet located**: a brute-force search over one- and two-term
`f_{a,b,c}` specializations with b ≤ 6 and exponents ≤ 8 found nothing. That route also needs a
Watson relation (f₀ + 2ψ₀(−q) = ∏, verified) proved independently. It is cheaper at L2 only if that
relation has an elementary proof.

## 4. Open items, in order

1. ~~**[Lean] L1:** define f₀, prove the Bailey pair, derive the Hecke-side identity.~~ **Done** (MockTheta5F0Pair.lean).
2. **[Reading] L2 strategy:** HM §5–6, then pick strategy 1 or 2.
3. **[Lean, M] L5:** `rank_AL` at z = q in base q⁵, then Prop 3.2.
4. **[Lean, L] L2**, then L3, L4, L6, which together give **MTC₀**.
5. **[Lookup] Andrews–Garvan 1989 reductions:** which Watson relations link φ₀ (and so χ₀) to f₀/F₀.
   `F₀(q²) ↔ f₀` is theta-only, but φ₀ appears in no two-term theta relation, so it needs either
   R1 (`χ₀ = 2F₀ − φ₀(−q)`, already the open target of MockTheta5R1.lean) plus one more relation,
   or its own HM n = 1 proof. This sets the path to the combinatorial corollary in §1.
6. **[Lean] MTC₁** (f₁, Ψ) mirrors MTC₀: f₁ uses (8.13), with the same Thm 0.11 n = 3 specialization.

## Scripts (`scripts/mtc_gap/`)
- `series.py`: exact q-series toolkit, all ten fifth-order functions, Φ, Ψ, and an eta-quotient detector.
- `al.py`: Laurent-series evaluator for j, J, and m(x,q,z) at monomial arguments.
- `search.py`, `pairs.py`: the identity searches behind §1.
- `check.py`: checks HM (4.11), (4.13), Prop 3.2 and Hecke form (0.3) exactly to q¹²⁰.
- `bailey_f0_pair.py`: the L1 Bailey pair.
