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
| L1 ✅ | **Andrews' Hecke form:** `J₁f₀ = Σ_{n≥0} Σ_{\|j\|≤n} (−1)^j q^{(5n²+n)/2−j²}(1−q^{4n+2})` (HM 0.3) | ✓ q¹²⁰ | `bailey_transform` (a=1) ✓; creative-telescoping pipeline ✓ (QPairA/B, al_pair) | **DONE** (MockTheta5F0Pair.lean, axiom-clean): `isBaileyPair_f0`, `qfacInf_mul_f0`, and Andrews' exact form `qfacInf_mul_f0_hecke`. L2 may still want the `f_{3,7,3}` reindexing (8.12), which is bookkeeping | — |
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

## 3. The crux: L2 (Hecke-type double sums → Appell–Lerch sums) — strategy reading done

`f_{a,b,c}(x,y,q) = Σ_{sg r = sg s} sg(r)(−1)^{r+s} x^r y^s q^{a·C(r,2) + brs + c·C(s,2)}` (HM 0.4).

**How HM prove it (§5–6, read 2026-10-23).** Two parts, of different nature:

- *Algebraic, formalizable as is:* functional equations of f, g and θ (Props 5.1–5.6, Lemma 5.9);
  and the closing step (5.17)–(5.22). There, `D = f − g − θ/J` satisfies
  `D(q^{p(2n+p)}x) = q^{…}(−x)ⁿ(−y)^{−(n+p)}D(x)`, so the Laurent coefficients of D grow like
  `q^{−np(2n+p)k²/2}`, and an entire D must vanish.
- *Analytic:* **D is entire** (Prop 5.11). This is shown by residue cancellation at every simple pole of
  g and θ, plus Hartogs at the finitely many intersection points.

**Formal translation.** The repo's method for `change_of_z` already handles this pattern in one
variable z. It works in ℂ((t)) at monomial points, expands on an annulus as a cone sum with coefficient
recurrences (`AA_rec`), and finishes with a determinant/zero argument. For L2 the variable is x at
fixed monomial y. "D entire" becomes: the annulus expansions of g + θ/J obey the homogeneous
recurrence, i.e. the jump terms across poles cancel. For `f_{3,7,3}` (n=3, p=4) that is about 100 poles
per fundamental annulus. The poles of g sit at `x⁷ ∈ c·q^{120k}`, which drags in 7th roots of unity,
and Θ₃,₄ adds more. Each family must be handled uniformly in (t, k, root). **Estimate: several thousand
lines of Lean — the largest single piece of the campaign.**

**Shortcuts checked, none available:**
- HM Thm 0.4 (`a | b`, `c | b`: only two m-terms) has **no form of discriminant 40** (f₀, f₁, F₀, F₁),
  nor of discriminant 45 (Garvan's χ₀ form). Proof: `b² = D·αγ/(αγ − 1)` is never a square for
  D = 40 or 45.
- Discriminant 15 (φ₀, ψ₀, via `f_{1,4,1}`) does admit Thm 0.4, with base q¹⁵. But ψ₀'s Hecke form
  is not located (two brute-force searches came up empty). And the link `f₀ + 2ψ₀(−q) = ∏`
  compares indefinite forms of different discriminants, so it is no more elementary than MTC itself.
- Garvan's Hecke–Rogers form for χ₀ (arXiv:1907.04803, Thm 1.1; two double sums) is verified to q¹⁵⁰
  (`garvan_chi0_hecke.py`). Its form is equivalent to `f_{12,9,3}`, discriminant 45, so it is no cheaper
  at L2.
- No elementary (modular-form-free, non-HM) proof of the MTC was found in the literature. The known
  proofs are Hickerson 1988 (constant terms), HM 2014, Folsom 2008 (Maass forms) and Andersen 2016
  (vector-valued modular forms).

**Decision:** follow HM Thm 0.3 or 0.11 for `f_{3,7,3}` at fixed monomial y, with the annulus-expansion
formalization of residue cancellation.

## 4. Open items, in order

1. ~~**[Lean] L1:** define f₀, prove the Bailey pair, derive the Hecke-side identity.~~ **Done** (MockTheta5F0Pair.lean).
2. ~~**[Reading] L2 strategy.**~~ **Done** (§3): the HM route with formal residue cancellation; no shortcut exists.
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
- `bailey_f0_pair.py`, `f0_pair_certificate.py`: the L1 Bailey pair and its certificate search.
- `garvan_chi0_hecke.py`: Garvan's Hecke–Rogers form for χ₀.

## 5. Status 2026-10-24

**L2 done at the MTC₀ point (axiom-clean):** `MTC.hm03_xstar` (RamanujanTau/MTC/Zeros373.lean) proves HM Theorem 0.3
for `f_{3,7,3}` at `q = t^{42}`, `x* = i t^{105}`, `y* = −i t^{105}`. The route: entire bilateral series over `ℂ((t))`
(Ent/Conv/ThSpace/ThFactor), `F = P·(J̄f − J̄g − κθ_{3,4})` with `P = Π j(A_r)j(B_s)` lies in `Th(55)` (FCore373), the
residue identities at the zeros of `j(B_s)` and `j(A_r)` are proved symbolically (ResB373, EvA373: a `q³ → q⁴⁸`
dissection indexed by `ρ = c₀ − r`), and `F` vanishes at 56 pairwise inequivalent points (`F0_eq_zero`).
**E1** `MTC.fS_xstar` (Hecke373): `f_{3,7,3}(x*, y*) = (q;q)_∞ f₀(Q)`, `Q = t^{168}` (HM (8.12)).
**E2** `MTC.gNum_xstar` (GX373): `J̄ g(x*, y*) = 2 j(Q²;Q³)(A(Q¹⁴) + Q⁻²A(Q⁴))`.
Remaining for MTC₀: `θ_{3,4}(x*)` as a product (ThetaX/ThetaY, in progress), `κ = J₄₀³` (KapJ), the sum→product bridge
(Bridge), L5 (`Φ(q²)` as Appell–Lerch sums), change of z, HM (8.16)/(1.9) with product rearrangements, ℤ⟦q⟧ bridge.

## 6. MTC₀ PROVED (2026-10-24, axiom-clean)

`MTC.mock_theta_conjecture_f0` (RamanujanTau/MTC/MTC0.lean):

    f₀(q) = (q⁵;q¹⁰)²_∞ (q¹⁰;q¹⁰)_∞ / ((q;q⁵)_∞ (q⁴;q⁵)_∞) − 2 Φ(q²)

with `f₀ = Σ q^{n²}/(−q;q)_n` (`MockTheta5.JTP.f0`) and `1 + Φ = RankProof.Phi 1`, in `ℤ⟦q⟧`; `#print axioms` gives
only `propext, Classical.choice, Quot.sound`. Multiplied-out form: `MTC.mtc0`.

Chain (all in `ℂ((t))`, `Q = t^{168}`, then pulled back by `ιN` injectivity):
* **Main** (`Endgame2.main_x`): HM Thm 0.3 at the MTC₀ point + E1 + E2 + E3 (`ThetaX373.thV_xstar`, `ThetaY373.S_prod`)
  + `κ = (q;q)³` (`KapJ`).
* **L5** (`L5.L5_lam`): `(1 + φ(q))(q⁵;q⁵)_∞ = A₁₀ + qA₁₅ + q²A₂₀` from the Appell–Lerch form of the rank generating
  function at `z = X`, `q = X⁵` (`RankALm.rank_AL_m`), partial fractions and `1/(1−y) = (1+y+y²)/(1−y³)`.
* Appell–Lerch calculus: `LamAb.Alam_eq_Ab` (Lambert form = `ALz.Ab`), `LamInv` (HM 2.2a, 2.2b), `Av_qshift` (2.2c),
  `kappa_eq_jacobi` (HM 1.3), four `ALz.change_of_z2` instances to `z₀ = Q⁴` (`Endgame1.I1`–`I4`).
* `endgame_reduce`: the unknown values `A(Q¹⁴,Q⁴)`, `A(Q⁴,Q⁴)` cancel using `LemA` (HM Prop 1.1, Weierstrass `P11W`)
  and `LemB` (HM Prop 3.2 ⟺ `F1prime`, Weierstrass).
* `LemC_of`: the remaining theta identity = (8.17) × products (`PI1`, `PI2`).
* (8.17) (`H19b.E817_holds`): HM (1.9) as an element of `Th(Q³⁰, 10, Q⁻¹⁰⁵)` (`H19.F19_mem`, via `ThExtra`:
  base multiplication, `x ↦ x^d`, `x^a`, products) vanishing at 11 inequivalent points (`F19_zero`), at `x = 1`.
* Product identities (`ProdId`): every theta becomes a product of atoms `ιN (u^r;u^M)_∞` (barred thetas via HM (1.4b)),
  then `field_simp`.

## 7. MTC₁ PROVED (2026-10-24, axiom-clean)

`MTC.mock_theta_conjecture_f1` (RamanujanTau/MTC/Final1.lean): `q f₁(q) = q θ₄(0,q⁵)/((q²;q⁵)_∞(q³;q⁵)_∞) − 2Ψ(q²)`.
Chain: Bailey pair for `f₁` relative to `a = q` (`αₙ = q^{(3n²+n)/2}(1−q^{2n+1})Sₙ/(1−q)`, certificate
`G(n,s) = q^{T(s)+n}/((q)_{n−s−1}(q)_{n+s+1})·(−q^{2s+1}(1−qⁿ)(1+q^{s+1})V_s + 2(1−q^{n+s+1})(−1)^s)`);
HM Thm 0.3 at `x₁ = i t^{189}` (zero tables shifted by +36; one `A`-class collides with a `B`-zero at `Z⁶³`);
`gNum(x₁) = 2J₁(Q⁻³A(Q²) + Q⁻⁹A(Q⁻⁸))`; `θ₃,₄(x₁) = 2J_{3,12}S₁`, `S₁ = −Q⁻³J_{3,20}J_{5,20}J_{7,20}J_{1,5}/(j̄₂j̄₈j̄₁₂j̄₁₈j₂₀)`;
`(1+ψ)(q⁵;q⁵)_∞ = A₁₀ + q²A₁₅ + q⁴A₂₀` (`a = 2`); changes of `z` to `z₀ = Q²` (with `z₀ = Q²` the ψ-side theta part
vanishes: Weierstrass `j₄j₁₂j₁₄ + Q⁴j₂j₄j₆ = j₆j₈j₁₄`); LemA₁ (Weierstrass at `x = Q⁶, y = −Q², u = Q⁴, v = Q¹⁰`);
(8.17)₁ `J̄_{5,20}J̄_{12,30} − Q³J̄_{2,5}J̄_{30,120} = J_{6,20}J_{3,12}` = HM (1.9) at `x = Q⁶`.
