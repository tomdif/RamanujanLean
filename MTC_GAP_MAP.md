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

## 8. Remaining: the χ₀ combinatorial corollary (route via `f_{2,3,2}`, in progress)

Goal: `χ₀ − 2 = 3Φ − J₅²J_{5,2}/J_{5,1}²`, then `rank_diff_mod5` gives `N(1,5,5n) − N(0,5,5n) = [qⁿ]χ₀`.

**Route.** Garvan's Hecke form (arXiv:1907.04803) of `(q)_∞(χ₀ − 2)` is a sum of `f_{12,9,3}` values (checked to q³⁰⁰):
`(q)_∞(χ₀ − 2) = −f(−q⁷,q²) + q f(−q¹³,q⁴) + q f(−q¹¹,q⁵) − q⁴ f(−q¹⁶,q⁸)`, and splitting the second index by parity,
`f_{12,9,3}(x,y,q) = f_{2,3,2}(x, −y²q³, q⁶) − y f_{2,3,2}(xq⁹, −y²q⁹, q⁶)`. So `(q)_∞(χ₀ − 2)` is a combination of
`f_{2,3,2}(−q^a, −q^b, q⁶)` at seven points (`(a,b)` ∈ {(7,7),(16,13),(11,13)×2,(22,17),(20,19),(16,19),(25,25)}), and
HM Theorem 0.3 with `n = 2, p = 1` (single θ-term) applies.

**Done (2026-10-25, axiom-clean):**
* `MTC/F232 … Ev232, UDecL2`: the `f_{2,3,2}` core (`F ∈ Th(11)`, residue identities without dissection).
* `MTC/Zeros232` (generator `scripts/mtc_gap/gen_zeros232.py`): `F ≡ 0` at `y = −t^{6b}`, `b ∈ {7,13,17,19,25}`, `q = t³⁶`.
* `MTC/HM232Real`: HM Theorem 0.3 at all eight real points (`hm03_77`, `hm03_16_13`, …, `hm03_25_25`).

**Hecke side, done (2026-10-25, axiom-clean, all pushed):**
* `Chi0Pair`: the new `a = q` Bailey pair `β_n = (1 − q^{2n+1})/(q²;q)_{2n}`,
  `α_{3m} = q^{6m²−m}(1 − q^{6m+1})`, `α_{3m−1} = −q^{6m²−5m+1}(1 − q^{6m−1})`, `α_{3m+1} = 0`.
  It is equivalent to the finite identity `Σ_j (q^{j(6j−1)} − q^{(2j+1)(3j+1)})[2n+1; n−3j] = 1 − q^{2n+1}`,
  proved by a WZ certificate in `FractionRing ℤ⟦X⟧` (`pair_identity`).
* `Chi0Conj`: Garvan's conjugate pair. Its recurrence `S_r + q^{3r+3}S_{r+1} = qʳ(1+q^{r+1})/(q)_∞` has a WZ
  certificate, and the closed form `γ_r = Σ_u (−1)^u q^{r+3ru+u(3u+5)/2}(1+q^{r+1+u})` follows by order-descent
  uniqueness (`γc_eq`).
* `Chi0Bailey`: the Bailey transform, `(q;q)_∞ χ₀ = Σ_j c_j γ_{r(j)}` (`qfacInf_mul_chi0`), with the sums exchanged
  coefficientwise.
* `MTC/Chi0Cone`, `MTC/Chi0Theta`: positive cones `Cp k ex ey` of `f_{12,9,3}` in `ℂ((t))`, their two shift
  relations, and the pentagonal boundary `(q;q)_∞ = Th3 0 2 − Th3 1 4`.
  `cone_identity` says the 8 Bailey cones minus the 8 cones of Garvan's four `f_{12,9,3}` values equal `2(q;q)_∞`;
  the proof is 8 shift moves.
  (In `f_{2,3,2}` coordinates the same bookkeeping needs affine automorphisms with Fibonacci entries; in `f_{12,9,3}`
  coordinates no automorphisms are needed.)
* `MTC/Chi0D`: the Bailey double sum, reindexed (`j = r` or `j = −1 − r`), is exactly the 8 cones (`qfac_chi0_cones`).
  This gives Garvan's Hecke form `qfac_chi0_garvan`.
* `MTC/Chi0Bridge`: the parity split `Cp = Cq − Cq`, and `Q^K f_{2,3,2}(−Q^a,−Q^b,Q⁶) = Cq − Cq` for the HM value
  `ev (fS hq36 (6b) (−1)) (6a) (−1)` (`f232_cones`). Together these give **`chi0_hecke_HM`**:
  `(Q;Q)_∞(χ₀ − 2) = −F(7,7) + Q²F(16,13) + 2Q F(11,13) − Q⁵F(22,17) − Q⁶F(20,19) − Q⁴F(16,19) + Q¹²F(25,25)`,
  at exactly the points where `HM232Real` proves HM Theorem 0.3.

**Appell–Lerch endgame, done (2026-10-25, axiom-clean):**
* `MTC/Chi0AL` (`hm_side`): all 28 g-terms of HM Theorem 0.3 at the seven points are normalized to
  `B_e = A(−t^e, −1)` in base `t^{360}`.
  The four even classes cancel termwise. The odd classes have coefficient `−3(Q;Q)_∞ Q^c`, proved by the pentagonal
  2-dissection `(Q;Q)_∞ = j(−t^{30};t^{72}) − t⁶ j(−t⁶;t^{72})`:
  `J̄ ((Q;Q)χ₀ − 2(Q;Q)) = −3(Q;Q)(B₁₇₄ + t⁻⁴²B₆ + t⁻¹⁸B₆₆ + t⁻⁶B₁₁₄) + κ Σ θ_{2,1}`.
* `MTC/Chi0Split` (`Alam_split2`, `czB`): the `n = 2` splitting of Appell–Lerch numerators and the change of `z`
  to `−1`, generic.
* `MTC/Chi0Phi` (`phi_side`): `L5_lam` at `Q`, split to base `t^{360}`, eight changes of `z`, the `(Q⁵;Q⁵)` dissection
  and `A₁₅ = (Q^{15};Q^{15})³/j(Q³;Q^{15})`.
  The result is `J̄ Φ (Q⁵;Q⁵) = −(Q⁵;Q⁵)(same four B's) + (Q⁵;Q⁵)J̄ + T₁ + t⁶J̄A₁₅`, so every mock part cancels.
* `MTC/Chi0Final`: `chi0_identity_of` gives `χ₀ − 2 = 3(Φ − 1) − (q⁵;q⁵)²J_{5,2}/J_{5,1}²`, and `rank_chi0_of` gives
  `N(1,5,5n) − N(0,5,5n) = [qⁿ]χ₀`. **Both are conditional on `ThetaId`**, a single explicit theta-function identity
  (`(Q⁵;Q⁵) κ Σ θ_{2,1} = 3(Q;Q)(T₁ + t⁶J̄A₁₅) − (Q;Q)J̄(Q⁵;Q⁵)³J_{5,2}/J_{5,1}²`).
  Given `hm_side` and `phi_side`, `ThetaId` is equivalent to the χ₀ identity, so it holds; it is checked numerically
  to `Q^{170}`.

**Still open: a proof of `ThetaId`.** Numerical reductions found so far:
* `T₁ + t⁶J̄A₁₅` (nine terms) is a **single product**,
  `Π_Φ = −3Q⁻⁷ (Q⁵;Q⁵)³ J_{5,2}-type · j(Q⁴⁸)/(j(Q²⁴)j(Q³⁶))` (base `Q^{120}`).
* `θ_{2,1}(22,17) + θ_{2,1}(20,19)` (weighted) is a single product. This is a two-theta Weierstrass relation in base
  `Q^{30}`.
* What remains is 6 HM theta-part terms = 2 explicit products. It is rigid: no 2- or 3-term sub-sum is a product (any
  small weights), no homomorphic argument deformation preserves it, and χ₀ has no single complex-point `f_{2,3,2}`
  Hecke form (searched `q' = Q^{d/D}`, `D ≤ 4`, 24th roots of unity). That last search would have given an
  MTC₀-style 3-term identity.
* **Weierstrass-chain search, depth 1 (2026-10-25): negative.**
  - Setup: all Weierstrass instances in bases 10, 12, 15, 20, 24, 30, 40, 60 with arguments `±Q^α` (785k distinct
    shapes), anchored at the 8 terms. That gives 3.5M relations, and the 2-core keeps 45k.
  - Result: the identity is **not** in their span (sparse least squares, residual norm ≈ 0.11).
  - A certificate therefore needs depth ≥ 2 (auxiliary products not adjacent to any original term), or half-integer
    arguments, or bases 120/240.
  - Adding all 136 `n`-dissection identities (`n = 2, 3, 5`) changes nothing (residual 0.111).
* **Weierstrass-chain search, depth 2 (pruned, 2026-10-25): negative.**
  - Every Weierstrass shape in bases ≤ 30 (64k shapes) was anchored at the 45k intermediate products of the depth-1
    core. Of the 6.1M hits, a 2-core of 407k relations survives.
  - Exact sparse least squares gives residual ≈ 0.076 (‖b‖ = 5.39), down from 0.111, so the identity is still not
    in the span.
  - The full depth-2 search with bases 40/60 is about 12× larger and was not run.
* **Watson route (found numerically 2026-10-25, exact to q⁶⁰⁰).**
  - Watson's relations are single products:
    - `W1`: `f₀(q) + 2F₀(q²) − 2 = ∏₂₀`;
    - `W2`: `f₀(q) − 2φ₀(−q²) = −∏₁₀`.
    - (Bajpai–Kimport–Liang–Ma–Ricci, arXiv:2202.12141, (2.5), list these as Watson's identities.)
  - Combined with MTC₀ (`f₀ = θ₄(0,q⁵)G(q) − 2φ(q²)`, proved) and `R1` (`χ₀ = 2F₀ − φ₀(−q)`) at `q²`, all mock
    parts cancel. The χ₀ identity becomes the 4-term product identity
    `2∏₂₀(q) − 3θ₄(0,q⁵)G(q) − ∏₁₀(q) + 2P(q²) = 0`, with `P = J₅²J_{5,2}/J_{5,1}²`.
  - That identity splits into three 3-term identities: two 2-dissections and one base-10 identity.
  - **Theta side fully certified (2026-10-25)**: every theta identity this route needs has a small exact certificate.
    The certificates came from the same depth-1 search, run on these small identities (scratchpad scripts
    `small.py`, `rog*.py`).
    - Rogers' `G(q)G(q⁴) + qH(q)H(q⁴) = φ(q)/f(−q²)` needs one Weierstrass relation in base 10.
    - Its companion `G(q)G(q⁴) − qH(q)H(q⁴) = φ(q⁵)/f(−q²)` needs two.
    - `G(−q)H(q) − G(q)H(−q) = −2q∏` needs one HM (1.4b) relation plus one Weierstrass relation.
    - T3 (`2P_A + P = P_B`) needs one Weierstrass relation in base 5.
    - T1 and T2 then follow by product bookkeeping. For example, `ϑ₄(q) + ϑ₄(q⁵) = 2f(−q²)G(−q)G(q⁴)`.
  - Still open: a Lean proof of `R1` that does not go through HM for χ₀. Any HM-based proof of a χ₀ relation
    reproduces the rigid θ-terms of `ThetaId`. No one-parameter generalization of `R1` was found in the natural
    families.
  - The cost moves to Lean proofs of `W1`, `W2` and `R1`, which are q-series relations (Watson 1936–37, via
    generalized Lambert series). This is the recommended next route.
* **Other negative results:**
  - the 7 HM theta values lie in 7 distinct proportionality classes;
  - those classes admit no pairwise addition-law merges beyond `(22,17)+(20,19)`;
  - degenerate points (where `f_{2,3,2}` is a product, on `a+b ∈ {42, 72}`) have `θ_{2,1} = 0`, so they cannot
    substitute for our points;
  - reflection and swapping preserve each class.
* **Modular route, scoped.** Mathlib has `ModularForm.eq_const_of_weight_zero` and `isZero_of_neg_weight`
  (arithmetic groups) and a norm map, which is enough for a Sturm-type argument.
  - Missing: modularity of the ~100-factor generalized eta quotients on `Γ₁(120)`, i.e. their transformation
    laws via `jacobiTheta₂`.
  - Missing: a kernel-checkable coefficient comparison up to the Sturm bound (~10⁴ coefficients at weight ≈ 30).
  - Both are far beyond the current scale.
* Also negative: no single Andrews-type Hecke form for χ₀ or φ₀; no single complex-point `f_{1,4,1}` form for φ₀.
* Alternative route identified: `R1: χ₀ = 2F₀ − φ₀(−q)` holds exactly. With MTC₀ and `f₀ + 2F₀(q²) − 2 = ∏`, the
  χ₀ identity reduces to the φ₀ conjecture, plus proofs of R1 and that Watson relation.
* Remaining candidate routes:
  - a deeper Weierstrass search;
  - an HM-type general identity with a free variable (as HM (1.9) was for MTC₀);
  - the φ₀ route;
  - a modular-forms (Sturm bound) proof.
