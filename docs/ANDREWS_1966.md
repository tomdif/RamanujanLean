# The sign pattern of Ramanujan's f(q) for every n ≥ 1, and Andrews 1966

`f(q) = Σ q^{n²}/(−q;q)_n² = Σ α(n) qⁿ`. Here `α(n) = N(0,2,n) − N(1,2,n)` (`MockTheta3.f3_rank`).

## G1: done for every n ≥ 1, by an elementary proof (Lean, axiom-clean)

```lean
-- RamanujanTau/Andrews/Sign.lean
theorem Andrews.alpha_sign {n : ℕ} (hn : 1 ≤ n) : 0 < (-1) ^ (n + 1) * Andrews.α n
   -- Andrews.α n := PowerSeries.coeff n MockTheta3.f3
theorem Andrews.rank_parity_sign_all {n : ℕ} (hn : 1 ≤ n) :
    0 < (-1) ^ (n + 1) * ((#{l : n.Partition | Even (rank l)} : ℤ) - #{l | ¬ Even (rank l)})
-- RamanujanTau/Andrews/Main.lean (imports Dragonette.Main)
theorem Andrews.dragonette_sign_all {n : ℕ} (hn : 1 ≤ n) : 0 < (-1) ^ (n + 1) * (Dragonette.α n : ℝ)
theorem Andrews.dragonette_with_sign : IsEquivalent atTop α (…Dragonette main term…) ∧ ∀ n ≥ 1, sign
```

For all of these, `#print axioms` gives `[propext, Classical.choice, Quot.sound]`. There is no `sorry`, no
`native_decide` and no new axiom.

**There is no finite cut-off N.** The circle method is not used at all, so no table of α(n) is needed. The
previous analysis said the route needed transformations at q → ±i and a kernel table up to a few thousand
(`ANDREWS_DRAGONETTE.md`, "explicit sign theorem"). That analysis is superseded: the sign theorem follows from
identities that are already formal in the repo, plus coefficientwise inequalities.

### Proof

1. **Watson (W1)**, already formal as `MockTheta3.Watson3.watson_W1`, says `f(q) = 2φ(−q) − b(q)`. Substitute
   `q ↦ −q` using `PowerSeries.rescale (−1)` (`alpha_formula`). This gives
   `(−1)^{n+1} α(n) = [qⁿ] (−q;q²)_∞ ϑ(q) − 2 [qⁿ] φ(q)`,
   where `ϑ = 1 + 2Σ_{k≥1} q^{k²}` and `φ(q) = Σ q^{m²}/(−q²;q²)_m`.
2. **Bounding φ.** For the inverse, `|[qᵏ] 1/(−q²;q²)_m| ≤ [qᵏ] 1/(q²;q²)_m` (`ADom_inv_NP`, using geometric
   series and multiplicativity of `|·| ≤`). Euler's identity `Σ q^{m²}/(q²;q²)_m = (−q;q²)_∞` is the repo's
   `Watson.euler_prod`. Together they give `|[qⁿ]φ| ≤ Q(n)` (`abs_phi3_le`). Here `Q(n)` is the number of
   partitions of `n` into distinct odd parts.
3. Hence, for `n ≥ 4`, `(−1)^{n+1} α(n) ≥ Q(n) + 2Q(n−1) + 2Q(n−4) − 2Q(n)` (`main_lower`).
4. **Partition inequalities.** Write `B(n)` for the number of partitions of `n` into distinct odd parts ≥ 3, so
   `Q(n+1) = B(n+1) + B(n)`.
   - Shifting the smallest part down by 2 gives `B(m+2) ≤ Q(m)` (`B_le_Q`).
   - Shifting the largest part up by 2 gives `B(m+1) ≤ B(m+3)` (`B_mono`).
   - Both are proved as generating-function dominations of finite products, by induction
     (`NP_shift_low` and `NP_shift_high` in `Andrews/Order.lean`).
   - Together they give `Q(n) ≤ 2Q(n−1)` for `n ≥ 4` (`Q_le_two`) and `Q(m) ≥ 1` for `m ≥ 3` (`Q_pos`).
   - So for `n ≥ 7`, and also for `n = 4, 5`, we get `(−1)^{n+1}α(n) ≥ 2Q(n−4) > 0`.
5. **Small n.** The cases `n = 1, 2, 3, 6` use `Q(0)=Q(1)=1`, `Q(2)=0` and `Q(6)=1`, from explicitly expanding
   `(1+q)(1+q³)(1+q⁵)`. They also use `[q³]φ = −1`. The crude bound actually fails at `n = 3`, which is why
   that case needs the exact value.

### Files

| file | lines | content |
|---|---|---|
| `RamanujanTau/Andrews/Order.lean` | ~200 | coefficientwise order `NN`/`Dom`/`ADom`, `geo`, `ADom_inv_NP`, `Dom_factor_NP`, `NP_shift_low`, `NP_shift_high` |
| `RamanujanTau/Andrews/Sign.lean` | ~330 | `Q`, `B`, partition inequalities, `phi3`, Euler bound, rescaling, `alpha_formula`, `alpha_sign`, `rank_parity_sign_all` |
| `RamanujanTau/Andrews/Main.lean` | ~30 | link to `Dragonette` (`dragonette_sign_all`, `dragonette_with_sign`) |
| `scripts/andrews/check_elementary.py` | | exact-integer check of every step for n ≤ 1500 |

Each file was built alone with `lake build RamanujanTau.Andrews.<File>`. The root `RamanujanTau.lean` is
untouched; the coordinator should add `import RamanujanTau.Andrews.Main`.

### Evidence levels

1. **Lean, axiom-clean.** The sign theorem for all `n ≥ 1`, its rank-parity form, and its combination with
   Dragonette's asymptotic. Also the side results:
   - `|[qⁿ]φ(q)| ≤ Q(n)`;
   - `Q(n) ≤ 2Q(n−1)` for `n ≥ 4`;
   - the exact identity `(−1)^{n+1}α(n) = [qⁿ](−q;q²)_∞ϑ(q) − 2[qⁿ]φ(q)`.
2. **Lean, conditional on named hypotheses.** None.
3. **Paper proof only.** None.
4. **Numerical evidence only.** The script confirms every inequality used for `n ≤ 1500`, and that `n = 3` is
   the only `n` where the crude bound fails.

**Literature.** I found no published elementary proof for `f(q)`. Two recent arXiv papers prove "sign laws"
for third-order mock theta functions: arXiv:2606.27902 treats ρ(q) with Watson's identity plus a root-of-unity
method, and arXiv:2606.31606 is "Sign Laws and Mock Theta Functions". The coordinator should check whether
2606.31606 covers `f(q)`. The argument above uses only Watson 1936 (W1), Euler, and two partition shifts, so
it may well be folklore; I make no novelty claim. As noted in the earlier doc, Gomez–Zhu's effective bound
would need a finite check up to about 10⁷.

## G2: Andrews 1966 with error O(√n): assessed, not attempted in Lean

The structure of a proof:
- **Main terms, feasible with existing infrastructure.** `b(q) = (q;q)_∞³/(q²;q²)_∞²` is a weight-1/2 eta
  quotient. Its order at a cusp `a/c` is `3/24 − 2·gcd(c,2)²/48`. That is negative only for even `c`, which
  explains why only even `k` appear in Andrews' formula. Ramanujan's claim (proved by Watson) says
  `f(q) − (−1)^k b(q) = O(1)` radially at primitive `2k`-th roots of unity. So Andrews' main terms are, up to
  sign, the circle-method main terms of the eta quotient `∓b`. Those can be built from the repo's
  `Rademacher/` stack: `F_transform` is the general eta transformation, plus `Farey`, `Chord`, `MainTerm` and
  `Bessel`. The work is the Kloosterman sums `A_{2k}`, with the 2τ-scaling handled cusp by cusp. Rough size:
  1–2k lines, by analogy with `Rademacher/`.
- **Error term, the hard part.** The circle method needs a *uniform* bound for `f(q) ∓ b(q)` on each Farey arc
  at even cusps, and for `f(q)` at odd cusps, of polynomial size in `k` and `1/|z|`. This needs the general
  transformation law of `f` under Γ₀-type matrices: Watson 1936, or Gordon–McIntosh via Appell–Lerch sums and
  Zwegers' μ-function transformation. Those laws express `f` at `h/k` in terms of `f`/`ω` at the image cusp
  plus Mordell integrals `h(z;τ)`. Formalizing this would require:
  - the transformation of μ(u,v;τ) under S and T;
  - the Mordell-integral functional equations and bounds;
  - the Appell–Lerch representation of `f` (`RankAL`/`ALBase` give pieces of the `(q;q)_∞ f = 1 + 4Σ…`
    side);
  - full SL₂(ℤ) Jacobi theta with characteristics (Mathlib has `jacobiTheta₂` S/T).
  
  My estimate is 4–8k Lean lines, a multi-week project. It was not attempted here: the ±i special case alone
  is no longer needed for G1, and on its own it does not give Andrews' error term.
- **Out of scope.** Bringmann–Ono, as instructed.

## Remaining gaps (precise)

- G2: everything above. Nothing is formalized; this is an assessment only.
- G1: none.

**Literature note (2026-11-04).** arXiv:2606.31606 (Ghosh Dastidar, "Sign Laws and Mock Theta Functions") proves a mod-3 sign law for the coefficients of ρ(q) (via ω(q) and Watson's identity, plus a finite computation) and mentions extensions to φ(q) and χ(q). Per its abstract it does not treat f(q) or N(0,2,n)−N(1,2,n). Novelty of `Andrews.alpha_sign` remains unclaimed pending a fuller search; the argument may be folklore.
