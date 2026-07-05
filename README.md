# RamanujanLean

A Lean 4 + Mathlib formalization of parts of **Ramanujan's mathematics**, in two arcs:

1. **Ramanujan's τ function** — the coefficient sequence of the modular discriminant
   `Δ(q) = q·∏(1−qⁿ)²⁴ = Σ τ(n) qⁿ`, extracted as a computable `τ : ℕ → ℤ` with its Hecke theory.
2. **q-series & partition theory** — a from-scratch formal-power-series framework (Bailey chains,
   Jacobi triple products, Durfee rectangles, the `d/dz` differentiation trick) culminating in three
   classical theorems proved **kernel-clean** (no `sorry`, no new axioms, no `native_decide`):
   Euler's pentagonal number theorem, Jacobi's cube identity, and **Ramanujan's partition congruence
   `p(5n+4) ≡ 0 (mod 5)`**.

> The Lean **package** is still named `RamanujanTau` (every module lives under `import RamanujanTau.…`);
> the repository is `RamanujanLean`.

| | |
|---|---|
| Modules | ~90 |
| Build | `lake build` → **3638 jobs, 0 errors** |
| `sorry` count | **0** |
| New `axiom` declarations | **0** (headline q-series theorems: `[propext, Classical.choice, Quot.sound]` only) |
| Lean toolchain | `leanprover/lean4:v4.30.0-rc2` + Mathlib |

---

## Part II — q-series & partition theory (headline results)

Everything here is built from a single from-scratch engine: formal power series over `ℤ`, `ℤ[z;z⁻¹]⟦q⟧`
(the "z-outer" ring), a z-degree projection `zProj`, coefficient stabilization for infinite products, and
a `d/dz|_{z=−1}` differentiation functional. Nothing below is imported from Mathlib — the Jacobi triple
product, the pentagonal/cube identities, and the congruence are not in Mathlib.

### `MockTheta5EulerPentagonal.lean` — Euler's pentagonal number theorem
```lean
theorem euler_pentagonal : qfacInf = pentSeries
--  (q;q)_∞ = Σ_{n∈ℤ} (−1)ⁿ q^{n(3n−1)/2}
```
Proved by building a **shifted base-`q³` bilateral Jacobi triple product**
`(q³;q³)_∞ · ∏(1+z q^{3i+1}) · ∏(1+z⁻¹ q^{3i−1}) = Σ_{n} zⁿ q^{(3n²−n)/2}` (`bilateral_pent_JTP`,
proved `zProj`-by-`zProj` against a Durfee-rectangle collapse), evaluating at `z = −1` (a *unit* — this is
how the `ℤ((q))` non-unit obstruction at `z = −q` is sidestepped), and reassembling the three residue-class
products mod 3 back into `(q;q)_∞`.

### `MockTheta5JacobiCubeProof.lean` — Jacobi's cube identity
```lean
theorem jacobi_cube_identity : qfacInf ^ 3 = jacobiCubeSum
--  (q;q)_∞³ = Σ_{m≥0} (−1)ᵐ (2m+1) q^{m(m+1)/2}
```
Proved from a **bilateral triangular Jacobi triple product** (`MockTheta5TriangularBilateral.lean`)
differentiated by the `d/dz|_{z=−1}` functional `L` (Leibniz via `Finsupp.addHom_ext`, the vanishing rule
`L((1+z)·f) = …`).

### `MockTheta5PartitionCongruence.lean` — Ramanujan's partition congruence
```lean
theorem five_dvd_coeff_partitionGF (n : ℕ) : (5 : ℤ) ∣ coeff (5*n+4) partitionGF
--  5 ∣ p(5n+4),   where p(n) = [qⁿ] 1/(q;q)_∞
```
The classical proof, fully formalized:
- **`MockTheta5Frobenius.lean`** — the char-5 Frobenius `(q;q)_∞⁵ ≡ (q⁵;q⁵)_∞ (mod 5)`, from per-factor
  freshman's dream `(1−x)⁵ = 1−x⁵` (`sub_pow_char`) lifted to the infinite product.
- **`MockTheta5Qfac4.lean`** — `(q;q)_∞⁴ = pentSeries · jacobiCubeSum`, whose coefficient at any exponent
  `≡ 4 (mod 5)` is `≡ 0 (mod 5)`: the Cauchy product feeds every `(pentagonal k, triangular m)` pair into the
  **arithmetic heart** `jacobi_weight_dvd_of_exponent` (`PartitionCongruenceMod5.lean`), which forces
  `2m+1 ≡ 0`.
- **`MockTheta5PartitionCongruence.lean`** — the capstone, via
  `Ψ₅ partitionGF = Ψ₅((q;q)_∞⁴) · expand₅(Ψ₅ partitionGF)`; the second factor is supported on multiples of
  5, so every `q^{5n+4}` term lands on a vanishing `(q;q)_∞⁴` coefficient. **No induction.**

### Supporting q-series infrastructure
Bailey pairs & the Bailey chain / transform (`MockTheta5Bailey*`), the classical and bilateral Jacobi
triple products (`MockTheta5JacobiTriple` / `…Bilateral` / `…ClassicalJTP`), Durfee-rectangle identities
(`MockTheta5Durfee*`), Cauchy/Euler sum=product identities, even/odd and distinct=odd partition theorems,
Gauss/alternating theta evaluations, and fifth-order mock-theta scoping (`MockTheta5R1`).

---

## Part I — Ramanujan's τ function

A computable `τ : ℕ → ℤ` (Mathlib has `ModularForm.discriminant : ℍ → ℂ` but does not extract the integer
coefficient function) via a small computable `List ℤ` polynomial representation:

```lean
def tau (n : ℕ) : ℤ :=
  let p   := eulerProductTrunc n n   -- ∏_{k=1}^{n} (1 − X^k), truncated to deg n
  let p24 := truncPowList n p 24      -- (·)^24, truncated
  coeffList (shiftList 1 p24) n       -- [X · (·)^24].coeff n
```

- **`Basic` / `SmallValues`** — the `τ` function, `τ(0)=0`, `τ(1)=1`, and exact values `τ(2..12)` by
  `native_decide`.
- **`HeckeTheory`** — a single master hypothesis class `TauHeckeMaster` (the `T_p`-action on the weight-12
  eigenform) from which both multiplicativity `TauMultiplicative` and the recurrence `TauHeckeRecurrence`
  are *derived as instances*.
- **`EulerFactor`** — under `TauHeckeRecurrence`, the local Euler factor
  `(1 − τ(p)X + p¹¹X²)·Σ τ(pʳ)Xʳ = 1`, `τ(p²)=τ(p)²−p¹¹`, and `τ(n)=∏ τ(p^k)`.
- **`Gegenbauer`** — the general closed form `τ(pʳ) = G_r(τ(p), p¹¹)` (Chebyshev-U family) plus the explicit
  binomial sum, subsuming `HeckePowers` (`τ(p⁴)…τ(p⁷)`).
- **`Deligne` / `Lehmer` / `Congruences`** — Deligne's bound `|τ(p)| ≤ 2p^{11/2}`, Lehmer's non-vanishing,
  and the mod-691 congruence, each certified on a finite range and exposed as a named hypothesis class for
  the universal statement.

Deep theorems are exposed as named typeclasses (`TauHeckeMaster`, `DeligneBound`, `LehmerConjecture`,
`TauMod691`), never asserted as `axiom`s — the same discipline as
[PlonkLean](https://github.com/tomdif/PlonkLean).

---

## Build

```sh
lake build
```

A Mathlib cache hit brings this down to seconds of project code on top of Mathlib.

## License

MIT.

## References

- Ramanujan, S. (1916). "On certain arithmetical functions." *Trans. Cambridge Philos. Soc.* **22**.
- Ramanujan, S. (1919). "Some properties of p(n), the number of partitions of n." *Proc. Cambridge Philos. Soc.* **19** — the congruence `p(5n+4)≡0 (mod 5)`.
- Euler, L. — the pentagonal number theorem. · Jacobi, C. G. J. (1829). *Fundamenta Nova* — the triple product and cube identity.
- Andrews, G. E. *The Theory of Partitions* — Bailey chains, Durfee squares, the Jacobi triple product.
- Deligne, P. (1974). `|τ(p)| ≤ 2p^{11/2}` (Weil conjectures). · Lehmer, D. H. (1947), *Duke Math. J.* **14**.
- Apostol, T. M. *Modular Functions and Dirichlet Series in Number Theory*.
- OEIS [A000594](https://oeis.org/A000594) (τ), [A000041](https://oeis.org/A000041) (p(n)).
