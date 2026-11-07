# Gauss's sign of the quadratic Gauss sum, and `EtaHecke Q k 1` for every prime Q ≥ 5

2026-11-04. Lean: `RamanujanTau/GaussSign/` (3 files, ~530 lines) plus `Audit.lean`.
Imports `RamanujanTau/HalfHecke/` without modifying it. Not added to the root import at the time;
`GaussSign.EtaHeckeAll` has since been added (`Audit.lean` is not imported).

## Results and evidence levels

| Statement | Level |
|---|---|
| `GaussSign.gaussQuad_eval`: for **every odd** `N ≥ 1`, `Σ_{r mod N} e(r²/N) = √N` if `N ≡ 1 (4)`, `= i√N` if `N ≡ 3 (4)` | **(1) Lean, axiom-clean** |
| `GaussSign.gQ_eval`: for a prime `Q ≥ 3`, `HalfHecke.gQ Q = Σ (x/Q) e(x/Q)` is `√Q` or `i√Q` (same split) | **(1)** |
| `GaussSign.gaussSign_of_even`: `HalfHecke.GaussSign Q k` for every prime `Q ≥ 5` and every even `k ≥ 2` | **(1)** |
| `GaussSign.etaHecke_all (Q) [Fact Q.Prime] (hQ : 5 ≤ Q) (k) (hk : 2 ≤ k) : EtaHecke Q k 1` | **(1)** |
| Reusable analytic lemmas: `tendsto_sqrt_cosKernel`, `tendsto_theta_quad` (`√y θ(2a/N+iy) → N⁻¹Σ_r e(ar²/N)`), `theta_pert`, `gaussQuad_limit` | **(1)** |

Each depends only on `propext`, `Classical.choice`, `Quot.sound` (`nice -n 10 lake env lean
RamanujanTau/GaussSign/Audit.lean`). No `sorry`, no `native_decide`, no new axiom.

Mathlib (this checkout) has `gaussSum_sq` (`g² = χ(−1)·#R`) but not the sign. It has no Schur DFT
eigenvalue argument and no theta proof of the sign either.

## Note on odd `k`

`GaussSign Q k` as defined in `HalfHecke/EtaHecke.lean` is **false** for odd `k` when `Q ≡ 3 (mod 4)`.
The right-hand side `heckeSign Q (k−1)` contains `((−1)^{k−1}/Q)`, which flips with the parity of `k`,
while the left-hand side does not depend on `k`. So `etaHecke_all` handles odd `k` separately: a
level-one form of odd weight is zero (`ModularForm.levelOne_odd_weight_eq_zero`), so `a = 0` and
`a' = 0` works. This falsity is checked by hand (level (3)); it is not formalized.

## Proof (theta function, `RamanujanTau/GaussSign/Theta.lean`, `Landsberg.lean`)

Let `θ(τ) = Σ_n e^{πin²τ}` (Mathlib's `jacobiTheta`), with `θ(τ) = (−iτ)^{−1/2} θ(−1/τ)`.

1. **Rational points** (`tendsto_theta_quad`). The phase `e^{πin²·2a/N} = e(an²/N)` depends only on
   `n mod N`. Finite Fourier inversion on `ZMod N` (Mathlib `ZMod.dft`) writes
   `θ(2a/N + iy) = N⁻¹ Σ_j 𝓕Φ(j) · cosKernel(j/N, y)`. By Mathlib's
   `evenKernel_functional_equation`, `√y·cosKernel(b, y) = evenKernel(b, 1/y)`, which tends to
   `[b ∈ ℤ]` as `y → 0⁺` (`isBigO_atTop_evenKernel_sub`). Only `j = 0` survives, giving
   `N⁻¹ Σ_r e(ar²/N)`.
2. **Vertical approach** `τ_t = 2/N + it`. Then `−1/τ_t = u + iv` with `s = N²/4`,
   `u = −(N/2)/(1+st²)` and `v = st/(1+st²)`. This is the cusp `−N/2` up to a real-part error
   `|u + N/2| = (N/2)·t·v`.
3. **Perturbation** (`theta_pert`): `‖θ(u+iv) − θ(u'+iv)‖ ≤ 2|u−u'|/v · evenKernel(0, v/2)`. The proof
   bounds `|e^{iα}−e^{iβ}| ≤ |α−β|` and `x e^{−x} ≤ 2e^{−x/2}` termwise. After multiplying by `√t`,
   the error is `≤ N t · √(2t/v) · √(v/2)·evenKernel(0,v/2) → 0`.
4. Comparing limits gives `N⁻¹ G = (−2i/N)^{−1/2} · (2/N) · ¼ Σ_{r mod 4} e(−Nr²/4)`
   (`gaussQuad_limit`). Hence `G = (1 + e(−N/4)) / (−2i/N)^{1/2}`. Evaluating the principal branch,
   `(−2i/N)^{1/2} = (1−i)/√N` (from `log(−i) = −πi/2`), and `e(−N/4) = −i` or `i` according to
   `N mod 4`.
5. `gQ_eq_sum_sq`: `Σ_r ψ(r²) = Σ_x (1+χ(x)) ψ(x) = g(χ,ψ)`. The proof uses `quadraticChar_card_sqrts`
   and `Σψ = 0`.
6. `gaussSign_of_even`: `χ(−24) = (−1/Q)(2/Q)(12/Q)` and `heckeSign Q (k−1) = (12/Q)(−1/Q)` for even
   `k`, so the condition reduces to `(2/Q)·e((Q−1)/8)·ε = 1` (`key_sign`), where `ε = 1` or `i`. This
   is checked on `Q mod 8`.

## Files

| file | content |
|---|---|
| `GaussSign/Theta.lean` | `tendsto_sqrt_cosKernel`, `hasSum_theta`, `tendsto_theta_quad`, `mul_exp_neg_le`, `theta_pert` (imports only Mathlib) |
| `GaussSign/Landsberg.lean` | `gaussQuad_limit`, `sqrt_neg_two_I_div`, `gaussQuad_eval` (imports only Mathlib + Theta) |
| `GaussSign/EtaHeckeAll.lean` | `gQ_eq_sum_sq`, `gQ_eval`, `epsQ`, `key_sign`, `gaussSign_of_even`, `etaHecke_all` |
| `GaussSign/Audit.lean` | `#print axioms` for the headline declarations |

Build: `nice -n 10 lake build RamanujanTau.GaussSign.EtaHeckeAll`, then
`nice -n 10 lake env lean RamanujanTau/GaussSign/Audit.lean`.

## Consequences / what remains

* `(etaHecke_all Q hQ k hk).toMod ℓ : EtaHeckeMod ℓ Q k 1` for every prime `Q ≥ 5`, `k ≥ 2`, `ℓ`.
* The Atkin mod-13 class theorems in `AtkinSporadic/Atkin13*.lean` also use Q-specific eigen data
  (`twisted_hecke`, `vanish_of_eigen`), so they do not extend to other `Q` from `etaHecke_all` alone.
  (The Q-specific eigen data was later supplied for every prime `5 ≤ Q < 500`, `Q ≠ 13`:
  `AtkinTwisted.eigen_all`, [ATKIN_TWISTED_ALL_Q](ATKIN_TWISTED_ALL_Q.md).)
* `j ≠ 1` (`η^{−j}`) still needs the HalfHecke construction itself to be generalized. That is not done.
* `gaussQuad_eval` works for any odd modulus. It gives the Landsberg–Schaar special case `q = 1` and
  could be reused for Gauss sums of Jacobi symbols.
