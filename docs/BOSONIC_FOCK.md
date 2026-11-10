# Completed occupation Hilbert space

The occupation model extends from finite energy shells to a complete Hilbert
space. Its energy operator is self-adjoint on its maximal domain, and completion
preserves the finite shell dimensions and leading entropy.

## Public theorems

Use `import RamanujanTau.BosonicFockSpectrum`, or the root `import RamanujanTau`.
Names below are in the namespace `BosonicOscillator`.

| Theorem | Statement |
|---|---|
| `polynomialEmbedding_dense` | Normalized polynomial states are dense in the square-summable occupation space |
| `fockHamiltonian_domain` | The domain consists exactly of amplitudes whose energy-weighted coordinates are square-summable |
| `fockHamiltonian_self_adjoint`, `fockHamiltonian_closed` | The maximal energy operator is self-adjoint and closed |
| `fockHamiltonian_extends_polynomial` | The analytic operator extends the existing algebraic Hamiltonian |
| `fockShellIsometry` | The natural-energy subspace is isometrically equivalent to the earlier finite shell |
| `mem_fockEnergySpace_iff` | Shell support is equivalent to domain membership and the eigenvector equation |
| `fockEnergySpace_finrank` | The energy-`n` eigenspace has dimension `p_k(n)` |
| `fockCharge_domain_eq`, `fockCharge_eq_hamiltonian_sub` | The 24-species charge is `H−I` on the same domain |
| `fockChargeSpace_finrank` | Charge `n` has multiplicity `p_24(n+1)` |
| `fockChargeSpace_entropy`, `fockChargeSpace_cardy_ratio` | Log-multiplicity divided by `√n` tends to `4π`; its ratio to the specified Cardy leading term tends to one |

The reusable diagonal-operator construction is in
[HilbertDiagonal](../RamanujanTau/HilbertDiagonal.lean). Its adjoint domain equals
the original maximal domain, which gives self-adjointness. The occupation
specialization is [BosonicHilbert](../RamanujanTau/BosonicHilbert.lean), and the
shell identification is [BosonicFockSpectrum](../RamanujanTau/BosonicFockSpectrum.lean).

## Scope

The vacuum offset is specified as minus one. This does not derive a regularized
vacuum energy or identify the model with a physical string or gravitational
system. The result describes eigenspaces, not the operator's full resolvent
spectrum. Infinite creation/annihilation adjoints, a thermal trace, colored
logarithmic corrections, and the quarter-BPS mock Jacobi extension remain open.

## Verification

```sh
lake build RamanujanTau.BosonicFockSpectrum
lake env lean scripts/audit/bosonic_fock.lean
python3 scripts/verify_lean.py --full
```

The [24-declaration audit](../scripts/audit/bosonic_fock.lean) covers the diagonal
operator, dense embedding, domains, shell identification, and entropy. Expected
axioms are a subset of `propext`, `Classical.choice`, and `Quot.sound`.
See the [publication record](verification/publication_2026_11_10.json) for build
results and source hashes. Earlier finite-shell records retain their original
scope and verification dates.
