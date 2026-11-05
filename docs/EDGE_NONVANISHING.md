# `L(Δ,s) ≠ 0` on the edge `Re s = 13/2`

Lean: `RamanujanTau/EdgeNonvanishing/` (5 files, about 900 lines, no `sorry`, no new axiom, no
`native_decide`). Build with `nice -n 10 lake build RamanujanTau.EdgeNonvanishing.Main`.

**Result.** `L(Δ,s)` has no zeros on the edge line `Re s = 13/2`. This is the GL(2) analogue of
`ζ(1+it) ≠ 0` (Rankin 1939, Ogg 1969, Moreno 1977; Jacquet–Shalika 1976 in general). With
`HeckeZeros.tauL_ne_zero_of_gt` it gives non-vanishing on `Re s ≥ 13/2`. The functional equation
then gives non-vanishing on `Re s ≤ 11/2` away from the trivial zeros `s = −n`. The proof does
**not** use Deligne's bound `|τ(p)| ≤ 2p^{11/2}`.

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every headline. This is
evidence level (1), unconditional, with no named hypotheses.

## Statements

```lean
-- RamanujanTau.EdgeNonvanishing
theorem tauL_ne_zero_edge (t : ℝ) : tauL (13 / 2 + t * I) ≠ 0
theorem tauL_ne_zero_of_ge {s : ℂ} (hs : 13 / 2 ≤ s.re) : tauL s ≠ 0
theorem tauL_ne_zero_of_le {s : ℂ} (hs : s.re ≤ 11 / 2) (hn : ∀ n : ℕ, s ≠ -n) : tauL s ≠ 0

-- ingredients
theorem localD_inv_eq_exp …   -- local factor of L(Π×Π̃) = exp ℓ, ℓ ≥ 0   (Local.lean)
theorem rs_sub_zeta_bound :   -- ‖R(s) − c ζ(s)‖ ≤ K‖s‖/(Re s − 3/5), Re s > 1   (RS.lean)
    ∃ K, 0 ≤ K ∧ ∀ s, 1 < s.re → ‖RS s - rsc * riemannZeta s‖ ≤ K * ‖s‖ / (s.re - 3/5)
theorem rs_eulerProduct (hs : 1 < s.re) : HasProd (fun p => ∑' e, term rsB s (p^e)) (RS s)
theorem alpha_sq_le …          -- Satake parameter ‖α_p‖² ≤ p, without Deligne   (PrimeLocal.lean)
theorem rs_local …             -- (1−p^{−2s})⁻¹ ∑_e b(p^e)p^{−es} = ((1−Y)²(1−α²Y)(1−β²Y))⁻¹
theorem one_le_norm_Fval (hσ : 1 < σ) (t : ℝ) : 1 ≤ ‖Fval σ t‖   (Assembly.lean)
```

Notation: `RS s = ∑ τ(n)² n^{−11} n^{−s}` is the normalized Rankin–Selberg series, with edge
`Re s = 1`. `L(s) := tauL(s + 11/2)` is the normalized L-function.

## The proof

The proof uses the classical positivity argument for `Π = 1 ⊞ Δ|·|^{it} ⊞ Δ|·|^{−it}`. Put

`F(σ) = ζ(σ) · L(σ+it)² L(σ−it)² · (ζ(2σ)R(σ))² · ζ(2σ+4it)R(σ+2it) · ζ(2σ−4it)R(σ−2it)`,

which is `L(Π × Π̃, σ)` (`Assembly.Fval`).

1. **Satake parameters without Deligne** (`PrimeLocal`). Put `λ = τ(p)p^{−11/2}`. Choose
   `α + β = λ`, `αβ = 1` with `‖β‖ ≤ 1 ≤ ‖α‖`. Write `u_k = τ(p^k)p^{−11k/2}`. Then
   `α^{k+1} = u_{k+1} − βu_k`, and Rankin's bound `u_k² ≤ K p^k` (from
   `RankinExact.rankinSelberg_exact`) gives `(‖α‖²/p)^{k+1} ≤ 4K` for every `k`. Hence
   `‖α‖² ≤ p`. This is all the size information that the Euler factors need for `σ > 1`.
2. **Local factors.** The local factor of `L(Δ,s)` is `(1−αZ)(1−βZ)`. The local factor of
   `ζ(2s)R(s)` is `((1−Y)²(1−α²Y)(1−β²Y))⁻¹`. The proof uses the cubic recurrence
   `v_{k+3} = (λ²−1)(v_{k+2} − v_{k+1}) + v_k` for `v_k = u_k²`, so that
   `∑ v_k Y^k = (1+Y)/((1−Y)(1−α²Y)(1−β²Y))`.
3. **Local positivity** (`Local`). The Euler factor of `F` is `∏_{j=1}^{25} (1−γ_j x)⁻¹` with
   `x = p^{−σ}`. Here `∑_j γ_j^k = (1 + A_k E_k)²`, where `A_k = α^k + β^k` and
   `E_k = p^{−ikt} + p^{ikt}` are both real. Hence the factor equals `exp ∑_k (1+A_kE_k)² x^k/k`,
   which is `≥ 1`. This uses `‖γ_j x‖ ≤ ‖α‖² p^{−σ} < 1` and Mathlib's
   `hasSum_taylorSeries_neg_log`.
4. **Global positivity.** Combining the Euler products (Mathlib's ζ, `HeckeZeros.tauL_eulerProduct`
   and `rs_eulerProduct`) gives `‖F(σ)‖ = ∏_p exp ℓ_p ≥ 1` for all `σ > 1`.
5. **Analytic input** (`RS.rs_sub_zeta_bound`). Rankin's `∑_{n≤N} τ(n)²/n¹¹ = cN + O(N^{3/5})`
   and Mathlib's `LSeries_eq_mul_integral` (Abel summation) give
   `R(s) − cζ(s) = s∫_1^∞ E(t)t^{−s−1}dt = O(‖s‖/(Re s − 3/5))`.
6. **Contradiction** (`Main`). Suppose `L(1+it) = 0` with `t ≠ 0`. Then `L(1−it) = 0` as well,
   by `tauL_zero_conj`. As `σ = 1 + h → 1⁺`:
   - `ζ(1+h) ≤ 2/h`, from `riemannZeta_residue_one`;
   - `L(σ±it) = O(h)`, since `tauL` is entire;
   - `ζ(2σ)R(σ) = O(1/h)`;
   - `ζ(2σ±4it)R(σ±2it) = O(1)`, by continuity of ζ at `1±2it` and step 5.

   So `‖F(1+h)‖ = O(h) → 0`, which contradicts step 4. The pole order is 3 and the zero order is 4.
7. **`t = 0`.** `L(Δ,13/2) > 0` by `HeckeL.tauL_pos`: `Λ(σ) = ∫ Δ(iy) y^{σ−1} dy` and `Δ(iy) > 0`.

## Files

| file | content |
|---|---|
| `Local.lean` | `pseq` power sums, `list_log`, the 25 parameters `gammas`, `localD_inv_eq_exp` |
| `RS.lean` | `rsb`, `RS`, `rs_partial`, `rs_le_linear`, `rs_summable`, `rs_sub_zeta_bound`, `rs_eulerProduct` |
| `PrimeLocal.lean` | `uu`, `lam`, `uu_rec`, `satake`, `alpha_sq_le`, `tau_local`, `rs_local` |
| `Assembly.lean` | `ep`, `fR`, `Fval`, `Fp`, `Fp_hasProd`, `Fp_eq_exp`, `one_le_norm_Fval` |
| `Main.lean` | analytic bounds, `tauL_ne_zero_edge`, `tauL_ne_zero_of_ge`, `tauL_ne_zero_of_le` |

## Remarks and gaps

- **No zero-free region.** The result is non-vanishing on the line only. A de la Vallée-Poussin
  region `σ ≥ 1 − c/log(|t|+2)` would need growth bounds for `L` and `R` in `t`. The inputs here
  are qualitative: continuity of ζ, and `‖s‖` linear in the Abel bound. Those growth bounds are
  available in principle from `HeckeConvex`, but they are not done.
- **No holomorphy of `L(Sym²Δ,s)` (Shimura) is needed.** Only `R(s) − cζ(s)` on `Re s > 3/5` is
  used, and that comes from Rankin's error term.
- For other level-one eigenforms the same proof goes through, given the analogue of
  `tauL_eulerProduct` and `rankinSelberg_exact_general`. Only Δ is formalized here.
