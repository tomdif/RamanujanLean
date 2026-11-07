> **Update (2026-11-04):** `GaussSign.etaHecke_all` removes the Gauss-sign hypothesis for every prime Q ≥ 5 ([GAUSS_SIGN](GAUSS_SIGN.md)). Caution: `GaussSign Q k` as defined here is false for odd k when Q ≡ 3 (mod 4); every use in this directory is at even k (k = 168).

# The Hecke operator T(Q²) on η⁻¹S_k(SL₂ℤ), and Atkin's congruence mod 13 unconditionally

2026-11-04. Lean: `RamanujanTau/HalfHecke/` (8 files, ~1,550 lines) plus
`RamanujanTau/AtkinSporadic/Atkin13Unconditional.lean`. Audit: `scripts/halfhecke/audit.lean`.
Numerical sanity check of the construction: `scripts/halfhecke/coset_check.py` (mpmath).

## Results and evidence levels

| Statement | Level |
|---|---|
| `Atkin13.atkin_13_unconditional : ∀ n, 13 ∣ p(17303 n + 237)` | **(1) Lean, axiom-clean** |
| `Atkin13.atkin_13_class_unconditional`: `13 ∣ p(N)` if `24N−1 = 11²m`, `(m/11)=1`, `(m/13)=−1` | **(1)** |
| `Atkin13.atkin_13_Q37_class_unconditional`: same with `37²m`, `(m/37)=−1`, `(m/13)=−1` | **(1)** |
| `HalfHecke.etaHecke_11_168 : EtaHecke 11 168 1`, `etaHecke_37_168 : EtaHecke 37 168 1` (characteristic 0, full statement, not only mod 13) | **(1)** |
| `HalfHecke.etaHecke_of_sign`: `EtaHecke Q k 1` for **every** prime `Q ≥ 5` and `k ≥ 2`, given `GaussSign Q k` (the classical sign of the quadratic Gauss sum, an explicit named hypothesis) | **(1)**, conditional only on `GaussSign` |

Every listed declaration depends only on `propext`, `Classical.choice`, `Quot.sound`;
no `sorry`, no `native_decide`, no new axiom.

## The construction (route actually used)

No general half-integral-weight theory was needed. For `G ∈ S_k(SL₂ℤ)` put `F = G/η` and

    T F(z) = Q^{2k−3} F(Q²z) + c_M Σ_{x mod Q} (x/Q) F(z + 24x/Q) + Q^{−2} Σ_{x mod Q²} F((z+24x)/Q²),

the `Q² + Q` cosets of `Γ diag(1,Q²) Γ`, with the translations scaled by 24 so that the
η-multiplier on each coset is trivial or quadratic, and `c_M = Q^{k−5/2} (−24/Q) e(3(Q−1)/24)`.

1. **q-expansion** (`Expansion.hasSum_TF`): `e(z/24) T F(z) = Σ_N B(N) qᴺ` with
   `B(N) = c(Q²N−d) + c_M g_Q ((24N−1)/Q) c(N) + Q^{2k−3} c((N+d)/Q²)`, `d = (Q²−1)/24`,
   `c = q-coefficients of G·P`. Ingredients: the repo's expansion of `G/η` (`ThetaLift.HalfExpansion`),
   `Σ_{x mod Q²} e(xn/Q²) = Q²[Q² ∣ n]` and the twisted Gauss sum `Σ (x/Q)e(xn/Q) = (n/Q) g_Q`
   (`Gauss.charSum`, from Mathlib's `gaussSum_mulShift`).
2. **S-covariance** (`SInv.TF_S`): `η(−1/z) TF(−1/z) = z^k η(z) TF(z)`. S permutes the cosets:
   `d=1 ↔ (d=Q², b=0)`, `(d=Q², Q∤b) ↔ (d=Q², b')` with `576bb' ≡ −1 (Q²)`, `(d=Q², b=Qb₁) ↔ (d=Q, b₂)`
   with `576b₁b₂ ≡ −1 (Q)`, via `γ = [24b, ·; Q² or Q, −24b']`. Each γ has odd positive `c`, so
   Petersson's formula already in the repo (`ThetaLift.etaLaw_odd`) gives the multiplier
   (`Transfer.transfer`, `SFacts.mult_Q2`, `mult_Q`); the reindexing is by the involutions
   `x ↦ −(576x)⁻¹` (`Reindex`, `SFacts.sum_sig1/2`). The constant `c_M` is forced here.
3. **Modularity** (`Main.Hform`): `H = η·TF = E·Σ B(N)qᴺ` is holomorphic, 1-periodic and bounded at ∞
   (coefficients polynomially bounded from the repo's Hecke bound `norm_cA_le`), S-invariant by (2), hence
   in `M_k(SL₂ℤ)` (`slash_action_generators_SL2Z`); `qExp_Hform` gives its expansion.
4. **Gauss sign**: the q-expansion middle term is `c_M g_Q (m/Q)`, which equals heckeHalf's
   `χ₁₂(Q)((−1)^λ m/Q)Q^{λ−1}` iff `g_Q` has Gauss's sign. Mathlib has `g_Q² = (−1/Q)Q` but not the sign,
   so it is the named hypothesis `GaussSign Q k`, proved for `Q = 11` (`gQ_11 : g = i√11`) and `Q = 37`
   (`gQ_37 : g = √37`) by pairing residues with larger non-residues and monotonicity of `sin`/`cos`
   (`GaussSign.lean`).
5. `EtaHecke.etaHecke_of_sign` matches `B` with `heckeHalf` and takes `a' = E·heckeHalf(a·P)`;
   `EtaHecke.toMod 13` feeds the existing `atkin_13`, `atkin_13_class`, `atkin_13_Q37_class`.

Cheaper alternatives considered: the Shimura-lift route fails (dim W = 7, see
`ATKIN_SPORADIC_CONGRUENCES.md`); a mod-13 Sturm argument on Γ₀(576·Q²) would need ~10⁶ coefficients
and half-integral-weight Sturm theory. The coset construction with S, T generators avoided the
even-`c` η-multiplier, double-coset theory and holomorphy at other cusps entirely.

## Files

| file | content |
|---|---|
| `HalfHecke/Gauss.lean` | `chiQ`, `gQ`, `charSum`, `gQ_sq` |
| `HalfHecke/GaussSign.lean` | `gQ_11`, `gQ_37` |
| `HalfHecke/Expansion.lean` | `Fc`, `TF`, `Bc`, `hasSum_V/M/U`, `hasSum_TF` |
| `HalfHecke/Transfer.lean` | `transfer` (η-multiplier step), `Gc_mob`, `sqrt_ofReal_mul` |
| `HalfHecke/Reindex.lean` | `sig`, `iota`, `sum_split` |
| `HalfHecke/SFacts.lean` | multipliers `mult_S`, `mult_Q2`, `mult_Q`; character identities; `sum_sig1/2` |
| `HalfHecke/SInv.lean` | `cMd`, five coset cases, `TF_S` |
| `HalfHecke/Main.lean` | `Bc_bound`, `Hf`, `Hf_T`, `Hf_S`, `Hform`, `qExp_Hform` |
| `HalfHecke/EtaHecke.lean` | `GaussSign`, `etaHecke_of_sign`, `gaussSign_11/37`, `etaHecke_11_168`, `etaHecke_37_168`, `etaHeckeMod_13_11/37` |
| `AtkinSporadic/Atkin13Unconditional.lean` | the three unconditional corollaries |

Build: `nice -n 10 lake build RamanujanTau.AtkinSporadic.Atkin13Unconditional`, then
`nice -n 10 lake env lean scripts/halfhecke/audit.lean`. Not added to the root import at the time (since added).

## What remains / extensions

* `GaussSign Q k` for general `Q` is the classical Gauss sign theorem (level (3) here); proving it in
  general (e.g. via theta transformation) would make `EtaHecke Q k 1` unconditional for all `Q ≥ 5`.
  For any specific `Q` it can be discharged as for 11 and 37. (Done: `GaussSign.etaHecke_all`, via
  `GaussSign.gaussSign_of_even`, for every prime `Q ≥ 5` and `k ≥ 2`; see the caution at the top for odd `k`.)
* Other `j` (`η^{−j}`, `gcd(j,6)=1`): the same construction should work with the translations `24x`
  and the multiplier exponents scaled by `j`; not done.
