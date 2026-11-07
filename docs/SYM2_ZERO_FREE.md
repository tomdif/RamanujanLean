# A zero-free region for `ζ(s)L(Sym²Δ,s) = ζ(2s)R(s)` and for `R(s) = Σ λ(n)² n^{−s}`

Lean: `RamanujanTau/Sym2ZeroFree/` (4 files, about 760 lines). There is no `sorry`, no new axiom
and no `native_decide`. Build with `nice -n 10 lake build RamanujanTau.Sym2ZeroFree.Main`; it
exits 0. The module is not imported from `RamanujanTau.lean`.

**Evidence level (1).** The results are unconditional and axiom-clean. All 16 `#print axioms` lines
print `[propext, Classical.choice, Quot.sound]`. There are no named hypotheses. `DeligneBound` is
not used, and neither is any GL(3) or GL(5) input (Gelbart–Jacquet, Sym⁴, or `L(Sym²×Sym²)`).

## 1. The route (paper)

### 1.1 The obvious route needs functions the repo cannot continue

The textbook de la Vallée-Poussin argument for `π = Sym²Δ` uses `L(Π×Π̃)` with
`Π = 1 ⊞ π|·|^{iγ} ⊞ π|·|^{−iγ}`. That product contains `L(Sym²Δ × Sym²Δ, s) = ζ(s)L(Sym²Δ,s)L(Sym⁴Δ,s)`.
Its analytic continuation and polynomial growth need GL(3)×GL(3) Rankin–Selberg theory, or Kim–Shahidi
for Sym⁴. None of that is in the repo. `docs/SELBERG_COEFFS.md` §7 estimated this route at 2–4k
lines plus those inputs.

### 1.2 The cheap route: 3–4–1 directly on `L(Δ×Δ, s)`

Put `H(s) = ζ(2s)R(s) = L(Δ×Δ, s) = ζ(s)L(Sym²Δ, s)`. The repo has this function as `HH`. Then:

* `log H(s) = Σ cR(n) n^{−s}` with `cR(p^k) = (α_p^k + β_p^k)²/k ≥ 0`. This is
  `TauPNTUncond.RSLog.exp_LSeries_cR`. It needs no Deligne: `α_p^k + β_p^k` is real because
  `α_p + β_p = λ(p)` is real and `α_pβ_p = 1`.
* `H` has a simple pole at `s = 1` and nothing else near `Re s = 1`. `KK = (s−1)H` is holomorphic
  on `s ≠ 0`, by `RankinSelbergFE`.

So `H` itself can play the role of `ζ` in the classical proof. Take

  `F(σ) = H(σ)³ · H(σ+iγ)⁴ · H(σ+2iγ)`.

Then `log ‖F(σ)‖ = Σ cR(n) n^{−σ} Re(3 + 4n^{−iγ} + n^{−2iγ}) ≥ 0`. Each term is non-increasing in
`σ`.

In representation language, `F` is `L(Π×Π̃)` for `Π = Δ ⊞ Δ|·|^{iγ} ⊞ Δ|·|^{2iγ}`, up to the
Fejér weights. Its pole order is 3, and a zero `ρ = β+iγ` of `H` contributes order 4.
**Only GL(2)×GL(2) Rankin–Selberg is needed, and the repo already has it.** This is the standard
remark that any `L`-function with non-negative log-coefficients and a simple pole has a
de la Vallée-Poussin region (Iwaniec–Kowalski, Thm 5.10 and §5.12, in the case `L(f×f̄)`).
A zero of `H` is a zero of `ζ` or of `L(Sym²Δ)`, so the region covers both factors at once.

### 1.3 Remaining steps

The rest is the argument of `ZeroFreeRegion` (see `docs/ZERO_FREE_REGION.md`), almost verbatim:

* **Sign.** `Ψ = (z−1)³F(z)` satisfies `Re Ψ'/Ψ(1+δ) ≤ 3/δ`, because `‖F(σ)‖` is antitone.
* **Landau's lemma.** Apply `ZeroFreeRegion.landau` with `m = 4` and `r = 1/4`.
* **Growth.** The needed bound is `‖H(w)‖ ≪ |w|` for `3/4 ≤ Re w`, `|Im w| ≥ 1/2`. It comes from
  `H = ζ(2·)·Rt`, where `Rt` is the Abel continuation with Rankin's `O(N^{3/5})` error (this needs
  the identity theorem, step 1 of §3), together with `‖ζ(2w)‖ ≤ ζ(3/2)`. Then
  `‖Ψ‖ ≤ B(9+|γ|)^5` on the disc.
* **Result.** `4/(δ+η) ≤ 3/δ + 48 log(B(9+|γ|)^{10}/δ³)`. Setting `δ = 1/(2592 log|γ|)` gives
  `η ≥ 1/(18144 log|γ|)`.

### 1.4 Small heights and exceptional zeros

* `KK ≠ 0` on the whole closed half-plane `Re s ≥ 1`, including `s = 1`, where `KK(1) = ‖Δ‖²γ(1)⁻¹`
  (`TauPNTUncond.KK_ne_zero`).
* `KK` is continuous, so a compactness argument (`IsCompact.exists_thickening_subset_open`) gives
  `ε > 0` with no zeros in `{|Im s| ≤ t₀, Re s > 1 − ε}`.
* Hence the region holds at all heights. In particular there is no real zero in `(1−ε, 1)`.
* **This is ineffective.** It is qualitatively the same as "no Siegel zero" for one fixed form.
  An effective version would need:
  * `ζ(σ) < 0` on `(0,1)`, which is cheap;
  * the Hoffstein–Lockhart / Goldfeld–Hoffstein–Lieman theorem that `L(Sym²f, s)` has no
    exceptional zero, which is not cheap. It needs the adjoint lift and the GHL auxiliary
    `L(Π×Π̃)` with `Π = 1 ⊞ Sym²f ⊞ …`;
  * or a numerical certificate for `L(Sym²Δ, σ) ≠ 0` on `[1−ε,1]` (level 4).

  The uniform constant also inherits `t₀`, which depends on existential constants: Rankin's error
  constant and a compactness bound for `KK` near 1.

### 1.5 Is this region enough for Selberg–Delange?

**Yes, for the main term with a `1/log` saving. It is more than the `(log y)^{−1/2}` saving that
(QF) needs.**

The Selberg–Delange method for `Σ a(n)n^{−s} = G(s)·(s−1)^{κ}`-type series needs four things:

1. `R(s)^{−1/2} = (ζ(2s)/H(s))^{1/2}` must be holomorphic in `σ > 1 − c/log(|t|+3)`, except on the
   slit `[1−c/log 3, 1]`. Equivalently, `KK = (s−1)H` must be non-zero there. **This is done:**
   `KK_zero_free_region_uniform`. The region is simply connected and `KK ≠ 0` on it, so
   `log KK` exists. Note that **no zero-free region for `ζ(s)` alone is needed**: only `ζ(2s)`
   enters, and that is harmless for `σ > 1/2`.
2. A growth bound `|log KK(s)| ≤ A log log(|t|+3) + O(1)`, or `|KK(s)^{±1/2}| ≪ (log t)^{A}`, in the
   smaller region `σ ≥ 1 − c/(2 log(|t|+3))`. **Not done.** The standard proof first bounds
   `−H'/H ≪ log t` in the half-region by Landau / Borel–Carathéodory, then integrates from `σ = 2`.
   The repo's `TauPNTError/LogDerivBound.lean` (`negLogDeriv_bound`, for `L(Δ)`) is the template.
   Every input it uses has an `H` analogue here: the disc growth bound `norm_PsiS_le` / `norm_HH_le`
   and the zero-free region. Estimate: 0.5–1k lines.
3. The Hankel-contour evaluation `(1/2πi)∫ (s−1)^{−κ} x^s ds/s`, with truncation. **Not done.**
   Estimate: about 2k lines.
4. Coefficient bounds for the Dirichlet polynomial side. These are already present
   (`SelbergCoeffs2/3`, `[DeligneBound]` where `|α(p^k)| ≤ 1` is used).

With a region of shape `1 − c/log t`, the method gives `Σ_{n≤x} a(n)/n = C(log x)^{κ} + O((log x)^{κ−1})`.
That is a full `1/log` saving. Even a weaker region `1 − c/log^A t` would give this main term with
an `O((log x)^{κ−1})` error, since only the contour near `s = 1` matters at that precision.

## 2. Statements

```lean
namespace RamanujanTau.Sym2ZeroFree
-- HH = ζ(2s)R(s) continued (TauPNTUncond.HH), KK = (s−1)HH, Rcont = HH/ζ(2s), Lsym2 = HH/ζ

theorem HH_zero_free_region : ∃ c > 0, ∃ t₀ : ℝ, ∀ s : ℂ, HH s = 0 → t₀ ≤ |s.im| →
    s.re ≤ 1 - c / Real.log |s.im|                                   -- c = 1/18144
theorem KK_zero_free_region_uniform : ∃ c > 0, ∀ s : ℂ, KK s = 0 →
    s.re ≤ 1 - c / Real.log (|s.im| + 3)
theorem HH_ne_zero_region : ∃ c > 0, ∀ s : ℂ, s ≠ 1 →
    1 - c / Real.log (|s.im| + 3) < s.re → HH s ≠ 0
theorem Rcont_ne_zero_region : ∃ c > 0, ∀ s : ℂ, s ≠ 1 →
    1 - c / Real.log (|s.im| + 3) < s.re → RankinSelbergFE.Rcont s ≠ 0
theorem Lsym2_ne_zero_region : ∃ c > 0, ∀ s : ℂ, s ≠ 1 → riemannZeta s ≠ 0 →
    1 - c / Real.log (|s.im| + 3) < s.re → Lsym2 s ≠ 0
```

Supporting results:

* `KK_eq_zeta_R1`: `KK s = ζ(2s)·R1 s` on `Re s > 3/5`, by the identity theorem.
* `HH_eq_zeta_Rt`: `HH s = ζ(2s)·Rt s` on `Re s > 3/5`, `s ≠ 1`.
* `norm_HH_le`: `‖HH w‖ ≤ C‖w‖` for `3/4 ≤ Re w`, `1/2 ≤ |Im w|`.
* `norm_FS_antitone`, `one_le_norm_FS`: positivity of the 3–4–1 product.
* `PsiS_real`, `four_le_order_PsiS`, `norm_PsiS_le`, `re_logDeriv_PsiS_le`, `coreS`: the
  auxiliary function and the core inequality.
* `KK_ne_zero_near_edge`: the compactness step.

**About `Lsym2`.** In Lean, `Lsym2 = HH/ζ` takes the junk value `0` at zeros of `ζ`. The genuine
statement about `ζ(s)L(Sym²Δ,s)` is therefore `HH_ne_zero_region`. A separate zero-free region for
`L(Sym²Δ)` alone would follow once its holomorphy is known, which needs Shimura's continuation and
is not in the repo. It would also follow from a ζ zero-free region, which would be a cheap copy of
this argument using `−ζ'/ζ = L(Λ)`. Neither is done; neither is needed for §1.5.

## 3. Files

| file | content |
|---|---|
| `Basic.lean` | `KK_eq_zeta_R1`, `HH_eq_zeta_Rt`, `norm_HH_le`, `FS`, `aS`, `norm_FS_eq`, `norm_FS_antitone`, `one_le_norm_FS` |
| `Psi.lean` | `PsiS = HH(z+iγ)⁴ · KK(z)³ HH(z+2iγ)`, holomorphy on `Om`, `PsiS_real`, `PsiS_ne_zero`, `four_le_order_PsiS`, `norm_PsiS_le` |
| `Region.lean` | `re_logDeriv_PsiS_le`, `coreS`, `HH_zero_free_region`, `KK_ne_zero_near_edge`, `KK_zero_free_region_uniform`, `HH_ne_zero_region`, `Rcont_ne_zero_region`, `Lsym2_ne_zero_region` |
| `Main.lean` | `#print axioms` (16 lines) |

Reused from the repo:

* `ZeroFreeRegion`: `landau`, `Rt`, `R1`, `norm_Rt_le`, `Om`, `ball_facts`, `norm_zeta_le_of_re`,
  `accPt_Ioi`, `re_div_eq`.
* `TauPNTUncond.Edge`: `HH`, `KK`, `HH_exp`, `KK_ne_zero`, `re_comb_nonneg`, `term_shift`.
* `RSLog`: `cR`, `cR_nonneg`, `LSeriesSummable_cR`.

## 4. Gaps

* **Ineffective constants** at small heights, and `t₀`. See §1.4.
* **Not done: log / log-derivative bounds in the region** (§1.5, item 2). This is the next
  prerequisite for Selberg–Delange.
* **Not done: the left mirror** `Re s ≥ c/log t`, from the functional equation `R*(s) = R*(1−s)`.
  It is easy but not needed.
* **Correction to `docs/SELBERG_COEFFS.md` §7.** The cost estimate there ("`L(Sym²×Sym²)`-positivity,
  2–4k lines, level 2 on `[DeligneBound]`") is superseded. The zero-free region is level 1, about
  760 lines, and needs no Deligne.

## 5. Literature

* de la Vallée Poussin (1899); Landau, *Handbuch* (1909).
* Iwaniec–Kowalski, *Analytic Number Theory*, Thm 5.10, §5.12 (Rankin–Selberg `L(f×f̄)`), and
  Thm 5.42 / Thm 5.44 (Sym² and the exceptional zero). These theorem numbers are from memory and
  have not been checked.
* Hoffstein–Lockhart, *Coefficients of Maass forms and the Siegel zero*, Ann. Math. 140 (1994),
  with the appendix by Goldfeld–Hoffstein–Lieman (no Siegel zero for `L(Sym²f)`).
* Selberg–Delange: Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, II.5.
* Moreno (1977) and Ogg (1969): Rankin–Selberg non-vanishing on `Re s = 1`.
