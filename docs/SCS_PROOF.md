# Discharging `ShiftedConvolutionBound η B` — route analysis and proof plan

**Status (2026-11-05): DONE, evidence level 1 (Lean, axiom-clean, no hypotheses).**
`ShiftedConvolutionBound (1/8000) 8` is proved unconditionally (the exact Rankin `N^{3/5}` error from
`RankinExact.rankinSelberg_exact` is used; the earlier `1/2^22` version is a corollary), hence unconditional t-aspect
subconvexity for `L(Δ,s)`.  Directory: `RamanujanTau/SCSProof/` (41 files, ≈5.4k lines).  See §6.

Target: `|Σ_{n≤N} λ(n)λ(n+h)| ≤ C (N+h)^{1−η} h^B` for all `h ≥ 1`, `N` (sharp cutoff),
`λ(n) = τ(n) n^{−11/2}`, for SOME `η > 0`, `B ≥ 0`.  Write `a_n = τ(n)τ(n+h)` and
`G_h(W) = Σ_{n≥1} a_n e^{−nW}` (`Re W > 0`).

## 1. The cheap route and why it cannot reach sharp sums (Laplace obstruction)

The cheapest power saving is spectral-free and Kloosterman-light:

* `F(z) = y¹²|Δ(z)|²` is bounded and `Γ`-invariant; its `h`-th horocycle coefficient is
  `F_h(y) = y¹² e^{−2πhy} G_h(4πy)` (`Subconvexity.hasSum_shifted_parseval`).
* Incomplete Poincaré series `P(z) = Σ_{Γ∞\Γ} ψ(Im γz) e(h Re γz)`, `ψ = 1_{[Y,2Y]}`.
  Unfolding: `⟨F,P⟩ = ∫ ψ(y) F_h(y) dy/y²`; `‖P‖² = ∫ψ²/y² + Σ_{c≥1} S(h,h;c) J_c` with
  `|J_c| ≤ 2√2/(cY)` and `J_c = 0` for `c > √2/Y` (pure support bookkeeping, no oscillatory
  integral analysis).  Weil `|S(h,h;c)| ≪ (h,c)^{1/2} c^{1/2+ε}` gives `‖P‖² ≪ h^{1/2} Y^{−3/2−ε}`.
* Cauchy–Schwarz: `∫_Y^{2Y} F_h(y) dy/y² ≪ h^{1/4} Y^{−3/4−ε}` vs. trivial `≍ 1/Y`:
  a saving `Y^{1/4−ε}` — the Selberg/Weil exponent — **but only for the real Laplace weights**
  `n ↦ ∫ψ(y) y^{10} e^{−4πny} dy`.

**Obstruction.** Every weight reachable this way is a Laplace transform `∫ g(y) e^{−ny} dy`; its
Mellin transform carries a factor `Γ(s)`, i.e. decays like `e^{−π|t|/2}`.  Approximating the sharp
cutoff `1_{n≤N}` (Mellin `1/s`) within width `N^{1−η}` needs Mellin control up to `|t| ≍ N^η`, which
costs `e^{cN^η}`.  This is a genuine Tauberian obstruction, not a technicality: the sequence
`a_n = n^{iT_k}` on blocks `[N_k, 2N_k]` with `T_k = (2π)^{−1} log N_k` satisfies all real-Laplace
bounds `Σ a_n e^{−nY} ≪ Y^{−3/4}` yet `Σ_{n≤N} a_n ≍ N/log N` (Korevaar, *Tauberian theory*,
Ch. VII: real-Laplace power remainders give only logarithmic remainders for partial sums).
The same obstruction kills route (ii) (horocycle Fourier coefficients of any `Γ\H`-function
built from `F` by invariant differential operators: all give polynomial×Laplace weights), and
the Selberg route b1–b4 of `SUBCONVEXITY.md` as sketched there: unfolding gives
`⟨F, P_h(·,s̄)⟩ = Γ(s+11)(4π)^{−s−11} D_h(s)`, and Cauchy–Schwarz cannot supply the
`e^{−π|Im s|/2}` decay of `⟨F,P_h(·,s̄)⟩` needed to get polynomial growth of `D_h`; Selberg/Good get
it from the spectral decomposition (not available), DFI from Voronoi + Bessel asymptotics.

## 2. The fix: complex Laplace directions from a two-point invariant on `Γ\(ℍ×ℍ)`

We need `G_h(W)` for `arg W` up to `π/2 − N^{−η}`.  Such values are horocycle coefficients of a
**two-point** function.  For `z, w ∈ ℍ` put

    Ψ(z,w) = (z − w̄)^{12} Δ(z) conj Δ(w).

* `Ψ(γz,γw) = Ψ(z,w)` for `γ ∈ SL₂(ℤ)` (diagonal action): `γz − γw̄ = (z−w̄)/(j(γ,z) j(γ,w̄))`
  cancels the automorphy factors of `Δ(γz)` and `conj Δ(γw) = conj j(γ,w)^{12} conj Δ(w)`.
* `|Ψ| ≤ M² (|z−w̄|²/(Im z Im w))^6`, `M = sup y⁶|Δ|`, and `|z−w̄|²/(Im z Im w) = 4cosh²(d/2)`
  depends only on the hyperbolic distance — bounded on `{d(z,w) ≤ R}`.
* Diagonal horocycle coefficient: with `w = x + yζ` (`ζ ∈ ℍ` the relative position),

      ∫₀¹ Ψ(x+iy, x+yζ) e(−hx) dx = y^{12}(i − ζ̄)^{12} e^{−2πhy} G_h(2πy(1 + iζ̄)),

  and `2πy(1 + iζ̄) = 2πy((1+Im ζ) + i Re ζ)` has **arbitrary argument** in `(−π/2, π/2)`.

(Equivalently `Γ\G`, the unit tangent bundle: pairs at distance `r`; the `ℍ×ℍ` model needs no
group theory and the fundamental domain is `U × ℍ`, so the repo's `lintegral_unfold_U` applies
fibrewise.)

**Test function.** `f(z,w) = 1_{[Y,Y(1+ε)]}(Im z) e(h Re z) 1_B(ζ)`, `ζ = (w − Re z)/Im z`,
`B = {|Re ζ − θ| ≤ ε, |Im ζ − 1| ≤ ε}`; `f(z+t,w+t) = e(ht) f(z,w)`.
`P(z,w) = ½ Σ_{γ∈SL₂(ℤ)} f̃(γz,γw)`, `f̃ = 1_{strip}(Re z) f`.

* Unfolding: `∫_{U×ℍ} Ψ conj P = ∫_{strip×ℍ} Ψ conj f = ∫∫ (coefficient above) dμ(ζ) dy/y²`.
* `‖P‖²_{U×ℍ} = ∫_{strip×ℍ} f conj P = ∫|f|² + Σ_{c≥1} S(h,h;c) J_c`, using
  `γu = a/c − 1/(c²(u + d/c))` and `f(γz,γw) = e(ha/c) f(ι_c(z+d/c), ι_c(w+d/c))`,
  `ι_c u = −1/(c²u)`; the `d mod c` sum with `a ≡ d̄` gives `S(h,h;c)`.
  `|J_c| ≤ μ(B) (ε/Y)(2√2/c)`, `J_c = 0` for `c > 1/Y`.  Weil:
  `‖P‖² ≪ μ(B)(ε/Y) h^{1/2} Y^{−1/2−δ}`.
* `∫_{U×ℍ} |Ψ|² 1_{P≠0} ≪ (θ+1)^{29}` (`P ≠ 0` forces `d(z,w)` bounded in terms of `θ`;
  hyperbolic balls of radius `R` have measure `≪ e^{2R}`).
* Cauchy–Schwarz + Lipschitz continuity of `G_h` on the box (`|G_h(W)−G_h(W')| ≤ |W−W'|
  Σ n|a_n|e^{−n min Re}`), with `μ(B) ≍ ε²`, `ε = Y^{1/10}`:

      (*)  (Re W)^{12} |G_h(W)| ≪ (1 + |Im W|/Re W)^{5/2} h^{1/4} (Re W)^{1/10 − δ},
           for Re W ≤ σ₀, h·Re W ≤ 1.

  (As formalized, with cruder bookkeeping — AM–GM instead of a square root, `δ = 1/40`,
  `|Ψ| ≤ M R⁶` with `R = 2(|θ|+3)²` — the proved bound is `pointwise_G`:
  `‖G_h(σ+iτ)‖ ≤ K h (|2τ/σ|+3)³² σ^{−12+3/40}` for `h ≥ 1`, `0 < σ ≤ 1`, `hσ ≤ 1`.)

  (Trivial: `(Re W)^{12}|G_h(W)| ≪ 1`.)  Numerically (PARI, `N = 3·10⁴`): `σ^{12}|G_1(σ(1+iθ))|`
  is `10²–10⁴` times smaller than the `h = 0` main term `1.53·10⁷` for `σ ∈ {.02,.005,.00125}`,
  `θ ∈ {0,1,4,16}`, consistent with (*).

## 3. From (*) to sharp sums (exponential-Riesz kernel, no Perron truncation)

`(1/2πi)∫_{(c)} e^{tW} dW/(W(1+LW)) = (1 − e^{−t/L}) 1_{t>0}` (Mellin inversion of the repo's
`RankinError.mellinInv_Pk`, `k=1`, after `u = e^{−t/L}`), so with `c = 1/x`

    Σ_{n<x} a_n (1 − e^{−(x−n)/L}) = (1/2π) ∫ G_h(c+iv) e^{x(c+iv)} dv / ((c+iv)(1+L(c+iv))).

* `|v| > V`: trivial `|G_h| ≪ x^{12}`, kernel `≤ 1/(L v²)` ⇒ `≪ x^{12}/(LV)`.
* `|v| ≤ V`: (*) with `|Im W|/Re W ≤ Vx` ⇒ `≪ x^{12−1/10+δ}(Vx)^{5/2} h^{1/4} log x`.
* `Σ_{n<x} a_n e^{−(x−n)/L} ≪ (x+h)^{11}(L + x^{1−ρ})` from the Rankin asymptotic with error
  (`RankinError.rankinSelberg_power_saving_unconditional`, `ρ = 2^{−22}`) on blocks of length `L`.
* `L = x^{1−κ}`, `V = x^{2κ}/x`: all errors `≪ x^{12−κ'}h^{1/4}` for a small explicit `κ'`;
  partial summation with `(n(n+h))^{−11/2}`; `h > N^{small}` by the trivial bound.

Result (as formalized): `SCS(1/8000, 8)` with the repo's exact Rankin error `N^{3/5}`.

## 4. Route comparison (Lean cost)

| route | needs | verdict |
|---|---|---|
| Γ\H incomplete Poincaré + C–S (§1) | unfolding, Bruhat, Weil | **insufficient** (Laplace obstruction) |
| Selberg `P_h(z,s)` (b1–b4) | polynomial growth of `D_h` in `Im s` | needs spectral theory; C–S gives exponential growth only |
| DFI δ-method / Jutila | Voronoi with `J₁₁` kernels + Bessel transform bounds | ≈ 4–6k lines |
| **two-point Ψ on Γ\(ℍ×ℍ) (§2–3)** | unfolding on `U×ℍ`, Bruhat + Kloosterman (`S(h,h;c)`), Weil, Lipschitz, exp-Riesz | **chosen**: no oscillatory-integral asymptotics, no spectral theory |

## 5. Lean module plan (`RamanujanTau/SCSProof/`)

1. `Kloost.lean` — `|S(h,h;c)| ≤ A h^{1/2} c^{1/2+δ}` (reduction `g = (h,c)`, fibres of
   `(ℤ/c)^× → (ℤ/c')^×`, then `kl_unit_eq` + `Discharge` Weil bound for `S(1,·;c')`).
2. `TwoPoint.lean` — `Ψ`, invariance, bound, diagonal horocycle coefficient.
3. `Unfold2.lean` — `∫_{U×ℍ} 1_U Σ_γ g(γz,γw) = 2∫ g`.
4. `Bruhat.lean` — `‖P‖²` via Kloosterman sums; support bounds.
5. `Pointwise.lean` — (*).
6. `Tauber.lean` — §3.
7. `Main.lean` — `shiftedConvolutionBound_of`, `tauL_subconvex`.

## 6. Status (what is proved)

Build: `nice -n 10 lake build RamanujanTau.SCSProof.Main` exits 0; every `#print axioms` in
`SCSProof/Main.lean` gives `[propext, Classical.choice, Quot.sound]`; `grep` finds no
`sorry`/`admit`/`native_decide`/`axiom` in `RamanujanTau/SCSProof/`.  No existing file modified.

Headlines (`RamanujanTau.SCSProof`):

* `instance shiftedConvolutionBound_3_5 : ShiftedConvolutionBound (1 / 8000) 8`, i.e.
  `|Σ_{n≤N} λ(n)λ(n+h)| ≤ C (N+h)^{1−1/8000} h⁸` for all `h ≥ 1`, `N`.
* `instance shiftedConvolutionBound_of : ShiftedConvolutionBound (1 / 2 ^ 22) 8` (kept; now via `.mono`).
* `tauL_subconvex_3_5 : ∃ C ≥ 0, ∀ t, ‖tauL (6 + t*I)‖ ≤ C * (1 + |t|) ^ (1/2 − 1/832000)`
  (`SubconvexityCond.tauL_subconvex_of_SCS`, `δ = subconvexDelta (1/8000) 8 = 1/832000`).
* `tauL_subconvex : ∃ δ > 0, ∃ C, ∀ t, ‖tauL (6 + t*I)‖ ≤ C * (1 + |t|) ^ (1/2 − δ)` (kept).

Intermediate results (all level 1):

| file | content |
|---|---|
| `Kloost` | `norm_kloosterman_hh_le`: `‖S(h,h;c)‖ ≤ A_δ h c^{1/2+δ}` (Weil, all `c`, uniform in `h`) |
| `TwoPoint` | `Psi_smul` (invariance), `norm_Psi_le`, `coeff_Psi` (diagonal horocycle coefficient = `G_h` at complex points) |
| `Unfold2` | `lintegral_unfold2`, `integral_unfold2` (unfolding on `U × ℍ`) |
| `Measures`, `Test`, `Bounds`, `Coord` | affine invariance, box bounds, test function, local finiteness `count_le`, invariant `Dh`, `integral_H` |
| `Bruhat1–8` | Bruhat decomposition: `hasSum_right_T`, `Rg_eq`, `hasSum_K`, Kloosterman phase `norm_phase_sum`, `Tl_eq`, `norm_tsum_Iγ_le` (`‖P‖² ≪ h ε³ Y^{−3/2−2δ}`) |
| `CS–CS4` | `μ(U) ≤ 2`, unfolding of `Ψ` and `‖Pt‖²`, Hölder: `norm_Q_le` |
| `Qform–Qform3` | skew-product change of variables, `Q_eq` (pairing = ∫∫ of horocycle coefficients) |
| `Gbounds*` | Parseval bound `Σ τ(n)²e^{−nσ} ≪ σ^{−12}`, Lipschitz bound for `G_h` |
| `Main1–4`, `Point1–4` | main-term comparison, lower bounds for `μ(I), μ(B)`, Lipschitz of `cf`, `pointwise_G` |
| `Tauber1–6` | exponential-Riesz Mellin inversion `laplace_riesz`, `Rmean_bound`, `rankin_short`, `Asum_bound_large` |
| `Final1–2` | uniform `Asum_bound`, Abel summation (`sum_mul_eq_sub_integral_mul₀'`), `shiftSum_bound` |

The Rankin–Selberg error term enters only through short sums of `λ(n)²` (`Tauber4.rankin_short`,
now from `RankinExact.rankinSelberg_exact`, `N^{3/5} ≤ N^{1−ρ}`); with `3/5` it is no longer the
bottleneck, and `η₀ = ρ = 1/8000` is set by the analytic part (`Rmean_bound`, saving `x^{1/8000}`,
and the tail cut-off `L = x^{1−1/4000}`).  Not optimized; Selberg's
`1/3` was not pursued.

Literature: Selberg (1965) and Good (1981) for the shifted Dirichlet series; Weil (1948) for
Kloosterman sums (`StepanovAS.weilPrimeBound` in the repo).  The two-point (unit tangent bundle)
function is used here only as a device to reach non-real Laplace directions; I have not checked
whether this exact argument appears in the literature.  The formal route avoids spectral theory,
Voronoi summation and stationary phase entirely.
