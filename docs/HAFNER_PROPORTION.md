# Positive proportion of critical zeros of L(Δ,s) (Selberg–Hafner)

Module: `RamanujanTau/HafnerProportion/` (entry point `Main.lean`).
Build: `nice -n 10 lake build RamanujanTau.HafnerProportion.Main` (exit 0). Every theorem below
prints `[propext, Classical.choice, Quot.sound]`. There is no `sorry`, no new axiom and no
`native_decide`.

**Status.** The full theorem is **not** proved. What this module contains:

* the Selberg reduction, formalized;
* Selberg's first-moment input (H1), proved unconditionally for L(Δ,s);
* (H2), reduced to the mollified second moment;
* the final count, conditional on one named hypothesis `SelbergHyp`. That hypothesis says no
  more than two classical mean-value estimates (MV2) and (SK), and it mentions no zeros.

The statement proved conditionally is the target: N₀(T) ≫ T log T, and N₀ ≥ c·N against
Riemann–von Mangoldt.

## 1. The Selberg–Hafner argument for Δ

Notation:

* λ(n) = τ(n)n^{−11/2}.
* The repo's line is Re s = 6, so L(Δ, 6+it) = Σ λ(n) n^{−1/2−it}.
* Λ(s) = (2π)^{−s}Γ(s)L(Δ,s), with Λ(12−s) = Λ(s).

**Hardy's function.** Z(t) = (2π)⁶ Λ(6+it)/|Γ(6+it)|.

* Z is real, because Λ(6+it) is real (`HardyZeros.Zc_eq_Zr`).
* |Z(t)| = |L(Δ,6+it)| (`norm_tauL_line`).
* Z(t) = 0 implies L(Δ, 6+it) = 0 (`tauL_zero_of_ZH_zero`).

**Mollifier.**

* M(s) = Σ_{1≤n≤y} b(n) n^{11/2−s} (`Mc`). On the line this is M(6+it) = Σ b(n) n^{−1/2−it}.
  We write w(t) = |M(6+it)|² (`wM`).
* Selberg's choice is b(n) = α(n)(1 − log n/log y), where the α(n) are the Dirichlet
  coefficients of L(Δ,s)^{−1/2} (in the analytic normalization).
* α is multiplicative with α(p) = −λ(p)/2, and |α(n)| ≤ d(n) under Deligne.
* The length is y = T^θ with θ > 0 small.

**Short integrals.** With h = K/log T and K a large constant:

    I(t) = ∫_t^{t+h} Z(u) w(u) du,     J(t) = ∫_t^{t+h} |Z(u)| w(u) du = ∫_t^{t+h} |L M²|(6+iu) du.

If |I(t)| < J(t), then Z changes sign in [t, t+h] (`exists_zero_of_abs_lt`).

**Measure argument** (`selberg_measure`). Let S = {t ∈ [T,2T] : |I| < J}.

* Off S we have J = |I|. On S we use AM–GM, |x| ≤ (λx² + 1/λ)/2. This replaces Cauchy–Schwarz.
* Hence the three conditions

      (H1) ∫_T^{2T} J ≥ aTh,   (H2) ∫_T^{2T} J² ≤ BTh²,   (H3) ∫_T^{2T} I² ≤ (a²/16)Th²

  give |S| ≥ 5a²T/(16B).
* Covering S by the intervals [γ−h, γ] then gives at least |S|/h distinct zeros
  (`zeros_of_measure`).
* So N₀(3T) − N₀(T) ≥ (5a²/16BK)·T log T (`selberg_zeros`).

**Where the inputs come from.**

| input | statement for Δ | source of the estimate |
|---|---|---|
| (H1) | ∫_{T+h}^{2T} \|L M²\| ≥ T/4 | first moment of L·M² |
| (MV2) ⇒ (H2) | ∫_T^{3T} \|L(6+it)M(6+it)²\|² dt ≪ T | twisted second moment ∫\|L\|²(m/n)^{it}, m,n ≤ y² |
| (SK) = (H3) | ∫_T^{2T} I(t)² dt ≪ T h² (h log T)^{−1/2} = T h² K^{−1/2} | Selberg's key lemma |

* (H1) is proved here with a = 1/4, by Cauchy's theorem on [6, σ₁] × [a, c]. The far line uses
  \|L−1\|, \|M−1\| ≤ 1/32, uniformly in y. The horizontal sides are ≪ T^{1/2+ε}y^{2+2η}.
  No arithmetic input is needed.
* (MV2) is the diagonal plus an off-diagonal term. The off-diagonal is controlled by shifted
  convolution sums Σ λ(n)λ(n+ℓ), with power saving uniform in ℓ ≤ T^{O(θ)}. The diagonal is a
  quadratic form in b built from the Rankin–Selberg series Σλ(n)²n^{−s} ~ ζ(s)L(Sym²Δ,s)/ζ(2s).
  Its boundedness for Selberg's b uses Rankin–Selberg asymptotics and Σ_p λ(p)²/p.
* (SK) comes from three steps:
  1. Expand Z via the approximate functional equation, Z(u) = 2Re(e^{iθ(u)} Σ_{n≤√(u/2π)·c} λ(n)n^{−1/2−iu}) + small.
  2. Integrate over [t, t+h] by stationary phase / the first-derivative test. This gives a
     Dirichlet polynomial in t with weights ≈ min(h, 1/|log(nν₁/ν₂)|).
  3. Apply the mean-value theorem for Dirichlet polynomials, and then Selberg's arithmetic lemma.
     The weights (1 − log ν/log y) make the resulting sum Σ_n|Σ_{ν₁ν₂…}|² save (h log y)^{−1/2}.
     For Δ this lemma needs the Rankin–Selberg PNT Σ_{p≤x} λ(p)² log p ~ x and bounds for α(n).

(SK) is the hard core, as it is for ζ (Titchmarsh §10.9–10.22). Hafner's papers carry it over
to holomorphic cusp forms (Math. Ann. 264, 1983) and to Maass forms (Crelle 377, 1987).

## 2. What is formalized (level 1 = axiom-clean)

`namespace RamanujanTau.HafnerProportion`

```lean
-- Abstract Selberg method (Abstract.lean)
theorem selberg_zeros {Z w : ℝ → ℝ} (hZ : Continuous Z) (hw : Continuous w) (hw0 : ∀ t, 0 ≤ w t)
    {T h a B : ℝ} (hT : 0 < T) (hh : 0 < h) (ha : 0 < a) (hB : 0 < B)
    (H1 : a * T * h ≤ ∫ t in Icc T (2 * T), selJ Z w h t)
    (H2 : ∫ t in Icc T (2 * T), selJ Z w h t ^ 2 ≤ B * T * h ^ 2)
    (H3 : ∫ t in Icc T (2 * T), selI Z w h t ^ 2 ≤ a ^ 2 / 16 * T * h ^ 2) :
    ∃ F : Finset ℝ, (∀ γ ∈ F, γ ∈ Icc T (2 * T + h) ∧ Z γ = 0) ∧
      5 * a ^ 2 / (16 * B) * T / h ≤ F.card

-- Mollified first moment (FirstMoment.lean), unconditional
theorem mollified_first_moment {β η : ℝ} (hβ : 0 ≤ β) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ (b : ℕ → ℂ) (y : ℕ), 1 ≤ y → b 1 = 1 →
      (∀ n : ℕ, ‖b n‖ ≤ β * (n : ℝ) ^ η) → (y : ℝ) ^ (2 + 2 * η) ≤ T ^ (1 / 4 : ℝ) →
      ∀ a c : ℝ, 0 ≤ a → a ≤ c → c ≤ 3 * T →
        (c - a) / 2 - T / 8 ≤ ∫ u in a..c, |ZH u| * wM b y u

-- Selberg's (H1) for Δ, unconditional (Selberg.lean)
theorem selberg_H1 ... : ... ∀ h, 0 < h → h ≤ T / 8 →
    1 / 4 * T * h ≤ ∫ t in Icc T (2 * T), selJ ZH (wM b y) h t

-- (H2) from the mollified second moment
theorem selberg_H2 (hT : 0 < T) (hh : 0 < h) (hhT : h ≤ T)
    (hMV : (∫ u in T..(3 * T), ‖tauL (6 + u * I) * Mc b y (6 + u * I) ^ 2‖ ^ 2) ≤ B * T) :
    ∫ t in Icc T (2 * T), selJ ZH (wM b y) h t ^ 2 ≤ B * T * h ^ 2
```

Supporting lemmas:

* `Reduce.double_lower` and `double_upper` are Fubini-free bounds via an antiderivative:
  h∫_{T+h}^{2T}G ≤ ∫_T^{2T}∫_t^{t+h}G ≤ h∫_T^{2T+h}G.
* `sq_integral_le` is Cauchy–Schwarz on a short interval, proved by AM–GM.
* `norm_tauL_sub_one_le_all`: \|L(7+k+iv)−1\| ≤ 2^{−k}S for all k.
* `norm_Mc_sub_one_le`: \|M(9+k₀+iv)−1\| ≤ β2^{−k₀}, uniformly in y.
* `norm_Mc_le`: \|M(s)\| ≤ βy^{1+η} for Re s ≥ 6.

## 3. Level 2 (conditional on the named hypothesis `SelbergHyp`)

```lean
def SelbergHyp : Prop :=
  ∃ β η B D : ℝ, 0 ≤ β ∧ 0 ≤ η ∧ η ≤ 1 ∧ 0 < B ∧ 0 ≤ D ∧
    ∀ K : ℝ, 1 ≤ K → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∃ (b : ℕ → ℂ) (y : ℕ), 1 ≤ y ∧ b 1 = 1 ∧ (∀ n : ℕ, ‖b n‖ ≤ β * (n : ℝ) ^ η) ∧
        (y : ℝ) ^ (2 + 2 * η) ≤ T ^ (1 / 4 : ℝ) ∧
        (∫ u in T..(3 * T), ‖tauL (6 + u * I) * Mc b y (6 + u * I) ^ 2‖ ^ 2) ≤ B * T ∧   -- (MV2)
        (∫ t in Icc T (2 * T), selI ZH (wM b y) (K / Real.log T) t ^ 2) ≤
          D / Real.sqrt K * T * (K / Real.log T) ^ 2                                    -- (SK)

theorem tauL_critical_zeros_T_log_T_of_selberg (H : SelbergHyp) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ γ ∈ S, T ≤ γ ∧ γ ≤ 3 * T ∧ tauL (6 + γ * I) = 0) ∧ c * T * Real.log T ≤ S.card

theorem tauL_positive_proportion_of_selberg (H : SelbergHyp) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ γ ∈ S, 0 < γ ∧ γ ≤ 3 * T ∧ tauL (6 + γ * I) = 0) ∧
        c * (zeroCount (3 * T) : ℝ) ≤ S.card      -- zeroCount = N(T) with multiplicity (RvM)
```

**Is the hypothesis trivially satisfiable?** No.

* The trivial mollifier b = δ₁ satisfies all the size conditions.
* But then (MV2) reads ∫_T^{3T}\|L\|² ≤ BT. That is false: the integral is ≍ T log T by
  `CriticalMeanSquareLower`.
* (SK) is not expected to hold for it either. Without a mollifier, the Hardy–Littlewood
  heuristic gives ∫I² of size about Th²·(h log T)·(log T)^{O(1)}.

So the hypothesis really asks for mollification.

**Uniformity.** The constants β, η, B, D must be independent of K and T. The mollifier may
depend on (K, T), which only weakens the hypothesis. Selberg's mollifier depends on T alone.

**Range.** The size window y^{2+2η} ≤ T^{1/4} gives θ ≤ 1/8. Selberg's method works for any
fixed θ > 0, so this costs nothing except the value of the constant c.

## 4. What the repo has and what is missing

**Have:**

* Hardy's Z (`HardyZeros`).
* N₀(T) ≫ T (`HardyCountHafner`).
* Riemann–von Mangoldt (`ZeroCountRvM`).
* The critical mean square ~ cT log T (`CriticalMeanSquareAsymp`, Good).
* Uniform mean squares off the line (`HardyCountHafner.mean_square_uniform`, `CramerMeanSquare`).
* A Dirichlet-polynomial mean-value theorem (`MeanSquare.mv_poly`, error 6H(N)Σn\|b_n\|²).
* Shifted convolution bounds `ShiftedConvolutionBound (1/21) (1/21)` (`SCSSharp2`).
* Rankin–Selberg with error O(x^{3/5}) (`RankinError`), and the RS prime number theorem
  Σλ(p)²log p ~ x (`TauPNTUncond.rs_prime_PNT`).
* Stirling and digamma asymptotics (`Stirling`, `ZeroCountRvM.DigammaAsymp`).
* Additive-twist functional equations (`Subconvexity`).
* Now also: the Selberg reduction, (H1), and (H2) ⇐ (MV2) (this module).

**Missing**, with rough line estimates:

1. **Approximate functional equation** for L(Δ,6+it), uniform in t, with a smooth cutoff and the
   exact Γ-ratio phase e^{iθ(t)}. About 1.2–2k lines (Stirling is available).
2. **Twisted second moment ⇒ (MV2)** for θ small. Expand \|LM²\|² = \|L\|²\|M²\|², and use
   ∫\|L(6+it)\|²(m/n)^{it}w(t/T)dt = diagonal + off-diagonal. The off-diagonal is the shifted sum
   Σλ(a)λ(b), am − bn = ℓ. That needs SCS with **two-sided coefficients** (am − bn, not n, n+ℓ),
   which is more than the repo's `ShiftedConvolutionBound`. It is classical, via Kloosterman or
   spectral methods; the repo's Bruhat/Weil Poincaré-series route in `SCSProof` generalizes with
   level-type twists. Then the diagonal quadratic form has to be bounded for Selberg's b.
   About 3–5k lines. This is the main obstacle after (SK).
3. **Selberg's arithmetic lemmas for Δ**: the coefficients α(n) of L^{−1/2}, the bound
   \|α(n)\| ≤ d(n) (needs `DeligneBound`, so level 2), and the sums Σ_{ν≤y} α(ν)²/ν ≍ (log y)^{1/4}-type
   via the RS PNT. About 1.5–2.5k lines. Without Deligne, Rankin averages might suffice; that is
   not checked.
4. **Selberg's key lemma (SK)**: AFE plus stationary phase for ∫_t^{t+h}e^{iθ(u)}(nν₁/ν₂)^{−iu}du,
   then the mean-value theorem for the resulting Dirichlet polynomial, then the lemmas in item 3.
   About 3–4k lines.
5. Plancherel alternative, unexplored. The repo's N₀ ≫ T used the Hecke–Hafner Fourier identity
   ∫Λ(σ+it)e^{−itw} = 2πe^{σw}Δ(ie^w) rather than an AFE. A mollified version would need
   ∫Λ(6+it)M(6+it)²·… to be expressed through Δ twisted by additive characters. The repo's
   `twLambda_functional_equation` is the starting point. This might shorten items 1 and 4, but
   that is not checked.

The total remaining work is roughly 9–13k lines. It cannot be finished in one pass.

**Realistic milestone sequence:**

1. **Done.** Reduction, (H1), (H2) ⇐ (MV2), proportion against RvM. About 1.1k lines, level 1
   and level 2.
2. Discharge (MV2) at level 2 from a named two-sided shifted-convolution hypothesis
   `SCS2 η B : Σ_{am−bn=ℓ} λ(a)λ(b)… ≪ …`. This needs the AFE (item 1) and
   `mv_poly`-type bookkeeping.
3. Selberg's arithmetic lemma (item 3), under `[DeligneBound]`.
4. (SK) (item 4). After this the theorem holds at level 2, under `[DeligneBound]` + `SCS2`.
5. Prove `SCS2` (a generalization of `SCSProof`) and remove Deligne, if possible.

## 5. Literature

- A. Selberg, *On the zeros of Riemann's zeta-function*, Skr. Norske Vid. Akad. Oslo (1942).
- E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §§10.9–10.22.
- J. L. Hafner, *Zeros on the critical line for Dirichlet series attached to certain cusp forms*,
  Math. Ann. 264 (1983) 21–37. This paper is attributed in `HARDY_COUNT_HAFNER.md` for
  N₀(T) ≫ T. Its main theorem is the positive proportion for holomorphic cusp forms.
- J. L. Hafner, *Zeros on the critical line for Maass wave form L-functions*, J. reine angew.
  Math. 377 (1987) 127–158.
- A. Good, *The square mean of Dirichlet series associated with cusp forms*, Mathematika 29 (1982).
