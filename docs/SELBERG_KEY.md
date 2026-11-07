# Selberg's key lemma (SK) for L(Δ,s) (2026-11-06)

Lean: `RamanujanTau/SelbergKey/` (6 files, about 1.07k lines; entry point `Main.lean`).

    nice -n 10 lake build RamanujanTau.SelbergKey.Main      # exit 0

* All 20 `#print axioms` in `Main.lean` give `[propext, Classical.choice, Quot.sound]`.
* `grep` finds no `sorry`, `admit`, `native_decide` or `axiom` in `RamanujanTau/SelbergKey/`.
* No committed file was modified. The module is not imported from `RamanujanTau.lean`.

**Status.** (SK) is **not** proved. What is done:

* the analytic front end of (SK), exact and unconditional (level 1):
  * a shifted product AFE for Z(u)Z(u′) with no root-number cross terms;
  * the lag form of ∫I²;
  * the full expansion of F(u)F(u+v), F = Z·|M|², with its diagonal / off-diagonal split;
* the reduction (SK) ⇐ `SKSplitHyp θ`, and positive proportion ⇐ `QFHyp ∧ SKSplitHyp θ`
  (level 2);
* the purely arithmetic hypothesis `SKQFHyp θ`, stated in Lean in the style of
  `HafnerBridge/QF.lean` (statement only).

The step `SKSplitHyp ⇐ SKQFHyp` (off-diagonal by shifted convolution sums, plus the Mellin
evaluation of the diagonal) is paper level (§3, §6).

Evidence levels: (1) Lean, axiom-clean; (2) Lean, conditional on named hypotheses; (3) paper;
(4) numerics.

## 1. Selberg / Hafner (from memory, NOT checked against the sources)

**Selberg for ζ (Titchmarsh §§10.9–10.22).**

* The mollifier is φ(s) = Σ_{ν<X} β_ν ν^{−s}, with β_ν = α_ν(1 − log ν/log X), where the α_ν are
  the coefficients of ζ^{−1/2}. Take X = T^θ and h = K/log T. Define

      I(t) = ∫_t^{t+h} Z(u)|φ(½+iu)|² du,     J(t) = ∫_t^{t+h} |Z(u)||φ|² du.

* The key lemma is ∫_T^{2T} I² ≪ T h²(h log X)^{−1/2}, i.e. ≪ T h²/√K for θ fixed.
* As I recall it, Titchmarsh's proof does **not** use the AFE. It goes through Hardy's Fourier
  route: Ξ(t), the theta function ψ(x) = Σe^{−n²πx}, and Parseval near the boundary of the
  strip of convergence. After Parseval one gets four-fold sums over ν₁…ν₄, with the theta
  transformation handling the off-diagonal.
* The arithmetic heart is a lemma on Σ β_{ν₁}β_{ν₂}β_{ν₃}β_{ν₄}/[ν₁ν₃, ν₂ν₄]·(twist)
  (Titchmarsh §10.20–10.22). The smoothing (1 − log ν/log X) produces the saving (h log X)^{−1/2}.
* I do not trust my memory of the exact shape of those sums; treat this as orientation only.

**Hafner for cusp forms (Math. Ann. 264, 1983).**

* Hafner transfers this to holomorphic cusp forms of level 1. In place of theta he uses
  modularity of f, through the Fourier identity ∫Λ(σ+it)e^{−itw}dt = 2πe^{σw}f(ie^w), with Δ
  near rational cusps ν₁/ν₂.
* His mollifier is built from L(f,s)^{−1/2}, and his arithmetic lemma uses the Rankin–Selberg
  prime number theorem.
* Also unchecked. In particular I do not remember whether Hafner needs Deligne. For Δ, Deligne
  is a theorem, so this does not matter for the truth of (SK). It matters only for what the repo
  must assume, which is `[DeligneBound]` at level 2.

**The route taken here** fits the repo's tools better: the exact |L|²-type AFE (`HeckeAFE3`),
the twisted second moment (`TwistedMoment`), `SCS2Coprime`, and the QF bridge (`HafnerBridge2`).
It is the "lag" version of the twisted-moment method:

1. ∫_{[T,2T]} I² ≤ ∫ φ(t)I(t)² for any φ ≥ 1_{[T,2T]}. This equals
   ∫_0^h∫_0^h∫φ(t)F(t+x)F(t+x′). So (SK) is the (h−|v|)-weighted average over lags |v| ≤ h of
   the lag correlations ∫F(u)F(u+v).
2. Z(u)Z(u′) is expanded **exactly** by a shifted product AFE. This has no root-number cross
   terms, and so no stationary phase.
3. Expand |M|² at u and u+v (four mollifier variables a, b, c, d) and split into diagonal and
   off-diagonal.
   * The off-diagonal consists of two-sided shifted convolution sums Σ_{acm − bdn = ℓ} λ(m)λ(n).
     These are expected to give power saving (`SCS2Coprime.scs2_general`), as in `TwistedMoment`.
   * The diagonal acm = bdn is a Mellin integral of D_{P₁,Q₁}(1 − iv + 2z) = R·ρ·ρ.
4. The residues at z = 0 and z = iv/2 give an explicit arithmetic function 𝒜(v, L) of the lag v.
   (SK) becomes Selberg's arithmetic lemma ∫_{−h}^{h}(h−|v|) Re 𝒜(v, L) dv ≪ h²/√K.

## 2. What is formalized (level 1)

`namespace RamanujanTau.SelbergKey`

### ShiftAFE.lean: Z(u)Z(u′) with no ε cross terms

The function P(z) = Λ(a+z)Λ(b+z) satisfies P(−z) = Λ(12−a+z)Λ(12−b+z) by Hecke's equation.
The residue machinery of `HeckeAFE` then gives:

```lean
-- ISh a b c = (2π)⁻¹ vline (Λ(a+z)Λ(b+z)e^{z²}/z) c
theorem heckeLambda_mul_afe (a b : ℂ) {c : ℝ} (hc : 0 < c) :
    heckeLambda a * heckeLambda b = ISh a b c + ISh (12 - a) (12 - b) c
theorem ISh_conj (a b : ℂ) (c : ℝ) : ISh (conj a) (conj b) c = conj (ISh a b c)
theorem ISh_eq_tsum {a b : ℂ} {c : ℝ} (hc : 0 < c) (hs1 : 7 < a.re + c) (hs2 : 7 < b.re + c) :
    ISh a b c = ∑' p : ℕ × ℕ, tauC p.1 * tauC p.2 * ((2 * π * p.1 : ℝ) : ℂ) ^ (-a) *
      ((2 * π * p.2 : ℝ) : ℂ) ^ (-b) * W2sh a b (4 * π ^ 2 * p.1 * p.2) c
theorem norm_Ush (u u' : ℝ) : ‖Ush u u'‖ = 1
theorem ZH_mul_ZH_afe (u u' : ℝ) :
    ZH u * ZH u' = 2 * (Ush u u' * ∑' p : ℕ × ℕ,
      tauC p.1 * tauC p.2 * (p.1 : ℂ) ^ (-(6 + u * I)) * (p.2 : ℂ) ^ (-(6 - u' * I)) *
        Wsh u u' (4 * π ^ 2 * p.1 * p.2)).re
```

The notation in `ZH_mul_ZH_afe`:

* U(u,u′) = (2π)^{i(u′−u)}Γ(6+iu)Γ(6−iu′)/(|Γ(6+iu)||Γ(6+iu′)|) = e^{i(ϑ(u)−ϑ(u′))}, where
  ϑ(u) = arg Γ(6+iu) − u log 2π.
* W̃_{u,u′}(ξ) = W(6+iu, 6−iu′; ξ)/(Γ(6+iu)Γ(6−iu′)), with
  W(a,b;ξ) = (1/2πi)∫_{(c)}Γ(a+z)Γ(b+z)ξ^{−z}e^{z²}dz/z.

In normalized form:

    Z(u)Z(u′) = 2Re[e^{i(ϑ(u)−ϑ(u′))} Σ λ(m)λ(n)(mn)^{−1/2} m^{−iu} n^{iu′} W̃_{u,u′}(4π²mn)].

For u = u′ this is `HeckeAFE3.tauL_normSq_afe`. The proof uses Λ(6−iu′) = Λ(6+iu′) and the
reality of Λ on the line (`HardyZeros.Zc_eq_Zr`).

### Lag.lean: the lag form

```lean
theorem weighted_shortInt_sq (hF : Continuous F) (hφ : Continuous φ) (hAB : A ≤ B) (hh : 0 ≤ h) :
    ∫ t in A..B, φ t * (∫ u in t..t + h, F u) ^ 2 =
      ∫ x in 0..h, ∫ x' in 0..h, ∫ t in A..B, φ t * (F (t + x) * F (t + x'))
theorem sk_le_weighted ... :   -- φ ≥ 0, φ ≥ 1 on [T,2T] ⊆ [A,B]
    ∫ t in Icc T (2 * T), (∫ u in t..t + h, F u) ^ 2 ≤ ∫ t in A..B, φ t * (∫ u in t..t + h, F u) ^ 2
theorem sk_le_lag ... :         -- the combination, with u = t + x and lag v = x' − x
    ... ≤ ∫ x in 0..h, ∫ x' in 0..h, ∫ u in (A + x)..(B + x), φ (u - x) * (F u * F (u + (x' - x)))
```

Fubini is applied to continuous functions on boxes (`intervalIntegral_swap`).

### Expand.lean: F(u)F(u+v) expanded, and the split

The expansion of |M|² is

    |M(6+iu)|² = Σ_{a,b≤y} wc(a,b)(b/a)^{iu},     wc(a,b) = β(a)β(b)(ab)^{−1/2}      (`wM_expand`).

```lean
theorem lag_product (β : ℕ → ℝ) (y : ℕ) (u u' : ℝ) :
    Fsel β y u * Fsel β y u' = 2 * (Ush u u' * quadSum β y u u' (fun _ _ _ _ => Sl u u')).re
theorem summable_sTerm (u u' : ℝ) : Summable (sTerm u u')     -- the lag series converges absolutely
theorem Sl_sub_diagS (a b c d) (u u') :
    Sl u u' - diagS a b c d u u' = ∑' p, if isDiag a b c d p then 0 else sTerm u u' p
theorem lag_split (β y u v) : OffLag β y u v =
    2 * (Ush u (u + v) * quadSum β y u (u + v) (fun a b c d => Sl u (u + v) - diagS a b c d u (u + v))).re
```

Definitions:

* `Fsel β y = ZH · wM β y`.
* `quadSum` is Σ_{a,b,c,d∈[1,y]} wc(a,b)wc(c,d)(b/a)^{iu}(d/c)^{iu′}·G(a,b,c,d).
* `isDiag a b c d (m,n) :⇔ n·b·d = m·a·c`. This says the u-frequency log(bdn/acm) vanishes.
* `DiagLag β y u v` is the diagonal part.
* `OffLag = F(u)F(u+v) − DiagLag`. By `lag_split` and `Sl_sub_diagS` it is exactly the sub-sum of
  absolutely convergent terms with bdn ≠ acm.

## 3. The diagonal, evaluated (level 3, paper)

**Indexing.** Put P = ac and Q = bd. The diagonal condition is mP = nQ. Write g = (P,Q),
P₁ = P/g, Q₁ = Q/g. Then m = Q₁r and n = P₁r.

**Coefficient.** The coefficient is β⁴/(r[P,Q]); the identity used is √(P₁Q₁PQ) = [P,Q]. The
lag phase is (P₁ d/c)^{iv} r^{iv}. Therefore

    DiagLag(u,v) = 2Re[U(u,u+v) Σ_{abcd} κ (P₁d/c)^{iv} Σ_r λ(Q₁r)λ(P₁r) r^{−1+iv} W̃_{u,u+v}(4π²P₁Q₁r²)],
    κ = β(a)β(b)β(c)β(d)/[P,Q].

**Mellin form of the r-sum.** Insert the Mellin form of W̃ (line Re z = 2). The r-sum becomes

    (1/2πi)∫ G_{u,u+v}(z)(4π²P₁Q₁)^{−z} D_{P₁,Q₁}(1 − iv + 2z) e^{z²}dz/z.

Here G_{u,u′}(z) = Γ(6+iu+z)Γ(6−iu′+z)/(Γ(6+iu)Γ(6−iu′)), and

    D_{P₁,Q₁}(s) = Σ_r λ(P₁r)λ(Q₁r)r^{−s} = R(s)ρ(P₁,s)ρ(Q₁,s)

for coprime P₁, Q₁ (Hecke multiplicativity; at s = 1 this is `HafnerBridge2.Twisted`).

**Contour shift.** Shift to Re z = −1/6. The continuation of R(s) = ζ(s)L(Sym²Δ,s)/ζ(2s) to
Re s ≥ 2/3 has polynomial growth (`SelbergDelange.norm_KK_le`). The shifted integral is
≪ T^{−1/3}y^{O(1)}, which is power saving. There are two residues:

* **z = 0:** D_{P₁,Q₁}(1−iv). With U = e^{i(ϑ(u)−ϑ(u+v))} = (u/2π)^{−iv}(1 + O(h/T)), it
  contributes (u/2π)^{−iv}R(1−iv)ρ(P₁,1−iv)ρ(Q₁,1−iv).
* **z = iv/2** (the pole of R): G(iv/2)(4π²P₁Q₁)^{−iv/2}e^{−v²/4}r₀ρ(P₁)ρ(Q₁)/(iv).
  * The identity U·G(iv/2) = (2π)^{iv}|Γ(6+i(u+v/2))|²/(|Γ(6+iu)||Γ(6+i(u+v))|) =
    (2π)^{iv}(1 + O(v²/T²)) holds by log-convexity and Stirling.
  * The factor (2π)^{iv} cancels (4π²)^{−iv/2}. So this term has **no u-oscillation**.

**Laurent step.** Replace R(1−iv) by its Laurent polynomial −r₀/(iv) + γ_R. With L = log(u/2π)
this gives

    DiagLag(u,v) ≈ 2 Re 𝒜(v, L),
    𝒜(v,L) = (r₀/(iv))(e^{−v²/4}𝒮⁰(v) − e^{−ivL}𝒮(v)) + γ_R e^{−ivL}𝒮(v),
    𝒮(v)  = Σ_{abcd} κ (P₁d/c)^{iv} ρ(P₁,1−iv)ρ(Q₁,1−iv),
    𝒮⁰(v) = Σ_{abcd} κ (P₁d/c)^{iv} (P₁Q₁)^{−iv/2} ρ(P₁)ρ(Q₁).

The remainder in the Laurent step is O(|v|·|𝒮(v)|).

**Checks.**

* At v = 0, 𝒮⁰(0) = 𝒮(0) = Q⁰(y) of `QFHyp`, because Σ_{ac=P}β(a)β(c) = c(P). So 𝒜 is regular
  at v = 0.
* For y = 1 (no mollifier), Re 𝒜 = r₀ sin(vL)/v + γ_R cos(vL). Hence
  ⟨Z(u)Z(u+v)⟩ ≈ 2r₀ sin(vL)/v. At v = 0 this is the mean square 2r₀ log(u/2π) = `cDelta`·log,
  consistent with `CriticalMeanSquareAsymp`.
* Also for y = 1, ∫(h−|v|)·2Re𝒜 ≈ 2πr₀h ≫ h²/√K. So (SK) fails without a mollifier, as expected.

**Why 1/√K.** 𝒮 and 𝒮⁰ vary on the scale 1/log y = h/(Kθ) in v. Heuristically they behave
like the generating function of the mollified L·M², with a branch point coming from R^{−1/2}.
This suggests 𝒮⁰(v)/(iv) ≈ (log y)^{−1}φ(v log y) with φ(x) ~ |x|^{−1/2}. Then

    ∫_{|v|≤h}(h−|v|)𝒮⁰/(iv) ≈ h·(log y)^{−1}·(Kθ)^{1/2} = h²/√(Kθ).

This is Selberg's saving. The e^{−ivL} terms oscillate K times on [−h, h] and contribute less.
Turning this heuristic into a proof is a Selberg–Delange statement with κ = −1/2, uniform in the
twist v. It is the same input as `QFHyp` (`SELBERG_DELANGE.md` §§3–4), deformed by v.

## 4. The hypotheses (Lean)

### `SKSplitHyp θ` (Reduce.lean): the interface, level 2

```lean
def SKSplitHyp (θ : ℝ) : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ ∀ K : ℝ, 1 ≤ K → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    ∃ (φ : ℝ → ℝ) (A B : ℝ), Admissible T A B φ ∧
      Continuous (Function.uncurry (DiagLag (HafnerMV2.βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊)) ∧
      lagInt (DiagLag (βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊) φ A B (K / log T) ≤ D / √K * T * (K / log T) ^ 2 ∧
      lagInt (OffLag (βSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊) φ A B (K / log T) ≤ 1 / √K * T * (K / log T) ^ 2
-- lagInt G φ A B h = ∫_0^h ∫_0^h ∫_A^B φ(t) G(t+x, x'−x)
-- Admissible T A B φ = φ continuous, φ ≥ 0, φ ≥ 1 on [T,2T], A ≤ T, 2T ≤ B

theorem sk_of_split {θ : ℝ} (H : SKSplitHyp θ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ K : ℝ, 1 ≤ K → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (∫ t in Set.Icc T (2 * T), selI ZH (wM (SelbergCoeffs.bSel ⌊T ^ θ⌋₊) ⌊T ^ θ⌋₊) (K / log T) t ^ 2) ≤
        D / √K * T * (K / log T) ^ 2                      -- exactly the (SK) conjunct of SelbergMollHyp
theorem selbergMollHyp_of_QF_split (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 81600)
    (hQ : HafnerBridge.QFHyp) (hS : SKSplitHyp θ) : SelbergCoeffs.SelbergMollHyp
theorem tauL_positive_proportion_of_QF_split (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 81600)
    (hQ : QFHyp) (hS : SKSplitHyp θ) :
    ∃ c T₀ : ℝ, 0 < c ∧ ∀ T, T₀ ≤ T → ∃ S : Finset ℝ,
      (∀ γ ∈ S, 0 < γ ∧ γ ≤ 3 * T ∧ tauL (6 + γ * I) = 0) ∧ c * (zeroCount (3 * T) : ℝ) ≤ S.card
```

**What `SKSplitHyp` asks for.**

* The two integral clauses are, respectively, the diagonal and the off-diagonal part of an
  *exact*, absolutely convergent expansion.
* The window φ is existentially quantified. A smooth φ is needed, because a sharp window leaves
  O(T)-size boundary off-diagonals of Hilbert-inequality type.
* The continuity clause is a regularity side condition: it is true, but not proved here.
* The off-diagonal clause is generous: 1/√K, where power saving T^{−δ} is expected.
* It mentions no zeros.

**Not trivially satisfiable.** For y = 1 the diagonal clause fails, by the computation in §3.
Here y = ⌊T^θ⌋ is forced to be Selberg's mollifier.

### `SKQFHyp θ` (Arith.lean): purely arithmetic, statement only

```lean
-- DpC p s = Σ_j λ(p^j)² p^{−js},  NpC p a s = Σ_j λ(p^{j+a})λ(p^j)p^{−js},
-- rhoC m s = Π_{p^a∥m} NpC/DpC;  P1 = ac/(ac,bd), Q1 = bd/(ac,bd);
-- kap y a b c d = βSel(a)βSel(b)βSel(c)βSel(d)/lcm(ac,bd);  ev = (P₁ d/c)^{iv}
-- Sv y v  = Σ_{[1,y]⁴} kap·ev·rhoC(P₁,1−iv)·rhoC(Q₁,1−iv)
-- S0v y v = Σ_{[1,y]⁴} kap·ev·(P₁Q₁)^{−iv/2}·rho(P₁)·rho(Q₁)
-- Av y v L = r0/(iv)·(e^{−v²/4}·S0v − e^{−ivL}·Sv) + gammaD·e^{−ivL}·Sv
def SKQFHyp (θ : ℝ) : Prop :=
  ∃ B D : ℝ, 0 ≤ D ∧ ∀ K : ℝ, 1 ≤ K → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (∀ v ∈ Icc (-(K / log T)) (K / log T), ‖Sv ⌊T ^ θ⌋₊ v‖ ≤ B) ∧
    ∀ L ∈ Icc (log (T / (4 * π))) (log T),
      |∫ v in (-(K / log T))..(K / log T), (K / log T - |v|) * (Av ⌊T ^ θ⌋₊ v L).re| ≤
        D / √K * (K / log T) ^ 2
```

* Clause (i), \|𝒮\| ≤ B, controls the Laurent remainder O(v)·𝒮. It gives T h³B ≪ T h²/√K.
* Clause (ii) is Selberg's lemma proper.
* (SK) ⇐ `SKQFHyp` is at level 3 (§3 and §6, M3–M4).
* The truth of `SKQFHyp` for Selberg's mollifier is level 3: it is expected from Hafner (1983)
  and the heuristic above. Not checked numerically.

**Possible pitfalls.**

* The window φ(u−x) depends on x, not only on v = x′−x. Replacing φ(u−x) by φ(u) costs
  O(h·∫|φ′|·∫|𝒜|dv) = O(h·log T·(log y)^{O(1)}), against a main term of size T h²/√K.
  This is harmless.
* The phase replacements U ≈ (u/2π)^{−iv} and U·G(iv/2) ≈ (2π)^{iv} cost relative O(h/T).
* So the pointwise-in-L, (h−|v|)-kernel form of (ii) is what the analytic reduction needs. A
  formal proof may still prefer a kernel κ(u,v) variant.

## 5. Files

| file | lines | content |
|---|---|---|
| `ShiftAFE.lean` | 395 | `ISh`, `W2sh`, `heckeLambda_mul_afe`, `ISh_conj`, `ISh_eq_tsum`, `Ush`, `Wsh`, `norm_Ush`, `ZH_mul_ZH_afe` |
| `Lag.lean` | 119 | `intervalIntegral_swap`, `shortInt_sq`, `weighted_shortInt_sq`, `inner_lag`, `sk_le_weighted`, `sk_le_lag` |
| `Expand.lean` | 246 | `wc`, `eph`, `wM_expand`, `sTerm`, `Sl`, `isDiag`, `diagS`, `Fsel`, `quadSum`, `lag_product`, `DiagLag`, `OffLag`, `lag_split`, `norm_W2sh_le`, `summable_sTerm`, `Sl_sub_diagS` |
| `Reduce.lean` | 165 | `Admissible`, `lagInt`, `lagInt_add`, `weighted_eq_lagInt`, `SKSplitHyp`, `sk_of_split`, `selbergMollHyp_of_QF_split`, `tauL_positive_proportion_of_QF_split` |
| `Arith.lean` | 108 | `DpC`, `NpC`, `rhoC`, `P1`, `Q1`, `kap`, `ev`, `sum4`, `Sv`, `S0v`, `Av`, `SKQFHyp`, `kap_one_one` |
| `Main.lean` | 32 | imports, 20 `#print axioms` |

## 6. Milestone plan (what remains)

| # | milestone | content | estimate |
|---|---|---|---|
| M0 | **done** | shifted AFE, lag form, expansion and split, (SK) ⇐ `SKSplitHyp`, `SKQFHyp` stated | 1.07k |
| M1 | weight bounds | W̃_{u,u+v}(ξ) ≪ (1+ξ/u²)^{−A}, W̃ − 1 ≪ (ξ/u²)^c, ∂_u^j W̃ ≪ u^{−j}(…), uniform in \|v\| ≤ 1. Copy `HeckeAFE3` (`norm_Rd_le` at u and −(u+v), product Leibniz). Plus joint continuity of `DiagLag` (the regularity clause) | 0.4–0.6k |
| M2 | off-diagonal clause | Integrate by parts in u (smooth φ) to kill \|log(bdn/acm)\| ≥ T^{−1+ε}. The rest is the two-sided sums Σ_{acm−bdn=ℓ}λλ, via `SCS2Coprime.scs2_general` + partial summation. Alternatively re-run `TwistedMoment`'s generic Good machinery with the lag weight. Expected O(T^{1−δ}y^{C}h²) | 1.5–3k |
| M3 | diagonal Mellin evaluation | Shift W̃ to Re z = −1/6. Needs: D_{P₁Q₁}(s) = R(s)ρ(P₁,s)ρ(Q₁,s) for **complex** s (the complex version of the `HafnerBridge2` peeling, ~0.5k); R on Re s ≥ 2/3 with polynomial growth (`SelbergDelange.norm_KK_le`); the residue at z = iv/2; the phase lemmas U ≈ (u/2π)^{−iv} and U·G(iv/2) ≈ (2π)^{iv} (digamma bounds, `HeckeAFE2.Psi`) | 1.5–2k |
| M4 | `SKSplitHyp ⇐ SKQFHyp` | Laurent remainder R(1−iv) + r₀/(iv) − γ_R = O(v) (from the `KK` expansion at 1); u-integration; φ(u−x) → φ(u) | 0.6–0.9k |
| M5 | `SKQFHyp` itself | Selberg–Delange κ = −1/2 for the four-variable form, uniform in the twist v ∈ [−h,h], plus Selberg's (1 − log/log y) bookkeeping. Shares all inputs with `QFHyp` (QFProof agent / `SelbergDelange2.logmean_LSD`, `rs_prime_PNT_error`), level 2 on `[DeligneBound]` | 3–5k |

Total remaining: about 7–11k lines. After M1–M4 the theorem would be at level 2 on
`QFHyp ∧ SKQFHyp θ`, with all analytic parts unconditional. This mirrors how (MV2) was
reduced to `QFHyp`.

## 7. Gaps and caveats

* §1 is from memory, and neither Titchmarsh nor Hafner was checked. The route of §§2–3 is
  self-contained and does not rely on them.
* The diagonal formula of §3 was derived by hand. The y = 1 specialization matches the repo's
  mean square (`cDelta = 2r₀`), but the four-variable form has not been tested numerically.
  * A PARI test of `SKQFHyp`(ii) at moderate y would be the cheapest check. It needs α(n), the
    local factors ρ_p(a, 1−iv), r₀ and γ_R; all of these are in `scripts/hafner_bridge/`.
  * Not run this session.
* The `SKSplitHyp` continuity clause is mathematically true (uniform convergence of the
  r-series via `summable_sTerm`-type bounds, locally uniform in (u,v)) but not proved.
* θ ≤ 1/81600 is inherited from (MV2) (`mv2_of_QF`). (SK) itself should work for any small θ.

## 8. Literature

- A. Selberg, *On the zeros of Riemann's zeta-function*, Skr. Norske Vid. Akad. Oslo (1942).
- E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., §§10.9–10.22.
- J. L. Hafner, *Zeros on the critical line for Dirichlet series attached to certain cusp forms*,
  Math. Ann. 264 (1983) 21–37.
- J. L. Hafner, *Zeros on the critical line for Maass wave form L-functions*, J. reine angew.
  Math. 377 (1987).
- (Background for the twisted / shifted second moment:) R. Balasubramanian, J. B. Conrey,
  D. R. Heath-Brown, *Asymptotic mean square of the product of the Riemann zeta-function and a
  Dirichlet polynomial*, J. reine angew. Math. 357 (1985). Also V. Blomer, *Shifted convolution
  sums and subconvexity bounds for automorphic L-functions*, IMRN 2004.

---

## 2026-11-06 (later): `SKQFHyp` checked numerically; M1 (a)+(b) done (`SelbergKey2/`)

### 1. Numerical truth check of `SKQFHyp` (level 4): it checks out

Scripts are in `scripts/selberg_key/`, with outputs in `*.out`. All are single-threaded and
niced; PARI runs with `nbthreads = 1`.

| script | what it does |
|---|---|
| `taup.gp` | writes `taup.txt`, the values τ(p) for p ≤ 40000 |
| `sk.c` | computes 𝒮(v) and 𝒮⁰(v) exactly for Selberg's β = α(1 − log n/log y) on a v-grid, output `S_y<y>.txt` |
| `post.py` | clauses (i) and (ii) |
| `extrap.py` | y → ∞ extrapolation |
| `zgrid.gp` | the actual Hardy Z of Δ on [400, 803], step 0.01 |
| `corr.py`, `skdirect.py` | end-to-end checks against the actual Z |

**How `sk.c` reduces the work.** The phase (P₁d/c) equals ad/g, so
𝒮(v) = Σ_{P,Q≤y²} x_v(P)x_v(Q) g^{1−iv}/(PQ)·ρ(P₁,1−iv)ρ(Q₁,1−iv), where
x_v(P) = Σ_{ac=P}β(a)β(c)a^{iv}. The local factors ρ_p(k, 1−iv) are summed directly as series
with 90 terms.

**Cross-check.** At v = 0, `sk.c` reproduces `scripts/qf_proof/q.c` exactly: Q⁰ = 0.7002506533
(y = 10) and 0.5500071003 (y = 30). This is an independent code path.

**Clause (i).** max_{|v|≤h}|𝒮(v)| lies between 0.40 and 0.74 for every (y, θ, K) tested, and it
decreases with y. For example 𝒮(0) = Q⁰ = 0.398 at y = 200.

**Clause (ii).** The tests use y = 30, 60, 100, 200 and θ = 1/4, 1/10, 1/20, with
log T = log y/θ, h = K/log T, and L scanned over [log T − log 4π, log T] (41 values).

* At fixed (K, θ), max_L|I|/h² converges as y → ∞. Fitting I/h² = A + B/ℓ + C/ℓ² with ℓ = log y,
  the quadratic and linear fits agree to about 2%. This is consistent with the scaling argument:
  with v = w/ℓ, I/h² becomes a function of (K, θ) alone.
* The K-dependence of the limit A(K, θ) (`extrap.out`):

  | θ | K = 1 | 2 | 4 | 8 | 16 | 32 | 64 |
  |---|---|---|---|---|---|---|---|
  | 1/4  | 4.42 | 4.03 | 2.94 | 1.67 | 0.98 | – | – |
  | 1/10 | 9.98 | 9.17 | 6.80 | 3.72 | 2.10 | 1.19 | – |
  | 1/20 | 19.2 | 17.7 | 13.2 | 7.13 | 3.90 | 2.13 | 1.20 |

* So √K·A(K) is bounded: its maximum is about 5.9, 13.6 and 26 at K ≈ 4 for the three θ, i.e.
  D(θ) ≈ 1.4/θ. At large K, A(K) decays like (log K)/K: K·A grows only logarithmically. This is
  *faster* than the 1/√K that (ii) requires.
* **Verdict: (ii) holds with room to spare; it is neither false nor mis-normalized.**
* Without the mollifier (y = 1) the same quantity is πr₀/h + O(1), i.e. ≍ log T/K. That is 1.7
  times the mollified value at y = 30 and 2.4 times at y = 200, and the gap grows with T. The y = 1 case of (ii) fails, as it
  should.

**End-to-end check of the four-variable 𝒜 formula against the real Z(t)** (`corr.out`,
`skdirect.out`, T = 400).

* *Lag correlations.* Measured (1/T)∫_T^{2T}F(u)F(u+v)du, with F = Z·|M_y|², against
  2⟨Re𝒜(v, log(u/2π))⟩_u for y = 1, 3, 5, 10 and v ∈ [0, 2.8].
  * The agreement is within about 0.1–0.2 in absolute terms, against values up to 5.1. For example,
    at y = 10 and v = 0 the measured value is 3.725 and the prediction 3.780.
  * The y-dependence matches: at v = 0, y = 1 → 10 moves the measured value 5.12 → 3.73 and the
    prediction 5.08 → 3.78.
  * Ratios near the zeros of C(v) are naturally noisy.
* *The integrated Selberg quantity.* Measured (1/T)∫_T^{2T}I(t)² against the 𝒜-prediction, both
  divided by h², for y = 1…10 and K = 1, 2, 4, 8: the ratio lies in 0.96–1.05 in every case.
* This confirms, numerically, all of the following:
  * the lag AFE;
  * the diagonal Mellin evaluation of §3, including the z = iv/2 residue;
  * the Laurent data r₀ = 0.384084, γ_R = 0.796028;
  * the 2Re factor and the (h−|v|) kernel;
  * that the off-diagonal is small (a few percent already at T = 400).

**Caveat.** The asymptotic regime is reached only through extrapolation. ℓ = log y ≤ 5.3, and
Q⁰·log y = 2.11 at y = 200, whereas the QF agent reports about 2.45 at y = 5000. The fits are
stable, but a y = 1000 run of `sk.c` (about 1 h) would tighten them.

### 2. M1 in Lean (`RamanujanTau/SelbergKey2/`, level 1)

    nice -n 10 lake build RamanujanTau.SelbergKey2.Main      # exit 0

* All 14 `#print axioms` give `[propext, Classical.choice, Quot.sound]`.
* There is no `sorry`, `admit`, `native_decide` or `axiom`.
* 3 files, 579 lines. `SelbergKey/` is unchanged.

**M1(a) `Cont.lean`: the regularity clause is removed.**

```lean
theorem continuous_W2sh_line (hξ : 0 < ξ) : Continuous fun q : ℝ × ℝ => W2sh (6 + q.1 * I) (6 - q.2 * I) ξ 2
theorem continuous_sTerm (p : ℕ × ℕ) : Continuous fun q : ℝ × ℝ => sTerm q.1 q.2 p
theorem norm_sTerm_le (u u' : ℝ) (p : ℕ × ℕ) :
    ‖sTerm u u' p‖ ≤ (C0 / ‖Gamma (6 + u * I) * Gamma (6 - u' * I)‖ * (4 * π ^ 2) ^ (-(2:ℝ))) * (gt p.1 * gt p.2)
theorem continuous_diagS (a b c d : ℕ) : Continuous fun q : ℝ × ℝ => diagS a b c d q.1 q.2
theorem continuous_DiagLag (β : ℕ → ℝ) (y : ℕ) : Continuous (Function.uncurry (DiagLag β y))
def SKSplitHyp' (θ : ℝ) : Prop      -- SKSplitHyp without the continuity clause
theorem splitHyp_of_splitHyp' : SKSplitHyp' θ → SKSplitHyp θ
theorem tauL_positive_proportion_of_QF_split' (hθ0 : 0 < θ) (hθ : θ ≤ 1/81600)
    (hQ : QFHyp) (hS : SKSplitHyp' θ) : ∃ c T₀, 0 < c ∧ ∀ T ≥ T₀, ∃ S, (… critical zeros …) ∧ c * zeroCount (3T) ≤ S.card
```

The proofs:

* **Continuity of W.** Dominated convergence: the bound |Γ(w)| ≤ Γ(Re w) makes the integrand
  ≤ Γ(8)²ξ^{−2}e⁴/2·e^{−y²}, uniformly in (u, u′).
* **Continuity of the diagonal sum.** The Weierstrass M-test (`continuousOn_tsum`) on closed
  balls, using the minimum of |Γ(6+iu)Γ(6−iu′)| on the compact ball.

`SKSplitHyp'` now consists of the two integral clauses only (diagonal and off-diagonal).

**M1(b) `WBound.lean`: uniform bounds for the lag weight.** Here T(t) = ‖3/2 + it‖ ≍ 1+|t|.

```lean
theorem W2sh_shift   : W2sh a b ξ c₁ = W2sh a b ξ c₂          -- 0 < c₁ ≤ c₂, Re a + c₁, Re b + c₁ > 0
theorem W2sh_residue : W2sh a b ξ c - W2sh a b ξ (-c') = Gamma a * Gamma b   -- 0 < c' < Re a, Re b
theorem W2sh_line_bound (hx : -9/2 ≤ x) (hx0 : x ≠ 0) : ∃ K ≥ 0, ∀ u u' ξ > 0,
    ‖W2sh (6 + u*I) (6 - u'*I) ξ x‖ ≤ K * (Tq u * Tq u' / ξ) ^ x * (‖Γ(6+iu)‖ * ‖Γ(6+iu')‖)
theorem Wsh_decay  (hA : 0 < A) : ∃ C ≥ 0, ∀ u u' ξ > 0, ‖Wsh u u' ξ‖ ≤ C * (Tq u * Tq u' / ξ) ^ A
theorem Wsh_sub_one (0 < c ≤ 9/2) : ∃ C ≥ 0, ∀ u u' ξ > 0, ‖Wsh u u' ξ - 1‖ ≤ C * (ξ / (Tq u * Tq u')) ^ c
theorem Wsh_bound  (hA : 0 ≤ A) : ∃ C ≥ 0, ∀ u u' ξ > 0, ‖Wsh u u' ξ‖ ≤ C * (1 + ξ / (Tq u * Tq u')) ^ (-A)
```

* All constants are uniform in u, u′ ∈ ℝ, hence in the lag v = u′ − u.
* The Stirling input is `HeckeAFE.norm_Gamma_ratio_line`, applied at t = u and t = −u′. Each gives
  a factor e^{π|y|/2}, so the product carries e^{π|y|}, which is absorbed by `poly_exp_bound2`.
* The effective length of the lag series is therefore mn ≲ T(u)T(u′)·T^ε. Since |v| ≤ h this is
  the same as for |L|², so the off-diagonal ranges are those of `TwistedMoment`.

### 3. What is left

* **M1(c), not done.** The bounds ∂_u^j W̃_{u,u+v}(ξ) ≪_j T(u)^{−j}(1+ξ/T(u)²)^{−A}, uniform in
  |v| ≤ 1.
  * Route: Leibniz for the product R(u,y)·R(−(u+v),y) of the two Γ-ratio symbols, then
    `HeckeAFE3.norm_Rd_le` at both arguments, then the `DerivJ` line integrals at x = A+1 and
    x = −1, exactly as `HeckeAFE3.V_iteratedDeriv_bound`.
  * The u-derivative of the phase U(u, u+v) is i(ψ-difference)·U = O(|v|/u). That is
    `HeckeAFE2.norm_digamma_diff_le`.
  * About 400–500 lines. It is needed only for the integration-by-parts route of M2.
* **M2 (the off-diagonal clause of `SKSplitHyp'`), not started.** The plan is unchanged; the
  inputs now in place are `Wsh_bound`, `summable_sTerm` and `norm_sTerm_le`. Two ways to finish:
  * Re-run `TwistedMoment`'s generic `GoodSeq` machinery with the lag weight. The obstacle is that
    the weight now depends on (u, u′) jointly, whereas `GoodSecondTerm2` uses the t-symmetric
    V(Λ − 2log(t/2π)).
  * Integration by parts in u (needs M1(c)), followed by `SCS2Coprime.scs2_general` partial
    summation over acm − bdn = ℓ.
  * Estimate 1.5–3k lines either way.
* After M1(c)+M2, M3 (diagonal Mellin evaluation) and M4 (`SKSplitHyp' ⇐ SKQFHyp`), the
  positive proportion would be at level 2 on `QFHyp ∧ SKQFHyp θ`. Both of these hypotheses now
  have numerical support (level 4).


Note: `scripts/selberg_key/zgrid.txt` (2.6 MB of Z-values) is not committed; regenerate it with `zgrid.gp` (under a minute).

---

## 2026-11-06 (third pass): M1(c) done; M2 checkpoint (`SelbergKey3/`)

    nice -n 10 lake build RamanujanTau.SelbergKey3.Main      # exit 0

* All 12 `#print axioms` give `[propext, Classical.choice, Quot.sound]`.
* There is no `sorry`, `admit`, `native_decide` or `axiom`.
* 3 files, 474 lines: `LagDeriv.lean`, `IBP.lean`, `Main.lean`.

### M1(c) `LagDeriv.lean`: all u-derivatives of the lag weight (level 1)

```lean
theorem Wlag_iteratedDeriv_bound {j : ℕ} (hj : 1 ≤ j) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v ξ : ℝ, |v| ≤ 1 → 0 < ξ →
      HasDerivAt (iteratedDeriv j (fun w : ℝ => Wsh w (w + v) ξ))
        (iteratedDeriv (j + 1) (fun w : ℝ => Wsh w (w + v) ξ) u) u ∧
      ‖iteratedDeriv j (fun w : ℝ => Wsh w (w + v) ξ) u‖ ≤
        C / (1 + |u|) ^ j * (1 + ξ / (Tq u * Tq (u + v))) ^ (-A)
```

So u ↦ W̃_{u,u+v}(ξ) is C^∞, and ∂_u^j W̃ ≪_{j,A} (1+|u|)^{−j}(1+ξ/(T(u)T(u+v)))^{−A}, uniformly in
the lag |v| ≤ 1. The j = 0 case is `SelbergKey2.Wsh_bound`.

The route is `HeckeAFE3.DerivJ` applied to the **product** symbol R(u,y)·R(−(u+v),y), where R is
the Γ-ratio `HeckeAFE3.Rf`:

* **Derivatives of the second factor.** For R(−(u+v)), `iteratedDeriv_Rf_neg` uses Mathlib's
  `iteratedDeriv_comp_neg` and `iteratedDeriv_comp_sub_const`.
* **Leibniz.** `iteratedDeriv_Pf` applies `iteratedDeriv_fun_mul`.
* **Symbol bound.** `norm_Pd_le` is `HeckeAFE3.norm_Rd_le` at u and at −(u+v), combined with
  (1+|u+v|) ≥ (1+|u|)/2 for |v| ≤ 1.
* **Under the integral.** `hasDerivAt_intPd` and `iteratedDeriv_Wl` use dominated
  differentiation, with local Gaussian domination as in `DerivJ`.
* **One line.** `norm_intPd_le`: ≪ (T(u)T(u+v)/ξ)^x(1+|u|)^{−j}.
* **Combining two lines.** The line x = A+1 (`Wsh_eq_Wl_pos`, via `W2sh_shift`) and the line
  x = −1 (`Wsh_eq_one_add_Wl`, via `W2sh_residue`; the constant 1 has zero derivative) are joined
  by `combine_r`.

### M2 building block `IBP.lean` (level 1)

```lean
theorem ibp_twice {g g' g'' : ℝ → ℂ} {A B ω : ℝ} (hω : ω ≠ 0) (hAB : A ≤ B)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : ∀ t, HasDerivAt g' (g'' t) t) (hg''c : Continuous g'')
    (hA : g A = 0) (hB : g B = 0) (hA' : g' A = 0) (hB' : g' B = 0) :
    ‖∫ t in A..B, g t * cexp ((ω * t : ℝ) * I)‖ ≤ (ω ^ 2)⁻¹ * ∫ t in A..B, ‖g'' t‖
```

### M2: status and the precise remaining plan (NOT done)

**Choice of route.** M2 goes by integration by parts and `scs2_general`. Reusing
`TwistedMoment`'s GoodSeq / averaging machinery was ruled out, for three reasons:

* that machinery runs on `GoodSecondTerm`'s *approximated* AFE weight V(log mn − 2log(t/2π)),
  not on the exact Γ-ratio weight W̃ of the lag expansion;
* it handles only real sequences with the **symmetric** twist cos(t log(n/m)). The lag product
  carries the complex factor n^{iv} and the phase U(u,u+v), so the antisymmetric sin-twist also
  appears (Gap 2 of `TWISTED_MOMENT.md`);
* its averaging identities assume a t-independent amplitude. Here U·W̃ depends on u.

**Why two integrations by parts are enough.** The off-diagonal frequencies are
ω = log(bdn/acm) with bdn − acm = k ≠ 0 an integer, so |ω| ≍ |k|/(acm).

* A term with |k| > K₀ is bounded by `ibp_twice` by ≪ (ac)²T/k² per m-row.
* Summed over m, n and k > K₀, these give ≪ T·y^{O(1)}/K₀.
* The terms with 1 ≤ |k| ≤ K₀ are shifted convolution sums Σ_m λ(m)λ((acm+k)/bd)·H_k(m), which
  are handled by partial summation against `SCS2Coprime.scs2_general`. They give
  ≪ K₀ T^{1−η} y^{B}.
* Taking K₀ = T^{η/2} gives a power saving T^{1−η/2}y^{O(1)}. That is far below the (1/√K)T h²
  required, for small θ and large T.

**Remaining sub-lemmas, with estimates.**

| # | lemma | est. lines |
|---|---|---|
| M2.0 | **Phase U(u,u+v).** U′ = iδU with δ = Re ψ(6+iu) − Re ψ(6+i(u+v)), and U″ = (iδ′ − δ²)U, with \|δ\|, \|δ′\| ≪ (1+\|u\|)^{−1}. Inputs: `HasDerivAt.norm_sq` for ‖Γ(6+iu)‖, `HeckeAFE2.norm_digamma_diff_le`, `HeckeAFE3.norm_iteratedDeriv_digamma_le` | 200 |
| M2.1 | **The window.** A concrete smooth admissible φ_T(t) = Φ(t/T) (`ContDiffBump`), with \|φ_T^{(j)}\| ≪ T^{−j}, supported in [T/2, 3T], and φ_T ≥ 1 on [T,2T] | 150 |
| M2.2 | **One far term.** For \|ω\| > 0: \|∫φ_T(t−x)·U·W̃_{t,t+v}(ξ)e^{itω}dt\| ≪ T^{−1}ω^{−2}(1+ξ/T²)^{−A}. Inputs: `ibp_twice`, M2.0, M2.1, `Wlag_iteratedDeriv_bound` (j ≤ 2), `Wsh_bound` | 250 |
| M2.3 | **ξ-derivative of W̃.** ξ∂_ξW̃ ≪ (1+ξ/T²)^{−A}; the line integral picks up an extra factor z. This is needed for partial summation in m | 150 |
| M2.4 | **Near terms.** Partial summation of Σ_m λ(m)λ((acm+k)/bd)H_k(m) against `scs2_general`, giving ≪ (T+k)^{1−η}(ab)^{B}·sup(\|H\|+m\|H′\|) | 400 |
| M2.5 | **Assembly.** Swap Σ' with the triple integral (dominated convergence, `norm_sTerm_le`); sum over the y⁴ quadruples, using \|β\| ≤ √n; split k ≤ K₀ / k > K₀; set K₀ = T^{η/2}, θ small; and the tail mn ≫ T^{2+ε} via `Wsh_bound`. The result is the off-diagonal clause of `SKSplitHyp'` | 800–1200 |

The total is about 2–2.4k lines, and it is entirely analytic: the only arithmetic input is the
already-proved `scs2_general`. After M2 the remaining work is M3 (diagonal Mellin evaluation)
and M4 (`SKSplitHyp' ⇐ SKQFHyp`).

---

## 2026-11-06 (fourth pass): M2.0–M2.3, M2.4 core and M2.5a done; `offLag_bound` NOT yet (`SelbergKey4/`)

    nice -n 10 lake build RamanujanTau.SelbergKey4.Main      # exit 0

* All 23 `#print axioms` in `SelbergKey4/Main.lean` give `[propext, Classical.choice, Quot.sound]`.
* `grep` finds no `sorry`, `admit`, `native_decide` or `axiom` in `RamanujanTau/SelbergKey4/`.
* 7 files, 1370 lines. No committed file was modified; `RamanujanTau.lean` does not import the module.

**Status.** The off-diagonal clause of `SKSplitHyp'` is **not** proved yet. All the analytic
single-term inputs are done (level 1), and so is the arithmetic core of the near-term
partial summation. What is missing is the summation over the lattice (§3 below).

### 1. What is proved (level 1)

**M2.0 `Phase.lean`: the phase U(u,u+v).**

```lean
theorem Ush_eq (u v : ℝ) : Ush u (u + v) = (2 * π : ℂ) ^ ((v : ℂ) * I) * (eG u * conj (eG (u + v)))
  -- eG u = Γ(6+iu)/|Γ(6+iu)|
theorem hasDerivAt_eG (u : ℝ) : HasDerivAt eG (I * (psR u : ℂ) * eG u) u      -- psR u = Re ψ(6+iu)
theorem hasDerivAt_Ulag (v u : ℝ) : HasDerivAt (Ulag v) (I * (dlt v u : ℂ) * Ulag v u) u
  -- Ulag v u = Ush u (u+v), dlt v u = Re ψ(6+iu) − Re ψ(6+i(u+v))
theorem hasDerivAt_Ulag1 (v u : ℝ) : HasDerivAt (fun w => I * (dlt v w : ℂ) * Ulag v w)
    ((I * (dlt1 v u : ℂ) - (dlt v u : ℂ) ^ 2) * Ulag v u) u
theorem Ulag_bounds : ∃ C ≥ 0, ∀ u v, |v| ≤ 1 → ‖Ulag v u‖ = 1 ∧
    ‖I * dlt v u * Ulag v u‖ ≤ C / (1 + |u|) ∧ ‖(I * dlt1 v u - dlt v u ^ 2) * Ulag v u‖ ≤ C / (1 + |u|) ^ 2
```

The second-derivative bound uses the *difference* ψ′(6+i(u+v)) − ψ′(6+iu) ≪ (1+|u|)^{−2}
(`HeckeAFE3.norm_iteratedDeriv_digamma_diff_le`). The bound ψ′ ≪ 1/u alone would be too weak:
it would give ∫|g″| ≍ 1 in M2.2 instead of 1/T.

**M2.1 `Window.lean`.** Φ = `ContDiffBump` at 7/4 with radii 3/4 < 1, and φ_T(t) = Φ(t/T).

```lean
theorem admissible_phiT (hT : 0 < T) : SelbergKey.Admissible T (T / 2) (3 * T) (phiT T)
lemma hasDerivAt_phiT  : HasDerivAt (phiT T) (Phi1 (t / T) / T) t
lemma hasDerivAt_phiT1 : HasDerivAt (fun t => Phi1 (t / T) / T) (Phi2 (t / T) / T ^ 2) t
lemma phiT_zero_outside (hT : 0 < T) (ht : t ∉ Icc (3/4*T) (11/4*T)) : Phi (t/T) = 0 ∧ Phi1 (t/T) = 0 ∧ Phi2 (t/T) = 0
lemma Phi_bounds : ∃ M ≥ 0, ∀ s, |Phi s| ≤ M ∧ |Phi1 s| ≤ M ∧ |Phi2 s| ≤ M
```

**M2.2 `FarTerm.lean`: one off-diagonal t-integral.** Here gT T x v ξ t = φ_T(t)·U(t+x, t+x+v)·W̃_{t+x,t+x+v}(ξ).

```lean
theorem farTerm_bound (A : ℝ) (hA : 0 ≤ A) :
    ∃ C ≥ 0, ∀ T x v ξ ω, 1 ≤ T → 0 ≤ x → x ≤ 1 → |v| ≤ 1 → 0 < ξ →
      ‖∫ t in (T/2)..(3*T), gT T x v ξ t * cexp ((ω * t : ℝ) * I)‖ ≤ C * T * (1 + ξ / T^2) ^ (-A) ∧
      (ω ≠ 0 → ‖∫ …‖ ≤ C / (ω ^ 2 * T) * (1 + ξ / T^2) ^ (-A))
```

The proof goes through a small C² calculus: the structure `C2 f f' f''`, `C2.mul` (Leibniz), and
`C2.comp_add`.

* `FW_package`: U·W̃ is C² with ‖(UW̃)^{(j)}‖ ≤ C(1+|u|)^{−j}(1+ξ/(T(u)T(u+v)))^{−A} for j ≤ 2.
* `R_le` localizes this to u ∈ [0, 4T].
* `gT2_bound` gives ‖g″‖ ≤ C T^{−2}(1+ξ/T²)^{−A}.
* `SelbergKey3.ibp_twice` then finishes the proof.

The case j = 0 of the W̃-derivative (`hasDerivAt_Wv0`) was missing from `SelbergKey3`. It is
added here.

**M2.3 `XiDeriv.lean`: ξ∂_ξ W̃.**

* On the line Re z = x, ∂_ξ[ξ^{−z}e^{z²}/z] = −ξ^{−1}ξ^{−z}e^{z²} (`hasDerivAt_Kf_xi`): the 1/z
  drops out.
* So ξ∂_ξ W̃ = −Vl x, with Vl x = ∫R(u)R(−(u+v))(2π)^{−1}ξ^{−z}e^{z²}dy. This holds on both
  lines x = A+1 and x = −1, and the two values agree by `HasDerivAt.unique`.
* `norm_Vl_le` gives ‖Vl x‖ ≤ K(T(u)T(u+v)/ξ)^x, and `combine_r` joins the two lines.

```lean
theorem Wxi_bound (hA : 0 ≤ A) : ∃ C ≥ 0, ∀ u v ξ, 0 < ξ →
    HasDerivAt (fun ξ' => Wsh u (u + v) ξ') (-(Vl (A + 1) v ξ u / ξ)) ξ ∧
    ‖(ξ : ℂ) * -(Vl (A + 1) v ξ u / ξ)‖ ≤ C * (1 + ξ / (Tq u * Tq (u + v))) ^ (-A)
```

This needs no condition on v.

**M2.4, arithmetic core (`Line.lean`): line partial sums are box sums.** Along
P m − Q n = k (P, Q ≥ 1), both m and n increase. Hence

```lean
theorem lineSum_eq_shiftSum2 (hP : 1 ≤ P) (hQ : 1 ≤ Q) (k : ℤ) (M : ℕ) :
    lineSum P Q k M = shiftSum2 P Q k (Nbox P Q k M)        -- Nbox = max(M, ⌊(PM−k)/Q⌋₊) ≤ M + PM + |k|
theorem abs_lineSum_le : ∃ C ≥ 0, ∀ P Q k M, 1 ≤ P → 1 ≤ Q → k ≠ 0 →
    |lineSum P Q k M| ≤ C * (M + P*M + |k|) ^ (1 - 1/21) * |k| ^ (1/21) * (P*Q) ^ 12      -- scs2_general
theorem norm_sum_mul_le_abel (h c : ℕ → ℂ) (N : ℕ) (hB : ∀ n ≤ N, ‖∑ i ∈ range n, c i‖ ≤ B) :
    ‖∑ i ∈ range N, h i * c i‖ ≤ B * (‖h (N-1)‖ + ∑ i ∈ range (N-1), ‖h (i+1) - h i‖)
```

Here lineSum P Q k M = Σ_{1≤m≤M} λ(m)λ((Pm−k)/Q), summed over the m for which the quotient is a
positive integer. This settles the question raised in the third pass of how to feed a
one-variable partial summation from the *box* sums of `scs2_general`. No new SCS input is needed.

**M2.5a `Term.lean`: one term of the exact expansion, windowed.** With ω = log(bdn/(acm))
(`omg`) and ξ = 4π²mn:

```lean
theorem term_eq (a b c d) (hm : 1 ≤ m) (hn : 1 ≤ n) (u v : ℝ) :
    Ush u (u+v) * (eph a b u * eph c d (u+v) * sTerm u (u+v) (m,n)) =
      kap4 c d m n v * (FW v (4π²mn) u * cexp ((omg a b c d m n * u : ℝ) * I))
theorem norm_kap4 : ‖kap4 c d m n v‖ = |τ(m)| * |τ(n)| * (m*n) ^ (-6)
theorem term_integral_bound (hA : 0 ≤ A) : ∃ C ≥ 0, ∀ a b c d m n T x v, 1 ≤ m → 1 ≤ n → 1 ≤ T →
    0 ≤ x → x ≤ 1 → |v| ≤ 1 →
    ‖∫ t in (T/2)..(3T), φ_T(t) * (Ush (t+x) (t+x+v) * (eph a b (t+x) * eph c d (t+x+v) * sTerm (t+x) (t+x+v) (m,n)))‖
      ≤ |τ(m)τ(n)|(mn)^{−6} * (C (1 + 4π²mn/T²)^{−A}) * min T (if ω = 0 then T else 1/(ω² T))
```

These are exactly the summands of `OffLag`, once `lag_split` and `Sl_sub_diagS` have been
applied and the window φ_T is used on [A, B] = [T/2, 3T].

### 2. A correction to the third-pass plan (paper)

Two points need changing.

* **Near terms must exclude small m.** For 1 ≤ |k| ≤ K₀ the weight is
  H_k(m) ≍ (T/m)·min(1, (Pm)²/(T k)²). For m ≤ T^{1−ε} the far-term bound already gives
  ≪ T^{1−2ε}y⁴/k². Partial summation over all m ≥ 1 would instead give a boundary term of size
  ≍ k·T at m ≍ 1, which is no saving. So split by m:
  * m ≤ T^{1−ε}: far bound;
  * T^{1−ε} < m ≤ T^{1+ε}: Abel summation, with `abs_lineSum_le` giving the saving T^{−1/21}
    (up to T^{ε}y^{O(1)}K₀^{O(1)});
  * mn > T^{2+ε}: the decay (1+ξ/T²)^{−A}.
* **The trivial bound is not enough.** Summing the far bound trivially over all off-diagonal
  terms gives ≍ T log T·y^{O(1)}. The target is T h²/√K = T K^{3/2}/log²T. So the k ≤ K₀ terms
  *must* get the SCS saving, and K₀ = T^{δ} for a small δ (≤ 1/50, say). Summing the far terms
  over m, n uses Σ_{m≤X}|λ(m)|² ≪ X (Rankin–Selberg, available as
  `RankinSelbergGeneral.rankinSelberg_asymptotic_discriminant`) and Cauchy–Schwarz. Deligne is
  not needed.

### 3. What remains for `offLag_bound` (estimate 1.2–1.8k lines)

| # | step | content |
|---|---|---|
| R1 | swap Σ' and ∫∫∫ | `lagInt (OffLag β y) (phiT T) (T/2) (3T) h` = 2Re Σ_{abcd} wc wc Σ'_{p ∉ diag} ∫∫∫ φ_T·(term). Use `lag_split`, `Sl_sub_diagS`, and `intervalIntegral.hasSum_integral_of_dominated_convergence` three times. Domination by `norm_sTerm_le`, where 1/\|Γ(6+iu)Γ(6−iu′)\| is bounded on the compact u-range. Note h = K/log T ≤ 1 for large T, so \|v\| ≤ 1. About 300 lines |
| R2 | far sum | Σ over m, n with \|bdn − acm\| = k, \|k\| > K₀ or m ≤ T^{1−ε}, of `term_integral_bound`. Use \|ω\| ≥ \|k\|/(2y²·max(m,n)·…) (`Real.log` ratio bound) and Σ\|τ(m)\|²m^{−11} ≪ X (Rankin–Selberg) with Cauchy–Schwarz. Result ≪ T^{1−δ′}y^{O(1)}. About 400 lines |
| R3 | near sum | For fixed (a,b,c,d), k ∈ [1, K₀] and m ∈ (T^{1−ε}, T^{1+ε}]: H_k(m) = (mn)^{−1/2}·(the `term_integral_eq` integral). Its variation Σ\|H(m+1) − H(m)\| is ≪ k·T^{ε}, from `Wxi_bound` (ξ-derivative), ∂_ω of the t-integral (≤ T²·\|gT\|) and the m-derivative of (mn)^{−1/2}. Then `norm_sum_mul_le_abel` + `abs_lineSum_le`. Result ≪ K₀^{O(1)}T^{1−1/21+O(ε)}y^{O(1)}. About 500 lines |
| R4 | assembly | Choose ε, δ, K₀, θ small (θ ≤ 1/81600 is plenty). For T ≥ T₀(K), T^{1−η}y^{O(1)} ≤ T h²/√K. This gives `offLag_bound`, and then `skSplitHyp'_of_diag : (diagonal clause for phiT) → SKSplitHyp' θ` is immediate from `admissible_phiT` (the window is now fixed, so the diagonal clause must be stated for φ_T, A = T/2, B = 3T). About 200 lines |

Evidence levels: everything in §1 is level 1. §2 and §3 are level 3 (paper). The diagonal
clause itself remains M3/M4 (level 3, numerically supported at level 4 by the second pass).

---

## 2026-11-06 (fifth pass): R1 and R4 done; off-diagonal clause reduced to `QuadOffHyp` (`SelbergKey5/`)

    nice -n 10 lake build RamanujanTau.SelbergKey5.Main      # exit 0

* All 14 `#print axioms` in `SelbergKey5/Main.lean` give `[propext, Classical.choice, Quot.sound]`.
* `grep` finds no `sorry`, `admit`, `native_decide` or `axiom` in the directory.
* 3 files, 492 lines.
* No committed file was modified. `SelbergKeyDiag/` was only read; it contains just `Conv.lean`
  (`lag_conv`) and no diagonal statement yet.
* So the diagonal hypothesis is stated here for the fixed window, as `DiagHypT θ` below.

**Status.** `offLag_bound` is proved at **level 2**, conditional on the named per-quadruple bound
`QuadOffHyp η B`.

* `QuadOffHyp` is **provable** with the existing tools (§3). It is not an unprovable input. It
  is the content of R2 and R3, which are not formalized yet.
* `skSplitHyp'_of_diag` (`DiagHypT θ ∧ QuadOffHyp η B ⇒ SKSplitHyp' θ`) is proved, also at
  level 2.

### 1. R1 `Inner.lean`: exact reduction to single-term integrals (level 1)

The windowed single term `Fq` is

    Fq T x v q p t = φ_T(t)·U(t+x, t+x+v)·(b/a)^{iu}(d/c)^{i(u+v)}·[p off-diagonal]·sTerm(u, u+v, p),   u = t + x.

For p off the diagonal this is exactly the integrand of `SelbergKey4.term_integral_bound`. The
weight is `wq β q = wc(a,b)·wc(c,d)` for q = (a,b,c,d).

```lean
theorem inner_offLag_eq (β y) (hT : 0 ≤ T) (x v) :
    ∫ t in (T/2)..(3*T), phiT T t * OffLag β y (t + x) v =
      2 * (∑ q ∈ Q4 y, (wq β q : ℂ) * ∑' p : ℕ × ℕ, ∫ t in (T/2)..(3*T), Fq T x v q p t).re
theorem abs_inner_offLag_le … : |…| ≤ 2 * ∑ q ∈ Q4 y, |wq β q| * ‖∑' p, ∫ … Fq T x v q p t‖
```

The proof applies `intervalIntegral.hasSum_integral_of_dominated_convergence` to the *real*
summands f_p = 2 Re Σ_q w(q) Fq(q; p). This needs no continuity of the limit.

* **Dominating function:** 2·Σ|w|·|φ_T(t)|·C₀|Γ(6+iu)Γ(6−i(u+v))|^{−1}(4π²)^{−2}·g(m)g(n), from
  `SelbergKey2.norm_sTerm_le`.
* **Pointwise limit:** `lag_split` + `Sl_sub_diagS` (`phi_offLag_eq`).
* **Exchanging Re and ∫:** `reCLM.intervalIntegral_comp_comm`.
* **Exchanging Σ' and Σ_q:** `Summable.tsum_finsetSum`, with ‖∫Fq‖ ≤ (∫Abd)·g(m)g(n).

### 2. R4 `Reduce.lean`: assembly (level 1 for the reductions, level 2 on `QuadOffHyp`)

```lean
theorem lagInt_le_of_inner (hh : 0 ≤ h)
    (hE : ∀ x ∈ Icc 0 h, ∀ x' ∈ Icc 0 h, |∫ t in A..B, φ t * G (t + x) (x' - x)| ≤ E) :
    lagInt G φ A B h ≤ h ^ 2 * E
lemma abs_wc_le (y) (ha : 1 ≤ a) (hb : 1 ≤ b) : |wc (βSel y) a b| ≤ 1          -- |βSel n| ≤ √n
def QuadOffHyp (η B : ℝ) : Prop :=
  ∃ C T₀, 0 ≤ C ∧ ∀ T ≥ T₀, ∀ q, 1 ≤ a → 1 ≤ b → 1 ≤ c → 1 ≤ d → ∀ x v, 0 ≤ x → x ≤ 1 → |v| ≤ 1 →
    ‖∑' p : ℕ × ℕ, ∫ t in (T/2)..(3*T), Fq T x v q p t‖ ≤ C * T ^ (1 - η) * (a*b*c*d) ^ B
theorem offLag_bound_of_quad (hB : 0 ≤ B) (hθ0 : 0 ≤ θ) (hηθ : 4*θ*(1+B) < η) (H : QuadOffHyp η B) :
    ∀ K ≥ 1, ∃ T₀, ∀ T ≥ T₀,
      lagInt (OffLag (βSel ⌊T^θ⌋₊) ⌊T^θ⌋₊) (phiT T) (T/2) (3*T) (K / log T) ≤ 1/√K * T * (K / log T)^2
def DiagHypT (θ : ℝ) : Prop :=   -- the diagonal clause of SKSplitHyp' for the fixed window φ_T on [T/2, 3T]
  ∃ D ≥ 0, ∀ K ≥ 1, ∃ T₀, ∀ T ≥ T₀,
    lagInt (DiagLag (βSel ⌊T^θ⌋₊) ⌊T^θ⌋₊) (phiT T) (T/2) (3*T) (K / log T) ≤ D/√K * T * (K / log T)^2
theorem skSplitHyp'_of_diag (hB : 0 ≤ B) (hθ0 : 0 ≤ θ) (hηθ : 4*θ*(1+B) < η)
    (hD : DiagHypT θ) (H : QuadOffHyp η B) : SKSplitHyp' θ
```

**How the bound is assembled.**

* For T ≥ e^K we have h = K/log T ≤ 1, so 0 ≤ x ≤ 1 and |v| ≤ 1.
* There are y⁴ ≤ T^{4θ} quadruples, |w| ≤ 1, and (abcd)^B ≤ T^{4θB}.
* So each inner integral is ≤ 2C·T^{1−η'}, with η' = η − 4θ(1+B) > 0, and this is ≤ T/√K
  once T^{η'} ≥ 2C√K + 1.

**Note for the diagonal agent.** `DiagHypT θ` is the exact statement needed. It uses the
window `SelbergKey4.phiT T` (Φ(t/T), with Φ the `ContDiffBump` at 7/4 of radii 3/4 < 1), the
range A = T/2, B = 3T, and h = K/log T.

### 3. What remains: prove `QuadOffHyp η B` (R2 + R3, paper level 3; estimate 0.9–1.4k lines)

The expected parameters are η = 1/21 − O(ε + δ) and B ≈ 14. Then `hηθ` holds for θ ≤ 1/2000,
and in particular for θ ≤ 1/81600.

Fix q = (a,b,c,d), P = ac, Q = bd. Every off-diagonal p = (m,n) with m, n ≥ 1 lies on exactly
one line Pm − Qn = ℓ ≠ 0 (terms with m = 0 or n = 0 vanish). The single-term bound is
`SelbergKey4.term_integral_bound`; through `if_neg` it applies verbatim to `Fq`.

1. **Re-index.** Write Σ'_p = Σ_{ℓ≠0} Σ_m over the lines. Absolute summability of
   p ↦ ∫Fq is already proved (`summable_integral_Fq`). Then use `tsum_fiberwise` / `HasSum.sigma`
   along p ↦ Pm − Qn.
2. **R2, far part.** Take the terms with |ℓ| > K₀ = T^δ, or m ≤ T^{1−ε}, or mn ≥ T^{2+ε}.
   * Bound them termwise with `term_integral_bound`, using |ω| ≥ |ℓ|/(2·max(Pm, Qn)).
   * Use Σ_{m≤X}|λ(m)|² ≪ X (Rankin–Selberg) and Cauchy–Schwarz along each line.
   * Total ≪ T^{1−min(δ, ε)}(PQ)^{O(1)}.
3. **R3, near part.** Take 1 ≤ |ℓ| ≤ K₀ and m ∈ (T^{1−ε}, T^{1+ε}).
   * The term equals λ(m)λ(n)·H_ℓ(m), with H_ℓ(m) = (mn)^{−1/2}e^{iv log(dn/c)}e^{iωx}J(ω_m, ξ_m)
     and n = (Pm − ℓ)/Q extended to real m.
   * The variation Σ|H(m+1) − H(m)| ≪ ℓ T^{O(ε)}. It comes from `SelbergKey4.Wxi_bound` (ξ∂_ξW̃),
     ∂_ω J ≤ ∫|t·gT|, and ∂_m of (mn)^{−1/2}.
   * Then `SelbergKey4.norm_sum_mul_le_abel` + `abs_lineSum_le` (`scs2_general`) give
     ≪ K₀^{2}T^{1−1/21+O(ε)}(PQ)^{12}.
   * One more input is needed: identify the line sum with `lineTerm`. Here
     `lineTerm P Q ℓ m` = λ(m)λ(n) when the line passes through (m,n), and 0 otherwise.

Evidence levels:

* §1 and §2: level 1 (Lean, axiom-clean).
* `offLag_bound_of_quad` and `skSplitHyp'_of_diag`: level 2, on `QuadOffHyp` (and `DiagHypT`).
* §3: level 3 (paper).

---

## 2026-11-06 (diagonal pass): M4 done; M3 reduced to one named analytic statement (`SelbergKeyDiag/`)

    nice -n 10 lake build RamanujanTau.SelbergKeyDiag.Main      # exit 0

* All 10 `#print axioms` in `Main.lean` give `[propext, Classical.choice, Quot.sound]`.
* No `sorry`, `admit`, `native_decide` or `axiom`; no warnings in these files. 7 files, 794 lines.
* No committed file was modified (this section is appended). Not imported from `RamanujanTau.lean`.
* Imports, read-only: `SelbergKey4.Window` (`phiT`), `SelbergKey5.Reduce` (`DiagHypT`, `QuadOffHyp`,
  `skSplitHyp'_of_diag`).

### Headlines

```lean
-- M3 output, as a named hypothesis (pure analysis; y = ⌊T^θ⌋, L = log(u/2π))
def DiagApproxHyp (θ : ℝ) : Prop :=
  ∃ C δ T₁ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ T, T₁ ≤ T → ∀ u ∈ Icc (T/2) (4*T), ∀ v, v ≠ 0 → |v| ≤ 1 →
    |DiagLag (βSel y) y u v - 2 * (Av y v (log (u / (2*π)))).re| ≤ C * (|v| * ‖Sv y v‖ + T ^ (-δ))

theorem diagLag_bound_of_SKQF (hS : SKQFHyp θ) (hD : DiagApproxHyp θ) :
    ∃ D ≥ 0, ∀ K ≥ 1, ∃ T₀, ∀ T ≥ T₀, ∀ φ A B, Continuous φ → (∀ t, 0 ≤ φ t) → (∀ t, φ t ≤ 1) →
      T/2 ≤ A → A ≤ B → B ≤ 3*T → lagInt (DiagLag (βSel y) y) φ A B (K/log T) ≤ D/√K * T * (K/log T)^2
theorem diagHypT_of_SKQF (hS : SKQFHyp θ) (hD : DiagApproxHyp θ) : SelbergKey5.DiagHypT θ
theorem sk_of_SKQF (hB : 0 ≤ B) (hθ0 : 0 ≤ θ) (hηθ : 4*θ*(1+B) < η)
    (hS : SKQFHyp θ) (hD : DiagApproxHyp θ) (hO : SelbergKey5.QuadOffHyp η B) : SKSplitHyp' θ
theorem tauL_positive_proportion_of_SKQF (0 < θ ≤ 1/81600) (0 ≤ B) (4θ(1+B) < η)
    (QFHyp) (SKQFHyp θ) (DiagApproxHyp θ) (QuadOffHyp η B) : ∃ c T₀, 0 < c ∧ … c·N(3T) ≤ N₀(3T)
```

`D = 6D₀ + 3`, where D₀ is the constant of `SKQFHyp` (ii). The window is the `φ_T` of
`SelbergKey4.Window` on [T/2, 3T], as for the off-diagonal side (`SelbergKey5`).

**Mismatch with the requested `diagHypT_of_SKQF : SKQFHyp θ → DiagHypT θ`.** The headline
needs the extra named hypothesis `DiagApproxHyp θ`, i.e. M3 is **not** discharged. Everything
downstream of the pointwise diagonal evaluation (M4) is unconditional.

### What is proved (level 1)

| file | content |
|---|---|
| `Conv.lean` | `lag_conv`: ∫₀ʰ∫₀ʰ a(x′−x) = ∫_{−h}^{h}(h−\|v\|)a(v) for any `a` integrable on (−h, h] (Fubini with kernel 1_{(0,h]}(x)1_{(0,h]}(x+v)), plus integrability of the outer integrand |
| `Meas.lean` | v ↦ N_p(a,1−iv), D_p(1−iv) continuous (M-test, `HafnerBridge.summable_Np`); `rhoC(m,1−iv)`, 𝒮, 𝒜(·,L) measurable; 𝒮⁰ continuous. Non-vanishing of D_p is not needed |
| `Generic.lean` | `lagInt_le_of_approx`: G continuous, \|G(t+x,x′−x) − a(x′−x, ℓ(t))\| ≤ ε for x ≠ x′, and \|∫(h−\|v\|)a(v,ℓ(t))\| ≤ M ⟹ lagInt G φ A B h ≤ (B−A)(M+εh²) for any continuous 0 ≤ φ ≤ 1. The approximant may be singular at v = 0 (as 𝒜 is) |
| `Reduce.lean` | `abs_reAv_sub_le`: \|Re𝒜(v,L₁) − Re𝒜(v,L₂)\| ≤ \|L₁−L₂\|·\|𝒮(v)\|·(\|γ_R\|\|v\| + r₀). With clause (i) this moves L from log((t+x)/2π) to log(t/2π) at cost O(hB/T), so **no** φ(u−x) → φ(u) shift is needed. Then `diagLag_bound_of_SKQF`: the error ε(T) = C(hB + T^{−δ}) + 4(h/T)B(r₀+\|γ_R\|) → 0, and clause (ii) supplies M = 2D₀h²/√K |
| `Assemble.lean` | `diagHypT_of_SKQF`, `sk_of_SKQF` (via `SelbergKey5.skSplitHyp'_of_diag`), `tauL_positive_proportion_of_SKQF` |
| `DiagIndex.lean` | M3 step 1: `diagS_eq_tsum_ray`: for a,b,c,d ≥ 1 the diagonal {n·bd = m·ac} is exactly the ray (m,n) = (Q₁r, P₁r), so diagS = Σ_r sTerm(Q₁r, P₁r) |

### What remains: M3 = `DiagApproxHyp θ` (level 3 + level 4 numerics, §§3 and 2026-11-06 later)

The numerical end-to-end check (`corr.out`, `skdirect.out`) supports `DiagApproxHyp` directly:
it compares DiagLag-dominated lag correlations with 2Re𝒜. A **real-variable route** avoids
analytically continuing R(s), and it reuses the `HafnerBridge2` machinery:

1. *(done)* Ray reindexing. Still to do: normalize the ray term to κ·e_v·λ(Q₁r)λ(P₁r)r^{−1+iv}W̃(4π²P₁Q₁r²),
   using the identities u-phase = 1 and √(abcd·P₁Q₁) = [ac,bd] (cpow algebra, ~150 lines).
2. Peeling at the level of coefficients: λ(P₁r)λ(Q₁r) = Σ_{m∣r, m (P₁Q₁)-smooth} G(m)λ(r/m)², with
   Σ_m G(m)m^{−s} = ρ(P₁,s)ρ(Q₁,s) for Re s = 1 (iterate `HafnerBridge2.T_peel`; the coefficient
   bounds are `abs_gseq_le`). ~400 lines.
3. Base sum by partial summation against `GoodSecondTerm.AA_asymp`:
   Σ_n λ(n)²n^{−1+iv}W̃(βn²) = γ_R W̃(β) + r₀∫₁^∞x^{iv−1}W̃(βx²)dx − iv·ε(v) + O((β/T²)^{c}),
   where ε(v) = ∫₁^∞E(x)x^{iv−1}dx is bounded. Summed over m with G(m)m^{−1+iv}, the ε-term is
   **exactly** the |v|·\|𝒮(v)\| term of `DiagApproxHyp`. This is why the structural form R·ρ·ρ, and not a
   per-(P₁,Q₁) Laurent bound, is needed. Needs ξ∂_ξW̃ bounds (`SelbergKey4.XiDeriv`, `Wxi_bound`). ~500 lines.
4. Mellin evaluation: ∫₁^∞x^{iv−1}W̃(βx²)dx = [G(iv/2)β^{−iv/2}e^{−v²/4} − 1]/(iv) + O((β/T²)^{1/6})
   (shift to Re z = −1/6; poles at z = 0 and z = iv/2 of G(z)α^{−z}e^{z²}/(z(2z−iv))). Pattern:
   `W2sh_residue`, but with two poles. ~400 lines.
5. Phases: U = (u/2π)^{−iv}(1+O(\|v\|/u)) and U·G(iv/2)(4π²)^{−iv/2} = 1 + O(v²/u) (Stirling /
   digamma; `SelbergKey4.Phase` has U′ = iδU with \|δ\| ≪ 1/u). ~300 lines.
6. Assembly over the y⁴ quadruples and the smooth m: |κ| ≤ y^{O(1)}, Σ\|G(m)\|m^{−1+2c} < ∞ for small c
   (|λ(n)| ≤ Cn^{11/40}). This forces θ small, as everywhere else. ~400 lines.

Estimate: about 2–2.2k lines for M3. M5 (`SKQFHyp` itself) is unchanged.

---

## 2026-11-06 (sixth pass): R2 building blocks only; `QuadOffHyp` NOT proved (`SelbergKey6/`)

    nice -n 10 lake build RamanujanTau.SelbergKey6.Main      # exit 0

* Both `#print axioms` give `[propext, Classical.choice, Quot.sound]`.
* `grep` finds no `sorry`, `admit`, `native_decide` or `axiom` in the directory.
* 2 files, 84 lines.

The context budget of this session ran out before R2 + R3 could be written. `QuadOffHyp η B`,
and with it the unconditional `offLag_bound`, are **still open**. Two R2 building blocks are done
(level 1):

```lean
theorem sum_lam_sq_mul_le : ∃ A ≥ 0, ∀ (G : ℕ → ℝ) N, (∀ m, 0 ≤ G m) → (∀ m, G (m+1) ≤ G m) →
    ∑ i ∈ range N, lam (i+1) ^ 2 * G (i+1) ≤ A * ∑ i ∈ range N, G (i+1)
theorem abs_log_sub_ge (hX : 0 < X) (hY : 0 < Y) : |X - Y| / max X Y ≤ |Real.log X - Real.log Y|
```

* The first is Rankin–Selberg against a non-increasing weight: Abel summation twice, applied to
  the partial sums of λ² and of 1. It is the device for the far part, via
  |λ(m)λ(n)| ≤ (λ(m)² + λ(n)²)/2: for fixed m, n ↦ ℓ is injective.
* The second gives |ω| ≥ |ℓ|/max(bdn, acm).

### Simpler route for the near part than the fifth-pass plan (level 3)

Do **not** take ω- or ξ-derivatives of the t-integral J. Instead:

1. Split the off-diagonal p-set into Near ∪ Far, where
   Near = {(m,n) on Pm − Qn = ℓ : 1 ≤ |ℓ| ≤ K₀, M₁ < m ≤ M₂}, with M₁ = T^{1−ε}, M₂ = T^{1+ε}.
   * Near is **finite**. So Σ_{Near}∫Fq = ∫Σ_{Near}Fq(·,t) needs only `integral_finsetSum`.
2. **Near.** For each fixed t and ℓ, the inner sum is Σ_m c_ℓ(m)·h_t(m), with
   c_ℓ(m) = `lineTerm P Q ℓ m` (= λ(m)λ(n) on the line, 0 off it). Here
   h_t(m) = φ_T(t)U·(phases)·(mñ)^{−1/2}·e^{iu·log(Qñ/(Pm))}·e^{iv log(dñ/c)}·W̃_{u,u+v}(4π²mñ),
   with ñ = (Pm − ℓ)/Q real.
   * Its m-derivative is ≪ (|ℓ|T/m² + 1/m + (ξ∂_ξW̃)/m)·|h|. This uses `SelbergKey4.Wxi_bound`
     and nothing else.
   * So Σ_{M₁<m≤M₂}|Δh| ≪ |ℓ|T/M₁²·√(Q/P) + 1/M₁.
   * `SelbergKey4.norm_sum_mul_le_abel` + `abs_lineSum_le` then give
     ≪ |ℓ|^{1+1/21}T^{−1/21+O(ε)}(PQ)^{13} per t.
   * After ∫dt and Σ_{|ℓ|≤K₀}: ≪ K₀^{2+1/21}T^{1−1/21+O(ε)}(PQ)^{13}.
3. **Far.** Bound termwise with `SelbergKey4.term_integral_bound`:
   min(T, 1/(ω²T))(1+mn/T²)^{−A}, with |ω| ≥ |ℓ|/max(Pm,Qn) (`abs_log_sub_ge`).
   * Split |λλ| ≤ (λ(m)²+λ(n)²)/2, sum over the partner variable for each fixed m (resp. n),
     and apply `sum_lam_sq_mul_le` to the resulting non-increasing majorant.
   * Sub-cases and their sizes:
     * |ℓ| > K₀: ≪ y⁴T^{1+2ε}/K₀;
     * m ≤ M₁: ≪ y⁴T^{1−2ε+o(1)};
     * m > M₂: W̃-decay, ≪ T^{−A ε}.
4. **Parameters.** ε = 1/400, K₀ = T^{1/200}, A = 10. These give η = 1/50 and B = 14.
   Then 4θ(1+B) < η for θ < 1/3000, so θ ≤ 1/81600 is fine.

Estimate for the rest: about 900–1300 lines.

* Near part: re-indexing Near by (ℓ, m) via `lineTerm`, the real-variable derivative of h_t,
  and Abel. About 500 lines.
* Far part: about 400 lines.
* Assembly into `QuadOffHyp (1/50) 14`: about 150 lines.
* Then `offLag_bound_of_quad` gives the unconditional off-diagonal clause.

---

## 2026-11-06 (seventh pass): `QuadOffHyp (1/300) 13` PROVED; off-diagonal clause unconditional (`SelbergKey7/`)

    nice -n 10 lake build RamanujanTau.SelbergKey7.Main      # exit 0

* All 16 `#print axioms` in `SelbergKey7/Main.lean` give `[propext, Classical.choice, Quot.sound]`.
* `grep` finds no `sorry`, `admit`, `native_decide` or `axiom` in the directory; no warnings in
  these files. 8 files, about 1.7k lines.
* No committed file was modified. Not imported from `RamanujanTau.lean`. Imports (read-only):
  `SelbergKey6.RSMajor` (hence `SelbergKey5`, `SelbergKey4`, …) and `SelbergKeyDiag.Assemble`.

**Status.** The off-diagonal clause of `SKSplitHyp'` is now **unconditional** (level 1).
The only open input of (SK) is the diagonal: `DiagHypT θ`, or `SKQFHyp θ ∧ DiagApproxHyp θ`.

### Headlines (level 1)

```lean
theorem quadOffHyp : SelbergKey5.QuadOffHyp (1 / 300) 13      -- T₀ = 4
theorem offLag_bound {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 16800) :
    ∀ K ≥ 1, ∃ T₀, ∀ T ≥ T₀,
      lagInt (OffLag (βSel ⌊T^θ⌋₊) ⌊T^θ⌋₊) (phiT T) (T/2) (3*T) (K / log T) ≤ 1/√K * T * (K / log T)^2
theorem offLag_bound_81600 (0 ≤ θ) (θ ≤ 1/81600) : (same conclusion)
theorem skSplitHyp'_of_diagHypT (0 ≤ θ) (θ < 1/16800) (hD : DiagHypT θ) : SKSplitHyp' θ
theorem tauL_positive_proportion_of_SKQF' (0 < θ) (θ ≤ 1/81600)
    (QFHyp) (SKQFHyp θ) (SelbergKeyDiag.DiagApproxHyp θ) : ∃ c T₀, 0 < c ∧ … c·N(3T) ≤ #S
```

The exponents: `4θ(1+B) < η` with `η = 1/300`, `B = 13` holds for `θ < 1/16800`.
`tauL_positive_proportion_of_SKQF'` is `SelbergKeyDiag.tauL_positive_proportion_of_SKQF` with its
`QuadOffHyp` hypothesis discharged.

### The proof (fixed quadruple, `P = ac`, `Q = bd`, `ℓ = Pm − Qn`)

Parameters: ε = 1/400, δ = 1/100, σ = 2001/2000, A = 3 (in `term_integral_bound`).
`M₁ = ⌊T^{399/400}⌋`, `M₂ = ⌊T^{401/400}⌋`, `K₀ = ⌊T^{1/100}⌋`.

`Σ'_p ∫Fq = Σ_{Near} ∫Fq + Σ'_{Nearᶜ} ∫Fq` (`Summable.sum_add_tsum_compl`, using
`summable_integral_Fq`), where

    Near = {M₁ < m ≤ M₂, 1 ≤ n ≤ P M₂ + K₀, ℓ ≠ 0, |ℓ| ≤ K₀}   (finite; `nearSet`).

**Far (`Far.lean`, `FarCore.lean`): `≪ (PQ)^6 T^{299/300}`.**
Terms on the diagonal or with m·n = 0 vanish (`Fq_eq_zero`). Otherwise
`term_integral_bound` (A = 3) and `abs_tau_mul_rpow` give `|λ(m)λ(n)|(mn)^{−1/2} D Mω`,
with `D = (1+4π²mn/T²)^{−3} ≤ (T²/(mn))^s` (`D_le`) and `Mω = min(T, 1/(ω²T))`,
`|ω| ≥ |ℓ|/max(Pm,Qn)` (`omg_bound`, from `abs_log_sub_ge`). Outside Near:
`m ≤ T^{399/400}` or `m > T^{401/400}` or `|ℓ| > T^{1/100}` (`far_of_not_near`; the floors cost
nothing). `far_pt_real` gives the majorant

    256 (PQ)^6 T^{299/300} [(λ(m)²+λ(n)²)(mn)^{−σ} + λ(m)² m^{−σ} g(ℓ) + λ(n)² n^{−σ} g(ℓ)],  g(ℓ) = |ℓ|^{−3/2},

by cases:

| case | bound on (mn)^{−1/2} D Mω | T-exponent |
|---|---|---|
| off the line (2Pm ≤ Qn or 2Qn ≤ Pm): \|ω\| ≥ 1/2 | 4 T^{2σ−2} (mn)^{−σ} | 1/1000 |
| near the line, m > T^{401/400} (s = 3) | 64 P²Q⁴ T⁵ m^{−5} ℓ^{−2} | 5 + (401/400)(σ−5) ≈ 0.9905 |
| near the line, m ≤ T^{399/400} (s = 0) | 8 P²Q m ℓ^{−2}/T | (399/400)(1+σ) − 1 ≈ 0.9955 |
| near the line, \|ℓ\| > T^{1/100} (s = 1) | 16 P²Q² T m^{−1} ℓ^{−2}, ℓ^{−2} ≤ T^{−1/200} g(ℓ) | 1 + (401/400)(σ−1) − 1/200 ≈ 0.9955 |

On the line `(mn)^{−1/2} ≤ 2Q/m` and `m^{−σ} ≤ 4P² n^{−σ}`. The majorant is summed over every box
`[0,N)²` (`sum_box_Maj`): Rankin–Selberg `Σ λ(m)² m^{−σ} ≤ S_σ` (`sum_lam_sq_rpow_le`, from
`SelbergKey6.sum_lam_sq_mul_le`), `Σ n^{−σ} ≤ Z_σ`, and `Σ_n g(Pm − Qn) ≤ Σ_ℤ g` by injectivity
(`sum_gl_le`). Then `Real.tsum_le_of_sum_le` (`far_bound`). Deligne is not used.

**Near (`NearId`, `NearDeriv`, `NearAbel`, `NearBound`): `≪ (PQ)^{13} T^{1−11/2100}`.**

* `integral_finsetSum` moves the finite sum inside the t-integral.
* `Fq_eq`: an off-diagonal term is `Z(t)·λ(m)λ(n)·G_u(m,n)`, with `‖Z(t)‖ ≤ 1` and
  `G_u(r,s) = exp(−½(log r + log s) + i(v log s + u(log s − log r)))·W̃_{u,u+v}(4π² r s)`.
* `near_sum_eq`: the near sum is `Z(t) Σ_{1≤|ℓ|≤K₀} Σ_{M₁<m≤M₂} lineTerm(P,Q,ℓ,m)·H_ℓ(m)`, with
  `H_ℓ(r) = G_u(r, (Pr−ℓ)/Q)` for **real** r.
* `Hl_deriv`: for `r > 0`, `2|ℓ| ≤ r`: `‖H_ℓ(r)‖ ≤ KQ/r` and `‖H_ℓ'(r)‖ ≤ KQ(1/r² + |u||ℓ|/r³)`. The
  W̃ part uses only `Wsh_bound` and `Wxi_bound` (ξ∂_ξW̃ ≪ 1); there are no ω- or ξ-derivatives
  of t-integrals (the sixth-pass simplification).
* `abel_line`: `norm_sum_mul_le_abel` with partial sums `lineSum(M₁+n) − lineSum(M₁)`, and the mean
  value inequality on each `[m, m+1]` with `m ≥ T^{399/400}`:
  `‖Σ‖ ≤ 2B(H₀ + M₂V)`.
* `line_bound`: B from `abs_lineSum_le` (`scs2_general`). The T-algebra:
  `B ≤ 3 C_L P (PQ)^{12} T^{401/420 + 1/100}` and `H₀ + M₂V ≤ 6KQ T^{−49/50}`, so one line gives
  `≪ (PQ)^{13} T^{401/420 + 1/100 − 49/50}`.
* `near_bound`: at most `3T^{1/100}` lines, times the t-length `5T/2`. The exponent is
  `1 + 401/420 + 2/100 − 49/50 = 1 − 11/2100 ≤ 299/300`.

### Files

| file | lines | content |
|---|---|---|
| `Basic.lean` | 136 | `D_le`, `abs_tau_mul_rpow`, `sum_rpow_le`, `sum_lam_sq_rpow_le`, `gl`, `sum_gl_le`, `inv_sq_le_gl(_mul)` |
| `FarCore.lean` | 432 | `Mw`, `Mw_off`, `Mw_near`, `theta_off`, `pow_trade_lo/hi`, `theta_F1/F2/F3`, `theta_near`, `far_pt_real` |
| `Far.lean` | 288 | `M1`, `M2`, `K0`, `ell`, `nearSet`, `far_of_not_near`, `Fq_eq_zero`, `omg_bound`, `Maj`, `far_pt`, `sum_box_Maj`, `far_bound` |
| `NearId.lean` | 180 | `Ef`, `Gf`, `Zt`, `norm_Zt_le`, `Fq_eq`, `nt`, `Hl`, `Lset`, `sum_n_eq_lineTerm`, `near_sum_eq` |
| `NearDeriv.lean` | 200 | `Wd`, `W_consts`, `norm_cexp_Ef_le`, `rho_bounds`, `hasDerivAt_Hl`, `Hl_deriv` |
| `NearAbel.lean` | 95 | `norm_sub_le_of_deriv`, `sum_range_shift`, `abel_line` |
| `NearBound.lean` | 251 | `one_div_pow_le`, `two_rpow_le`, `var_T_alg`, `line_bound`, `card_Lset_le`, `near_bound` |
| `Main.lean` | 115 | `quadOffHyp`, `offLag_bound`, `offLag_bound_81600`, `skSplitHyp'_of_diagHypT`, `tauL_positive_proportion_of_SKQF'`, 16 `#print axioms` |

### What remains for (SK)

The diagonal only: `DiagHypT θ` (M3/M4). `SelbergKeyDiag` reduces it to `SKQFHyp θ ∧ DiagApproxHyp θ`.
`DiagApproxHyp` is the M3 Mellin evaluation; `SKQFHyp` is Selberg's arithmetic lemma (M5).
Evidence levels:

* everything in this section is level 1;
* (SK) and positive proportion are level 2 on `QFHyp ∧ SKQFHyp θ ∧ DiagApproxHyp θ`.

---

## 2026-11-06 (M3 pass): the diagonal Mellin evaluation (`SelbergKeyDiag2/`), checkpoint

    nice -n 10 lake build RamanujanTau.SelbergKeyDiag2.Main      # exit 0

* All `#print axioms` in `Main.lean` give `[propext, Classical.choice, Quot.sound]`.
* No `sorry`, `admit`, `native_decide` or `axiom`.
* The real-variable route (steps 1–6 of the previous section) is followed. Steps 1–4 are done at
  level 1. Steps 5 (phases) and 6 (assembly into `DiagApproxHyp θ`) remain.

### Proved (level 1)

| file | content |
|---|---|
| `Residue.lean` | `vline_residue_at`: for `F` holomorphic and bounded on a strip `a < 0 < b`, `∫_{(b)} − ∫_{(a)}` of `F e^{u²}/(u − iβ)` equals `2π F(iβ) e^{−β²}`. This is a pole off the real axis. Proof: write `e^{u²} = e^{(u−iβ)²}e^{2iβu+β²}`; the `dslope` part still has Gaussian decay |
| `Mellin.lean` | `mellin_line2`: `∫₁^∞ x^{iv−1} W(a,b;αx²) dx = (2π)⁻¹ ∫_{(2)} Γ(a+z)Γ(b+z)α^{−z}e^{z²}/(z(2z−iv)) dy` (Fubini; `∫₁^∞ x^{iv−1−2z} = 1/(2z−iv)`) |
| `Mellin2.lean` | partial fractions `1/(z(2z−iv)) = (iv)⁻¹(1/(z−iv/2) − 1/z)` and the two residues; `mellin_Wsh`: `∫₁^∞ x^{iv−1}W̃(αx²) = (G(iv/2)α^{−iv/2}e^{−v²/4} − 1)/(iv) + R` |
| `Remainder.lean` | `norm_Rsh_le`: `\|R\| ≤ K (α/T(u)T(u'))^{1/6}` uniformly (Stirling on `Re z = −1/6`) |
| `Base1–3.lean` | Abel summation (Mathlib `tendsto_sum_mul_atTop_nhds_one_sub_integral₀`) against `A(t) = Σ_{n≤t}λ(n)²/n = c₀ log t + γ_Δ + E(t)`, `\|E(t)\| ≪ t^{−1/5}` (`AA_asymp`), then integration by parts. `base_eval`: `Σ (λ(n)²/n) n^{iv} W̃(αn²) = γ_Δ W̃(α) + c₀J(α) − iv ε(v) + O((α/TT)^{1/20})`, where `ε(v) = ∫₁^∞ t^{iv−1}E(t)dt` depends on neither `u` nor `α`. Inputs: `Wsh_sub_one`, `SelbergKey4.Wxi_bound`, and `\|ξW̃'(ξ)\| ≪ (ξ/TT)^{1/20}` (`norm_xi_Wd_small`, from the `x = −1` line) |
| `BaseFull.lean` | `base_full`: the base sum equals `c₀G(p)α^{−p}e^{−v²/4}/(iv) + (−c₀/(iv) + γ_Δ − iv ε(v)) + O(r^{1/20} + r^{1/6})` with `p = iv/2`, `r = α/T(u)T(u+v)`. Both residues are included and the Laurent remainder is exact (`−iv ε(v)`) |
| `EvalC.lean` | `evC_gps`: `Σ_j g_j p^{−js} = N_p(a,s)/D_p(s)` and `D_p(s) ≠ 0` on `Re s = 1`. This is the complex version of the `HafnerBridge2` power-series evaluation (`g·D = U`, `ε·D = 1`) |
| `Peel.lean` | `Bs_peel` (exact): `Σ_r λ(p^a h' r)λ(kr) r^{−1+iv}W̃(αr²) = Σ_j g_j p^{−j(1−iv)} · [same for h'](αp^{2j})`. Proof via `T_peel`, a double series with `Summable.tsum_comm`, and the rescaling `ft_rescale` |
| `Induct1.lean` | the main term `Mn(h,k) = ρ(h)ρ(k)P(α) + ρ(h,1−iv)ρ(k,1−iv)L(v)` is stable under peeling (`hasSum_Mn_peel`). The point is `(αp^{2j})^{−iv/2}(p^{−(1−iv)})^j = α^{−iv/2}p^{−j}` |
| `Induct2–3.lean` | `twisted_eval`: for all coprime `h, k ≥ 1`, uniformly in `u`, `0 < \|v\| ≤ 1`, `α > 0`, `\|Bs(h,k)(α) − Mn(h,k)(α)\| ≤ Z₀M^{ω(hk)}(hk)²·(r^{1/20} + r^{1/6})`. Strong induction on `hk`; each peel costs `Σ_j\|g_j\|p^{−2j/3} ≤ M p^{2a}` |
| `Norm.lean` | `ray_term` and `diag_quad` (exact): `quadSum β y u (u+v) diagS = Σ_{[1,y]⁴} κ e_v · Bs(Q₁,P₁)(4π²P₁Q₁)`. The `u`-phase cancels since `bd·P₁ = ac·Q₁`, and `abcd·P₁Q₁ = [ac,bd]²` |

The Laurent remainder `−iv ε(v)·ρ(·,1−iv)ρ(·,1−iv)` is carried exactly through the peeling.
After summing over quadruples it is literally `−iv ε(v)·𝒮(v)`, the `|v|·‖𝒮‖` term of
`DiagApproxHyp`.

### Remaining for `DiagApproxHyp θ` (est. 0.6–0.8k lines)

1. **Phases (step 5).**
   * `\|U(u,u+v) − e^{−iv log(u/2π)}\| ≪ \|v\|/u`. Route: `h(s) = eG(u+s)e^{−is log u}`, with `h' = i(psR(u+s) − log u)h`, `\|psR(t) − log t\| ≪ 1/t` (`HeckeAFE2.norm_digamma_sub_log_le`), then the mean value theorem.
   * `\|U·G(iv/2)(4π²)^{−iv/2} − 1\| ≪ v²/u`. This product equals `‖Γ(6+iw)‖²/(‖Γ(6+i(w−v/2))‖‖Γ(6+i(w+v/2))‖)` with `w = u + v/2`. Its log is a second difference of `log‖Γ(6+it)‖`, bounded via `‖ψ'(6+it)‖ ≤ 72/‖6+it‖` (`HeckeAFE3.norm_iteratedDeriv_digamma_le`).
2. **Assembly (step 6).**
   * Apply `diag_quad` + `twisted_eval` (with `h = Q₁`, `k = P₁`, coprime by `SelbergKeyDiag.coprime_P1_Q1`).
   * Bound `\|ρ\|, \|ρ(·,1−iv)\| ≤ M^{ω}m²` (both are `Σ g_j x^j` with `\|x\| = 1/p`) and `\|κ\| ≤ max\|β\|⁴`.
   * Sum `y⁴` quadruples, giving errors `y^{O(1)}((y⁴/u²)^{1/20} + 1/u)`.
   * Choose `θ` small so that `y^{O(1)}T^{−1/10} ≤ T^{−δ}`. The statement then becomes `θ ≤ θ₀ → DiagApproxHyp θ`.

**Evidence levels.** Steps 1–4: level 1. `DiagApproxHyp`: still level 3 (paper) plus level 4
(the `corr.out` / `skdirect.out` numerics).

---

## 2026-11-06 (M3 complete): `DiagApproxHyp θ` proved for small θ (`SelbergKeyDiag2/`)

    nice -n 10 lake build RamanujanTau.SelbergKeyDiag2.Main      # exit 0

* All 28 `#print axioms` in `Main.lean` give `[propext, Classical.choice, Quot.sound]`.
* No `sorry`, `admit`, `native_decide` or `axiom`. 22 files, about 3.1k lines.
* No committed file was modified.
* This supersedes the "Remaining" list of the checkpoint section above.

### Headlines

```lean
theorem diag_pointwise : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (y : ℕ) (u v : ℝ), 1 ≤ y → 40 ≤ u → v ≠ 0 →
    |v| ≤ 1 → 16 * π ^ 2 * (y : ℝ) ^ 4 ≤ u ^ 2 →
      |DiagLag (βSel y) y u v - 2 * (Av y v (Real.log (u / (2 * π)))).re| ≤
        C * (|v| * ‖Sv y v‖ + (y : ℝ) ^ N * u ^ (-(1 / 10 : ℝ)))
theorem diagApproxHyp_small : ∃ θ₀ > 0, ∀ θ, 0 ≤ θ → θ ≤ θ₀ → SelbergKeyDiag.DiagApproxHyp θ
theorem diagHypT_of_SKQF' : ∃ θ₀ > 0, ∀ θ, 0 ≤ θ → θ ≤ θ₀ → SKQFHyp θ → SelbergKey5.DiagHypT θ
theorem sk_of_SKQF' : ∃ θ₀ > 0, ∀ θ η B, 0 ≤ θ → θ ≤ θ₀ → 0 ≤ B → 4θ(1+B) < η →
    SKQFHyp θ → SelbergKey5.QuadOffHyp η B → SKSplitHyp' θ
theorem tauL_positive_proportion_of_SKQF' : ∃ θ₀ > 0, ∀ θ η B, 0 < θ → θ ≤ θ₀ → θ ≤ 1/81600 → 0 ≤ B →
    4θ(1+B) < η → QFHyp → SKQFHyp θ → QuadOffHyp η B → (positive proportion of critical zeros)
```

* `θ₀ = 1/(20(N+1))`, where `N` is an explicit-in-principle exponent coming from the polynomial
  bounds `M^{ω(m)} ≤ m^K` and `|ρ(m)|, |ρ(m,1−iv)| ≤ m^{K+2}`. Then `δ = 1/20` and `T₁ = 2000`.
* `diagHypT_of_SKQF'` is the requested `SKQFHyp θ → DiagHypT θ`, valid for `θ ≤ θ₀`. The extra
  hypothesis `DiagApproxHyp` of `SelbergKeyDiag` is now discharged.

### New files since the checkpoint (level 1)

| file | content |
|---|---|
| `Phase.lean` | `phase_U`: `‖U(u,u+v) − e^{−iv log(u/2π)}‖ ≤ 118\|v\|/u`. `phase_Phi`: `‖U·G(iv/2)(4π²)^{−iv/2} − 1‖ ≤ 144v²/u` for `u ≥ 40`. The product equals `‖Γ(6+iw)‖²/(‖Γ(6+i(w−v/2))‖‖Γ(6+i(w+v/2))‖)`, and its log is a second difference bounded by `ψ'` (`digamma_lip`) |
| `Final1.lean` | `\|ρ_p(a)\|, \|N_p/D_p\| ≤ Gp(p,a) ≤ Mp^{2a}`; `\|ρ(m)\|, \|ρ(m,s)\| ≤ M^{ω(m)}m²`; `2^{ω(m)} ≤ m` |
| `Final2.lean` | `diagLag_eq`: `DiagLag = 2Re[U(Σ_q κe(Bs_q − Mn_q) + Xm)]`; `sum_Mn`; `UXm_sub_Av`, the exact difference from `𝒜` (three terms) |
| `Final3.lean` | `\|κ\| ≤ y²`, `P₁, Q₁ ≤ y²`, `\|𝒮⁰\|, \|𝒮\| ≤ y^{4K+14}`, `\|ε(v)\| ≤ 5C₁` |
| `Final4.lean` | `diag_pointwise` |
| `Final5.lean` | `diagApproxHyp_small` and the assembled headlines |

### Evidence levels and what is left for (SK)

* **Diagonal clause of `SKSplitHyp'`:** level 2 on `SKQFHyp θ` alone, for `θ ≤ θ₀`. M3 and M4 are level 1.
* **Positive proportion:** level 2 on `QFHyp ∧ SKQFHyp θ ∧ QuadOffHyp η B` (the last from `SelbergKey5`).
* **Remaining open inputs:**
  * `SKQFHyp θ` (M5): a Selberg–Delange statement for the four-variable form, uniform in the twist; level 4 numerics.
  * `QFHyp`.
  * The off-diagonal `QuadOffHyp`.
* **Caveat:** `θ₀` is not computed numerically. It is `1/(20(N+1))`, with `N = 4K₁ + 4K₂ + 15`
  and `K₁, K₂` the exponents with `M ≤ 2^K`. The value is tiny but positive. The positive-proportion
  statement additionally needs `θ ≤ 1/81600` and `4θ(1+B) < η`.
