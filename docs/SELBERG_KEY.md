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
