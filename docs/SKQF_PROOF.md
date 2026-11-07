# `SKQFHyp θ` (milestone M5): proof chain and Lean checkpoint (2026-11-06)

Lean: `RamanujanTau/SKQFProof/` (`Real`, `Elem`, `Contour`, `Bound`, `Final`, `Assemble`, `Main`;
about 1.15k lines). No sorry, no new axiom, no native_decide. All 8 headlines print
`[propext, Classical.choice, Quot.sound]`.

    nice -n 10 lake build RamanujanTau.SKQFProof.Main      # exit 0

**Status.** Clause (ii) of `SKQFHyp`, Selberg's lemma proper, is **reduced in Lean (level 1)** to
one bound of type (i): a `v`-uniform `1/log y` bound for `𝒮`, continued slightly below the real
axis (`SvStripHyp`). The reduction needs no branch-point or Selberg–Delange asymptotics. It uses
two exact facts and one contour shift. **`SvStripHyp` itself is not yet proved.** It is the complex
(`s = 1 − iz`) version of the `QFHyp` chain of `QF_PROOF.md`. §4 below gives the plan.

## 1. Two exact facts (Lean, level 1, `Real.lean`)

**(a) `𝒮⁰(v)` is real (`S0v_im`).** The phase of the `(a,b,c,d)` term of `𝒮⁰` is

    (P₁d/c)^{iv} (P₁Q₁)^{−iv/2} = (a/c)^{iv/2} (d/b)^{iv/2}.

The involution `(a,b,c,d) ↦ (c,d,a,b)` fixes `κ`, `P₁` and `Q₁`, and it conjugates this phase.
Since `r₀/(iv)` is purely imaginary, `Re[r₀ e^{−v²/4} 𝒮⁰(v)/(iv)] = 0`. **The `𝒮⁰` term drops out
of clause (ii) entirely.**

**(b) `𝒮(0) = Q⁰` is real (`Sv_zero_im`).** Writing `𝒮(v) = F₀ + v·G(v)`, where
`G = dslope 𝒮 0`, gives for `v ≠ 0` (`re_Av_eq`):

    Re 𝒜(v,L) = γ_R Re(e^{−ivL}𝒮(v)) + r₀ F₀ · L sinc(vL) − r₀ Im(e^{−ivL} G(v)).

**Numerical caveat about `scripts/selberg_key/sk.c`.** Its `S0` column carries an extra factor
`g^{iv}`, where `g = (ac,bd)`:

* the code computes `(ad)^{iv}(P₁Q₁)^{−iv/2}`;
* the Lean definition, and the derivation in `SELBERG_KEY.md` §3, have `(ad/g)^{iv}(P₁Q₁)^{−iv/2}`.

Consequently the code's `S0` is complex, and the `A(K,θ)` table in `SELBERG_KEY.md` is for the
code's 𝒜, not the Lean one. The `𝒮` column agrees with Lean.

**Re-run with the Lean 𝒜** (scratch post-processing of the existing `S_y*.txt`, level 4):

* **Clause (ii).** `max_L |I|/h²` at `y = 200` is:

  | θ | K = 1 | 2 | 4 | 8 | 16 | 32 | 64 |
  |---|---|---|---|---|---|---|---|
  | 1/10 | 8.36 | 7.64 | 5.55 | 2.92 | 1.54 | 0.78 | 0.39 |
  | 1/20 | 16.3 | 14.9 | 11.0 | 5.82 | 3.07 | 1.56 | 0.79 |

  This is a clean `1/K` decay. The large-`K` value is exactly the main term `π r₀ Q⁰ log y/(θK)`.
* **End-to-end lag correlation** against the real `Z(t)` at `T = 400`, `y = 5, 10`:
  * the Lean 𝒜 fits better at `v ≤ 0.6`: measured 2.875 at y = 10, v = 0.2, against Lean
    2.852 and code 2.938;
  * the two are comparable at larger `v`.

  So the Lean definition appears to be the correct one. This is relevant to `DiagApproxHyp`.

## 2. The reduction (Lean, level 1)

```lean
def stripR (δ₀ : ℝ) : Set ℂ := {z | |z.re| ≤ 1 ∧ -δ₀ ≤ z.im ∧ z.im ≤ 0}

def SvStripHyp (c' : ℝ) : Prop :=
  ∃ C δ₀ : ℝ, 0 ≤ C ∧ 0 < δ₀ ∧ ∀ y : ℕ, 2 ≤ y → ∃ F : ℂ → ℂ, ∃ U : Set ℂ, IsOpen U ∧
    stripR δ₀ ⊆ U ∧ DifferentiableOn ℂ F U ∧ (∀ v : ℝ, |v| ≤ 1 → F v = Sv y v) ∧
    ∀ z ∈ stripR δ₀, ‖F z‖ ≤
      C * (1 + |z.re| * Real.log y) ^ 2 * Real.exp (c' * |z.im| * Real.log y) / Real.log y

theorem skqfHyp_of_strip {θ c' : ℝ} (hθ : 0 < θ) (hc' : 0 ≤ c') (hθc : 8 * (c' + 1) * θ ≤ 1)
    (H : SvStripHyp c') : SKQFHyp θ
theorem skqfHyp_small_of_strip {c' : ℝ} (hc' : 0 ≤ c') (H : SvStripHyp c') :
    ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₁ → SKQFHyp θ
```

The constants are explicit: `B = 1` and `D = 1 + 24|r₀|C/θ + |r₀|(1 + 2048C/θ + 32C/θ)`.

**Proof.** Put `ℓ = log y`, `Λ = log T`, `h = K/Λ`. For `T ≥ T₀(K)` we have
`θΛ/2 ≤ ℓ ≤ θΛ`, `L ≥ Λ/2` and `hℓ ≤ K`.

1. **γ_R term.** It is at most `2|γ_R| h² C(1+K)²/ℓ`, which is `≤ h²/√K` once `ℓ ≫_K 1`.
   This is the only place where `T₀` depends on `K` polynomially.
2. **Main term `r₀F₀ L sinc`.** Use `|L sinc(vL)| ≤ 2L/(1+|v|L)` and
   `∫_{−h}^{h} L/(1+|v|L) = 2 log(1+hL)`. The term is at most `4|r₀|(C/ℓ) h log(1+K)`, which is
   `≪ h² log(1+K)/(θK) ≪ h²/(θ√K)`. **This is where the saving comes from: `Q⁰ ≪ 1/log y`
   against the Fejér kernel, giving `(log K)/K`.** No branch point is involved.
3. **Oscillatory term `∫(h−|v|) e^{−ivL} G(v)`** (`contour_bound`). Apply Cauchy on
   `[0,h]×[−δ₀,0]` with integrand `(h−z)e^{−izL}G`, and on `[−h,0]×[−δ₀,0]` with `(h+z)e^{−izL}G`.
   * On `Re z = 0` the two combine to `2e^{−izL}(F(z)−F(0))`, so there is no `1/z`. This part is
     `≤ 4M₀/b`.
   * On `Re z = ±h` the weight `h ∓ z = ∓iy` vanishes at the axis. These parts are
     `≤ 16M₁/(hb²)`.
   * The bottom is `≤ 4h(h+δ₀)M₁e^{−bδ₀}/δ₀`.
   * Here `M₀ = C/ℓ`, `M₁ = C(1+hℓ)²/ℓ` and `b = L − c'ℓ ≥ Λ/4`.
   * All three are `≪ h²/(θ√K)`. The side terms tolerate a loss `(1+Kθ)^c` with `c ≤ 5/2`; the
     hypothesis has `c = 2`.

**Answer to "can (ii) be reduced to (i)-type bounds plus an explicit v-integral?"** Yes, and this
is now done in Lean. The (i)-type input must be:

* uniform in `|Re z| log y`, with at most polynomial loss of degree `< 5/2`;
* holomorphic slightly below the axis.

The real-axis `v`-uniform bound alone does not suffice, because the term `e^{−ivL}(𝒮(v) − 𝒮(0))/v`
needs the oscillation. The uniform bound in `K` is the delicate point: `D` must not depend on
`K`. The contour argument meets it without any `v`-derivative bounds.

## 3. Evidence levels

| statement | level |
|---|---|
| `S0v_im`, `Sv_zero_im`, `re_Av_eq`, `contour_bound`, `int_bound`, `final_real` | 1 |
| `skqfHyp_of_strip`, `skqfHyp_small_of_strip` | 2 (on `SvStripHyp c'`) |
| `SvStripHyp c'` for some `c' ≤ 10` | 3 (plan in §4); real-axis part level 4 (`|𝒮(v)| log y ≤ 3.4` for `|v| log y ≤ 7`, `y ≤ 200`) |

## 4. Proving `SvStripHyp` under Deligne (paper, level 3): the complex QF chain

Put `s = 1 − iz`, `z = u − it` with `0 ≤ t ≤ δ₀ ≤ 1/4`, so that `|p^{−s}| = p^{−1+t}`.

1. **Bilinear form.** We have `e_z g^{−iz} = (ad)^{iz}(PQ)^{−iz}[P,Q]^{iz}`. Hence
   `𝒮(z) = Σ_{P,Q} x_z(P) x_z(Q) K^{[s]}(P,Q)`, where `x_z(P) = Σ_{ac=P} β(a)β(c) c^{−iz}` and
   `K^{[s]}(h,k) = [h,k]^{−s}ρ(h₁,s)ρ(k₁,s)`.
2. **Complex local closed forms.** `ρ_p(a,s) = (λ_a − Xλ_{a−2})/(1+X)` with `X = p^{−s}`.
   * The `1+X ≠ 0` and `D_p ≠ 0` facts come from
     `D_p(X)(1 − (λ²−1)X + (λ²−1)X² − X³) = 1 + X`, a formal Hecke identity that needs no
     Deligne.
   * This gives holomorphy of `rhoC(m, 1 − iz)` on `Im z > −1/2`, via `tsum` differentiability
     (M-test with `|λ(p^j)| ≤ j+1`).
3. **Complex Cholesky.** `K^{[s]} = Σ_{d|(h,k)} W^{[s]}(d) U^{[s]}(h,d) U^{[s]}(k,d)`.
   * The local LDLᵀ (`chol_loc`) is a polynomial identity in `X`. It is stated over `ℝ`
     (`variable (l X : ℝ)`), so it needs a mechanical copy over `ℂ`.
   * The work is to port `QFProof3` (`Decomp`, `DChol`) from `1/p` to `p^{−s}`.
4. **Factorization and smoothing.** `y_d = (log y)^{−2} Σ_{u₁,u₂≤y} Γ^z_d(u₁,u₂) J_z(y/u₁) J_0(y/u₂)`,
   with `J_z(x) = Σ_{m≤x} fR(m) m^{−1+iz} log(x/m)`.
   * On the `c` side the twist `c^{−iz}` cancels against `U^{[s]} ∝ c^{−s}`, so only `J_0` occurs
     there.
   * The first-order cancellations survive: `Γ(1,0) = X²λ²/(2(1+X))` and
     `Γ(0,1) = λ²X X̄₁/(2(1+X))`, both `O(p^{−2+2t})`.
5. **`J_z` bound** (Abel summation against `S_f(σ) = Σ_{log m≤σ} fR(m)/m`):

       J_z = ∫_0^τ S_f e^{izσ} dσ − iz ∫_0^τ (τ−σ) S_f e^{izσ} dσ.

   The pointwise `|S_f| ≪ (1+σ)^{−1/2}` (first clause of `selberg_sum_fR`) then gives
   `|J_z(x)| ≪ (log x)^{1/2}(1 + |z| log x) x^{t}`. Hence the exponent 2 in `SvStripHyp`.
6. **Local masses and Euler sums.** These are L1–L6 of `QF_PROOF.md` with `|X| = p^{−1+t}`.
   * Every `d^t`, `u^t`, `m^t` with `d ≤ y²` and `u, m ≤ y` is bounded by `y^{2t}`.
   * The products over primes converge for `t ≤ 1/4`.
   * The constants of `QFProof5` change only by absolute factors.
   * Result: `|𝒮(z)| ≪ (1+|u|ℓ)² y^{c't}/ℓ` with `c' ≈ 10`.
   * `8(c'+1)θ ≤ 1` holds for `θ ≤ 1/100`, and in particular for `θ ≤ 1/81600`.

**Milestones and estimates (Lean):**

| step | content | lines |
|---|---|---|
| S1 | items 2–3 | 0.8k |
| S2 | item 4 (port `QFProof3.Factor` and `QFProof4` multiplicativity to the twisted `Γ^z`) | 0.5k |
| S3 | item 5 | 0.3k |
| S4 | item 6 (port `QFProof5.Local`/`Euler` with complex `X`) | 1.0–1.3k |
| S5 | holomorphic `SvC` and assembly into `SvStripHyp 10` | 0.4k |

Total about 3–3.3k lines. The end product would be
`skqfHyp_deligne [DeligneBound] : ∃ θ₁ > 0, ∀ θ ∈ (0, θ₁], SKQFHyp θ`, by `skqfHyp_small_of_strip`.

## Literature

* Selberg (1942).
* Titchmarsh, §§10.9–10.22.
* Hafner, Math. Ann. 264 (1983).

## 2026-11-06 (SvStripB): §4 step 5, the `J_z` bound, is done in Lean (level 1)

Lean: `RamanujanTau/SvStripB/` (`JTwist`, `Downstream`, `Main`; 481 lines). No sorry, no new
axiom, no native_decide. No Deligne input. All 12 headlines print `[propext, Classical.choice, Quot.sound]`.

    nice -n 10 lake build RamanujanTau.SvStripB.Main      # exit 0

**Definition.** `Jz z x = Σ_{m≤x} (fR(m)/m) e^{iz log m} log(x/m)`.
* `Jz_eq_cpow`: this equals `Σ_{m≤x} fR(m) m^{−(1−iz)} log(x/m)`, the §4 normalisation with `s = 1 − iz`.
* `Jz_zero`: `J_0 = Isum fR`.

**Headlines.**
* `Jz_differentiable`: `z ↦ J_z(x)` is entire, since it is a finite sum.
* `Ssum_bound`: `|Σ_{m≤u} fR(m)/m| ≤ K/√(1+log u)` for `u ≥ 1`. This comes from the first clause of
  `selberg_sum_fR`, together with a trivial bound for small `u`.
* `Jz_eq_integral`: Abel summation via Mathlib's `sum_mul_eq_sub_integral_mul₀`, with weight
  `φ(u) = u^{iz}(log x − log u)` and `φ(x) = 0`:
  `J_z(x) = −∫_{(1,x]} u^{iz}(iz log(x/u) − 1) u^{−1} S(u) du`.
* `Jz_bound`: **`‖J_z(x)‖ ≤ K √(1+log x) (1 + ‖z‖ log x) exp(|Im z| log x)`** for all `z ∈ ℂ`
  and `x ≥ 1`.
  * The proof uses `∫_1^x du/(u√(1+log u)) = 2√(1+log x) − 2`.
  * It is uniform on all of ℂ, so no strip restriction is needed.
  * `Jz_bound_rpow` is the same statement written with `(1+log x)^{1/2}`.
* `Jz_bound_re`: `‖J_z(x)‖ ≤ K √(1+log x)(1 + |Re z| log x) exp(2|Im z| log x)`. It uses
  `1 + a + b ≤ (1+a)e^b`. This is the form whose polynomial factor is in `|Re z| log y`, matching
  `SvStripHyp`.

**Downstream form for step 4.** These lemmas are uniform in the kernel, so they apply to `Γ^z_d` for
each `z`.
* `Jz_div_bound`: `‖J_z(y/u)‖ ≤ K √(1+log y)(1+|Re z| log y) y^{2|Im z|}` for `u ∈ (0,y]`.
* `yd_bound`, for every `Γ : ℕ → ℕ → ℂ`:

      ‖Σ_{u₁,u₂≤y} Γ(u₁,u₂) J_z(y/u₁) J_0(y/u₂)‖
          ≤ K (1+log y)(1+|Re z| log y) y^{2|Im z|} Σ_{u₁,u₂≤y} ‖Γ(u₁,u₂)‖.

* `yd_bound_div`: the same bound with the `(log y)^{−2}` normalisation of `y_d`. It is the complex
  analogue of `QFProof.abs_yv_le`.
* `yd_holo`: if `z ↦ Γ^z(u₁,u₂)` is entire, so is the `y_d` sum.

**Consequences for §4 item 6.**
* The `J` side costs only the factor `(1 + |Re z| ℓ) y^{2t}`. That is degree 1 in `|Re z|ℓ`, while
  `SvStripHyp` allows degree 2. It also adds 2 to `c'`.
* The remaining degree-1 room is available to the `Γ^z` and Euler-sum side (S4).
* No derivative or log-weighted `J_z` bound is needed: the contour argument (`contour_bound`) uses
  only sup bounds and holomorphy.

**Evidence levels.** Every statement in this section is level 1.

**Remaining for `SvStripHyp`:** S1 (complex `ρ`/Cholesky), S2 (twisted factorisation
`y_d = (log y)^{−2} Σ Γ^z J_z J_0` as an exact identity), S4 (complex local masses and Euler sums,
giving `Σ|Γ^z_d| ≪ y^{O(t)}`) and S5 (assembly). S3 is now closed.

## 2026-11-06 (SvStripA): §4 steps 1–2 in Lean — complex local closed forms, holomorphy, complex Cholesky (level 1)

Lean: `RamanujanTau/SvStripA/` (`Chol`, `Local`, `Decomp`, `Holo`, `Main`; 915 lines). No sorry, no new
axiom, no native_decide. **No Deligne:** the only arithmetic input is the unconditional
`|λ(n)| ≤ C n^{11/40}` (`HafnerBridge.lam_bound`). All 19 headlines print `[propext, Classical.choice, Quot.sound]`.

    nice -n 10 lake build RamanujanTau.SvStripA.Main      # exit 0

**Step 1: closed forms** (`Local.lean`). Put `x = p^{−s}`, `N_x(a) = Σ_j λ(p^{j+a})λ(p^j)x^j` and `D_x = N_x(0)`;
`NpC p a s = N_{p^{−s}}(a)` and `DpC p s = D_{p^{−s}}`.
* Absolute convergence holds for `‖x‖p^{11/20} < 1`, that is for **`Re s > 11/20`** (`norm_xs_lt`).
* `Nx_succ`: `N(a+1) = λ_{a+1}D − λ_a x N(1)`.
* `Dx_mul_P`: `D(x)(1 − (λ_p²−1)x + (λ_p²−1)x² − x³) = 1 + x`. This is `HafnerBridge2.Dps_mul_P`
  evaluated by the complex Cauchy product.
* So `D ≠ 0` whenever `1 + x ≠ 0` (`Dx_ne_zero`).
* `Nx_eq_rhoPx_mul` and `NpC_div_DpC`: `N_p(a,s)/D_p(s) = ρ_p(a,x)`, where `ρ_p(a,x) := rrK x μ_p a` is
  `1`, `λ_p/(1+x)` or `(λ_{a+2} − xλ_a)/(1+x)`.
* `rhoC_eq_rhoCF`: `rhoC m s = rhoCF m s := Π_{p^a∥m} ρ_p(a, p^{−s})` for `Re s > 11/20`.
* Uniform local bounds for `‖x‖ ≤ 3/5` (for example `Re s ≥ 3/4`):
  * `norm_rhoPx_le`: `‖ρ_p(a,x)‖ ≤ (5/2)(|λ(p^a)| + |λ(p^{a−2})|)`;
  * `norm_WcK_le`: `‖W_e‖ ≤ 7(4+‖l‖²)‖x‖^e`.

**Holomorphy** (`Holo.lean`). The domain is `Ω = {Im z > −1}`, that is `Re(1−iz) > 0`. On `Ω`:
* `diff_rhoCF`: `z ↦ ρ(m,1−iz)` is holomorphic, since it is a finite product of rational functions
  of the entire `p^{−(1−iz)}`, and these have no pole while `‖x‖ < 1`.
* `diff_WdC`, `diff_UdC`, `diff_KqC`: the Cholesky data and the twisted kernel are holomorphic.

`SvC y z := Σ κ (P₁d/c)^{iz} ρ(P₁,1−iz) ρ(Q₁,1−iz)` (with closed-form `ρ`) satisfies:
* `SvC_ofReal`: `SvC y v = Sv y v` for all real `v`;
* `diff_SvC`: `SvC y` is holomorphic on `Ω`.

Therefore
```lean
def SvCBound (c' : ℝ) : Prop :=
  ∃ C δ₀ : ℝ, 0 ≤ C ∧ 0 < δ₀ ∧ δ₀ < 1 ∧ ∀ y : ℕ, 2 ≤ y → ∀ z ∈ stripR δ₀, ‖SvC y z‖ ≤
    C * (1 + |z.re| * Real.log y) ^ 2 * Real.exp (c' * |z.im| * Real.log y) / Real.log y
theorem svStripHyp_of_bound {c' : ℝ} (H : SvCBound c') : SvStripHyp c'
```
**The continuation part of `SvStripHyp` is now proved.** What remains is a pure size bound on an
explicit finite sum of explicit holomorphic functions.

**Step 2: complex Cholesky** (`Chol.lean`, `Decomp.lean`).
* `cholK` is `chol_loc` over an arbitrary field.
* `loc_cholC`: `Σ_{e≤a} W_e(x_p) L(a,e) L(a+n,e) = x_p^{a+n} ρ_p(n,x_p)`.
* `KqC_prod`: `n^{−s}` and `ρ` factor over primes. This uses `natCast_prod_cpow`.
* **`qDecompC`** (for `Re s > 0`):

      K^{[s]}(h,k) := [h,k]^{−s} ρ(h₁,s) ρ(k₁,s) = Σ_{d|h} W^{[s]}(d) U^{[s]}(h,d) U^{[s]}(k,d),

  with `U^{[s]}(h,d) = 0` unless `d | h`. Here:
  * `W^{[s]}(d) = Π WcK(λ_p, p^{−s}, v_p d)`;
  * `U^{[s]}(h,d) = 1_{d|h} Π L_p(v_p h, v_p d)`;
  * `L_p(a,0) = x^aρ_p(a,x)` and `L_p(a,e) = x^{a−e}λ(p^{a−e})`.

  This is the complex copy of `QFProof3.qDecomp`, with `W` and `U` holomorphic in `z` (`diff_WdC`, `diff_UdC`).

**Gaps / not done here.**
* §4 item 1, the bilinear form `𝒮(z) = Σ x_z(P)x_z(Q)K^{[1−iz]}(P,Q)` in terms of `KqC`, is not
  stated in Lean.
* The consistency check `KqC 1 = QFProof.Kq` (that is, `rhoPx p a (1/p) = rhoP p a`) is not stated.
  It follows from `rhoC_eq_rhoCF` together with `QFProof.rhoP_one`/`rhoP_add_two`, but it is not
  needed for S5.
* S2 (`QFactor` for the twisted `Γ^z`), S4 (complex Euler sums) and the `SvCBound` estimate itself
  remain open.

## 2026-11-06 (SvStripC): S2 in Lean — twisted bilinear form, diagonalization and factorization (level 1)

Lean: `RamanujanTau/SvStripC/` (`Defs`, `Prod`, `Ident`, `Holo`, `Main`; 609 lines). No sorry, no new axiom,
no native_decide, no Deligne. All 11 headlines print `[propext, Classical.choice, Quot.sound]`.

    nice -n 10 lake build RamanujanTau.SvStripC.Main      # exit 0

**Stable definitions (`Defs.lean`, imported by `SvStripD`).** Put `s = 1−iz` and `tw z m = m^{iz}`.
* `Fz z m = (fR(m)/m) m^{iz}` and its Dirichlet inverse `Fiz z m = Fi(m) m^{iz}`.
* `Gz z d v₁ v₂ = v₂^{−iz} U^{[s]}(v₁v₂,d)`.
* **`Γz z d u₁ u₂ = Σ_{v₁|u₁,v₂|u₂} α(v₁)α(v₂) Gz z d v₁ v₂ · Fiz z (u₁/v₁) · Fi(u₂/v₂)`**.
* The local factor `γz z p e i j = Σ_{a≤i,b≤j} α(p^a)α(p^b)(p^{−iz})^b L^{[s]}_p(a+b,e) Fi(p^{i−a})(p^{iz})^{i−a} Fi(p^{j−b})`.
* `xz y z P = Σ_{ac=P} β(a)β(c)c^{−iz}`.
* `SvBil y z = Σ_{P,Q≤y²} xz(P)xz(Q) K^{[s]}(P,Q)`.
* `Yd y z d = Σ_{n₁,n₂≤y} β(n₁)β(n₂) Gz z d n₁ n₂`.
* `YdJ y z d = (log y)^{−2} Σ_{u₁,u₂≤y} Γz z d u₁ u₂ J_z(y/u₁) J_0(y/u₂)`. This is literally the expression in
  `SvStripB.yd_bound_div` with `Γ = Γz z d`.

**Theorems.**
* **`Γz_eq_prod`**: `Γz z d u₁ u₂ = Π_{p∈S} γz z p (v_p d)(v_p u₁)(v_p u₂)` for `d,u₁,u₂ ≠ 0` and
  `S ⊇` the primes of `u₁u₂d`. This is the twisted copy of `QFProof4.Γc_eq_prod`.
* **`SvC_eq_SvBil`** (all `z`): `𝒮(z) = Σ_{P,Q} x_z(P)x_z(Q)K^{[1−iz]}(P,Q)`. The term identity `term_eq` is
  `κ e_z = β(a)β(c)c^{−iz}·β(d)β(b)b^{−iz}·[P,Q]^{−s}`, which uses `[P,Q] = P₁bd`.
* **`SvBil_diag`** (`Im z > −1`): `SvBil = Σ_{d≤y²} W^{[s]}(d) Yd²`.
* **`qFactorC`**: `α(n₁)α(n₂)Gz(n₁,n₂) = Σ_{u|n} Γz(u₁,u₂)F_z(n₁/u₁)F(n₂/u₂)`. It rests on `FizA_mul_FzA`: twisting by
  the completely multiplicative `m^{iz}` preserves `Fi ∗ F = 1`.
* **`Yd_eq_YdJ`** (`y ≥ 2`).
* **`SvC_eq_diag`** (`y ≥ 2`, `Im z > −1`): **`𝒮(z) = Σ_{d≤y²} W^{[1−iz]}(d)·YdJ(y,z,d)²`**.
* **`diff_Γz`, `diff_YdJ`**: holomorphy on `Im z > −1`.

**How `c^{−iz}` and the `J_0` side work out.** In `Yd` the twist `c^{−iz}` (with `c = n₂`) sits inside `Gz`. Hence the
second variable carries plain `F`/`Fi`, so only `J_0` occurs there, and the whole `z`-dependence on that side is in
`Γz`. In particular:
* `|tw(−z) p| = p^{Im z}`;
* `|tw z p| = p^{−Im z}`;
* `|x_p| = p^{−1−Im z}`.

Since `Im z ∈ [−δ₀, 0]`, the `S4` local mass `Σ_{i,j}|γz|` differs from the real `QFProof4.γl` only by factors
`p^{O(δ₀)(i+j+e)}`.

**Remaining for `SvCBound`:**
* S4 (`SvStripD`): `Σ_{d≤y²}|W^{[s]}(d)| (Σ_{u₁,u₂≤y}|Γz z d u₁ u₂|)² ≪ y^{O(t)} log y`.
* S5: combine with `yd_bound_div` and `SvC_eq_diag`.

Note that `SvStripB.yd_holo` asks for entire `Γ`, but `Γz` is only holomorphic on `Im z > −1`; use `diff_YdJ` instead.
