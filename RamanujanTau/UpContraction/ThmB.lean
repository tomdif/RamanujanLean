/-
# The `U_p` contraction bound (input I1), conditional on the geometric description of `U`

Setting: `K` complete, ultrametric, algebraically closed, `φ : ℤ_[p] →+* K` integral, `p ≥ 5`,
`0 < ‖p‖ < 1`. `E = Eh φ hp5` is `E_{p−1}` as a polynomial in `(E₄, E₆)`, test objects are
good-reduction Weierstrass curves (`IsTest`), and weight-0 Katz series `Σ b_i / E^i` are evaluated at
`pt W = (c₄(W), −c₆(W))` (`kval`). The Katz pieces are `katzPiece φ (Bz p hp5 0) i` (weight `i(p−1)`).

`Brk W` is the break region `v(E(W)) < p/(p+1)`, i.e. `‖p‖^p < ‖E(W)‖^{p+1}`.

The geometric `U` (Katz 3.11, Vonk Thm B): on a test curve `W`,
`p · U f(W) = Σ_{C ≠ H} f(W/C, π̌^*ω)`, the sum over the `p` order-`p` subgroups other than the
canonical one. It enters here through a family `Q W : Fin p → WeierstrassCurve K` (the `p` non-canonical
quotients) and two hypotheses:
* `QuotHyp` (Buzzard 3.3(v) on curves): for `W` test in the break region, every `Q W c` is a test curve
  with `‖E(Q W c)‖^p = ‖E(W)‖`. (Formal-group form: `QuotientHasse.hasse_quot_noncanonical`;
  see `UpContraction/Transport.lean` for the reduction of `QuotHyp` to that theorem.)
* `hU` (the q-expansion principle for `U_p`): the Katz expansion `a` of `p·U f` (obtained from
  coefficient extraction `U_p` on q-expansions) satisfies `kval E a (pt W) = Σ_c f(Q W c)` on the break
  region.

Results:
* `norm_sum_le_one`, `pointwise_bound`, `pointwise_bound_div` — deliverable (a).
* **`thmB`** — Vonk Thm B: `f ∈ B_E(r)` (`gnorm b_i ≤ ‖r‖^i`) and `‖p‖ < ‖r‖^{p+1}` give
  `p·U f ∈ B_E(r^p)` (`gnorm a_i ≤ ‖r‖^{p i}`).
* **`UB`** — the coefficient bound (UB): for `b ∈ B_j` with `gnorm b ≤ 1` and
  `U(b/E^j) = Σ a_i/E^i` with `ℚ_p`-rational coefficients, every coefficient satisfies
  `‖a_{ij}‖ ≤ ‖p‖^{u(i,j)}`, `u(i,j) = ⌈(pi − j)/(p+1)⌉ − 1` = `AtkinOBrien.u p i j`.
-/
import RamanujanTau.Igusa.Unconditional
import RamanujanTau.AtkinOBrien.Envelope

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UpContraction
open KatzForms Igusa MvPolynomial Filter Topology

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-! ### (a) The pointwise bound -/

/-- Ultrametric: a finite sum of values of norm `≤ 1` has norm `≤ 1`. -/
theorem norm_sum_le_one {ι : Type*} (s : Finset ι) (g : ι → K) (h : ∀ c ∈ s, ‖g c‖ ≤ 1) :
    ‖∑ c ∈ s, g c‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one h

/-- **Pointwise bound** (deliverable (a)). If `f = Σ b_i/E^i ∈ B_E(r)` and the quotient curves `Q c`
are test curves with `‖E(Q c)‖^n = ‖E(W)‖ ≥ ‖r‖^n`, then `‖Σ_c f(Q c)‖ ≤ 1`. -/
theorem pointwise_bound [CompleteSpace K] (E : MvPolynomial (Fin 2) K)
    (b : ℕ → MvPolynomial (Fin 2) K) {r : K} (hr0 : 0 < ‖r‖) (hcoef : ∀ i, gnorm (b i) ≤ ‖r‖ ^ i)
    {n : ℕ} (hn : n ≠ 0) {ι : Type*} (s : Finset ι) (W : WeierstrassCurve K)
    (Q : ι → WeierstrassCurve K) (hrW : ‖r‖ ^ n ≤ ‖eval (pt W) E‖)
    (hQ : ∀ c ∈ s, IsTest (Q c) ∧ ‖eval (pt (Q c)) E‖ ^ n = ‖eval (pt W) E‖) :
    ‖∑ c ∈ s, kval E b (pt (Q c))‖ ≤ 1 := by
  refine norm_sum_le_one s _ fun c hc => ?_
  obtain ⟨hT, hE⟩ := hQ c hc
  have hle : ‖r‖ ≤ ‖eval (pt (Q c)) E‖ := by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hn, hE]; exact hrW
  exact katz_easy E b hr0 hcoef hT hle

/-- The same bound for `U f = (1/p) Σ_c f(Q c)`: `‖U f(W)‖ ≤ ‖p‖⁻¹`. -/
theorem pointwise_bound_div [CompleteSpace K] (E : MvPolynomial (Fin 2) K)
    (b : ℕ → MvPolynomial (Fin 2) K) {r : K} (hr0 : 0 < ‖r‖) (hcoef : ∀ i, gnorm (b i) ≤ ‖r‖ ^ i)
    {n : ℕ} (hn : n ≠ 0) {ι : Type*} (s : Finset ι) (W : WeierstrassCurve K)
    (Q : ι → WeierstrassCurve K) (hrW : ‖r‖ ^ n ≤ ‖eval (pt W) E‖)
    (hQ : ∀ c ∈ s, IsTest (Q c) ∧ ‖eval (pt (Q c)) E‖ ^ n = ‖eval (pt W) E‖) (m : ℕ) :
    ‖(m : K)⁻¹ * ∑ c ∈ s, kval E b (pt (Q c))‖ ≤ ‖(m : K)‖⁻¹ := by
  rw [norm_mul, norm_inv]
  calc ‖(m : K)‖⁻¹ * ‖∑ c ∈ s, kval E b (pt (Q c))‖ ≤ ‖(m : K)‖⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (pointwise_bound E b hr0 hcoef hn s W Q hrW hQ)
          (inv_nonneg.mpr (norm_nonneg _))
    _ = _ := mul_one _

/-! ### (b) Vonk Thm B, conditional on the geometric description of `U` -/

section ThmB
variable {p : ℕ} [hp : Fact p.Prime]

/-- The break region `v(E(W)) < p/(p+1)`. -/
def Brk (p : ℕ) (E : MvPolynomial (Fin 2) K) (W : WeierstrassCurve K) : Prop :=
  ‖(p : K)‖ ^ p < ‖eval (pt W) E‖ ^ (p + 1)

/-- **Buzzard 3.3(v) on curves** (hypothesis): on the break region, the `p` non-canonical quotients
`Q W c` are test curves with `‖E(Q W c)‖^p = ‖E(W)‖`, i.e. `v(E(W/C)) = v(E(W))/p`. -/
def QuotHyp (p : ℕ) (E : MvPolynomial (Fin 2) K) (Q : WeierstrassCurve K → Fin p → WeierstrassCurve K) :
    Prop :=
  ∀ W, IsTest W → Brk p E W → ∀ c, IsTest (Q W c) ∧ ‖eval (pt (Q W c)) E‖ ^ p = ‖eval (pt W) E‖

/-- `‖r‖^p ≤ ‖E(W)‖` with `‖p‖ < ‖r‖^{p+1}` lies in the break region. -/
lemma brk_of_le (E : MvPolynomial (Fin 2) K) {r : K} (hr : ‖(p : K)‖ < ‖r‖ ^ (p + 1))
    {W : WeierstrassCurve K} (hW : ‖r‖ ^ p ≤ ‖eval (pt W) E‖) : Brk p E W := by
  unfold Brk
  have hp0 : p ≠ 0 := hp.out.ne_zero
  calc ‖(p : K)‖ ^ p < (‖r‖ ^ (p + 1)) ^ p := pow_lt_pow_left₀ hr (norm_nonneg _) hp0
    _ = (‖r‖ ^ p) ^ (p + 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ ‖eval (pt W) E‖ ^ (p + 1) := pow_le_pow_left₀ (pow_nonneg (norm_nonneg _) _) hW _

/-- **Vonk Thm B** (conditional on `QuotHyp` and the q-expansion principle `hU` for `U`).
Let `‖p‖ < ‖r‖^{p+1} < 1` (i.e. `0 < v(r) < 1/(p+1)`), `f = Σ b_i/E^i ∈ B_E(r)`, and let `a` be the Katz
expansion of `p·U f` (coefficients in the Katz pieces, convergent on `{‖E‖ ≥ ‖r‖^p}`). Then
`p·U f ∈ B_E(r^p)`: `gnorm a_i ≤ (‖r‖^p)^i`. -/
theorem thmB [CompleteSpace K] [IsAlgClosed K] (φ : ℤ_[p] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hpK : ‖(p : K)‖ < 1) (hp5 : 5 ≤ p)
    (Q : WeierstrassCurve K → Fin p → WeierstrassCurve K) (hQ : QuotHyp p (Eh φ hp5) Q)
    (r : K) (hr : ‖(p : K)‖ < ‖r‖ ^ (p + 1)) (hr1 : ‖r‖ < 1)
    (b : ℕ → MvPolynomial (Fin 2) K) (hb : ∀ i, gnorm (b i) ≤ ‖r‖ ^ i)
    (a : ℕ → MvPolynomial (Fin 2) K) (haB : ∀ i, a i ∈ katzPiece φ (Bz p hp5 0) i)
    (hdec : Tendsto (fun i => gnorm (a i) / ‖r ^ p‖ ^ i) atTop (𝓝 0))
    (hU : ∀ W, IsTest W → Brk p (Eh φ hp5) W →
      kval (Eh φ hp5) a (pt W) = ∑ c, kval (Eh φ hp5) b (pt (Q W c))) :
    ∀ i, gnorm (a i) ≤ ‖r ^ p‖ ^ i := by
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hr0 : 0 < ‖r‖ := by
    by_contra h
    have h0 : ‖r‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [h0, zero_pow (Nat.succ_ne_zero _)] at hr
    exact absurd hr (not_lt.mpr (norm_nonneg _))
  have hrp0 : 0 < ‖r ^ p‖ := by rw [norm_pow]; exact pow_pos hr0 _
  have hrp1 : ‖r ^ p‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hr1 hp0
  refine (katz_iff_hasse' φ hφ hpK hp5 0 (r ^ p) hrp0 hrp1 a haB hdec).mpr ?_
  intro W hW hrW
  rw [norm_pow] at hrW
  rw [hU W hW (brk_of_le _ hr hrW)]
  exact pointwise_bound _ b hr0 hb hp0 Finset.univ W (Q W) hrW fun c _ =>
    hQ W hW (brk_of_le _ hr hrW) c

end ThmB

/-! ### From Thm B to the coefficient bound (UB) -/

section UB

lemma gnorm_C_mul_le (c : K) (P : MvPolynomial (Fin 2) K) : gnorm (C c * P) ≤ ‖c‖ * gnorm P :=
  gnorm_le (mul_nonneg (norm_nonneg _) (gnorm_nonneg _)) fun d => by
    rw [coeff_C_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_coeff_le_gnorm P d) (norm_nonneg _)

/-- Integer core of the radius limit: if `m·x ≤ N·k` whenever `0 < m` and `m·P < N`, then
`x ≤ k·P`. -/
lemma int_radius {x k P : ℤ} (hP : 0 < P)
    (h : ∀ m N : ℕ, 0 < m → (m : ℤ) * P < N → (m : ℤ) * x ≤ N * k) : x ≤ k * P := by
  by_contra hc
  push Not at hc
  set m : ℕ := k.toNat + 1
  have hm : (m : ℤ) = k.toNat + 1 := by simp [m]
  have hkm : k < m := by rw [hm]; have := Int.self_le_toNat k; omega
  have hm0 : 0 < m := Nat.succ_pos _
  have := h m (m * P.toNat + 1) hm0 (by
    have : (P.toNat : ℤ) = P := Int.toNat_of_nonneg hP.le
    push_cast; rw [this]; omega)
  have hPn : (P.toNat : ℤ) = P := Int.toNat_of_nonneg hP.le
  push_cast at this
  rw [hPn] at this
  have h1 : (1 : ℤ) ≤ x - k * P := by omega
  have h2 : (m : ℤ) * (x - k * P) ≥ m := by nlinarith
  nlinarith

/-- The ceiling form: `x ≤ (n+1)(p+1)` gives `⌈x/(p+1)⌉ − 1 ≤ n`. -/
lemma ceil_le_of (p : ℕ) (i j : ℕ) (n : ℤ) (h : ((p : ℤ) * i - j) ≤ (n + 1) * (p + 1)) :
    AtkinOBrien.u p i j ≤ n := by
  unfold AtkinOBrien.u
  have hle : ⌈((p : ℚ) * i - j) / (p + 1)⌉ ≤ n + 1 := by
    rw [Int.ceil_le, div_le_iff₀ (by positivity)]
    exact_mod_cast h
  omega

/-- `ℚ_p`-rational coefficients have norms in `‖p‖^ℤ`. -/
lemma norm_disc {p : ℕ} [hp : Fact p.Prime] (φ : ℤ_[p] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hε : 0 < ‖(p : K)‖) (x : ℤ_[p]) (k : ℕ) :
    φ x / (p : K) ^ k = 0 ∨ ∃ n : ℤ, ‖φ x / (p : K) ^ k‖ = ‖(p : K)‖ ^ n := by
  by_cases hx : x = 0
  · left; simp [hx]
  right
  refine ⟨(x.valuation : ℤ) - k, ?_⟩
  have hu : ‖φ (PadicInt.unitCoeff hx : ℤ_[p])‖ = 1 :=
    norm_phi_unit φ hφ (Units.isUnit _)
  have hε' : ‖(p : K)‖ ≠ 0 := hε.ne'
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [map_mul, map_pow, map_natCast, norm_div, norm_mul, hu, one_mul, norm_pow, norm_pow,
    zpow_sub₀ hε', zpow_natCast, zpow_natCast]

variable {p : ℕ} [hp : Fact p.Prime]

/-- **(UB)**, conditional on `QuotHyp` and the q-expansion principle for `U_p`.

Let `b ∈ B_j ⊗ K` with `gnorm b ≤ 1`, and let `U(b/E^j) = Σ_i a_i/E^i` be the Katz expansion of
`U(b/E^j)`:
* `haB`: `a_i ∈ B_i ⊗ K`;
* `hrat`: the coefficients are `ℚ_p`-rational (`φ x / p^k`);
* `hdec`: the expansion converges on every region `{‖E‖ ≥ ‖s‖}` with `v(s) < p/(p+1)`;
* `hU`: on the break region, `p·U(b/E^j)(W) = Σ_{c} (b/E^j)(Q W c)`.

Then every coefficient satisfies `‖(a_i)_d‖ ≤ ‖p‖^{u(i,j)}`, i.e. `v(a_{ij}) ≥ ⌈(pi−j)/(p+1)⌉ − 1`. -/
theorem UB [CompleteSpace K] [IsAlgClosed K] (φ : ℤ_[p] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hε : 0 < ‖(p : K)‖) (hpK : ‖(p : K)‖ < 1) (hp5 : 5 ≤ p)
    (Q : WeierstrassCurve K → Fin p → WeierstrassCurve K) (hQ : QuotHyp p (Eh φ hp5) Q)
    (j : ℕ) (bj : MvPolynomial (Fin 2) K) (hbj : gnorm bj ≤ 1)
    (a : ℕ → MvPolynomial (Fin 2) K) (haB : ∀ i, a i ∈ katzPiece φ (Bz p hp5 0) i)
    (hrat : ∀ i d, ∃ (x : ℤ_[p]) (k : ℕ), (a i).coeff d = φ x / (p : K) ^ k)
    (hdec : ∀ s : K, ‖(p : K)‖ ^ p < ‖s‖ ^ (p + 1) → ‖s‖ < 1 →
      Tendsto (fun i => gnorm (a i) / ‖s‖ ^ i) atTop (𝓝 0))
    (hU : ∀ W, IsTest W → Brk p (Eh φ hp5) W →
      (p : K) * kval (Eh φ hp5) a (pt W) =
        ∑ c, eval (pt (Q W c)) bj / eval (pt (Q W c)) (Eh φ hp5) ^ j) :
    ∀ i d, ‖(a i).coeff d‖ ≤ ‖(p : K)‖ ^ AtkinOBrien.u p i j := by
  intro i d
  set E := Eh φ hp5
  set t := ‖(p : K)‖ with ht
  have hp0 : p ≠ 0 := hp.out.ne_zero
  obtain ⟨x, k, hxk⟩ := hrat i d
  rcases norm_disc φ hφ hε x k with h0 | ⟨n, hn⟩
  · rw [hxk, h0, norm_zero]; exact zpow_nonneg (norm_nonneg _) _
  rw [hxk, hn]
  rw [← hxk] at hn
  refine (zpow_le_zpow_iff_right_of_lt_one₀ hε hpK).mpr ?_
  refine ceil_le_of p i j n ?_
  refine int_radius (by positivity) fun m N hm hmN => ?_
  -- the radius `r` with `r^N = p^m`, `v(r) = m/N < 1/(p+1)`
  have hN : 0 < N := by
    have : (0 : ℤ) < N := lt_of_le_of_lt (by positivity) hmN
    exact_mod_cast this
  obtain ⟨r, hrN⟩ := IsAlgClosed.exists_pow_nat_eq ((p : K) ^ m) hN
  have hrN' : ‖r‖ ^ N = t ^ m := by rw [← norm_pow, hrN, norm_pow]
  have hr0 : 0 < ‖r‖ := by
    rcases (norm_nonneg r).eq_or_lt with h | h
    · rw [← h, zero_pow hN.ne'] at hrN'
      exact absurd hrN'.symm (pow_ne_zero _ hε.ne')
    · exact h
  have hr1 : ‖r‖ < 1 := by
    have : ‖r‖ ^ N < 1 := by rw [hrN']; exact pow_lt_one₀ hε.le hpK hm.ne'
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hN.ne').mp this
  have hmN' : m * (p + 1) < N := by exact_mod_cast hmN
  have hr : t < ‖r‖ ^ (p + 1) := by
    have : t ^ N < (‖r‖ ^ (p + 1)) ^ N := by
      rw [← pow_mul, mul_comm, pow_mul, hrN', ← pow_mul]
      exact pow_lt_pow_right_of_lt_one₀ hε hpK hmN'
    exact (pow_lt_pow_iff_left₀ hε.le (pow_nonneg (norm_nonneg _) _) hN.ne').mp this
  -- apply Thm B to `f = r^j b / E^j`
  set b' : ℕ → MvPolynomial (Fin 2) K := fun l => if l = j then C (r ^ j) * bj else 0
  set a' : ℕ → MvPolynomial (Fin 2) K := fun l => C ((p : K) * r ^ j) * a l
  have hb' : ∀ l, gnorm (b' l) ≤ ‖r‖ ^ l := by
    intro l
    simp only [b']
    split_ifs with hl
    · subst hl
      refine (gnorm_C_mul_le _ _).trans ?_
      rw [norm_pow]
      calc ‖r‖ ^ l * gnorm bj ≤ ‖r‖ ^ l * 1 :=
            mul_le_mul_of_nonneg_left hbj (pow_nonneg (norm_nonneg _) _)
        _ = _ := mul_one _
    · rw [gnorm_zero]; exact pow_nonneg (norm_nonneg _) _
  have haB' : ∀ l, a' l ∈ katzPiece φ (Bz p hp5 0) l := fun l => by
    simp only [a']; rw [C_mul']; exact Submodule.smul_mem _ _ (haB l)
  have hs : ‖(p : K)‖ ^ p < ‖r ^ p‖ ^ (p + 1) := by
    rw [norm_pow, ← pow_mul, mul_comm, pow_mul]
    exact pow_lt_pow_left₀ hr hε.le hp0
  have hsp : ‖r ^ p‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hr1 hp0
  have hdec' : Tendsto (fun l => gnorm (a' l) / ‖r ^ p‖ ^ l) atTop (𝓝 0) := by
    have h := (hdec (r ^ p) hs hsp).const_mul ‖(p : K) * r ^ j‖
    rw [mul_zero] at h
    refine squeeze_zero (fun l => div_nonneg (gnorm_nonneg _) (pow_nonneg (norm_nonneg _) _))
      (fun l => ?_) h
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (gnorm_C_mul_le _ _) (pow_nonneg (norm_nonneg _) _)
  have hU' : ∀ W, IsTest W → Brk p E W → kval E a' (pt W) = ∑ c, kval E b' (pt (Q W c)) := by
    intro W hW hB
    have hl : kval E a' (pt W) = r ^ j * ((p : K) * kval E a (pt W)) := by
      simp only [kval, a', map_mul, eval_C]
      rw [← tsum_mul_left, ← tsum_mul_left]
      congr 1; ext l; ring
    have hr' : ∀ c, kval E b' (pt (Q W c)) =
        r ^ j * (eval (pt (Q W c)) bj / eval (pt (Q W c)) E ^ j) := by
      intro c
      simp only [kval, b']
      rw [tsum_eq_single j]
      · simp only [↓reduceIte, map_mul, eval_C]; ring
      · intro l hl; simp [if_neg hl]
    rw [hl, hU W hW hB, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => (hr' c).symm
  have hB := thmB φ hφ hpK hp5 Q hQ r hr hr1 b' hb' a' haB' hdec' hU' i
  -- extract the coefficient bound
  have hcoef : ‖(a' i).coeff d‖ ≤ ‖r ^ p‖ ^ i := (norm_coeff_le_gnorm _ _).trans hB
  simp only [a', coeff_C_mul, norm_mul, norm_pow] at hcoef
  rw [hn] at hcoef
  -- `t · ‖r‖^j · t^n ≤ ‖r‖^{p i}`; raise to the `N`-th power
  have hpow := pow_le_pow_left₀ (by positivity) hcoef N
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul] at hpow
  -- rewrite powers of `‖r‖` via `‖r‖^N = t^m`
  have e1 : ‖r‖ ^ (j * N) = t ^ (m * j) := by rw [mul_comm j N, pow_mul, hrN', ← pow_mul]
  have e2 : ‖r‖ ^ (p * (i * N)) = t ^ (m * (p * i)) := by
    rw [show p * (i * N) = N * (p * i) by ring, pow_mul, hrN', ← pow_mul]
  rw [e1, e2] at hpow
  have hz : t ^ ((N : ℤ) + (m * j : ℕ) + n * N) ≤ t ^ ((m * (p * i) : ℕ) : ℤ) := by
    rw [zpow_add₀ hε.ne', zpow_add₀ hε.ne', zpow_natCast, zpow_natCast, zpow_natCast,
      zpow_mul, zpow_natCast]
    exact hpow
  have := (zpow_le_zpow_iff_right_of_lt_one₀ hε hpK).mp hz
  push_cast at this
  nlinarith

end UB

end UpContraction
