/-
# Rationality of the Kloosterman L-function, and Weil's bound from a Stepanov-type bound

Over a finite field `F` with `q` elements, a primitive additive character `ψ`, and `a, b ≠ 0`:

* `kloosterman_L_rational`: with `L(T) = Σ_n A_n T^n`, `A_n = Σ_{deg f = n monic} λ(f)`:
  `A₀ = 1`, `A₁ = K₁`, `A₂ = q`, `A_n = 0` (`n ≥ 3`), i.e. `L(T) = 1 + K₁T + qT²`, and
  `n A_n = Σ_{k=1}^n K_k A_{n-k}` with `K_k` the Kloosterman sum over any extension of degree `k`
  (coefficient form of `T L'/L = Σ_k K_k T^k`, equivalently `exp(Σ K_r T^r / r) = 1 + K₁T + qT²`).
* `klL_eq_neg_pow_add`: `K_r = −(α^r + β^r)` where `α + β = −K₁`, `αβ = q`.
* `weilPrimeBound_of_stepanov`: the named hypothesis `StepanovKloosterman`
  (`|K_r(1,b;p)| ≤ C p^{r/2}` over `GaloisField p r`) implies `WeilKloosterman.WeilPrimeBound`.
-/
import RamanujanTau.KloostermanL.Roots
import RamanujanTau.KloostermanL.Amplify
import RamanujanTau.WeilKloosterman.Main

set_option autoImplicit false

namespace RamanujanTau.KloostermanL

open Polynomial Finset
open scoped Classical

section General

variable {F : Type*} [Field F] [Fintype F] (ψ : AddChar F ℂ) (a b : F)

theorem vM_one : vM ψ a b 1 = klF ψ a b := by
  have h := newton_identity ψ a b 1
  simp only [Nat.cast_one, one_mul, Icc_self, sum_singleton, Nat.sub_self, degSum_zero,
    mul_one] at h
  rw [← h, degSum_one]

theorem vM_two (hψ : ψ.IsPrimitive) (ha : a ≠ 0) (hb : b ≠ 0) :
    vM ψ a b 2 = 2 * (Fintype.card F : ℂ) - klF ψ a b ^ 2 := by
  have h := newton_identity ψ a b 2
  have hI : Icc 1 2 = {1, 2} := by decide
  rw [hI, sum_insert (by decide), sum_singleton, degSum_two ψ a b hψ ha hb] at h
  simp only [Nat.reduceSub, degSum_zero, degSum_one, vM_one, mul_one] at h
  push_cast at h
  linear_combination -h

/-- The three-term recurrence `K_n = −K₁ K_{n−1} − q K_{n−2}` (`n ≥ 3`). -/
theorem vM_recurrence (hψ : ψ.IsPrimitive) (ha : a ≠ 0) (hb : b ≠ 0) {n : ℕ} (hn : 3 ≤ n) :
    vM ψ a b n = -(klF ψ a b * vM ψ a b (n - 1)) - Fintype.card F * vM ψ a b (n - 2) := by
  have hψ1 : ψ ≠ 1 := fun h => hψ (one_ne_zero (α := F)) (by rw [h]; ext x; simp)
  have h := newton_identity ψ a b n
  rw [degSum_eq_zero ψ a b hψ1 ha hn, mul_zero] at h
  have hsub : ({n - 2, n - 1, n} : Finset ℕ) ⊆ Icc 1 n := by
    intro k hk; simp only [mem_insert, mem_singleton] at hk; rw [mem_Icc]; omega
  rw [← sum_subset hsub (fun k hk hk' => by
    have : 3 ≤ n - k := by
      simp only [mem_insert, mem_singleton, not_or] at hk'; rw [mem_Icc] at hk; omega
    rw [degSum_eq_zero ψ a b hψ1 ha this, mul_zero])] at h
  rw [sum_insert (by simp only [mem_insert, mem_singleton]; omega),
    sum_insert (by simp only [mem_singleton]; omega), sum_singleton] at h
  rw [show n - (n - 2) = 2 by omega, show n - (n - 1) = 1 by omega, Nat.sub_self,
    degSum_two ψ a b hψ ha hb, degSum_one, degSum_zero] at h
  linear_combination -h

/-- **Rationality, root form.** If `α + β = −K₁` and `αβ = q`, then `V_r = −(α^r+β^r)`, `r ≥ 1`. -/
theorem vM_eq_neg_pow_add (hψ : ψ.IsPrimitive) (ha : a ≠ 0) (hb : b ≠ 0) {α β : ℂ}
    (hs : α + β = -klF ψ a b) (hp : α * β = Fintype.card F) :
    ∀ r : ℕ, 1 ≤ r → vM ψ a b r = -(α ^ r + β ^ r) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    rcases (show r = 1 ∨ r = 2 ∨ 3 ≤ r by omega) with rfl | rfl | h3
    · rw [vM_one]; linear_combination hs
    · rw [vM_two ψ a b hψ ha hb]; linear_combination (α + β - klF ψ a b) * hs - 2 * hp
    · rw [vM_recurrence ψ a b hψ ha hb h3, ih (r - 1) (by omega) (by omega),
        ih (r - 2) (by omega) (by omega)]
      have e1 : α ^ r = α * α ^ (r - 1) := by rw [← pow_succ']; congr 1; omega
      have e2 : β ^ r = β * β ^ (r - 1) := by rw [← pow_succ']; congr 1; omega
      have e3 : α ^ (r - 1) = α * α ^ (r - 2) := by rw [← pow_succ']; congr 1; omega
      have e4 : β ^ (r - 1) = β * β ^ (r - 2) := by rw [← pow_succ']; congr 1; omega
      rw [e1, e2, e3, e4]
      linear_combination (α * α ^ (r - 2) + β * β ^ (r - 2)) * hs - (α ^ (r - 2) + β ^ (r - 2)) * hp

/-- The two "Frobenius eigenvalues" exist: roots of `X² + K₁X + q`. -/
theorem exists_frobenius_roots (K q : ℂ) : ∃ α β : ℂ, α + β = -K ∧ α * β = q := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (K ^ 2 - 4 * q) (n := 2) (by norm_num)
  exact ⟨(-K + s) / 2, (-K - s) / 2, by ring, by linear_combination (-1 / 4 : ℂ) * hs⟩

variable {L : Type*} [Field L] [Fintype L] [Algebra F L]

/-- **Rationality of the Kloosterman L-function** (all four facts together). -/
theorem kloosterman_L_rational (hψ : ψ.IsPrimitive) (ha : a ≠ 0) (hb : b ≠ 0) :
    degSum ψ a b 0 = 1 ∧ degSum ψ a b 1 = klF ψ a b ∧
    degSum ψ a b 2 = Fintype.card F ∧ (∀ n, 3 ≤ n → degSum ψ a b n = 0) ∧
    (∀ n : ℕ, (n : ℂ) * degSum ψ a b n = ∑ k ∈ Icc 1 n, vM ψ a b k * degSum ψ a b (n - k)) ∧
    (∀ (L : Type) [Field L] [Fintype L] [Algebra F L], 1 ≤ Module.finrank F L →
      vM ψ a b (Module.finrank F L) = klL L ψ a b) := by
  have hψ1 : ψ ≠ 1 := fun h => hψ (one_ne_zero (α := F)) (by rw [h]; ext x; simp)
  exact ⟨degSum_zero ψ a b, degSum_one ψ a b, degSum_two ψ a b hψ ha hb,
    fun n hn => degSum_eq_zero ψ a b hψ1 ha hn, newton_identity ψ a b,
    fun L _ _ _ hk => vM_eq_klL ψ a b hk⟩

/-- **`K_r = −(α^r + β^r)`** for the Kloosterman sum over any extension `L` of degree `r ≥ 1`,
where `α + β = −K₁` and `αβ = q`. -/
theorem klL_eq_neg_pow_add (hψ : ψ.IsPrimitive) (ha : a ≠ 0) (hb : b ≠ 0) {α β : ℂ}
    (hs : α + β = -klF ψ a b) (hp : α * β = Fintype.card F)
    (hk : 1 ≤ Module.finrank F L) :
    klL L ψ a b = -(α ^ Module.finrank F L + β ^ Module.finrank F L) := by
  rw [← vM_eq_klL ψ a b hk, vM_eq_neg_pow_add ψ a b hψ ha hb hs hp _ hk]

end General

/-! ### Prime fields: `GaloisField p r` and `kl p 1 b` -/

section Prime

variable (p : ℕ) [Fact p.Prime]

/-- `K_r(a,b;p) = Σ_{x ∈ F_{p^r}^×} ψ(Tr(ax + b/x))`, `ψ = ZMod.stdAddChar`. -/
noncomputable def klGF (r : ℕ) (a b : ZMod p) : ℂ :=
  letI : Fintype (GaloisField p r) := Fintype.ofFinite _
  klL (GaloisField p r) ZMod.stdAddChar a b

/-- `klGF` does not depend on the chosen `Fintype` instance. -/
theorem klGF_def (r : ℕ) (a b : ZMod p) [Fintype (GaloisField p r)] :
    klGF p r a b = klL (GaloisField p r) ZMod.stdAddChar a b := by
  unfold klGF
  convert rfl

theorem klF_eq_kl (a b : ZMod p) : klF ZMod.stdAddChar a b = TauBound.kl p a b := by
  unfold klF TauBound.kl
  convert rfl

/-- **Rationality over `F_p`.** For `b ≠ 0` there are `α, β` with `α + β = −S(1,b;p)`,
`αβ = p`, and `K_r(1,b;p) = −(α^r + β^r)` for every `r ≥ 1`. -/
theorem klGF_eq_neg_pow_add {b : ZMod p} (hb : b ≠ 0) :
    ∃ α β : ℂ, α + β = -TauBound.kl p 1 b ∧ α * β = p ∧
      ∀ r : ℕ, 1 ≤ r → klGF p r 1 b = -(α ^ r + β ^ r) := by
  obtain ⟨α, β, hs, hp⟩ := exists_frobenius_roots (TauBound.kl p 1 b) p
  refine ⟨α, β, hs, hp, fun r hr => ?_⟩
  letI : Fintype (GaloisField p r) := Fintype.ofFinite _
  have hfr : Module.finrank (ZMod p) (GaloisField p r) = r := GaloisField.finrank p (by omega)
  have := klL_eq_neg_pow_add (L := GaloisField p r) ZMod.stdAddChar 1 b
    (ZMod.isPrimitive_stdAddChar p) one_ne_zero hb (α := α) (β := β)
    (by rw [klF_eq_kl]; exact hs) (by rw [ZMod.card]; exact hp) (by omega)
  rw [hfr] at this
  unfold klGF
  convert this

end Prime

/-! ### The Stepanov-type hypothesis and amplification -/

/-- **Stepanov-type bound** (named hypothesis, the target of the Stepanov track):
`|K_r(1,b;p)| ≤ C p^{r/2}` for all primes `p`, all `r ≥ 1`, all `b ≢ 0`, with one constant `C`. -/
def StepanovKloosterman : Prop :=
  ∃ C : ℝ, ∀ (p : ℕ) (hp : p.Prime), haveI : Fact p.Prime := ⟨hp⟩
    ∀ r : ℕ, 1 ≤ r → ∀ b : ZMod p, b ≠ 0 → ‖klGF p r 1 b‖ ≤ C * Real.sqrt p ^ r

/-- A weaker form, which already suffices: for each `p` and `b ≢ 0`, some constant `C` and
threshold `r₀` (both allowed to depend on `p, b`) with `|K_r(1,b;p)| ≤ C p^{r/2}` for `r ≥ r₀`. -/
def StepanovKloostermanEventually : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), haveI : Fact p.Prime := ⟨hp⟩
    ∀ b : ZMod p, b ≠ 0 → ∃ (C : ℝ) (r₀ : ℕ), ∀ r : ℕ, r₀ ≤ r →
      ‖klGF p r 1 b‖ ≤ C * Real.sqrt p ^ r

theorem stepanovKloostermanEventually_of_stepanov (h : StepanovKloosterman) :
    StepanovKloostermanEventually := by
  obtain ⟨C, hC⟩ := h
  intro p hp b hb
  exact ⟨C, 1, fun r hr => hC p hp r hr b hb⟩

/-- **Weil's bound from the eventual Stepanov bound** (rationality + amplification). -/
theorem weilPrimeBound_of_stepanovEventually (h : StepanovKloostermanEventually) :
    WeilKloosterman.WeilPrimeBound := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  intro b hb
  obtain ⟨C, r₀, hC⟩ := h p hp b hb
  obtain ⟨α, β, hs, hαβ, hK⟩ := klGF_eq_neg_pow_add p hb
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hamp := norm_add_le_two_sqrt_of_powSum_bound (α := α) (β := β) (C := C) hp0
    (by rw [hαβ]; push_cast; rfl) (max r₀ 1) (fun r hr => by
      have := hC r (le_of_max_le_left hr)
      rwa [hK r (le_of_max_le_right hr), norm_neg] at this)
  have : TauBound.kl p 1 b = -(α + β) := by rw [hs, neg_neg]
  rw [this, norm_neg]
  exact hamp.2.2

/-- **`weilPrimeBound_of_stepanov`**: `StepanovKloosterman → WeilPrimeBound`. -/
theorem weilPrimeBound_of_stepanov (h : StepanovKloosterman) : WeilKloosterman.WeilPrimeBound :=
  weilPrimeBound_of_stepanovEventually (stepanovKloostermanEventually_of_stepanov h)

/-- `StepanovKloosterman → τ(n) = O(n^{23/4+ε})`. -/
theorem tau_isBigO_23_4_of_stepanov (h : StepanovKloosterman) (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (RamanujanTau.tau n : ℝ)) =O[Filter.atTop]
      fun n => (n : ℝ) ^ ((23 / 4 : ℝ) + ε) :=
  WeilKloosterman.tau_isBigO_23_4_of_weil (weilPrimeBound_of_stepanov h) ε hε

end RamanujanTau.KloostermanL

#print axioms RamanujanTau.KloostermanL.norm_add_le_two_sqrt_of_powSum_bound
#print axioms RamanujanTau.KloostermanL.lam_mul
#print axioms RamanujanTau.KloostermanL.newton_identity
#print axioms RamanujanTau.KloostermanL.vM_eq_klL
#print axioms RamanujanTau.KloostermanL.kloosterman_L_rational
#print axioms RamanujanTau.KloostermanL.klL_eq_neg_pow_add
#print axioms RamanujanTau.KloostermanL.klGF_eq_neg_pow_add
#print axioms RamanujanTau.KloostermanL.weilPrimeBound_of_stepanovEventually
#print axioms RamanujanTau.KloostermanL.weilPrimeBound_of_stepanov
#print axioms RamanujanTau.KloostermanL.tau_isBigO_23_4_of_stepanov
