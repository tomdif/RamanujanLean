/-
# `QFactor` with the canonical `Γ` (unconditional)

* `recF_unique`: `F(1) = 1`, `F·log = g ∗ F` ⇒ `F = recF g`;
* `recFA_mul`: `recF g₁ ∗ recF g₂ = recF (g₁ + g₂)` (log is a derivation);
* `Fi = divN (recF (−gR))` (`= fR⁻¹/n`, coefficients of `R^{1/2}`), `Fi ∗ F = 1` for `F = fR/n`;
* **`qFactor_canon`**: `QFactor U (Γc U)` for every `U`, with
  `Γc U d u₁ u₂ = Σ_{v₁|u₁, v₂|u₂} α(v₁)α(v₂)U(v₁v₂,d) Fi(u₁/v₁) Fi(u₂/v₂)`.
-/
import RamanujanTau.QFProof.Reduction

set_option autoImplicit false

namespace RamanujanTau.QFProof3

open Finset ArithmeticFunction RamanujanTau.QFProof
open RamanujanTau.SelbergDelange3 (recF recFA toA recF_eq recF_zero recF_one recF_log fR gR gR_zero gR_one)
open RamanujanTau.SelbergDelange2 (divN divN_mul divN_apply)
open RamanujanTau.SelbergCoeffs (alpha)

lemma conv_eq' (g : ℕ → ℝ) (h0 : g 0 = 0) (h1 : g 1 = 0) (F : ArithmeticFunction ℝ) {n : ℕ} (hn : n ≠ 0) :
    (toA g h0 * F) n = ∑ d ∈ n.properDivisors, g (n / d) * F d := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal' (f := fun a b => toA g h0 a * F b)]
  rw [← Nat.insert_self_properDivisors hn, sum_insert Nat.self_notMem_properDivisors]
  simp only [toA, coe_mk, Nat.div_self (Nat.pos_of_ne_zero hn), h1, zero_mul, zero_add]

theorem recF_unique (g : ℕ → ℝ) (h0 : g 0 = 0) (h1 : g 1 = 0) (F : ArithmeticFunction ℝ)
    (hF1 : F 1 = 1) (hlog : ∀ n : ℕ, 0 < n → F n * Real.log n = (toA g h0 * F) n) (n : ℕ) :
    F n = recF g n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [recF_eq]
    split_ifs with hn0 hn1
    · subst hn0; simp
    · subst hn1; exact hF1
    · have hl : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
      have := hlog n (by omega)
      rw [conv_eq' g h0 h1 F hn0] at this
      rw [eq_div_iff hl, this]
      refine sum_congr rfl fun d hd => ?_
      rw [ih d (Nat.mem_properDivisors.1 hd).2]

/-- `f ↦ f · log`. -/
noncomputable def pLog (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n * Real.log n, by simp⟩

lemma pLog_mul (f h : ArithmeticFunction ℝ) : pLog (f * h) = pLog f * h + f * pLog h := by
  ext n
  simp only [pLog, coe_mk, add_apply, mul_apply, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun x hx => ?_
  have hx' := Nat.mem_divisorsAntidiagonal.1 hx
  have h1 : x.1 ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx))
  have h2 : x.2 ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx))
  rw [← hx'.1, Nat.cast_mul, Real.log_mul (by exact_mod_cast h1) (by exact_mod_cast h2)]
  ring

lemma pLog_recFA (g : ℕ → ℝ) (h0 : g 0 = 0) (h1 : g 1 = 0) :
    pLog (recFA g) = toA g h0 * recFA g := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pLog]
  · exact recF_log g h0 h1 n hn

theorem recFA_mul (g₁ g₂ : ℕ → ℝ) (h₁0 : g₁ 0 = 0) (h₁1 : g₁ 1 = 0) (h₂0 : g₂ 0 = 0) (h₂1 : g₂ 1 = 0) :
    recFA g₁ * recFA g₂ = recFA (fun n => g₁ n + g₂ n) := by
  have hs0 : (fun n => g₁ n + g₂ n) 0 = 0 := by simp [h₁0, h₂0]
  have hs1 : (fun n => g₁ n + g₂ n) 1 = 0 := by simp [h₁1, h₂1]
  ext n
  refine recF_unique _ hs0 hs1 _ ?_ ?_ n
  · rw [mul_apply, Nat.divisorsAntidiagonal_one, sum_singleton]
    simp [recFA, recF_one]
  · intro m hm
    show pLog (recFA g₁ * recFA g₂) m = _
    have : toA (fun n => g₁ n + g₂ n) hs0 = toA g₁ h₁0 + toA g₂ h₂0 := by
      ext k; simp [toA]
    rw [pLog_mul, pLog_recFA g₁ h₁0 h₁1, pLog_recFA g₂ h₂0 h₂1, this]
    have key : toA g₁ h₁0 * recFA g₁ * recFA g₂ + recFA g₁ * (toA g₂ h₂0 * recFA g₂) =
        (toA g₁ h₁0 + toA g₂ h₂0) * (recFA g₁ * recFA g₂) := by ring
    rw [key]

lemma recFA_zero_fun : recFA (fun _ => (0 : ℝ)) = 1 := by
  ext n
  symm
  refine recF_unique _ rfl rfl _ (by simp) (fun m hm => ?_) n
  have : toA (fun _ => (0 : ℝ)) rfl = 0 := by ext; simp [toA]
  rw [this, zero_mul, ArithmeticFunction.zero_apply]
  rcases eq_or_ne m 1 with rfl | h
  · simp
  · simp [ArithmeticFunction.one_apply_ne h]

/-- `gR⁻ = −gR = ΛR/2`. -/
noncomputable def gRm (n : ℕ) : ℝ := -gR n

/-- `Fi = fR⁻¹/n`. -/
noncomputable def Fi : ArithmeticFunction ℝ := divN (recF gRm)

lemma Fi_mul_F : Fi * divN fR = 1 := by
  have hm := recFA_mul gRm gR (by simp [gRm, gR_zero]) (by simp [gRm, gR_one]) gR_zero gR_one
  have hz : (fun n => gRm n + gR n) = fun _ => (0 : ℝ) := by funext n; simp [gRm]
  rw [hz, recFA_zero_fun] at hm
  ext n
  have := divN_mul (recFA gR) (recFA gRm) n
  unfold Fi
  rw [show divN (recF gRm) = divN (recFA gRm) from rfl, show divN fR = divN (recFA gR) from rfl,
    this, hm]
  rcases eq_or_ne n 1 with rfl | h
  · simp
  · rw [ArithmeticFunction.one_apply_ne h, zero_div]

lemma Fm_eq (m : ℕ) : Fm m = divN fR m := rfl

/-- One-variable inversion. -/
lemma one_inv (g : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    ∑ u ∈ n.divisors, (∑ v ∈ u.divisors, g v * Fi (u / v)) * Fm (n / u) = g n := by
  set G : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else g n, by simp⟩ with hG
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (show (G * Fi) * divN fR = G by
    rw [mul_assoc, Fi_mul_F, mul_one])
  simp only at h
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => (G * Fi) a * divN fR b)] at h
  have hGn : G n = g n := by simp [hG, hn.ne']
  rw [← hGn, ← h]
  refine sum_congr rfl fun u hu => ?_
  rw [Fm_eq, mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => G a * Fi b)]
  congr 1
  refine sum_congr rfl fun v hv => ?_
  have : v ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hv)
  simp [hG, this]

/-- Two-variable inversion. -/
lemma two_inv (G : ℕ → ℕ → ℝ) {n₁ n₂ : ℕ} (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    ∑ u₁ ∈ n₁.divisors, ∑ u₂ ∈ n₂.divisors,
      (∑ v₁ ∈ u₁.divisors, ∑ v₂ ∈ u₂.divisors, G v₁ v₂ * Fi (u₁ / v₁) * Fi (u₂ / v₂)) *
        Fm (n₁ / u₁) * Fm (n₂ / u₂) = G n₁ n₂ := by
  have step : ∀ u₁, ∑ u₂ ∈ n₂.divisors,
      (∑ v₁ ∈ u₁.divisors, ∑ v₂ ∈ u₂.divisors, G v₁ v₂ * Fi (u₁ / v₁) * Fi (u₂ / v₂)) *
        Fm (n₁ / u₁) * Fm (n₂ / u₂) =
      (∑ v₁ ∈ u₁.divisors, (∑ u₂ ∈ n₂.divisors,
        (∑ v₂ ∈ u₂.divisors, G v₁ v₂ * Fi (u₂ / v₂)) * Fm (n₂ / u₂)) * Fi (u₁ / v₁)) * Fm (n₁ / u₁) := by
    intro u₁
    simp only [sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun v₁ _ => ?_
    refine sum_congr rfl fun u₂ _ => ?_
    refine sum_congr rfl fun v₂ _ => ?_
    ring
  rw [sum_congr rfl fun u₁ _ => step u₁]
  simp only [one_inv (G _) h₂]
  rw [← one_inv (fun v => G v n₂) h₁]

/-- The canonical `Γ`. -/
noncomputable def Γc (U : ℕ → ℕ → ℝ) (d u₁ u₂ : ℕ) : ℝ :=
  ∑ v₁ ∈ u₁.divisors, ∑ v₂ ∈ u₂.divisors, alpha v₁ * alpha v₂ * U (v₁ * v₂) d * Fi (u₁ / v₁) * Fi (u₂ / v₂)

/-- **`QFactor U (Γc U)`** for every `U`. -/
theorem qFactor_canon (U : ℕ → ℕ → ℝ) : QFactor U (Γc U) := by
  intro d n₁ n₂ h₁ h₂
  unfold Γc
  rw [← two_inv (fun v₁ v₂ => alpha v₁ * alpha v₂ * U (v₁ * v₂) d) h₁ h₂]

end RamanujanTau.QFProof3
