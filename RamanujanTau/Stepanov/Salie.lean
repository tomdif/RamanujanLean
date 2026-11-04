/-
# Salié's bound `|S(1,b;p)| ≪ p^{2/3}` via the sixth moment and Stepanov (genus 1)

* `sum_norm_kl_pow_six`: `∑_{a,b} |S(a,b;p)|⁶ = p² N₆`, `N₆ = ∑_{u,v} M(u,v)²`;
* `∑_{u,v} M(u,v) = (p-1)³` and `∑_{u,v} (M(u,v) - p)² ≤ C₀ p³` (`SalieCount.lean`);
* orbit argument: `(p-1)|S(1,b)|⁶ + (p-1)⁶ ≤ ∑_{a,b}|S(a,b)|⁶`;
* hence `|S(1,b;p)|⁶ ≤ 2 C₀ p⁴` (`p` odd), i.e. `|S(1,b;p)| ≤ (2C₀)^{1/6} p^{2/3}`.
This proves `WeilKloosterman.SaliePrimeBound`, and hence `τ(n) = O(n^{35/6+ε})` unconditionally.
-/
import RamanujanTau.Stepanov.SalieCount
import RamanujanTau.WeilKloosterman.Main

set_option autoImplicit false

namespace RamanujanTau.Stepanov

open Complex Finset RamanujanTau.TauBound Asymptotics Filter
open scoped ComplexConjugate

variable {p : ℕ} [hp : Fact p.Prime]

local notation "F" => ZMod p
local notation "U" => (ZMod p)ˣ
local notation "ψ" => (ZMod.stdAddChar (N := p))

/-- `(x, (y, z)) ↦ x + y + z`. -/
noncomputable def s3 (w : U × (U × U)) : F := (w.1 : F) + sP w.2
/-- `(x, (y, z)) ↦ x⁻¹ + y⁻¹ + z⁻¹`. -/
noncomputable def t3 (w : U × (U × U)) : F := (w.1 : F)⁻¹ + tP w.2

lemma kl_cube (a b : F) :
    kl p a b ^ 3 = ∑ w : U × (U × U), ψ (a * s3 w + b * t3 w) := by
  rw [pow_succ', kl_sq, kl_eq_field, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_congr _ _ (fun w => ?_)
  rw [← AddChar.map_add_eq_mul, s3, t3]
  ring_nf

lemma conj_kl_cube (a b : F) :
    conj (kl p a b ^ 3) = ∑ w : U × (U × U), ψ (-(a * s3 w + b * t3 w)) := by
  rw [kl_cube, map_sum]
  simp only [conj_stdAddChar]

/-- The sixth-moment identity `∑_{a,b} |S(a,b)|⁶ = p² N₆`. -/
theorem sum_norm_kl_pow_six :
    (∑ a : F, ∑ b : F, (‖kl p a b‖ ^ 6 : ℝ) : ℂ) =
      (p : ℂ) ^ 2 * ((univ.filter (fun ww : (U × (U × U)) × (U × (U × U)) =>
        s3 ww.1 = s3 ww.2 ∧ t3 ww.1 = t3 ww.2)).card : ℂ) := by
  have h6 : ∀ a b : F, ((‖kl p a b‖ ^ 6 : ℝ) : ℂ) = kl p a b ^ 3 * conj (kl p a b ^ 3) := by
    intro a b
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow]
    push_cast; ring
  have hterm : ∀ a b : F, kl p a b ^ 3 * conj (kl p a b ^ 3) =
      ∑ ww : (U × (U × U)) × (U × (U × U)),
        ψ (a * (s3 ww.1 - s3 ww.2)) * ψ (b * (t3 ww.1 - t3 ww.2)) := by
    intro a b
    rw [conj_kl_cube, kl_cube, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
    refine Fintype.sum_congr _ _ (fun ww => ?_)
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; ring_nf
  simp_rw [h6, hterm]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm), Finset.sum_comm]
  have hinner : ∀ ww : (U × (U × U)) × (U × (U × U)),
      ∑ a : F, ∑ b : F, ψ (a * (s3 ww.1 - s3 ww.2)) * ψ (b * (t3 ww.1 - t3 ww.2)) =
        if s3 ww.1 = s3 ww.2 ∧ t3 ww.1 = t3 ww.2 then (p : ℂ) ^ 2 else 0 := by
    intro ww
    rw [← Finset.sum_mul_sum, sum_psi_mul, sum_psi_mul]
    simp only [sub_eq_zero]
    split_ifs <;> simp_all [sq]
  simp_rw [hinner]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  ring

/-- `#{(x,y) : g x = g y} = ∑_b #(g⁻¹ b)²`. -/
theorem card_pairs_eq_sum_sq {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (g : α → β) :
    #(univ.filter (fun ww : α × α => g ww.1 = g ww.2)) =
      ∑ y : β, #(univ.filter (fun w => g w = y)) ^ 2 := by
  classical
  rw [card_filter, Fintype.sum_prod_type]
  have h1 : ∀ x : α, (∑ x' : α, if g x = g x' then 1 else 0) =
      #(univ.filter (fun w => g w = g x)) := by
    intro x; rw [card_filter]
    refine Finset.sum_congr rfl fun x' _ => ?_
    by_cases h : g x = g x' <;> simp [h, eq_comm]
  simp_rw [h1]
  rw [← Finset.sum_fiberwise univ g (fun x => #(univ.filter (fun w => g w = g x)))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_congr rfl (fun x hx => by rw [(mem_filter.mp hx).2]), sum_const, smul_eq_mul,
    sq]

theorem card_fibre_eq_M3 (y : F × F) :
    #(univ.filter (fun w : U × (U × U) => (s3 w, t3 w) = y)) = M3 y.1 y.2 := by
  unfold M3
  congr 1
  ext w
  simp only [mem_filter, mem_univ, true_and, Prod.ext_iff]
  rfl

theorem sum_M3 : ∑ y : F × F, (M3 y.1 y.2 : ℝ) = ((p : ℝ) - 1) ^ 3 := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (U × (U × U))))
    (t := (univ : Finset (F × F))) (f := fun w => (s3 w, t3 w)) (fun _ _ => mem_univ _)
  simp only [card_univ, Fintype.card_prod, ZMod.card_units] at h
  have : ∑ y : F × F, (M3 y.1 y.2 : ℝ) = (((p - 1) * ((p - 1) * (p - 1)) : ℕ) : ℝ) := by
    rw [h]; push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← card_fibre_eq_M3]
  rw [this]
  have := hp.out.one_lt
  push_cast [Nat.cast_sub this.le]
  ring

theorem sum_bad_le :
    ∑ y : F × F, (if y.1 = 0 ∨ y.1 * y.2 = 1 then 9 * (p : ℝ) ^ 2 else 0) ≤ 18 * (p : ℝ) ^ 3 := by
  rw [Fintype.sum_prod_type]
  have hrow : ∀ u : F, (∑ v : F, (if u = 0 ∨ u * v = 1 then 9 * (p : ℝ) ^ 2 else 0)) ≤
      9 * (p : ℝ) ^ 2 + (if u = 0 then 9 * (p : ℝ) ^ 3 else 0) := by
    intro u
    by_cases hu : u = 0
    · simp only [hu, true_or, if_true, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
      nlinarith [sq_nonneg (p : ℝ)]
    · simp only [hu, false_or, if_false, add_zero]
      rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
      have : #(univ.filter (fun v : F => u * v = 1)) ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        simp only [mem_filter, mem_univ, true_and] at ha hb
        exact mul_left_cancel₀ hu (ha.trans hb.symm)
      have : (#(univ.filter (fun v : F => u * v = 1)) : ℝ) ≤ 1 := by exact_mod_cast this
      nlinarith [sq_nonneg (p : ℝ)]
  refine (Finset.sum_le_sum fun u _ => hrow u).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' univ (0 : F), if_pos (mem_univ _), sum_const,
    card_univ, ZMod.card, nsmul_eq_mul]
  nlinarith

/-- `∑_{u,v} (M(u,v) - p)² ≤ (196² + 18) p³`. -/
theorem sum_M3_sub_sq_le (hp2 : p ≠ 2) :
    ∑ y : F × F, ((M3 y.1 y.2 : ℝ) - p) ^ 2 ≤ (196 ^ 2 + 18) * (p : ℝ) ^ 3 := by
  have h : ∀ y : F × F, ((M3 y.1 y.2 : ℝ) - p) ^ 2 ≤
      196 ^ 2 * p + (if y.1 = 0 ∨ y.1 * y.2 = 1 then 9 * (p : ℝ) ^ 2 else 0) := by
    intro y
    have := M3_sub_p_sq_le hp2 y.1 y.2
    push_cast at this; exact this
  refine (Finset.sum_le_sum fun y _ => h y).trans ?_
  rw [Finset.sum_add_distrib, sum_const, card_univ, Fintype.card_prod, ZMod.card, nsmul_eq_mul]
  have := sum_bad_le (p := p)
  push_cast
  nlinarith

theorem kl_zero_zero : kl p 0 0 = ((p : ℂ) - 1) := by
  unfold kl
  simp only [zero_mul, add_zero, AddChar.map_zero_eq_one, sum_const, card_univ,
    ZMod.card_units, nsmul_eq_mul, mul_one]
  have := hp.out.one_lt
  push_cast [Nat.cast_sub this.le]
  ring

/-- **Salié's bound, sixth-power form**: `|S(1,b;p)|⁶ ≤ 2(196²+18) p⁴` for odd `p`. -/
theorem norm_kl_prime_pow_six_le (hp2 : p ≠ 2) (b : F) :
    ‖kl p 1 b‖ ^ 6 ≤ 2 * (196 ^ 2 + 18) * (p : ℝ) ^ 4 := by
  have hp2' : 2 ≤ p := hp.out.two_le
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2'
  set Mv : F × F → ℝ := fun y => (M3 y.1 y.2 : ℝ)
  have hid := sum_norm_kl_pow_six (p := p)
  have hN : ((univ.filter (fun ww : (U × (U × U)) × (U × (U × U)) =>
        s3 ww.1 = s3 ww.2 ∧ t3 ww.1 = t3 ww.2)).card : ℝ) = ∑ y : F × F, Mv y ^ 2 := by
    have := card_pairs_eq_sum_sq (fun w : U × (U × U) => (s3 w, t3 w))
    have e : (univ.filter (fun ww : (U × (U × U)) × (U × (U × U)) =>
        s3 ww.1 = s3 ww.2 ∧ t3 ww.1 = t3 ww.2)) =
        univ.filter (fun ww : (U × (U × U)) × (U × (U × U)) =>
          (s3 ww.1, t3 ww.1) = (s3 ww.2, t3 ww.2)) := by
      ext ww; simp [Prod.ext_iff]
    rw [e, this]
    push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [card_fibre_eq_M3]
  have hreal : (∑ a : F, ∑ b : F, ‖kl p a b‖ ^ 6 : ℝ) = (p : ℝ) ^ 2 * ∑ y : F × F, Mv y ^ 2 := by
    rw [← hN]; exact_mod_cast hid
  -- algebra: ∑ M² = ∑ (M-p)² + 2p ∑ M - p⁴
  have hS1 : ∑ y : F × F, Mv y = ((p : ℝ) - 1) ^ 3 := sum_M3
  have hS2 : ∑ y : F × F, Mv y ^ 2 =
      ∑ y : F × F, (Mv y - p) ^ 2 + 2 * p * ∑ y : F × F, Mv y - (p : ℝ) ^ 4 := by
    have : ∀ y : F × F, Mv y ^ 2 = (Mv y - p) ^ 2 + 2 * p * Mv y - (p : ℝ) ^ 2 := by
      intro y; ring
    rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_const, card_univ, Fintype.card_prod, ZMod.card, nsmul_eq_mul]
    push_cast; ring
  have hdev := sum_M3_sub_sq_le hp2
  -- orbit lower bound
  set K := ‖kl p 1 b‖ ^ 6
  have horbit : ∀ a : F, (if a = 0 then ((p : ℝ) - 1) ^ 6 else K) ≤
      ∑ b' : F, ‖kl p a b'‖ ^ 6 := by
    intro a
    split_ifs with ha
    · subst ha
      have := Finset.single_le_sum (f := fun b' => ‖kl p 0 b'‖ ^ 6)
        (fun _ _ => by positivity) (Finset.mem_univ 0)
      simp only at this
      rw [kl_zero_zero] at this
      have e : ‖(p : ℂ) - 1‖ = (p : ℝ) - 1 := by
        have : ((p : ℂ) - 1) = (((p : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      rwa [e] at this
    · have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha
      have hk : kl p a (a⁻¹ * b) = kl p 1 b := by
        have := kl_unit_eq p hu.unit (a⁻¹ * b)
        simp only [IsUnit.unit_spec] at this
        rw [this, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
      have := Finset.single_le_sum (f := fun b' => ‖kl p a b'‖ ^ 6)
        (fun _ _ => by positivity) (Finset.mem_univ (a⁻¹ * b))
      simp only at this
      rwa [hk] at this
  have hsumG : (∑ a : F, (if a = 0 then ((p : ℝ) - 1) ^ 6 else K)) =
      ((p : ℝ) - 1) ^ 6 + ((p : ℝ) - 1) * K := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have h0 : (univ.filter (fun a : F => a = 0)).card = 1 := by
      rw [Finset.filter_eq']; simp
    have h1 : (univ.filter (fun a : F => ¬ a = 0)).card = p - 1 := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
      simp [ZMod.card, Finset.filter_eq']
    rw [h0, h1]; push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring
  have hlow : ((p : ℝ) - 1) ^ 6 + ((p : ℝ) - 1) * K ≤ (p : ℝ) ^ 2 * ∑ y : F × F, Mv y ^ 2 := by
    rw [← hsumG, ← hreal]
    exact Finset.sum_le_sum fun a _ => horbit a
  rw [hS2, hS1] at hlow
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hK0 : 0 ≤ K := by positivity
  -- (p-1) K ≤ p² ∑(M-p)² - (p³ - (p-1)³)² ≤ C₀ p⁵
  have hK1 : ((p : ℝ) - 1) * K ≤ (196 ^ 2 + 18) * (p : ℝ) ^ 5 := by
    have hsq : 0 ≤ ((p : ℝ) ^ 3 - ((p : ℝ) - 1) ^ 3) ^ 2 := sq_nonneg _
    nlinarith
  have hp1' : (p : ℝ) ≤ 2 * ((p : ℝ) - 1) := by linarith
  have : ((p : ℝ) - 1) * K ≤ ((p : ℝ) - 1) * (2 * (196 ^ 2 + 18) * (p : ℝ) ^ 4) := by
    have : (196 ^ 2 + 18) * (p : ℝ) ^ 5 ≤ ((p : ℝ) - 1) * (2 * (196 ^ 2 + 18) * (p : ℝ) ^ 4) := by
      have h4 : (0 : ℝ) ≤ (p : ℝ) ^ 4 := by positivity
      nlinarith
    linarith
  exact le_of_mul_le_mul_left this hp1

theorem norm_kl_le_card (a b : F) : ‖kl p a b‖ ≤ (p : ℝ) := by
  unfold kl
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_stdAddChar, sum_const, card_univ, ZMod.card_units, nsmul_eq_mul, mul_one]
  have := hp.out.one_lt
  push_cast [Nat.cast_sub this.le]
  linarith

end RamanujanTau.Stepanov

namespace RamanujanTau.Stepanov
open RamanujanTau.TauBound RamanujanTau.WeilKloosterman Asymptotics Filter

/-- **Salié's bound (1931/32)**, proved: `WeilKloosterman.SaliePrimeBound`. -/
theorem saliePrimeBound : SaliePrimeBound := by
  set D : ℝ := 2 * (196 ^ 2 + 18)
  refine ⟨max (D ^ ((1 : ℝ) / 6)) 2, fun p hp => ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  intro b _
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have hD : 0 ≤ D := by norm_num [D]
  by_cases hp2 : p = 2
  · subst hp2
    have h := norm_kl_le_card (p := 2) 1 b
    have h23 : (1 : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) / 3) := Real.one_le_rpow (by norm_num) (by norm_num)
    have : (2 : ℝ) ≤ max (D ^ ((1 : ℝ) / 6)) 2 * (2 : ℝ) ^ ((2 : ℝ) / 3) := by
      have := le_max_right (D ^ ((1 : ℝ) / 6)) 2
      nlinarith
    push_cast at h
    linarith
  · have h6 := norm_kl_prime_pow_six_le hp2 b
    have hpow : (D ^ ((1 : ℝ) / 6) * (p : ℝ) ^ ((2 : ℝ) / 3)) ^ 6 = D * (p : ℝ) ^ 4 := by
      rw [mul_pow, ← Real.rpow_natCast (D ^ ((1 : ℝ) / 6)), ← Real.rpow_mul hD,
        ← Real.rpow_natCast ((p : ℝ) ^ ((2 : ℝ) / 3)), ← Real.rpow_mul hp0]
      norm_num
    have hle : ‖kl p 1 b‖ ≤ D ^ ((1 : ℝ) / 6) * (p : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num : (6 : ℕ) ≠ 0),
        hpow]
      exact h6
    refine hle.trans ?_
    gcongr
    exact le_max_left _ _

/-- **`τ(n) = O(n^{35/6+ε})` unconditionally** (Salié exponent). -/
theorem tau_isBigO_35_6_unconditional (ε : ℝ) (hε : 0 < ε) :
    (fun n : ℕ => (tau n : ℝ)) =O[atTop] fun n => (n : ℝ) ^ ((35 / 6 : ℝ) + ε) :=
  tau_isBigO_35_6_of_salie saliePrimeBound ε hε

end RamanujanTau.Stepanov

#print axioms RamanujanTau.Stepanov.norm_kl_prime_pow_six_le
#print axioms RamanujanTau.Stepanov.saliePrimeBound
#print axioms RamanujanTau.Stepanov.tau_isBigO_35_6_unconditional
