/-
# Item (a)+(b): the uniform twisted Rankin asymptotic

For coprime `h, k ≥ 1` (`twisted_asymp`):

    Σ_{r≤N} λ(hr)λ(kr)/r = r₀ρ(h)ρ(k) log N + K₁(h,k) + O(E N^{−1/5}),
    K₁ = γ_Δ ρ(h)ρ(k) + r₀(ρ₁(h)ρ(k) + ρ(h)ρ₁(k)),

with `E + |r₀ρρ| + |K₁| ≤ Z₀ (hk)⁴` uniformly. Proof: induction on the prime factorisation of `hk`.
Peeling `p^a ∥ h` writes `λ(hr)λ(kr) = Σ_{p^j∣r} g_j λ(h'r/p^j)λ(kr/p^j)` with `g = U_{p,a}/D_p`
(`T_peel`, Hecke multiplicativity and `g·D = U`), and `peel_asymp` applies with
`G = ρ_p(a)`, `G₁ = −ρ_p'(a)` (`Gg_gseq`, `G1g_gseq`). The base case is `GoodSecondTerm.AA_asymp`.
The constant: `5S ≤ P₀ p^{4a}` for `p < P₀` and `≤ p^{4a}` for `p ≥ P₀`, so the small primes cost a
fixed factor `P₀^{P₀}`.
-/
import RamanujanTau.HafnerBridge2.Eval

set_option autoImplicit false

namespace RamanujanTau.HafnerBridge2

open Finset PowerSeries
open RamanujanTau.HafnerBridge

/-- `T_{h,k}(r) = λ(hr)λ(kr)`. -/
noncomputable def T (h k r : ℕ) : ℝ := lam (h * r) * lam (k * r)

noncomputable def cT (h k : ℕ) : ℝ := r0 * (rho h * rho k)

noncomputable def KT (h k : ℕ) : ℝ :=
  RamanujanTau.GoodSecondTerm.gammaD * (rho h * rho k) + r0 * (rho1 h * rho k + rho h * rho1 k)

def TwAsym (h k : ℕ) (E : ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → |Asum (T h k) N - cT h k * Real.log N - KT h k| ≤ E * (N : ℝ) ^ (-(1 / 5 : ℝ))

/-! ### `ρ`, `ρ₁` under peeling a prime power -/

lemma rho_one : rho 1 = 1 := by simp [rho]

lemma rho1_one : rho1 1 = 0 := by simp [rho1]

lemma pf_peel {p a m : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hm : 1 ≤ m) :
    (p ^ a * m).primeFactors = insert p m.primeFactors := by
  rw [Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) (by omega), Nat.primeFactors_prime_pow (by omega) hp]
  rfl

lemma fact_peel_p {p a m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) (hpm : ¬ p ∣ m) :
    (p ^ a * m).factorization p = a := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (by omega), Finsupp.add_apply, hp.factorization_pow,
    Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hpm, add_zero]

lemma fact_peel_q {p a m q : ℕ} (hp : p.Prime) (hm : 1 ≤ m) (hq : q ≠ p) :
    (p ^ a * m).factorization q = m.factorization q := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (by omega), Finsupp.add_apply, hp.factorization_pow,
    Finsupp.single_apply, if_neg (Ne.symm hq), zero_add]

lemma p_notMem {p m : ℕ} (hpm : ¬ p ∣ m) : p ∉ m.primeFactors := fun h => hpm (Nat.dvd_of_mem_primeFactors h)

lemma rho_peel {p a m : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hm : 1 ≤ m) (hpm : ¬ p ∣ m) :
    rho (p ^ a * m) = rhoP p a * rho m := by
  unfold rho
  rw [pf_peel hp ha hm, Finset.prod_insert (p_notMem hpm), fact_peel_p hp hm hpm]
  refine congrArg _ (Finset.prod_congr rfl fun q hq => ?_)
  rw [fact_peel_q hp hm (fun h => p_notMem hpm (h ▸ hq))]

lemma rho1_peel {p a m : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hm : 1 ≤ m) (hpm : ¬ p ∣ m) :
    rho1 (p ^ a * m) = rhoP' p a * rho m + rhoP p a * rho1 m := by
  unfold rho1 rho
  rw [pf_peel hp ha hm, Finset.sum_insert (p_notMem hpm), fact_peel_p hp hm hpm,
    Finset.erase_insert (p_notMem hpm)]
  have hP : ∏ q ∈ m.primeFactors, rhoP q ((p ^ a * m).factorization q) =
      ∏ q ∈ m.primeFactors, rhoP q (m.factorization q) :=
    Finset.prod_congr rfl fun q hq => by rw [fact_peel_q hp hm (fun h => p_notMem hpm (h ▸ hq))]
  rw [hP]
  refine congrArg _ ?_
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hqp : q ≠ p := fun h => p_notMem hpm (h ▸ hq)
    rw [fact_peel_q hp hm hqp, Finset.erase_insert_of_ne (Ne.symm hqp),
      Finset.prod_insert (fun h => p_notMem hpm (Finset.mem_of_mem_erase h)), fact_peel_p hp hm hpm]
    have : ∀ q' ∈ m.primeFactors.erase q, rhoP q' ((p ^ a * m).factorization q') =
        rhoP q' (m.factorization q') := by
      intro q' hq'
      rw [fact_peel_q hp hm (fun h => p_notMem hpm (h ▸ Finset.mem_of_mem_erase hq'))]
    rw [Finset.prod_congr rfl this]
    ring

/-! ### The peeling identity for `T` -/

lemma coprime_pow_of_not_dvd {p i m : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) : (p ^ i).Coprime m :=
  Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)

lemma T_pow_mul {p h' k i r' : ℕ} (hp : p.Prime) (hph : ¬ p ∣ h') (hpk : ¬ p ∣ k) (hpr : ¬ p ∣ r') :
    T h' k (p ^ i * r') = lam (p ^ i) ^ 2 * T h' k r' := by
  unfold T
  have e1 : h' * (p ^ i * r') = p ^ i * (h' * r') := by ring
  have e2 : k * (p ^ i * r') = p ^ i * (k * r') := by ring
  rw [e1, e2, lam_mul_coprime (coprime_pow_of_not_dvd hp (fun h => (Nat.Prime.dvd_mul hp).mp h |>.elim hph hpr)),
    lam_mul_coprime (coprime_pow_of_not_dvd hp (fun h => (Nat.Prime.dvd_mul hp).mp h |>.elim hpk hpr))]
  ring

lemma T_peel {p a h' k : ℕ} (hp : p.Prime) (hph : ¬ p ∣ h') (hpk : ¬ p ∣ k) {r : ℕ} (hr : 1 ≤ r) :
    T (p ^ a * h') k r = conv p (gseq p a) (T h' k) r := by
  set J := r.factorization p with hJ
  set r' := r / p ^ J with hr'
  have hr0 : r ≠ 0 := by omega
  have hrr : p ^ J * r' = r := Nat.ordProj_mul_ordCompl_eq_self r p
  have hpr : ¬ p ∣ r' := Nat.not_dvd_ordCompl hp hr0
  -- LHS
  have hL : T (p ^ a * h') k r = lam (p ^ (J + a)) * lam (p ^ J) * T h' k r' := by
    unfold T
    rw [← hrr]
    have e1 : p ^ a * h' * (p ^ J * r') = p ^ (J + a) * (h' * r') := by ring
    have e2 : k * (p ^ J * r') = p ^ J * (k * r') := by ring
    rw [e1, e2, lam_mul_coprime (coprime_pow_of_not_dvd hp (fun h => (Nat.Prime.dvd_mul hp).mp h |>.elim hph hpr)),
      lam_mul_coprime (coprime_pow_of_not_dvd hp (fun h => (Nat.Prime.dvd_mul hp).mp h |>.elim hpk hpr))]
    ring
  -- RHS
  have hJr : J + 1 ≤ r + 1 := by
    have h1 : p ^ J ≤ r := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd r p)
    have h2 : J < p ^ J := Nat.lt_pow_self hp.one_lt
    omega
  have hR : conv p (gseq p a) (T h' k) r = ∑ j ∈ range (J + 1), gseq p a j * (lam (p ^ (J - j)) ^ 2 * T h' k r') := by
    unfold conv
    rw [← Finset.sum_subset (range_subset_range.mpr hJr) (fun j hj hj' => ?_)]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [mem_range] at hj
      have hd : p ^ j ∣ r := (hp.pow_dvd_iff_le_factorization hr0).mpr (by omega)
      rw [if_pos hd]
      have : r / p ^ j = p ^ (J - j) * r' := by
        have e : r = p ^ j * (p ^ (J - j) * r') := by
          rw [← hrr, ← mul_assoc, ← pow_add, show j + (J - j) = J by omega]
        rw [e, Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
      rw [this, T_pow_mul hp hph hpk hpr]
    · rw [mem_range] at hj'
      rw [if_neg]
      intro hd
      have := (hp.pow_dvd_iff_le_factorization hr0).mp hd
      omega
  rw [hL, hR]
  have hc := congrArg (coeff J) (gps_mul_Dps p a)
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i l => coeff i (gps p a) * coeff l (Dps p))] at hc
  simp only [Ups, Dps, coeff_mk] at hc
  rw [← hc, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [gseq]; ring

/-! ### The induction -/

lemma TwAsym_swap {h k : ℕ} {E : ℝ} (hT : TwAsym h k E) : TwAsym k h E := by
  intro N hN
  have e1 : Asum (T k h) N = Asum (T h k) N := by
    unfold Asum T; refine Finset.sum_congr rfl fun r _ => by ring
  have e2 : cT k h = cT h k := by unfold cT; ring
  have e3 : KT k h = KT h k := by unfold KT; ring
  rw [e1, e2, e3]; exact hT N hN

lemma TwAsym_base : ∃ E, 0 ≤ E ∧ TwAsym 1 1 E := by
  obtain ⟨C, hC0, hC⟩ := RamanujanTau.GoodSecondTerm.AA_asymp
  refine ⟨C, hC0, fun N hN => ?_⟩
  have e1 : Asum (T 1 1) N = RamanujanTau.GoodSecondTerm.AA N := by
    unfold Asum T RamanujanTau.GoodSecondTerm.AA
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [mem_Icc] at hr
    rw [one_mul, ← sq, lam_sq_eq_bb hr.1]
  have e2 : cT 1 1 = RamanujanTau.GoodSecondTerm.c0 := by unfold cT r0; simp [rho_one]
  have e3 : KT 1 1 = RamanujanTau.GoodSecondTerm.gammaD := by unfold KT; simp [rho_one, rho1_one]
  rw [e1, e2, e3]; exact hC N hN

section
variable {C : ℝ} (hC1 : 1 ≤ C) (hC : ∀ n : ℕ, 1 ≤ n → |lam n| ≤ C * (n : ℝ) ^ (11 / 40 : ℝ))
include hC1 hC

/-- One peeling step, with the constant. -/
lemma TwAsym_peel {p a h' k : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hh' : 1 ≤ h') (hk : 1 ≤ k)
    (hph : ¬ p ∣ h') (hpk : ¬ p ∣ k) {E : ℝ} (hE : 0 ≤ E) (hT : TwAsym h' k E) :
    ∃ E', 0 ≤ E' ∧ TwAsym (p ^ a * h') k E' ∧
      E' + |cT (p ^ a * h') k| + |KT (p ^ a * h') k| ≤
        5 * Sg p (gseq p a) * (E + |cT h' k| + |KT h' k|) := by
  have hS := summable_Sg hC1 hC hp ha
  have hS0 := Sg_nonneg p hp.two_le (gseq p a)
  have hG := Gg_gseq hC1 hC hp a
  have hG1 := G1g_gseq hC1 hC hp a
  have hcT : cT (p ^ a * h') k = cT h' k * Gg p (gseq p a) := by
    rw [hG]; unfold cT; rw [rho_peel hp ha hh' hph]; ring
  have hKT : KT (p ^ a * h') k = KT h' k * Gg p (gseq p a) - cT h' k * G1g p (gseq p a) := by
    rw [hG, hG1]; unfold KT cT; rw [rho_peel hp ha hh' hph, rho1_peel hp ha hh' hph]; ring
  refine ⟨(2 * E + 3 * |cT h' k| + |KT h' k|) * Sg p (gseq p a),
    mul_nonneg (by have := abs_nonneg (cT h' k); have := abs_nonneg (KT h' k); linarith) hS0,
    fun N hN => ?_, ?_⟩
  · have hA : Asum (T (p ^ a * h') k) N = Asum (conv p (gseq p a) (T h' k)) N := by
      unfold Asum
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [mem_Icc] at hr
      rw [T_peel hp hph hpk hr.1]
    rw [hA, hcT, hKT]
    have := peel_asymp hp.two_le hE hT hS N hN
    convert this using 2
  · rw [hcT, hKT]
    have h1 := abs_Gg_le hp.two_le hS
    have h2 := abs_G1g_le hp.two_le hS
    have hc0 := abs_nonneg (cT h' k)
    have hK0 := abs_nonneg (KT h' k)
    have b1 : |cT h' k * Gg p (gseq p a)| ≤ |cT h' k| * Sg p (gseq p a) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 hc0
    have b2 : |KT h' k * Gg p (gseq p a) - cT h' k * G1g p (gseq p a)| ≤
        |KT h' k| * Sg p (gseq p a) + |cT h' k| * Sg p (gseq p a) := by
      refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
      · exact mul_le_mul_of_nonneg_left h1 hK0
      · exact mul_le_mul_of_nonneg_left h2 hc0
    nlinarith [mul_nonneg hE hS0, mul_nonneg hc0 hS0, mul_nonneg hK0 hS0]

/-- The prime threshold `P₀ ≥ 30 C⁴ W₀`. -/
noncomputable def P0 (C : ℝ) : ℕ := ⌈30 * C ^ 4 * W0⌉₊ + 1

omit hC1 hC in
lemma one_le_P0 (C : ℝ) : 1 ≤ P0 C := by unfold P0; omega

/-- `5S ≤ (P₀ or 1) p^{4a}`. -/
lemma fiveS_le {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    5 * Sg p (gseq p a) ≤ (if p < P0 C then (P0 C : ℝ) else 1) * (p : ℝ) ^ (4 * a) := by
  have hS := Sg_le hC1 hC hp ha
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hW : 30 * C ^ 4 * W0 ≤ P0 C := by
    unfold P0; push_cast; have := Nat.le_ceil (30 * C ^ 4 * W0); linarith
  have hpa : (p : ℝ) ^ (3 * a) ≥ 0 := by positivity
  have e4 : (p : ℝ) ^ (4 * a) = (p : ℝ) ^ (3 * a) * (p : ℝ) ^ a := by rw [← pow_add]; ring_nf
  have hpa1 : (1 : ℝ) ≤ (p : ℝ) ^ a := one_le_pow₀ hp1
  have hpap : (p : ℝ) ≤ (p : ℝ) ^ a := by
    calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (p : ℝ) ^ a := pow_le_pow_right₀ hp1 ha
  split_ifs with hlt
  · rw [e4]
    calc 5 * Sg p (gseq p a) ≤ 5 * (6 * C ^ 4 * W0 * (p : ℝ) ^ (3 * a)) := by linarith
      _ = (30 * C ^ 4 * W0) * (p : ℝ) ^ (3 * a) := by ring
      _ ≤ (P0 C : ℝ) * ((p : ℝ) ^ (3 * a) * 1) := by rw [mul_one]; gcongr
      _ ≤ (P0 C : ℝ) * ((p : ℝ) ^ (3 * a) * (p : ℝ) ^ a) := by gcongr
  · push Not at hlt
    have hpP : (P0 C : ℝ) ≤ p := by exact_mod_cast hlt
    rw [e4, one_mul]
    calc 5 * Sg p (gseq p a) ≤ 5 * (6 * C ^ 4 * W0 * (p : ℝ) ^ (3 * a)) := by linarith
      _ = (30 * C ^ 4 * W0) * (p : ℝ) ^ (3 * a) := by ring
      _ ≤ (p : ℝ) * (p : ℝ) ^ (3 * a) := by gcongr; linarith
      _ ≤ (p : ℝ) ^ a * (p : ℝ) ^ (3 * a) := by gcongr
      _ = _ := by ring

/-- The bound invariant. -/
def Inv (C Z₀ : ℝ) (h k : ℕ) : Prop :=
  ∃ E, 0 ≤ E ∧ TwAsym h k E ∧
    E + |cT h k| + |KT h k| ≤
      Z₀ * (P0 C : ℝ) ^ ((h * k).primeFactors.filter (fun q => q < P0 C)).card * ((h * k : ℕ) : ℝ) ^ 4

omit hC1 hC in
lemma Inv_swap {Z₀ : ℝ} {h k : ℕ} (hI : Inv C Z₀ h k) : Inv C Z₀ k h := by
  obtain ⟨E, hE, hT, hb⟩ := hI
  refine ⟨E, hE, TwAsym_swap hT, ?_⟩
  have e2 : cT k h = cT h k := by unfold cT; ring
  have e3 : KT k h = KT h k := by unfold KT; ring
  rw [e2, e3, mul_comm k h]; exact hb

lemma Inv_peel {Z₀ : ℝ} (hZ₀ : 0 ≤ Z₀) {p a h' k : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hh' : 1 ≤ h') (hk : 1 ≤ k)
    (hph : ¬ p ∣ h') (hpk : ¬ p ∣ k) (hI : Inv C Z₀ h' k) : Inv C Z₀ (p ^ a * h') k := by
  obtain ⟨E, hE, hT, hb⟩ := hI
  obtain ⟨E', hE', hT', hb'⟩ := TwAsym_peel hC1 hC hp ha hh' hk hph hpk hE hT
  refine ⟨E', hE', hT', ?_⟩
  have h5 := fiveS_le hC1 hC hp ha
  have hpk' : ¬ p ∣ h' * k := fun h => (Nat.Prime.dvd_mul hp).mp h |>.elim hph hpk
  have hpf : (p ^ a * h' * k).primeFactors = insert p (h' * k).primeFactors := by
    rw [mul_assoc]; exact pf_peel hp ha (Nat.mul_pos hh' hk)
  have hcard : ((p ^ a * h' * k).primeFactors.filter (fun q => q < P0 C)).card =
      (if p < P0 C then 1 else 0) + ((h' * k).primeFactors.filter (fun q => q < P0 C)).card := by
    rw [hpf, Finset.filter_insert]
    split_ifs with hlt
    · rw [Finset.card_insert_of_notMem (fun h => p_notMem hpk' (Finset.mem_of_mem_filter _ h))]; ring
    · simp
  set c' := ((h' * k).primeFactors.filter (fun q => q < P0 C)).card
  have hP1 : (1 : ℝ) ≤ P0 C := by exact_mod_cast one_le_P0 C
  have hS0 := Sg_nonneg p hp.two_le (gseq p a)
  have hZ : 0 ≤ E + |cT h' k| + |KT h' k| := by positivity
  have hmul : ((p ^ a * h' * k : ℕ) : ℝ) ^ 4 = (p : ℝ) ^ (4 * a) * ((h' * k : ℕ) : ℝ) ^ 4 := by
    push_cast; ring
  rw [hcard, hmul]
  calc E' + |cT (p ^ a * h') k| + |KT (p ^ a * h') k| ≤ 5 * Sg p (gseq p a) * (E + |cT h' k| + |KT h' k|) := hb'
    _ ≤ ((if p < P0 C then (P0 C : ℝ) else 1) * (p : ℝ) ^ (4 * a)) *
          (Z₀ * (P0 C : ℝ) ^ c' * ((h' * k : ℕ) : ℝ) ^ 4) := mul_le_mul h5 hb hZ (by positivity)
    _ = Z₀ * (P0 C : ℝ) ^ ((if p < P0 C then 1 else 0) + c') * ((p : ℝ) ^ (4 * a) * ((h' * k : ℕ) : ℝ) ^ 4) := by
        split_ifs <;> ring

lemma Inv_all {Z₀ : ℝ} (hZ₀ : 0 ≤ Z₀) (hbase : Inv C Z₀ 1 1) :
    ∀ n h k : ℕ, h * k = n → 1 ≤ h → 1 ≤ k → h.Coprime k → Inv C Z₀ h k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro h k hn hh hk hcop
  -- peeling the smallest prime of `m > 1`, against a coprime `l`
  have peel : ∀ m l : ℕ, 1 < m → 1 ≤ l → m.Coprime l → m * l = n → Inv C Z₀ m l := by
    intro m l hm hl hml hmn
    set p := m.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime (by omega)
    set a := m.factorization p
    set m' := m / p ^ a with hm'def
    have hm0 : m ≠ 0 := by omega
    have hmm : p ^ a * m' = m := Nat.ordProj_mul_ordCompl_eq_self m p
    have hpm' : ¬ p ∣ m' := Nat.not_dvd_ordCompl hp hm0
    have ha : 1 ≤ a := hp.factorization_pos_of_dvd hm0 (Nat.minFac_dvd m)
    have hm'1 : 1 ≤ m' := Nat.ordCompl_pos p hm0
    have hpl : ¬ p ∣ l := fun h => by
      have := Nat.Coprime.coprime_dvd_left (Nat.minFac_dvd m) hml
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd this h)
    have hlt : m' * l < n := by
      rw [← hmn, ← hmm]
      have : 2 ≤ p ^ a := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
      have : 1 ≤ m' * l := Nat.mul_pos hm'1 hl
      nlinarith
    have hcop' : m'.Coprime l := Nat.Coprime.coprime_dvd_left ⟨p ^ a, by rw [← hmm]; ring⟩ hml
    have := Inv_peel hC1 hC hZ₀ hp ha hm'1 hl hpm' hpl (ih (m' * l) hlt m' l rfl hm'1 hl hcop')
    rwa [hmm] at this
  rcases Nat.lt_or_ge 1 h with h1 | h1
  · exact peel h k h1 hk hcop hn
  · have hh1 : h = 1 := by omega
    subst hh1
    rcases Nat.lt_or_ge 1 k with k1 | k1
    · exact Inv_swap (peel k 1 k1 le_rfl (Nat.coprime_one_right k) (by rw [← hn]; ring))
    · have : k = 1 := by omega
      subst this; exact hbase

end

/-- **Item (a)+(b)**: the uniform twisted Rankin asymptotic. -/
theorem twisted_asymp : ∃ Z : ℝ, 0 ≤ Z ∧ ∀ h k : ℕ, 1 ≤ h → 1 ≤ k → h.Coprime k →
    ∃ E, 0 ≤ E ∧ TwAsym h k E ∧ E + |cT h k| + |KT h k| ≤ Z * ((h * k : ℕ) : ℝ) ^ 4 := by
  obtain ⟨C, hC1, hC⟩ := lam_bound
  obtain ⟨E₀, hE₀, hT₀⟩ := TwAsym_base
  set Z₀ := E₀ + |cT 1 1| + |KT 1 1| with hZ₀
  have hZ₀0 : 0 ≤ Z₀ := by positivity
  have hbase : Inv C Z₀ 1 1 := ⟨E₀, hE₀, hT₀, by simp [hZ₀]⟩
  refine ⟨Z₀ * (P0 C : ℝ) ^ (P0 C), by positivity, fun h k hh hk hcop => ?_⟩
  obtain ⟨E, hE, hT, hb⟩ := Inv_all hC1 hC hZ₀0 hbase (h * k) h k rfl hh hk hcop
  refine ⟨E, hE, hT, hb.trans ?_⟩
  have hP1 : (1 : ℝ) ≤ P0 C := by exact_mod_cast one_le_P0 C
  have hcard : ((h * k).primeFactors.filter (fun q => q < P0 C)).card ≤ P0 C := by
    calc _ ≤ (range (P0 C)).card := Finset.card_le_card (fun q hq => by
          rw [Finset.mem_filter] at hq; exact Finset.mem_range.mpr hq.2)
      _ = P0 C := Finset.card_range _
  have := pow_le_pow_right₀ hP1 hcard
  have h4 : 0 ≤ ((h * k : ℕ) : ℝ) ^ 4 := by positivity
  gcongr

end RamanujanTau.HafnerBridge2
