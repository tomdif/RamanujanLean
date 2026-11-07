import RamanujanTau.LehmerSmall.FinalDeep

/-! # `τ(n) mod 23` as a kernel-computable pentagonal double sum

`Δ ≡ q(q;q)_∞(q²³;q²³)_∞ (mod 23)` (Frobenius, as in `TauCong.tau_mod23`). Euler's pentagonal theorem
turns the coefficient of `q^{N+1}` into
`a(N+1) = c(N) + Σ_m (−1)^{m+1} (c(N − 23·plo m) + c(N − 23·phi m))`,
where `plo m = (m+1)(3m+2)/2` and `phi m = (m+1)(3m+4)/2` are the generalized pentagonal numbers.
Here `c(k)` is the coefficient of `qᵏ` in `(q;q)_∞`. In closed form `c(k) = pcfR k (√(24k+1))`:
* `(−1)^{(r+1)/6}` if `24k+1 = r²` with `r ≡ 5 (mod 6)`;
* `(−1)^{(r−1)/6}` if `24k+1 = r²` with `r ≡ 1 (mod 6)`;
* `0` otherwise.

`tau_mod23_formula` states this with a fuel-bounded Newton square root `isq`. The root is not proved correct
in general; each value used is certified by `r² ≤ s < (r+1)²` (`sqOK`), and that check is part of the kernel
computation.
-/

set_option autoImplicit false

namespace RamanujanTau.LehmerSmall
open PowerSeries Finset

/-! ## pentagonal numbers -/

def plo (m : ℕ) : ℕ := (m + 1) * (3 * m + 2) / 2
def phi (m : ℕ) : ℕ := (m + 1) * (3 * m + 4) / 2

lemma two_plo (m : ℕ) : 2 * plo m = (m + 1) * (3 * m + 2) := by
  apply Nat.mul_div_cancel'
  rcases Nat.even_or_odd m with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact ⟨(t + t + 1) * (3 * t + 1), by ring⟩
  · exact ⟨(t + 1) * (3 * (2 * t + 1) + 2), by ring⟩

lemma two_phi (m : ℕ) : 2 * phi m = (m + 1) * (3 * m + 4) := by
  apply Nat.mul_div_cancel'
  rcases Nat.even_or_odd m with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact ⟨(t + t + 1) * (3 * t + 2), by ring⟩
  · exact ⟨(t + 1) * (3 * (2 * t + 1) + 4), by ring⟩

lemma sq_plo (m : ℕ) : 24 * plo m + 1 = (6 * m + 5) * (6 * m + 5) := by
  have h := two_plo m; nlinarith [h]

lemma sq_phi (m : ℕ) : 24 * phi m + 1 = (6 * m + 7) * (6 * m + 7) := by
  have h := two_phi m; nlinarith [h]

lemma plo_strictMono : StrictMono plo := by
  apply strictMono_nat_of_lt_succ
  intro m
  have h1 := sq_plo m; have h2 := sq_plo (m + 1)
  nlinarith

lemma phi_strictMono : StrictMono phi := by
  apply strictMono_nat_of_lt_succ
  intro m
  have h1 := sq_phi m; have h2 := sq_phi (m + 1)
  nlinarith

lemma plo_le_phi (m : ℕ) : plo m ≤ phi m := by
  have h1 := sq_plo m; have h2 := sq_phi m; nlinarith

lemma plo_pos (m : ℕ) : 1 ≤ plo m := by
  have h1 := sq_plo m; nlinarith

lemma lt_plo_self (m : ℕ) : m < plo m := by
  have h1 := sq_plo m; nlinarith

lemma plo_ne_phi (a b : ℕ) : plo a ≠ phi b := by
  intro h
  have h1 := sq_plo a; have h2 := sq_phi b
  rw [h] at h1
  have := Nat.mul_self_inj.mp (h1.symm.trans h2)
  omega

/-! ## the truncated pentagonal series -/

noncomputable def PJ (J : ℕ) : PowerSeries ℤ :=
  1 + ∑ m ∈ range J, (C ((-1 : ℤ) ^ (m + 1)) * X ^ plo m + C ((-1 : ℤ) ^ (m + 1)) * X ^ phi m)

lemma coeff_PJ (J k : ℕ) : coeff k (PJ J) = (if k = 0 then 1 else 0) +
    ∑ m ∈ range J, ((-1 : ℤ) ^ (m + 1) * (if k = plo m then 1 else 0) +
      (-1 : ℤ) ^ (m + 1) * (if k = phi m then 1 else 0)) := by
  simp only [PJ, map_add, map_sum, coeff_C_mul, coeff_X_pow, coeff_one]

/-- The pentagonal coefficient in closed form, given the square root `r` of `24k+1`. -/
def pcfR (k r : ℕ) : ℤ :=
  if r * r = 24 * k + 1 then
    (if r % 6 = 5 then (-1) ^ ((r + 1) / 6) else if r % 6 = 1 then (-1) ^ ((r - 1) / 6) else 0)
  else 0

lemma sum_single_plo {J k m : ℕ} (hm : plo m = k) (hmJ : m < J) :
    ∑ b ∈ range J, (-1 : ℤ) ^ (b + 1) * (if k = plo b then 1 else 0) = (-1) ^ (m + 1) := by
  rw [Finset.sum_eq_single m]
  · rw [if_pos hm.symm, mul_one]
  · intro b _ hb
    rw [if_neg (fun h => hb (plo_strictMono.injective (h.symm.trans hm.symm).symm).symm), mul_zero]
  · intro h; exact absurd (mem_range.mpr hmJ) h

lemma sum_single_phi {J k m : ℕ} (hm : phi m = k) (hmJ : m < J) :
    ∑ b ∈ range J, (-1 : ℤ) ^ (b + 1) * (if k = phi b then 1 else 0) = (-1) ^ (m + 1) := by
  rw [Finset.sum_eq_single m]
  · rw [if_pos hm.symm, mul_one]
  · intro b _ hb
    rw [if_neg (fun h => hb (phi_strictMono.injective (h.symm.trans hm.symm).symm).symm), mul_zero]
  · intro h; exact absurd (mem_range.mpr hmJ) h

lemma sum_zero_plo {J k : ℕ} (h : ∀ b, plo b ≠ k) :
    ∑ b ∈ range J, (-1 : ℤ) ^ (b + 1) * (if k = plo b then 1 else 0) = 0 :=
  Finset.sum_eq_zero fun b _ => by rw [if_neg (fun e => h b e.symm), mul_zero]

lemma sum_zero_phi {J k : ℕ} (h : ∀ b, phi b ≠ k) :
    ∑ b ∈ range J, (-1 : ℤ) ^ (b + 1) * (if k = phi b then 1 else 0) = 0 :=
  Finset.sum_eq_zero fun b _ => by rw [if_neg (fun e => h b e.symm), mul_zero]

/-- **Closed form** of the truncated pentagonal coefficients. -/
lemma coeff_PJ_closed {J k : ℕ} (hk : k < plo J) : coeff k (PJ J) = pcfR k (Nat.sqrt (24 * k + 1)) := by
  rw [coeff_PJ, Finset.sum_add_distrib]
  set r := Nat.sqrt (24 * k + 1) with hr
  have hlo_r : ∀ b, plo b = k → r = 6 * b + 5 := by
    intro b hb; rw [hr, ← hb, sq_plo]; exact Nat.sqrt_eq _
  have hphi_r : ∀ b, phi b = k → r = 6 * b + 7 := by
    intro b hb; rw [hr, ← hb, sq_phi]; exact Nat.sqrt_eq _
  have hk0_r : k = 0 → r = 1 := by intro h; rw [hr, h]; rfl
  have hloJ : ∀ b, plo b = k → b < J := by
    intro b hb; by_contra h; push_neg at h; have := plo_strictMono.monotone h; omega
  have hphiJ : ∀ b, phi b = k → b < J := by
    intro b hb; by_contra h; push_neg at h; have := plo_strictMono.monotone h
    have := plo_le_phi b; omega
  by_cases hsq : r * r = 24 * k + 1
  · by_cases h5 : r % 6 = 5
    · set m := (r - 5) / 6
      have hm : r = 6 * m + 5 := by omega
      have hlo : plo m = k := by
        have := sq_plo m; rw [← hm, hsq] at this; omega
      have hk0 : k ≠ 0 := by have := plo_pos m; omega
      rw [if_neg hk0, zero_add, sum_single_plo hlo (hloJ m hlo),
        sum_zero_phi (fun b hb => plo_ne_phi m b (hlo.trans hb.symm)), add_zero, pcfR, if_pos hsq, if_pos h5]
      congr 1; omega
    · by_cases h1 : r % 6 = 1
      · by_cases hr1 : r = 1
        · have hk0 : k = 0 := by rw [hr1] at hsq; omega
          rw [if_pos hk0, sum_zero_plo (fun b hb => by have := plo_pos b; omega),
            sum_zero_phi (fun b hb => by have := plo_pos b; have := plo_le_phi b; omega), pcfR, if_pos hsq,
            if_neg h5, if_pos h1, hr1]
          norm_num
        · set m := (r - 7) / 6
          have hm : r = 6 * m + 7 := by omega
          have hphi : phi m = k := by
            have := sq_phi m; rw [← hm, hsq] at this; omega
          have hk0 : k ≠ 0 := by have := plo_pos m; have := plo_le_phi m; omega
          rw [if_neg hk0, zero_add, sum_single_phi hphi (hphiJ m hphi),
            sum_zero_plo (fun b hb => plo_ne_phi b m (hb.trans hphi.symm)), zero_add, pcfR, if_pos hsq,
            if_neg h5, if_pos h1]
          congr 1; omega
      · have hk0 : k ≠ 0 := fun h => by have := hk0_r h; omega
        rw [if_neg hk0, zero_add, sum_zero_plo (fun b hb => by have := hlo_r b hb; omega),
          sum_zero_phi (fun b hb => by have := hphi_r b hb; omega), pcfR, if_pos hsq, if_neg h5, if_neg h1]
        norm_num
  · have hk0 : k ≠ 0 := fun h => by have := hk0_r h; rw [this, h] at hsq; exact hsq rfl
    rw [if_neg hk0, zero_add,
      sum_zero_plo (fun b hb => by
        have := hlo_r b hb; apply hsq; rw [this, ← hb, sq_plo]),
      sum_zero_phi (fun b hb => by
        have := hphi_r b hb; apply hsq; rw [this, ← hb, sq_phi]), pcfR, if_neg hsq]
    norm_num

lemma sgn_conv (m : ℕ) : MockTheta5.JTP.sgn ((m : ℤ) + 1) = (-1 : ℤ) ^ (m + 1) := by
  rw [MockTheta5.JTP.sgn_succ, MockTheta5.JTP.sgn_natCast, pow_succ]; ring

lemma coeff_XC (i e : ℕ) (c : ℤ) : coeff i (X ^ e * C c) = if i = e then c else 0 := by
  rw [mul_comm, coeff_C_mul, coeff_X_pow]; split_ifs <;> simp

/-- `pentSeries` agrees with `PJ J` below `plo J`. -/
lemma coeff_pent_PJ {J i : ℕ} (hi : i < plo J) : coeff i MockTheta5.JTP.pentSeries = coeff i (PJ J) := by
  rw [MockTheta5.JTP.coeff_pentSeries_lt (M := J + (i + 1)) (by omega),
    MockTheta5.JTP.map_evm1_pentFiniteP, PJ]
  simp only [map_add, map_sum, coeff_one]
  congr 1
  rw [Finset.sum_range_add, Finset.sum_eq_zero (s := range (i + 1)), add_zero]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_XC, coeff_XC, coeff_C_mul, coeff_X_pow, coeff_C_mul, coeff_X_pow, MockTheta5.JTP.sgn_neg,
      sgn_conv]
    simp only [plo, phi]
    split_ifs <;> simp
  · intro x _
    have h1 : plo J ≤ plo (J + x) := plo_strictMono.monotone (Nat.le_add_right J x)
    have h2 := plo_le_phi (J + x)
    rw [show (J + x + 1) * (3 * (J + x) + 2) / 2 = plo (J + x) from rfl,
      show (J + x + 1) * (3 * (J + x) + 4) / 2 = phi (J + x) from rfl, coeff_XC, coeff_XC]
    split_ifs <;> first | omega | ring

/-! ## the coefficient of `Ea a (pent) · pent` -/

lemma Ea_C (a : ℕ) (ha : a ≠ 0) (c : ℤ) : RankProof.Ea a ha (C c) = C c :=
  PowerSeries.expand_C (p := a) (hp := ha) c

lemma coeff_Ea_pent {a N J : ℕ} (ha : a ≠ 0) (hN : N < plo J) :
    coeff N (RankProof.Ea a ha MockTheta5.JTP.pentSeries * MockTheta5.JTP.pentSeries) =
      coeff N (RankProof.Ea a ha (PJ J) * PJ J) := by
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [RankProof.coeff_Ea, RankProof.coeff_Ea, coeff_pent_PJ (J := J) (i := x.2) (by omega)]
  split_ifs with h
  · rw [coeff_pent_PJ (J := J) (by have := Nat.div_le_self x.1 a; omega)]
  · rfl

lemma Ea_Xpow (a : ℕ) (ha : a ≠ 0) (e : ℕ) : RankProof.Ea a ha (X ^ e) = X ^ (a * e) := by
  rw [map_pow, RankProof.Ea_X, ← pow_mul]

lemma coeff_Ea_PJ (a N J : ℕ) (ha : a ≠ 0) :
    coeff N (RankProof.Ea a ha (PJ J) * PJ J) = coeff N (PJ J) +
      ∑ m ∈ range J, (-1 : ℤ) ^ (m + 1) *
        ((if a * plo m ≤ N then coeff (N - a * plo m) (PJ J) else 0) +
          (if a * phi m ≤ N then coeff (N - a * phi m) (PJ J) else 0)) := by
  conv_lhs => rw [show RankProof.Ea a ha (PJ J) = 1 + ∑ m ∈ range J,
      (C ((-1 : ℤ) ^ (m + 1)) * X ^ (a * plo m) + C ((-1 : ℤ) ^ (m + 1)) * X ^ (a * phi m)) by
    rw [PJ, map_add, map_one, map_sum]
    refine congrArg _ (Finset.sum_congr rfl fun m _ => ?_)
    rw [map_add, map_mul, map_mul, Ea_C, Ea_Xpow, Ea_Xpow]]
  rw [add_mul, one_mul, Finset.sum_mul, map_add, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [add_mul, map_add, mul_assoc, mul_assoc, coeff_C_mul, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow_mul']
  ring

/-! ## kernel-computable pieces -/

def isqIter : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | f + 1, n, x => if (x + n / x) / 2 < x then isqIter f n ((x + n / x) / 2) else x

def isq (n : ℕ) : ℕ := isqIter 128 n n

def sqOK (s : ℕ) : Bool := decide (isq s * isq s ≤ s) && decide (s < (isq s + 1) * (isq s + 1))

lemma sqrt_of_sqOK {s : ℕ} (h : sqOK s = true) : Nat.sqrt s = isq s := by
  simp only [sqOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (Nat.eq_sqrt.mpr h).symm

def pc (k : ℕ) : ℤ := pcfR k (isq (24 * k + 1))

def termC (a N m : ℕ) : ℤ :=
  (-1 : ℤ) ^ (m + 1) * ((if a * plo m ≤ N then pc (N - a * plo m) else 0) +
    (if a * phi m ≤ N then pc (N - a * phi m) else 0))

def okC (a N m : ℕ) : Bool :=
  (!(decide (a * plo m ≤ N)) || sqOK (24 * (N - a * plo m) + 1)) &&
    (!(decide (a * phi m ≤ N)) || sqOK (24 * (N - a * phi m) + 1))

def rsum (f : ℕ → ℤ) : ℕ → ℕ → ℤ
  | _, 0 => 0
  | a, n + 1 => f a + rsum f (a + 1) n

def rall (f : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => true
  | a, n + 1 => f a && rall f (a + 1) n

lemma rsum_eq (f : ℕ → ℤ) : ∀ a n, rsum f a n = ∑ i ∈ range n, f (a + i)
  | _, 0 => by simp [rsum]
  | a, n + 1 => by
    rw [rsum, rsum_eq f (a + 1) n, Finset.sum_range_succ']
    simp only [add_zero]; rw [add_comm]; congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [add_assoc, add_comm 1 i]

lemma rall_eq (f : ℕ → Bool) : ∀ a n, rall f a n = true → ∀ i < n, f (a + i) = true
  | _, 0 => by intro _ i hi; omega
  | a, n + 1 => by
    intro h i hi
    simp only [rall, Bool.and_eq_true] at h
    rcases i with _ | i
    · simpa using h.1
    · have := rall_eq f (a + 1) n h.2 i (by omega)
      rwa [show a + 1 + i = a + (i + 1) by omega] at this

lemma rsum_add (f : ℕ → ℤ) (a n m : ℕ) : rsum f a (n + m) = rsum f a n + rsum f (a + n) m := by
  rw [rsum_eq, rsum_eq, rsum_eq, Finset.sum_range_add]
  congr 1; exact Finset.sum_congr rfl fun i _ => by rw [add_assoc]

lemma rall_add (f : ℕ → Bool) (a n m : ℕ) : rall f a (n + m) = (rall f a n && rall f (a + n) m) := by
  induction n generalizing a with
  | zero => simp [rall]
  | succ n ih => rw [show n + 1 + m = (n + m) + 1 by omega, rall, rall, ih, Bool.and_assoc,
      show a + 1 + n = a + (n + 1) by omega]

/-! ## Frobenius: `Δ ≡ η(z)η(23z) (mod 23)` -/

instance fact23 : Fact (Nat.Prime 23) := ⟨by norm_num⟩

lemma tau_mod23_pent (N : ℕ) :
    ((TauCong.tauPS (N + 1) : ℤ) : ZMod 23) =
      ((coeff N (RankProof.Ea (23 ^ 1) (TauCong.ppow_ne 23 1) MockTheta5.JTP.pentSeries *
        MockTheta5.JTP.pentSeries) : ℤ) : ZMod 23) := by
  have hΨ : TauCong.Ψ 23 (X * MockTheta5.JTP.qfacInf ^ 24)
      = TauCong.Ψ 23 (X * (RankProof.Ea (23 ^ 1) (TauCong.ppow_ne 23 1) MockTheta5.JTP.pentSeries *
        MockTheta5.JTP.pentSeries)) := by
    rw [← MockTheta5.JTP.euler_pentagonal, map_mul,
      show MockTheta5.JTP.qfacInf ^ 24 = MockTheta5.JTP.qfacInf ^ (23 ^ 1) * MockTheta5.JTP.qfacInf by ring,
      map_mul, map_pow, TauCong.frob_qfacInf 23 1]
    simp only [map_mul, map_pow]
  have h := congrArg (coeff (N + 1)) hΨ
  rw [TauCong.coeff_Ψ, TauCong.coeff_Ψ, coeff_succ_X_mul, coeff_succ_X_mul] at h
  rw [TauCong.tauPS, coeff_succ_X_mul]
  exact h

/-- **`τ(N+1) mod 23` as a certified finite sum.** -/
theorem tau_mod23_formula {N J₁ : ℕ} (hJ₁ : N < 23 * plo J₁) (hok : rall (okC 23 N) 0 J₁ = true)
    (hN : sqOK (24 * N + 1) = true) :
    ((TauCong.tauPS (N + 1) : ℤ) : ZMod 23) = ((pc N + rsum (termC 23 N) 0 J₁ : ℤ) : ZMod 23) := by
  have hNJ : N < plo (J₁ + (N + 1)) := by
    have := lt_plo_self (J₁ + (N + 1)); omega
  rw [tau_mod23_pent, coeff_Ea_pent _ hNJ, coeff_Ea_PJ]
  simp only [pow_one]
  congr 2
  · rw [coeff_PJ_closed hNJ, sqrt_of_sqOK hN]; rfl
  · rw [Finset.sum_range_add, rsum_eq]
    have hz : ∑ x ∈ range (N + 1), (-1 : ℤ) ^ (J₁ + x + 1) *
        ((if 23 * plo (J₁ + x) ≤ N then coeff (N - 23 * plo (J₁ + x)) (PJ (J₁ + (N + 1))) else 0) +
          (if 23 * phi (J₁ + x) ≤ N then coeff (N - 23 * phi (J₁ + x)) (PJ (J₁ + (N + 1))) else 0)) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      have h1 : plo J₁ ≤ plo (J₁ + x) := plo_strictMono.monotone (Nat.le_add_right _ _)
      have h2 := plo_le_phi (J₁ + x)
      rw [if_neg (by omega), if_neg (by omega)]; ring
    rw [hz, add_zero]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    have hm' := rall_eq _ 0 J₁ hok m hm
    rw [zero_add] at hm'
    simp only [okC, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      not_le] at hm'
    rw [zero_add, termC]
    congr 1
    congr 1
    · split_ifs with h
      · rw [coeff_PJ_closed (by omega)]
        rcases hm'.1 with h' | h'
        · omega
        · rw [sqrt_of_sqOK h']; rfl
      · rfl
    · split_ifs with h
      · rw [coeff_PJ_closed (by omega)]
        rcases hm'.2 with h' | h'
        · omega
        · rw [sqrt_of_sqOK h']; rfl
      · rfl

end RamanujanTau.LehmerSmall

#print axioms RamanujanTau.LehmerSmall.tau_mod23_formula
