import RamanujanTau.AtkinSporadic.HalfHecke
import RamanujanTau.TheoremA.LiftReduction
import RamanujanTau.HeckeQExp.Tq

/-!
# Hecke equivariance of the explicit Shimura lift (formal identity)

For the explicit lift `S_t A (n) = Σ_{de=n} (d/t) d^{λ−1} χ₁₂(e) A[(te²+ℓ)/24]`
(`TheoremA.HalfIntegral.liftSeries`) and the half-integral weight operator `T(Q²)` in the
`N`-coordinate (`heckeHalf`), for every prime `Q ≥ 5`, squarefree `t ≡ −ℓ (mod 24)` and every
integer sequence `A`:

  `S_t (T(Q²) A) = χ₁₂(Q) · T_Q (S_t A)`,   `T_Q B(n) = B(Qn) + Q^{2λ−1} B(n/Q)`.

This is a purely formal Dirichlet-convolution identity (no modular forms): the pointwise relation
`χ₁₂(e)(T(Q²)A)[te²] = χ₁₂(Q)(c(Qe) + ψ(Q)[Q∤e]c(e) + Q^{2λ−1}[Q∣e]c(e/Q))` with
`c(e) = χ₁₂(e)A[te²]`, followed by the convolution identity `conv_hecke` valid for every completely
multiplicative `ψ`. The middle term uses quadratic reciprocity together with the parity
`(−1/t) = (−1)^λ`, which holds because `t ≡ −ℓ (mod 24)` and `λ = (ℓ−3)/2`.
-/

set_option autoImplicit false

namespace RamanujanTau.AtkinSporadic.Equivariance
open PowerSeries RamanujanTau.TheoremA.HalfIntegral RamanujanTau.TheoremA.SignLattice

/-! ### Reindexing divisor sums -/

lemma sum_filter_dvd_snd {Q : ℕ} (hQ : 0 < Q) (h : ℕ × ℕ → ℤ) (n : ℕ) :
    ∑ x ∈ (Q * n).divisorsAntidiagonal.filter (fun x => Q ∣ x.2), h x =
      ∑ x ∈ n.divisorsAntidiagonal, h (x.1, Q * x.2) := by
  symm
  apply Finset.sum_nbij' (fun x => (x.1, Q * x.2)) (fun y => (y.1, y.2 / Q))
  · intro x hx
    simp only [Nat.mem_divisorsAntidiagonal] at hx
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
    · rw [← hx.1]; ring
    · exact mul_ne_zero hQ.ne' hx.2
  · intro y hy
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hy
    obtain ⟨⟨h1, h2⟩, k, hk⟩ := hy
    simp only [Nat.mem_divisorsAntidiagonal]
    rw [hk, Nat.mul_div_cancel_left _ hQ]
    refine ⟨?_, fun h0 => h2 (by rw [h0, mul_zero])⟩
    apply Nat.eq_of_mul_eq_mul_left hQ
    rw [← h1, hk]; ring
  · intro x _
    simp [Nat.mul_div_cancel_left _ hQ]
  · intro y hy
    simp only [Finset.mem_filter] at hy
    simp [Nat.mul_div_cancel' hy.2]
  · intro x _
    rfl

lemma sum_filter_not_dvd_snd {Q : ℕ} (hQ : Q.Prime) (h : ℕ × ℕ → ℤ) (n : ℕ) :
    ∑ x ∈ (Q * n).divisorsAntidiagonal.filter (fun x => ¬ Q ∣ x.2), h x =
      ∑ x ∈ n.divisorsAntidiagonal.filter (fun x => ¬ Q ∣ x.2), h (Q * x.1, x.2) := by
  symm
  have hQ0 := hQ.pos
  apply Finset.sum_nbij' (fun x => (Q * x.1, x.2)) (fun y => (y.1 / Q, y.2))
  · intro x hx
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx ⊢
    refine ⟨⟨?_, mul_ne_zero hQ0.ne' hx.1.2⟩, hx.2⟩
    rw [← hx.1.1]; ring
  · intro y hy
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hy ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hy
    have hd : Q ∣ y.1 := ((hQ.dvd_mul.mp (Dvd.intro n h1.symm)).resolve_right h3)
    obtain ⟨k, hk⟩ := hd
    rw [hk, Nat.mul_div_cancel_left _ hQ0]
    refine ⟨⟨?_, fun h0 => h2 (by rw [h0, mul_zero])⟩, h3⟩
    apply Nat.eq_of_mul_eq_mul_left hQ0
    rw [← h1, hk]; ring
  · intro x _
    simp [Nat.mul_div_cancel_left _ hQ0]
  · intro y hy
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hy
    obtain ⟨⟨h1, -⟩, h3⟩ := hy
    have hd : Q ∣ y.1 := ((hQ.dvd_mul.mp (Dvd.intro n h1.symm)).resolve_right h3)
    simp [Nat.mul_div_cancel' hd]
  · intro x _
    rfl

/-- `(Qn)` splits into `(d, Qe)` and `(Qd, e)` with `Q ∤ e`. -/
lemma sum_dAD_mul_prime {Q : ℕ} (hQ : Q.Prime) (g : ℕ × ℕ → ℤ) (n : ℕ) :
    ∑ x ∈ (Q * n).divisorsAntidiagonal, g x =
      ∑ x ∈ n.divisorsAntidiagonal, g (x.1, Q * x.2) +
        ∑ x ∈ n.divisorsAntidiagonal, (if Q ∣ x.2 then 0 else g (Q * x.1, x.2)) := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun x : ℕ × ℕ => Q ∣ x.2),
    sum_filter_dvd_snd hQ.pos, sum_filter_not_dvd_snd hQ, Finset.sum_ite, Finset.sum_const_zero,
    zero_add]

lemma sum_dAD_div_prime {Q : ℕ} (hQ : Q.Prime) (g : ℕ × ℕ → ℤ) (n : ℕ) :
    ∑ x ∈ n.divisorsAntidiagonal, (if Q ∣ x.2 then g (x.1, x.2 / Q) else 0) =
      if Q ∣ n then ∑ x ∈ (n / Q).divisorsAntidiagonal, g x else 0 := by
  rw [← Finset.sum_filter]
  split_ifs with hn
  · obtain ⟨m, rfl⟩ := hn
    rw [sum_filter_dvd_snd hQ.pos, Nat.mul_div_cancel_left _ hQ.pos]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Nat.mul_div_cancel_left _ hQ.pos]
  · apply Finset.sum_eq_zero
    intro x hx
    exfalso
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx
    exact hn (hx.2.trans (Dvd.intro_left _ hx.1.1))

/-- **The convolution identity.** For completely multiplicative `ψ`, if
`c' e = c(Qe) + ψ(Q)[Q∤e]c(e) + P[Q∣e]c(e/Q)` then `ψ * c' = T_Q^{(P)} (ψ * c)`. -/
theorem conv_hecke {Q : ℕ} (hQ : Q.Prime) (ψ : ℕ → ℤ) (hψ : ∀ a b, ψ (a * b) = ψ a * ψ b)
    (c c' : ℕ → ℤ) (P : ℤ)
    (h : ∀ e, e ≠ 0 → c' e = c (Q * e) + ψ Q * (if Q ∣ e then 0 else c e) +
      P * (if Q ∣ e then c (e / Q) else 0)) (n : ℕ) :
    ∑ x ∈ n.divisorsAntidiagonal, ψ x.1 * c' x.2 =
      ∑ x ∈ (Q * n).divisorsAntidiagonal, ψ x.1 * c x.2 +
        P * (if Q ∣ n then ∑ x ∈ (n / Q).divisorsAntidiagonal, ψ x.1 * c x.2 else 0) := by
  have e1 : ∑ x ∈ n.divisorsAntidiagonal, ψ x.1 * c' x.2 =
      ∑ x ∈ n.divisorsAntidiagonal, ((ψ x.1 * c (Q * x.2) +
        (if Q ∣ x.2 then 0 else ψ (Q * x.1) * c x.2)) +
        P * (if Q ∣ x.2 then ψ x.1 * c (x.2 / Q) else 0)) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx2 : x.2 ≠ 0 := fun h0 => (Nat.mem_divisorsAntidiagonal.mp hx).2 (by rw [← (Nat.mem_divisorsAntidiagonal.mp hx).1, h0, mul_zero])
    rw [h x.2 hx2, hψ]
    split_ifs <;> ring
  rw [e1, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_dAD_mul_prime hQ (fun x => ψ x.1 * c x.2)]
  congr 2
  exact sum_dAD_div_prime hQ (fun x => ψ x.1 * c x.2) n

/-! ### Characters -/

lemma chi12_mod (e : ℕ) : chi12 e = chi12 (e % 12) := by
  unfold chi12
  simp only [Nat.mod_mod]

lemma chi12_mul (a b : ℕ) : chi12 (a * b) = chi12 a * chi12 b := by
  rw [chi12_mod (a * b), chi12_mod a, chi12_mod b, Nat.mul_mod]
  have ha := Nat.mod_lt a (show 12 > 0 by norm_num)
  have hb := Nat.mod_lt b (show 12 > 0 by norm_num)
  generalize a % 12 = x at ha ⊢
  generalize b % 12 = y at hb ⊢
  interval_cases x <;> interval_cases y <;> decide

lemma chi12_sq {Q : ℕ} (h2 : ¬ 2 ∣ Q) (h3 : ¬ 3 ∣ Q) : chi12 Q * chi12 Q = 1 := by
  rcases chi12_ne_zero h2 h3 with h | h <;> rw [h] <;> norm_num

lemma prime_ge_five {Q : ℕ} (hQ : Q.Prime) (h5 : 5 ≤ Q) : ¬ 2 ∣ Q ∧ ¬ 3 ∣ Q := by
  constructor
  · intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hQ).mp h
    omega
  · intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hQ).mp h
    omega

/-- `(12/Q) = χ₁₂(Q)` for primes `Q ≥ 5`. -/
lemma legendre_twelve {Q : ℕ} [hQ : Fact Q.Prime] (h5 : 5 ≤ Q) : legendreSym Q 12 = chi12 Q := by
  obtain ⟨h2, h3⟩ := prime_ge_five hQ.out h5
  have h4 : legendreSym Q 4 = 1 := by
    have : (4 : ℤ) = 2 ^ 2 := by norm_num
    rw [this]
    apply legendreSym.sq_one'
    intro h0
    have h0' : ((2 : ℕ) : ZMod Q) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h0'
    exact absurd (Nat.le_of_dvd (by norm_num) h0') (by omega)
  rw [show (12 : ℤ) = 4 * 3 by norm_num, legendreSym.mul, h4, one_mul,
    jacobiSym.legendreSym.to_jacobiSym, jacobi_three h2 h3]
  unfold chi12
  have hs : Q % 12 = 1 ∨ Q % 12 = 5 ∨ Q % 12 = 7 ∨ Q % 12 = 11 := by omega
  rcases hs with h | h | h | h
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]; norm_num
  · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]; norm_num
  · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]; norm_num
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; norm_num

/-- `((−1)^λ t / Q) = (Q/t)` when `(−1/t) = (−1)^λ`, here encoded by `t ≡ 1 (4) ↔ λ` even. -/
lemma recip {Q t lam : ℕ} [hQ : Fact Q.Prime] (hQ2 : ¬ 2 ∣ Q) (ht : t % 4 = 1 ∨ t % 4 = 3)
    (hpar : t % 4 = 1 ↔ Even lam) :
    legendreSym Q ((-1) ^ lam) * legendreSym Q t = jacobiSym Q t := by
  have hQodd : Odd Q := Nat.odd_iff.mpr (by omega)
  have htodd : Odd t := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.legendreSym.to_jacobiSym]
  rcases ht with h | h
  · have hev : Even lam := hpar.mp h
    rw [hev.neg_one_pow, jacobiSym.one_left, one_mul]
    exact jacobiSym.quadratic_reciprocity_one_mod_four h hQodd
  · have hod : Odd lam := by
      rcases Nat.even_or_odd lam with he | ho
      · exact absurd (hpar.mpr he) (by omega)
      · exact ho
    rw [hod.neg_one_pow, jacobiSym.at_neg_one hQodd]
    rcases (by omega : Q % 4 = 1 ∨ Q % 4 = 3) with hq | hq
    · rw [ZMod.χ₄_nat_one_mod_four hq, one_mul]
      exact (jacobiSym.quadratic_reciprocity_one_mod_four hq htodd).symm
    · rw [ZMod.χ₄_nat_three_mod_four hq, jacobiSym.quadratic_reciprocity_three_mod_four h hq]
      ring

/-! ### Index arithmetic -/

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

omit hℓ in
lemma latIndex_spec {t e : ℕ} (ht : 24 ∣ t + jj ℓ) (h2 : ¬ 2 ∣ e) (h3 : ¬ 3 ∣ e) :
    24 * latIndex ℓ t e = t * e ^ 2 + jj ℓ := by
  have hs := sq_mod_24 h2 h3
  obtain ⟨k, hk⟩ : ∃ k, e ^ 2 = 24 * k + 1 := ⟨e ^ 2 / 24, by omega⟩
  have hte : t * e ^ 2 = 24 * (t * k) + t := by rw [hk]; ring
  unfold latIndex
  generalize t * e ^ 2 = u at hte ⊢
  omega

lemma hshift_spec {Q : ℕ} (hQ2 : ¬ 2 ∣ Q) (hQ3 : ¬ 3 ∣ Q) (j : ℕ) :
    24 * hshift Q j = (Q ^ 2 - 1) * j := by
  have hs := sq_mod_24 hQ2 hQ3
  have h1 : 1 ≤ Q ^ 2 := by omega
  obtain ⟨k, hk⟩ : ∃ k, Q ^ 2 - 1 = 24 * k := ⟨(Q ^ 2 - 1) / 24, by omega⟩
  unfold hshift
  rw [hk, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]

/-! ### The pointwise relation -/

section Pointwise

variable (h13 : 13 ≤ ℓ) (h24 : ℓ < 24) {Q : ℕ} [hQ : Fact Q.Prime] (hQ5 : 5 ≤ Q)
  {t : ℕ} (hsf : Squarefree t) (ht : 24 ∣ t + jj ℓ)

include h13 h24 hQ5 hsf ht in
/-- `χ₁₂(e)·(T(Q²)A)[te²] = χ₁₂(Q)·(c(Qe) + ψ(Q)[Q∤e]c(e) + Q^{2λ−1}[Q∣e]c(e/Q))`. -/
theorem pointwise (A : PowerSeries ℤ) (e : ℕ) (he : e ≠ 0) :
    chi12 e * (heckeHalf Q ℓ (halfWt ℓ) (heckeSign Q (halfWt ℓ)) A).coeff (latIndex ℓ t e) =
      chi12 Q * ((chi12 (Q * e) * A.coeff (latIndex ℓ t (Q * e))) +
        psi t (halfWt ℓ) Q * (if Q ∣ e then 0 else chi12 e * A.coeff (latIndex ℓ t e)) +
        (Q : ℤ) ^ (2 * halfWt ℓ - 1) *
          (if Q ∣ e then chi12 (e / Q) * A.coeff (latIndex ℓ t (e / Q)) else 0)) := by
  obtain ⟨hQ2, hQ3⟩ := prime_ge_five hQ.out hQ5
  have hjj : jj ℓ = ℓ := Nat.mod_eq_of_lt h24
  have hl2 : ¬ 2 ∣ ℓ := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ.out).mp h; omega
  have hcQ := chi12_sq hQ2 hQ3
  by_cases hbad : 2 ∣ e ∨ 3 ∣ e
  · -- every term vanishes
    have h0 : chi12 e = 0 := by
      rcases hbad with h | h
      · exact chi12_eq_zero_of_two h
      · exact chi12_eq_zero_of_three h
    have h1 : chi12 (Q * e) = 0 := by rw [chi12_mul, h0, mul_zero]
    have h2 : Q ∣ e → chi12 (e / Q) = 0 := by
      intro hd
      obtain ⟨k, hk⟩ := hd
      rw [hk, Nat.mul_div_cancel_left _ hQ.out.pos]
      have : chi12 Q * chi12 k = 0 := by rw [← chi12_mul, ← hk, h0]
      rcases mul_eq_zero.mp this with h | h
      · rcases chi12_ne_zero hQ2 hQ3 with h' | h' <;> rw [h'] at h <;> norm_num at h
      · exact h
    rw [h0, h1]
    split_ifs with hd
    · rw [h2 hd]; ring
    · ring
  simp only [not_or] at hbad
  obtain ⟨he2, he3⟩ := hbad
  set N := latIndex ℓ t e with hNdef
  have hN := latIndex_spec (ℓ := ℓ) ht he2 he3
  rw [← hNdef, hjj] at hN
  have hd := hshift_spec hQ2 hQ3 ℓ
  have hQ1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ.out.pos
  have hQe2 : ¬ 2 ∣ Q * e := fun h => (Nat.Prime.dvd_mul Nat.prime_two).mp h |>.elim hQ2 he2
  have hQe3 : ¬ 3 ∣ Q * e := fun h => (Nat.Prime.dvd_mul Nat.prime_three).mp h |>.elim hQ3 he3
  have hNQ := latIndex_spec (ℓ := ℓ) ht hQe2 hQe3
  rw [hjj] at hNQ
  -- first term
  have hle : hshift Q ℓ ≤ Q ^ 2 * N := by
    have : 24 * hshift Q ℓ ≤ 24 * (Q ^ 2 * N) := by
      rw [hd, show 24 * (Q ^ 2 * N) = Q ^ 2 * (24 * N) by ring, hN, Nat.sub_mul, one_mul]
      have : ℓ ≤ t * e ^ 2 + ℓ := by omega
      calc Q ^ 2 * ℓ - ℓ ≤ Q ^ 2 * ℓ := Nat.sub_le _ _
        _ ≤ Q ^ 2 * (t * e ^ 2 + ℓ) := Nat.mul_le_mul_left _ this
    omega
  have hidx1 : Q ^ 2 * N - hshift Q ℓ = latIndex ℓ t (Q * e) := by
    have : 24 * (Q ^ 2 * N - hshift Q ℓ) = 24 * latIndex ℓ t (Q * e) := by
      rw [hNQ, Nat.mul_sub, hd, show 24 * (Q ^ 2 * N) = Q ^ 2 * (24 * N) by ring, hN]
      rw [show (Q * e) ^ 2 = Q ^ 2 * e ^ 2 by ring, Nat.sub_mul, one_mul]
      have h1 : Q ^ 2 * (t * e ^ 2 + ℓ) = t * (Q ^ 2 * e ^ 2) + Q ^ 2 * ℓ := by ring
      have h2 : ℓ ≤ Q ^ 2 * ℓ := Nat.le_mul_of_pos_left _ (by omega)
      rw [h1]
      omega
    omega
  -- middle term
  have hleg : legendreSym Q (24 * (N : ℤ) - ℓ) = legendreSym Q t * (if Q ∣ e then 0 else 1) := by
    have e1 : (24 * (N : ℤ) - ℓ) = (t : ℤ) * (e : ℤ) ^ 2 := by
      have : ((24 * N : ℕ) : ℤ) = ((t * e ^ 2 + ℓ : ℕ) : ℤ) := by rw [hN]
      push_cast at this
      linarith
    rw [e1, legendreSym.mul]
    split_ifs with hQe
    · have : legendreSym Q ((e : ℤ) ^ 2) = 0 := by
        rw [legendreSym.eq_zero_iff]
        have : ((e : ℤ) : ZMod Q) = 0 := by
          rw [Int.cast_natCast, ZMod.natCast_eq_zero_iff]; exact hQe
        push_cast at this ⊢
        rw [this]; ring
      rw [this]
    · rw [legendreSym.sq_one', mul_one]
      intro h0
      apply hQe
      rw [Int.cast_natCast, ZMod.natCast_eq_zero_iff] at h0
      exact h0
  have ht4 : t % 4 = 1 ∨ t % 4 = 3 := by
    have : ¬ 2 ∣ t := by rw [hjj] at ht; omega
    omega
  have hpar : t % 4 = 1 ↔ Even (halfWt ℓ) := by
    rw [hjj] at ht
    unfold halfWt
    constructor
    · intro h
      have : ℓ % 4 = 3 := by omega
      exact Nat.even_iff.mpr (by omega)
    · intro h
      have := Nat.even_iff.mp h
      omega
  have hmid : heckeSign Q (halfWt ℓ) * legendreSym Q (24 * (N : ℤ) - ℓ) *
      (Q : ℤ) ^ (halfWt ℓ - 1) = chi12 Q * psi t (halfWt ℓ) Q * (if Q ∣ e then 0 else 1) := by
    rw [hleg, heckeSign, legendre_twelve hQ5, psi]
    have hr := recip (Q := Q) (t := t) (lam := halfWt ℓ) hQ2 ht4 hpar
    calc chi12 Q * legendreSym Q ((-1) ^ halfWt ℓ) * (legendreSym Q t * (if Q ∣ e then 0 else 1)) *
          (Q : ℤ) ^ (halfWt ℓ - 1) =
        chi12 Q * (legendreSym Q ((-1) ^ halfWt ℓ) * legendreSym Q t) * (Q : ℤ) ^ (halfWt ℓ - 1) *
          (if Q ∣ e then 0 else 1) := by ring
      _ = _ := by rw [hr]; ring
  -- third term
  have hthird : Q ^ 2 ∣ N + hshift Q ℓ ↔ Q ∣ e := by
    have h24' : 24 * (N + hshift Q ℓ) = t * e ^ 2 + Q ^ 2 * ℓ := by
      rw [mul_add, hN, hd, Nat.sub_mul, one_mul]
      have h2 : ℓ ≤ Q ^ 2 * ℓ := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hcop : Nat.Coprime (Q ^ 2) 24 := by
      apply Nat.Coprime.pow_left
      rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num]
      apply Nat.Coprime.mul_right
      · exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hQ.out).mpr
          (fun h => hQ2 ((Nat.prime_dvd_prime_iff_eq hQ.out Nat.prime_two).mp h ▸ dvd_refl _)))
      · exact (Nat.Prime.coprime_iff_not_dvd hQ.out).mpr
          (fun h => hQ3 ((Nat.prime_dvd_prime_iff_eq hQ.out Nat.prime_three).mp h ▸ dvd_refl _))
    constructor
    · intro hdv
      have h1 : Q ^ 2 ∣ t * e ^ 2 := by
        have : Q ^ 2 ∣ 24 * (N + hshift Q ℓ) := hdv.mul_left 24
        rw [h24'] at this
        exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp (by rwa [add_comm] at this)
      by_contra hQe
      have hcop' : Nat.Coprime Q (e ^ 2) :=
        Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hQ.out).mpr hQe)
      have : Q * Q ∣ t := by
        rw [← pow_two]
        exact (Nat.Coprime.pow_left 2 hcop').dvd_of_dvd_mul_right h1
      have := hsf Q this
      exact hQ.out.one_lt.ne' (Nat.isUnit_iff.mp this)
    · rintro ⟨k, rfl⟩
      have : Q ^ 2 ∣ 24 * (N + hshift Q ℓ) := by
        rw [h24']
        exact dvd_add ⟨t * k ^ 2, by ring⟩ (dvd_mul_right _ _)
      exact hcop.dvd_of_dvd_mul_left this
  have hidx3 : Q ∣ e → (N + hshift Q ℓ) / Q ^ 2 = latIndex ℓ t (e / Q) := by
    rintro ⟨k, rfl⟩
    rw [Nat.mul_div_cancel_left _ hQ.out.pos]
    have hk2 : ¬ 2 ∣ k := fun h => he2 (h.mul_left Q)
    have hk3 : ¬ 3 ∣ k := fun h => he3 (h.mul_left Q)
    have hK := latIndex_spec (ℓ := ℓ) ht hk2 hk3
    rw [hjj] at hK
    have h24' : 24 * (N + hshift Q ℓ) = Q ^ 2 * (24 * latIndex ℓ t k) := by
      rw [mul_add, hN, hd, Nat.sub_mul, one_mul, hK]
      have h2 : ℓ ≤ Q ^ 2 * ℓ := Nat.le_mul_of_pos_left _ (by omega)
      have : t * (Q * k) ^ 2 = Q ^ 2 * (t * k ^ 2) := by ring
      rw [this]
      have : Q ^ 2 * (t * k ^ 2 + ℓ) = Q ^ 2 * (t * k ^ 2) + Q ^ 2 * ℓ := by ring
      omega
    have : N + hshift Q ℓ = Q ^ 2 * latIndex ℓ t k := by
      have : 24 * (N + hshift Q ℓ) = 24 * (Q ^ 2 * latIndex ℓ t k) := by rw [h24']; ring
      omega
    rw [this, Nat.mul_div_cancel_left _ (by positivity)]
  -- assemble
  rw [coeff_heckeHalf, if_pos hle, hidx1, hmid]
  simp only [Int.cast_id]
  have hce : chi12 e = chi12 Q * chi12 (Q * e) := by
    rw [chi12_mul, ← mul_assoc, hcQ, one_mul]
  by_cases hQe : Q ∣ e
  · have hc3 : chi12 e = chi12 Q * chi12 (e / Q) := by
      rw [← chi12_mul, Nat.mul_div_cancel' hQe]
    rw [if_pos (hthird.mpr hQe), hidx3 hQe]
    simp only [if_pos hQe, mul_zero, zero_mul, add_zero]
    linear_combination A.coeff (latIndex ℓ t (Q * e)) * hce +
      (Q : ℤ) ^ (2 * halfWt ℓ - 1) * A.coeff (latIndex ℓ t (e / Q)) * hc3
  · rw [if_neg (mt hthird.mp hQe)]
    simp only [if_neg hQe, mul_zero, mul_one, add_zero]
    linear_combination A.coeff (latIndex ℓ t (Q * e)) * hce

include h13 h24 hQ5 hsf ht in
/-- **Hecke equivariance of the lift**: `S_t(T(Q²)A) = χ₁₂(Q) · T_Q(S_t A)`. -/
theorem lift_heckeHalf (A : PowerSeries ℤ) :
    liftSeries ℓ t (heckeHalf Q ℓ (halfWt ℓ) (heckeSign Q (halfWt ℓ)) A) =
      chi12 Q • HeckeQExp.Tq Q ((Q : ℤ) ^ (2 * halfWt ℓ - 1)) (liftSeries ℓ t A) := by
  ext n
  rw [coeff_liftSeries, map_zsmul, HeckeQExp.coeff_Tq, coeff_liftSeries, smul_eq_mul]
  have hc := conv_hecke hQ.out (psi t (halfWt ℓ)) (fun a b => psi_mul t _ a b)
    (fun e => chi12 e * A.coeff (latIndex ℓ t e))
    (fun e => chi12 (Q * e) * A.coeff (latIndex ℓ t (Q * e)) +
        psi t (halfWt ℓ) Q * (if Q ∣ e then 0 else chi12 e * A.coeff (latIndex ℓ t e)) +
        (Q : ℤ) ^ (2 * halfWt ℓ - 1) *
          (if Q ∣ e then chi12 (e / Q) * A.coeff (latIndex ℓ t (e / Q)) else 0))
    ((Q : ℤ) ^ (2 * halfWt ℓ - 1)) (fun e _ => rfl) n
  have e1 : ∑ x ∈ n.divisorsAntidiagonal, psi t (halfWt ℓ) x.1 *
      (chi12 x.2 * (heckeHalf Q ℓ (halfWt ℓ) (heckeSign Q (halfWt ℓ)) A).coeff (latIndex ℓ t x.2)) =
      chi12 Q * ∑ x ∈ n.divisorsAntidiagonal, psi t (halfWt ℓ) x.1 *
        (chi12 (Q * x.2) * A.coeff (latIndex ℓ t (Q * x.2)) +
        psi t (halfWt ℓ) Q * (if Q ∣ x.2 then 0 else chi12 x.2 * A.coeff (latIndex ℓ t x.2)) +
        (Q : ℤ) ^ (2 * halfWt ℓ - 1) *
          (if Q ∣ x.2 then chi12 (x.2 / Q) * A.coeff (latIndex ℓ t (x.2 / Q)) else 0)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx2 : x.2 ≠ 0 := fun h0 => (Nat.mem_divisorsAntidiagonal.mp hx).2 (by rw [← (Nat.mem_divisorsAntidiagonal.mp hx).1, h0, mul_zero])
    rw [pointwise h13 h24 hQ5 hsf ht A x.2 hx2]
    ring
  rw [e1, hc]
  congr 1
  congr 1
  split_ifs
  · rw [coeff_liftSeries]
  · rfl

end Pointwise

end RamanujanTau.AtkinSporadic.Equivariance
