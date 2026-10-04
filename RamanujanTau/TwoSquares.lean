/-
# Jacobi's two-square theorem

  `r₂(N) = #{(a,b) ∈ ℤ² : a²+b² = N} = 4 (d₁(N) − d₃(N))`   (`N ≥ 1`),

where `d_i(N)` counts the divisors `≡ i (mod 4)`. The route is the same as for four squares
(`FourSquares.lean`): the specialization `a = 1, b = i, c = −i, d = −1` of Jackson's ₈φ₇ gives

  `(−q)ₙ²/(q)ₙ² + Σ_{k=1}^n 4(−1)^k q^k/(1+q^{2k}) · (−q)_{n−k}(−q)_{n+k}/((q)_{n−k}(q)_{n+k}) = 1`,

with WZ certificate `G(n,k) = 4(−1)^k c(n) (−q)_{n+1−k}(−q)_{n+k}/((q)_{n+1−k}(q)_{n+k})` and
`c(n) = −q^{n+1}/((1−q^{n+1})(1+q^{n+1}))`. Its limit is `φ(−q)² = 1 + 4 Σ (−1)^k q^k/(1+q^{2k})`.
-/
import RamanujanTau.FourSquares

set_option autoImplicit false

namespace FourSquares
open PowerSeries Finset MockTheta5.Bailey MockTheta5.JTP
open RankProof (thetaS)

lemma isUnit_one_add_sq {k : ℕ} (hk : 1 ≤ k) : IsUnit (1 + (X ^ k) ^ 2 : PowerSeries ℤ) :=
  isUnit_of_cc (by simp [zero_pow (by omega : k ≠ 0)])

macro "unit_tac2" : tactic =>
  `(tactic| repeat' (first | exact isUnit_qfac _ | exact isUnit_mfac _ | exact isUnit_one_add (by omega) | exact isUnit_one_sub (by omega) | exact isUnit_one_add_sq (by omega) | apply IsUnit.mul | apply IsUnit.pow))

noncomputable def c2 (n : ℕ) : PowerSeries ℤ :=
  -X ^ (n + 1) * Ring.inverse ((1 - X ^ (n + 1)) * (1 + X ^ (n + 1)))

noncomputable def C2 (n : ℕ) : PowerSeries ℤ := mfac n ^ 2 * Ring.inverse (qfac n ^ 2)

noncomputable def T2 (n k : ℕ) : PowerSeries ℤ :=
  4 * (-1) ^ k * X ^ k * Ring.inverse (1 + (X ^ k) ^ 2) * (mfac (n - k) * mfac (n + k))
    * Ring.inverse (qfac (n - k) * qfac (n + k))

noncomputable def G2 (n k : ℕ) : PowerSeries ℤ :=
  4 * (-1) ^ k * c2 n * (mfac (n + 1 - k) * mfac (n + k)) * Ring.inverse (qfac (n + 1 - k) * qfac (n + k))

noncomputable def S2 (n : ℕ) : PowerSeries ℤ := C2 n + ∑ i ∈ range n, T2 n (i + 1)

lemma wz2_C (n : ℕ) : C2 (n + 1) - C2 n = G2 n 1 := by
  apply φ_inj
  have hq := φ_ne (isUnit_qfac n)
  have hm := φ_ne (isUnit_mfac n)
  have h1 := φ_ne (isUnit_one_sub (m := n + 1) (by omega))
  have h2 := φ_ne (isUnit_one_add (m := n + 1) (by omega))
  simp only [map_sub, map_add, map_one, map_pow] at h1 h2
  simp only [C2, G2, c2, show n + 1 - 1 = n by omega, mfac_succ, qfac_succ', pow_one]
  simp (disch := unit_tac2) only [φ_inverse, map_sub, map_add, map_mul, map_neg, map_one, map_pow, map_ofNat]
  generalize φ (X ^ (n + 1)) = u at *
  generalize φ (qfac n) = p at *
  generalize φ (mfac n) = m at *
  field_simp
  ring

lemma wz2_step (j k : ℕ) (hk : 1 ≤ k) :
    T2 (j + k + 1) k - T2 (j + k) k = G2 (j + k) (k + 1) - G2 (j + k) k := by
  apply φ_inj
  have hq1 := φ_ne (isUnit_qfac j)
  have hq2 := φ_ne (isUnit_qfac (j + k + k))
  have hm1 := φ_ne (isUnit_mfac j)
  have hm2 := φ_ne (isUnit_mfac (j + k + k))
  have h1 := φ_ne (isUnit_one_sub (m := j + 1) (by omega))
  have h2 := φ_ne (isUnit_one_sub (m := j + k + k + 1) (by omega))
  have h3 := φ_ne (isUnit_one_sub (m := j + k + 1) (by omega))
  have h4 := φ_ne (isUnit_one_add (m := j + k + 1) (by omega))
  have h5 := φ_ne (isUnit_one_add_sq hk)
  have h6 := φ_ne (isUnit_one_add (m := j + 1) (by omega))
  have h7 := φ_ne (isUnit_one_add (m := j + k + k + 1) (by omega))
  simp only [map_sub, map_add, map_one, map_pow, map_mul, pow_add, pow_one] at h1 h2 h3 h4 h5 h6 h7
  simp only [T2, G2, c2, show j + k + 1 - k = j + 1 by omega, show j + k + 1 + k = j + k + k + 1 by ring,
    show j + k - k = j by omega, show j + k + 1 - (k + 1) = j by omega, show j + k + (k + 1) = j + k + k + 1 by ring,
    mfac_succ, qfac_succ']
  simp (disch := unit_tac2) only [φ_inverse, map_sub, map_add, map_mul, map_neg, map_one, map_pow, map_ofNat]
  simp only [pow_add, pow_one]
  generalize φ X ^ j = a at *
  generalize φ X ^ k = b at *
  generalize φ X = x at *
  generalize φ (qfac j) = p1 at *
  generalize φ (qfac (j + k + k)) = p2 at *
  generalize φ (mfac j) = m1 at *
  generalize φ (mfac (j + k + k)) = m2 at *
  generalize hv : a * b * b * x = v at *
  generalize hu : a * b * x = u at *
  generalize hw : a * x = w at *
  generalize hb2 : b ^ 2 = bb at *
  field_simp
  subst hu hv hw hb2
  ring

lemma wz2_end (n : ℕ) : T2 (n + 1) (n + 1) = -G2 n (n + 1) := by
  apply φ_inj
  have hq1 := φ_ne (isUnit_qfac (n + n + 1))
  have hm1 := φ_ne (isUnit_mfac (n + n + 1))
  have h2 := φ_ne (isUnit_one_sub (m := n + n + 1 + 1) (by omega))
  have h3 := φ_ne (isUnit_one_sub (m := n + 1) (by omega))
  have h4 := φ_ne (isUnit_one_add (m := n + 1) (by omega))
  have h6 := φ_ne (isUnit_one_add (m := n + n + 1 + 1) (by omega))
  rw [T2, G2, c2, show n + 1 - (n + 1) = 0 by omega, show n + 1 + (n + 1) = n + n + 1 + 1 by ring,
    show n + (n + 1) = n + n + 1 by ring, mfac_succ (n + n + 1), qfac_succ' (n + n + 1), mfac_zero, qfac_zero]
  simp only [one_mul]
  simp (disch := unit_tac2) only [φ_inverse, map_sub, map_add, map_mul, map_neg, map_one, map_pow, map_ofNat]
  simp only [map_sub, map_add, map_one, map_pow] at h2 h3 h4 h6
  have e2 : φ X ^ (n + n + 1 + 1) = (φ X ^ (n + 1)) ^ 2 := by rw [← pow_mul]; ring_nf
  rw [e2] at h2 h6 ⊢
  generalize φ X ^ (n + 1) = u at *
  generalize φ (qfac (n + n + 1)) = p1 at *
  generalize φ (mfac (n + n + 1)) = m1 at *
  generalize hv : u ^ 2 = v at *
  field_simp
  subst hv
  ring

lemma wz2_step' {n k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ n) : T2 (n + 1) k - T2 n k = G2 n (k + 1) - G2 n k := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + k := ⟨n - k, by omega⟩
  exact wz2_step j k h1

theorem S2_eq_one (n : ℕ) : S2 n = 1 := by
  induction n with
  | zero => simp [S2, C2, mfac_zero, qfac_zero]
  | succ n ih =>
    rw [← ih, S2, S2, sum_range_succ, wz2_end]
    have hC := wz2_C n
    have hT : ∑ i ∈ range n, T2 (n + 1) (i + 1)
        = ∑ i ∈ range n, T2 n (i + 1) + ∑ i ∈ range n, (G2 n (i + 1 + 1) - G2 n (i + 1)) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun i hi => ?_
      have := wz2_step' (n := n) (k := i + 1) (by omega) (by simp at hi; omega)
      linear_combination this
    rw [hT, sum_range_sub (fun i => G2 n (i + 1))]
    linear_combination hC


/-! ## the limit -/

/-- `(−1)^k q^k/(1+q^{2k})`. -/
noncomputable def t2 (k : ℕ) : PowerSeries ℤ := (-1) ^ k * X ^ k * Ring.inverse (1 + (X ^ k) ^ 2)

noncomputable def L2 : PowerSeries ℤ := mk fun m => coeff m (∑ i ∈ range m, t2 (i + 1))

lemma π_L2 (N : ℕ) : π N L2 = π N (∑ i ∈ range N, t2 (i + 1)) := by
  rw [π_eq_iff, PowerSeries.X_pow_dvd_iff]
  intro m hm
  rw [map_sub, L2, coeff_mk, sub_eq_zero, map_sum, map_sum, show N = m + (N - m) by omega, sum_range_add]
  rw [sum_eq_zero (s := range (N - m)) fun i _ => by
    rw [t2, mul_comm ((-1 : PowerSeries ℤ) ^ (m + i + 1)), mul_assoc, coeff_X_pow_mul', if_neg (by omega)], add_zero]

theorem limit2 : mfacInf ^ 2 * Ring.inverse (qfacInf ^ 2) * (1 + 4 * L2) = 1 := by
  refine eq_of_dvd_all fun N => ?_
  rw [← π_eq_iff, map_one]
  set n := N + 1 + (N + 1) with hn
  have hS := congrArg (π (N + 1)) (S2_eq_one n)
  rw [S2, C2, map_one, map_add, map_sum, hn, sum_range_add] at hS
  rw [sum_eq_zero (s := range (N + 1)) (f := fun x => π (N + 1) (T2 (N + 1 + (N + 1)) (N + 1 + x + 1))) (fun i _ => by
    dsimp only; rw [T2]; simp only [map_mul, π_X_pow (show N + 1 ≤ N + 1 + i + 1 by omega), mul_zero, zero_mul]),
    add_zero, ← hn] at hS
  have hP : ∀ m, N + 1 ≤ m → π (N + 1) (qfac m) = π (N + 1) qfacInf := fun m h => π_qfac h
  have hM : ∀ m, N + 1 ≤ m → π (N + 1) (mfac m) = π (N + 1) mfacInf := fun m h => π_mfac h
  have hC : π (N + 1) (mfac n ^ 2 * Ring.inverse (qfac n ^ 2))
      = π (N + 1) (mfacInf ^ 2 * Ring.inverse (qfacInf ^ 2)) := by
    simp (disch := unit_tac2) only [map_mul, map_pow, π_inverse]
    rw [hM n (by omega), hP n (by omega), π_inverse ((isUnit_qfacInf).pow 2), map_pow]
  have hT : ∀ i ∈ range (N + 1), π (N + 1) (T2 n (i + 1))
      = π (N + 1) (mfacInf ^ 2 * Ring.inverse (qfacInf ^ 2)) * (4 * π (N + 1) (t2 (i + 1))) := by
    intro i hi
    rw [mem_range] at hi
    rw [T2, t2]
    simp (disch := unit_tac2) only [map_mul, map_pow, π_inverse]
    rw [hM (n - (i + 1)) (by omega), hM (n + (i + 1)) (by omega), hP (n - (i + 1)) (by omega),
      hP (n + (i + 1)) (by omega), π_inverse ((isUnit_qfacInf).pow 2), map_pow,
      show π (N + 1) qfacInf * π (N + 1) qfacInf = π (N + 1) qfacInf ^ 2 by ring]
    simp only [map_ofNat]
    ring
  rw [← hS, hC, sum_congr rfl hT, ← mul_sum]
  simp only [map_mul, map_add, map_one, π_L2, map_sum, map_ofNat]
  rw [← mul_sum]
  ring

/-- **`φ(−q)² = 1 + 4 Σ_{k≥1} (−1)^k q^k/(1+q^{2k})`**. -/
theorem theta_sq : thetaS 2 1 ^ 2 = 1 + 4 * L2 := by
  have hl := limit2
  have ht := theta_mul_mfacInf
  have hq : qfacInf ^ 2 * Ring.inverse (qfacInf ^ 2) = 1 := Ring.mul_inverse_cancel _ (isUnit_qfacInf.pow 2)
  calc thetaS 2 1 ^ 2 = thetaS 2 1 ^ 2 * (mfacInf ^ 2 * Ring.inverse (qfacInf ^ 2) * (1 + 4 * L2)) := by
        rw [hl, mul_one]
    _ = (thetaS 2 1 * mfacInf) ^ 2 * Ring.inverse (qfacInf ^ 2) * (1 + 4 * L2) := by ring
    _ = 1 + 4 * L2 := by rw [ht, hq, one_mul]

/-! ## coefficients -/

/-- `1/(1+q^{2k}) = Σ_m (−1)^m q^{2km}`. -/
noncomputable def h2s (k : ℕ) : PowerSeries ℤ := mk fun j => if 2 * k ∣ j then (-1) ^ (j / (2 * k)) else 0

lemma h2s_eval {k : ℕ} (hk : 1 ≤ k) (m r : ℕ) (hr : r < 2 * k) :
    coeff (2 * k * m + r) (h2s k) = if r = 0 then (-1) ^ m else 0 := by
  rw [h2s, coeff_mk]
  have hdiv : (2 * k * m + r) / (2 * k) = m := by
    rw [add_comm, Nat.add_mul_div_left r m (by omega), Nat.div_eq_of_lt hr, zero_add]
  have hdvd : 2 * k ∣ 2 * k * m + r ↔ r = 0 := by
    rw [Nat.dvd_add_right (dvd_mul_right _ m)]
    exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hr, fun h => h ▸ dvd_zero _⟩
  by_cases h0 : r = 0
  · rw [if_pos (hdvd.mpr h0), if_pos h0, hdiv]
  · rw [if_neg (fun h => h0 (hdvd.mp h)), if_neg h0]

lemma mul_h2s {k : ℕ} (hk : 1 ≤ k) : (1 + (X ^ k) ^ 2) * h2s k = 1 := by
  ext j
  rw [add_mul, one_mul, map_add, ← pow_mul, show k * 2 = 2 * k by ring, coeff_X_pow_mul', coeff_one]
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 2 * k ∧ j = 2 * k * m + r :=
    ⟨j / (2 * k), j % (2 * k), Nat.mod_lt _ (by omega), (Nat.div_add_mod j (2 * k)).symm⟩
  rw [h2s_eval hk m r hr]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [if_neg (show ¬ 2 * k ≤ 2 * k * 0 + r by omega)]
    by_cases h0 : r = 0 <;> simp [h0]
  · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [if_pos (show 2 * k ≤ 2 * k * (m + 1) + r by nlinarith),
      show 2 * k * (m + 1) + r - 2 * k = 2 * k * m + r by rw [Nat.mul_succ]; omega, h2s_eval hk m r hr,
      if_neg (show 2 * k * (m + 1) + r ≠ 0 by nlinarith)]
    by_cases h0 : r = 0
    · simp only [h0, if_true]; ring
    · simp [h0]

lemma coeff_t2 {k N : ℕ} (hk : 1 ≤ k) :
    coeff N (t2 k) = if k ∣ N ∧ Odd (N / k) then (-1) ^ k * (-1) ^ (N / k / 2) else 0 := by
  rw [t2, inverse_eq_of_mul' (mul_h2s hk), mul_assoc, show ((-1 : PowerSeries ℤ) ^ k) = C ((-1) ^ k) by simp,
    coeff_C_mul, coeff_X_pow_mul']
  by_cases hkN : k ≤ N
  · rw [if_pos hkN]
    obtain ⟨m, r, hr, hmr⟩ : ∃ m r, r < 2 * k ∧ N - k = 2 * k * m + r :=
      ⟨(N - k) / (2 * k), (N - k) % (2 * k), Nat.mod_lt _ (by omega), (Nat.div_add_mod _ _).symm⟩
    rw [hmr, h2s_eval hk m r hr]
    by_cases h0 : r = 0
    · subst h0
      have hN : N = k * (2 * m + 1) := by rw [Nat.sub_eq_iff_eq_add hkN] at hmr; rw [hmr]; ring
      have hdiv : N / k = 2 * m + 1 := by rw [hN, Nat.mul_div_cancel_left _ (by omega)]
      rw [if_pos rfl, if_pos ⟨⟨_, hN⟩, by rw [hdiv]; exact odd_two_mul_add_one m⟩, hdiv,
        show (2 * m + 1) / 2 = m by omega]
    · rw [if_neg h0, mul_zero, if_neg]
      rintro ⟨⟨t, ht⟩, hodd⟩
      rw [ht, Nat.mul_div_cancel_left _ (by omega)] at hodd
      obtain ⟨u, rfl⟩ := hodd
      have e : 2 * k * u = 2 * k * m + r := by
        rw [← hmr, ht, show k * (2 * u + 1) = 2 * k * u + k by ring, Nat.add_sub_cancel]
      have := congrArg (· % (2 * k)) e
      simp only [Nat.mul_mod_right, Nat.mul_add_mod, Nat.mod_eq_of_lt hr] at this
      exact h0 this.symm
  · rw [if_neg hkN, mul_zero, if_neg]
    rintro ⟨⟨t, ht⟩, hodd⟩
    rw [ht, Nat.mul_div_cancel_left _ (by omega)] at hodd
    obtain ⟨u, rfl⟩ := hodd
    apply hkN; rw [ht]; exact Nat.le_mul_of_pos_right _ (by omega)


lemma coeff_L2 {N : ℕ} (hN : 1 ≤ N) :
    (-1) ^ N * coeff N L2 = ∑ d ∈ N.divisors.filter Odd, (-1 : ℤ) ^ (d / 2) := by
  rw [L2, coeff_mk, map_sum]
  rw [sum_congr rfl fun i _ => coeff_t2 (k := i + 1) (N := N) (by omega)]
  simp only [ite_and]
  rw [sum_range_dvd (fun k => if Odd (N / k) then (-1 : ℤ) ^ k * (-1) ^ (N / k / 2) else 0) hN le_rfl]
  set f : ℕ → ℤ := fun e => if Odd e then (-1 : ℤ) ^ (N / e) * (-1) ^ (e / 2) else 0 with hf
  rw [show (∑ d ∈ N.divisors, if Odd (N / d) then (-1 : ℤ) ^ d * (-1) ^ (N / d / 2) else 0)
      = ∑ d ∈ N.divisors, f (N / d) from sum_congr rfl fun d hd => by
        rw [hf]; dsimp only; rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) (by omega)],
    Nat.sum_div_divisors N f, sum_filter, mul_sum]
  refine sum_congr rfl fun d hd => ?_
  have hdd := Nat.dvd_of_mem_divisors hd
  by_cases ho : Odd d
  · rw [if_pos ho, if_pos ho, ← mul_assoc, ← pow_add]
    obtain ⟨c, hc⟩ := hdd
    have hpar : Even (N + N / d) := by
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      rw [hc, Nat.mul_div_cancel_left _ hd0]
      obtain ⟨t, rfl⟩ := ho
      exact ⟨c * (t + 1), by ring⟩
    rw [hpar.neg_one_pow, one_mul]
  · rw [if_neg ho, if_neg ho, mul_zero]

/-- the box `[-N, N]²`. -/
noncomputable def box2 (N : ℕ) : Finset (ℤ × ℤ) := Icc (-(N : ℤ)) N ×ˢ Icc (-(N : ℤ)) N

/-- `r₂(N)`: the representations of `N` as an ordered sum of two squares of integers. -/
noncomputable def r2 (N : ℕ) : ℕ := ((box2 N).filter fun v => v.1 ^ 2 + v.2 ^ 2 = (N : ℤ)).card

lemma coeff_thN_sq (N : ℕ) : coeff N (thN N ^ 2) = (-1) ^ N * (r2 N : ℤ) := by
  rw [sq, thN, mul_sum_prod, map_sum, r2, card_eq_sum_ones, Nat.cast_sum, mul_sum, sum_filter]
  refine sum_congr rfl fun v _ => ?_
  obtain ⟨a, b⟩ := v
  simp only [fz]
  rw [show C ((-1 : ℤ) ^ a.natAbs) * X ^ (a.natAbs ^ 2) * (C ((-1 : ℤ) ^ b.natAbs) * X ^ (b.natAbs ^ 2))
      = C ((-1 : ℤ) ^ (a.natAbs ^ 2 + b.natAbs ^ 2)) * X ^ (a.natAbs ^ 2 + b.natAbs ^ 2) by
    rw [neg_one_pow_natAbs_sq a, neg_one_pow_natAbs_sq b]
    simp only [pow_add, map_mul]; ring,
    coeff_C_mul, coeff_X_pow]
  have hcast : (a.natAbs ^ 2 + b.natAbs ^ 2 = N) ↔ a ^ 2 + b ^ 2 = (N : ℤ) := by
    rw [← Int.natAbs_sq a, ← Int.natAbs_sq b]
    exact_mod_cast Iff.rfl
  by_cases h : a.natAbs ^ 2 + b.natAbs ^ 2 = N
  · rw [if_pos h.symm, if_pos (hcast.mp h), h]; simp
  · rw [if_neg (Ne.symm h), if_neg (fun h' => h (hcast.mpr h'))]; simp

/-- the odd-divisor character sum is `d₁(N) − d₃(N)`. -/
lemma chi_sum (N : ℕ) : ∑ d ∈ N.divisors.filter Odd, (-1 : ℤ) ^ (d / 2)
    = (N.divisors.filter (fun d => d % 4 = 1)).card - (N.divisors.filter (fun d => d % 4 = 3)).card := by
  have hsplit : N.divisors.filter Odd = N.divisors.filter (fun d => d % 4 = 1) ∪ N.divisors.filter (fun d => d % 4 = 3) := by
    ext d; simp only [mem_filter, mem_union, Nat.odd_iff]
    have : d % 2 = 1 ↔ d % 4 = 1 ∨ d % 4 = 3 := by omega
    tauto
  have hdisj : Disjoint (N.divisors.filter (fun d => d % 4 = 1)) (N.divisors.filter (fun d => d % 4 = 3)) := by
    rw [disjoint_filter]; intro d _ h1 h3; omega
  rw [hsplit, sum_union hdisj, card_eq_sum_ones, card_eq_sum_ones, Nat.cast_sum, Nat.cast_sum, sub_eq_add_neg,
    ← sum_neg_distrib]
  congr 1
  · refine sum_congr rfl fun d hd => ?_
    obtain ⟨-, hd4⟩ := mem_filter.mp hd
    rw [(show Even (d / 2) from ⟨d / 4, by omega⟩).neg_one_pow]; simp
  · refine sum_congr rfl fun d hd => ?_
    obtain ⟨-, hd4⟩ := mem_filter.mp hd
    rw [(show Odd (d / 2) from ⟨d / 4, by omega⟩).neg_one_pow]; simp

/-- **Jacobi's two-square theorem**: for `N ≥ 1`, the number of `(a,b) ∈ ℤ²` with `a² + b² = N` is
`4 (d₁(N) − d₃(N))`, where `dᵢ(N)` counts the divisors of `N` congruent to `i` mod 4. -/
theorem jacobi_two_squares {N : ℕ} (hN : 1 ≤ N) :
    (r2 N : ℤ) = 4 * ((N.divisors.filter (fun d => d % 4 = 1)).card
      - (N.divisors.filter (fun d => d % 4 = 3)).card : ℤ) := by
  have h1 : coeff N (thetaS 2 1 ^ 2) = coeff N (thN N ^ 2) := by
    have := congrArg (· ^ 2) (π_theta N)
    simp only [← map_pow] at this
    exact coeff_eq_of_dvd (π_eq_iff.mp this) (Nat.lt_succ_self N)
  rw [theta_sq, coeff_thN_sq, map_add, coeff_one, if_neg (by omega), zero_add,
    show (4 : PowerSeries ℤ) = C 4 by simp, coeff_C_mul] at h1
  have h2 := coeff_L2 hN
  rw [chi_sum] at h2
  have hsq : ((-1 : ℤ) ^ N) * (-1) ^ N = 1 := by rw [← mul_pow]; norm_num
  rw [← h2]
  linear_combination (-(-1 : ℤ) ^ N) * h1 - (r2 N : ℤ) * hsq

/-- `r2` counts all integer solutions. -/
theorem r2_eq_ncard (N : ℕ) : {v : ℤ × ℤ | v.1 ^ 2 + v.2 ^ 2 = (N : ℤ)}.ncard = r2 N := by
  rw [r2, ← Set.ncard_coe_finset]
  congr 1
  ext ⟨a, b⟩
  simp only [Set.mem_setOf_eq, coe_filter, box2, mem_product, mem_Icc]
  constructor
  · intro h
    have := Int.le_self_sq a; have := Int.le_self_sq (-a); have := Int.le_self_sq b; have := Int.le_self_sq (-b)
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, h⟩ <;> nlinarith [sq_nonneg a, sq_nonneg b]
  · exact fun h => h.2

end FourSquares
