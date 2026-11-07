/-
# Seventh pass, R2: the far part of `Σ'_p ∫ Fq`

The near set (for `P = ac`, `Q = bd`, `ℓ = Pm − Qn`) is

    Near = {(m,n) : ⌊T^{399/400}⌋ < m ≤ ⌊T^{401/400}⌋, 1 ≤ n ≤ P⌊T^{401/400}⌋ + ⌊T^{1/100}⌋,
            ℓ ≠ 0, |ℓ| ≤ ⌊T^{1/100}⌋}                                           (`nearSet`).

Every other term is bounded by `term_integral_bound` (A = 3) and `far_pt_real`; the majorant
sums by Rankin–Selberg (`sum_lam_sq_rpow_le`) and injectivity of `n ↦ ℓ`, `m ↦ ℓ` (`sum_gl_le`):

    Σ'_{p ∉ Near} ‖∫ Fq(p)‖ ≤ K (PQ)^6 T^{299/300}                          (`far_bound`).

Level 1.
-/
import RamanujanTau.SelbergKey7.FarCore

set_option autoImplicit false

namespace RamanujanTau.SelbergKey7

open Complex Finset RamanujanTau.SubconvexityCond RamanujanTau.SelbergKey RamanujanTau.SelbergKey4
  RamanujanTau.SelbergKey5
open scoped Real

/-- `M₁ = ⌊T^{1−ε}⌋`, `M₂ = ⌊T^{1+ε}⌋`, `K₀ = ⌊T^δ⌋` (ε = 1/400, δ = 1/100). -/
noncomputable def M1 (T : ℝ) : ℕ := ⌊T ^ (399 / 400 : ℝ)⌋₊
noncomputable def M2 (T : ℝ) : ℕ := ⌊T ^ (401 / 400 : ℝ)⌋₊
noncomputable def K0 (T : ℝ) : ℕ := ⌊T ^ (1 / 100 : ℝ)⌋₊

/-- The line index `ℓ = Pm − Qn`. -/
def ell (P Q : ℕ) (p : ℕ × ℕ) : ℤ := (P : ℤ) * p.1 - (Q : ℤ) * p.2

/-- The near set. -/
noncomputable def nearSet (P Q : ℕ) (T : ℝ) : Finset (ℕ × ℕ) :=
  ((Icc (M1 T + 1) (M2 T)) ×ˢ (Icc 1 (P * M2 T + K0 T))).filter
    fun p => ell P Q p ≠ 0 ∧ (ell P Q p).natAbs ≤ K0 T

/-- Outside the near set, an off-diagonal term is in one of the far ranges. -/
lemma far_of_not_near {P Q : ℕ} (hQ : 1 ≤ Q) {T : ℝ} (hT : 1 ≤ T) {m n : ℕ} (hn : 1 ≤ n)
    (hℓ : ell P Q (m, n) ≠ 0) (hp : (m, n) ∉ nearSet P Q T) :
    (m : ℝ) ≤ T ^ (399 / 400 : ℝ) ∨ T ^ (401 / 400 : ℝ) < m ∨
      T ^ (1 / 100 : ℝ) < |((ell P Q (m, n) : ℤ) : ℝ)| := by
  have hT0 : 0 ≤ T := by linarith
  by_cases h1 : m ≤ M1 T
  · left
    exact le_trans (by exact_mod_cast h1) (Nat.floor_le (Real.rpow_nonneg hT0 _))
  by_cases h2 : M2 T < m
  · right; left
    have := Nat.lt_floor_add_one (T ^ (401 / 400 : ℝ))
    have h3 : ((M2 T : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast h2
    unfold M2 at h3; linarith
  by_cases h3 : K0 T < (ell P Q (m, n)).natAbs
  · right; right
    have := Nat.lt_floor_add_one (T ^ (1 / 100 : ℝ))
    have h4 : ((K0 T : ℕ) : ℝ) + 1 ≤ ((ell P Q (m, n)).natAbs : ℝ) := by exact_mod_cast h3
    rw [Nat.cast_natAbs, Int.cast_abs] at h4
    unfold K0 at h4; linarith
  exfalso; apply hp
  push Not at h1 h2 h3
  unfold nearSet
  rw [mem_filter, mem_product, mem_Icc, mem_Icc]
  refine ⟨⟨⟨by omega, h2⟩, hn, ?_⟩, hℓ, h3⟩
  -- `n ≤ Qn = Pm − ℓ ≤ P M₂ + K₀`
  have e : (Q : ℤ) * n = P * m - ell P Q (m, n) := by unfold ell; ring
  have hab : -(ell P Q (m, n)) ≤ ((ell P Q (m, n)).natAbs : ℤ) := by
    rw [Int.natCast_natAbs]; exact neg_le_abs _
  have hPm : (P : ℤ) * m ≤ (P : ℤ) * (M2 T) := by
    have : (m : ℤ) ≤ M2 T := by exact_mod_cast h2
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hnQ : (n : ℤ) ≤ (Q : ℤ) * n := by
    have : (1 : ℤ) ≤ Q := by exact_mod_cast hQ
    nlinarith
  have h5 : (n : ℤ) ≤ ((P * M2 T + K0 T : ℕ) : ℤ) := by
    push_cast
    have : ((ell P Q (m, n)).natAbs : ℤ) ≤ K0 T := by exact_mod_cast h3
    linarith
  exact_mod_cast h5

/-- `Fq` vanishes on the diagonal and at `m = 0` or `n = 0`. -/
lemma Fq_eq_zero (T x v : ℝ) (q : ℕ × ℕ × ℕ × ℕ) (p : ℕ × ℕ)
    (h : isDiag q.1 q.2.1 q.2.2.1 q.2.2.2 p ∨ p.1 = 0 ∨ p.2 = 0) (t : ℝ) : Fq T x v q p t = 0 := by
  unfold Fq
  split_ifs with hd
  · simp
  · rcases h with h | h | h
    · exact absurd h hd
    · simp [sTerm, h, RamanujanTau.tauC, RamanujanTau.tau_zero]
    · simp [sTerm, h, RamanujanTau.tauC, RamanujanTau.tau_zero]

/-- The frequency in terms of `P = ac`, `Q = bd`. -/
lemma omg_bound (a b c d m n : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    |((b * d : ℕ) : ℝ) * n - ((a * c : ℕ) : ℝ) * m| /
        max (((b * d : ℕ) : ℝ) * n) (((a * c : ℕ) : ℝ) * m) ≤ |omg a b c d m n| := by
  have pos : ∀ k : ℕ, 1 ≤ k → (0 : ℝ) < k := fun k hk => by exact_mod_cast hk
  have h := RamanujanTau.SelbergKey6.abs_log_sub_ge
    (X := ((b * d : ℕ) : ℝ) * n) (Y := ((a * c : ℕ) : ℝ) * m)
    (by push_cast; have := pos b hb; have := pos d hd; have := pos n hn; positivity)
    (by push_cast; have := pos a ha; have := pos c hc; have := pos m hm; positivity)
  refine h.trans (le_of_eq ?_)
  congr 1
  unfold omg
  push_cast
  rw [Real.log_mul (by have := pos b hb; have := pos d hd; positivity) (pos n hn).ne',
    Real.log_mul (pos b hb).ne' (pos d hd).ne',
    Real.log_mul (by have := pos a ha; have := pos c hc; positivity) (pos m hm).ne',
    Real.log_mul (pos a ha).ne' (pos c hc).ne']
  ring

/-- The majorant. -/
noncomputable def Maj (P Q : ℕ) (p : ℕ × ℕ) : ℝ :=
  lam p.1 ^ 2 * (p.1 : ℝ) ^ (-(2001 / 2000 : ℝ)) * (p.2 : ℝ) ^ (-(2001 / 2000 : ℝ)) +
  lam p.2 ^ 2 * (p.1 : ℝ) ^ (-(2001 / 2000 : ℝ)) * (p.2 : ℝ) ^ (-(2001 / 2000 : ℝ)) +
  lam p.1 ^ 2 * (p.1 : ℝ) ^ (-(2001 / 2000 : ℝ)) * gl (ell P Q p) +
  lam p.2 ^ 2 * (p.2 : ℝ) ^ (-(2001 / 2000 : ℝ)) * gl (ell P Q p)

lemma Maj_nonneg (P Q : ℕ) (p : ℕ × ℕ) : 0 ≤ Maj P Q p := by
  unfold Maj
  have := gl_nonneg (ell P Q p)
  have h1 : 0 ≤ (p.1 : ℝ) ^ (-(2001 / 2000 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h2 : 0 ≤ (p.2 : ℝ) ^ (-(2001 / 2000 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  positivity

/-- **Far pointwise bound.** -/
lemma far_pt : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b c d : ℕ) (T x v : ℝ), 1 ≤ a → 1 ≤ b → 1 ≤ c → 1 ≤ d →
    1 ≤ T → 0 ≤ x → x ≤ 1 → |v| ≤ 1 → ∀ p : ℕ × ℕ, p ∉ nearSet (a * c) (b * d) T →
      ‖∫ t in (T / 2)..(3 * T), Fq T x v (a, b, c, d) p t‖ ≤
        C * (((a * c : ℕ) : ℝ) * ((b * d : ℕ) : ℝ)) ^ 6 * T ^ (299 / 300 : ℝ) * Maj (a * c) (b * d) p := by
  obtain ⟨CA, hCA0, hCA⟩ := term_integral_bound 3 (by norm_num)
  refine ⟨256 * CA, by positivity, fun a b c d T x v ha hb hc hd hT hx0 hx1 hv p hp => ?_⟩
  obtain ⟨m, n⟩ := p
  have hR0 : 0 ≤ 256 * CA * (((a * c : ℕ) : ℝ) * ((b * d : ℕ) : ℝ)) ^ 6 * T ^ (299 / 300 : ℝ) *
      Maj (a * c) (b * d) (m, n) := by
    have := Maj_nonneg (a * c) (b * d) (m, n)
    have : 0 ≤ T ^ (299 / 300 : ℝ) := Real.rpow_nonneg (by linarith) _
    positivity
  by_cases h0 : isDiag a b c d (m, n) ∨ m = 0 ∨ n = 0
  · have : ∀ t, Fq T x v (a, b, c, d) (m, n) t = 0 := Fq_eq_zero T x v (a, b, c, d) (m, n) h0
    simp only [this, intervalIntegral.integral_zero, norm_zero]
    exact hR0
  push Not at h0
  obtain ⟨hdiag, hm0, hn0⟩ := h0
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 hm0
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn0
  have hFq : (fun t => Fq T x v (a, b, c, d) (m, n) t) = fun t => ((phiT T t : ℝ) : ℂ) *
      (Ush (t + x) (t + x + v) * (eph a b (t + x) * eph c d (t + x + v) *
        sTerm (t + x) (t + x + v) (m, n))) := by
    funext t; unfold Fq; simp only; rw [if_neg hdiag]
  rw [hFq]
  refine (hCA a b c d m n T x v hm hn hT hx0 hx1 hv).trans ?_
  rw [abs_tau_mul_rpow hm hn]
  have hℓ0 : ell (a * c) (b * d) (m, n) ≠ 0 := by
    intro h; apply hdiag; unfold isDiag ell at *; simp only at h ⊢
    have : ((a * c : ℕ) : ℤ) * m = ((b * d : ℕ) : ℤ) * n := by linarith
    have h2 : a * c * m = b * d * n := by exact_mod_cast this
    calc n * b * d = b * d * n := by ring
      _ = a * c * m := h2.symm
      _ = m * a * c := by ring
  have hfar := far_of_not_near (P := a * c) (Q := b * d) (Nat.one_le_iff_ne_zero.2 (by positivity))
    hT hn hℓ0 hp
  have hℓ : ((ell (a * c) (b * d) (m, n) : ℤ) : ℝ) = ((a * c : ℕ) : ℝ) * m - ((b * d : ℕ) : ℝ) * n := by
    unfold ell; push_cast; ring
  have key := far_pt_real (T := T) (P := ((a * c : ℕ) : ℝ)) (Q := ((b * d : ℕ) : ℝ)) (m := m) (n := n)
    (lm := |lam m|) (ln := |lam n|) (ω := omg a b c d m n) hT
    (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity))
    (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity))
    (by exact_mod_cast hm) (by exact_mod_cast hn) hℓ hℓ0 (abs_nonneg _) (abs_nonneg _)
    (omg_bound a b c d m n ha hb hc hd hm hn) hfar
  rw [sq_abs, sq_abs] at key
  have hmn : ((m : ℝ) * n) ^ (-(2001 / 2000 : ℝ)) =
      (m : ℝ) ^ (-(2001 / 2000 : ℝ)) * (n : ℝ) ^ (-(2001 / 2000 : ℝ)) :=
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [hmn] at key
  have eM : Maj (a * c) (b * d) (m, n) = (lam m ^ 2 + lam n ^ 2) *
      ((m : ℝ) ^ (-(2001 / 2000 : ℝ)) * (n : ℝ) ^ (-(2001 / 2000 : ℝ))) +
      lam m ^ 2 * (m : ℝ) ^ (-(2001 / 2000 : ℝ)) * gl (ell (a * c) (b * d) (m, n)) +
      lam n ^ 2 * (n : ℝ) ^ (-(2001 / 2000 : ℝ)) * gl (ell (a * c) (b * d) (m, n)) := by
    unfold Maj; simp only; ring
  rw [eM]
  have hMw : min T (if omg a b c d m n = 0 then T else 1 / (omg a b c d m n ^ 2 * T)) =
      Mw T (omg a b c d m n) := rfl
  rw [hMw]
  calc |lam m| * |lam n| * ((m : ℝ) * n) ^ (-(1 / 2) : ℝ) *
        (CA * (1 + 4 * π ^ 2 * m * n / T ^ 2) ^ (-(3 : ℝ))) * Mw T (omg a b c d m n)
      = CA * (|lam m| * |lam n| * (((m : ℝ) * n) ^ (-(1 / 2) : ℝ) *
          (1 + 4 * π ^ 2 * m * n / T ^ 2) ^ (-(3 : ℝ)) * Mw T (omg a b c d m n))) := by ring
    _ ≤ CA * (256 * (((a * c : ℕ) : ℝ) * ((b * d : ℕ) : ℝ)) ^ 6 * T ^ (299 / 300 : ℝ) * _) :=
        mul_le_mul_of_nonneg_left key hCA0
    _ = _ := by ring

/-- **The majorant sums.** -/
lemma sum_box_Maj : ∃ K : ℝ, 0 ≤ K ∧ ∀ P Q : ℕ, 1 ≤ P → 1 ≤ Q → ∀ N : ℕ,
    ∑ p ∈ range N ×ˢ range N, Maj P Q p ≤ K := by
  obtain ⟨S, hS0, hS⟩ := sum_lam_sq_rpow_le (σ := 2001 / 2000) (by norm_num)
  obtain ⟨Z, hZ0, hZ⟩ := sum_rpow_le (σ := 2001 / 2000) (by norm_num)
  obtain ⟨G, hG0, hG⟩ := sum_gl_le
  refine ⟨2 * S * Z + 2 * S * G, by positivity, fun P Q hP hQ N => ?_⟩
  set σ : ℝ := 2001 / 2000
  have hr : ∀ k : ℕ, 0 ≤ (k : ℝ) ^ (-σ) := fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hl : ∀ k : ℕ, 0 ≤ lam k ^ 2 * (k : ℝ) ^ (-σ) := fun k => mul_nonneg (sq_nonneg _) (hr k)
  rw [sum_product]
  unfold Maj
  simp only [sum_add_distrib]
  have t1 : ∑ m ∈ range N, ∑ n ∈ range N, lam m ^ 2 * (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) ≤ S * Z := by
    simp only [← mul_sum]
    calc ∑ m ∈ range N, lam m ^ 2 * (m : ℝ) ^ (-σ) * ∑ n ∈ range N, (n : ℝ) ^ (-σ)
        ≤ ∑ m ∈ range N, lam m ^ 2 * (m : ℝ) ^ (-σ) * Z :=
          sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hZ N) (hl m)
      _ = (∑ m ∈ range N, lam m ^ 2 * (m : ℝ) ^ (-σ)) * Z := by rw [sum_mul]
      _ ≤ S * Z := mul_le_mul_of_nonneg_right (hS N) hZ0
  have t2 : ∑ m ∈ range N, ∑ n ∈ range N, lam n ^ 2 * (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) ≤ S * Z := by
    have e : ∀ m n : ℕ, lam n ^ 2 * (m : ℝ) ^ (-σ) * (n : ℝ) ^ (-σ) =
        (m : ℝ) ^ (-σ) * (lam n ^ 2 * (n : ℝ) ^ (-σ)) := fun m n => by ring
    simp only [e, ← mul_sum, ← sum_mul]
    calc (∑ m ∈ range N, (m : ℝ) ^ (-σ)) * ∑ n ∈ range N, lam n ^ 2 * (n : ℝ) ^ (-σ)
        ≤ Z * S := mul_le_mul (hZ N) (hS N) (sum_nonneg fun n _ => hl n) hZ0
      _ = S * Z := by ring
  have t3 : ∑ m ∈ range N, ∑ n ∈ range N, lam m ^ 2 * (m : ℝ) ^ (-σ) * gl (ell P Q (m, n)) ≤
      S * G := by
    simp only [← mul_sum]
    calc ∑ m ∈ range N, lam m ^ 2 * (m : ℝ) ^ (-σ) * ∑ n ∈ range N, gl (ell P Q (m, n))
        ≤ ∑ m ∈ range N, lam m ^ 2 * (m : ℝ) ^ (-σ) * G := by
          refine sum_le_sum fun m _ => mul_le_mul_of_nonneg_left ?_ (hl m)
          refine hG (range N) (fun n => ell P Q (m, n)) fun n₁ _ n₂ _ h => ?_
          unfold ell at h; simp only at h
          have hQ' : (Q : ℤ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
          have : (Q : ℤ) * n₁ = Q * n₂ := by linarith
          exact_mod_cast mul_left_cancel₀ hQ' this
      _ = (∑ m ∈ range N, lam m ^ 2 * (m : ℝ) ^ (-σ)) * G := by rw [sum_mul]
      _ ≤ S * G := mul_le_mul_of_nonneg_right (hS N) hG0
  have t4 : ∑ m ∈ range N, ∑ n ∈ range N, lam n ^ 2 * (n : ℝ) ^ (-σ) * gl (ell P Q (m, n)) ≤
      S * G := by
    rw [sum_comm]
    simp only [← mul_sum]
    calc ∑ n ∈ range N, lam n ^ 2 * (n : ℝ) ^ (-σ) * ∑ m ∈ range N, gl (ell P Q (m, n))
        ≤ ∑ n ∈ range N, lam n ^ 2 * (n : ℝ) ^ (-σ) * G := by
          refine sum_le_sum fun n _ => mul_le_mul_of_nonneg_left ?_ (hl n)
          refine hG (range N) (fun m => ell P Q (m, n)) fun m₁ _ m₂ _ h => ?_
          unfold ell at h; simp only at h
          have hP' : (P : ℤ) ≠ 0 := by exact_mod_cast (show P ≠ 0 by omega)
          have : (P : ℤ) * m₁ = P * m₂ := by linarith
          exact_mod_cast mul_left_cancel₀ hP' this
      _ = (∑ n ∈ range N, lam n ^ 2 * (n : ℝ) ^ (-σ)) * G := by rw [sum_mul]
      _ ≤ S * G := mul_le_mul_of_nonneg_right (hS N) hG0
  linarith

/-- **R2: the far part.** -/
theorem far_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ (a b c d : ℕ) (T x v : ℝ), 1 ≤ a → 1 ≤ b → 1 ≤ c → 1 ≤ d →
    1 ≤ T → 0 ≤ x → x ≤ 1 → |v| ≤ 1 →
      ∑' p : ℕ × ℕ, ‖((↑(nearSet (a * c) (b * d) T) : Set (ℕ × ℕ))ᶜ).indicator
          (fun p => ∫ t in (T / 2)..(3 * T), Fq T x v (a, b, c, d) p t) p‖ ≤
        K * (((a * c : ℕ) : ℝ) * ((b * d : ℕ) : ℝ)) ^ 6 * T ^ (299 / 300 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := far_pt
  obtain ⟨K, hK0, hK⟩ := sum_box_Maj
  refine ⟨C * K, by positivity, fun a b c d T x v ha hb hc hd hT hx0 hx1 hv => ?_⟩
  set W := C * (((a * c : ℕ) : ℝ) * ((b * d : ℕ) : ℝ)) ^ 6 * T ^ (299 / 300 : ℝ)
  have hW0 : 0 ≤ W := by
    have : 0 ≤ T ^ (299 / 300 : ℝ) := Real.rpow_nonneg (by linarith) _
    positivity
  have hpt : ∀ p : ℕ × ℕ, ‖((↑(nearSet (a * c) (b * d) T) : Set (ℕ × ℕ))ᶜ).indicator
      (fun p => ∫ t in (T / 2)..(3 * T), Fq T x v (a, b, c, d) p t) p‖ ≤ W * Maj (a * c) (b * d) p := by
    intro p
    by_cases hp : p ∈ nearSet (a * c) (b * d) T
    · rw [Set.indicator_of_notMem (by simpa using hp), norm_zero]
      exact mul_nonneg hW0 (Maj_nonneg _ _ _)
    · rw [Set.indicator_of_mem (by simpa using hp)]
      exact hC a b c d T x v ha hb hc hd hT hx0 hx1 hv p hp
  have hP : 1 ≤ a * c := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hQ : 1 ≤ b * d := Nat.one_le_iff_ne_zero.2 (by positivity)
  have e : C * K * (((a * c : ℕ) : ℝ) * ((b * d : ℕ) : ℝ)) ^ 6 * T ^ (299 / 300 : ℝ) = W * K := by
    simp only [W]; ring
  rw [e]
  refine Real.tsum_le_of_sum_le (fun p => norm_nonneg _) fun u => ?_
  set N := u.sup (fun p => p.1 + p.2) + 1
  have hu : u ⊆ range N ×ˢ range N := by
    intro p hp
    have := Finset.le_sup (f := fun p : ℕ × ℕ => p.1 + p.2) hp
    simp only at this
    rw [mem_product, mem_range, mem_range]
    constructor <;> omega
  calc ∑ p ∈ u, _ ≤ ∑ p ∈ u, W * Maj (a * c) (b * d) p := sum_le_sum fun p _ => hpt p
    _ ≤ ∑ p ∈ range N ×ˢ range N, W * Maj (a * c) (b * d) p :=
        sum_le_sum_of_subset_of_nonneg hu fun p _ _ => mul_nonneg hW0 (Maj_nonneg _ _ _)
    _ = W * ∑ p ∈ range N ×ˢ range N, Maj (a * c) (b * d) p := by rw [mul_sum]
    _ ≤ W * K := mul_le_mul_of_nonneg_left (hK _ _ hP hQ N) hW0

end RamanujanTau.SelbergKey7
