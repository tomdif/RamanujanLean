/-
# Seventh pass, far part: the real-variable core

For one off-diagonal term `(m,n)` with `ℓ = Pm − Qn ≠ 0` outside the near set
`{T^{1−ε} < m ≤ T^{1+ε}, |ℓ| ≤ T^δ}` (ε = 1/400, δ = 1/100), the bound
`(mn)^{−1/2} (1+4π²mn/T²)^{−3} min(T, 1/(ω²T))` with `|ω| ≥ |ℓ|/max(Pm,Qn)` is turned into
the Rankin–Selberg-summable majorant (σ = 2001/2000, η = 1/300)

    |λ(m)λ(n)| Θ ≤ 256 (PQ)^6 T^{1−η} [(λ(m)²+λ(n)²)(mn)^{−σ} + λ(m)² m^{−σ} g(ℓ) + λ(n)² n^{−σ} g(ℓ)].

Level 1.
-/
import RamanujanTau.SelbergKey7.Basic

set_option autoImplicit false

namespace RamanujanTau.SelbergKey7

open scoped Real

/-- The frequency factor `min(T, 1/(ω²T))`. -/
noncomputable def Mw (T ω : ℝ) : ℝ := min T (if ω = 0 then T else 1 / (ω ^ 2 * T))

lemma Mw_le_of {T ω X : ℝ} (hT : 0 < T) (hX : 0 < X) (hω : X ≤ |ω|) : Mw T ω ≤ 1 / (X ^ 2 * T) := by
  have hω0 : ω ≠ 0 := by intro h; rw [h, abs_zero] at hω; linarith
  unfold Mw
  rw [if_neg hω0]
  refine (min_le_right _ _).trans ?_
  have : X ^ 2 ≤ ω ^ 2 := by rw [← sq_abs ω]; exact pow_le_pow_left₀ hX.le hω 2
  exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right this hT.le)

lemma Mw_nonneg {T ω : ℝ} (hT : 0 < T) : 0 ≤ Mw T ω := by
  unfold Mw; split_ifs
  · rw [min_self]; exact hT.le
  · exact le_min hT.le (by positivity)

/-- Off the line: `|ω| ≥ 1/2`, so `min(T, 1/(ω²T)) ≤ 4/T`. -/
lemma Mw_off {T ω Y Z : ℝ} (hT : 0 < T) (hY : 0 < Y) (hZ : 0 < Z)
    (hω : |Z - Y| / max Z Y ≤ |ω|) (hoff : 2 * Y ≤ Z ∨ 2 * Z ≤ Y) : Mw T ω ≤ 4 / T := by
  have h12 : 1 / 2 ≤ |Z - Y| / max Z Y := by
    rcases hoff with h | h
    · rw [max_eq_left (by linarith), abs_of_nonneg (by linarith), le_div_iff₀ (by linarith)]
      linarith
    · rw [max_eq_right (by linarith), abs_of_nonpos (by linarith), le_div_iff₀ (by linarith)]
      linarith
  refine (Mw_le_of hT (by norm_num) (h12.trans hω)).trans (le_of_eq ?_)
  field_simp; norm_num

/-- Near the line: `min(T, 1/(ω²T)) ≤ 4Y²/((Z−Y)²T)` (`Y = Pm`, `Z = Qn`). -/
lemma Mw_near {T ω Y Z : ℝ} (hT : 0 < T) (hY : 0 < Y) (hZ : 0 < Z) (hYZ : Y ≠ Z)
    (hω : |Z - Y| / max Z Y ≤ |ω|) (hnear : Z < 2 * Y) :
    Mw T ω ≤ 4 * Y ^ 2 / ((Z - Y) ^ 2 * T) := by
  have hd : 0 < |Z - Y| := abs_pos.2 (sub_ne_zero.2 hYZ.symm)
  have h1 : |Z - Y| / (2 * Y) ≤ |ω| :=
    le_trans (div_le_div_of_nonneg_left hd.le (by positivity)
      (max_le hnear.le (by linarith))) hω
  refine (Mw_le_of hT (by positivity) h1).trans (le_of_eq ?_)
  rw [div_pow, ← sq_abs (Z - Y)]
  field_simp
  norm_num

/-- **Off the line.** -/
lemma theta_off {T m n : ℝ} (hT : 1 ≤ T) (hm : 0 < m) (hn : 0 < n) {D M : ℝ}
    (hD : D ≤ (T ^ 2 / (m * n)) ^ ((2001 / 2000 : ℝ) - 1 / 2)) (hM0 : 0 ≤ M) (hM : M ≤ 4 / T) :
    (m * n) ^ (-(1 / 2) : ℝ) * D * M ≤ 4 * T ^ ((1 : ℝ) / 1000) * (m * n) ^ (-(2001 / 2000 : ℝ)) := by
  have hT0 : 0 < T := by linarith
  have hw : 0 < m * n := mul_pos hm hn
  set w := m * n
  have hwr : 0 ≤ w ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hw.le _
  calc w ^ (-(1 / 2) : ℝ) * D * M ≤ w ^ (-(1 / 2) : ℝ) * (T ^ 2 / w) ^ ((2001 / 2000 : ℝ) - 1 / 2) *
        (4 / T) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hD hwr) hM hM0
          (mul_nonneg hwr (Real.rpow_nonneg (by positivity) _))
    _ = _ := by
        rw [Real.div_rpow (by positivity) hw.le, ← Real.rpow_natCast T 2, ← Real.rpow_mul hT0.le]
        have e1 : T ^ (((2 : ℕ) : ℝ) * ((2001 / 2000 : ℝ) - 1 / 2)) = T ^ ((1 : ℝ) / 1000) * T := by
          rw [← Real.rpow_add_one hT0.ne']; norm_num
        have e2 : w ^ (-(2001 / 2000 : ℝ)) = w ^ (-(1 / 2) : ℝ) / w ^ ((2001 / 2000 : ℝ) - 1 / 2) := by
          have h3 : w ^ (2001 / 2000 : ℝ) = w ^ (1 / 2 : ℝ) * w ^ ((2001 / 2000 : ℝ) - 1 / 2) := by
            rw [← Real.rpow_add hw]; norm_num
          rw [Real.rpow_neg hw.le, Real.rpow_neg hw.le, h3]; field_simp
        rw [e1, e2]
        field_simp

/-- `T^a · m^{−k} ≤ T^b · m^{−σ}` from `m ≥ T^c` (`c > 0`, `k ≥ σ`), when `a + c(σ−k) ≤ b`. -/
lemma pow_trade_lo {T m a b c k σ : ℝ} (hT : 1 ≤ T) (hm : T ^ c ≤ m) (hkσ : σ ≤ k)
    (hab : a + c * (σ - k) ≤ b) : T ^ a * m ^ (-k) ≤ T ^ b * m ^ (-σ) := by
  have hT0 : 0 < T := by linarith
  have hTc : 0 < T ^ c := Real.rpow_pos_of_pos hT0 c
  have hm0 : 0 < m := lt_of_lt_of_le hTc hm
  have e : m ^ (-k) = m ^ (-σ) * m ^ (σ - k) := by rw [← Real.rpow_add hm0]; ring_nf
  have h1 : m ^ (σ - k) ≤ T ^ (c * (σ - k)) := by
    rw [Real.rpow_mul hT0.le]
    exact Real.rpow_le_rpow_of_nonpos hTc hm (by linarith)
  have h2 : T ^ a * T ^ (c * (σ - k)) ≤ T ^ b := by
    rw [← Real.rpow_add hT0]; exact Real.rpow_le_rpow_of_exponent_le hT hab
  rw [e]
  have hmσ : 0 ≤ m ^ (-σ) := Real.rpow_nonneg hm0.le _
  calc T ^ a * (m ^ (-σ) * m ^ (σ - k)) = m ^ (-σ) * (T ^ a * m ^ (σ - k)) := by ring
    _ ≤ m ^ (-σ) * (T ^ a * T ^ (c * (σ - k))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hT0.le _)) hmσ
    _ ≤ m ^ (-σ) * T ^ b := mul_le_mul_of_nonneg_left h2 hmσ
    _ = _ := by ring

/-- `T^a · m^{j} ≤ T^b · m^{−σ}` from `0 < m ≤ T^c` (`c ≥ 0`, `j + σ ≥ 0`), when `a + c(j+σ) ≤ b`. -/
lemma pow_trade_hi {T m a b c j σ : ℝ} (hT : 1 ≤ T) (hm0 : 0 < m) (hm : m ≤ T ^ c) (hjσ : 0 ≤ j + σ)
    (hab : a + c * (j + σ) ≤ b) : T ^ a * m ^ j ≤ T ^ b * m ^ (-σ) := by
  have hT0 : 0 < T := by linarith
  have e : m ^ j = m ^ (-σ) * m ^ (j + σ) := by rw [← Real.rpow_add hm0]; ring_nf
  have h1 : m ^ (j + σ) ≤ T ^ (c * (j + σ)) := by
    rw [Real.rpow_mul hT0.le]
    exact Real.rpow_le_rpow hm0.le hm hjσ
  have h2 : T ^ a * T ^ (c * (j + σ)) ≤ T ^ b := by
    rw [← Real.rpow_add hT0]; exact Real.rpow_le_rpow_of_exponent_le hT hab
  rw [e]
  have hmσ : 0 ≤ m ^ (-σ) := Real.rpow_nonneg hm0.le _
  calc T ^ a * (m ^ (-σ) * m ^ (j + σ)) = m ^ (-σ) * (T ^ a * m ^ (j + σ)) := by ring
    _ ≤ m ^ (-σ) * (T ^ a * T ^ (c * (j + σ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hT0.le _)) hmσ
    _ ≤ m ^ (-σ) * T ^ b := mul_le_mul_of_nonneg_left h2 hmσ
    _ = _ := by ring

lemma three_le_mul {s D M s' D' M' : ℝ} (hs : 0 ≤ s) (hD : 0 ≤ D) (hM : 0 ≤ M) (hs' : s ≤ s')
    (hD' : D ≤ D') (hM' : M ≤ M') : s * D * M ≤ s' * D' * M' :=
  mul_le_mul (mul_le_mul hs' hD' hD (hs.trans hs')) hM' hM
    (mul_nonneg (hs.trans hs') (hD.trans hD'))

/-- **Near the line, `m > T^{1+ε}`**. -/
lemma theta_F3 {T m P Q L g s D M : ℝ} (hT : 1 ≤ T) (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hL : 1 ≤ L)
    (hm : T ^ (401 / 400 : ℝ) ≤ m) (hg : 1 / L ^ 2 ≤ g)
    (hs0 : 0 ≤ s) (hD0 : 0 ≤ D) (hM0 : 0 ≤ M) (hs : s ≤ 2 * Q / m)
    (hD : D ≤ (2 * Q * T ^ 2 / m ^ 2) ^ 3) (hM : M ≤ 4 * (P * m) ^ 2 / (L ^ 2 * T)) :
    s * D * M ≤ 64 * (P * Q) ^ 4 * T ^ (299 / 300 : ℝ) * m ^ (-(2001 / 2000 : ℝ)) * g := by
  have hT0 : 0 < T := by linarith
  have hm0 : 0 < m := lt_of_lt_of_le (Real.rpow_pos_of_pos hT0 _) hm
  have h1 := three_le_mul hs0 hD0 hM0 hs hD hM
  have key : T ^ (5 : ℝ) * m ^ (-(5 : ℝ)) ≤ T ^ (299 / 300 : ℝ) * m ^ (-(2001 / 2000 : ℝ)) :=
    pow_trade_lo hT hm (by norm_num) (by norm_num)
  have e : 2 * Q / m * (2 * Q * T ^ 2 / m ^ 2) ^ 3 * (4 * (P * m) ^ 2 / (L ^ 2 * T)) =
      64 * Q ^ 4 * P ^ 2 * (T ^ (5 : ℝ) * m ^ (-(5 : ℝ))) * (1 / L ^ 2) := by
    rw [Real.rpow_neg hm0.le, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.rpow_natCast]
    field_simp; ring
  rw [e] at h1
  refine h1.trans ?_
  have hPQ : Q ^ 4 * P ^ 2 ≤ (P * Q) ^ 4 := by
    rw [mul_pow]; nlinarith [pow_le_pow_right₀ hP (show 2 ≤ 4 by norm_num), pow_pos (by linarith : (0:ℝ) < Q) 4]
  have hL2 : 0 ≤ 1 / L ^ 2 := by positivity
  have hX : 0 ≤ T ^ (5 : ℝ) * m ^ (-(5 : ℝ)) := by positivity
  calc 64 * Q ^ 4 * P ^ 2 * (T ^ (5 : ℝ) * m ^ (-(5 : ℝ))) * (1 / L ^ 2)
      = 64 * (Q ^ 4 * P ^ 2) * (T ^ (5 : ℝ) * m ^ (-(5 : ℝ))) * (1 / L ^ 2) := by ring
    _ ≤ 64 * (P * Q) ^ 4 * (T ^ (299 / 300 : ℝ) * m ^ (-(2001 / 2000 : ℝ))) * g := by
        gcongr
    _ = _ := by ring

/-- **Near the line, `m ≤ T^{1−ε}`**. -/
lemma theta_F2 {T m P Q L g s D M : ℝ} (hT : 1 ≤ T) (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hL : 1 ≤ L)
    (hm0 : 0 < m) (hm : m ≤ T ^ (399 / 400 : ℝ)) (hg : 1 / L ^ 2 ≤ g)
    (hs0 : 0 ≤ s) (hD0 : 0 ≤ D) (hM0 : 0 ≤ M) (hs : s ≤ 2 * Q / m)
    (hD : D ≤ 1) (hM : M ≤ 4 * (P * m) ^ 2 / (L ^ 2 * T)) :
    s * D * M ≤ 64 * (P * Q) ^ 4 * T ^ (299 / 300 : ℝ) * m ^ (-(2001 / 2000 : ℝ)) * g := by
  have hT0 : 0 < T := by linarith
  have h1 := three_le_mul hs0 hD0 hM0 hs hD hM
  have key : T ^ (-1 : ℝ) * m ^ (1 : ℝ) ≤ T ^ (299 / 300 : ℝ) * m ^ (-(2001 / 2000 : ℝ)) :=
    pow_trade_hi hT hm0 hm (by norm_num) (by norm_num)
  have e : 2 * Q / m * 1 * (4 * (P * m) ^ 2 / (L ^ 2 * T)) =
      8 * Q * P ^ 2 * (T ^ (-1 : ℝ) * m ^ (1 : ℝ)) * (1 / L ^ 2) := by
    rw [Real.rpow_neg_one, Real.rpow_one]
    field_simp; ring
  rw [e] at h1
  refine h1.trans ?_
  have hPQ : 8 * Q * P ^ 2 ≤ 64 * (P * Q) ^ 4 := by
    rw [mul_pow]
    have h1 : Q ≤ Q ^ 4 := by nlinarith [pow_le_pow_right₀ hQ (show 1 ≤ 4 by norm_num)]
    have h2 : P ^ 2 ≤ P ^ 4 := pow_le_pow_right₀ hP (by norm_num)
    have : Q * P ^ 2 ≤ Q ^ 4 * P ^ 4 := mul_le_mul h1 h2 (by positivity) (by positivity)
    nlinarith
  have hX : 0 ≤ T ^ (-1 : ℝ) * m ^ (1 : ℝ) := by positivity
  calc 8 * Q * P ^ 2 * (T ^ (-1 : ℝ) * m ^ (1 : ℝ)) * (1 / L ^ 2)
      ≤ 64 * (P * Q) ^ 4 * (T ^ (299 / 300 : ℝ) * m ^ (-(2001 / 2000 : ℝ))) * g := by
        gcongr
    _ = _ := by ring

/-- **Near the line, `m ≤ T^{1+ε}`, `|ℓ| > T^δ`**. -/
lemma theta_F1 {T m P Q L g s D M : ℝ} (hT : 1 ≤ T) (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hL : 1 ≤ L)
    (hm0 : 0 < m) (hm : m ≤ T ^ (401 / 400 : ℝ)) (hLT : T ^ (1 / 100 : ℝ) ≤ L)
    (hg : 1 / L ^ 2 ≤ L ^ (-(1 / 2 : ℝ)) * g) (hg0 : 0 ≤ g)
    (hs0 : 0 ≤ s) (hD0 : 0 ≤ D) (hM0 : 0 ≤ M) (hs : s ≤ 2 * Q / m)
    (hD : D ≤ 2 * Q * T ^ 2 / m ^ 2) (hM : M ≤ 4 * (P * m) ^ 2 / (L ^ 2 * T)) :
    s * D * M ≤ 64 * (P * Q) ^ 4 * T ^ (299 / 300 : ℝ) * m ^ (-(2001 / 2000 : ℝ)) * g := by
  have hT0 : 0 < T := by linarith
  have h1 := three_le_mul hs0 hD0 hM0 hs hD hM
  have key : T ^ (1 - 1 / 200 : ℝ) * m ^ (-1 : ℝ) ≤ T ^ (299 / 300 : ℝ) * m ^ (-(2001 / 2000 : ℝ)) :=
    pow_trade_hi hT hm0 hm (by norm_num) (by norm_num)
  have hLg : 1 / L ^ 2 ≤ T ^ (-(1 / 200) : ℝ) * g := by
    refine hg.trans (mul_le_mul_of_nonneg_right ?_ hg0)
    calc L ^ (-(1 / 2 : ℝ)) ≤ (T ^ (1 / 100 : ℝ)) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hT0 _) hLT (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hT0.le]; norm_num
  have e : 2 * Q / m * (2 * Q * T ^ 2 / m ^ 2) * (4 * (P * m) ^ 2 / (L ^ 2 * T)) =
      16 * Q ^ 2 * P ^ 2 * (T ^ (1 : ℝ) * m ^ (-1 : ℝ)) * (1 / L ^ 2) := by
    rw [Real.rpow_neg_one, Real.rpow_one]
    field_simp; ring
  rw [e] at h1
  refine h1.trans ?_
  have hPQ : 16 * Q ^ 2 * P ^ 2 ≤ 64 * (P * Q) ^ 4 := by
    rw [mul_pow]
    have h1 : Q ^ 2 ≤ Q ^ 4 := pow_le_pow_right₀ hQ (by norm_num)
    have h2 : P ^ 2 ≤ P ^ 4 := pow_le_pow_right₀ hP (by norm_num)
    have : Q ^ 2 * P ^ 2 ≤ Q ^ 4 * P ^ 4 := mul_le_mul h1 h2 (by positivity) (by positivity)
    nlinarith
  have hX : 0 ≤ T ^ (1 : ℝ) * m ^ (-1 : ℝ) := by positivity
  have e2 : T ^ (1 : ℝ) * m ^ (-1 : ℝ) * (T ^ (-(1 / 200) : ℝ) * g) =
      T ^ (1 - 1 / 200 : ℝ) * m ^ (-1 : ℝ) * g := by
    rw [Real.rpow_sub hT0, Real.rpow_neg hT0.le]; field_simp
  calc 16 * Q ^ 2 * P ^ 2 * (T ^ (1 : ℝ) * m ^ (-1 : ℝ)) * (1 / L ^ 2)
      ≤ 16 * Q ^ 2 * P ^ 2 * (T ^ (1 : ℝ) * m ^ (-1 : ℝ) * (T ^ (-(1 / 200) : ℝ) * g)) := by
        rw [mul_assoc (16 * Q ^ 2 * P ^ 2)]; gcongr
    _ = 16 * Q ^ 2 * P ^ 2 * (T ^ (1 - 1 / 200 : ℝ) * m ^ (-1 : ℝ)) * g := by rw [e2]; ring
    _ ≤ 64 * (P * Q) ^ 4 * (T ^ (299 / 300 : ℝ) * m ^ (-(2001 / 2000 : ℝ))) * g := by
        gcongr
    _ = _ := by ring

lemma inv_sq_le_gl' {ℓ : ℤ} (hℓ : ℓ ≠ 0) : 1 / |(ℓ : ℝ)| ^ 2 ≤ gl ℓ := by
  rw [sq_abs]; exact inv_sq_le_gl hℓ

lemma inv_sq_le_gl_mul' {ℓ : ℤ} {L : ℝ} (hL : 0 < L) (hℓ : L ≤ |(ℓ : ℝ)|) :
    1 / |(ℓ : ℝ)| ^ 2 ≤ |(ℓ : ℝ)| ^ (-(1 / 2 : ℝ)) * gl ℓ := by
  rw [sq_abs]; exact inv_sq_le_gl_mul (lt_of_lt_of_le hL hℓ) le_rfl

lemma rpow_half_le {m n Q : ℝ} (hm0 : 0 < m) (hQ : 1 ≤ Q) (hmn : m ^ 2 / (2 * Q) ≤ m * n) :
    (m * n) ^ (-(1 / 2) : ℝ) ≤ 2 * Q / m := by
  have hsq : (m / (2 * Q)) ^ 2 ≤ m * n := by
    refine le_trans ?_ hmn
    rw [div_pow]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  calc (m * n) ^ (-(1 / 2) : ℝ) ≤ ((m / (2 * Q)) ^ 2) ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hsq (by norm_num)
    _ = 2 * Q / m := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
        rw [Real.rpow_neg_one, inv_div]

lemma rpow_sig_le {m n P : ℝ} (hn0 : 0 < n) (hP : 1 ≤ P) (hmn' : n / (2 * P) ≤ m) :
    m ^ (-(2001 / 2000 : ℝ)) ≤ 4 * P ^ 2 * n ^ (-(2001 / 2000 : ℝ)) := by
  have hP0 : 0 < P := by linarith
  calc m ^ (-(2001 / 2000 : ℝ)) ≤ (n / (2 * P)) ^ (-(2001 / 2000 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hmn' (by norm_num)
    _ = (2 * P) ^ (2001 / 2000 : ℝ) * n ^ (-(2001 / 2000 : ℝ)) := by
        rw [Real.div_rpow hn0.le (by positivity),
          Real.rpow_neg (by positivity : (0:ℝ) ≤ 2 * P) (2001 / 2000), div_inv_eq_mul, mul_comm]
    _ ≤ (2 * P) ^ (2 : ℝ) * n ^ (-(2001 / 2000 : ℝ)) := by
        gcongr
        · linarith
        · norm_num
    _ = 4 * P ^ 2 * n ^ (-(2001 / 2000 : ℝ)) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring

/-- The near-line `Θ` bound. -/
lemma theta_near {T P Q m n ω : ℝ} {ℓ : ℤ} (hT : 1 ≤ T) (hP : 1 ≤ P) (hQ : 1 ≤ Q)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hℓ : (ℓ : ℝ) = P * m - Q * n) (hℓ0 : ℓ ≠ 0)
    (hω : |Q * n - P * m| / max (Q * n) (P * m) ≤ |ω|)
    (hfar : m ≤ T ^ (399 / 400 : ℝ) ∨ T ^ (401 / 400 : ℝ) < m ∨ T ^ (1 / 100 : ℝ) < |(ℓ : ℝ)|)
    (h1 : Q * n < 2 * (P * m)) (h2 : P * m < 2 * (Q * n)) :
    (m * n) ^ (-(1 / 2) : ℝ) * (1 + 4 * π ^ 2 * m * n / T ^ 2) ^ (-(3 : ℝ)) * Mw T ω ≤
      64 * (P * Q) ^ 4 * T ^ (299 / 300 : ℝ) * m ^ (-(2001 / 2000 : ℝ)) * gl ℓ := by
  have hT0 : 0 < T := by linarith
  have hm0 : 0 < m := by linarith
  have hn0 : 0 < n := by linarith
  have hP0 : 0 < P := by linarith
  have hQ0 : 0 < Q := by linarith
  have hD0 : 0 ≤ (1 + 4 * π ^ 2 * m * n / T ^ 2) ^ (-(3 : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hM0 : 0 ≤ Mw T ω := Mw_nonneg hT0
  have hs0 : 0 ≤ (m * n) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by positivity) _
  have hYZ : P * m ≠ Q * n := by
    intro h; apply hℓ0; exact_mod_cast (show (ℓ : ℝ) = 0 by rw [hℓ, h, sub_self])
  have hL : |(ℓ : ℝ)| = |Q * n - P * m| := by rw [hℓ, abs_sub_comm]
  have hL1 : 1 ≤ |(ℓ : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hℓ0
  have hM : Mw T ω ≤ 4 * (P * m) ^ 2 / (|(ℓ : ℝ)| ^ 2 * T) := by
    have := Mw_near hT0 (by positivity) (by positivity) hYZ hω h1
    rwa [hL, sq_abs]
  have hn2 : m / (2 * Q) ≤ n := by
    have hPm : m ≤ P * m := le_mul_of_one_le_left hm0.le hP
    rw [div_le_iff₀ (by positivity)]; linarith
  have hmn : m ^ 2 / (2 * Q) ≤ m * n := by
    have h3 := (div_le_iff₀ (by positivity : (0:ℝ) < 2 * Q)).1 hn2
    rw [div_le_iff₀ (by positivity)]
    calc m ^ 2 = m * m := by ring
      _ ≤ m * (n * (2 * Q)) := mul_le_mul_of_nonneg_left h3 hm0.le
      _ = m * n * (2 * Q) := by ring
  have hs := rpow_half_le hm0 hQ hmn
  have hTmn : T ^ 2 / (m * n) ≤ 2 * Q * T ^ 2 / m ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h7 := (div_le_iff₀ (by positivity : (0:ℝ) < 2 * Q)).1 hmn
    calc T ^ 2 * m ^ 2 ≤ T ^ 2 * (m * n * (2 * Q)) := mul_le_mul_of_nonneg_left h7 (sq_nonneg T)
      _ = 2 * Q * T ^ 2 * (m * n) := by ring
  have hDk : ∀ k : ℕ, k ≤ 3 → (1 + 4 * π ^ 2 * m * n / T ^ 2) ^ (-(3 : ℝ)) ≤
      (2 * Q * T ^ 2 / m ^ 2) ^ k := by
    intro k hk
    have := D_le (A := 3) (s := (k : ℝ)) hT0 hm0 hn0 (by positivity) (by exact_mod_cast hk)
    rw [Real.rpow_natCast] at this
    exact this.trans (pow_le_pow_left₀ (by positivity) hTmn k)
  have hD0' := hDk 0 (by norm_num)
  have hD1 := hDk 1 (by norm_num)
  rw [pow_zero] at hD0'
  rw [pow_one] at hD1
  rcases hfar with hf | hf | hf
  · exact theta_F2 hT hP hQ hL1 hm0 hf (inv_sq_le_gl' hℓ0) hs0 hD0 hM0 hs hD0' hM
  · exact theta_F3 hT hP hQ hL1 hf.le (inv_sq_le_gl' hℓ0) hs0 hD0 hM0 hs (hDk 3 le_rfl) hM
  · by_cases hm2 : T ^ (401 / 400 : ℝ) < m
    · exact theta_F3 hT hP hQ hL1 hm2.le (inv_sq_le_gl' hℓ0) hs0 hD0 hM0 hs (hDk 3 le_rfl) hM
    · push Not at hm2
      exact theta_F1 hT hP hQ hL1 hm0 hm2 hf.le
        (inv_sq_le_gl_mul' (Real.rpow_pos_of_pos hT0 _) hf.le) (gl_nonneg ℓ) hs0 hD0 hM0 hs hD1 hM

/-- Combining `|λλ| ≤ (λ²+λ²)/2` with the near-line bound. -/
lemma far_pt_near_comb {lm ln Θ W P n m g : ℝ} (hΘ0 : 0 ≤ Θ)
    (hW0 : 0 ≤ W) (hg : 0 ≤ g) (hP : 1 ≤ P) (hm0 : 0 < m)
    (hΘ : Θ ≤ W * m ^ (-(2001 / 2000 : ℝ)) * g)
    (hmσn : m ^ (-(2001 / 2000 : ℝ)) ≤ 4 * P ^ 2 * n ^ (-(2001 / 2000 : ℝ))) :
    lm * ln * Θ ≤ lm ^ 2 * (4 * P ^ 2 * W) * m ^ (-(2001 / 2000 : ℝ)) * g +
      ln ^ 2 * (4 * P ^ 2 * W) * n ^ (-(2001 / 2000 : ℝ)) * g := by
  have hlmn : lm * ln ≤ (lm ^ 2 + ln ^ 2) / 2 := by nlinarith [sq_nonneg (lm - ln)]
  have hmσ : 0 ≤ m ^ (-(2001 / 2000 : ℝ)) := Real.rpow_nonneg hm0.le _
  have h4 : 1 ≤ 4 * P ^ 2 := by nlinarith
  have a1 : lm * ln * Θ ≤ (lm ^ 2 + ln ^ 2) / 2 * (W * m ^ (-(2001 / 2000 : ℝ)) * g) :=
    mul_le_mul hlmn hΘ hΘ0 (by positivity)
  have a2 : W * m ^ (-(2001 / 2000 : ℝ)) * g ≤ (4 * P ^ 2 * W) * m ^ (-(2001 / 2000 : ℝ)) * g := by
    have : W ≤ 4 * P ^ 2 * W := by nlinarith
    gcongr
  have a3 : W * m ^ (-(2001 / 2000 : ℝ)) * g ≤ (4 * P ^ 2 * W) * n ^ (-(2001 / 2000 : ℝ)) * g := by
    calc W * m ^ (-(2001 / 2000 : ℝ)) * g ≤ W * (4 * P ^ 2 * n ^ (-(2001 / 2000 : ℝ))) * g := by
          gcongr
      _ = _ := by ring
  have b1 : 0 ≤ lm ^ 2 := sq_nonneg _
  have b2 : 0 ≤ ln ^ 2 := sq_nonneg _
  have c1 := mul_le_mul_of_nonneg_left a2 b1
  have c2 := mul_le_mul_of_nonneg_left a3 b2
  have hX : 0 ≤ W * m ^ (-(2001 / 2000 : ℝ)) * g := by positivity
  nlinarith

/-- **The far majorant, real-variable form.** -/
lemma far_pt_real {T P Q m n lm ln ω : ℝ} {ℓ : ℤ} (hT : 1 ≤ T) (hP : 1 ≤ P) (hQ : 1 ≤ Q)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hℓ : (ℓ : ℝ) = P * m - Q * n) (hℓ0 : ℓ ≠ 0)
    (_hlm : 0 ≤ lm) (_hln : 0 ≤ ln) (hω : |Q * n - P * m| / max (Q * n) (P * m) ≤ |ω|)
    (hfar : m ≤ T ^ (399 / 400 : ℝ) ∨ T ^ (401 / 400 : ℝ) < m ∨ T ^ (1 / 100 : ℝ) < |(ℓ : ℝ)|) :
    lm * ln * ((m * n) ^ (-(1 / 2) : ℝ) * (1 + 4 * π ^ 2 * m * n / T ^ 2) ^ (-(3 : ℝ)) * Mw T ω) ≤
      256 * (P * Q) ^ 6 * T ^ (299 / 300 : ℝ) *
        ((lm ^ 2 + ln ^ 2) * (m * n) ^ (-(2001 / 2000 : ℝ)) +
          lm ^ 2 * m ^ (-(2001 / 2000 : ℝ)) * gl ℓ + ln ^ 2 * n ^ (-(2001 / 2000 : ℝ)) * gl ℓ) := by
  have hT0 : 0 < T := by linarith
  have hm0 : 0 < m := by linarith
  have hn0 : 0 < n := by linarith
  have hP0 : 0 < P := by linarith
  have hQ0 : 0 < Q := by linarith
  have hD0 : 0 ≤ (1 + 4 * π ^ 2 * m * n / T ^ 2) ^ (-(3 : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hM0 : 0 ≤ Mw T ω := Mw_nonneg hT0
  have hs0 : 0 ≤ (m * n) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by positivity) _
  have hΘ0 : 0 ≤ (m * n) ^ (-(1 / 2) : ℝ) * (1 + 4 * π ^ 2 * m * n / T ^ 2) ^ (-(3 : ℝ)) * Mw T ω :=
    by positivity
  have hPQ1 : 1 ≤ P * Q := one_le_mul_of_one_le_of_one_le hP hQ
  have hT1 : 1 ≤ T ^ (299 / 300 : ℝ) := Real.one_le_rpow hT (by norm_num)
  have hgl := gl_nonneg ℓ
  have hmσ : 0 ≤ m ^ (-(2001 / 2000 : ℝ)) := Real.rpow_nonneg hm0.le _
  have hnσ : 0 ≤ n ^ (-(2001 / 2000 : ℝ)) := Real.rpow_nonneg hn0.le _
  have hmnσ : 0 ≤ (m * n) ^ (-(2001 / 2000 : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hR0 : 0 ≤ 256 * (P * Q) ^ 6 * T ^ (299 / 300 : ℝ) := by positivity
  by_cases hoff : 2 * (P * m) ≤ Q * n ∨ 2 * (Q * n) ≤ P * m
  · have hM := Mw_off hT0 (by positivity) (by positivity) hω hoff
    have hD := D_le (A := 3) (s := (2001 / 2000 : ℝ) - 1 / 2) hT0 hm0 hn0 (by norm_num) (by norm_num)
    have hθ := theta_off hT hm0 hn0 hD hM0 hM
    have hT2 : T ^ ((1 : ℝ) / 1000) ≤ T ^ (299 / 300 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
    have hPQ6 : 1 ≤ (P * Q) ^ 6 := one_le_pow₀ hPQ1
    have hlmn : lm * ln ≤ (lm ^ 2 + ln ^ 2) / 2 := by nlinarith [sq_nonneg (lm - ln)]
    have a1 := mul_le_mul hlmn hθ hΘ0 (by positivity)
    have h4 : 2 * T ^ ((1 : ℝ) / 1000) ≤ 256 * (P * Q) ^ 6 * T ^ (299 / 300 : ℝ) := by
      have : 0 ≤ T ^ ((1 : ℝ) / 1000) := by positivity
      nlinarith
    have h3 : 0 ≤ (lm ^ 2 + ln ^ 2) * (m * n) ^ (-(2001 / 2000 : ℝ)) := by positivity
    have a2 : (lm ^ 2 + ln ^ 2) / 2 * (4 * T ^ ((1 : ℝ) / 1000) * (m * n) ^ (-(2001 / 2000 : ℝ))) ≤
        256 * (P * Q) ^ 6 * T ^ (299 / 300 : ℝ) * ((lm ^ 2 + ln ^ 2) * (m * n) ^ (-(2001 / 2000 : ℝ))) := by
      have e : (lm ^ 2 + ln ^ 2) / 2 * (4 * T ^ ((1 : ℝ) / 1000) * (m * n) ^ (-(2001 / 2000 : ℝ))) =
          (2 * T ^ ((1 : ℝ) / 1000)) * ((lm ^ 2 + ln ^ 2) * (m * n) ^ (-(2001 / 2000 : ℝ))) := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right h4 h3
    have h5 : 0 ≤ lm ^ 2 * m ^ (-(2001 / 2000 : ℝ)) * gl ℓ + ln ^ 2 * n ^ (-(2001 / 2000 : ℝ)) * gl ℓ := by
      positivity
    calc _ ≤ _ := a1.trans a2
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hR0
  · push Not at hoff
    obtain ⟨h1, h2⟩ := hoff
    have hΘ := theta_near hT hP hQ hm hn hℓ hℓ0 hω hfar h1 h2
    have hmn' : n / (2 * P) ≤ m := by
      have hQn : n ≤ Q * n := le_mul_of_one_le_left hn0.le hQ
      rw [div_le_iff₀ (by positivity)]; linarith
    have hmσn := rpow_sig_le hn0 hP hmn'
    have hc := far_pt_near_comb (lm := lm) (ln := ln) hΘ0 (by positivity) hgl hP hm0 hΘ hmσn
    have hP2 : P ^ 2 ≤ (P * Q) ^ 2 := by
      rw [mul_pow]; nlinarith [one_le_pow₀ (n := 2) hQ, sq_nonneg P]
    have hW4 : 4 * P ^ 2 * (64 * (P * Q) ^ 4 * T ^ (299 / 300 : ℝ)) ≤
        256 * (P * Q) ^ 6 * T ^ (299 / 300 : ℝ) := by
      have e : 256 * (P * Q) ^ 6 * T ^ (299 / 300 : ℝ) =
          4 * (P * Q) ^ 2 * (64 * (P * Q) ^ 4 * T ^ (299 / 300 : ℝ)) := by ring
      rw [e]
      have h0 : 0 ≤ 64 * (P * Q) ^ 4 * T ^ (299 / 300 : ℝ) := by positivity
      gcongr
    have b1 : lm ^ 2 * (4 * P ^ 2 * (64 * (P * Q) ^ 4 * T ^ (299 / 300 : ℝ))) * m ^ (-(2001 / 2000 : ℝ)) * gl ℓ
        ≤ 256 * (P * Q) ^ 6 * T ^ (299 / 300 : ℝ) * (lm ^ 2 * m ^ (-(2001 / 2000 : ℝ)) * gl ℓ) := by
      have e : lm ^ 2 * (4 * P ^ 2 * (64 * (P * Q) ^ 4 * T ^ (299 / 300 : ℝ))) * m ^ (-(2001 / 2000 : ℝ)) * gl ℓ
          = (4 * P ^ 2 * (64 * (P * Q) ^ 4 * T ^ (299 / 300 : ℝ))) * (lm ^ 2 * m ^ (-(2001 / 2000 : ℝ)) * gl ℓ) := by
        ring
      rw [e]; exact mul_le_mul_of_nonneg_right hW4 (by positivity)
    have b2 : ln ^ 2 * (4 * P ^ 2 * (64 * (P * Q) ^ 4 * T ^ (299 / 300 : ℝ))) * n ^ (-(2001 / 2000 : ℝ)) * gl ℓ
        ≤ 256 * (P * Q) ^ 6 * T ^ (299 / 300 : ℝ) * (ln ^ 2 * n ^ (-(2001 / 2000 : ℝ)) * gl ℓ) := by
      have e : ln ^ 2 * (4 * P ^ 2 * (64 * (P * Q) ^ 4 * T ^ (299 / 300 : ℝ))) * n ^ (-(2001 / 2000 : ℝ)) * gl ℓ
          = (4 * P ^ 2 * (64 * (P * Q) ^ 4 * T ^ (299 / 300 : ℝ))) * (ln ^ 2 * n ^ (-(2001 / 2000 : ℝ)) * gl ℓ) := by
        ring
      rw [e]; exact mul_le_mul_of_nonneg_right hW4 (by positivity)
    have h3 : 0 ≤ 256 * (P * Q) ^ 6 * T ^ (299 / 300 : ℝ) *
        ((lm ^ 2 + ln ^ 2) * (m * n) ^ (-(2001 / 2000 : ℝ))) := by positivity
    have e : 256 * (P * Q) ^ 6 * T ^ (299 / 300 : ℝ) *
        ((lm ^ 2 + ln ^ 2) * (m * n) ^ (-(2001 / 2000 : ℝ)) +
          lm ^ 2 * m ^ (-(2001 / 2000 : ℝ)) * gl ℓ + ln ^ 2 * n ^ (-(2001 / 2000 : ℝ)) * gl ℓ) =
        256 * (P * Q) ^ 6 * T ^ (299 / 300 : ℝ) * ((lm ^ 2 + ln ^ 2) * (m * n) ^ (-(2001 / 2000 : ℝ))) +
        256 * (P * Q) ^ 6 * T ^ (299 / 300 : ℝ) * (lm ^ 2 * m ^ (-(2001 / 2000 : ℝ)) * gl ℓ) +
        256 * (P * Q) ^ 6 * T ^ (299 / 300 : ℝ) * (ln ^ 2 * n ^ (-(2001 / 2000 : ℝ)) * gl ℓ) := by ring
    rw [e]
    linarith

end RamanujanTau.SelbergKey7
