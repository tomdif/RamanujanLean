/-
# Item (c), part 4: the leading-coefficient evaluation of one pair

`pair_eval`: uniformly in `h, k ≥ 1`, `X ≥ 16`, `H > 0`,

    MainTw(h,k,X,H) = 2√(hk) · W(h,k),
    |W(h,k) − (2r₀/[h,k]) (q₀(h,k) I₁ + q₁(h,k) I₀)| ≤ Z (hk)⁵ (X+H)^{9/10},

with `I₀ = Wint 1`, `I₁ = Wint ℓ(t)`, `q₀ = ρ(h₁)ρ(k₁)`, `q₁` the `Q¹` summand.
-/
import RamanujanTau.HafnerBridge2.Pair

set_option autoImplicit false

namespace RamanujanTau.HafnerBridge2

open MeasureTheory Set Filter Topology Complex
open RamanujanTau.ZetaAFE RamanujanTau.GoodSecondTerm RamanujanTau.GoodSecondTerm2 RamanujanTau.TwistedMoment
open RamanujanTau.HafnerBridge
open scoped Interval

noncomputable def q0 (h k : ℕ) : ℝ := rho (h / Nat.gcd h k) * rho (k / Nat.gcd h k)

noncomputable def q1 (h k : ℕ) : ℝ :=
  rho (h / Nat.gcd h k) * rho (k / Nat.gcd h k) *
      (gamR - 1 / 2 * Real.log ((h / Nat.gcd h k * (k / Nat.gcd h k) : ℕ) : ℝ)) +
    rho1 (h / Nat.gcd h k) * rho (k / Nat.gcd h k) + rho (h / Nat.gcd h k) * rho1 (k / Nat.gcd h k)

noncomputable def I0 (X H : ℝ) : ℝ := Wint X H (fun _ => 1)

noncomputable def I1 (X H : ℝ) : ℝ := Wint X H ellT

lemma ellT_nonneg {t : ℝ} (ht : 16 ≤ t) : 0 ≤ ellT t := by
  unfold ellT
  apply Real.log_nonneg
  rw [le_div_iff₀ (by positivity)]
  have := Real.pi_lt_d2; linarith

lemma two_pi_rpow_le : (2 * Real.pi) ^ (1 / 10 : ℝ) ≤ 2 := by
  have h1 : 2 * Real.pi ≤ (2 : ℝ) ^ (10 : ℕ) := by have := Real.pi_lt_d2; norm_num; linarith
  calc (2 * Real.pi) ^ (1 / 10 : ℝ) ≤ ((2 : ℝ) ^ (10 : ℕ)) ^ (1 / 10 : ℝ) :=
        Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    _ = 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num

/-- `(1+|L|)e^{−L/10} ≤ 40 t^{−1/10}` when `L ≥ 2ℓ(t)`, `t ≥ 16`. -/
lemma decay_le {L t : ℝ} (ht : 16 ≤ t) (hL : 2 * ellT t ≤ L) :
    (1 + |L|) * Real.exp (-L / 10) ≤ 40 * t ^ (-(1 / 10 : ℝ)) := by
  have hℓ := ellT_nonneg ht
  have hL0 : 0 ≤ L := by linarith
  have ht0 : 0 < t := by linarith
  rw [abs_of_nonneg hL0]
  have h1 : 1 + L ≤ 20 * Real.exp (L / 20) := by have := Real.add_one_le_exp (L / 20); linarith
  have h2 : (1 + L) * Real.exp (-L / 10) ≤ 20 * Real.exp (-L / 20) := by
    calc (1 + L) * Real.exp (-L / 10) ≤ 20 * Real.exp (L / 20) * Real.exp (-L / 10) := by gcongr
      _ = 20 * Real.exp (-L / 20) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
  have h3 : Real.exp (-L / 20) ≤ Real.exp (-ellT t / 10) := Real.exp_le_exp.mpr (by linarith)
  have h4 : Real.exp (-ellT t / 10) = t ^ (-(1 / 10 : ℝ)) * (2 * Real.pi) ^ (1 / 10 : ℝ) := by
    have hp : 0 < t / (2 * Real.pi) := by positivity
    have e : Real.exp (-ellT t / 10) = (t / (2 * Real.pi)) ^ (-(1 / 10 : ℝ)) := by
      rw [Real.rpow_def_of_pos hp]; unfold ellT; ring_nf
    rw [e, Real.div_rpow ht0.le (by positivity), Real.rpow_neg (by positivity : (0:ℝ) ≤ 2 * Real.pi),
      div_inv_eq_mul]
  have h5 : 0 < t ^ (-(1 / 10 : ℝ)) := Real.rpow_pos_of_pos ht0 _
  calc (1 + L) * Real.exp (-L / 10) ≤ 20 * Real.exp (-L / 20) := h2
    _ ≤ 20 * Real.exp (-ellT t / 10) := by gcongr
    _ = 20 * (t ^ (-(1 / 10 : ℝ)) * (2 * Real.pi) ^ (1 / 10 : ℝ)) := by rw [h4]
    _ ≤ 20 * (t ^ (-(1 / 10 : ℝ)) * 2) := by gcongr; exact two_pi_rpow_le
    _ = 40 * t ^ (-(1 / 10 : ℝ)) := by ring

lemma integral_rpow_le {Y : ℝ} (hY : 16 ≤ Y) : ∫ t in (16 : ℝ)..Y, t ^ (-(1 / 10 : ℝ)) ≤ 10 / 9 * Y ^ (9 / 10 : ℝ) := by
  rw [integral_rpow (Or.inl (by norm_num))]
  norm_num
  have : 0 ≤ (16 : ℝ) ^ (9 / 10 : ℝ) := by positivity
  have h : (-(1 / 10 : ℝ)) + 1 = 9 / 10 := by norm_num
  linarith

lemma ADD_nonneg : 0 ≤ ADD := integral_nonneg fun u => by have := gk_pos u; positivity

lemma continuousOn_ellT' {X H : ℝ} : ContinuousOn ellT (Icc 16 (X + H)) := continuousOn_ellT (by norm_num)

/-- **One pair.** -/
theorem pair_eval : ∃ Z : ℝ, 0 ≤ Z ∧ ∀ h k : ℕ, 1 ≤ h → 1 ≤ k → ∀ X H : ℝ, 16 ≤ X → 0 < H →
    MainTw h k X H = ((2 * Real.sqrt ((h * k : ℕ) : ℝ) * Wint X H (Phi (fseq h k) (Real.log ((h * k : ℕ) : ℝ))) : ℝ) : ℂ) ∧
    |Wint X H (Phi (fseq h k) (Real.log ((h * k : ℕ) : ℝ))) -
        2 * r0 / (Nat.lcm h k : ℝ) * (q0 h k * I1 X H + q1 h k * I0 X H)| ≤
      Z * ((h * k : ℕ) : ℝ) ^ 5 * (X + H) ^ (9 / 10 : ℝ) := by
  obtain ⟨Z, hZ0, hTw⟩ := twisted_asymp
  refine ⟨225 * ADD * Z, by have := ADD_nonneg; positivity, fun h k hh hk X H hX hH => ?_⟩
  set g := Nat.gcd h k
  have hg := g_pos hh hk
  have hh1 : 1 ≤ h / g := Nat.div_pos (Nat.gcd_le_left _ (by omega)) hg
  have hk1 : 1 ≤ k / g := Nat.div_pos (Nat.gcd_le_right _ (by omega)) hg
  have hcop : (h / g).Coprime (k / g) := Nat.coprime_div_gcd_div_gcd hg
  obtain ⟨E, hE, hT, hb⟩ := hTw (h / g) (k / g) hh1 hk1 hcop
  set c := cT (h / g) (k / g) with hc
  set K := KT (h / g) (k / g) with hK
  set ℓ := Nat.lcm h k with hℓ
  have hl := lcm_pos hh hk
  have hl1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hl
  have hl0 : (0 : ℝ) < ℓ := by linarith
  have hS := logAsym_fseq hh hk hE hT
  set c'' := c / ℓ
  set K'' := (K - c * Real.log ℓ) / ℓ
  set E'' := (2 * E + 2 * |c| + |K|) * ℓ
  have hE'' : 0 ≤ E'' := by positivity
  set Λ₀ := Real.log ((h * k : ℕ) : ℝ) with hΛ
  have hΛ0 : 0 ≤ Λ₀ := Real.log_nonneg (by exact_mod_cast Nat.mul_pos (by omega : 0 < h) (by omega : 0 < k))
  refine ⟨MainTw_eq hE'' hS hX hH, ?_⟩
  have hXH : 16 ≤ X + H := by linarith
  set Z'' := E'' + 2 * |c''| + |K''| with hZ''
  have hADD := ADD_nonneg
  -- the main term
  set Mn : ℝ → ℝ := fun t => (c'' * Λ₀ + 2 * K'') * 1 + (2 * c'') * ellT t with hMn
  have hMnc : ContinuousOn Mn (Icc 16 (X + H)) :=
    continuousOn_const.add (continuousOn_const.mul continuousOn_ellT')
  have hPc : ContinuousOn (Phi (fseq h k) Λ₀) (Icc 16 (X + H)) := continuousOn_Phi hE'' hS Λ₀ (by norm_num)
  have hWM : Wint X H Mn = 2 * r0 / ℓ * (q0 h k * I1 X H + q1 h k * I0 X H) := by
    have ha := Wint_add hX hH (F := fun _ => (c'' * Λ₀ + 2 * K'') * 1) (G := fun t => (2 * c'') * ellT t)
      continuousOn_const (continuousOn_const.mul continuousOn_ellT')
    have hs1 := Wint_smul (X := X) (H := H) (c'' * Λ₀ + 2 * K'') (fun _ => 1)
    have hs2 := Wint_smul (X := X) (H := H) (2 * c'') ellT
    beta_reduce at ha hs1 hs2
    rw [hMn, ha, hs1, hs2]
    unfold I0 I1 q0 q1
    rw [log_n_eq hh hk]
    have hc' : c = r0 * (rho (h / g) * rho (k / g)) := rfl
    have hK' : K = gammaD * (rho (h / g) * rho (k / g)) + r0 * (rho1 (h / g) * rho (k / g) + rho (h / g) * rho1 (k / g)) := rfl
    have hgam : gamR = gammaD / r0 := rfl
    simp only [c'', K'']
    rw [hc', hK', hgam, ← hΛ]
    have := r0_pos.ne'
    field_simp
    ring
  -- pointwise error
  have hpt : ∀ t ∈ Icc 16 (X + H), |Phi (fseq h k) Λ₀ t - Mn t| ≤ 40 * ADD * Z'' * t ^ (-(1 / 10 : ℝ)) := by
    intro t ht
    have h1 := abs_Dsum_sub_le hE'' hS (Λ₀ + 2 * ellT t)
    have h2 := decay_le ht.1 (show 2 * ellT t ≤ Λ₀ + 2 * ellT t by linarith)
    have hZ''0 : 0 ≤ Z'' := by positivity
    have e : Phi (fseq h k) Λ₀ t - Mn t = ∑' m : ℕ, fseq h k m * V (2 * lg m - (Λ₀ + 2 * ellT t)) -
        c'' * (Λ₀ + 2 * ellT t) - 2 * K'' := by simp only [Phi, hMn]; ring
    rw [e]
    calc _ ≤ ADD * Z'' * ((1 + |Λ₀ + 2 * ellT t|) * Real.exp (-(Λ₀ + 2 * ellT t) / 10)) := h1
      _ ≤ ADD * Z'' * (40 * t ^ (-(1 / 10 : ℝ))) := by gcongr
      _ = _ := by ring
  have hGc : ContinuousOn (fun t : ℝ => 40 * ADD * Z'' * t ^ (-(1 / 10 : ℝ))) (Icc 16 (X + H)) :=
    continuousOn_const.mul (fun t ht => (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [ht.1]))).continuousWithinAt)
  have herr := abs_Wint_le hX hH (hPc.sub hMnc) hGc hpt
  rw [intervalIntegral.integral_const_mul] at herr
  have hint := integral_rpow_le hXH
  -- the constant
  have hZ''le : Z'' ≤ 5 * ℓ * (E + |c| + |K|) := by
    have hlogl : Real.log ℓ ≤ ℓ := (Real.log_le_sub_one_of_pos hl0).trans (by linarith)
    have hlog0 : 0 ≤ Real.log ℓ := Real.log_nonneg hl1
    have a1 : |c''| ≤ |c| := by
      simp only [c'']; rw [abs_div, abs_of_pos hl0, div_le_iff₀ hl0]; nlinarith [abs_nonneg c]
    have a2 : |K''| ≤ |K| + |c| := by
      simp only [K'']; rw [abs_div, abs_of_pos hl0, div_le_iff₀ hl0]
      have : |K - c * Real.log ℓ| ≤ |K| + |c| * ℓ := by
        refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
        rw [abs_mul, abs_of_nonneg hlog0]; exact mul_le_mul_of_nonneg_left hlogl (abs_nonneg c)
      nlinarith [abs_nonneg c, abs_nonneg K]
    simp only [hZ'', E'']
    nlinarith [abs_nonneg c, abs_nonneg K]
  have hlk : (ℓ : ℝ) ≤ ((h * k : ℕ) : ℝ) := by
    have := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega))
      (Nat.lcm_dvd (Nat.dvd_mul_right h k) (Nat.dvd_mul_left k h))
    exact_mod_cast this
  have hn : (((h / g) * (k / g) : ℕ) : ℝ) ≤ ((h * k : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul (Nat.div_le_self h g) (Nat.div_le_self k g)
  have hZb : Z'' ≤ 5 * Z * ((h * k : ℕ) : ℝ) ^ 5 := by
    calc Z'' ≤ 5 * ℓ * (E + |c| + |K|) := hZ''le
      _ ≤ 5 * ((h * k : ℕ) : ℝ) * (Z * (((h / g) * (k / g) : ℕ) : ℝ) ^ 4) := by gcongr
      _ ≤ 5 * ((h * k : ℕ) : ℝ) * (Z * ((h * k : ℕ) : ℝ) ^ 4) := by gcongr
      _ = _ := by ring
  rw [← hWM, ← Wint_sub hX hH hPc hMnc]
  have hY : 0 ≤ (X + H) ^ (9 / 10 : ℝ) := by positivity
  have hZ''0 : 0 ≤ Z'' := by positivity
  calc _ ≤ 40 * ADD * Z'' * ∫ t in (16 : ℝ)..X + H, t ^ (-(1 / 10 : ℝ)) := herr
    _ ≤ 40 * ADD * Z'' * (10 / 9 * (X + H) ^ (9 / 10 : ℝ)) := by gcongr
    _ ≤ 45 * ADD * Z'' * (X + H) ^ (9 / 10 : ℝ) := by nlinarith [mul_nonneg (mul_nonneg hADD hZ''0) hY]
    _ ≤ 45 * ADD * (5 * Z * ((h * k : ℕ) : ℝ) ^ 5) * (X + H) ^ (9 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hZb (by positivity)) hY
    _ = 225 * ADD * Z * ((h * k : ℕ) : ℝ) ^ 5 * (X + H) ^ (9 / 10 : ℝ) := by ring

end RamanujanTau.HafnerBridge2
