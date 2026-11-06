/-
# Short-sum inputs and the resulting pointwise formulas / partial-sum exponents

* `short_rankin`: `Σ_{x<n≤x+2u}|τ(n)| ≤ √Q u^{1/2} x^{29/5}` for `1 ≤ u ≤ x^{3/5}`
  (Cauchy–Schwarz + Rankin's `O(N^{3/5})`, via `TauPartialSumsSharp.short_bound`; unconditional);
* `short_deligne` (`[DeligneBound]`): `Σ_{x<n≤x+H}|τ(n)| ≤ C(H+1)(x+H)^{11/2+δ}`;
* `voronoi_pointwise_uncond`: `|S(x) − V_N(x)| ≤ C x^{121/20+ε} N^{−1/4}` for `1 ≤ N ≤ x^{3/5}`;
* `voronoi_pointwise_deligne` (`[DeligneBound]`): `|S(x) − V_N(x)| ≤ C x^{6+ε} N^{−1/2}` for `1 ≤ N ≤ x^{1/3}`;
* `partial_uncond`: `|S(x)| ≤ C x^{59/10+ε}`;  `partial_deligne` (`[DeligneBound]`): `|S(x)| ≤ C x^{35/6+ε}`.
-/
import RamanujanTau.VoronoiPointwise.Simple
import RamanujanTau.VoronoiPointwise.DeligneTau
import RamanujanTau.TauPartialSumsSharp.Main

set_option autoImplicit false

namespace RamanujanTau.VoronoiPointwise

open Real ModularForm
open RamanujanTau.VoronoiTrunc
open scoped MatrixGroups

/-! ### Short sums -/

/-- Rankin–Selberg short sums for `τ` (unconditional). -/
theorem short_rankin : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ x : ℝ, 1 ≤ x → ∀ u : ℝ, 1 ≤ u → u ≤ x ^ ((3 : ℝ) / 5) →
    ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + 2 * u⌋₊, |((tau n : ℤ) : ℝ)| ≤
      Real.sqrt Q * (u ^ ((1 : ℝ) / 2) * x ^ ((29 : ℝ) / 5)) := by
  obtain ⟨Crs, hRS⟩ := RankinExact.rankinSelberg_exact_general (k := 12)
    (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ))
  have hsq : ∀ n, RankinSelbergGeneral.coeffSq (k := 12)
      (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) n = ‖tauC n‖ ^ 2 := fun n => by
    rw [← HeckeConvexGeneral.coef_discriminant n]; rfl
  have hT : ∀ N : ℕ, 1 ≤ N →
      |∑ n ∈ Finset.Icc 1 N, ‖tauC n‖ ^ 2 / (n : ℝ) ^ (11 : ℕ) -
          RankinSelbergGeneral.rsConst (k := 12)
            (CuspForm.discriminant : CuspForm 𝒮ℒ ((12 : ℕ) : ℤ)) * N| ≤
        Crs * (N : ℝ) ^ ((3 : ℝ) / 5) := by
    intro N hN
    have := hRS N hN
    simp only [hsq] at this
    exact this
  obtain ⟨Q, hQ0, hQ⟩ := TauPartialSumsSharp.short_bound tauC 11 hT 2
  refine ⟨Q, hQ0, fun x hx u hu1 hu => ?_⟩
  have := hQ x hx u hu1 hu
  simp only [norm_tauC] at this
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, show ((11 : ℕ) : ℝ) / 2 + 3 / 10 = (29 : ℝ) / 5 by norm_num]
    at this
  exact this

/-- Deligne short sums (`[DeligneBound]`). -/
theorem short_deligne [DeligneBound] {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x H : ℝ, 0 ≤ x → 0 ≤ H →
      ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, |((tau n : ℤ) : ℝ)| ≤ C * ((H + 1) * (x + H) ^ (11 / 2 + δ)) := by
  obtain ⟨C, hC1, hC⟩ := abs_tau_le_rpow hδ
  refine ⟨C, hC1, fun x H hx hH => ?_⟩
  have hb : ∀ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + H⌋₊, |((tau n : ℤ) : ℝ)| ≤ C * (x + H) ^ (11 / 2 + δ) := by
    intro n hn
    have hn2 : (n : ℝ) ≤ x + H := by
      have := (Finset.mem_Ioc.1 hn).2
      exact le_trans (by exact_mod_cast this) (Nat.floor_le (by linarith))
    refine (hC n).trans ?_
    gcongr
  refine (Finset.sum_le_sum hb).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc := card_Ioc_floor_le hx hH
  have : 0 ≤ C * (x + H) ^ (11 / 2 + δ) := by
    have : 0 ≤ x + H := by linarith
    positivity
  nlinarith

/-! ### rpow helpers -/

lemma rpow_le_of_le_rpow {N x a b : ℝ} (hN : 0 ≤ N) (hx : 0 ≤ x) (hNa : N ≤ x ^ a) (hb : 0 ≤ b) :
    N ^ b ≤ x ^ (a * b) := by
  rw [Real.rpow_mul hx]; exact Real.rpow_le_rpow hN hNa hb

lemma floor_ge_half {y : ℝ} (hy : 1 ≤ y) : y / 2 ≤ (⌊y⌋₊ : ℝ) := by
  have h1 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  have h2 : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast Nat.one_le_floor_iff y |>.2 hy
  linarith

lemma neg_rpow_le_of_ge {N x a c : ℝ} (hx : 0 < x) (hc : 0 ≤ c) (hN : x ^ a / 2 ≤ N) :
    N ^ (-c) ≤ 2 ^ c * x ^ (-(a * c)) := by
  have hpos : 0 < x ^ a / 2 := by positivity
  calc N ^ (-c) ≤ (x ^ a / 2) ^ (-c) := Real.rpow_le_rpow_of_nonpos hpos hN (by linarith)
    _ = 2 ^ c * x ^ (-(a * c)) := by
        rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hx.le,
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) c]
        rw [show a * -c = -(a * c) by ring]
        field_simp

/-! ### The pointwise formulas -/

/-- **Unconditional pointwise truncated Voronoi**: `|S − V_N| ≤ C x^{121/20+ε} N^{−1/4}`,
`1 ≤ N ≤ x^{3/5}`. -/
theorem voronoi_pointwise_uncond {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ x ^ ((3 : ℝ) / 5) →
      |Sre x - Vth N x| ≤ C * (x ^ ((121 : ℝ) / 20 + ε) * (N : ℝ) ^ (-(1 / 4) : ℝ)) := by
  set δ : ℝ := min ε 1 with hδdef
  have hδ0 : 0 < δ := lt_min hε one_pos
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  obtain ⟨C0, hC00, hC0⟩ := pointwise_simple hδ0 (by linarith)
  obtain ⟨Q, hQ0, hQ⟩ := short_rankin
  refine ⟨Real.sqrt Q + C0, by positivity, fun x hx N hN hNx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hx35 : x ^ ((3 : ℝ) / 5) ≤ x := by
    calc x ^ ((3 : ℝ) / 5) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      _ = x := Real.rpow_one x
  have hNx' : (N : ℝ) ≤ x := hNx.trans hx35
  set u : ℝ := √(x / N) with hu
  have hu1 : 1 ≤ u := one_le_sqrt_div hN0 hNx'
  have hu35 : u ≤ x ^ ((3 : ℝ) / 5) := by
    calc u ≤ √x := Real.sqrt_le_sqrt (div_le_self hx0.le hN1)
      _ = x ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow x
      _ ≤ x ^ ((3 : ℝ) / 5) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hmain := hC0 x hx N hN hNx'
  have hshort := hQ x hx u hu1 hu35
  set E : ℝ := x ^ ((121 : ℝ) / 20 + ε) * (N : ℝ) ^ (-(1 / 4) : ℝ) with hE
  -- short sum part
  have s1 : u ^ ((1 : ℝ) / 2) * x ^ ((29 : ℝ) / 5) ≤ E := by
    have e : u ^ ((1 : ℝ) / 2) = x ^ ((1 : ℝ) / 4) * (N : ℝ) ^ (-(1 / 4) : ℝ) := by
      rw [hu, Real.sqrt_eq_rpow, ← Real.rpow_mul (div_nonneg hx0.le hN0.le),
        Real.div_rpow hx0.le hN0.le, Real.rpow_neg hN0.le]
      norm_num; rfl
    rw [e, hE]
    have : x ^ ((1 : ℝ) / 4) * x ^ ((29 : ℝ) / 5) ≤ x ^ ((121 : ℝ) / 20 + ε) := by
      rw [← Real.rpow_add hx0]; exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    have hN4 : 0 ≤ (N : ℝ) ^ (-(1 / 4) : ℝ) := by positivity
    nlinarith
  -- main part
  have s2 : x ^ (23 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 + δ) ≤ E := by
    have e : (N : ℝ) ^ (1 / 4 + δ) = (N : ℝ) ^ (1 / 2 + δ) * (N : ℝ) ^ (-(1 / 4) : ℝ) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have b : (N : ℝ) ^ (1 / 2 + δ) ≤ x ^ ((3 : ℝ) / 5 * (1 / 2 + δ)) :=
      rpow_le_of_le_rpow hN0.le hx0.le hNx (by linarith)
    have c : x ^ (23 / 4 : ℝ) * x ^ ((3 : ℝ) / 5 * (1 / 2 + δ)) ≤ x ^ ((121 : ℝ) / 20 + ε) := by
      rw [← Real.rpow_add hx0]; exact Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)
    rw [e, hE]
    have hN4 : 0 ≤ (N : ℝ) ^ (-(1 / 4) : ℝ) := by positivity
    have hx4 : 0 ≤ x ^ (23 / 4 : ℝ) := by positivity
    calc x ^ (23 / 4 : ℝ) * ((N : ℝ) ^ (1 / 2 + δ) * (N : ℝ) ^ (-(1 / 4) : ℝ))
        = (x ^ (23 / 4 : ℝ) * (N : ℝ) ^ (1 / 2 + δ)) * (N : ℝ) ^ (-(1 / 4) : ℝ) := by ring
      _ ≤ (x ^ (23 / 4 : ℝ) * x ^ ((3 : ℝ) / 5 * (1 / 2 + δ))) * (N : ℝ) ^ (-(1 / 4) : ℝ) := by gcongr
      _ ≤ x ^ ((121 : ℝ) / 20 + ε) * (N : ℝ) ^ (-(1 / 4) : ℝ) := by gcongr
  have hsq : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg Q
  calc |Sre x - Vth N x| ≤ Real.sqrt Q * (u ^ ((1 : ℝ) / 2) * x ^ ((29 : ℝ) / 5)) +
        C0 * (x ^ (23 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 + δ)) := hmain.trans (by rw [← hu]; linarith)
    _ ≤ Real.sqrt Q * E + C0 * E := by gcongr
    _ = (Real.sqrt Q + C0) * E := by ring

/-- **Deligne-conditional pointwise truncated Voronoi** (classical form):
`|S − V_N| ≤ C x^{6+ε} N^{−1/2}` for `1 ≤ N ≤ x^{1/3}`. -/
theorem voronoi_pointwise_deligne [DeligneBound] {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ x ^ ((1 : ℝ) / 3) →
      |Sre x - Vth N x| ≤ C * (x ^ (6 + ε) * (N : ℝ) ^ (-(1 / 2) : ℝ)) := by
  set δ : ℝ := min ε 1 with hδdef
  have hδ0 : 0 < δ := lt_min hε one_pos
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  obtain ⟨C0, hC00, hC0⟩ := pointwise_simple hδ0 (by linarith)
  obtain ⟨D, hD1, hD⟩ := short_deligne hδ0
  refine ⟨D * 3 * 3 ^ (11 / 2 + δ) + C0, by positivity, fun x hx N hN hNx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hx13 : x ^ ((1 : ℝ) / 3) ≤ x := by
    calc x ^ ((1 : ℝ) / 3) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      _ = x := Real.rpow_one x
  have hNx' : (N : ℝ) ≤ x := hNx.trans hx13
  set u : ℝ := √(x / N) with hu
  have hu1 : 1 ≤ u := one_le_sqrt_div hN0 hNx'
  have hux : u ≤ x := sqrt_div_le hx hN1
  have hmain := hC0 x hx N hN hNx'
  have hshort := hD x (2 * u) hx0.le (by linarith)
  set E : ℝ := x ^ (6 + ε) * (N : ℝ) ^ (-(1 / 2) : ℝ) with hE
  have hue : u = x ^ ((1 : ℝ) / 2) * (N : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [hu, Real.sqrt_eq_rpow, Real.div_rpow hx0.le hN0.le, Real.rpow_neg hN0.le, div_eq_mul_inv]
  -- short sum
  have s1 : D * ((2 * u + 1) * (x + 2 * u) ^ (11 / 2 + δ)) ≤ D * 3 * 3 ^ (11 / 2 + δ) * E := by
    have a1 : 2 * u + 1 ≤ 3 * u := by linarith
    have a2 : (x + 2 * u) ^ (11 / 2 + δ) ≤ (3 * x) ^ (11 / 2 + δ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    have a3 : u * x ^ (11 / 2 + δ) ≤ E := by
      rw [hue, hE]
      have : x ^ ((1 : ℝ) / 2) * x ^ (11 / 2 + δ) ≤ x ^ (6 + ε) := by
        rw [← Real.rpow_add hx0]; exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      have hN2 : 0 ≤ (N : ℝ) ^ (-(1 / 2) : ℝ) := by positivity
      calc x ^ ((1 : ℝ) / 2) * (N : ℝ) ^ (-(1 / 2) : ℝ) * x ^ (11 / 2 + δ)
          = (x ^ ((1 : ℝ) / 2) * x ^ (11 / 2 + δ)) * (N : ℝ) ^ (-(1 / 2) : ℝ) := by ring
        _ ≤ x ^ (6 + ε) * (N : ℝ) ^ (-(1 / 2) : ℝ) := by gcongr
    have hD0 : 0 ≤ D := by linarith
    rw [Real.mul_rpow (by norm_num) hx0.le] at a2
    have h0 : 0 ≤ (x + 2 * u) ^ (11 / 2 + δ) := by
      have : 0 ≤ x + 2 * u := by linarith
      positivity
    have h3 : (0 : ℝ) ≤ 3 ^ (11 / 2 + δ) := by positivity
    calc D * ((2 * u + 1) * (x + 2 * u) ^ (11 / 2 + δ))
        ≤ D * ((3 * u) * (3 ^ (11 / 2 + δ) * x ^ (11 / 2 + δ))) := by gcongr
      _ = D * 3 * 3 ^ (11 / 2 + δ) * (u * x ^ (11 / 2 + δ)) := by ring
      _ ≤ D * 3 * 3 ^ (11 / 2 + δ) * E := by gcongr
  -- main
  have s2 : x ^ (23 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 + δ) ≤ E := by
    have e : (N : ℝ) ^ (1 / 4 + δ) = (N : ℝ) ^ (3 / 4 + δ) * (N : ℝ) ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have b : (N : ℝ) ^ (3 / 4 + δ) ≤ x ^ ((1 : ℝ) / 3 * (3 / 4 + δ)) :=
      rpow_le_of_le_rpow hN0.le hx0.le hNx (by linarith)
    have c : x ^ (23 / 4 : ℝ) * x ^ ((1 : ℝ) / 3 * (3 / 4 + δ)) ≤ x ^ (6 + ε) := by
      rw [← Real.rpow_add hx0]; exact Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)
    rw [e, hE]
    have hN4 : 0 ≤ (N : ℝ) ^ (-(1 / 2) : ℝ) := by positivity
    calc x ^ (23 / 4 : ℝ) * ((N : ℝ) ^ (3 / 4 + δ) * (N : ℝ) ^ (-(1 / 2) : ℝ))
        = (x ^ (23 / 4 : ℝ) * (N : ℝ) ^ (3 / 4 + δ)) * (N : ℝ) ^ (-(1 / 2) : ℝ) := by ring
      _ ≤ (x ^ (23 / 4 : ℝ) * x ^ ((1 : ℝ) / 3 * (3 / 4 + δ))) * (N : ℝ) ^ (-(1 / 2) : ℝ) := by gcongr
      _ ≤ x ^ (6 + ε) * (N : ℝ) ^ (-(1 / 2) : ℝ) := by gcongr
  calc |Sre x - Vth N x| ≤ D * ((2 * u + 1) * (x + 2 * u) ^ (11 / 2 + δ)) +
        C0 * (x ^ (23 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 + δ)) := hmain.trans (by rw [← hu]; linarith)
    _ ≤ D * 3 * 3 ^ (11 / 2 + δ) * E + C0 * E := by gcongr
    _ = (D * 3 * 3 ^ (11 / 2 + δ) + C0) * E := by ring

/-! ### Partial sums -/

/-- `|S(x)| ≤ C x^{59/10+ε}` from the unconditional pointwise formula at `N = ⌊x^{3/5}⌋`. -/
theorem partial_uncond {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |Sre x| ≤ C * x ^ ((59 : ℝ) / 10 + ε) := by
  obtain ⟨C1, hC10, hC1⟩ := voronoi_pointwise_uncond hε
  set β : ℝ := 13 / 2 + ε with hβdef
  have hβ : 13 / 2 < β := by linarith
  refine ⟨C1 * 2 ^ ((1 : ℝ) / 4) + 1 / (π * √2) * St β, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hy : 1 ≤ x ^ ((3 : ℝ) / 5) := Real.one_le_rpow hx (by norm_num)
  set N : ℕ := ⌊x ^ ((3 : ℝ) / 5)⌋₊ with hNdef
  have hN : 1 ≤ N := Nat.one_le_floor_iff _ |>.2 hy
  have hNx : (N : ℝ) ≤ x ^ ((3 : ℝ) / 5) := Nat.floor_le (by positivity)
  have hNh : x ^ ((3 : ℝ) / 5) / 2 ≤ N := floor_ge_half hy
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := hC1 x hx N hN hNx
  have h2 := abs_Vth_le hβ hx0.le N
  have hS := St_nonneg β
  -- error part
  have e1 : x ^ ((121 : ℝ) / 20 + ε) * (N : ℝ) ^ (-(1 / 4) : ℝ) ≤
      2 ^ ((1 : ℝ) / 4) * x ^ ((59 : ℝ) / 10 + ε) := by
    have := neg_rpow_le_of_ge (c := 1 / 4) hx0 (by norm_num) hNh
    calc x ^ ((121 : ℝ) / 20 + ε) * (N : ℝ) ^ (-(1 / 4) : ℝ)
        ≤ x ^ ((121 : ℝ) / 20 + ε) * (2 ^ ((1 : ℝ) / 4) * x ^ (-((3 : ℝ) / 5 * (1 / 4)))) := by
          gcongr
      _ = 2 ^ ((1 : ℝ) / 4) * (x ^ ((121 : ℝ) / 20 + ε) * x ^ (-((3 : ℝ) / 5 * (1 / 4)))) := by ring
      _ = 2 ^ ((1 : ℝ) / 4) * x ^ ((59 : ℝ) / 10 + ε) := by
          rw [← Real.rpow_add hx0]; congr 2; ring
  -- main part
  have e2 : x ^ (23 / 4 : ℝ) / (π * √2) * ((N : ℝ) ^ (β - 25 / 4) * St β) ≤
      1 / (π * √2) * St β * x ^ ((59 : ℝ) / 10 + ε) := by
    have b : (N : ℝ) ^ (β - 25 / 4) ≤ x ^ ((3 : ℝ) / 5 * (β - 25 / 4)) :=
      rpow_le_of_le_rpow hN0.le hx0.le hNx (by linarith)
    have c : x ^ (23 / 4 : ℝ) * x ^ ((3 : ℝ) / 5 * (β - 25 / 4)) ≤ x ^ ((59 : ℝ) / 10 + ε) := by
      rw [← Real.rpow_add hx0]; exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    have hp : 0 < π * √2 := by positivity
    calc x ^ (23 / 4 : ℝ) / (π * √2) * ((N : ℝ) ^ (β - 25 / 4) * St β)
        = 1 / (π * √2) * St β * (x ^ (23 / 4 : ℝ) * (N : ℝ) ^ (β - 25 / 4)) := by ring
      _ ≤ 1 / (π * √2) * St β * (x ^ (23 / 4 : ℝ) * x ^ ((3 : ℝ) / 5 * (β - 25 / 4))) := by gcongr
      _ ≤ 1 / (π * √2) * St β * x ^ ((59 : ℝ) / 10 + ε) := by gcongr
  have tri : |Sre x| ≤ |Sre x - Vth N x| + |Vth N x| := by
    have := abs_add_le (Sre x - Vth N x) (Vth N x); simpa using this
  have : C1 * (x ^ ((121 : ℝ) / 20 + ε) * (N : ℝ) ^ (-(1 / 4) : ℝ)) ≤
      C1 * (2 ^ ((1 : ℝ) / 4) * x ^ ((59 : ℝ) / 10 + ε)) := by gcongr
  nlinarith

/-- `|S(x)| ≤ C x^{35/6+ε}` (`[DeligneBound]`), from the classical pointwise formula at `N = ⌊x^{1/3}⌋`. -/
theorem partial_deligne [DeligneBound] {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |Sre x| ≤ C * x ^ ((35 : ℝ) / 6 + ε) := by
  obtain ⟨C1, hC10, hC1⟩ := voronoi_pointwise_deligne hε
  set β : ℝ := 13 / 2 + ε with hβdef
  have hβ : 13 / 2 < β := by linarith
  refine ⟨C1 * 2 ^ ((1 : ℝ) / 2) + 1 / (π * √2) * St β, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hy : 1 ≤ x ^ ((1 : ℝ) / 3) := Real.one_le_rpow hx (by norm_num)
  set N : ℕ := ⌊x ^ ((1 : ℝ) / 3)⌋₊ with hNdef
  have hN : 1 ≤ N := Nat.one_le_floor_iff _ |>.2 hy
  have hNx : (N : ℝ) ≤ x ^ ((1 : ℝ) / 3) := Nat.floor_le (by positivity)
  have hNh : x ^ ((1 : ℝ) / 3) / 2 ≤ N := floor_ge_half hy
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := hC1 x hx N hN hNx
  have h2 := abs_Vth_le hβ hx0.le N
  have hS := St_nonneg β
  have e1 : x ^ (6 + ε) * (N : ℝ) ^ (-(1 / 2) : ℝ) ≤ 2 ^ ((1 : ℝ) / 2) * x ^ ((35 : ℝ) / 6 + ε) := by
    have := neg_rpow_le_of_ge (c := 1 / 2) hx0 (by norm_num) hNh
    calc x ^ (6 + ε) * (N : ℝ) ^ (-(1 / 2) : ℝ)
        ≤ x ^ (6 + ε) * (2 ^ ((1 : ℝ) / 2) * x ^ (-((1 : ℝ) / 3 * (1 / 2)))) := by gcongr
      _ = 2 ^ ((1 : ℝ) / 2) * (x ^ (6 + ε) * x ^ (-((1 : ℝ) / 3 * (1 / 2)))) := by ring
      _ = 2 ^ ((1 : ℝ) / 2) * x ^ ((35 : ℝ) / 6 + ε) := by
          rw [← Real.rpow_add hx0]; congr 2; ring
  have e2 : x ^ (23 / 4 : ℝ) / (π * √2) * ((N : ℝ) ^ (β - 25 / 4) * St β) ≤
      1 / (π * √2) * St β * x ^ ((35 : ℝ) / 6 + ε) := by
    have b : (N : ℝ) ^ (β - 25 / 4) ≤ x ^ ((1 : ℝ) / 3 * (β - 25 / 4)) :=
      rpow_le_of_le_rpow hN0.le hx0.le hNx (by linarith)
    have c : x ^ (23 / 4 : ℝ) * x ^ ((1 : ℝ) / 3 * (β - 25 / 4)) ≤ x ^ ((35 : ℝ) / 6 + ε) := by
      rw [← Real.rpow_add hx0]; exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    calc x ^ (23 / 4 : ℝ) / (π * √2) * ((N : ℝ) ^ (β - 25 / 4) * St β)
        = 1 / (π * √2) * St β * (x ^ (23 / 4 : ℝ) * (N : ℝ) ^ (β - 25 / 4)) := by ring
      _ ≤ 1 / (π * √2) * St β * (x ^ (23 / 4 : ℝ) * x ^ ((1 : ℝ) / 3 * (β - 25 / 4))) := by gcongr
      _ ≤ 1 / (π * √2) * St β * x ^ ((35 : ℝ) / 6 + ε) := by gcongr
  have tri : |Sre x| ≤ |Sre x - Vth N x| + |Vth N x| := by
    have := abs_add_le (Sre x - Vth N x) (Vth N x); simpa using this
  have : C1 * (x ^ (6 + ε) * (N : ℝ) ^ (-(1 / 2) : ℝ)) ≤
      C1 * (2 ^ ((1 : ℝ) / 2) * x ^ ((35 : ℝ) / 6 + ε)) := by gcongr
  nlinarith

end RamanujanTau.VoronoiPointwise
