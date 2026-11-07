import RamanujanTau.FiniteArithmetic.RankRError
import RamanujanTau.BLBound.ThresholdR

/-!
# `b_ℓ(m) = 2m − 1` from finite data with an order-`r` recurrence

`RankR.Data2.bEll_eq`: the `RankSMain` theorem for an odd recurrence of order `r` on `s + r`
forms. The error vector `eₙ = (obs_a(U Gₙ))_a mod ℓ` satisfies `eₙ₊₁ = θ eₙ` (`divided_step`);
with `θ` invertible and `e₀ ≠ 0`, at each `n` some observation sees `Gₙ`, which feeds
`BLBound.not_mem_of_errorsR`. The window determinant is `det₀ · (det C)ⁿ` for the companion
matrix `C`.
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.RankR
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal
open RankS (bounds B odd_mem even_U odd_D odd_succ Xop toZMod_prime_zmod L_env)

variable {ℓ s r : ℕ} [hℓ : Fact ℓ.Prime]

namespace Data2
variable (D : Data2 ℓ s r) (h29 : 29 ≤ ℓ) (h24 : 24 * δ ℓ + 1 = ℓ ^ 2)

lemma ell_ne : (ℓ : ℤ_[ℓ]) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero

lemma map_ell_smul (F : PS ℓ) :
    PowerSeries.map (PadicInt.toZMod (p := ℓ)) ((ℓ : ℤ_[ℓ]) • F) = 0 := by
  rw [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, toZMod_prime_zmod, map_zero, zero_mul]

include h29 h24 in
/-- **The vector of observable errors is multiplied by `θ` at each cycle.** -/
theorem divided_step (a : Fin s) (H E : PS ℓ) (hH : H ∈ envSub D.hℓ5 1 (α ℓ))
    (hE : Dlin ℓ H = (ℓ : ℤ_[ℓ]) • E) :
    PadicInt.toZMod (obs (D.w a) (Ulin ℓ E)) =
      ∑ b, D.θ a b * PadicInt.toZMod (obs (D.w b) H) := by
  obtain ⟨c, R, hR, he⟩ := D.decompose h29 H hH
  obtain ⟨w', hw⟩ := D.obs_Y h29 h24 a H R c hR he
  have hY : Yop H = (ℓ : ℤ_[ℓ]) • Ulin ℓ E := by
    change Ulin ℓ (Dlin ℓ H) = _
    rw [hE, map_smul]
  rw [hY, map_smul, smul_eq_mul] at hw
  have hw' := mul_left_cancel₀ (ell_ne (ℓ := ℓ)) hw
  set cb : Fin (s + r) → ZMod ℓ := fun i => PadicInt.toZMod (c i)
  have hHbar : PowerSeries.map (PadicInt.toZMod (p := ℓ)) H = D.comb cb := by
    rw [he, map_add, D.map_sum_lift, map_ell_smul, add_zero]
  have hz : D.comb (mv D.Dmat cb) = 0 := by
    have h := congrArg (PowerSeries.map (PadicInt.toZMod (p := ℓ))) hE
    rw [reduce_D h24, hHbar, D.D_comb, map_ell_smul] at h
    exact h
  have hDc := D.comb_zero_iff _ hz
  have hobs : ∀ b, PadicInt.toZMod (obs (D.w b) H) = ∑ i, D.ω b i * cb i := fun b => by
    rw [obs_reduce, hHbar, D.obsBar_comb]
  simp only [hobs]
  rw [hw', map_add, map_mul, toZMod_prime_zmod, zero_mul, add_zero, map_sum]
  have hsum : ∑ i, PadicInt.toZMod (c i * (D.z a i : ℤ_[ℓ])) =
      ∑ i, cb i * (∑ b, D.θ a b * D.ω b i + ∑ j, D.μ a j * D.Dmat j i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_intCast, D.hθ a i]
    rfl
  rw [hsum]
  have hμ : ∑ i, cb i * ∑ j, D.μ a j * D.Dmat j i = 0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h0 : mv D.Dmat cb j = 0 := by rw [hDc]; rfl
    rw [show ∑ i, cb i * (D.μ a j * D.Dmat j i) = D.μ a j * mv D.Dmat cb j by
      rw [mv, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, h0, mul_zero]
  rw [show (∑ i, cb i * (∑ b, D.θ a b * D.ω b i + ∑ j, D.μ a j * D.Dmat j i)) =
      (∑ i, cb i * ∑ b, D.θ a b * D.ω b i) + ∑ i, cb i * ∑ j, D.μ a j * D.Dmat j i by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring, hμ, add_zero]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring

include h29 in
lemma U_mem (F : PS ℓ) (hF : F ∈ B h29 s 2) : Ulin ℓ F ∈ envSub D.hℓ5 1 (α ℓ) := by
  refine ⟨?_, U_env D.hℓ5 (by omega) (bounds h29).1 2 le_rfl _ hF.1.2⟩
  change coeff 0 (U ℓ F) = 0
  rw [coeff_U, mul_zero]
  exact hF.1.1

include h29 in
lemma even_mem (n : ℕ) : Ll ℓ (2 * n + 2) ∈ envSub D.hℓ5 1 (α ℓ) := by
  refine ⟨?_, ?_⟩
  · rw [even_U]
    change coeff 0 (U ℓ (Ll ℓ (2 * n + 1))) = 0
    rw [coeff_U, mul_zero]
    exact (odd_mem h29 D.hlow n).1.1
  · simpa [γ, show Even (2 * n + 2) from ⟨n + 1, by ring⟩] using L_env h29 (2 * n + 2)

lemma even_succ (n : ℕ) : Ll ℓ (2 * n + 4) = Yop (Ll ℓ (2 * n + 2)) := by
  rw [show 2 * n + 4 = 2 * (n + 1) + 2 by omega, even_U, odd_D]
  rfl

include h29 h24 in
/-- `obs_a(Y L(2n+2)) = ℓ (Σ (U oₙ)ᵢ z_{ai} + ℓ w)`. -/
lemma obs_Y_even (n : ℕ) : ∃ c : Fin (s + r) → ℤ_[ℓ], (fun i => PadicInt.toZMod (c i)) =
    mv D.Umat (D.odd n) ∧ ∀ a, ∃ w' : ℤ_[ℓ],
      obs (D.w a) (Ll ℓ (2 * n + 4)) = (ℓ : ℤ_[ℓ]) * (∑ i, c i * (D.z a i : ℤ_[ℓ]) + ℓ * w') := by
  obtain ⟨c, R, hR, he⟩ := D.decompose h29 _ (D.even_mem h29 n)
  refine ⟨c, ?_, fun a => ?_⟩
  · apply D.comb_inj
    rw [← D.map_sum_lift, ← D.even_reduction h24 n, he, map_add, map_ell_smul, add_zero]
  · rw [even_succ]; exact D.obs_Y h29 h24 a _ R c hR he

end Data2

/-! ### The main theorem -/

/-- `obs_a(L(2j+2))/ℓ mod ℓ`: `zL2` at `j = 0`, then `Σᵢ (U o_{j-1})ᵢ z_{ai}`. -/
def Data2.zev (D : Data2 ℓ s r) (zL2 : Fin s → ℤ) : ℕ → Fin s → ZMod ℓ
  | 0 => fun a => ((zL2 a : ℤ) : ZMod ℓ)
  | j + 1 => fun a => ∑ i, mv D.Umat (D.odd j) i * ((D.z a i : ℤ) : ZMod ℓ)

/-- The predicted initial observations `obs_a(U G₀) mod ℓ`. -/
def Data2.init (D : Data2 ℓ s r) (k : Fin r → ZMod ℓ) (zL2 : Fin s → ℤ) : Fin s → ZMod ℓ :=
  fun a => D.zev zL2 r a - ∑ j, k j * D.zev zL2 j.val a

lemma mv_inv {θ θi : Fin s → Fin s → ZMod ℓ} (h : ∀ a c, ∑ b, θi a b * θ b c = if a = c then 1 else 0)
    (v : Fin s → ZMod ℓ) : mv θi (mv θ v) = v := by
  ext a
  simp only [mv, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ c, ∑ b, θi a b * (θ b c * v c) = (if a = c then 1 else 0) * v c := fun c => by
    rw [← h a c, Finset.sum_mul]; exact Finset.sum_congr rfl fun b _ => by ring
  simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

variable (D : Data2 ℓ s r) (h29 : 29 ≤ ℓ) (h24 : 24 * δ ℓ + 1 = ℓ ^ 2)

include h29 h24 in
lemma Data2.obs_even (zL2 : Fin s → ℤ)
    (hL2 : ∀ a, ∃ t : ℤ_[ℓ], obs (D.w a) (Ll ℓ 2) = (ℓ : ℤ_[ℓ]) * ((zL2 a : ℤ_[ℓ]) + ℓ * t))
    (j : ℕ) (a : Fin s) : ∃ x : ℤ_[ℓ], PadicInt.toZMod x = D.zev zL2 j a ∧
      ∃ t : ℤ_[ℓ], obs (D.w a) (Ll ℓ (2 * j + 2)) = (ℓ : ℤ_[ℓ]) * (x + ℓ * t) := by
  cases j with
  | zero =>
    obtain ⟨t, ht⟩ := hL2 a
    exact ⟨(zL2 a : ℤ_[ℓ]), by simp [Data2.zev], t, by simpa using ht⟩
  | succ j =>
    obtain ⟨c, hc, hw⟩ := D.obs_Y_even h29 h24 j
    obtain ⟨w', hw'⟩ := hw a
    refine ⟨∑ i, c i * (D.z a i : ℤ_[ℓ]), ?_, w', by
      rw [show 2 * (j + 1) + 2 = 2 * j + 4 by ring]; exact hw'⟩
    simp only [map_sum, map_mul, map_intCast, Data2.zev, ← hc]

include h29 h24 in
/-- **`b_ℓ(m) = 2m − 1` for every `m ≥ 1`, from order-`r` data with `s + r` forms.** -/
theorem Data2.bEll_eq (hr : 0 < r) {k : Fin r → ZMod ℓ} (hcay : D.odd r = ∑ j, k j • D.odd j.val)
    (hcomp : (comp k).det ≠ 0) (hdet₀ : D.det 0 ≠ 0) (zL2 : Fin s → ℤ)
    (hL2 : ∀ a, ∃ t : ℤ_[ℓ], obs (D.w a) (Ll ℓ 2) = (ℓ : ℤ_[ℓ]) * ((zL2 a : ℤ_[ℓ]) + ℓ * t))
    (θi : Fin s → Fin s → ZMod ℓ)
    (hθi : ∀ a c, ∑ b, θi a b * D.θ b c = if a = c then 1 else 0)
    (hinit : D.init k zL2 ≠ 0) (m : ℕ) (hm : 1 ≤ m) :
    BLBound.bEll ℓ m = 2 * m - 1 := by
  have hdet : ∀ n, D.det n ≠ 0 := fun n => by
    rw [D.det_eq hcay n]; exact mul_ne_zero hdet₀ (pow_ne_zero _ hcomp)
  obtain ⟨κ, hκ, h⟩ := odd_padicR h29 D.hlow h24 D.toData hcay hdet
  choose G hGm hG using h
  have hodd : ∀ n, Xop (Ll ℓ (2 * n + 1)) = Ll ℓ (2 * (n + 1) + 1) := fun n => (odd_succ n).symm
  -- `X Gₙ = ℓ Gₙ₊₁`
  have hX : ∀ n, Dlin ℓ (Ulin ℓ (G n)) = (ℓ : ℤ_[ℓ]) • G (n + 1) := by
    intro n
    have hh := congrArg Xop (hG n)
    rw [map_sub, map_sum, map_smul, hodd] at hh
    simp only [map_smul, hodd] at hh
    have hs := hG (n + 1)
    rw [show (ℓ : ℤ_[ℓ]) ^ (n + 1 + 1) = (ℓ : ℤ_[ℓ]) ^ (n + 1) * ℓ from pow_succ _ _, mul_smul,
      show 2 * (n + 1 + r) + 1 = 2 * (n + r + 1) + 1 by ring] at hs
    simp only [show ∀ j : Fin r, 2 * (n + 1 + j.val) + 1 = 2 * (n + j.val + 1) + 1 from
      fun j => by ring] at hs
    apply sub_eq_zero.mp
    apply cancel_pow (ℓ : ℤ_[ℓ]) PS_reg (n + 1)
    rw [smul_sub]
    change (ℓ : ℤ_[ℓ]) ^ (n + 1) • Xop (G n) - _ = 0
    rw [← hh, hs, sub_self]
  -- the initial observations
  have hinit' : ∀ a, PadicInt.toZMod (obs (D.w a) (Ulin ℓ (G 0))) = D.init k zL2 a := by
    intro a
    have hU := congrArg (Ulin ℓ) (hG 0)
    rw [map_sub, map_sum, map_smul, ← even_U] at hU
    simp only [map_smul, ← even_U, Nat.zero_add, zero_add, pow_one] at hU
    have hO := congrArg (obs (D.w a)) hU
    rw [map_sub, map_sum, map_smul, smul_eq_mul] at hO
    simp only [map_smul, smul_eq_mul] at hO
    choose x hx t ht using fun j => D.obs_even h29 h24 zL2 hL2 j a
    simp only [ht] at hO
    have hO' : obs (D.w a) (Ulin ℓ (G 0)) = (x r + ℓ * t r) - ∑ j, κ j * (x j.val + ℓ * t j.val) := by
      apply mul_left_cancel₀ (Data2.ell_ne (ℓ := ℓ))
      rw [← hO, mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hO', Data2.init]
    simp only [map_sub, map_mul, map_add, map_sum, toZMod_prime_zmod, zero_mul, add_zero, hx, hκ]
  set e : ℕ → Fin s → ZMod ℓ := fun n a => PadicInt.toZMod (obs (D.w a) (Ulin ℓ (G n))) with he
  have hstep : ∀ n, e (n + 1) = mv D.θ (e n) := fun n => by
    ext a
    exact D.divided_step h29 h24 a _ _ (D.U_mem h29 _ (hGm n)) (hX n)
  have herr : ∀ n, e n ≠ 0 := by
    intro n
    induction n with
    | zero =>
      have : e 0 = D.init k zL2 := funext hinit'
      rw [this]; exact hinit
    | succ n ih =>
      intro h0
      apply ih
      rw [← mv_inv hθi (e n), ← hstep, h0]
      ext a; simp [mv]
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  refine BLBound.bEll_eq_of_not_mem (by omega) m hm fun K hK => ?_
  obtain ⟨a, ha⟩ : ∃ a, e K a ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact herr K (funext hc)
  set k' : ℕ → ℤ_[ℓ] := fun j => if h : j < q + 1 then κ ⟨j, h⟩ else 0
  have hrec : ∀ n, Ll ℓ (2 * n + 2 * q + 3) -
      ∑ j ∈ Finset.range (q + 1), k' j • Ll ℓ (2 * (n + j) + 1) = (ℓ : ℤ_[ℓ]) ^ (n + 1) • G n := by
    intro n
    rw [← hG n, show 2 * (n + (q + 1)) + 1 = 2 * n + 2 * q + 3 by ring,
      ← Fin.sum_univ_eq_sum_range (fun j => k' j • Ll ℓ (2 * (n + j) + 1))]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by simp only [k', dif_pos j.isLt]
  refine BLBound.not_mem_of_errorsR q k' G (fun i => PowerSeries.coeff (s + 1 + i.val)) (obs (D.w a))
    hrec (fun n => ?_) m K hK ?_ ha
  · -- `obs_a ∘ U` kills the odd series
    rw [obs_reduce, reduce_U, D.odd_reduction h24, D.U_comb, D.obsBar_comb]
    exact D.obs_U_low a _ fun t => lin_zero_odd h29 D.hlow h24 D.toData n _ (by simp)
  · -- separation
    rw [RingHom.map_det]
    have : (PadicInt.toZMod (p := ℓ)).mapMatrix
        (fun i j : Fin (q + 1) => PowerSeries.coeff (s + 1 + i.val) (Ll ℓ (2 * (K + j.val) + 1))) =
        D.oddM K := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Data.oddM]
      rw [← coeff_map, D.odd_reduction h24, show s + 1 + i.val = (high s i).val + 1 by
        simp [high]; ring, D.coeff_comb]
      rfl
    rw [this]
    exact hdet K

end RamanujanTau.FiniteArithmetic.RankR
