import RamanujanTau.FiniteArithmetic.RankSError
import RamanujanTau.BLBound.Threshold2

/-!
# `b_ℓ(m) = 2m − 1` from finite data with `s + 2` forms

`RankS.Data2.bEll_eq`: the `Rank2Main` theorem when `D` kills `a₁, …, a_s` and the error is
seen by `s` observations. The vector `eₙ = (obs_a(U Gₙ))_a mod ℓ` satisfies `eₙ₊₁ = θ eₙ`
(`divided_step`). With `θ` invertible and `e₀ ≠ 0` it never vanishes, so at each `n` some
observation sees `Gₙ`, which feeds `BLBound.not_mem_of_errors2_at`.
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.RankS
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal

variable {ℓ s : ℕ} [hℓ : Fact ℓ.Prime]

namespace Data2
variable (D : Data2 ℓ s) (h29 : 29 ≤ ℓ) (h24 : 24 * δ ℓ + 1 = ℓ ^ 2)

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
  set cb : Fin (s + 2) → ZMod ℓ := fun i => PadicInt.toZMod (c i)
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
lemma obs_Y_even (n : ℕ) : ∃ c : Fin (s + 2) → ℤ_[ℓ], (fun i => PadicInt.toZMod (c i)) =
    mv D.Umat (D.odd n) ∧ ∀ a, ∃ w' : ℤ_[ℓ],
      obs (D.w a) (Ll ℓ (2 * n + 4)) = (ℓ : ℤ_[ℓ]) * (∑ i, c i * (D.z a i : ℤ_[ℓ]) + ℓ * w') := by
  obtain ⟨c, R, hR, he⟩ := D.decompose h29 _ (D.even_mem h29 n)
  refine ⟨c, ?_, fun a => ?_⟩
  · apply D.comb_inj
    rw [← D.map_sum_lift, ← D.even_reduction h24 n, he, map_add, map_ell_smul, add_zero]
  · rw [even_succ]; exact D.obs_Y h29 h24 a _ R c hR he

end Data2

/-! ### The main theorem -/

/-- The predicted initial observations `obs_a(U G₀) mod ℓ`. -/
def Data2.init (D : Data2 ℓ s) (k₀ k₁ : ZMod ℓ) (zL2 : Fin s → ℤ) : Fin s → ZMod ℓ := fun a =>
  ∑ i, mv D.Umat (D.odd 1) i * ((D.z a i : ℤ) : ZMod ℓ) -
    k₁ * ∑ i, mv D.Umat (D.odd 0) i * ((D.z a i : ℤ) : ZMod ℓ) - k₀ * ((zL2 a : ℤ) : ZMod ℓ)

lemma mv_inv {θ θi : Fin s → Fin s → ZMod ℓ} (h : ∀ a c, ∑ b, θi a b * θ b c = if a = c then 1 else 0)
    (v : Fin s → ZMod ℓ) : mv θi (mv θ v) = v := by
  ext a
  simp only [mv, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ c, ∑ b, θi a b * (θ b c * v c) = (if a = c then 1 else 0) * v c := fun c => by
    rw [← h a c, Finset.sum_mul]; exact Finset.sum_congr rfl fun b _ => by ring
  simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

variable (D : Data2 ℓ s) (h29 : 29 ≤ ℓ) (h24 : 24 * δ ℓ + 1 = ℓ ^ 2)

include h29 h24 in
/-- **`b_ℓ(m) = 2m − 1` for every `m ≥ 1`, from data with `s + 2` forms.** -/
theorem Data2.bEll_eq {k₀ k₁ : ZMod ℓ} (hcay : D.odd 2 = k₁ • D.odd 1 + k₀ • D.odd 0)
    (hk₀ : k₀ ≠ 0) (hdet₀ : D.det 0 ≠ 0) (zL2 : Fin s → ℤ)
    (hL2 : ∀ a, ∃ t : ℤ_[ℓ], obs (D.w a) (Ll ℓ 2) = (ℓ : ℤ_[ℓ]) * ((zL2 a : ℤ_[ℓ]) + ℓ * t))
    (θi : Fin s → Fin s → ZMod ℓ)
    (hθi : ∀ a c, ∑ b, θi a b * D.θ b c = if a = c then 1 else 0)
    (hinit : D.init k₀ k₁ zL2 ≠ 0) (m : ℕ) (hm : 1 ≤ m) :
    BLBound.bEll ℓ m = 2 * m - 1 := by
  have hdet : ∀ n, D.det n ≠ 0 := fun n => by
    rw [D.det_eq hcay n]; exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hk₀)) hdet₀
  obtain ⟨κ₀, κ₁, hκ₀, hκ₁, h⟩ := odd_padic2 h29 D.hlow h24 D.toData hcay hdet
  choose G hGm hG using h
  -- `X Gₙ = ℓ Gₙ₊₁`
  have hX : ∀ n, Dlin ℓ (Ulin ℓ (G n)) = (ℓ : ℤ_[ℓ]) • G (n + 1) := by
    intro n
    have hh := congrArg Xop (hG n)
    rw [map_sub, map_sub, map_smul, map_smul, map_smul] at hh
    have hs := hG (n + 1)
    have a1 : Ll ℓ (2 * (n + 1) + 5) = Xop (Ll ℓ (2 * n + 5)) := by
      have := odd_succ (ℓ := ℓ) (n + 2)
      rwa [show 2 * (n + 2 + 1) + 1 = 2 * (n + 1) + 5 by ring, show 2 * (n + 2) + 1 = 2 * n + 5 by ring] at this
    have a2 : Ll ℓ (2 * (n + 1) + 3) = Xop (Ll ℓ (2 * n + 3)) := by
      have := odd_succ (ℓ := ℓ) (n + 1)
      rwa [show 2 * (n + 1 + 1) + 1 = 2 * (n + 1) + 3 by ring, show 2 * (n + 1) + 1 = 2 * n + 3 by ring] at this
    have a3 : Ll ℓ (2 * (n + 1) + 1) = Xop (Ll ℓ (2 * n + 1)) := odd_succ n
    rw [a1, a2, a3, hh, show (ℓ : ℤ_[ℓ]) ^ (n + 1 + 1) = (ℓ : ℤ_[ℓ]) ^ (n + 1) * ℓ from pow_succ _ _,
      mul_smul] at hs
    apply sub_eq_zero.mp
    apply cancel_pow (ℓ : ℤ_[ℓ]) PS_reg (n + 1)
    rw [smul_sub]
    change (ℓ : ℤ_[ℓ]) ^ (n + 1) • Xop (G n) - _ = 0
    rw [hs, sub_self]
  -- the initial observations
  have hinit' : ∀ a, PadicInt.toZMod (obs (D.w a) (Ulin ℓ (G 0))) = D.init k₀ k₁ zL2 a := by
    intro a
    have hU := congrArg (Ulin ℓ) (hG 0)
    have u5 : Ulin ℓ (Ll ℓ 5) = Ll ℓ 6 := by rw [show (6 : ℕ) = 2 * 2 + 2 from rfl, even_U]
    have u3 : Ulin ℓ (Ll ℓ 3) = Ll ℓ 4 := by rw [show (4 : ℕ) = 2 * 1 + 2 from rfl, even_U]
    have u1 : Ulin ℓ (Ll ℓ 1) = Ll ℓ 2 := by rw [show (2 : ℕ) = 2 * 0 + 2 from rfl, even_U]
    rw [map_sub, map_sub, map_smul, map_smul, map_smul] at hU
    simp only [Nat.mul_zero, Nat.zero_add, pow_one] at hU
    rw [u5, u3, u1] at hU
    obtain ⟨c, hc, hw₁⟩ := D.obs_Y_even h29 h24 0
    obtain ⟨c', hc', hw₂⟩ := D.obs_Y_even h29 h24 1
    obtain ⟨w₁, hw₁⟩ := hw₁ a
    obtain ⟨w₂, hw₂⟩ := hw₂ a
    obtain ⟨t, ht⟩ := hL2 a
    have hO := congrArg (obs (D.w a)) hU
    rw [map_sub, map_sub, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at hO
    simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at hw₁ hw₂
    rw [show 2 * 1 + 4 = 6 from rfl] at hw₂
    rw [hw₁, hw₂, ht] at hO
    have hO' : obs (D.w a) (Ulin ℓ (G 0)) = (∑ i, c' i * (D.z a i : ℤ_[ℓ]) + ℓ * w₂) -
        κ₁ * (∑ i, c i * (D.z a i : ℤ_[ℓ]) + ℓ * w₁) - κ₀ * ((zL2 a : ℤ_[ℓ]) + ℓ * t) := by
      apply mul_left_cancel₀ (Data2.ell_ne (ℓ := ℓ))
      linear_combination -hO
    rw [hO', Data2.init]
    simp only [map_sub, map_mul, map_add, map_sum, toZMod_prime_zmod, zero_mul, add_zero,
      map_intCast, hκ₀, hκ₁]
    rw [← hc, ← hc']
  set e : ℕ → Fin s → ZMod ℓ := fun n a => PadicInt.toZMod (obs (D.w a) (Ulin ℓ (G n))) with he
  have hstep : ∀ n, e (n + 1) = mv D.θ (e n) := fun n => by
    ext a
    exact D.divided_step h29 h24 a _ _ (D.U_mem h29 _ (hGm n)) (hX n)
  have herr : ∀ n, e n ≠ 0 := by
    intro n
    induction n with
    | zero =>
      have : e 0 = D.init k₀ k₁ zL2 := funext hinit'
      rw [this]; exact hinit
    | succ n ih =>
      intro h0
      apply ih
      rw [← mv_inv hθi (e n), ← hstep, h0]
      ext a; simp [mv]
  refine BLBound.bEll_eq_of_not_mem (by omega) m hm fun k hk => ?_
  obtain ⟨a, ha⟩ : ∃ a, e k a ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact herr k (funext hc)
  refine BLBound.not_mem_of_errors2_at κ₀ κ₁ G (PowerSeries.coeff (s + 1)) (PowerSeries.coeff (s + 2))
    (obs (D.w a)) hG (fun n => ?_) (fun n => ?_) m k hk ha
  · -- separation
    have h1 := D.odd_reduction h24 n
    have h2 := D.odd_reduction h24 (n + 1)
    rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring] at h2
    simp only [BLBound.det2, map_sub, map_mul]
    have c2 : ∀ v, coeff (s + 1) (D.comb v) = lin D.toData (iS s) v := fun v => D.coeff_comb v (iS s)
    have c3 : ∀ v, coeff (s + 2) (D.comb v) = lin D.toData (iT s) v := fun v => D.coeff_comb v (iT s)
    rw [← coeff_map, ← coeff_map, ← coeff_map, ← coeff_map, h1, h2, c2, c2, c3, c3]
    exact hdet n
  · -- `obs_a ∘ U` kills the odd series
    rw [obs_reduce, reduce_U, D.odd_reduction h24, D.U_comb, D.obsBar_comb]
    exact D.obs_U_low a _ fun t => lin_zero_odd h29 D.hlow h24 D.toData n _ (by simp)

end RamanujanTau.FiniteArithmetic.RankS
