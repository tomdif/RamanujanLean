import RamanujanTau.BLBound.ThetaFiltration

/-!
# No Ramanujan congruence at the class `24β ≡ 1` for `ℓ ≥ 13`

This is the theorem of Ahlgren–Boylan for that class. If `U(Δ^δ) ≡ 0` then `θ^(ℓ-1)` fixes `Δ^δ`. Every term of the
cycle vanishes to order `δ`, so has filtration at least `12δ`, and `cycle_weight_four` forces
`θ^((ℓ+3)/2) Δ^δ = c E₄ Δ^δ`. Comparing two coefficients gives `(-23)^((ℓ+3)/2) ≡ 241`, so `ℓ ∣ 23⁴ - 241²`, whose prime
factors are `2, 3, 5, 7, 11`.

Hence `L(2k+1) ≢ 0 (mod ℓ)` for all `k`, and the stable module is never zero.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.BLBound
open MvPolynomial ModP Igusa BoylanWebb AtkinOBrien AtkinOBrienFinal
open RamanujanTau.TheoremA.HalfIntegral

noncomputable section

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma formBar_Dl (h5 : 5 ≤ ℓ) : FormBar ℓ 12 (Dl ℓ) := by
  have h1728 := ne_zero_1728 (p := ℓ) h5
  refine ⟨C (1728 : ZMod ℓ)⁻¹ * disc (ZMod ℓ), iso_disc.C_mul _, ?_⟩
  rw [map_mul, ev_disc, ev_C]
  have e : (1728 : PowerSeries (ZMod ℓ)) = PowerSeries.C (1728 : ZMod ℓ) := (map_ofNat _ 1728).symm
  rw [e, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h1728, map_one, one_mul]

lemma formBar_Dl_pow (h5 : 5 ≤ ℓ) (d : ℕ) : FormBar ℓ (12 * d) (Dl ℓ ^ d) := by
  obtain ⟨P, hP, he⟩ := formBar_Dl (ℓ := ℓ) h5
  refine ⟨P ^ d, iso_of_eq (hP.pow d) (by rw [smul_eq_mul, mul_comm]), ?_⟩
  rw [map_pow, he]

lemma coeff_theta_iter (m n : ℕ) (f : PowerSeries (ZMod ℓ)) :
    PowerSeries.coeff n (Igusa.theta^[m] f) = (n : ZMod ℓ) ^ m * PowerSeries.coeff n f := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', coeff_theta, ih, pow_succ]
    ring

lemma coeff_one_qfac : PowerSeries.coeff 1 (MockTheta5.JTP.qfacInf : PowerSeries ℤ) = -1 := by
  have h := congrArg (PowerSeries.coeff 1) qfac_mul_pgf
  have h0 : PowerSeries.coeff 0 (MockTheta5.JTP.qfacInf : PowerSeries ℤ) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact constantCoeff_qfac
  have hp0 : PowerSeries.coeff 0 MockTheta5.JTP.partitionGF = (1 : ℤ) := by
    rw [MockTheta5.JTP.coeff_partitionGF_eq_card]
    simp
  have hp1 : PowerSeries.coeff 1 MockTheta5.JTP.partitionGF = (1 : ℤ) := by
    rw [MockTheta5.JTP.coeff_partitionGF_eq_card]
    simp
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ] at h
  simp only [Finset.Nat.antidiagonal_zero, Finset.cons_eq_insert, Finset.map_singleton,
    Function.Embedding.prodMap, Function.Embedding.coeFn_mk, Prod.map, Finset.mem_singleton,
    Finset.sum_insert, Finset.sum_singleton, PowerSeries.coeff_one] at h
  simp at h
  have hp0' : PowerSeries.constantCoeff MockTheta5.JTP.partitionGF = (1 : ℤ) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hp0
  simp [h0, hp0', hp1] at h
  linarith

lemma coeff_one_pow {u : PowerSeries ℤ} (h0 : PowerSeries.constantCoeff u = 1) (n : ℕ) :
    PowerSeries.coeff 1 (u ^ n) = n * PowerSeries.coeff 1 u := by
  have h00 : PowerSeries.coeff 0 u = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
  induction n with
  | zero => simp [PowerSeries.coeff_one]
  | succ n ih =>
    have hc : PowerSeries.coeff 0 (u ^ n) = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, h0, one_pow]
    rw [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]
    simp [hc, h00, ih]
    ring

/-- `(q;q)^{ℓ²-1}` starts `1 + q + ⋯` modulo `ℓ`. -/
lemma coeff_h (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) :
    PowerSeries.coeff 0 (PowerSeries.map (Int.castRingHom (ZMod ℓ))
        (MockTheta5.JTP.qfacInf ^ (24 * δ ℓ))) = 1 ∧
      PowerSeries.coeff 1 (PowerSeries.map (Int.castRingHom (ZMod ℓ))
        (MockTheta5.JTP.qfacInf ^ (24 * δ ℓ))) = 1 := by
  have hx : ((24 * δ ℓ : ℕ) : ZMod ℓ) + 1 = 0 := by
    have := congrArg (Nat.cast : ℕ → ZMod ℓ) h24
    push_cast at this ⊢
    rw [this, CharP.cast_eq_zero (ZMod ℓ) ℓ]
    simp [hℓ.out.ne_zero]
  constructor
  · rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_qfac]
    simp
  · rw [PowerSeries.coeff_map, coeff_one_pow constantCoeff_qfac, coeff_one_qfac, eq_intCast]
    push_cast at hx ⊢
    linear_combination -hx

lemma ell_dvd_contra (h13 : 13 ≤ ℓ) (h : ℓ ∣ 2 ^ 6 * (3 ^ 2 * (5 * (7 * 11)))) : False := by
  have hp := hℓ.out
  rcases (hp.dvd_mul).mp h with h | h
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
    omega
  rcases (hp.dvd_mul).mp h with h | h
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
    omega
  rcases (hp.dvd_mul).mp h with h | h
  · have := Nat.le_of_dvd (by norm_num) h
    omega
  rcases (hp.dvd_mul).mp h with h | h
  · have := Nat.le_of_dvd (by norm_num) h
    omega
  · have := Nat.le_of_dvd (by norm_num) h
    omega

/-- The final arithmetic. -/
lemma arith_contra (h13 : 13 ≤ ℓ) {s : ℕ} (hs : ℓ = 2 * s + 1) {x c : ZMod ℓ} (hx : 24 * x + 1 = 0)
    (h1 : x ^ (s + 2) = c) (h2 : (x + 1) ^ (s + 2) = 241 * c) : False := by
  have hp := hℓ.out
  have e23 : (24 * x + 24) = 23 := by linear_combination hx
  have hE : (23 : ZMod ℓ) ^ (s + 2) = 241 * (-1) ^ (s + 2) := by
    have hm1 : 24 * x = -1 := by linear_combination hx
    calc (23 : ZMod ℓ) ^ (s + 2) = (24 * (x + 1)) ^ (s + 2) := by rw [← e23]; ring
      _ = 24 ^ (s + 2) * (241 * x ^ (s + 2)) := by rw [mul_pow, h2, h1]
      _ = 241 * (24 * x) ^ (s + 2) := by rw [mul_pow]; ring
      _ = _ := by rw [hm1]
  have hsq : (23 : ZMod ℓ) ^ (2 * s) * 23 ^ 4 = 241 ^ 2 := by
    have := congrArg (· ^ 2) hE
    simp only at this
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (s + 2) 2, pow_mul (-1 : ZMod ℓ) 2] at this
    simp only [neg_one_sq, one_pow, mul_one] at this
    rw [← pow_add, show 2 * s + 4 = 2 * (s + 2) by ring]
    exact this
  by_cases h0 : (23 : ZMod ℓ) = 0
  · rw [h0] at hsq
    have h241' : (241 : ZMod ℓ) ^ 2 = 0 := by
      rw [← hsq]
      simp
    have h241 : ((58081 : ℕ) : ZMod ℓ) = 0 := by
      push_cast
      linear_combination h241'
    have h23 : ((23 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h0
    have hd := Nat.dvd_gcd ((ZMod.natCast_eq_zero_iff _ _).mp h23) ((ZMod.natCast_eq_zero_iff _ _).mp h241)
    norm_num at hd
    exact hp.one_lt.ne' hd
  · have hone : (23 : ZMod ℓ) ^ (2 * s) = 1 := by
      have := ZMod.pow_card_sub_one_eq_one h0
      rwa [show ℓ - 1 = 2 * s by omega] at this
    rw [hone, one_mul] at hsq
    have hN : ((2 ^ 6 * (3 ^ 2 * (5 * (7 * 11))) : ℕ) : ZMod ℓ) = 0 := by
      push_cast
      linear_combination hsq
    exact ell_dvd_contra h13 ((ZMod.natCast_eq_zero_iff _ _).mp hN)

/-- **`U(Δ^δ) ≢ 0 (mod ℓ)` for every prime `ℓ ≥ 13`.** -/
theorem U_Dl_ne_zero (h13 : 13 ≤ ℓ) : U ℓ (Dl ℓ ^ δ ℓ) ≠ 0 := by
  intro hU
  have hp := hℓ.out
  have h5 : 5 ≤ ℓ := by omega
  have h24' := h24 (ℓ := ℓ) h13
  obtain ⟨s, hs⟩ : ∃ s, ℓ = 2 * s + 1 := by
    obtain ⟨s, hs⟩ := hp.odd_of_ne_two (by omega)
    exact ⟨s, hs⟩
  have hs6 : 6 ≤ s := by omega
  have hl1 : ℓ - 1 = 2 * s := by omega
  set dl := δ ℓ with hdl
  have hK : 12 * dl = 2 * s ^ 2 + 2 * s := by
    have : 24 * dl = 4 * s ^ 2 + 4 * s := by
      have e : ℓ ^ 2 = 4 * s ^ 2 + 4 * s + 1 := by rw [hs]; ring
      omega
    omega
  set f := Dl ℓ ^ dl with hf
  have hx : 24 * (dl : ZMod ℓ) + 1 = 0 := by
    have := congrArg (Nat.cast : ℕ → ZMod ℓ) h24'
    push_cast at this
    rw [this, CharP.cast_eq_zero (ZMod ℓ) ℓ]
    simp [hp.ne_zero]
  have hx0 : (dl : ZMod ℓ) ≠ 0 := by
    intro h
    rw [h] at hx
    simp at hx
  obtain ⟨hc0, hc1⟩ := coeff_h (ℓ := ℓ) h24'
  set h := PowerSeries.map (Int.castRingHom (ZMod ℓ)) (MockTheta5.JTP.qfacInf ^ (24 * dl)) with hh
  have hfX : f = PowerSeries.X ^ dl * h := Dl_pow dl
  have hfd : PowerSeries.coeff dl f = 1 := by
    rw [hfX, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, hc0]
  have hfd1 : PowerSeries.coeff (dl + 1) f = 1 := by
    rw [hfX, PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel_left, hc1]
  have hflow : ∀ n < dl, PowerSeries.coeff n f = 0 := by
    intro n hn
    rw [hfX, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  have hf12 := formBar_Dl_pow (ℓ := ℓ) h5 dl
  let g : ℕ → PowerSeries (ZMod ℓ) := fun i => Igusa.theta^[i] f
  have hg0 : ∀ i, g i ≠ 0 := by
    intro i hi
    have := congrArg (PowerSeries.coeff dl) hi
    simp only [g, map_zero] at this
    rw [coeff_theta_iter, hfd, mul_one] at this
    exact pow_ne_zero _ hx0 this
  have hglow : ∀ i, ∀ n < dl, PowerSeries.coeff n (g i) = 0 := by
    intro i n hn
    simp only [g]
    rw [coeff_theta_iter, hflow n hn, mul_zero]
  have hclass : ∀ i, (12 * dl + i * (ℓ + 1)) % (ℓ - 1) = (12 * dl + 2 * i) % (ℓ - 1) := by
    intro i
    have e : 12 * dl + i * (ℓ + 1) = 12 * dl + 2 * i + (ℓ - 1) * i := by
      rw [show ℓ + 1 = (ℓ - 1) + 2 by omega]
      ring
    rw [e, Nat.add_mul_mod_self_left]
  have hFg : ∀ i, FormBar ℓ (12 * dl + i * (ℓ + 1)) (g i) := fun i => hf12.theta_iter h5 i
  let W : ℕ → ℕ := fun i => filt ℓ (12 * dl + 2 * i) (g i)
  have hrep : ∀ i, FormBar ℓ (W i) (g i) := fun i => (filt_spec (hclass i) (hFg i)).2
  have hlower : ∀ i, 12 * dl ≤ W i := by
    intro i
    obtain ⟨P, hP, he⟩ := hrep i
    refine (div_Delta_pow h5 dl hP (by rw [he]; exact hglow i) (by rw [he]; exact hg0 i)).1
  have hstep : ∀ i, ∃ d : ℕ, W i + (ℓ + 1) = W (i + 1) + (ℓ - 1) * d ∧ (¬ ℓ ∣ W i → d = 0) := by
    intro i
    have eg : Igusa.theta (g i) = g (i + 1) := (Function.iterate_succ_apply' _ _ _).symm
    have er : 12 * dl + 2 * i + 2 = 12 * dl + 2 * (i + 1) := by ring
    obtain ⟨d, hd⟩ := filt_theta_step h5 (hclass i) (hFg i)
    rw [eg, er] at hd
    refine ⟨d, hd, fun hnd => ?_⟩
    have hk : ((W i : ℕ) : ZMod ℓ) ≠ 0 := fun h0 => hnd ((ZMod.natCast_eq_zero_iff _ _).mp h0)
    have heq := filt_theta_eq h5 (hclass i) (hFg i) (hg0 i) hk
    rw [eg, er] at heq
    change W (i + 1) = W i + (ℓ + 1) at heq
    have h2 : (ℓ - 1) * d = 0 := by
      change W i + (ℓ + 1) = W (i + 1) + (ℓ - 1) * d at hd
      omega
    exact (Nat.mul_eq_zero.mp h2).resolve_left (by omega)
  choose d hd hdrop using hstep
  have hW0 : W 0 = 12 * dl := by
    refine le_antisymm ?_ (hlower 0)
    exact filt_le (by rfl) hf12
  have hcycle : g (2 * s) = f := by
    have h1 := U_pow_char f
    rw [hU, zero_pow hp.ne_zero, hl1] at h1
    exact (sub_eq_zero.mp h1.symm).symm
  have hclose : W (2 * s) = 12 * dl := by
    rw [← hW0]
    change filt ℓ (12 * dl + 2 * (2 * s)) (g (2 * s)) = filt ℓ (12 * dl + 2 * 0) (g 0)
    rw [hcycle]
    refine filt_congr f ?_
    rw [hl1, show 12 * dl + 2 * (2 * s) = 12 * dl + 2 * 0 + 2 * s * 2 by ring, Nat.add_mul_mod_self_left]
  have hmain := cycle_weight_four s (by omega) ((12 * dl : ℕ) : ℤ) (by rw [hK]; push_cast; ring)
    (fun i => (W i : ℤ)) (fun i => (d i : ℤ))
    (fun i _ => by
      change ((12 * dl : ℕ) : ℤ) ≤ (W i : ℤ)
      exact_mod_cast hlower i) (fun i _ => by positivity)
    (fun i _ => by
      have := hd i
      rw [hl1] at this
      have e : ((W i + (ℓ + 1) : ℕ) : ℤ) = ((W (i + 1) + 2 * s * d i : ℕ) : ℤ) := by rw [this]
      rw [hs] at e
      push_cast at e ⊢
      linear_combination -e)
    (fun i _ hnd => by
      have hnd' : ¬ ℓ ∣ W i := by
        intro h0
        apply hnd
        have : ((ℓ : ℕ) : ℤ) ∣ (W i : ℤ) := by exact_mod_cast h0
        rw [hs] at this
        push_cast at this
        exact this
      simp [hdrop i hnd'])
    (by
      change (W 0 : ℤ) = ((12 * dl : ℕ) : ℤ)
      exact_mod_cast hW0) (by
      change (W (2 * s) : ℤ) = ((12 * dl : ℕ) : ℤ)
      exact_mod_cast hclose)
  have hW4 : W (s + 2) = 12 * dl + 4 := by
    have hm' : (W (s + 2) : ℤ) = ((12 * dl : ℕ) : ℤ) + 4 := hmain
    exact_mod_cast hm'
  obtain ⟨P, hP, he⟩ := hrep (s + 2)
  obtain ⟨-, Q, hQ, heQ⟩ := div_Delta_pow h5 dl hP (by rw [he]; exact hglow _) (by rw [he]; exact hg0 _)
  rw [hW4, Nat.add_sub_cancel_left] at hQ
  obtain ⟨Q₀, -, hQ₀, hQe⟩ := disc_decomp hQ
  rw [hQ₀ (by norm_num), mul_zero, add_zero] at hQe
  set c := eval one2 Q with hc
  have hb4 : (base 4 : MvPolynomial (Fin 2) (ZMod ℓ)) = X 0 := by
    simp [base, bexp0, bexp1]
  have hevQ : ev (ZMod ℓ) Q = PowerSeries.C c * E4 (ZMod ℓ) := by
    rw [hQe, map_mul, ev_C, hb4, ev_X0]
  have hgform : g (s + 2) = PowerSeries.X ^ dl * (h * (PowerSeries.C c * E4 (ZMod ℓ))) := by
    rw [← he, heQ, hevQ]
    change f * _ = _
    rw [hfX, mul_assoc]
  have hE40 : PowerSeries.coeff 0 (E4 (ZMod ℓ)) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_E4]
  have hE41 : PowerSeries.coeff 1 (E4 (ZMod ℓ)) = 240 := by
    rw [E4, PowerSeries.coeff_map, RamanujanTau.Mod691.coeff_p4]
    simp
  have e1 : (dl : ZMod ℓ) ^ (s + 2) = c := by
    have := congrArg (PowerSeries.coeff dl) hgform
    simp only [g] at this
    rw [coeff_theta_iter, hfd, mul_one, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      mul_left_comm, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul] at this
    simpa [hc0, hE40] using this
  have e2 : ((dl : ZMod ℓ) + 1) ^ (s + 2) = 241 * c := by
    have := congrArg (PowerSeries.coeff (dl + 1)) hgform
    simp only [g] at this
    rw [coeff_theta_iter, hfd1, mul_one, PowerSeries.coeff_X_pow_mul', if_pos (by omega),
      Nat.add_sub_cancel_left, mul_left_comm, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
      Finset.Nat.antidiagonal_succ] at this
    simp [hc0, hc1, hE40, hE41] at this
    rw [this]
    ring
  exact arith_contra h13 hs hx e1 e2

lemma Psi_Dz_pow : Ψ ℓ (Dz ^ δ ℓ) = Dl ℓ ^ δ ℓ := by
  rw [map_pow]
  rfl

/-- **`L(1) ≢ 0 (mod ℓ)` for every prime `ℓ ≥ 13`.** -/
theorem L_one_ne_zero (h13 : 13 ≤ ℓ) : Ψ ℓ (L ℓ 1) ≠ 0 := by
  have h24' := h24 (ℓ := ℓ) h13
  have e : Ψ ℓ (L ℓ 1) = U ℓ (Dl ℓ ^ δ ℓ) := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, L_succ, Ψ_T_even ℓ h24' 0 (by simp), Psi_Dz_pow]
    simp [L]
  rw [e]
  exact U_Dl_ne_zero h13

/-- **The theorem of Ahlgren–Boylan at the class `24ν ≡ 1`.** For every prime `ℓ ≥ 13` there is `ν` with
`24ν ≡ 1 (mod ℓ)` and `ℓ ∤ p(ν)`. -/
theorem exists_partition_not_dvd (h13 : 13 ≤ ℓ) :
    ∃ ν : ℕ, (ℓ : ℤ) ∣ 24 * ν - 1 ∧ ¬ (ℓ : ℤ) ∣ (Fintype.card (Nat.Partition ν) : ℤ) := by
  have h24' := h24 (ℓ := ℓ) h13
  have hL := (L_eq_partition ℓ h24' 0).2
  have hne := L_one_ne_zero (ℓ := ℓ) h13
  rw [show 2 * 0 + 1 = 1 from rfl] at hL
  rw [hL, map_mul] at hne
  have hP : Ψ ℓ (Pser ℓ 1) ≠ 0 := right_ne_zero_of_mul hne
  obtain ⟨t, ht⟩ : ∃ t, PowerSeries.coeff t (Ψ ℓ (Pser ℓ 1)) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hP (PowerSeries.ext fun n => by rw [hc n, map_zero])
  rw [PowerSeries.coeff_map, Pser, PowerSeries.coeff_mk] at ht
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = (ℓ : ℤ) ^ 1 * t - eB ℓ 1 := ⟨_, rfl⟩
  rw [← hn] at ht
  have hn0 : 0 ≤ n := by
    by_contra hneg
    apply ht
    rw [pZ, if_pos (by omega)]
    simp
  obtain ⟨ν, hν⟩ := Int.eq_ofNat_of_zero_le hn0
  refine ⟨ν, ?_, ?_⟩
  · have he := ek_mul ℓ h24' 1
    have heB : eB ℓ 1 = ek ℓ 1 := rfl
    refine ⟨24 * t - ℓ, ?_⟩
    rw [← hν, hn, heB, pow_one]
    linear_combination -he
  · rw [hν, pZ_natCast] at ht
    intro hd
    exact ht ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd)

/-- **No Ramanujan congruence for `ℓ ≥ 13`**, at the class `24β ≡ 1`. -/
theorem no_ramanujan_congruence (h13 : 13 ≤ ℓ) {β : ℕ} (hβ : β < ℓ) (hc : (ℓ : ℤ) ∣ 24 * β - 1) :
    ¬ ∀ n : ℕ, ℓ ∣ Fintype.card (Nat.Partition (ℓ * n + β)) := by
  intro hall
  obtain ⟨ν, hν, hnd⟩ := exists_partition_not_dvd (ℓ := ℓ) h13
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ.out
  have h1 : (ℓ : ℤ) ∣ 24 * ((ν : ℤ) - β) := by
    have := dvd_sub hν hc
    convert this using 1
    ring
  have h2 : (ℓ : ℤ) ∣ (ν : ℤ) - β := by
    refine (hprime.dvd_or_dvd h1).resolve_left fun h => ?_
    have h' : ℓ ∣ 2 ^ 3 * 3 := by exact_mod_cast h
    rcases (hℓ.out.dvd_mul).mp h' with h'' | h''
    · have := Nat.le_of_dvd (by norm_num) (hℓ.out.dvd_of_dvd_pow h'')
      omega
    · have := Nat.le_of_dvd (by norm_num) h''
      omega
  have hmod : ν % ℓ = β := by
    have := (Nat.modEq_iff_dvd.mpr h2)
    rw [Nat.ModEq, Nat.mod_eq_of_lt hβ] at this
    exact this.symm
  apply hnd
  have := hall (ν / ℓ)
  rw [← hmod, Nat.div_add_mod] at this
  exact_mod_cast this

/-! ### The module is never zero -/

lemma Psi_L_step (h24' : 24 * δ ℓ + 1 = ℓ ^ 2) (k : ℕ) :
    Ψ ℓ (L ℓ (2 * (k + 1) + 1)) = Xbar ℓ (Ψ ℓ (L ℓ (2 * k + 1))) := by
  rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, L_succ, T, if_pos ⟨k + 1, by ring⟩, map_U, map_mul,
    L_succ ℓ (2 * k + 1), T, if_neg (not_even_2b1 k), map_U]
  rfl

/-- **`L(2k+1) ≢ 0 (mod ℓ)` for all `k`.** -/
theorem L_odd_ne_zero (h13 : 13 ≤ ℓ) (k : ℕ) : Ψ ℓ (L ℓ (2 * k + 1)) ≠ 0 ∧ Ψ ℓ (L ℓ (2 * k + 1)) ∈ Vbar ℓ := by
  have h5 : 5 ≤ ℓ := by omega
  have h24' := h24 (ℓ := ℓ) h13
  induction k with
  | zero =>
    refine ⟨L_one_ne_zero h13, ?_⟩
    have e : Ll ℓ 1 = Dlin ℓ 1 := by
      have := odd_D (ℓ := ℓ) 0
      simpa [Ll, L] using this
    have hV : red ℓ (Dlin ℓ 1) ∈ Vbar ℓ := by
      refine red_D_mem h13 ⟨hasseBar ℓ h5, iso_hasseBar h5, ?_⟩
      rw [ev_hasseBar, map_one]
    rw [← e] at hV
    have e2 : red ℓ (Ll ℓ 1) = Ψ ℓ (L ℓ 1) := by
      rw [Ll, map_map_int]
    rw [e2] at hV
    exact hV
  | succ k ih =>
    rw [Psi_L_step h24']
    exact ⟨fun h0 => ih.1 (Xbar_inj h13 ih.2 h0), Xbar_mem h13 ih.2⟩

/-- The generators are nonzero modulo `ℓ^m`. -/
lemma gm_ne_zero (h13 : 13 ≤ ℓ) (m : ℕ) (hm : 1 ≤ m) (k : ℕ) : gm ℓ m k ≠ 0 := by
  intro h0
  apply (L_odd_ne_zero (ℓ := ℓ) h13 k).1
  ext n
  have hc := congrArg (PowerSeries.coeff n) h0
  rw [gm, PowerSeries.coeff_map, map_zero] at hc
  rw [PowerSeries.coeff_map, map_zero]
  have hd : (ℓ ^ m : ℤ) ∣ PowerSeries.coeff n (L ℓ (2 * k + 1)) := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (ℓ ^ m)).mp hc
    exact_mod_cast this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mpr ((dvd_pow_self _ (by omega)).trans hd)

/-- **`r_ℓ(m) ≥ 1`.** -/
theorem rEll_pos (h13 : 13 ≤ ℓ) (m : ℕ) (hm : 1 ≤ m) : 1 ≤ rEll ℓ m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨s, -, hspan⟩ := rank_Lam_le (ℓ := ℓ) h13 (k + 1) hm k le_rfl
  rw [show 2 * k + 1 = 2 * (k + 1) - 1 by omega] at hspan
  have hmem := Nat.sInf_mem (s := {r | ∃ s : Finset (PowerSeries (Rm ℓ (k + 1))), s.card = r ∧
    Submodule.span (Rm ℓ (k + 1)) (s : Set (PowerSeries (Rm ℓ (k + 1)))) = Lam ℓ (k + 1) (2 * (k + 1) - 1)})
    ⟨_, s, rfl, hspan⟩
  obtain ⟨s', hs', hspan'⟩ := hmem
  by_contra hlt
  have h0 : s'.card = 0 := by
    have : rEll ℓ (k + 1) = 0 := by omega
    rw [hs']
    exact this
  rw [Finset.card_eq_zero] at h0
  rw [h0] at hspan'
  simp only [Finset.coe_empty, Submodule.span_empty] at hspan'
  have hg : gm ℓ (k + 1) k ∈ Lam ℓ (k + 1) (2 * (k + 1) - 1) := by
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, Lam_eq]
    exact Submodule.subset_span ⟨0, rfl⟩
  rw [← hspan'] at hg
  exact gm_ne_zero h13 (k + 1) hm k ((Submodule.mem_bot _).mp hg)

/-- **`r_ℓ(m) = 1` for `13 ≤ ℓ < 36`.** -/
theorem rEll_eq_one (h13 : 13 ≤ ℓ) (h36 : ℓ < 36) (m : ℕ) (hm : 1 ≤ m) : rEll ℓ m = 1 := by
  have h1 := rEll_le (ℓ := ℓ) h13 m hm
  have h2 := rEll_pos (ℓ := ℓ) h13 m hm
  have : (ℓ + 12) / 24 = 1 := by omega
  omega

end

end RamanujanTau.BLBound
