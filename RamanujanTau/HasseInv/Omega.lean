/-
# The coefficient `a` of `T^p` in `[p](T)` versus the invariant differential

For a commutative one-dimensional formal group `F` over `R` let `ω(T) = 1/Ψ(T)` (`ω(T) dT` is the
normalized invariant differential, `Ψ(T) = (∂₂F)(T,0)`), `ω(T) = Σ bₙ Tⁿ`.

* `pd_nmul_mul_omega`: `[n]'(T) · ω([n](T)) = n · ω(T)` (i.e. `[n]^* ω = n ω`), over any ring.
* `coeff_nmul_sub_omega_mem` (**Honda / Hazewinkel congruence**): if `p` is a non-zero-divisor in `R`,
  then `a − b_{p−1} ∈ (p)`, where `a` is the coefficient of `T^p` in `[p](T)`.

Proof: take the coefficient of `T^{p−1}` in `[p]'(T) · ω([p](T)) = p ω(T)`. Writing `u = [p](T)`, all
coefficients of `u` and of `u'` in degrees `≤ p − 1` are divisible by `p` (`FGL.p_dvd_coeff_nmul`), so
`coeff_{p−1}(u' uⁿ) ∈ (p^{n+1})`; the `n = 0` term is `p · a`. Hence `p a + (p²) ∋ p b_{p−1}`.
-/
import RamanujanTau.FormalGroupLayer.HeightTwo

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HasseInv
open MvPowerSeries FGL

variable {R : Type*} [CommRing R]

local notation "R1" => MvPowerSeries Unit R

section Omega
variable (F : FormalGroup R)

lemma cc_Ψ_T : constantCoeff (Ψ F (T : R1)) = 1 := by
  rw [Ψ, cc_subst _ (cc_vec2 cc_T (by simp)), ← coeff_zero_eq_constantCoeff_apply, coeff_pd, zero_add]
  simp [F.lin_coeff_Y]

/-- the invariant differential `ω(T) = 1/Ψ(T)` (so `ω(T) dT` is the normalized invariant differential). -/
noncomputable def omega : R1 := invOfUnit (Ψ F (T : R1)) 1

lemma Ψ_mul_omega : Ψ F (T : R1) * omega F = 1 :=
  mul_invOfUnit _ _ (by rw [cc_Ψ_T]; rfl)

lemma cc_omega : constantCoeff (omega F) = 1 := by
  rw [omega, constantCoeff_invOfUnit]; simp

/-- `Ψ(u)` is `Ψ(T)` evaluated at `T = u`. -/
lemma Ψ_subst {u : R1} (hu : constantCoeff u = 0) :
    Ψ F u = subst (fun _ : Unit => u) (Ψ F (T : R1)) := by
  rw [Ψ, Ψ, ss _ _ (cc_vec2 cc_T (by simp)) (h1 hu)]
  congr 1; funext s; fin_cases s
  · exact (sX _ (h1 hu) ()).symm
  · exact (s0 _ (h1 hu)).symm

lemma subst_one' (u : R1) : subst (fun _ : Unit => u) (1 : R1) = 1 := by
  have := subst_C (a := fun _ : Unit => u) (1 : R)
  simpa using this

/-- **`[n]^* ω = n ω`**: `[n]'(T) · ω([n](T)) = n · ω(T)`. -/
theorem pd_nmul_mul_omega [F.IsComm] (n : ℕ) :
    pd () (nmul F n) * subst (fun _ : Unit => nmul F n) (omega F) = (n : R1) * omega F := by
  have hu := cc_nmul F n
  have hinv : Ψ F (nmul F n) * subst (fun _ : Unit => nmul F n) (omega F) = 1 := by
    rw [Ψ_subst F hu, ← subst_mul (hs (h1 hu)), Ψ_mul_omega, subst_one' _]
  have hI := nmul_invariant F n
  have hΨω := Ψ_mul_omega F
  linear_combination (omega F * subst (fun _ : Unit => nmul F n) (omega F)) * hI -
    (pd () (nmul F n) * subst (fun _ : Unit => nmul F n) (omega F)) * hΨω +
    ((n : R1) * omega F) * hinv

end Omega

/-! ## Coefficients in an ideal up to a given degree -/

section Low

/-- all coefficients of `f` in degrees `≤ N` lie in `I`. -/
def LowIn (I : Ideal R) (N : ℕ) (f : PowerSeries R) : Prop :=
  ∀ k ≤ N, PowerSeries.coeff k f ∈ I

lemma lowIn_mul {I J : Ideal R} {N : ℕ} {f g : PowerSeries R} (hf : LowIn I N f) (hg : LowIn J N g) :
    LowIn (I * J) N (f * g) := by
  intro k hk
  rw [PowerSeries.coeff_mul]
  refine Ideal.sum_mem _ fun x hx => Ideal.mul_mem_mul (hf _ ?_) (hg _ ?_)
  · have := Finset.antidiagonal.fst_le hx; omega
  · have := Finset.antidiagonal.snd_le hx; omega

lemma lowIn_pow {I : Ideal R} {N : ℕ} {f : PowerSeries R} (hf : LowIn I N f) (n : ℕ) :
    LowIn (I ^ n) N (f ^ n) := by
  induction n with
  | zero => intro k _; simp
  | succ n ih => rw [pow_succ, pow_succ]; exact lowIn_mul ih hf

end Low

lemma coeff_pd' (f : R1) (k : ℕ) :
    PowerSeries.coeff k (pd () f) = PowerSeries.coeff (k + 1) f * ((k : R) + 1) := by
  show MvPowerSeries.coeff (Finsupp.single () k) _ = MvPowerSeries.coeff (Finsupp.single () (k + 1)) f * _
  rw [coeff_pd, ← Finsupp.single_add, Finsupp.single_eq_same]

/-- `f = Σ_{n < N} fₙ Tⁿ + T^N ρ`. -/
lemma exists_split (f : PowerSeries R) (N : ℕ) :
    ∃ ρ : PowerSeries R, f = ∑ n ∈ Finset.range N, PowerSeries.C (PowerSeries.coeff n f) *
      PowerSeries.X ^ n + PowerSeries.X ^ N * ρ := by
  have : (PowerSeries.X : PowerSeries R) ^ N ∣
      f - ∑ n ∈ Finset.range N, PowerSeries.C (PowerSeries.coeff n f) * PowerSeries.X ^ n := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [map_sub, map_sum, PowerSeries.coeff_X_pow, Finset.mem_range, hm]
  obtain ⟨ρ, hρ⟩ := this
  exact ⟨ρ, by rw [← hρ]; ring⟩

/-! ## The congruence -/

section Main
variable (F : FormalGroup R) (p : ℕ) [hp : Fact p.Prime] [F.IsComm]

lemma lowIn_nmul : LowIn (Ideal.span {(p : R)}) (p - 1) (nmul F p) := by
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · show MvPowerSeries.coeff (Finsupp.single () 0) (nmul F p) ∈ _
    rw [Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply, cc_nmul]; exact Ideal.zero_mem _
  · have hnd : ¬ p ∣ k := fun h => by
      have := Nat.le_of_dvd hk0 h; have := hp.out.one_lt; omega
    exact Ideal.mem_span_singleton.mpr (p_dvd_coeff_nmul F p k hnd)

lemma lowIn_pd_nmul : LowIn (Ideal.span {(p : R)}) (p - 1) (pd () (nmul F p)) := by
  intro k hk
  rw [coeff_pd']
  have h1p := hp.out.one_lt
  rcases Nat.lt_or_ge (k + 1) p with hlt | hge
  · exact Ideal.mul_mem_right _ _ (lowIn_nmul F p (k + 1) (by omega))
  · have : (k : R) + 1 = (p : R) := by rw [show p = k + 1 by omega]; push_cast; ring
    rw [this]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

/-- **Honda–Hazewinkel congruence.** If `p` is a non-zero-divisor of `R`, the coefficient `a` of `T^p` in
`[p](T)` is congruent mod `p` to the coefficient `b_{p−1}` of `T^{p−1}` in `ω(T) = 1/Ψ(T)`. -/
theorem coeff_nmul_sub_omega_mem (htf : ∀ x : R, (p : R) * x = 0 → x = 0) :
    MvPowerSeries.coeff (Finsupp.single () p) (nmul F p) -
      MvPowerSeries.coeff (Finsupp.single () (p - 1)) (omega F) ∈ Ideal.span {(p : R)} := by
  set I : Ideal R := Ideal.span {(p : R)} with hI
  set u : PowerSeries R := nmul F p with hu_def
  set ω : PowerSeries R := omega F with hω_def
  have hu0 : constantCoeff (u : R1) = 0 := cc_nmul F p
  have h1p := hp.out.one_lt
  have hkey := pd_nmul_mul_omega F p
  rw [← hu_def, ← hω_def] at hkey
  obtain ⟨ρ, hρ⟩ := exists_split ω p
  -- `ω(u) = Σ_{n<p} bₙ uⁿ + u^p ρ(u)`
  have hsub : subst (fun _ : Unit => (u : R1)) (ω : R1) =
      ∑ n ∈ Finset.range p, PowerSeries.C (PowerSeries.coeff n ω) * u ^ n +
        u ^ p * subst (fun _ : Unit => (u : R1)) (ρ : R1) := by
    conv_lhs => rw [hρ]
    rw [← coe_substAlgHom (hs (h1 hu0))]
    simp only [map_add, map_sum, map_mul, map_pow]
    have hX : substAlgHom (hs (h1 hu0)) (PowerSeries.X : PowerSeries R) = u :=
      substAlgHom_X (hs (h1 hu0)) ()
    have hC : ∀ r : R, substAlgHom (hs (h1 hu0)) (PowerSeries.C r : PowerSeries R) =
        PowerSeries.C r := fun r => by
      rw [coe_substAlgHom]; exact subst_C r
    simp only [hX, hC]
  have hXu : (PowerSeries.X : PowerSeries R) ∣ u := PowerSeries.X_dvd_iff.mpr hu0
  obtain ⟨u₁, hu₁⟩ := hXu
  -- coefficient `p − 1`
  have hc := congrArg (PowerSeries.coeff (p - 1)) hkey
  rw [hsub, mul_add, map_add, Finset.mul_sum, map_sum] at hc
  have htail : PowerSeries.coeff (p - 1)
      (pd () (u : R1) * (u ^ p * subst (fun _ : Unit => (u : R1)) (ρ : R1)) : PowerSeries R) = 0 := by
    have : (pd () (u : R1) * (u ^ p * subst (fun _ : Unit => (u : R1)) (ρ : R1)) : PowerSeries R) =
        PowerSeries.X ^ p * (pd () (u : R1) * u₁ ^ p * subst (fun _ : Unit => (u : R1)) (ρ : R1)) := by
      rw [hu₁]; ring
    rw [this, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  rw [htail, add_zero] at hc
  have hR : PowerSeries.coeff (p - 1) ((p : R1) * (ω : R1) : PowerSeries R) =
      (p : R) * PowerSeries.coeff (p - 1) ω := by
    rw [show ((p : R1) : PowerSeries R) = PowerSeries.C (p : R) from (map_natCast _ p).symm,
      PowerSeries.coeff_C_mul]
  rw [hR] at hc
  have hterm : ∀ n, PowerSeries.coeff (p - 1)
      (pd () (u : R1) * (PowerSeries.C (PowerSeries.coeff n ω) * u ^ n) : PowerSeries R) =
      PowerSeries.coeff n ω * PowerSeries.coeff (p - 1) (pd () (u : R1) * u ^ n : PowerSeries R) := by
    intro n
    rw [mul_left_comm, PowerSeries.coeff_C_mul]
  simp only [hterm] at hc
  rw [show p = (p - 1) + 1 by omega, Finset.sum_range_succ'] at hc
  rw [show p - 1 + 1 - 1 = p - 1 by omega] at hc
  -- the `n = 0` term
  have h0 : PowerSeries.coeff 0 ω * PowerSeries.coeff (p - 1) (pd () (u : R1) * u ^ 0 : PowerSeries R) =
      PowerSeries.coeff p u * (p : R) := by
    have hω0 : PowerSeries.coeff 0 ω = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact cc_omega F
    rw [hω0, one_mul, pow_zero, mul_one, coeff_pd', show p - 1 + 1 = p by omega]
    congr 1
    rw [show ((p - 1 : ℕ) : R) + 1 = ((p - 1 + 1 : ℕ) : R) by push_cast; ring, show p - 1 + 1 = p by omega]
  rw [h0] at hc
  -- the other terms lie in `(p²)`
  have hS : ∑ n ∈ Finset.range (p - 1), PowerSeries.coeff (n + 1) ω *
      PowerSeries.coeff (p - 1) (pd () (u : R1) * u ^ (n + 1) : PowerSeries R) ∈ I ^ 2 := by
    refine Ideal.sum_mem _ fun n _ => Ideal.mul_mem_left _ _ ?_
    have hl := lowIn_mul (lowIn_pd_nmul F p) (lowIn_pow (lowIn_nmul F p) (n + 1))
    have hmem := hl (p - 1) le_rfl
    rw [← pow_succ'] at hmem
    exact Ideal.pow_le_pow_right (by omega) hmem
  rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hS
  obtain ⟨r, hr⟩ := hS
  rw [hr] at hc
  have hp1 : ((p - 1 + 1 : ℕ) : R) = p := by rw [Nat.sub_add_cancel hp.out.one_lt.le]
  rw [hp1] at hc
  have hz : (p : R) * (PowerSeries.coeff p u - PowerSeries.coeff (p - 1) ω + p * r) = 0 := by
    linear_combination hc
  have := htf _ hz
  rw [Ideal.mem_span_singleton]
  exact ⟨-r, by
    show PowerSeries.coeff p u - PowerSeries.coeff (p - 1) ω = _
    linear_combination this⟩

/-- **characteristic `p`**: `a = b_{p−1}`, if `F` is the reduction of a formal group over a ring in which
`p` is a non-zero-divisor. -/
theorem aH_eq_of_lift {S : Type*} [CommRing S] [CharP S p] (f : R →+* S) [(F.map f).IsComm]
    (htf : ∀ x : R, (p : R) * x = 0 → x = 0) :
    aH p (F.map f) = MvPowerSeries.coeff (Finsupp.single () (p - 1)) (MvPowerSeries.map f (omega F)) := by
  have h := coeff_nmul_sub_omega_mem F p htf
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have := congrArg f hc
  rw [map_sub, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, sub_eq_zero] at this
  rw [aH, nmul_map, coeff_map, this, coeff_map]

end Main

end HasseInv
