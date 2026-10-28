/-
# The invariant differential of a Weierstrass curve in characteristic `p` and the Hasse invariant

For a Weierstrass curve `W` over a ring of characteristic `p` (`p` an odd prime) the coefficient
`b_{p−1}` of `T^{p−1}` in `ω(T) = 1/Ψ(T)` (`ω(T)dT = dx/(2y + a₁x + a₃)`) equals the Hasse invariant
  `H(W) =` coefficient of `x^{p−1}` in `f(x)^{(p−1)/2}`, `f(x) = 4x³ + b₂x² + 2b₄x + b₆`
(`f(x) = (2y + a₁x + a₃)²`). We read `H(W)` in the homogenization `f̂(X,Y) = 4X³ + b₂X²Y + 2b₄XY² + b₆Y³`:
`H(W) = coeff_{X^{p−1} Y^{(p−1)/2}} f̂^{(p−1)/2}` (`hasseH`; `hasseH_eq_coeff_poly` in `Poly.lean` gives the
one-variable form).

Proof (a coefficient-level Cartier argument, no Laurent series): write `w = T³ v`, `V = v⁻¹`,
`D = −2 + a₁T + a₃w` (so `D = (2y + a₁x + a₃)·w`). Then
* `Ψ · (−2V + T V') = V D`                                       (from `Ψ_mul_eq`);
* `(D V)² = f̂(V, T²)`                                            (the curve equation);
* hence `Ψ · K = (V D)^p` with `K = (−2V + TV') · f̂^{(p−1)/2}(V, T²)`, so `ω · (VD)^p = K`;
* in characteristic `p`, `(VD)^p ≡ (−2)^p = −2 (mod T^p)`, so `−2 b_{p−1} = coeff_{p−1} K`;
* each monomial `V^a T^{2b}` (`a + b = 3(p−1)/2`) contributes `(−2V + TV') V^a T^{2b}`, which for
  `a ≠ p − 1` is `(a+1)⁻¹ (V^{a+1} T^{2b+1})'` (an exact form, as `2b + 1 ≡ −2(a+1)`), whose
  `T^{p−1}`-coefficient vanishes; for `a = p − 1` it contributes `−2`.
-/
import RamanujanTau.HasseInv.Omega
import RamanujanTau.EllipticFormal.Differential

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HasseInv
open MvPowerSeries EllipticFormal

variable {R : Type*} [CommRing R]

local notation "R1" => MvPowerSeries Unit R
local notation "T" => (X () : MvPowerSeries Unit R)

/-- the homogenized `f(x) = 4x³ + b₂x² + 2b₄x + b₆`: `f̂(X,Y) = 4X³ + b₂X²Y + 2b₄XY² + b₆Y³`. -/
noncomputable def fhat (W : WeierstrassCurve R) : MvPolynomial (Fin 2) R :=
  MvPolynomial.C 4 * MvPolynomial.X 0 ^ 3 + MvPolynomial.C W.b₂ * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 +
    MvPolynomial.C (2 * W.b₄) * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 +
    MvPolynomial.C W.b₆ * MvPolynomial.X 1 ^ 3

/-- **the Hasse invariant** `H(W)`: the coefficient of `x^{p−1}` in `f(x)^{(p−1)/2}`, read as the
coefficient of `X^{p−1} Y^{(p−1)/2}` in `f̂(X,Y)^{(p−1)/2}`. -/
noncomputable def hasseH (p : ℕ) (W : WeierstrassCurve R) : R :=
  MvPolynomial.coeff (Finsupp.single 0 (p - 1) + Finsupp.single 1 ((p - 1) / 2)) (fhat W ^ ((p - 1) / 2))

lemma isHom_cast {φ : MvPolynomial (Fin 2) R} {a b : ℕ} (h : a = b) (hφ : φ.IsHomogeneous a) :
    φ.IsHomogeneous b := h ▸ hφ

lemma fhat_isHomogeneous (W : WeierstrassCurve R) : (fhat W).IsHomogeneous 3 := by
  have X0 := MvPolynomial.isHomogeneous_X R (0 : Fin 2)
  have X1 := MvPolynomial.isHomogeneous_X R (1 : Fin 2)
  unfold fhat
  refine (((?_ : MvPolynomial.IsHomogeneous _ 3).add ?_).add ?_).add ?_
  · exact isHom_cast (by norm_num) ((X0.pow 3).C_mul 4)
  · exact isHom_cast (by norm_num) (((X0.pow 2).C_mul _).mul X1)
  · exact isHom_cast (by norm_num) ((X0.C_mul _).mul (X1.pow 2))
  · exact isHom_cast (by norm_num) ((X1.pow 3).C_mul _)

/-- cancellation of `T^n` in `R⟦T⟧`. -/
lemma Xpow_mul_cancel {n : ℕ} {f : PowerSeries R} (h : PowerSeries.X ^ n * f = 0) : f = 0 := by
  ext d
  have := congrArg (PowerSeries.coeff (d + n)) h
  rwa [PowerSeries.coeff_X_pow_mul, map_zero] at this

lemma pd_one' : pd () (1 : R1) = 0 := by
  rw [← map_one (MvPowerSeries.C (σ := Unit) (R := R)), pd_C]

lemma pd_pow_succ (f : R1) (n : ℕ) : pd () (f ^ (n + 1)) = ((n : R1) + 1) * f ^ n * pd () f := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pd_mul, ih]; push_cast; ring

lemma natCast_R1 (k : ℕ) : ((k : R1) : PowerSeries R) = PowerSeries.C (k : R) := (map_natCast _ k).symm

section CharP
variable (p : ℕ) [hp : Fact p.Prime] [CharP R p]

/-- in characteristic `p`, multiplication by `k` with `p ∤ k` is injective. -/
lemma natCast_mul_eq_zero {k : ℕ} (hk : ¬ p ∣ k) {x : R} (h : (k : R) * x = 0) : x = 0 := by
  have hk' : (k : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hu : IsUnit ((ZMod.castHom (dvd_refl p) R) (k : ZMod p)) := (isUnit_iff_ne_zero.mpr hk').map _
  rw [map_natCast] at hu
  exact hu.mul_right_eq_zero.mp h

lemma p_R1 : (p : R1) = 0 := by
  rw [← map_natCast (MvPowerSeries.C (σ := Unit) (R := R)), CharP.cast_eq_zero, map_zero]

lemma odd_p (hp2 : p ≠ 2) : p = 2 * ((p - 1) / 2) + 1 := by
  rcases hp.out.eq_two_or_odd with h | h
  · exact absurd h hp2
  · omega

/-- **one monomial**: for `a + b = 3(p−1)/2`, the `T^{p−1}`-coefficient of `(−2V + TV') V^a T^{2b}` is `−2`
if `a = p − 1` and `0` otherwise. -/
lemma term_coeff (hp2 : p ≠ 2) (V : R1) (hV : constantCoeff V = 1) (a b : ℕ)
    (hab : a + b = 3 * ((p - 1) / 2)) :
    PowerSeries.coeff (p - 1) ((-2 * V + T * pd () V) * V ^ a * (T ^ 2) ^ b : R1) =
      if a = p - 1 then -2 else 0 := by
  have hpm := odd_p p hp2
  set m := (p - 1) / 2 with hm
  split_ifs with ha
  · have hb : b = m := by omega
    have e : ((-2 * V + T * pd () V) * V ^ a * (T ^ 2) ^ b : R1) =
        T ^ (p - 1) * ((-2 * V + T * pd () V) * V ^ a) := by
      rw [hb, ← pow_mul, show 2 * m = p - 1 by omega]; ring
    rw [e]
    have := PowerSeries.coeff_X_pow_mul ((-2 * V + T * pd () V) * V ^ a : R1) (p - 1) 0
    rw [zero_add] at this
    erw [this]; rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    show constantCoeff ((-2 * V + T * pd () V) * V ^ a : R1) = -2
    simp [hV, map_ofNat]
  · -- the exact form `(V^{a+1} T^{2b+1})'`
    set g : R1 := (-2 * V + T * pd () V) * V ^ a * (T ^ 2) ^ b
    have hcast : 2 * (b : R1) + 1 + 2 * ((a : R1) + 1) = 0 := by
      have : ((2 * a + 2 * b + 3 : ℕ) : R1) = 0 := by
        rw [show 2 * a + 2 * b + 3 = 3 * p by omega]; push_cast; rw [p_R1]; ring
      push_cast at this; linear_combination this
    have hQ : pd () (V ^ (a + 1) * T ^ (2 * b + 1)) = ((a : R1) + 1) * g := by
      rw [pd_mul, pd_pow_succ, pd_pow_succ, FGL.pd_X', if_pos rfl]
      simp only [g]
      push_cast
      linear_combination (V ^ (a + 1) * T ^ (2 * b)) * hcast
    have h0 : PowerSeries.coeff (p - 1) (pd () (V ^ (a + 1) * T ^ (2 * b + 1)) : PowerSeries R) = 0 := by
      rw [coeff_pd']
      have : ((p - 1 : ℕ) : R) + 1 = 0 := by
        rw [show ((p - 1 : ℕ) : R) + 1 = ((p - 1 + 1 : ℕ) : R) by push_cast; ring,
          Nat.sub_add_cancel hp.out.one_lt.le, CharP.cast_eq_zero]
      rw [this, mul_zero]
    rw [hQ, show ((a : R1) + 1 : PowerSeries R) = PowerSeries.C ((a + 1 : ℕ) : R) by
      rw [← natCast_R1]; push_cast; rfl, PowerSeries.coeff_C_mul] at h0
    refine natCast_mul_eq_zero p (k := a + 1) ?_ h0
    intro hd
    have h1 : 0 < a + 1 := by omega
    obtain ⟨c, hc⟩ := hd
    rcases c with _ | _ | c
    · omega
    · exact ha (by omega)
    · nlinarith

/-- **the invariant differential and the Hasse invariant**: in characteristic `p` (odd), the coefficient
of `T^{p−1}` in `ω(T) = 1/Ψ(T)` is the Hasse invariant `H(W)`. -/
theorem coeff_omega_eq_hasseH (hp2 : p ≠ 2) (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (Finsupp.single () (p - 1)) (omega (formalGroup W)) = hasseH p W := by
  have hpm := odd_p p hp2
  set m := (p - 1) / 2 with hm
  haveI : CharP R1 p := charP_of_injective_algebraMap (fun a b h => by
    have := congrArg constantCoeff h; simpa using this) p
  set v : R1 := v W with hv_def
  have hw : (w W : R1) = T ^ 3 * v := w_eq_X3_mul_v W
  have hv0 : constantCoeff v = 1 := cc_v W
  set V : R1 := invOfUnit v 1 with hV_def
  have hvV : v * V = 1 := mul_invOfUnit v 1 (by rw [hv0]; rfl)
  have hV0 : constantCoeff V = 1 := by rw [hV_def, constantCoeff_invOfUnit]; simp
  set Ψ : R1 := FGL.Ψ (formalGroup W) (FGL.T : R1) with hΨ_def
  set D : R1 := -2 + C W.a₁ * T + C W.a₃ * (T ^ 3 * v) with hD
  -- `Ψ · (−2v − T v') = v D`
  have hΨ := Ψ_mul_eq W
  rw [hw, pd_mul, pd_pow_succ, FGL.pd_X', if_pos rfl] at hΨ
  rw [← hΨ_def] at hΨ
  have h1 : Ψ * (-2 * v - T * pd () v) = v * D := by
    have : Ψ * (-2 * v - T * pd () v) - v * D = 0 := by
      apply Xpow_mul_cancel (n := 3)
      show T ^ 3 * (Ψ * (-2 * v - T * pd () v) - v * D) = 0
      rw [hD]; push_cast at hΨ ⊢; linear_combination hΨ
    linear_combination this
  have hd : pd () v * V + v * pd () V = 0 := by
    have := congrArg (pd ()) hvV; rwa [pd_mul, pd_one'] at this
  have hΨV : Ψ * (-2 * V + T * pd () V) = V * D := by
    linear_combination V ^ 2 * h1 + (2 * Ψ * V - Ψ * T * pd () V + V * D) * hvV + Ψ * T * V * hd
  -- the curve equation: `(D V)² = f̂(V, T²)`
  have hG := G_T W
  rw [hw] at hG
  have hc : D ^ 2 * v = 4 + C W.b₂ * T ^ 2 * v + 2 * C W.b₄ * T ^ 4 * v ^ 2 + C W.b₆ * T ^ 6 * v ^ 3 := by
    have : D ^ 2 * v - (4 + C W.b₂ * T ^ 2 * v + 2 * C W.b₄ * T ^ 4 * v ^ 2 + C W.b₆ * T ^ 6 * v ^ 3) = 0 := by
      apply Xpow_mul_cancel (n := 3)
      show T ^ 3 * _ = 0
      rw [hD]
      simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, map_add, map_mul, map_pow,
        map_ofNat]
      linear_combination (-4) * hG
    linear_combination this
  have hsq : (D * V) ^ 2 = 4 * V ^ 3 + C W.b₂ * T ^ 2 * V ^ 2 + 2 * C W.b₄ * T ^ 4 * V +
      C W.b₆ * T ^ 6 := by
    linear_combination V ^ 3 * hc + (-D ^ 2 * V ^ 2 + C W.b₂ * T ^ 2 * V ^ 2 +
      2 * C W.b₄ * T ^ 4 * V * (v * V + 1) + C W.b₆ * T ^ 6 * (v ^ 2 * V ^ 2 + v * V + 1)) * hvV
  have hev : MvPolynomial.aeval (![V, T ^ 2] : Fin 2 → R1) (fhat W) = (D * V) ^ 2 := by
    rw [hsq]
    simp [fhat, map_mul, map_ofNat]
    simp only [show ∀ r : R, (PowerSeries.C r : PowerSeries R) = (C r : R1) from fun _ => rfl]
    ring
  -- `Ψ K = (V D)^p` and `ω (V D)^p = K`
  set K : R1 := (-2 * V + T * pd () V) * MvPolynomial.aeval (![V, T ^ 2] : Fin 2 → R1) (fhat W ^ m)
    with hK_def
  have hK : Ψ * K = (V * D) ^ p := by
    rw [hK_def, map_pow, hev, ← pow_mul]
    conv_rhs => rw [hpm]
    linear_combination (D * V) ^ (2 * m) * hΨV
  set ω : R1 := omega (formalGroup W) with hω_def
  have hΨω : Ψ * ω = 1 := Ψ_mul_omega _
  have hωK : ω * (V * D) ^ p = K := by linear_combination (-ω) * hK + K * hΨω
  -- `(V D)^p ≡ (−2)^p mod T^p`
  have hVD0 : constantCoeff (V * D) = -2 := by rw [hD]; simp [hV0, map_ofNat]
  obtain ⟨E, hE⟩ : (PowerSeries.X : PowerSeries R) ∣ (V * D - C (-2) : R1) := by
    rw [PowerSeries.X_dvd_iff]
    show constantCoeff (V * D - C (-2) : R1) = 0
    rw [map_sub, hVD0]; simp
  have hpow : (V * D) ^ p = C ((-2 : R) ^ p) + T ^ p * E ^ p := by
    have : V * D = C (-2) + T * E := by
      rw [← sub_eq_iff_eq_add']; exact hE
    rw [this, add_pow_char, mul_pow, map_pow]
  have hcoef := congrArg (PowerSeries.coeff (p - 1)) hωK
  rw [hpow, mul_add, map_add] at hcoef
  have e2 : PowerSeries.coeff (p - 1) (ω * (T ^ p * E ^ p) : PowerSeries R) = 0 := by
    rw [show (ω * (T ^ p * E ^ p) : R1) = T ^ p * (ω * E ^ p) by ring]
    erw [PowerSeries.coeff_X_pow_mul']; rw [if_neg (by omega)]
  rw [e2, add_zero] at hcoef
  erw [PowerSeries.coeff_mul_C] at hcoef
  have hm2 : ((-2 : R)) ^ p = -2 := by
    have := ZMod.pow_card (-2 : ZMod p)
    have h := congrArg (ZMod.castHom (dvd_refl p) R) this
    rwa [map_pow, map_neg, map_ofNat] at h
  rw [hm2] at hcoef
  -- `coeff_{p−1} K = −2 H(W)`
  have hKc : PowerSeries.coeff (p - 1) K = -2 * hasseH p W := by
    rw [hK_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.mul_sum, map_sum]
    have hterm : ∀ d : Fin 2 →₀ ℕ, PowerSeries.coeff (p - 1)
        ((-2 * V + T * pd () V) * ((algebraMap R R1) ((fhat W ^ m).coeff d) *
          ∏ i, (![V, T ^ 2] : Fin 2 → R1) i ^ d i) : PowerSeries R) =
        (fhat W ^ m).coeff d * PowerSeries.coeff (p - 1)
          ((-2 * V + T * pd () V) * V ^ d 0 * (T ^ 2) ^ d 1 : R1) := by
      intro d
      rw [Fin.prod_univ_two, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [show ((-2 * V + T * pd () V) * (C ((fhat W ^ m).coeff d) * (V ^ d 0 * (T ^ 2) ^ d 1)) : R1) =
        PowerSeries.C ((fhat W ^ m).coeff d) * ((-2 * V + T * pd () V) * V ^ d 0 * (T ^ 2) ^ d 1) by
          rw [show (PowerSeries.C ((fhat W ^ m).coeff d) : PowerSeries R) =
            (C ((fhat W ^ m).coeff d) : R1) from rfl]; ring]
      rw [PowerSeries.coeff_C_mul]
    simp only [hterm]
    have hhom := (fhat_isHomogeneous W).pow m
    set d₀ : Fin 2 →₀ ℕ := Finsupp.single 0 (p - 1) + Finsupp.single 1 m with hd₀
    have hdeg : ∀ d : Fin 2 →₀ ℕ, d ∈ (fhat W ^ m).support → d 0 + d 1 = 3 * m := by
      intro d hdm
      have := hhom (MvPolynomial.mem_support_iff.mp hdm)
      rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at this
      simp at this
      omega
    rw [Finset.sum_eq_single d₀]
    · rw [term_coeff p hp2 V hV0 (d₀ 0) (d₀ 1) (by simp [hd₀]; omega), if_pos (by simp [hd₀])]
      rw [hasseH]; ring
    · intro d hdm hne
      rw [term_coeff p hp2 V hV0 (d 0) (d 1) (hdeg d hdm), if_neg, mul_zero]
      intro h0
      apply hne
      ext i; fin_cases i
      · simp [hd₀, h0]
      · have := hdeg d hdm; simp [hd₀]; omega
    · intro hn
      rw [MvPolynomial.notMem_support_iff.mp hn, zero_mul]
  rw [hKc] at hcoef
  have h2 : ((2 : ℕ) : R) * (PowerSeries.coeff (p - 1) ω - hasseH p W) = 0 := by
    push_cast; linear_combination -hcoef
  have hnd : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
  have := natCast_mul_eq_zero p hnd h2
  show PowerSeries.coeff (p - 1) ω = _
  linear_combination this

end CharP

end HasseInv
