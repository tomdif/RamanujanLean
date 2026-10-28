/-
# The Hasse invariant of an elliptic formal group

* `coeff_nmul_sub_omega_mem_W`: for **any** Weierstrass curve over **any** commutative ring, the coefficient
  `a` of `T^p` in `[p]_W(T)` is `≡ b_{p−1}` (coefficient of `T^{p−1}` in `ω = 1/Ψ`) mod `p`.
  Proof: the Honda–Hazewinkel congruence (`coeff_nmul_sub_omega_mem`) over the universal coefficient
  ring `ℤ[a₁,a₂,a₃,a₄,a₆]` (where `p` is a non-zero-divisor), then specialization.
* `aH_formalGroup_eq_hasseH`: in characteristic `p` (odd), `aH p (formalGroup W) = H(W)`, the Hasse
  invariant (coefficient of `x^{p−1}` in `(4x³ + b₂x² + 2b₄x + b₆)^{(p−1)/2}`).
* `coeff_nmul_sub_hasseH_mem`: in any ring, `a ≡ H(W) (mod p)` provided `R/p` makes sense
  (no hypothesis: stated in the ideal `(p)`).
-/
import RamanujanTau.HasseInv.Weierstrass

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace HasseInv
open MvPowerSeries EllipticFormal FGL

variable {R : Type*} [CommRing R]

local notation "R1" => MvPowerSeries Unit R

lemma map_Ψ_formalGroup {S : Type*} [CommRing S] (f : R →+* S) (W : WeierstrassCurve R) :
    MvPowerSeries.map f (Ψ (formalGroup W) (T : R1)) = Ψ (formalGroup (W.map f)) (T : MvPowerSeries Unit S) := by
  show MvPowerSeries.map f (E1 (F W)) = E1 (F (W.map f))
  rw [map_E1, map_F]

lemma map_omega_formalGroup {S : Type*} [CommRing S] (f : R →+* S) (W : WeierstrassCurve R) :
    MvPowerSeries.map f (omega (formalGroup W)) = omega (formalGroup (W.map f)) := by
  have h1 : Ψ (formalGroup (W.map f)) (T : MvPowerSeries Unit S) *
      MvPowerSeries.map f (omega (formalGroup W)) = 1 := by
    rw [← map_Ψ_formalGroup, ← map_mul, Ψ_mul_omega, map_one]
  have h2 := Ψ_mul_omega (formalGroup (W.map f))
  calc MvPowerSeries.map f (omega (formalGroup W))
      = MvPowerSeries.map f (omega (formalGroup W)) *
          (Ψ (formalGroup (W.map f)) (T : MvPowerSeries Unit S) * omega (formalGroup (W.map f))) := by
        rw [h2, mul_one]
    _ = omega (formalGroup (W.map f)) := by rw [← mul_assoc, mul_comm _ (Ψ _ _), h1, one_mul]

lemma nmul_formalGroup_map {S : Type*} [CommRing S] (f : R →+* S) (W : WeierstrassCurve R) (n : ℕ) :
    MvPowerSeries.map f (nmul (formalGroup W) n) = nmul (formalGroup (W.map f)) n := by
  rw [← nmul_map, formalGroup_map]

/-- **`a ≡ b_{p−1} (mod p)` for every Weierstrass curve over every commutative ring.** -/
theorem coeff_nmul_sub_omega_mem_W (p : ℕ) [hp : Fact p.Prime] (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (Finsupp.single () p) (nmul (formalGroup W) p) -
      MvPowerSeries.coeff (Finsupp.single () (p - 1)) (omega (formalGroup W)) ∈ Ideal.span {(p : R)} := by
  have htf : ∀ x : Ru, (p : Ru) * x = 0 → x = 0 := fun x hx =>
    (mul_eq_zero.mp hx).resolve_left (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have h := coeff_nmul_sub_omega_mem (formalGroup Wu) p htf
  rw [Ideal.mem_span_singleton] at h ⊢
  obtain ⟨c, hc⟩ := h
  refine ⟨spec W c, ?_⟩
  have := congrArg (spec W) hc
  rw [map_sub, map_mul, map_natCast, ← coeff_map, ← coeff_map, nmul_formalGroup_map,
    map_omega_formalGroup, Wu_map_spec] at this
  exact this

/-- **characteristic `p`**: the coefficient `a` of `T^p` in `[p]` is the coefficient of `T^{p−1}` in `ω`. -/
theorem aH_formalGroup_eq_coeff_omega (p : ℕ) [Fact p.Prime] [CharP R p] (W : WeierstrassCurve R) :
    aH p (formalGroup W) = MvPowerSeries.coeff (Finsupp.single () (p - 1)) (omega (formalGroup W)) := by
  have h := coeff_nmul_sub_omega_mem_W p W
  rw [CharP.cast_eq_zero, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot, sub_eq_zero] at h
  exact h

/-- **The Hasse invariant of the formal group of `W`** (characteristic `p ≠ 2`): the coefficient `a` of
`T^p` in `[p]_W(T)` equals `H(W)`, the coefficient of `x^{p−1}` in `(4x³ + b₂x² + 2b₄x + b₆)^{(p−1)/2}`. -/
theorem aH_formalGroup_eq_hasseH (p : ℕ) [Fact p.Prime] [CharP R p] (hp2 : p ≠ 2)
    (W : WeierstrassCurve R) : aH p (formalGroup W) = hasseH p W := by
  rw [aH_formalGroup_eq_coeff_omega, coeff_omega_eq_hasseH p hp2]

lemma map_fhat {S : Type*} [CommRing S] (f : R →+* S) (W : WeierstrassCurve R) :
    MvPolynomial.map f (fhat W) = fhat (W.map f) := by
  simp [fhat, map_ofNat]

lemma map_hasseH {S : Type*} [CommRing S] (f : R →+* S) (p : ℕ) (W : WeierstrassCurve R) :
    f (hasseH p W) = hasseH p (W.map f) := by
  rw [hasseH, hasseH, ← MvPolynomial.coeff_map, map_pow, map_fhat]

/-- **mixed characteristic**: over any commutative ring and for odd `p`, `a ≡ H(W) (mod p)`. -/
theorem coeff_nmul_sub_hasseH_mem (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (Finsupp.single () p) (nmul (formalGroup W) p) - hasseH p W ∈
      Ideal.span {(p : R)} := by
  set I := Ideal.span {(p : R)}
  set π := Ideal.Quotient.mk I
  by_cases hI : I = ⊤
  · rw [hI]; trivial
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hpS : ((p : R ⧸ I)) = 0 := by
    rw [← map_natCast π, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
  haveI : CharP (R ⧸ I) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr hpS
  have h := aH_formalGroup_eq_hasseH p hp2 (W.map π)
  rw [aH, ← nmul_formalGroup_map, coeff_map, ← map_hasseH, ← sub_eq_zero, ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem] at h
  exact h

end HasseInv
