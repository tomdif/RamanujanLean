/-
# The Tate point over `ℤ[a]⟦b⟧` (`a = u`, `b = q/u`) and its differential equations

`R2 = ℤ[a]⟦b⟧`. The monomial `u^e q^N` of `ℤ[u,u⁻¹]⟦q⟧` corresponds to `a^{N+e} b^N`. The
injective ring map `jHom : R2 → ℤ[u,u⁻¹]⟦q⟧` (`a ↦ u`, `b ↦ q/u`) carries
* `zB 0 ↦ x̌ = (u−1)² x` (`TateFormal.xA`) and `zB 1 ↦ q̌ = (u−1)³ θx` (`TateFormal.qA`),
so Tate's identity `EA_eq_zero` pulls back to `R2` (`EB_eq_zero`).

On `R2` the derivation `Θ = a∂_a − b∂_b` is `θ = u d/du` (at fixed `q`). With
`zB m = (u−1)^{m+2} θ^m x` (explicit series) one has `(a−1)·Θ(zB m) = (m+2)a·zB m + zB (m+1)`,
and differentiating the Weierstrass equation gives (with `v = a − 1`)
* `zB 2 = 6 z₀² + v² z₀ + 2 a₄ v⁴`                               (`zB2_eq`, `θ²x = 6x² + x + 2a₄`),
* `zB 4 = 120 z₀³ + 30 v² z₀² + (72a₄+1) v⁴ z₀ + (48a₆+2a₄) v⁶`  (`zB4_eq`).
-/
import RamanujanTau.TateFormal.Formal

set_option autoImplicit false

noncomputable section

namespace TateQuot

open PowerSeries

/-- `ℤ[a]`. -/
abbrev P := Polynomial ℤ
/-- `ℤ[a]⟦b⟧`. -/
abbrev R2 := PowerSeries P

local notation "LT" => LaurentPolynomial.T (R := ℤ)
local notation "aX" => (Polynomial.X : P)

/-- `jHom : ℤ[a]⟦b⟧ → ℤ[u,u⁻¹]⟦q⟧`, `a ↦ u`, `b ↦ q u⁻¹`. -/
def jHom : R2 →+* PowerSeries TateFormal.A :=
  (rescale (LT (-1))).comp (PowerSeries.map Polynomial.toLaurent)

lemma coeff_jHom (F : R2) (N : ℕ) :
    coeff N (jHom F) = LT (-(N : ℤ)) * Polynomial.toLaurent (coeff N F) := by
  simp [jHom, coeff_rescale, LaurentPolynomial.T_pow]

lemma jHom_C (c : P) : jHom (C c) = C (Polynomial.toLaurent c) := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_jHom, coeff_C, coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

lemma jHom_injective : Function.Injective jHom := by
  intro F G h
  refine PowerSeries.ext fun N => ?_
  have h1 := congrArg (coeff N) h
  rw [coeff_jHom, coeff_jHom] at h1
  have hu : IsUnit (LT (-(N : ℤ))) := LaurentPolynomial.isUnit_T _
  exact Polynomial.toLaurent_injective (hu.mul_left_cancel h1)

/-! ### The explicit series -/

/-- `Rm m N = Σ_{d ∣ N} d^{m+1} (a^{N+d} + (−1)^m a^{N−d} − 2[m=0] a^N)`. -/
def Rm (m N : ℕ) : P :=
  ∑ d ∈ N.divisors, ((d : P) ^ (m + 1)) *
    (aX ^ (N + d) + (-1) ^ m * aX ^ (N - d) - (if m = 0 then 2 else 0) * aX ^ N)

/-- `cpoly m = (u−1)^{m+2} θ^m (u/(1−u)²)` (Eulerian polynomials, up to sign), `m ≤ 4`. -/
def cpoly : ℕ → P
  | 0 => aX
  | 1 => -(aX * (1 + aX))
  | 2 => aX * (1 + 4 * aX + aX ^ 2)
  | 3 => -(aX * (1 + 11 * aX + 11 * aX ^ 2 + aX ^ 3))
  | _ => aX * (1 + 26 * aX + 66 * aX ^ 2 + 26 * aX ^ 3 + aX ^ 4)

/-- `zB m = (u−1)^{m+2} θ^m x` over `ℤ[a]⟦b⟧`. -/
def zB (m : ℕ) : R2 := C (cpoly m) + C ((aX - 1) ^ (m + 2)) * mk (Rm m)

/-- `a₄(q)` over `ℤ[a]⟦b⟧` (`qᴺ = aᴺ bᴺ`). -/
def a4B : R2 := rescale aX (PowerSeries.map (Int.castRingHom P) TateCurve.a4)
/-- `a₆(q)` over `ℤ[a]⟦b⟧`. -/
def a6B : R2 := rescale aX (PowerSeries.map (Int.castRingHom P) TateCurve.a6)

/-- The Weierstrass defect over `ℤ[a]⟦b⟧`. -/
def EB : R2 :=
  zB 1 ^ 2 - (4 * zB 0 ^ 3 + C ((aX - 1) ^ 2) * zB 0 ^ 2 + 4 * C ((aX - 1) ^ 4) * a4B * zB 0 +
    4 * C ((aX - 1) ^ 6) * a6B)

/-! ### Comparison with `ℤ[u,u⁻¹]⟦q⟧` -/

lemma T_mul_toLaurent_pow (N k : ℕ) :
    LT (-(N : ℤ)) * Polynomial.toLaurent (aX ^ k) = LT ((k : ℤ) - N) := by
  rw [Polynomial.toLaurent_X_pow, ← LaurentPolynomial.T_add]; congr 1; ring

lemma jHom_mk_Rm0 : jHom (mk (Rm 0)) = mk TateFormal.Pc := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_jHom, coeff_mk, coeff_mk, Rm, TateFormal.Pc, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdN : d ≤ N := Nat.divisor_le hd
  simp only [pow_zero, one_mul, if_true, map_mul, map_sub, map_add,
    map_ofNat, mul_sub, mul_add]
  rw [mul_left_comm, T_mul_toLaurent_pow, mul_left_comm, T_mul_toLaurent_pow, mul_left_comm,
    mul_left_comm (LT _), T_mul_toLaurent_pow]
  push_cast [hdN]
  ring_nf
  simp [LaurentPolynomial.T_zero]

lemma jHom_mk_Rm1 : jHom (mk (Rm 1)) = mk TateFormal.Qc := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_jHom, coeff_mk, coeff_mk, Rm, TateFormal.Qc, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdN : d ≤ N := Nat.divisor_le hd
  simp only [one_ne_zero, if_false, zero_mul, sub_zero, map_mul, map_add, map_pow, map_natCast,
    map_neg, map_one, Polynomial.toLaurent_X, LaurentPolynomial.T_pow, mul_add]
  rw [mul_left_comm, ← LaurentPolynomial.T_add, mul_left_comm (LT _), mul_left_comm (LT _),
    ← LaurentPolynomial.T_add]
  push_cast [hdN]
  ring_nf

lemma toLaurent_aX : Polynomial.toLaurent aX = TateFormal.U := by
  rw [Polynomial.toLaurent_X]; rfl

lemma jHom_zB0 : jHom (zB 0) = TateFormal.xA := by
  rw [zB, TateFormal.xA, map_add, map_mul, jHom_C, jHom_C, jHom_mk_Rm0]
  simp [cpoly, TateFormal.U]

lemma jHom_zB1 : jHom (zB 1) = TateFormal.qA := by
  rw [zB, TateFormal.qA, map_add, map_mul, jHom_C, jHom_C, jHom_mk_Rm1]
  simp [cpoly, TateFormal.U]

lemma jHom_resc (f : PowerSeries ℤ) :
    jHom (rescale aX (PowerSeries.map (Int.castRingHom P) f)) =
      PowerSeries.map (Int.castRingHom TateFormal.A) f := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_jHom, coeff_rescale, coeff_map, coeff_map, map_mul, map_pow, toLaurent_aX]
  simp only [TateFormal.U, LaurentPolynomial.T_pow, eq_intCast, map_intCast]
  rw [← mul_assoc, ← LaurentPolynomial.T_add]
  simp

lemma jHom_EB : jHom EB = TateFormal.EA := by
  simp only [EB, TateFormal.EA, map_sub, map_add, map_mul, map_pow, map_ofNat, jHom_C, jHom_zB0,
    jHom_zB1, a4B, a6B, jHom_resc, TateFormal.a4A, TateFormal.a6A, map_one, toLaurent_aX]

/-- **Tate's identity over `ℤ[a]⟦b⟧`.** -/
theorem EB_eq_zero : EB = 0 :=
  jHom_injective (by rw [jHom_EB, TateFormal.EA_eq_zero, map_zero])

end TateQuot
