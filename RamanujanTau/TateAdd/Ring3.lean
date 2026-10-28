/-
# Three Tate points over `R3 = ℚ[a,c]⟦b⟧` and their images in `T`

`R3 = ℚ[a][c]⟦b⟧` with `u = a`, `v = c`, `q = acb` (so `q/u = cb`, `q/v = ab`, `q/(uv) = b`).
The Tate point at `u`, `v`, `uv` is obtained from `ℤ[a]⟦b⟧` (`TateQuot.R2`, `a = u`, `b = q/u`) by
* `ιu3`: `a ↦ a`, `b ↦ cb`;  `ιv3`: `a ↦ c`, `b ↦ ab`;  `ιw3`: `a ↦ ac`, `b ↦ b`.

`Ψ : R3 → T = ℚ⟦a⟧⟦X⟧⟦b⟧`, `c ↦ 1 + X`, is injective, and on the images the derivation `D` of
`T` (`a∂_a − c∂_c`) acts as `Θ`, `−Θ`, `0` (`D_ιu`, `D_ιv`, `D_ιw`).
-/
import RamanujanTau.TateQuot.Deriv
import RamanujanTau.TateAdd.Deriv

set_option autoImplicit false

noncomputable section

namespace TateAdd

open PowerSeries TateQuot

/-- `ℚ[a][c]`. -/
abbrev P3 := Polynomial (Polynomial ℚ)
/-- `ℚ[a][c]⟦b⟧`. -/
abbrev R3 := PowerSeries P3

/-- `a`. -/
abbrev A3 : P3 := Polynomial.C Polynomial.X
/-- `c`. -/
abbrev C3 : P3 := Polynomial.X

/-- `ℤ[a] → ℚ[a][c]`, `a ↦ a`. -/
def ja : P →+* P3 := Polynomial.eval₂RingHom (Int.castRingHom P3) A3
/-- `a ↦ c`. -/
def jc : P →+* P3 := Polynomial.eval₂RingHom (Int.castRingHom P3) C3
/-- `a ↦ ac`. -/
def jac : P →+* P3 := Polynomial.eval₂RingHom (Int.castRingHom P3) (A3 * C3)

/-- the point `u`: `a ↦ a`, `b ↦ cb`. -/
def ιu3 : R2 →+* R3 := (rescale C3).comp (PowerSeries.map ja)
/-- the point `v`: `a ↦ c`, `b ↦ ab`. -/
def ιv3 : R2 →+* R3 := (rescale A3).comp (PowerSeries.map jc)
/-- the point `uv`: `a ↦ ac`, `b ↦ b`. -/
def ιw3 : R2 →+* R3 := PowerSeries.map jac

lemma coeff_ιu3 (F : R2) (N : ℕ) : coeff N (ιu3 F) = C3 ^ N * ja (coeff N F) := by
  simp [ιu3, coeff_rescale]
lemma coeff_ιv3 (F : R2) (N : ℕ) : coeff N (ιv3 F) = A3 ^ N * jc (coeff N F) := by
  simp [ιv3, coeff_rescale]
lemma coeff_ιw3 (F : R2) (N : ℕ) : coeff N (ιw3 F) = jac (coeff N F) := by
  simp [ιw3]

lemma eval₂_int {S : Type*} [CommRing S] (f : ℤ →+* S) (x : S) (n : ℤ) :
    Polynomial.eval₂ f x (n : Polynomial ℤ) = f n := by
  rw [← Polynomial.C_eq_intCast, Polynomial.eval₂_C, Int.cast_id]

/-- series in `q = ab` give the same element under all three maps. -/
lemma ι3_resc (f : PowerSeries ℤ) :
    ιu3 (rescale (Polynomial.X : P) (PowerSeries.map (Int.castRingHom P) f)) =
      ιw3 (rescale (Polynomial.X : P) (PowerSeries.map (Int.castRingHom P) f)) ∧
    ιv3 (rescale (Polynomial.X : P) (PowerSeries.map (Int.castRingHom P) f)) =
      ιw3 (rescale (Polynomial.X : P) (PowerSeries.map (Int.castRingHom P) f)) := by
  constructor <;> refine PowerSeries.ext fun N => ?_ <;>
    simp [coeff_ιu3, coeff_ιv3, coeff_ιw3, coeff_rescale, ja, jc, jac, eval₂_int] <;> ring

/-! ### The map to `T` -/

/-- `ℚ[a] → k2`, `a ↦ a`. -/
def ψ0 : Polynomial ℚ →+* k2 := (C (R := k1)).comp (Polynomial.coeToPowerSeries.ringHom (R := ℚ))
/-- `ψ : ℚ[a][c] → k2`, `c ↦ 1 + X`. -/
def ψ : P3 →+* k2 := Polynomial.eval₂RingHom ψ0 (1 + X)
/-- `Ψ : R3 → T`. -/
def Ψ : R3 →+* T := PowerSeries.map ψ

def ιu : R2 →+* T := Ψ.comp ιu3
def ιv : R2 →+* T := Ψ.comp ιv3
def ιw : R2 →+* T := Ψ.comp ιw3

/-- `ℤ`-polynomial evaluation in `k2`. -/
abbrev ev2 (x : k2) (p : P) : k2 := Polynomial.eval₂ (Int.castRingHom k2) x p

lemma ψ_int (n : ℤ) : ψ (n : P3) = (n : k2) := map_intCast ψ n

lemma ψ_ja (p : P) : ψ (ja p) = ev2 ca p := by
  simp only [ja, Polynomial.coe_eval₂RingHom, ev2]
  rw [Polynomial.hom_eval₂]
  congr 1
  · ext n; simp
  · simp [ψ, ψ0]
lemma ψ_jc (p : P) : ψ (jc p) = ev2 (1 + X) p := by
  simp only [jc, Polynomial.coe_eval₂RingHom, ev2]
  rw [Polynomial.hom_eval₂]
  congr 1
  · ext n; simp
  · simp [ψ, ψ0]
lemma ψ_jac (p : P) : ψ (jac p) = ev2 (ca * (1 + X)) p := by
  simp only [jac, Polynomial.coe_eval₂RingHom, ev2]
  rw [Polynomial.hom_eval₂]
  congr 1
  · ext n; simp
  · simp [ψ, ψ0]
lemma ψ_A3 : ψ A3 = ca := by simp [ψ, ψ0]
lemma ψ_C3 : ψ C3 = 1 + X := by simp [ψ]

lemma coeff_ιu (F : R2) (N : ℕ) : coeff N (ιu F) = (1 + X) ^ N * ev2 ca (coeff N F) := by
  simp [ιu, Ψ, coeff_ιu3, ψ_ja, ψ_C3]
lemma coeff_ιv (F : R2) (N : ℕ) : coeff N (ιv F) = ca ^ N * ev2 (1 + X) (coeff N F) := by
  simp [ιv, Ψ, coeff_ιv3, ψ_jc, ψ_A3]
lemma coeff_ιw (F : R2) (N : ℕ) : coeff N (ιw F) = ev2 (ca * (1 + X)) (coeff N F) := by
  simp [ιw, Ψ, coeff_ιw3, ψ_jac]

/-! ### `D` on the images -/

lemma IsDer.intCast {R : Type*} [CommRing R] {δ : R → R} (hδ : IsDer δ) (n : ℤ) :
    δ (n : R) = 0 := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simpa using hδ.natCast m
  · simpa [hδ.neg] using hδ.natCast m

lemma IsDer.ev2 {δ : k2 → k2} (hδ : IsDer δ) (x : k2) (p : P) :
    δ (ev2 x p) = ev2 x (Polynomial.derivative p) * δ x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [ev2, Polynomial.eval₂_add, map_add] at hp hq ⊢; rw [hδ.add, hp, hq]; ring
  | monomial n a =>
    simp only [ev2, Polynomial.eval₂_monomial, Polynomial.derivative_monomial, eq_intCast]
    rcases n with _ | n
    · simp [hδ.intCast]
    · rw [hδ.mul, hδ.intCast, hδ.pow]; push_cast; ring

lemma D'_pow_one_add_X (N : ℕ) : D' ((1 + X) ^ N) = -((N : k2) * (1 + X) ^ N) := by
  rcases N with _ | N
  · simp [isDer_D'.one]
  · rw [isDer_D'.pow, D'_one_add_X]; push_cast; ring

lemma D'_ca_pow (N : ℕ) : D' (ca ^ N) = (N : k2) * ca ^ N := by
  rcases N with _ | N
  · simp [isDer_D'.one]
  · rw [isDer_D'.pow, D'_ca]; push_cast; ring

lemma ev2_X_mul_deriv (x : k2) (p : P) :
    ev2 x ((Polynomial.X : P) * Polynomial.derivative p) = x * ev2 x (Polynomial.derivative p) := by
  simp [ev2]

/-- `D ∘ ιu = ιu ∘ Θ`. -/
theorem D_ιu (F : R2) : D (ιu F) = ιu (Θ F) := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_D, coeff_ιu, coeff_ιu, coeff_Θ, isDer_D'.mul, isDer_D'.ev2, D'_ca, D'_pow_one_add_X]
  simp only [ev2, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X,
    Polynomial.eval₂_natCast]
  ring

/-- `D ∘ ιv = −ιv ∘ Θ`. -/
theorem D_ιv (F : R2) : D (ιv F) = -ιv (Θ F) := by
  refine PowerSeries.ext fun N => ?_
  rw [map_neg, coeff_D, coeff_ιv, coeff_ιv, coeff_Θ, isDer_D'.mul, isDer_D'.ev2, D'_one_add_X,
    D'_ca_pow]
  simp only [ev2, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X,
    Polynomial.eval₂_natCast]
  ring

/-- `D ∘ ιw = 0`. -/
theorem D_ιw (F : R2) : D (ιw F) = 0 := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_D, coeff_ιw, isDer_D'.ev2, isDer_D'.mul, D'_ca, D'_one_add_X, map_zero]
  ring

/-! ### `X = 0` -/

lemma ev0_ιu_ιw (F : R2) : ev0 (ιu F) = ev0 (ιw F) := by
  refine PowerSeries.ext fun N => ?_
  rw [coeff_ev0, coeff_ev0, coeff_ιu, coeff_ιw, map_mul, map_pow]
  simp only [ev2, Polynomial.hom_eval₂]
  simp

/-! ### Injectivity of `Ψ` -/

lemma ψ_eq (p : P3) : ψ p = ((p.map (Polynomial.coeToPowerSeries.ringHom (R := ℚ))).comp
    (Polynomial.X + 1) : Polynomial k1) := by
  have : ψ = (Polynomial.coeToPowerSeries.ringHom (R := k1)).comp
      ((Polynomial.compRingHom (Polynomial.X + 1)).comp
        (Polynomial.mapRingHom (Polynomial.coeToPowerSeries.ringHom (R := ℚ)))) := by
    apply Polynomial.ringHom_ext
    · intro r; simp [ψ, ψ0]
    · simp [ψ, add_comm]
  rw [this]; rfl

lemma ψ_injective : Function.Injective ψ := by
  intro p q h
  rw [ψ_eq, ψ_eq] at h
  have h1 := Polynomial.coe_injective k1 h
  have h2 := congrArg (fun r : Polynomial k1 => r.comp (Polynomial.X - 1)) h1
  simp only [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp, Polynomial.one_comp,
    sub_add_cancel, Polynomial.comp_X] at h2
  exact Polynomial.map_injective _ (Polynomial.coe_injective ℚ) h2

lemma Ψ_injective : Function.Injective Ψ := by
  intro F G h
  refine PowerSeries.ext fun n => ψ_injective ?_
  have := congrArg (coeff n) h
  simpa [Ψ] using this

end TateAdd
