import RamanujanTau.UBSharp.Basic
import RamanujanTau.ConjAlg.Main

/-!
# `QuotBound` implies `SharpHQ.HConj`

The `Δ`-conjugates are `y_C = Δ(V C)` (Vélu normalization), so the `Δ`-bounds of `QuotBound` are
exactly the valuation part of `SharpHQ.ConjBound`;
* the Hecke clause of `QuotBound` for `P = Δ^m` gives the power sums `Σ_C y_C^m = ℓ·(T_ℓΔ^m)(W)`, and
  Newton's identities, as polynomials over `ℤ_ℓ` (`newton_polyZ`, from the q-expansions
  `J(f_k) = e_k(ys)`), give `f_k(W) = e_k(y)`.

So a single geometric hypothesis `QuotBound` discharges both `UB` (`UBSharp.UB_of_quot`) and
`HConj` (**`HConj_of_quotBound`**).

(`newton_polyQ` and `eq_esymm_of_newton` are copies of `ConjAlg.newton_poly` /
`ConjAlg.eq_esymm_of_newton`, kept local so that this directory does not depend on work in progress.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UBSharp
open MvPolynomial ModP VLayer HeckeQExp AtkinOBrienFinal AtkinOBrien DBound KatzForms Igusa

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)

/-! ### `T_ℓ` over `ℤ_ℓ`, with the polynomial identity -/

include hℓ in
/-- `T_ℓ` on classical forms over `ℤ_ℓ`, together with `map ιz PT = heckePoly (map ιz P)`. -/
theorem exists_hecke_Zp' {k : ℕ} (hk : 1 ≤ k) {P : Poly ℓ} (hP : Iso P k) :
    ∃ P' : Poly ℓ, Iso P' k ∧ MvPolynomial.map (ιz ℓ) P' = heckePoly ℓ (MvPolynomial.map (ιz ℓ) P) ∧
      ev ℤ_[ℓ] P' = Tq ℓ ((ℓ : ℤ_[ℓ]) ^ (k - 1)) (ev ℤ_[ℓ] P) := by
  set Pq := MvPolynomial.map (ιz ℓ) P
  have hPq : Iso Pq k := iso_map _ hP
  have hev := ev_heckePoly ℓ hPq
  have hc : algebraMap ℚ ℚ_[ℓ] (mulQ ℓ k) = ιz ℓ ((ℓ : ℤ_[ℓ]) ^ (k - 1)) := by
    rw [mulQ_of_pos ℓ hk]; simp
  obtain ⟨P', hP', hP'e⟩ := descend (ιz ℓ) Subtype.val_injective (isUnit_1728_Zp hℓ) k
    (heckePoly ℓ Pq) (iso_heckePoly ℓ hPq)
    ⟨Tq ℓ ((ℓ : ℤ_[ℓ]) ^ (k - 1)) (ev ℤ_[ℓ] P), by rw [map_Tq, hev, hc, map_ev]⟩
  refine ⟨P', hP', hP'e, PowerSeries.map_injective (ιz ℓ) Subtype.val_injective ?_⟩
  rw [map_ev, hP'e, hev, hc, map_Tq, map_ev]

/-! ### Newton's identities (copies of `ConjAlg`) -/

/-- If `F` satisfies Newton's recursion with the power sums of `y` (and `F 0 = 1`), then
`F k = e_k(y)`. -/
theorem eq_esymm_of_newton {K σ : Type*} [Field K] [CharZero K] [Fintype σ] (y : σ → K)
    (F p : ℕ → K) (hp : ∀ m, 1 ≤ m → ∑ i, y i ^ m = p m) (h0 : F 0 = 1)
    (hN : ∀ k : ℕ, (k : K) * F k = (-1) ^ (k + 1) *
      ∑ a ∈ Finset.antidiagonal k with a.1 < k, (-1) ^ a.1 * F a.1 * p a.2) :
    ∀ k, F k = eval y (esymm σ K k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [h0, esymm_zero, map_one]
  have hE := congrArg (eval y) (mul_esymm_eq_sum σ K k)
  simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast] at hE
  have hS : ∑ a ∈ Finset.antidiagonal k with a.1 < k, (-1) ^ a.1 * F a.1 * p a.2 =
      ∑ a ∈ Finset.antidiagonal k with a.1 < k,
        (-1) ^ a.1 * eval y (esymm σ K a.1) * eval y (psum σ K a.2) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    have hsum : a.1 + a.2 = k := Finset.mem_antidiagonal.mp ha1
    rw [ih a.1 ha2, ← hp a.2 (by omega)]
    simp [psum]
  have hk0 : (k : K) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  apply mul_left_cancel₀ hk0
  rw [hN, hS, hE]

lemma iso_map_f {f : ℕ → Poly ℓ} (hf : ∀ k, Iso (f k) (k * 12)) (k : ℕ) :
    Iso (MvPolynomial.map (ιz ℓ) (f k)) (k * 12) := iso_map _ (hf k)

lemma J_ev_map {f : ℕ → Poly ℓ} {ζ : PadicAlgCl ℓ}
    (hJ : ∀ k, J ℓ (PowerSeries.map (ιz ℓ) (ev ℤ_[ℓ] (f k))) =
      MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k)) (k : ℕ) :
    J ℓ (ev ℚ_[ℓ] (MvPolynomial.map (ιz ℓ) (f k))) =
      MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k) := by
  rw [← map_ev, hJ]

/-- `f_0 = 1`. -/
theorem f_zero {f : ℕ → Poly ℓ} (hf : ∀ k, Iso (f k) (k * 12)) {ζ : PadicAlgCl ℓ}
    (hJ : ∀ k, J ℓ (PowerSeries.map (ιz ℓ) (ev ℤ_[ℓ] (f k))) =
      MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k)) :
    MvPolynomial.map (ιz ℓ) (f 0) = 1 := by
  have h1 : Iso (1 : MvPolynomial (Fin 2) ℚ_[ℓ]) (0 * 12) := by
    simpa using (MvPolynomial.isWeightedHomogeneous_one ℚ_[ℓ] wt)
  refine ev_injOn_iso (isUnit_1728 (R := ℚ_[ℓ])) (iso_map_f hf 0) h1 (J_injective ℓ ?_)
  rw [J_ev_map hℓ hJ, map_one, map_one, MvPolynomial.esymm_zero, map_one]

/-- Newton's identities for the `f_k` over `ℚ_ℓ`. -/
theorem newton_polyQ {f : ℕ → Poly ℓ} (hf : ∀ k, Iso (f k) (k * 12)) {ζ : PadicAlgCl ℓ}
    (hζ : IsPrimitiveRoot ζ ℓ)
    (hJ : ∀ k, J ℓ (PowerSeries.map (ιz ℓ) (ev ℤ_[ℓ] (f k))) =
      MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ) (MvPolynomial.esymm (Option (Fin ℓ)) ℤ k)) (k : ℕ) :
    C (k : ℚ_[ℓ]) * MvPolynomial.map (ιz ℓ) (f k) =
      C ((-1 : ℚ_[ℓ]) ^ (k + 1)) * ∑ a ∈ Finset.antidiagonal k with a.1 < k,
        C ((-1 : ℚ_[ℓ]) ^ a.1) * MvPolynomial.map (ιz ℓ) (f a.1) * sigP (Pdisc hℓ) a.2 := by
  classical
  have hL : Iso (C (k : ℚ_[ℓ]) * MvPolynomial.map (ιz ℓ) (f k)) (k * 12) :=
    (iso_map_f hf k).C_mul _
  have hR : Iso (C ((-1 : ℚ_[ℓ]) ^ (k + 1)) * ∑ a ∈ Finset.antidiagonal k with a.1 < k,
      C ((-1 : ℚ_[ℓ]) ^ a.1) * MvPolynomial.map (ιz ℓ) (f a.1) * sigP (Pdisc hℓ) a.2) (k * 12) := by
    refine (MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun a ha => ?_).C_mul _
    obtain ⟨ha1, -⟩ := Finset.mem_filter.mp ha
    have hsum : a.1 + a.2 = k := Finset.mem_antidiagonal.mp ha1
    refine iso_of_eq (((MvPolynomial.isWeightedHomogeneous_C wt _).mul
      (iso_map_f hf a.1)).mul (iso_sigP (iso_Pdisc hℓ) a.2)) ?_
    rw [← hsum]; ring
  refine ev_injOn_iso (isUnit_1728 (R := ℚ_[ℓ])) hL hR (J_injective ℓ ?_)
  have hN := congrArg (MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ))
    (MvPolynomial.mul_esymm_eq_sum (Option (Fin ℓ)) ℤ k)
  simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast] at hN
  rw [map_mul, map_mul, ev_C, J_C, J_ev_map hℓ hJ, map_mul, map_sum, map_mul, ev_C, J_C, map_sum]
  have hS : ∀ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 < k),
      J ℓ (ev ℚ_[ℓ] (C ((-1 : ℚ_[ℓ]) ^ a.1) * MvPolynomial.map (ιz ℓ) (f a.1) *
        sigP (Pdisc hℓ) a.2)) =
      (-1) ^ a.1 * MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ)
          (MvPolynomial.esymm (Option (Fin ℓ)) ℤ a.1) *
        MvPolynomial.aeval (ys (Pdisc hℓ) 12 ζ) (MvPolynomial.psum (Option (Fin ℓ)) ℤ a.2) := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    have hsum : a.1 + a.2 = k := Finset.mem_antidiagonal.mp ha1
    rw [map_mul, map_mul, map_mul, map_mul, ev_C, J_C, J_ev_map hℓ hJ, aeval_psum_ys,
      psum_ys (iso_Pdisc hℓ) (by norm_num) hζ (by omega)]
    simp
  rw [Finset.sum_congr rfl hS]
  simp only [map_pow, map_neg, map_one, map_natCast]
  exact hN

/-! ### the theorem -/

section Main
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

lemma charZero_of_phi (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖) :
    CharZero K := by
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra h
  have hx : (n : ℤ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.mpr h
  have := SharpHQ.norm_phi_eq φ hφ hx
  rw [map_natCast, hn, norm_zero] at this
  exact (pow_ne_zero _ hε.ne') this.symm

/-- **`QuotBound` discharges `HConj`.** -/
theorem HConj_of_quotBound (φ : ℤ_[ℓ] →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (hε : 0 < ‖(ℓ : K)‖)
    (hQ : QuotBound ℓ hℓ φ) : SharpHQ.HConj ℓ hℓ φ := by
  classical
  haveI := charZero_of_phi φ hφ hε
  intro f hf ⟨ζ, hζ, hJ⟩ W hW hBrk
  obtain ⟨V, hHk, -, hΔH, hΔC, -, -⟩ := hQ W hW hBrk
  set y : Option (Fin ℓ) → K := fun C => eval (pt (V C)) (MvPolynomial.map φ (Pdisc hℓ)) with hy
  -- `T_ℓ Δ^m` over `ℤ_ℓ`
  have hPTex : ∀ m : ℕ, ∃ PT : Poly ℓ, 1 ≤ m → (Iso PT (m * 12) ∧
      MvPolynomial.map (ιz ℓ) PT = heckePoly ℓ (MvPolynomial.map (ιz ℓ) (Pdisc hℓ ^ m)) ∧
      ev ℤ_[ℓ] PT = Tq ℓ ((ℓ : ℤ_[ℓ]) ^ (m * 12 - 1)) (ev ℤ_[ℓ] (Pdisc hℓ ^ m))) := by
    intro m
    by_cases hm : 1 ≤ m
    · obtain ⟨PT, h1, h2, h3⟩ := exists_hecke_Zp' hℓ (by omega : 1 ≤ m * 12)
        (iso_of_eq ((iso_Pdisc hℓ).pow m) (by rw [smul_eq_mul]))
      exact ⟨PT, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h => absurd h hm⟩
  choose PT hPT using hPTex
  set p : ℕ → K := fun m => (ℓ : K) * eval (pt W) (MvPolynomial.map φ (PT m)) with hp
  have hpow : ∀ m, 1 ≤ m → ∑ i, y i ^ m = p m := by
    intro m hm
    obtain ⟨h1, -, h3⟩ := hPT m hm
    rw [hp]; beta_reduce
    rw [hHk (m * 12) (Pdisc hℓ ^ m) (PT m) (by omega)
      (iso_of_eq ((iso_Pdisc hℓ).pow m) (by rw [smul_eq_mul])) h1 h3]
    refine Finset.sum_congr rfl fun C _ => ?_
    simp only [hy, map_pow, eval_pow]
  -- the Newton identities over `ℤ_ℓ`, evaluated at `W`
  have hNZ : ∀ k : ℕ, C (k : ℤ_[ℓ]) * f k = C ((-1 : ℤ_[ℓ]) ^ (k + 1)) *
      ∑ a ∈ Finset.antidiagonal k with a.1 < k,
        C ((-1 : ℤ_[ℓ]) ^ a.1) * f a.1 * (C (ℓ : ℤ_[ℓ]) * PT a.2) := by
    intro k
    apply MvPolynomial.map_injective (ιz ℓ) Subtype.val_injective
    have h := newton_polyQ hℓ hf hζ hJ k
    simp only [map_mul, map_sum, map_C, map_pow, map_neg, map_one, map_natCast] at h ⊢
    rw [h]
    congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    have hsum : a.1 + a.2 = k := Finset.mem_antidiagonal.mp ha1
    obtain ⟨-, h2, -⟩ := hPT a.2 (by omega)
    rw [h2, sigP, Pq, map_pow, map_natCast]
  have hN : ∀ k : ℕ, (k : K) * eval (pt W) (MvPolynomial.map φ (f k)) = (-1) ^ (k + 1) *
      ∑ a ∈ Finset.antidiagonal k with a.1 < k,
        (-1) ^ a.1 * eval (pt W) (MvPolynomial.map φ (f a.1)) * p a.2 := by
    intro k
    have h := congrArg (fun P => eval (pt W) (MvPolynomial.map φ P)) (hNZ k)
    simp only [map_mul, map_sum, map_C, eval_mul, eval_sum, eval_C, map_pow, map_neg, map_one,
      map_natCast] at h
    rw [h, hp]
  have h0 : eval (pt W) (MvPolynomial.map φ (f 0)) = 1 := by
    have : f 0 = 1 := MvPolynomial.map_injective (ιz ℓ) Subtype.val_injective
      (by rw [f_zero hℓ hf hJ, map_one])
    rw [this, map_one, map_one]
  have hE := eq_esymm_of_newton y _ p hpow h0 hN
  have hyΔ : ∀ C, y C = (V C).Δ := fun C => ConjAlg.eval_Pdisc hℓ φ (V C)
  refine ⟨y, fun k _ => hE k, ?_, fun c => ?_⟩
  · rw [hyΔ]; exact hΔH
  · rw [hyΔ]; exact hΔC c

end Main

end UBSharp
