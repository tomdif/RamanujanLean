import RamanujanTau.FiniteArithmetic.EnvelopeReduction
import RamanujanTau.FiniteArithmetic.PadicDivision
import RamanujanTau.AtkinOBrienFinal.Main
import RamanujanTau.DBound.Decomp

/-!
# Exactness of the Atkin–O'Brien recurrence, from a finite model

Let `ℓ ∈ {13, 17, 19, 23}` and `ℓ^b ∣ L(b+2) − κ L(b)` (`AtkinOBrienFinal.L_padic`). Write
`L(b+2) − κ L(b) = ℓ^b g_b`. Then `g_b` lies in the offset-2 envelope, `T_b g_b = ℓ g_{b+1}`, and the
reduction `ḡ_b` is a cusp form of weight `2(ℓ−1)` modulo `ℓ`.

Modulo `ℓ`, the next reduction `ḡ_{b+1}` is determined by `ḡ_b` up to a contribution from the
offset-3 tail, and that contribution reduces into `ℂ + 𝔽_ℓ f` (`tail_reduce`). A finite family of
coefficient functionals that kills `1` and `f̄` therefore sees `ḡ_{b+1}` through finitely many
residues modulo `ℓ²` of `T(B_k/E²)`, for a basis `B_k` of cusp forms of weight `2(ℓ−1)`.
A finite check then propagates `ḡ_b ≠ 0` (`Model.nonzero`).

`Model.exact` concludes that no scalar improves the recurrence by one power of `ℓ` at any `b ≥ 1`.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanTau.FiniteArithmetic.ExactAtkin
open PowerSeries AtkinOBrien BoylanWebb AtkinOBrienFinal

/-! ### The tail inequalities -/

/-- Target exponents for the tail: everything beyond the weight `ℓ − 1` piece vanishes mod `ℓ`. -/
def τe (i : ℕ) : ℤ := if 2 ≤ i then 2 else 0

section ineq
variable {p : ℕ}

lemma int_ge_of_rat {n : ℤ} {k : ℤ} (h : ((k : ℚ) - 1) < n) : k ≤ n := by
  have : (k - 1 : ℤ) < n := by exact_mod_cast h
  omega

theorem U_tail (hp : 13 ≤ p) (i j : ℕ) : τe i - 1 ≤ max 0 (β p j - 3) + u p i j := by
  have hp' : (13 : ℚ) ≤ p := by exact_mod_cast hp
  have hpos : (0 : ℚ) < p + 1 := by linarith
  have hu : ((p : ℚ) * i - j) / (p + 1) - 1 ≤ u p i j := by
    unfold u; push_cast; linarith [Int.le_ceil (((p : ℚ) * i - j) / (p + 1))]
  have hβ : ((p : ℚ) * j - 2 - s p) / (p + 1) ≤ β p j := Int.le_ceil _
  have hs : s p = ((p : ℚ) + 1) / 2 := rfl
  have hmax : (β p j - 3 : ℤ) ≤ max 0 (β p j - 3) := le_max_right _ _
  have hmax0 : (0 : ℤ) ≤ max 0 (β p j - 3) := le_max_left _ _
  have hmq : ((β p j : ℚ) - 3) ≤ ((max 0 (β p j - 3) : ℤ) : ℚ) := by exact_mod_cast hmax
  generalize max 0 (β p j - 3) = M at hmq hmax0 hmax ⊢
  unfold τe
  split_ifs with hi
  · have hi' : (2 : ℚ) ≤ i := by exact_mod_cast hi
    by_cases hj : (j : ℚ) < p - 1
    · have hx : (1 : ℚ) < ((p : ℚ) * i - j) / (p + 1) := by
        rw [lt_div_iff₀ hpos]; nlinarith
      have : (1 : ℤ) < ⌈((p : ℚ) * i - j) / (p + 1)⌉ := Int.lt_ceil.mpr (by exact_mod_cast hx)
      unfold u; omega
    · push Not at hj
      apply int_ge_of_rat
      push_cast
      have key : (0 : ℚ) < ((p : ℚ) * j - 2 - s p) / (p + 1) - 3 + (((p : ℚ) * i - j) / (p + 1) - 1) := by
        rw [hs]
        have : ((p : ℚ) * j - 2 - (p + 1) / 2) / (p + 1) - 3 + (((p : ℚ) * i - j) / (p + 1) - 1) =
            (((p : ℚ) - 1) * j + p * i - 2 - (p + 1) / 2 - 4 * (p + 1)) / (p + 1) := by
          field_simp; ring
        rw [this]
        apply div_pos _ hpos
        nlinarith
      linarith
  · push Not at hi
    by_cases hj : (j : ℚ) < p + 1
    · have hx : (-1 : ℚ) < ((p : ℚ) * i - j) / (p + 1) := by
        rw [lt_div_iff₀ hpos]
        have : (0 : ℚ) ≤ (p : ℚ) * i := by positivity
        nlinarith
      have : (-1 : ℤ) < ⌈((p : ℚ) * i - j) / (p + 1)⌉ := Int.lt_ceil.mpr (by exact_mod_cast hx)
      unfold u; omega
    · push Not at hj
      apply int_ge_of_rat
      push_cast
      have key : (-2 : ℚ) < ((p : ℚ) * j - 2 - s p) / (p + 1) - 3 + (((p : ℚ) * i - j) / (p + 1) - 1) := by
        rw [hs]
        have : ((p : ℚ) * j - 2 - (p + 1) / 2) / (p + 1) - 3 + (((p : ℚ) * i - j) / (p + 1) - 1) + 2 =
            (((p : ℚ) - 1) * j + p * i - 2 - (p + 1) / 2 - 2 * (p + 1)) / (p + 1) := by
          field_simp; ring
        have h0 : (0 : ℚ) ≤ (p : ℚ) * i := by positivity
        have : (0 : ℚ) < (((p : ℚ) - 1) * j + p * i - 2 - (p + 1) / 2 - 2 * (p + 1)) / (p + 1) := by
          apply div_pos _ hpos; nlinarith
        linarith
      linarith

theorem D_tail (hp : 13 ≤ p) (i j : ℕ) : τe i - 1 ≤ max 0 (α p j - 3) + d p i j := by
  have hp' : (13 : ℚ) ≤ p := by exact_mod_cast hp
  have hpos : (0 : ℚ) < p + 1 := by linarith
  have hs : s p = ((p : ℚ) + 1) / 2 := rfl
  have hd : ((p : ℚ) * i - j - s p) / (p + 1) - 1 ≤ d p i j := by
    unfold d; push_cast; linarith [Int.le_ceil (((p : ℚ) * i - j - s p) / (p + 1))]
  have hα : ((p : ℚ) * j - 2) / (p + 1) ≤ α p j := Int.le_ceil _
  have hmax : (α p j - 3 : ℤ) ≤ max 0 (α p j - 3) := le_max_right _ _
  have hmax0 : (0 : ℤ) ≤ max 0 (α p j - 3) := le_max_left _ _
  have hmq : ((α p j : ℚ) - 3) ≤ ((max 0 (α p j - 3) : ℤ) : ℚ) := by exact_mod_cast hmax
  generalize max 0 (α p j - 3) = M at hmq hmax0 hmax ⊢
  unfold τe
  split_ifs with hi
  · have hi' : (2 : ℚ) ≤ i := by exact_mod_cast hi
    by_cases hj : (j : ℚ) < p - 1 - s p
    · have hx : (1 : ℚ) < ((p : ℚ) * i - j - s p) / (p + 1) := by
        rw [lt_div_iff₀ hpos]; nlinarith
      have : (1 : ℤ) < ⌈((p : ℚ) * i - j - s p) / (p + 1)⌉ := Int.lt_ceil.mpr (by exact_mod_cast hx)
      unfold d; omega
    · push Not at hj
      rw [hs] at hj
      apply int_ge_of_rat
      push_cast
      have key : (0 : ℚ) < ((p : ℚ) * j - 2) / (p + 1) - 3 + (((p : ℚ) * i - j - s p) / (p + 1) - 1) := by
        rw [hs]
        have : ((p : ℚ) * j - 2) / (p + 1) - 3 + (((p : ℚ) * i - j - (p + 1) / 2) / (p + 1) - 1) =
            (((p : ℚ) - 1) * j + p * i - 2 - (p + 1) / 2 - 4 * (p + 1)) / (p + 1) := by
          field_simp; ring
        rw [this]
        apply div_pos _ hpos
        nlinarith
      linarith
  · push Not at hi
    by_cases hj : (j : ℚ) < p + 1 - s p
    · have hx : (-1 : ℚ) < ((p : ℚ) * i - j - s p) / (p + 1) := by
        rw [lt_div_iff₀ hpos]
        have : (0 : ℚ) ≤ (p : ℚ) * i := by positivity
        nlinarith
      have : (-1 : ℤ) < ⌈((p : ℚ) * i - j - s p) / (p + 1)⌉ := Int.lt_ceil.mpr (by exact_mod_cast hx)
      unfold d; omega
    · push Not at hj
      rw [hs] at hj
      apply int_ge_of_rat
      push_cast
      have key : (-2 : ℚ) < ((p : ℚ) * j - 2) / (p + 1) - 3 + (((p : ℚ) * i - j - s p) / (p + 1) - 1) := by
        rw [hs]
        have : ((p : ℚ) * j - 2) / (p + 1) - 3 + (((p : ℚ) * i - j - (p + 1) / 2) / (p + 1) - 1) + 2 =
            (((p : ℚ) - 1) * j + p * i - 2 - (p + 1) / 2 - 2 * (p + 1)) / (p + 1) := by
          field_simp; ring
        have h0 : (0 : ℚ) ≤ (p : ℚ) * i := by positivity
        have : (0 : ℚ) < (((p : ℚ) - 1) * j + p * i - 2 - (p + 1) / 2 - 2 * (p + 1)) / (p + 1) := by
          apply div_pos _ hpos; nlinarith
        linarith
      linarith

lemma envelopes_ge_three (hp : 13 ≤ p) (i : ℕ) (hi : 3 ≤ i) : 3 ≤ α p i ∧ 3 ≤ β p i := by
  have hp' : (13 : ℚ) ≤ p := by exact_mod_cast hp
  have hi' : (3 : ℚ) ≤ i := by exact_mod_cast hi
  have hpos : (0 : ℚ) < p + 1 := by linarith
  have h1 : (2 : ℚ) < ((p : ℚ) * i - 2 - s p) / (p + 1) := by
    rw [lt_div_iff₀ hpos]; unfold s; nlinarith
  have h2 : ((p : ℚ) * i - 2 - s p) / (p + 1) ≤ ((p : ℚ) * i - 2) / (p + 1) := by
    apply div_le_div_of_nonneg_right _ hpos.le; unfold s; linarith
  constructor
  · have : (2 : ℤ) < α p i := Int.lt_ceil.mpr (by push_cast; linarith)
    omega
  · have : (2 : ℤ) < β p i := Int.lt_ceil.mpr (by push_cast; linarith)
    omega

lemma envelopes_le_two (hp : 13 ≤ p) (i : ℕ) (hi : i ≤ 2) : α p i ≤ 2 ∧ β p i ≤ 2 := by
  have hp' : (13 : ℚ) ≤ p := by exact_mod_cast hp
  have hi' : (i : ℚ) ≤ 2 := by exact_mod_cast hi
  have hi0 : (0 : ℚ) ≤ i := by positivity
  have hpos : (0 : ℚ) < p + 1 := by linarith
  have h1 : ((p : ℚ) * i - 2) / (p + 1) ≤ 2 := by
    rw [div_le_iff₀ hpos]; nlinarith
  have h2 : ((p : ℚ) * i - 2 - s p) / (p + 1) ≤ ((p : ℚ) * i - 2) / (p + 1) := by
    apply div_le_div_of_nonneg_right _ hpos.le; unfold s; linarith
  exact ⟨Int.ceil_le.mpr (by exact_mod_cast h1), Int.ceil_le.mpr (by push_cast; linarith)⟩

end ineq

variable {ℓ : ℕ} [hℓp : Fact ℓ.Prime] (hℓ : 5 ≤ ℓ)
include hℓ

/-! ### The tail reduces into `𝔽_ℓ + 𝔽_ℓ f̄` -/

lemma γ_ge_three (hℓ13 : 13 ≤ ℓ) (b i : ℕ) (hi : 3 ≤ i) : 3 ≤ γ ℓ b i := by
  have := envelopes_ge_three hℓ13 i hi
  unfold γ; split_ifs
  · exact this.1
  · exact this.2

lemma γ_le_two (hℓ13 : 13 ≤ ℓ) (b i : ℕ) (hi : i ≤ 2) : γ ℓ b i ≤ 2 := by
  have := envelopes_le_two hℓ13 i hi
  unfold γ; split_ifs
  · exact this.1
  · exact this.2

theorem tail_env (hℓ13 : 13 ≤ ℓ) (hUB : UB ℓ hℓ) (hDB : DB ℓ hℓ) (b : ℕ) (y : PS ℓ)
    (hy : Env ℓ hℓ 3 (γ ℓ b) y) : Env ℓ hℓ 1 τe (Tl ℓ b y) := by
  unfold γ Tl at *
  split_ifs at * with h
  · exact transfer hℓ (Dlin ℓ) (d ℓ) (cols_D ℓ hℓ hDB) 3 (α ℓ) τe (D_tail hℓ13) y hy
  · exact transfer hℓ (Ulin ℓ) (u ℓ) (cols_U ℓ hℓ hUB) 3 (β ℓ) τe (U_tail hℓ13) y hy

/-- An offset-1 element of the tail envelope reduces to a constant plus a multiple of `f̄`. -/
theorem tail_reduce (hℓ13 : 13 ≤ ℓ) (hℓ24 : ℓ ≤ 24) (f : PowerSeries ℤ)
    (hf : IntForm ((ℓ - 1 : ℕ) : ℤ) f) (hf0 : coeff 0 f = 0) (hf1 : coeff 1 (Ψ ℓ f) ≠ 0)
    (F : PS ℓ) (hF : Env ℓ hℓ 1 τe F) :
    ∃ a t : ZMod ℓ, PowerSeries.map (PadicInt.toZMod (p := ℓ)) F = C a + C t * Ψ ℓ f := by
  obtain ⟨g, hg, hgF⟩ := envelope_reduction hℓ τe (fun i hi => by simp [τe, hi]) F hF
  obtain ⟨A, hA, hAe⟩ := exists_hasse_lift ℓ hℓ
  set a : ZMod ℓ := coeff 0 (Ψ ℓ g)
  set h := g - C ((a.val : ℕ) : ℤ) * A
  have hh : IntForm ((ℓ - 1 : ℕ) : ℤ) h := hg.sub (hA.C_mul _)
  have hΨ : Ψ ℓ h = Ψ ℓ g - C a := by
    simp only [h, map_sub, map_mul, PowerSeries.map_C, hAe, mul_one]
    congr 2
    simp
  have h0 : coeff 0 (Ψ ℓ h) = 0 := by rw [hΨ, map_sub, coeff_C]; simp [a]
  obtain ⟨t, ht⟩ := line hℓ13 hℓ24 f hf hf0 hf1 h hh h0
  refine ⟨a, t, ?_⟩
  rw [← hgF, ← ht, hΨ]
  ring

/-! ### The error sequence -/

lemma Ll_env (hℓ13 : 13 ≤ ℓ) (hUB : UB ℓ hℓ) (hDB : DB ℓ hℓ) (b : ℕ) :
    Env ℓ hℓ 1 (γ ℓ b) (Ll ℓ b) := by
  induction b with
  | zero =>
    have : γ ℓ 0 = α ℓ := by simp [γ]
    rw [this, show Ll ℓ 0 = 1 by simp [Ll, BoylanWebb.L]]
    exact env_one hℓ
  | succ b ih => rw [Ll_succ]; exact env_step hℓ hℓ13 hUB hDB 1 (by norm_num) b _ ih

lemma Ll_cusp (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (b : ℕ) (hb : 1 ≤ b) : coeff 0 (Ll ℓ b) = 0 := by
  rw [Ll, coeff_map, L_cuspidal ℓ h24 hℓ b hb, map_zero]

lemma e_succ (κ : ℤ_[ℓ]) (b : ℕ) :
    Ll ℓ (b + 1 + 2) - κ • Ll ℓ (b + 1) = Tl ℓ b (Ll ℓ (b + 2) - κ • Ll ℓ b) := by
  have h1 : Ll ℓ (b + 1 + 2) = Tl ℓ b (Ll ℓ (b + 2)) := by
    rw [show b + 1 + 2 = (b + 2) + 1 by ring, Ll_succ, Tl_add_two]
  rw [map_sub, map_smul, h1, Ll_succ b]

/-- **The normalized errors.** -/
theorem errors (hℓ13 : 13 ≤ ℓ) (h24 : 24 * δ ℓ + 1 = ℓ ^ 2) (hUB : UB ℓ hℓ) (hDB : DB ℓ hℓ)
    (κ : ℤ_[ℓ]) (hser : ∀ b, 1 ≤ b → Dvd (ℓ : ℤ_[ℓ]) b (Ll ℓ (b + 2) - κ • Ll ℓ b)) :
    ∃ g : ℕ → PS ℓ, ∀ b, 1 ≤ b → g b ∈ envSub hℓ 2 (γ ℓ b) ∧
      Ll ℓ (b + 2) - κ • Ll ℓ b = (ℓ : ℤ_[ℓ]) ^ b • g b ∧ Tl ℓ b (g b) = (ℓ : ℤ_[ℓ]) • g (b + 1) := by
  classical
  let g : ℕ → PS ℓ := fun b => if hb : 1 ≤ b then (hser b hb).choose else 0
  have hg : ∀ b, 1 ≤ b → Ll ℓ (b + 2) - κ • Ll ℓ b = (ℓ : ℤ_[ℓ]) ^ b • g b := fun b hb => by
    simp only [g, dif_pos hb]; exact (hser b hb).choose_spec
  have hT : ∀ b, 1 ≤ b → Tl ℓ b (g b) = (ℓ : ℤ_[ℓ]) • g (b + 1) := by
    intro b hb
    have h1 := hg (b + 1) (by omega)
    rw [e_succ hℓ, hg b hb, map_smul, pow_succ, mul_smul] at h1
    have h0 : (ℓ : ℤ_[ℓ]) ^ b • (Tl ℓ b (g b) - (ℓ : ℤ_[ℓ]) • g (b + 1)) = 0 := by
      rw [smul_sub, h1, sub_self]
    exact sub_eq_zero.mp (cancel_pow (ℓ : ℤ_[ℓ]) PS_reg b _ h0)
  have he : ∀ b, 1 ≤ b → Ll ℓ (b + 2) - κ • Ll ℓ b ∈ envSub hℓ 1 (γ ℓ b) := by
    intro b hb
    have h2 : Ll ℓ (b + 2) ∈ envSub hℓ 1 (γ ℓ b) :=
      ⟨Ll_cusp hℓ h24 _ (by omega), by rw [← γ_add_two]; exact Ll_env hℓ hℓ13 hUB hDB _⟩
    exact Submodule.sub_mem _ h2
      (Submodule.smul_mem _ _ ⟨Ll_cusp hℓ h24 _ hb, Ll_env hℓ hℓ13 hUB hDB _⟩)
  have hcusp : ∀ b, 1 ≤ b → coeff 0 (g b) = 0 := by
    intro b hb
    have h := congrArg (coeff 0) (hg b hb)
    rw [(he b hb).1, coeff_smul, smul_eq_mul] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ ell_ne_zero)
  have hmem : ∀ b, 1 ≤ b → g b ∈ envSub hℓ 2 (γ ℓ b) := by
    intro b hb
    induction b, hb using Nat.le_induction with
    | base =>
      refine ⟨hcusp 1 le_rfl, ?_⟩
      have := env_div hℓ 1 (γ ℓ 1) (he 1 le_rfl).2 (by rw [hg 1 le_rfl, pow_one])
      simpa using this
    | succ b hb ih =>
      refine ⟨hcusp (b + 1) (by omega), ?_⟩
      have h := env_div hℓ 1 (γ ℓ (b + 1)) (env_step hℓ hℓ13 hUB hDB 2 le_rfl b _ ih.2) (hT b hb)
      simpa using h
  exact ⟨g, fun b hb => ⟨hmem b hb, hg b hb, hT b hb⟩⟩

/-! ### The offset-2 envelope modulo `ℓ` -/

/-- An offset-2 element reduces to a form of weight `2(ℓ − 1)`. -/
theorem env2_reduction (γ : ℕ → ℤ) (hγ : ∀ i, 3 ≤ i → 3 ≤ γ i) (F : PS ℓ) (hF : Env ℓ hℓ 2 γ F) :
    ∃ g : PowerSeries ℤ, IntForm ((2 * (ℓ - 1) : ℕ) : ℤ) g ∧
      Ψ ℓ g = PowerSeries.map (PadicInt.toZMod (p := ℓ)) F := by
  obtain ⟨I₀, a₀, haK₀, hA₀, hab₀⟩ := hF 1
  set I := max I₀ 3 with hI
  set a := trunc I₀ a₀ with ha
  have haK : ∀ i, a i ∈ Kpiece ℓ hℓ i := trunc_mem hℓ haK₀
  have hA : Approx ℓ hℓ 1 I a F := approx_trunc hℓ hA₀ (le_max_left _ _)
  have hab : ∀ i, Dvd (ℓ : ℤ_[ℓ]) (max 0 (γ i - 2)).toNat (a i) := fun i => trunc_dvd i (hab₀ i)
  have hz : ∀ i, 3 ≤ i → MvPolynomial.map (PadicInt.toZMod (p := ℓ)) (a i) = 0 := by
    intro i hi
    obtain ⟨z, hz⟩ := Dvd_mono (a := 1) (by have := hγ i hi; omega) (hab i)
    rw [hz, pow_one, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_natCast,
      ZMod.natCast_self, map_zero, zero_mul]
  set P₀ := MvPolynomial.map (PadicInt.toZMod (p := ℓ)) (a 0)
  set P₁ := MvPolynomial.map (PadicInt.toZMod (p := ℓ)) (a 1)
  set P₂ := MvPolynomial.map (PadicInt.toZMod (p := ℓ)) (a 2)
  have hFbar : PowerSeries.map (PadicInt.toZMod (p := ℓ)) F =
      ModP.ev (ZMod ℓ) P₀ + ModP.ev (ZMod ℓ) P₁ + ModP.ev (ZMod ℓ) P₂ := by
    obtain ⟨g, hg⟩ := hA
    have e : F = ∑ i ∈ Finset.range I, ModP.ev ℤ_[ℓ] (a i) * Einv ℓ hℓ ^ i + (ℓ : ℤ_[ℓ]) ^ 1 • g := by
      rw [← hg]; abel
    rw [e, map_add, map_katzSum, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, map_pow,
      map_natCast, ZMod.natCast_self, zero_pow one_ne_zero, map_zero, zero_mul, add_zero,
      ← Finset.sum_range_add_sum_Ico _ (le_max_right I₀ 3 : 3 ≤ I)]
    rw [Finset.sum_eq_zero (s := Finset.Ico 3 I) (fun i hi => by
      rw [hz i (Finset.mem_Ico.mp hi).1, map_zero]), add_zero, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]
  have hiso : ∀ i, ModP.Iso (MvPolynomial.map (PadicInt.toZMod (p := ℓ)) (a i)) (0 + i * (ℓ - 1)) :=
    fun i => iso_of_mem hℓ ((Finset.coe_subset.mpr (MvPolynomial.support_map_subset _ _)).trans
      ((mem_Kpiece hℓ).mp (haK i)))
  have hA2 := ModP.iso_hasseBar hℓ
  have hiso' : ModP.Iso (P₀ * ModP.hasseBar ℓ hℓ ^ 2 + P₁ * ModP.hasseBar ℓ hℓ + P₂) (2 * (ℓ - 1)) := by
    refine MvPolynomial.IsWeightedHomogeneous.add (MvPolynomial.IsWeightedHomogeneous.add ?_ ?_) ?_
    · exact ModP.iso_of_eq ((hiso 0).mul (hA2.pow 2)) (by simp; try ring)
    · exact ModP.iso_of_eq ((hiso 1).mul hA2) (by simp; try ring)
    · exact ModP.iso_of_eq (hiso 2) (by simp; try ring)
  obtain ⟨g, hg, hgΨ⟩ := lift_iso ℓ (2 * (ℓ - 1)) _ hiso'
  refine ⟨g, hg, ?_⟩
  rw [hgΨ, hFbar, map_add, map_add, map_mul, map_mul, map_pow, ModP.ev_hasseBar, one_pow, mul_one,
    mul_one]

/-- A classical form of weight `2(ℓ − 1)` divided by `E²` is in every envelope of offset `≥ γ(i)`,
`i ≤ 2`. -/
theorem fraction_env2 (P : Poly ℓ) (hP : ModP.Iso P (2 * (ℓ - 1))) (c : ℤ) (γ : ℕ → ℤ)
    (hγ : ∀ i, i ≤ 2 → γ i ≤ c) : Env ℓ hℓ c γ (ModP.ev ℤ_[ℓ] P * Einv ℓ hℓ ^ 2) := by
  intro N
  obtain ⟨cc, hc, hc0, hD⟩ := DBound.decompN hℓ N 2 P (by simpa using hP)
  refine ⟨3, cc, hc, hD, fun i => ?_⟩
  by_cases hi : i ≤ 2
  · have he : (max 0 (γ i - c)).toNat = 0 := by have := hγ i hi; omega
    rw [he]
    exact ⟨cc i, by simp⟩
  · rw [hc0 i (by omega)]
    exact Dvd_zero _

/-! ### Coefficient functionals -/

/-- `F ↦ Σ_{m < K} w_m a_m(F)`. -/
noncomputable def obs (w : ℕ → ℤ) (K : ℕ) : PS ℓ →ₗ[ℤ_[ℓ]] ℤ_[ℓ] :=
  ∑ m ∈ Finset.range K, (w m : ℤ_[ℓ]) • coeff m

omit hℓ in
lemma obs_apply (w : ℕ → ℤ) (K : ℕ) (F : PS ℓ) :
    obs w K F = ∑ m ∈ Finset.range K, (w m : ℤ_[ℓ]) * coeff m F := by
  simp [obs]

omit hℓ in
lemma toZMod_obs (w : ℕ → ℤ) (K : ℕ) (F : PS ℓ) :
    PadicInt.toZMod (obs w K F) =
      ∑ m ∈ Finset.range K, (w m : ZMod ℓ) * coeff m (PowerSeries.map (PadicInt.toZMod (p := ℓ)) F) := by
  rw [obs_apply, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, map_intCast, coeff_map]

/-! ### One step of the finite model -/

/-- The finite data for one operator. -/
structure StepData (n r K : ℕ) (Top : PS ℓ →ₗ[ℤ_[ℓ]] PS ℓ) (G : Fin n → PS ℓ) (w : Fin r → ℕ → ℤ)
    where
  mu : Fin n → ZMod ℓ
  tau : Fin r → Fin n → ℕ
  hmu : ∀ k, PadicInt.toZMod (coeff 1 (Top (G k))) = mu k
  htau : ∀ j k, PadicInt.toZModPow 2 (obs (w j) K (Top (G k))) =
    PadicInt.toZModPow 2 ((ℓ : ℤ_[ℓ]) * (tau j k : ℤ_[ℓ]))
  check : ∀ c : Fin n → ZMod ℓ, c ≠ 0 → ∑ k, c k * mu k = 0 →
    ∃ j, ∑ k, c k * (tau j k : ZMod ℓ) ≠ 0

omit hℓ in
lemma toZMod_lift (c : ZMod ℓ) : PadicInt.toZMod (((c.val : ℕ) : ℤ_[ℓ])) = c := by
  rw [map_natCast, ZMod.natCast_zmod_val]

/-- **The step**: a nonzero reduction stays nonzero. -/
theorem step (hℓ13 : 13 ≤ ℓ) (hℓ24 : ℓ ≤ 24) (f : PowerSeries ℤ)
    (hf : IntForm ((ℓ - 1 : ℕ) : ℤ) f) (hf0 : coeff 0 f = 0) (hf1 : coeff 1 (Ψ ℓ f) ≠ 0)
    {n r K : ℕ} (B : Fin n → Poly ℓ) (hB : ∀ k, ModP.Iso (B k) (2 * (ℓ - 1)))
    (hB0 : ∀ k, coeff 0 (ModP.ev ℤ_[ℓ] (B k)) = 0)
    (hspan : ∀ a : PowerSeries ℤ, IntForm ((2 * (ℓ - 1) : ℕ) : ℤ) a → coeff 0 (Ψ ℓ a) = 0 →
      ∃ c : Fin n → ZMod ℓ, Ψ ℓ a =
        ∑ k, C (c k) * PowerSeries.map (PadicInt.toZMod (p := ℓ)) (ModP.ev ℤ_[ℓ] (B k)))
    (w : Fin r → ℕ → ℤ) (hw0 : ∀ j, w j 0 = 0)
    (hwf : ∀ j, ∑ m ∈ Finset.range K, (w j m : ZMod ℓ) * coeff m (Ψ ℓ f) = 0)
    (γ : ℕ → ℤ) (hγ3 : ∀ i, 3 ≤ i → 3 ≤ γ i) (hγ2 : ∀ i, i ≤ 2 → γ i ≤ 2)
    (Top : PS ℓ →ₗ[ℤ_[ℓ]] PS ℓ) (htail : ∀ y, Env ℓ hℓ 3 γ y → Env ℓ hℓ 1 τe (Top y))
    (D : StepData n r K Top (fun k => ModP.ev ℤ_[ℓ] (B k) * Einv ℓ hℓ ^ 2) w)
    (g g' : PS ℓ) (hg : g ∈ envSub hℓ 2 γ) (hT : Top g = (ℓ : ℤ_[ℓ]) • g')
    (hne : PowerSeries.map (PadicInt.toZMod (p := ℓ)) g ≠ 0) :
    PowerSeries.map (PadicInt.toZMod (p := ℓ)) g' ≠ 0 := by
  set G : Fin n → PS ℓ := fun k => ModP.ev ℤ_[ℓ] (B k) * Einv ℓ hℓ ^ 2 with hGdef
  obtain ⟨a, ha, hae⟩ := env2_reduction hℓ γ hγ3 g hg.2
  have ha0 : coeff 0 (Ψ ℓ a) = 0 := by rw [hae, coeff_map, hg.1, map_zero]
  obtain ⟨c, hc⟩ := hspan a ha ha0
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hne
    rw [← hae, hc]
    simp
  set cl : Fin n → ℤ_[ℓ] := fun k => ((c k).val : ℤ_[ℓ])
  set G0 := ∑ k, cl k • G k
  have hmapG : ∀ k, PowerSeries.map (PadicInt.toZMod (p := ℓ)) (G k) =
      PowerSeries.map (PadicInt.toZMod (p := ℓ)) (ModP.ev ℤ_[ℓ] (B k)) := fun k => by
    simp only [hGdef, map_mul, map_pow, map_Einv, one_pow, mul_one]
  have hdiff : PowerSeries.map (PadicInt.toZMod (p := ℓ)) (g - G0) = 0 := by
    rw [map_sub, ← hae, hc, map_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, toZMod_lift, hmapG]
  obtain ⟨y, hy⟩ := PS_dvd_of_map (g - G0) hdiff
  have hGmem : ∀ k, G k ∈ envSub hℓ 2 γ := fun k =>
    ⟨by rw [hGdef]; simp only [coeff_zero_eq_constantCoeff_apply, map_mul]
        rw [← coeff_zero_eq_constantCoeff_apply, hB0 k, zero_mul],
     fraction_env2 hℓ (B k) (hB k) 2 γ hγ2⟩
  have hG0 : G0 ∈ envSub hℓ 2 γ := Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hGmem k)
  have hyenv : Env ℓ hℓ 3 γ y := by
    have := env_div hℓ 2 γ (Submodule.sub_mem _ hg hG0).2 hy
    simpa using this
  have hTg : (ℓ : ℤ_[ℓ]) • g' = ∑ k, cl k • Top (G k) + (ℓ : ℤ_[ℓ]) • Top y := by
    rw [← hT, show g = G0 + (ℓ : ℤ_[ℓ]) • y by rw [← hy]; abel, map_add, map_sum, map_smul]
    simp only [map_smul]
  -- the constraint
  have hμ : ∑ k, c k * D.mu k = 0 := by
    have h := congrArg (fun F => PadicInt.toZMod (coeff 1 F)) hTg
    simp only [coeff_smul, smul_eq_mul, map_mul, map_natCast, ZMod.natCast_self, zero_mul,
      map_add, map_sum, add_zero] at h
    rw [show ∑ k, c k * D.mu k =
        ∑ k, PadicInt.toZMod (cl k) * PadicInt.toZMod (coeff 1 (Top (G k))) from
      Finset.sum_congr rfl fun k _ => by rw [toZMod_lift, D.hmu]]
    exact h.symm
  obtain ⟨j, hj⟩ := D.check c hc0 hμ
  -- the observation
  have htailz : PadicInt.toZMod (obs (w j) K (Top y)) = 0 := by
    obtain ⟨a', t, ht⟩ := tail_reduce hℓ hℓ13 hℓ24 f hf hf0 hf1 _ (htail y hyenv)
    rw [toZMod_obs, ht]
    simp only [map_add, coeff_C, coeff_C_mul, mul_add]
    rw [Finset.sum_add_distrib]
    have h1 : ∑ m ∈ Finset.range K, (w j m : ZMod ℓ) * (if m = 0 then a' else 0) = 0 :=
      Finset.sum_eq_zero fun m _ => by split_ifs with hm <;> simp [hm, hw0]
    rw [h1, zero_add]
    have h2 := hwf j
    rw [show ∑ m ∈ Finset.range K, (w j m : ZMod ℓ) * (t * coeff m (Ψ ℓ f)) =
      t * ∑ m ∈ Finset.range K, (w j m : ZMod ℓ) * coeff m (Ψ ℓ f) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring, h2, mul_zero]
  have hobs : PadicInt.toZModPow 2 ((ℓ : ℤ_[ℓ]) * obs (w j) K g') =
      PadicInt.toZModPow 2 ((ℓ : ℤ_[ℓ]) *
        (∑ k, cl k * (D.tau j k : ℤ_[ℓ]) + obs (w j) K (Top y))) := by
    have h := congrArg (fun F => PadicInt.toZModPow 2 (obs (w j) K F)) hTg
    simp only [map_add, map_sum, map_smul, smul_eq_mul, map_mul] at h
    rw [map_mul, h, mul_add, map_add, Finset.mul_sum, map_sum]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [D.htau j k]; simp only [map_mul]; ring
    · rw [map_mul]
  have hval := (PadicDivision.cancel_mod_square _ _).mp hobs
  rw [map_add, htailz, add_zero, map_sum] at hval
  intro h0
  apply hj
  have : PadicInt.toZMod (obs (w j) K g') = 0 := by rw [toZMod_obs, h0]; simp
  rw [this] at hval
  rw [hval]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, toZMod_lift, map_natCast]

/-! ### Exactness at every `b` -/

omit hℓ in
lemma isUnit_of_toZMod {x : ℤ_[ℓ]} (hx : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  by_contra hn
  apply hx
  have hz : x ∈ IsLocalRing.maximalIdeal ℤ_[ℓ] := (IsLocalRing.mem_maximalIdeal _).mpr hn
  rwa [← PadicInt.ker_toZMod, RingHom.mem_ker] at hz

omit hℓ in
lemma unit_coeff (f : PowerSeries ℤ) (hf1 : coeff 1 (Ψ ℓ f) ≠ 0)
    (hrank : ∀ b, 1 ≤ b → ∃ x : ZMod ℓ, x ≠ 0 ∧ Ψ ℓ (L ℓ b) = C x * Ψ ℓ f) (b : ℕ) (hb : 1 ≤ b) :
    coeff 1 (PowerSeries.map (PadicInt.toZMod (p := ℓ)) (Ll ℓ b)) ≠ 0 := by
  obtain ⟨x, hx, hL⟩ := hrank b hb
  rw [Ll, map_map_int, hL, coeff_C_mul]
  exact mul_ne_zero hx hf1

/-- **Exactness from the finite model**: no scalar improves the recurrence by one power of `ℓ`. -/
theorem exact_of_model (hℓ13 : 13 ≤ ℓ) (hℓ24 : ℓ ≤ 24) (h24 : 24 * δ ℓ + 1 = ℓ ^ 2)
    (hUB : UB ℓ hℓ) (hDB : DB ℓ hℓ) (κ : ℤ_[ℓ])
    (hser : ∀ b, 1 ≤ b → Dvd (ℓ : ℤ_[ℓ]) b (Ll ℓ (b + 2) - κ • Ll ℓ b))
    (f : PowerSeries ℤ) (hf : IntForm ((ℓ - 1 : ℕ) : ℤ) f) (hf0 : coeff 0 f = 0)
    (hf1 : coeff 1 (Ψ ℓ f) ≠ 0)
    (hrank : ∀ b, 1 ≤ b → ∃ x : ZMod ℓ, x ≠ 0 ∧ Ψ ℓ (L ℓ b) = C x * Ψ ℓ f)
    (hbase : ∀ c : ℤ_[ℓ], ¬ Dvd (ℓ : ℤ_[ℓ]) 2 (Ll ℓ 3 - c • Ll ℓ 1))
    {n r K : ℕ} (B : Fin n → Poly ℓ) (hB : ∀ k, ModP.Iso (B k) (2 * (ℓ - 1)))
    (hB0 : ∀ k, coeff 0 (ModP.ev ℤ_[ℓ] (B k)) = 0)
    (hspan : ∀ a : PowerSeries ℤ, IntForm ((2 * (ℓ - 1) : ℕ) : ℤ) a → coeff 0 (Ψ ℓ a) = 0 →
      ∃ c : Fin n → ZMod ℓ, Ψ ℓ a =
        ∑ k, C (c k) * PowerSeries.map (PadicInt.toZMod (p := ℓ)) (ModP.ev ℤ_[ℓ] (B k)))
    (w : Fin r → ℕ → ℤ) (hw0 : ∀ j, w j 0 = 0)
    (hwf : ∀ j, ∑ m ∈ Finset.range K, (w j m : ZMod ℓ) * coeff m (Ψ ℓ f) = 0)
    (DU : StepData n r K (Ulin ℓ) (fun k => ModP.ev ℤ_[ℓ] (B k) * Einv ℓ hℓ ^ 2) w)
    (DD : StepData n r K (Dlin ℓ) (fun k => ModP.ev ℤ_[ℓ] (B k) * Einv ℓ hℓ ^ 2) w) :
    ∀ b, 1 ≤ b → ∀ c : ℤ_[ℓ], ¬ Dvd (ℓ : ℤ_[ℓ]) (b + 1) (Ll ℓ (b + 2) - c • Ll ℓ b) := by
  obtain ⟨g, hg⟩ := errors hℓ hℓ13 h24 hUB hDB κ hser
  have hstep : ∀ b, 1 ≤ b → PowerSeries.map (PadicInt.toZMod (p := ℓ)) (g b) ≠ 0 →
      PowerSeries.map (PadicInt.toZMod (p := ℓ)) (g (b + 1)) ≠ 0 := by
    intro b hb hne
    rcases Nat.even_or_odd b with h | h
    · have hT : Tl ℓ b = Dlin ℓ := by simp [Tl, h]
      have htail : ∀ y, Env ℓ hℓ 3 (γ ℓ b) y → Env ℓ hℓ 1 τe (Dlin ℓ y) := fun y hy => by
        have := tail_env hℓ hℓ13 hUB hDB b y hy; rwa [hT] at this
      exact step hℓ hℓ13 hℓ24 f hf hf0 hf1 B hB hB0 hspan w hw0 hwf (γ ℓ b)
        (γ_ge_three hℓ hℓ13 b) (γ_le_two hℓ hℓ13 b) (Dlin ℓ) htail DD (g b) (g (b + 1))
        (hg b hb).1 (by rw [← hT]; exact (hg b hb).2.2) hne
    · have hT : Tl ℓ b = Ulin ℓ := by simp [Tl, Nat.not_even_iff_odd.mpr h]
      have htail : ∀ y, Env ℓ hℓ 3 (γ ℓ b) y → Env ℓ hℓ 1 τe (Ulin ℓ y) := fun y hy => by
        have := tail_env hℓ hℓ13 hUB hDB b y hy; rwa [hT] at this
      exact step hℓ hℓ13 hℓ24 f hf hf0 hf1 B hB hB0 hspan w hw0 hwf (γ ℓ b)
        (γ_ge_three hℓ hℓ13 b) (γ_le_two hℓ hℓ13 b) (Ulin ℓ) htail DU (g b) (g (b + 1))
        (hg b hb).1 (by rw [← hT]; exact (hg b hb).2.2) hne
  have hbase' : PowerSeries.map (PadicInt.toZMod (p := ℓ)) (g 1) ≠ 0 := by
    intro h0
    obtain ⟨y, hy⟩ := PS_dvd_of_map _ h0
    apply hbase κ
    refine ⟨y, ?_⟩
    rw [(hg 1 le_rfl).2.1, hy, pow_one, smul_smul, ← pow_two]
  have hall : ∀ b, 1 ≤ b → PowerSeries.map (PadicInt.toZMod (p := ℓ)) (g b) ≠ 0 := by
    intro b hb
    induction b, hb using Nat.le_induction with
    | base => exact hbase'
    | succ b hb ih => exact hstep b hb ih
  intro b hb c ⟨z, hz⟩
  have he := (hg b hb).2.1
  -- `(κ - c) L(b) = ℓ^b (ℓ z - g_b)`
  have hdiff : (κ - c) • Ll ℓ b = (ℓ : ℤ_[ℓ]) ^ b • ((ℓ : ℤ_[ℓ]) • z - g b) := by
    rw [smul_sub, ← he, smul_smul, ← pow_succ, ← hz, sub_smul]
    abel
  have hu : IsUnit (coeff 1 (Ll ℓ b)) := by
    apply isUnit_of_toZMod
    have := unit_coeff f hf1 hrank b hb
    rwa [coeff_map] at this
  obtain ⟨u, hu⟩ := hu
  set t : ℤ_[ℓ] := coeff 1 ((ℓ : ℤ_[ℓ]) • z - g b) * ↑u⁻¹
  have hkt : κ - c = (ℓ : ℤ_[ℓ]) ^ b * t := by
    have h1 := congrArg (coeff 1) hdiff
    simp only [coeff_smul, smul_eq_mul] at h1
    rw [← hu] at h1
    calc κ - c = (κ - c) * ↑u * ↑u⁻¹ := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, mul_assoc]
  have hgb : g b = (ℓ : ℤ_[ℓ]) • z - t • Ll ℓ b := by
    have h2 : (ℓ : ℤ_[ℓ]) ^ b • (t • Ll ℓ b - ((ℓ : ℤ_[ℓ]) • z - g b)) = 0 := by
      rw [smul_sub, smul_smul, ← hkt, hdiff, sub_self]
    have := sub_eq_zero.mp (cancel_pow (ℓ : ℤ_[ℓ]) PS_reg b _ h2)
    rw [this]; abel
  have hred : ∀ F : PS ℓ, PowerSeries.map (PadicInt.toZMod (p := ℓ)) ((ℓ : ℤ_[ℓ]) • F) = 0 := by
    intro F
    rw [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, map_natCast, ZMod.natCast_self,
      map_zero, zero_mul]
  have hT := (hg b hb).2.2
  rw [hgb, map_sub, map_smul, map_smul, ← Ll_succ] at hT
  have h3 := congrArg (fun F => coeff 1 (PowerSeries.map (PadicInt.toZMod (p := ℓ)) F)) hT
  simp only [map_sub, hred, zero_sub, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C,
    map_neg, coeff_C_mul] at h3
  have hz1 := unit_coeff f hf1 hrank (b + 1) (by omega)
  have ht0 : PadicInt.toZMod t = 0 := by
    have hl0 : PadicInt.toZMod (ℓ : ℤ_[ℓ]) = 0 := by rw [map_natCast, ZMod.natCast_self]
    rw [hl0, zero_mul, zero_mul, zero_sub, neg_eq_zero] at h3
    exact (mul_eq_zero.mp h3).resolve_right hz1
  apply hall b hb
  rw [hgb, map_sub, hred, zero_sub, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C,
    ht0, map_zero, zero_mul, neg_zero]

end RamanujanTau.FiniteArithmetic.ExactAtkin
