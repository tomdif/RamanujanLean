/-
# Stepanov's method, part 3: the Hasse–Weil-type bound for `y² = f(x)` over `𝔽_p`

Headlines (all axiom-clean):
* `stepanov_card_le_real`: `#{x : f(x)^{(p-1)/2} = ε} ≤ p/2 + 2 m √m √p` for `p ≥ 144 m²`, `ε ≠ 0`;
* `stepanov_charSum_le`: `|∑ χ(f(x))| ≤ 4 m √m √p + m` for `p ≥ 144 m²`;
* `hasseWeil_charSum_le`: `|∑ χ(f(x))| ≤ 12 m² √p` for **every** odd prime `p`;
* `hasseWeil_pointCount`: `|#{(x,y) : y² = f(x)} - p| ≤ 12 m² √p`;
* `hasse_elliptic`: for squarefree cubics, `|#{y² = f(x)} - p| ≤ 108 √p` (Hasse up to the constant).
Here `f` is not a constant times a square (e.g. squarefree and nonconstant), `m = deg f`.
-/
import RamanujanTau.Stepanov.Aux

set_option autoImplicit false

namespace RamanujanTau.Stepanov

open Polynomial Finset

variable {p : ℕ} [hp : Fact p.Prime]

local notation "F" => ZMod p

omit hp in
/-- Choice of `J = j + 1 ≈ √p / (4√m)`. -/
theorem exists_param (m : ℕ) (hm : 1 ≤ m) (hpm : 144 * m ^ 2 ≤ p) :
    ∃ j : ℕ, 16 * m * (j + 1) ^ 2 ≤ p ∧ 2 ≤ j ∧
      Real.sqrt p ≤ 4 * Real.sqrt m * (2 * j + 1) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  set x := Real.sqrt p / (4 * Real.sqrt m)
  have hx0 : 0 ≤ x := by positivity
  have hx3 : (3 : ℝ) ≤ x := by
    rw [le_div_iff₀ (by positivity)]
    have : Real.sqrt (144 * m) ≤ Real.sqrt p := by
      apply Real.sqrt_le_sqrt
      have : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith [show (1 : ℝ) ≤ m by exact_mod_cast hm]
      have h' : (144 * m ^ 2 : ℝ) ≤ p := by exact_mod_cast hpm
      nlinarith
    rw [Real.sqrt_mul (by norm_num), show Real.sqrt 144 = 12 by
      rw [show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
    linarith
  set J := ⌊x⌋₊
  have hJx : (J : ℝ) ≤ x := Nat.floor_le hx0
  have hxJ : x < J + 1 := Nat.lt_floor_add_one x
  have hJ3 : 3 ≤ J := Nat.le_floor (by exact_mod_cast hx3)
  refine ⟨J - 1, ?_, by omega, ?_⟩
  · have hJ' : J - 1 + 1 = J := by omega
    rw [hJ']
    have h1 : 4 * Real.sqrt m * J ≤ Real.sqrt p := by
      have := (le_div_iff₀ (by positivity : (0:ℝ) < 4 * Real.sqrt m)).mp hJx; linarith
    have h2 : (4 * Real.sqrt m * J) ^ 2 ≤ (Real.sqrt p) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [mul_pow, mul_pow, Real.sq_sqrt hm0.le, Real.sq_sqrt (Nat.cast_nonneg _)] at h2
    have : ((16 * m * J ^ 2 : ℕ) : ℝ) ≤ p := by push_cast; nlinarith
    exact_mod_cast this
  · have h1 : Real.sqrt p < 4 * Real.sqrt m * (J + 1) := by
      have := (div_lt_iff₀ (by positivity : (0:ℝ) < 4 * Real.sqrt m)).mp hxJ; linarith
    have hJ' : ((J - 1 : ℕ) : ℝ) = J - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hJ']
    have : (J : ℝ) + 1 ≤ 2 * (J - 1) + 1 := by
      have : (3 : ℝ) ≤ J := by exact_mod_cast hJ3
      linarith
    nlinarith

theorem notConstSq_natDegree_pos {f : F[X]} (hf : NotConstSq f) (hf0 : f ≠ 0) :
    1 ≤ f.natDegree := by
  by_contra h
  push Not at h
  have hc : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
  have ha : f.coeff 0 ≠ 0 := by
    intro h0; rw [h0, C_0] at hc; exact hf0 hc
  have := hf (f.coeff 0) 1 1 ha (by rw [hc]; simp)
  exact one_ne_zero this

/-- **One-sided Stepanov bound** (real form). -/
theorem stepanov_card_le_real (hp2 : p ≠ 2) (f : F[X]) (hf : NotConstSq f) (hf0 : f ≠ 0)
    (ε : F) (hε : ε ≠ 0) (hpm : 144 * f.natDegree ^ 2 ≤ p) :
    (#(univ.filter (fun x : F => (f.eval x) ^ ((p - 1) / 2) = ε)) : ℝ) ≤
      p / 2 + 2 * f.natDegree * Real.sqrt f.natDegree * Real.sqrt p := by
  have hm : 1 ≤ f.natDegree := notConstSq_natDegree_pos hf hf0
  set m := f.natDegree with hmdef
  set N := #(univ.filter (fun x : F => (f.eval x) ^ ((p - 1) / 2) = ε))
  obtain ⟨j, hj16, hj2, hjs⟩ := exists_param m hm hpm
  have hpodd : 2 * ((p - 1) / 2) + 1 = p := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · have := hp.out.two_le; omega
  set c := (p - 1) / 2
  have hm2 : m ≤ m ^ 2 := by nlinarith
  -- the combinatorial hypotheses
  have hbig : 6 * m * (j + 1) ^ 2 + m + 2 ≤ c := by
    have : 16 * m ≤ p := by nlinarith
    nlinarith
  have hdim' : (2 * j + 1) * ((c - m + 1) + (j + 1) + (2 * j + 1) * m) <
      2 * (j + 1) * (c - m + 1) := by
    have hA : m + 1 ≤ c := by nlinarith
    obtain ⟨a, ha⟩ : ∃ a, c - m + 1 = a := ⟨_, rfl⟩
    have ha' : c = a + m - 1 := by omega
    rw [ha]
    have : (2 * j + 1) * (j + 1 + (2 * j + 1) * m) < a := by
      have h1 : (2 * j + 1) * (j + 1 + (2 * j + 1) * m) ≤ 6 * m * (j + 1) ^ 2 := by
        nlinarith
      omega
    nlinarith
  have hjj : 2 * j + 1 ≤ 6 * m * (j + 1) ^ 2 := by nlinarith
  have key := stepanov_card_le hp2 f hf hf0 hm ε hε (A := c - m + 1) (J := j + 1)
    (ℓ := 2 * j + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by
      calc (2 * j + 1) * (c - m + 1 + (j + 1) - 1 + (2 * j + 1 - 1) * (m - 1))
          ≤ (2 * j + 1) * ((c - m + 1) + (j + 1) + (2 * j + 1) * m) := by
            apply Nat.mul_le_mul_left
            have : (2 * j + 1 - 1) * (m - 1) ≤ (2 * j + 1) * m :=
              Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
            omega
        _ < 2 * (j + 1) * (c - m + 1) := hdim')
  -- convert to reals
  have hkey2 : 2 * ((2 * j + 1) * N) ≤ p * (2 * j + 1 + m) := by
    have h3 : 2 * (c - m + 1 - 1 + c * m + p * (j + 1 - 1)) ≤ p * (2 * j + 1 + m) := by
      have : c - m + 1 - 1 = c - m := by omega
      rw [this, Nat.add_sub_cancel]
      have h4 : 2 * (c * m) ≤ p * m := by nlinarith
      have h5 : 2 * (c - m) ≤ p := by omega
      nlinarith
    exact (Nat.mul_le_mul_left 2 key).trans h3
  have hkR : 2 * ((2 * j + 1 : ℝ) * N) ≤ p * (2 * j + 1 + m) := by exact_mod_cast hkey2
  have hpos : (0 : ℝ) < 2 * j + 1 := by positivity
  have hN : (N : ℝ) ≤ p / 2 + p * m / (2 * (2 * j + 1)) := by
    rw [div_add_div _ _ (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
    nlinarith
  have hsp : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have : p * m / (2 * (2 * j + 1)) ≤ 2 * m * Real.sqrt m * Real.sqrt p := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (p : ℝ) * m ≤ m * (Real.sqrt p * (4 * Real.sqrt m * (2 * j + 1))) := by
      have := mul_le_mul_of_nonneg_left hjs (Real.sqrt_nonneg (p : ℝ))
      have h2 : (p : ℝ) ≤ Real.sqrt p * (4 * Real.sqrt m * (2 * j + 1)) := by
        calc (p : ℝ) = Real.sqrt p * Real.sqrt p := hsp.symm
          _ ≤ _ := this
      nlinarith
    nlinarith
  linarith

/-- Partition of `𝔽_p` according to `f(x)^{(p-1)/2} ∈ {0, 1, -1}` and the character sum. -/
theorem charSum_eq (hp2 : p ≠ 2) (f : F[X]) :
    (∑ x : F, (quadraticChar F (f.eval x) : ℤ)) =
      #(univ.filter (fun x : F => (f.eval x) ^ ((p - 1) / 2) = 1)) -
      #(univ.filter (fun x : F => (f.eval x) ^ ((p - 1) / 2) = -1)) ∧
    (p : ℤ) = #(univ.filter (fun x : F => f.eval x = 0)) +
      #(univ.filter (fun x : F => (f.eval x) ^ ((p - 1) / 2) = 1)) +
      #(univ.filter (fun x : F => (f.eval x) ^ ((p - 1) / 2) = -1)) := by
  have hF : ringChar F ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hcard : Fintype.card F / 2 = (p - 1) / 2 := by
    rw [ZMod.card]
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have h1ne : (1 : F) ≠ -1 := by
    intro h; exact Ring.neg_one_ne_one_of_char_ne_two hF h.symm
  have hpt : ∀ x : F, (quadraticChar F (f.eval x) : ℤ) =
      (if (f.eval x) ^ ((p - 1) / 2) = 1 then 1 else 0) -
      (if (f.eval x) ^ ((p - 1) / 2) = -1 then 1 else 0) ∧
      (1 : ℤ) = (if f.eval x = 0 then 1 else 0) +
      (if (f.eval x) ^ ((p - 1) / 2) = 1 then 1 else 0) +
      (if (f.eval x) ^ ((p - 1) / 2) = -1 then 1 else 0) := by
    intro x
    have he := quadraticChar_eq_pow_of_char_ne_two' hF (f.eval x)
    rw [hcard] at he
    by_cases h0 : f.eval x = 0
    · have hc0 : 0 < (p - 1) / 2 := by have := hp.out.two_le; rcases hp.out.eq_two_or_odd with h | h <;> omega
      simp [h0, zero_pow hc0.ne']
    · rcases quadraticChar_dichotomy h0 with h | h
      · rw [h] at he ⊢; simp at he; rw [← he]; simp [h1ne, h0]
      · rw [h] at he ⊢; simp at he; rw [← he]; simp [h1ne.symm, h0]
  constructor
  · rw [Finset.sum_congr rfl (fun x _ => (hpt x).1), Finset.sum_sub_distrib]
    simp [Finset.sum_boole]
  · have := Finset.sum_congr rfl (fun x (_ : x ∈ (univ : Finset F)) => (hpt x).2)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one,
      Finset.sum_boole] at this
    exact_mod_cast this

/-- **Two-sided Stepanov bound** for the quadratic-character sum, `p ≥ 144 m²`. -/
theorem stepanov_charSum_le (hp2 : p ≠ 2) (f : F[X]) (hf : NotConstSq f) (hf0 : f ≠ 0)
    (hpm : 144 * f.natDegree ^ 2 ≤ p) :
    |(∑ x : F, (quadraticChar F (f.eval x) : ℤ) : ℝ)| ≤
      4 * f.natDegree * Real.sqrt f.natDegree * Real.sqrt p + f.natDegree := by
  obtain ⟨hsum, hpart⟩ := charSum_eq hp2 f
  have hP := stepanov_card_le_real hp2 f hf hf0 1 one_ne_zero hpm
  have hM := stepanov_card_le_real hp2 f hf hf0 (-1) (neg_ne_zero.mpr one_ne_zero) hpm
  have h0 : #(univ.filter (fun x : F => f.eval x = 0)) ≤ f.natDegree := by
    have := card_nonroots_ge f hf0
    have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset F))
      (fun y => f.eval y = 0)
    rw [Finset.card_univ, ZMod.card] at h1
    have h3 : #(univ.filter (fun y : F => f.eval y ≠ 0)) =
      #(univ.filter (fun y : F => ¬ f.eval y = 0)) := rfl
    omega
  have hsumR : (∑ x : F, (quadraticChar F (f.eval x) : ℤ) : ℝ) =
      (#(univ.filter (fun x : F => (f.eval x) ^ ((p - 1) / 2) = 1)) : ℝ) -
      #(univ.filter (fun x : F => (f.eval x) ^ ((p - 1) / 2) = -1)) := by
    exact_mod_cast hsum
  have hpartR : (p : ℝ) = #(univ.filter (fun x : F => f.eval x = 0)) +
      #(univ.filter (fun x : F => (f.eval x) ^ ((p - 1) / 2) = 1)) +
      #(univ.filter (fun x : F => (f.eval x) ^ ((p - 1) / 2) = -1)) := by
    exact_mod_cast hpart
  have h0R : (#(univ.filter (fun x : F => f.eval x = 0)) : ℝ) ≤ f.natDegree := by
    exact_mod_cast h0
  rw [hsumR, abs_le]
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (#(univ.filter (fun x : F => f.eval x = 0)))]

/-- **Hasse–Weil-type bound, all odd primes**: `|∑_x χ(f(x))| ≤ 12 m² √p`. -/
theorem hasseWeil_charSum_le_of_notConstSq (hp2 : p ≠ 2) (f : F[X]) (hf : NotConstSq f)
    (hf0 : f ≠ 0) :
    |(∑ x : F, (quadraticChar F (f.eval x) : ℤ) : ℝ)| ≤
      12 * (f.natDegree : ℝ) ^ 2 * Real.sqrt p := by
  set m := f.natDegree
  have hm := notConstSq_natDegree_pos hf hf0
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsp : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hp1 : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]; exact_mod_cast hp.out.one_lt.le
  by_cases hpm : 144 * m ^ 2 ≤ p
  · have h := stepanov_charSum_le hp2 f hf hf0 hpm
    have hsm : Real.sqrt m ≤ m := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    have : 4 * m * Real.sqrt m * Real.sqrt p ≤ 4 * m * m * Real.sqrt p := by
      have := Real.sqrt_nonneg (p : ℝ); gcongr
    nlinarith
  · push Not at hpm
    -- trivial bound `|∑ χ| ≤ p`
    have htriv : |(∑ x : F, (quadraticChar F (f.eval x) : ℤ) : ℝ)| ≤ p := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : ∀ x : F, |((quadraticChar F (f.eval x) : ℤ) : ℝ)| ≤ 1 := by
        intro x
        by_cases h0 : f.eval x = 0
        · simp [h0]
        · rcases quadraticChar_dichotomy h0 with h | h <;> simp [h]
      refine (Finset.sum_le_sum fun x _ => this x).trans ?_
      simp
    have hpR : (p : ℝ) < 144 * m ^ 2 := by exact_mod_cast hpm
    have hsq : Real.sqrt p < 12 * m := by
      rw [Real.sqrt_lt' (by positivity)]; nlinarith
    have hmm : (m : ℝ) ≤ m ^ 2 := by nlinarith
    have : (p : ℝ) ≤ 12 * m ^ 2 * Real.sqrt p := by
      calc (p : ℝ) = Real.sqrt p * Real.sqrt p := hsp.symm
        _ ≤ (12 * m) * Real.sqrt p := mul_le_mul_of_nonneg_right hsq.le (Real.sqrt_nonneg _)
        _ ≤ 12 * m ^ 2 * Real.sqrt p := by gcongr
    linarith

theorem hasseWeil_charSum_le (hp2 : p ≠ 2) (f : F[X]) (hsq : Squarefree f)
    (hdeg : 0 < f.natDegree) :
    |(∑ x : F, (quadraticChar F (f.eval x) : ℤ) : ℝ)| ≤
      12 * (f.natDegree : ℝ) ^ 2 * Real.sqrt p :=
  hasseWeil_charSum_le_of_notConstSq hp2 f (notConstSq_of_squarefree hsq hdeg)
    (by rintro rfl; simp at hdeg)

/-- point count on `y² = f(x)`. -/
theorem pointCount_eq (hp2 : p ≠ 2) (f : F[X]) :
    (#(univ.filter (fun xy : F × F => xy.2 ^ 2 = f.eval xy.1)) : ℤ) =
      p + ∑ x : F, (quadraticChar F (f.eval x) : ℤ) := by
  have hF : ringChar F ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  rw [Finset.card_filter, Fintype.sum_prod_type]
  push_cast
  have : ∀ x : F, (∑ y : F, if y ^ 2 = f.eval x then (1 : ℤ) else 0) =
      quadraticChar F (f.eval x) + 1 := by
    intro x
    rw [← quadraticChar_card_sqrts hF (f.eval x), Finset.sum_boole]
    congr 2
    ext y; simp
  simp only [this, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  ring

/-- **Hasse–Weil for `y² = f(x)` over `𝔽_p`**: `|#{y² = f(x)} - p| ≤ 12 m² √p`. -/
theorem hasseWeil_pointCount (hp2 : p ≠ 2) (f : F[X]) (hsq : Squarefree f)
    (hdeg : 0 < f.natDegree) :
    |((#(univ.filter (fun xy : F × F => xy.2 ^ 2 = f.eval xy.1)) : ℝ) - p)| ≤
      12 * (f.natDegree : ℝ) ^ 2 * Real.sqrt p := by
  have h := pointCount_eq hp2 f
  have h' : ((#(univ.filter (fun xy : F × F => xy.2 ^ 2 = f.eval xy.1)) : ℝ) - p) =
      ((∑ x : F, (quadraticChar F (f.eval x) : ℤ) : ℤ) : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) h; push_cast at this ⊢; linarith
  rw [h']; push_cast
  exact hasseWeil_charSum_le hp2 f hsq hdeg

/-- **Hasse's theorem up to the constant**: for a squarefree cubic `f` over `𝔽_p`, `p` odd,
`|#{(x,y) : y² = f(x)} - p| ≤ 108 √p`. -/
theorem hasse_elliptic (hp2 : p ≠ 2) (f : F[X]) (hsq : Squarefree f) (hdeg : f.natDegree = 3) :
    |((#(univ.filter (fun xy : F × F => xy.2 ^ 2 = f.eval xy.1)) : ℝ) - p)| ≤
      108 * Real.sqrt p := by
  have := hasseWeil_pointCount hp2 f hsq (by omega)
  rw [hdeg] at this; norm_num at this; linarith

end RamanujanTau.Stepanov

#print axioms RamanujanTau.Stepanov.stepanov_nonvanish
#print axioms RamanujanTau.Stepanov.stepanov_card_le
#print axioms RamanujanTau.Stepanov.stepanov_card_le_real
#print axioms RamanujanTau.Stepanov.stepanov_charSum_le
#print axioms RamanujanTau.Stepanov.hasseWeil_charSum_le
#print axioms RamanujanTau.Stepanov.hasseWeil_pointCount
#print axioms RamanujanTau.Stepanov.hasse_elliptic
