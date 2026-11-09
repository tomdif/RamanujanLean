/-
# Son's Entry 1.1(iv)/(v), first symmetric function, via a quaternion lattice

Write the 7-dissection components of `φ(q) = Σ_{k∈ℤ} q^{k²}` (variable `q`, i.e. Rebák's `q^{1/7}`) as

  `a = Σ_{k≡0} q^{k²} = φ(q⁴⁹)`, `b = Σ_{k≡1} = q f(q³⁵,q⁶³)`, `c = Σ_{k≡2} = q⁴ f(q²¹,q⁷⁷)`,
  `d = Σ_{k≡3} = q⁹ f(q⁷,q⁹¹)`  (classes mod 7, `k ≡ ±j` give the same series),

so that `u = 2b/a`, `v = 2c/a`, `w = 2d/a`, and let `Φ = φ(q⁷)`. Then

  **`Φ⁴ = a⁴ + 24abcd + 8(b³c + c³d + d³b)`**   (`quaternion_identity`).

Dividing by `a⁴`, this is `u³v + v³w + w³u = 2φ⁴(q⁷)/φ⁴(q⁴⁹) − 6uvw − 2`, i.e. the coefficient of `ξ²` in
Ramanujan's cubic `r(ξ)` of Entry 1.1(v) once one notes that the roots of `r` are `u³v, v³w, w³u`
(see `docs/SEPTIC_PAGE206.md`).

**Proof.** Left multiplication by the Lipschitz quaternion `g = 2 + i + j + k` (norm 7) is the integer matrix
`M` with `MᵀM = 7I`, so `n ↦ Mn` is a bijection of `ℤ⁴` onto the lattice `L = {k : Mᵀk ≡ 0 (mod 7)}`, with
`|Mn|² = 7|n|²`. Hence `Φ⁴ = Σ_{n∈ℤ⁴} q^{7|n|²} = Σ_{k∈L} q^{|k|²}`. Modulo 7, `L` is the isotropic plane
`k₂ ≡ 3k₀ + 2k₁, k₃ ≡ 2k₀ + 4k₁`; splitting `L` by `(k₀, k₁) mod 7` gives 49 products of four class series,
which collect to `a⁴ + 24abcd + 8(b³c + c³d + d³b)`. Pure counting; no modular forms.
-/
import RamanujanTau.Septic.Dissection

set_option autoImplicit false

namespace RamanujanTau.Septic

open PowerSeries Finset

/-! ### Theta series of a weight function -/

/-- The theta series of `f : α → ℤ`: the coefficient of `q^N` is `#{a : f a = N}`. -/
noncomputable def cnt {α : Type*} (f : α → ℤ) : PowerSeries ℤ :=
  mk fun N => (Nat.card {a // f a = (N : ℤ)} : ℤ)

/-- Nonnegative weight with finite fibres. -/
structure Good {α : Type*} (f : α → ℤ) : Prop where
  nonneg : ∀ a, 0 ≤ f a
  fin : ∀ N : ℤ, Finite {a // f a = N}

lemma coeff_cnt {α : Type*} (f : α → ℤ) (N : ℕ) :
    coeff N (cnt f) = (Nat.card {a // f a = (N : ℤ)} : ℤ) := by
  rw [cnt, coeff_mk]

lemma cnt_congr {α β : Type*} {f : α → ℤ} {g : β → ℤ} (e : α ≃ β) (h : ∀ a, g (e a) = f a) :
    cnt f = cnt g := by
  ext N
  rw [coeff_cnt, coeff_cnt]
  congr 1
  exact Nat.card_congr (e.subtypeEquiv fun a => by rw [h])

section prod

variable {α β : Type*} (f : α → ℤ) (g : β → ℤ)

/-- The fibre of the sum weight over the antidiagonal. -/
def fibreMap (hf : Good f) (hg : Good g) (N : ℕ) :
    {p : α × β // f p.1 + g p.2 = N} → antidiagonal N :=
  fun p => ⟨((f p.1.1).toNat, (g p.1.2).toNat), by
    have h1 := hf.nonneg p.1.1; have h2 := hg.nonneg p.1.2; have h3 := p.2
    rw [mem_antidiagonal]; omega⟩

def fibreEquiv (hf : Good f) (hg : Good g) (N : ℕ) (y : antidiagonal N) :
    {p : {p : α × β // f p.1 + g p.2 = N} // fibreMap f g hf hg N p = y}
      ≃ {a // f a = (y.1.1 : ℤ)} × {b // g b = (y.1.2 : ℤ)} where
  toFun p := (⟨p.1.1.1, by
      have h1 := hf.nonneg p.1.1.1
      have := congrArg (fun z : antidiagonal N => z.1.1) p.2
      simp only [fibreMap] at this; omega⟩,
    ⟨p.1.1.2, by
      have h1 := hg.nonneg p.1.1.2
      have := congrArg (fun z : antidiagonal N => z.1.2) p.2
      simp only [fibreMap] at this; omega⟩)
  invFun ab := ⟨⟨(ab.1.1, ab.2.1), by
      have := y.2; rw [mem_antidiagonal] at this
      simp only [ab.1.2, ab.2.2]; omega⟩, by
      apply Subtype.ext; simp only [fibreMap, ab.1.2, ab.2.2, Int.toNat_natCast]⟩
  left_inv p := by rfl
  right_inv ab := by rfl

lemma finite_fibre (hf : Good f) (hg : Good g) (N : ℕ) :
    Finite {p : α × β // f p.1 + g p.2 = N} := by
  haveI : ∀ y : antidiagonal N,
      Finite {p : {p : α × β // f p.1 + g p.2 = N} // fibreMap f g hf hg N p = y} := fun y => by
    haveI := hf.fin (y.1.1 : ℤ); haveI := hg.fin (y.1.2 : ℤ)
    exact Finite.of_equiv _ (fibreEquiv f g hf hg N y).symm
  exact Finite.of_equiv _ (Equiv.sigmaFiberEquiv (fibreMap f g hf hg N))

lemma good_prod (hf : Good f) (hg : Good g) : Good (fun p : α × β => f p.1 + g p.2) where
  nonneg p := add_nonneg (hf.nonneg _) (hg.nonneg _)
  fin N := by
    rcases lt_or_ge N 0 with h | h
    · haveI : IsEmpty {p : α × β // f p.1 + g p.2 = N} := ⟨fun p => by
        have := hf.nonneg p.1.1; have := hg.nonneg p.1.2; have := p.2; omega⟩
      infer_instance
    · obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le h
      exact finite_fibre f g hf hg M

theorem cnt_mul (hf : Good f) (hg : Good g) :
    cnt f * cnt g = cnt (fun p : α × β => f p.1 + g p.2) := by
  ext N
  rw [coeff_mul, coeff_cnt]
  haveI : ∀ y : antidiagonal N,
      Finite {p : {p : α × β // f p.1 + g p.2 = N} // fibreMap f g hf hg N p = y} := fun y => by
    haveI := hf.fin (y.1.1 : ℤ); haveI := hg.fin (y.1.2 : ℤ)
    exact Finite.of_equiv _ (fibreEquiv f g hf hg N y).symm
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (fibreMap f g hf hg N)), Nat.card_sigma]
  push_cast
  rw [← Finset.sum_coe_sort (antidiagonal N)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Nat.card_congr (fibreEquiv f g hf hg N y), Nat.card_prod, coeff_cnt, coeff_cnt]
  push_cast; rfl

end prod

/-- Splitting over a finite first factor. -/
theorem cnt_fin_prod {ι β : Type*} [Fintype ι] (f : ι → β → ℤ) (hf : ∀ i, Good (f i)) :
    cnt (fun p : ι × β => f p.1 p.2) = ∑ i, cnt (f i) := by
  ext N
  rw [coeff_cnt, map_sum]
  haveI : ∀ i, Finite {b // f i b = (N : ℤ)} := fun i => (hf i).fin _
  have e : {p : ι × β // f p.1 p.2 = (N : ℤ)} ≃ Σ i, {b // f i b = (N : ℤ)} :=
    { toFun := fun p => ⟨p.1.1, p.1.2, p.2⟩
      invFun := fun s => ⟨(s.1, s.2.1), s.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  push_cast
  exact Finset.sum_congr rfl fun i _ => (coeff_cnt _ _).symm

/-! ### The class series `T r = Σ_{n∈ℤ} q^{(7n+r)²}` -/

/-- `T r = Σ_{n∈ℤ} q^{(7n+r)²}`. -/
noncomputable def T (r : ℤ) : PowerSeries ℤ := cnt fun n : ℤ => (7 * n + r) ^ 2

lemma good_T (r : ℤ) : Good fun n : ℤ => (7 * n + r) ^ 2 :=
  ⟨fun _ => sq_nonneg _, fun N => finite_class N r⟩

lemma T_neg (r : ℤ) : T (-r) = T r := by
  ext N; rw [T, T, coeff_cnt, coeff_cnt]
  exact_mod_cast (cls_neg (N : ℤ) r).symm

lemma T_add_seven (r : ℤ) : T (r + 7) = T r := by
  ext N; rw [T, T, coeff_cnt, coeff_cnt]
  exact_mod_cast cls_shift (N : ℤ) r

/-- `q^j f(q^α, q^β) = T r` whenever the exponents match. -/
lemma Xpow_ramF_eq_T {α β j : ℕ} (hα : 1 ≤ α) (hβ : 1 ≤ β) (r : ℤ)
    (h : ∀ n : ℤ, ex2 α β n + 2 * (j : ℤ) = 2 * (7 * n + r) ^ 2) :
    X ^ j * ramF α β = T r := by
  ext N
  rw [coeff_X_pow_mul_ramF hα hβ, T, coeff_cnt]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun n => by rw [h n]; omega)

/-- `a = φ(q⁴⁹)`. -/
lemma T0_eq : T 0 = ramF 49 49 := by
  rw [← Xpow_ramF_eq_T (α := 49) (β := 49) (j := 0) (by norm_num) (by norm_num) 0 (fun n => by simp [ex2]; ring),
    pow_zero, one_mul]

lemma T1_eq : T 1 = X * ramF 35 63 := by
  rw [← T_neg, ← Xpow_ramF_eq_T (α := 35) (β := 63) (j := 1) (by norm_num) (by norm_num) (-1)
    (fun n => by simp [ex2]; ring), pow_one]

lemma T2_eq : T 2 = X ^ 4 * ramF 21 77 := by
  rw [← T_neg, ← Xpow_ramF_eq_T (α := 21) (β := 77) (j := 4) (by norm_num) (by norm_num) (-2)
    (fun n => by simp [ex2]; ring)]

lemma T3_eq : T 3 = X ^ 9 * ramF 7 91 := by
  rw [← T_neg, ← Xpow_ramF_eq_T (α := 7) (β := 91) (j := 9) (by norm_num) (by norm_num) (-3)
    (fun n => by simp [ex2]; ring)]

lemma T4 : T 4 = T 3 := by rw [show (4 : ℤ) = -3 + 7 by norm_num, T_add_seven, T_neg]
lemma T5 : T 5 = T 2 := by rw [show (5 : ℤ) = -2 + 7 by norm_num, T_add_seven, T_neg]
lemma T6 : T 6 = T 1 := by rw [show (6 : ℤ) = -1 + 7 by norm_num, T_add_seven, T_neg]

/-- `φ(q⁷) = Σ_n q^{7n²}`. -/
lemma ramF77_eq : ramF 7 7 = cnt fun n : ℤ => 7 * n ^ 2 := by
  ext N
  rw [coeff_ramF (by norm_num) (by norm_num), coeff_cnt]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun n => by
    have : ex2 7 7 n = 2 * (7 * n ^ 2) := by simp [ex2]; ring
    rw [this]; omega)

lemma good_seven_sq : Good fun n : ℤ => 7 * n ^ 2 :=
  ⟨fun n => by positivity, fun N => by
    haveI := finite_sq (7 * N)
    exact Finite.of_injective (fun n : {n : ℤ // 7 * n ^ 2 = N} => (⟨7 * n.1, by
        have h := n.2; linear_combination 7 * h⟩ : {k : ℤ // k ^ 2 = 7 * N}))
      (fun x y h => Subtype.ext (by have := congrArg Subtype.val h; simp at this; omega))⟩

/-! ### The quaternion bijection -/

/-- `ℤ⁴`, nested as the product weights come out of `cnt_mul`. -/
abbrev Z4 := ((ℤ × ℤ) × ℤ) × ℤ

/-- residues of the isotropic plane `L mod 7`: `(s, t, 3s+2t, 2s+4t)`. -/
def r2 (s t : ℤ) : ℤ := (3 * s + 2 * t) % 7
def r3 (s t : ℤ) : ℤ := (2 * s + 4 * t) % 7

/-- weight of `(s,t; m)`: `Σ (7mᵢ + rᵢ)²`. -/
def G (st : Fin 7 × Fin 7) (m : Z4) : ℤ :=
  (((7 * m.1.1.1 + (st.1 : ℕ)) ^ 2 + (7 * m.1.1.2 + (st.2 : ℕ)) ^ 2)
    + (7 * m.1.2 + r2 (st.1 : ℕ) (st.2 : ℕ)) ^ 2) + (7 * m.2 + r3 (st.1 : ℕ) (st.2 : ℕ)) ^ 2

/-- weight `7|n|²` on `ℤ⁴`. -/
def W4 (n : Z4) : ℤ := ((7 * n.1.1.1 ^ 2 + 7 * n.1.1.2 ^ 2) + 7 * n.1.2 ^ 2) + 7 * n.2 ^ 2

/-- Left multiplication by `2 + i + j + k`. -/
def Mk0 (n : Z4) : ℤ := 2 * n.1.1.1 - n.1.1.2 - n.1.2 - n.2
def Mk1 (n : Z4) : ℤ := n.1.1.1 + 2 * n.1.1.2 - n.1.2 + n.2
def Mk2 (n : Z4) : ℤ := n.1.1.1 + n.1.1.2 + 2 * n.1.2 - n.2
def Mk3 (n : Z4) : ℤ := n.1.1.1 - n.1.1.2 + n.1.2 + 2 * n.2

lemma toNat_emod7 (x : ℤ) : (((x % 7).toNat : ℕ) : ℤ) = x % 7 :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))

/-- `n ↦ ((Mn mod 7 on the first two coordinates), (Mn − r)/7)`. -/
def quatEquiv : Z4 ≃ (Fin 7 × Fin 7) × Z4 where
  toFun n :=
    ((⟨(Mk0 n % 7).toNat, by omega⟩, ⟨(Mk1 n % 7).toNat, by omega⟩),
      (((Mk0 n / 7, Mk1 n / 7), (Mk2 n - r2 (Mk0 n % 7) (Mk1 n % 7)) / 7),
        (Mk3 n - r3 (Mk0 n % 7) (Mk1 n % 7)) / 7))
  invFun p :=
    let k0 := 7 * p.2.1.1.1 + ((p.1.1 : ℕ) : ℤ)
    let k1 := 7 * p.2.1.1.2 + ((p.1.2 : ℕ) : ℤ)
    let k2 := 7 * p.2.1.2 + r2 (p.1.1 : ℕ) (p.1.2 : ℕ)
    let k3 := 7 * p.2.2 + r3 (p.1.1 : ℕ) (p.1.2 : ℕ)
    ((((2 * k0 + k1 + k2 + k3) / 7, (-k0 + 2 * k1 + k2 - k3) / 7),
      (-k0 - k1 + 2 * k2 + k3) / 7), (-k0 + k1 - k2 + 2 * k3) / 7)
  left_inv n := by
    obtain ⟨⟨⟨n0, n1⟩, n2⟩, n3⟩ := n
    simp only [Mk0, Mk1, Mk2, Mk3, r2, r3, toNat_emod7]
    ext <;> simp only <;> omega
  right_inv p := by
    obtain ⟨⟨⟨s, hs⟩, ⟨t, ht⟩⟩, ⟨⟨m0, m1⟩, m2⟩, m3⟩ := p
    simp only [Mk0, Mk1, Mk2, Mk3, r2, r3]
    ext <;> simp only <;> omega

lemma G_quatEquiv (n : Z4) : G (quatEquiv n).1 (quatEquiv n).2 = W4 n := by
  obtain ⟨⟨⟨n0, n1⟩, n2⟩, n3⟩ := n
  simp only [G, W4, quatEquiv, Equiv.coe_fn_mk, Mk0, Mk1, Mk2, Mk3, r2, r3]
  have h0 : 7 * ((2 * n0 - n1 - n2 - n3) / 7) + (((2 * n0 - n1 - n2 - n3) % 7).toNat : ℤ)
      = 2 * n0 - n1 - n2 - n3 := by omega
  have h1 : 7 * ((n0 + 2 * n1 - n2 + n3) / 7) + (((n0 + 2 * n1 - n2 + n3) % 7).toNat : ℤ)
      = n0 + 2 * n1 - n2 + n3 := by omega
  have h2 : 7 * ((n0 + n1 + 2 * n2 - n3 - (3 * ((2 * n0 - n1 - n2 - n3) % 7)
      + 2 * ((n0 + 2 * n1 - n2 + n3) % 7)) % 7) / 7)
      + (3 * ((((2 * n0 - n1 - n2 - n3) % 7).toNat : ℕ) : ℤ)
      + 2 * ((((n0 + 2 * n1 - n2 + n3) % 7).toNat : ℕ) : ℤ)) % 7 = n0 + n1 + 2 * n2 - n3 := by omega
  have h3 : 7 * ((n0 - n1 + n2 + 2 * n3 - (2 * ((2 * n0 - n1 - n2 - n3) % 7)
      + 4 * ((n0 + 2 * n1 - n2 + n3) % 7)) % 7) / 7)
      + (2 * ((((2 * n0 - n1 - n2 - n3) % 7).toNat : ℕ) : ℤ)
      + 4 * ((((n0 + 2 * n1 - n2 + n3) % 7).toNat : ℕ) : ℤ)) % 7 = n0 - n1 + n2 + 2 * n3 := by omega
  rw [h0, h1, h2, h3]; ring

lemma good_W4 : Good W4 := by
  have h := good_prod _ _ (good_prod _ _ (good_prod _ _ good_seven_sq good_seven_sq) good_seven_sq)
    good_seven_sq
  exact h

lemma good_G (st : Fin 7 × Fin 7) : Good (G st) :=
  good_prod _ _ (good_prod _ _ (good_prod _ _ (good_T _) (good_T _)) (good_T _)) (good_T _)

lemma cnt_G (st : Fin 7 × Fin 7) :
    cnt (G st) = T ((st.1 : ℕ) : ℤ) * T ((st.2 : ℕ) : ℤ) * T (r2 (st.1 : ℕ) (st.2 : ℕ))
      * T (r3 (st.1 : ℕ) (st.2 : ℕ)) := by
  rw [T, T, T, T, cnt_mul _ _ (good_T _) (good_T _),
    cnt_mul _ _ (good_prod _ _ (good_T _) (good_T _)) (good_T _),
    cnt_mul _ _ (good_prod _ _ (good_prod _ _ (good_T _) (good_T _)) (good_T _)) (good_T _)]
  rfl

lemma Phi4_cnt : ramF 7 7 ^ 4 = cnt W4 := by
  rw [ramF77_eq, pow_succ, pow_succ, pow_succ, pow_one,
    cnt_mul _ _ good_seven_sq good_seven_sq,
    cnt_mul _ _ (good_prod _ _ good_seven_sq good_seven_sq) good_seven_sq,
    cnt_mul _ _ (good_prod _ _ (good_prod _ _ good_seven_sq good_seven_sq) good_seven_sq)
      good_seven_sq]
  rfl

/-- **The quaternion identity** `φ(q⁷)⁴ = a⁴ + 24abcd + 8(b³c + c³d + d³b)` with `a,b,c,d = T 0..3`. -/
theorem quaternion_identity_T :
    ramF 7 7 ^ 4 = T 0 ^ 4 + 24 * T 0 * T 1 * T 2 * T 3
      + 8 * (T 1 ^ 3 * T 2 + T 2 ^ 3 * T 3 + T 3 ^ 3 * T 1) := by
  have e1 : cnt W4 = cnt (fun p : (Fin 7 × Fin 7) × Z4 => G p.1 p.2) :=
    cnt_congr quatEquiv G_quatEquiv
  have e2 : cnt (fun p : (Fin 7 × Fin 7) × Z4 => G p.1 p.2) = ∑ st, cnt (G st) :=
    cnt_fin_prod G good_G
  rw [Phi4_cnt, e1, e2]
  simp only [cnt_G, Fintype.sum_prod_type]
  rw [Fin.sum_univ_eq_sum_range (fun s => ∑ t : Fin 7, T (s : ℤ) * T ((t : ℕ) : ℤ)
    * T (r2 s (t : ℕ)) * T (r3 s (t : ℕ))) 7]
  simp only [fun s : ℕ => Fin.sum_univ_eq_sum_range (fun t => T (s : ℤ) * T (t : ℤ)
    * T (r2 s t) * T (r3 s t)) 7]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, r2, r3]
  norm_num [T4, T5, T6]
  ring

/-- **The quaternion identity**, in Ramanujan's notation:
`φ(q⁷)⁴ = φ(q⁴⁹)⁴ + 24 φ(q⁴⁹) B C D + 8(B³C + C³D + D³B)` with
`B = q f(q³⁵,q⁶³)`, `C = q⁴ f(q²¹,q⁷⁷)`, `D = q⁹ f(q⁷,q⁹¹)`. -/
theorem quaternion_identity :
    ramF 7 7 ^ 4 = ramF 49 49 ^ 4
      + 24 * ramF 49 49 * (X * ramF 35 63) * (X ^ 4 * ramF 21 77) * (X ^ 9 * ramF 7 91)
      + 8 * ((X * ramF 35 63) ^ 3 * (X ^ 4 * ramF 21 77) + (X ^ 4 * ramF 21 77) ^ 3 * (X ^ 9 * ramF 7 91)
        + (X ^ 9 * ramF 7 91) ^ 3 * (X * ramF 35 63)) := by
  rw [quaternion_identity_T, T0_eq, T1_eq, T2_eq, T3_eq]

end RamanujanTau.Septic
