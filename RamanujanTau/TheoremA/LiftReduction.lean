import RamanujanTau.TheoremA.BWDictionary
import RamanujanTau.TheoremA.LevelLowering
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# Theorem A from modularity of the explicit Shimura lifts

For squarefree `t ≡ -ℓ (mod 24)` the Ahlgren–Andersen–Dicks lift of `h = Σ a(n) q^{n/24}` is
`Σ_n (Σ_{de=n} (d/t) d^(λ-1) (12/e) a(te²)) qⁿ`. `AADModularity` states that it is a level-six
modular form. That is Theorem 1.1 of Ahlgren–Andersen–Dicks (Adv. Math. 2024), proved there with a
theta kernel. `ThetaLift.aadModularity` proves it, in `RamanujanTau/ThetaLift/Final.lean`.

Everything else is proved, and no Hecke operator on the half-integral space, eigenvector, or
correspondence is needed. If `U_{ℓ²} h ≡ 0`, each lift is killed by `U_ℓ` modulo `ℓ` and has the
prescribed `U₂, U₃` eigenvalues, so ordinarity makes it vanish modulo `ℓ`. Möbius-style triangularity
gives `a(te²) ≡ 0`, and every index has the form `te²`, so `h ≡ 0`.
-/

set_option autoImplicit false

namespace RamanujanTau.TheoremA.HalfIntegral
open ModularForm CongruenceSubgroup UpperHalfPlane PowerSeries MockTheta5.JTP SignLattice BoylanWebb
open scoped MatrixGroups ModularForm

/-- The character `(12/·)`. -/
def chi12 (e : ℕ) : ℤ :=
  if e % 12 = 1 ∨ e % 12 = 11 then 1 else if e % 12 = 5 ∨ e % 12 = 7 then -1 else 0

lemma chi12_eq_zero_of_two {e : ℕ} (h : 2 ∣ e) : chi12 e = 0 := by
  unfold chi12
  rw [if_neg (by omega), if_neg (by omega)]

lemma chi12_eq_zero_of_three {e : ℕ} (h : 3 ∣ e) : chi12 e = 0 := by
  unfold chi12
  rw [if_neg (by omega), if_neg (by omega)]

lemma chi12_ne_zero {e : ℕ} (h2 : ¬ 2 ∣ e) (h3 : ¬ 3 ∣ e) : chi12 e = 1 ∨ chi12 e = -1 := by
  unfold chi12
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl | omega

lemma sq_mod_24 {e : ℕ} (h2 : ¬ 2 ∣ e) (h3 : ¬ 3 ∣ e) : e ^ 2 % 24 = 1 := by
  have hs : e % 24 = 1 ∨ e % 24 = 5 ∨ e % 24 = 7 ∨ e % 24 = 11 ∨ e % 24 = 13 ∨ e % 24 = 17 ∨
      e % 24 = 19 ∨ e % 24 = 23 := by omega
  rw [Nat.pow_mod]
  rcases hs with h | h | h | h | h | h | h | h <;> rw [h]

/-- The Dirichlet factor `d ↦ (d/t) d^(λ-1)`. -/
def psi (t lam d : ℕ) : ℤ := jacobiSym (d : ℤ) t * (d : ℤ) ^ (lam - 1)

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- The coefficient `a(te²)` in the coordinate `A[m] = a(24m-j)`. -/
def latIndex (ℓ t e : ℕ) : ℕ := (t * e ^ 2 + jj ℓ) / 24

/-- **The explicit Ahlgren–Andersen–Dicks lift.** -/
noncomputable def liftSeries (ℓ t : ℕ) (A : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => ∑ x ∈ n.divisorsAntidiagonal,
    psi t (halfWt ℓ) x.1 * (chi12 x.2 * A.coeff (latIndex ℓ t x.2))

lemma coeff_liftSeries (t : ℕ) (A : PowerSeries ℤ) (n : ℕ) :
    (liftSeries ℓ t A).coeff n = ∑ x ∈ n.divisorsAntidiagonal,
      psi t (halfWt ℓ) x.1 * (chi12 x.2 * A.coeff (latIndex ℓ t x.2)) :=
  PowerSeries.coeff_mk _ _

variable (ℓ) in
/-- **Modularity of the lifts** (Ahlgren–Andersen–Dicks, Theorem 1.1). See `ThetaLift.aadModularity`. -/
def AADModularity : Prop :=
  ∀ a ∈ intLattice ℓ, ∀ t : ℕ, Squarefree t → 24 ∣ t + jj ℓ →
    ∃ g : Forms ℓ, PowerSeries.map (Int.castRingHom ℂ) (liftSeries ℓ t (coordOf ℓ a)) =
      qExpansion 1 g

variable (ℓ) in
/-- The raised form of the statement, at level `6t`, where the lift has multiplier `ν`. -/
def AADRaisedModularity : Prop :=
  ∀ a ∈ intLattice ℓ, ∀ t : ℕ, Squarefree t → 24 ∣ t + jj ℓ →
    ∀ [NeZero t] [NeZero (6 * t)], ∃ g : ModularForm (Gamma0 (6 * t) : Subgroup (GL (Fin 2) ℝ))
      ((2 * halfWt ℓ : ℕ) : ℤ),
      qExpansion 1 g = PowerSeries.expand t (NeZero.ne t)
        (PowerSeries.map (Int.castRingHom ℂ) (liftSeries ℓ t (coordOf ℓ a)))

/-- Level lowering reduces the hypothesis to level `6t`. -/
theorem aadModularity_of_raised (H : AADRaisedModularity ℓ) : AADModularity ℓ := by
  intro a ha t hsf ht
  haveI : NeZero t := ⟨hsf.ne_zero⟩
  haveI : NeZero (6 * t) := ⟨mul_ne_zero (by norm_num) hsf.ne_zero⟩
  obtain ⟨g, hg⟩ := H a ha t hsf ht
  obtain ⟨f, hf⟩ := LevelLowering.exists_lowered (M := 6) (t := t) g _ hg
  exact ⟨f, hf.symm⟩

/-- Removing a prime from a Dirichlet convolution whose second factor is supported off that prime. -/
lemma convolution_prime {p : ℕ} (hp : p.Prime) (ψ c : ℕ → ℤ)
    (hψ : ∀ d, ψ (p * d) = ψ p * ψ d) (hc : ∀ e, c (p * e) = 0) (n : ℕ) :
    ∑ x ∈ (p * n).divisorsAntidiagonal, ψ x.1 * c x.2 =
      ψ p * ∑ x ∈ n.divisorsAntidiagonal, ψ x.1 * c x.2 := by
  classical
  by_cases hn : n = 0
  · subst hn
    simp
  have hpn : p * n ≠ 0 := mul_ne_zero hp.ne_zero hn
  rw [Finset.mul_sum]
  let f : ℕ × ℕ → ℕ × ℕ := fun x => (p * x.1, x.2)
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨c', d⟩ h
    simp only [f, Prod.mk.injEq] at h
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left hp.pos h.1) h.2
  have himg : ∑ x ∈ n.divisorsAntidiagonal, ψ p * (ψ x.1 * c x.2) =
      ∑ y ∈ n.divisorsAntidiagonal.image f, ψ y.1 * c y.2 := by
    rw [Finset.sum_image (fun a _ b _ h => hf h)]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [f, hψ]
    ring
  rw [himg]
  symm
  apply Finset.sum_subset
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [Nat.mem_divisorsAntidiagonal] at hx ⊢
    refine ⟨?_, hpn⟩
    simp only [f]
    rw [mul_assoc, hx.1]
  · rintro ⟨d, e⟩ hy hny
    rw [Nat.mem_divisorsAntidiagonal] at hy
    have hde : d * e = p * n := hy.1
    by_cases hd : p ∣ d
    · exfalso
      obtain ⟨d', rfl⟩ := hd
      apply hny
      refine Finset.mem_image.mpr ⟨(d', e), ?_, rfl⟩
      rw [Nat.mem_divisorsAntidiagonal]
      refine ⟨Nat.eq_of_mul_eq_mul_left hp.pos (by rw [← mul_assoc, hde]), hn⟩
    · have he : p ∣ e := (hp.dvd_mul.mp (Dvd.intro n hde.symm)).resolve_left hd
      obtain ⟨e', rfl⟩ := he
      simp [hc]

lemma psi_mul (t lam p d : ℕ) : psi t lam (p * d) = psi t lam p * psi t lam d := by
  unfold psi
  push_cast
  rw [jacobiSym.mul_left, mul_pow]
  ring

/-- `U_p` on the lift, for `p = 2, 3`. -/
lemma U_lift {p : ℕ} (hp : p = 2 ∨ p = 3) (t : ℕ) (A : PowerSeries ℤ) :
    U p (liftSeries ℓ t A) = psi t (halfWt ℓ) p • liftSeries ℓ t A := by
  have hpr : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  ext n
  rw [coeff_U, coeff_liftSeries, map_zsmul, smul_eq_mul, coeff_liftSeries]
  refine convolution_prime hpr (psi t (halfWt ℓ))
    (fun e => chi12 e * A.coeff (latIndex ℓ t e)) (psi_mul _ _ _) (fun e => ?_) n
  have : chi12 (p * e) = 0 := by
    rcases hp with rfl | rfl
    · exact chi12_eq_zero_of_two (dvd_mul_right _ _)
    · exact chi12_eq_zero_of_three (dvd_mul_right _ _)
  change chi12 (p * e) * _ = 0
  rw [this, zero_mul]

/-- `J(3 | n)` in terms of `n` modulo 3 and 4. -/
lemma jacobi_three {n : ℕ} (h2 : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n) :
    jacobiSym 3 n = (if n % 4 = 1 then 1 else -1) * (if n % 3 = 1 then 1 else -1) := by
  have hmod : jacobiSym (n : ℤ) 3 = if n % 3 = 1 then 1 else -1 := by
    rw [jacobiSym.mod_left]
    have hc : ((n : ℤ) % ((3 : ℕ) : ℤ)) = ((n % 3 : ℕ) : ℤ) := by push_cast; rfl
    rw [hc]
    have hn : n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hn with h | h <;> rw [h] <;> norm_num
  have h4 : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rcases h4 with h | h
  · have hr := jacobiSym.quadratic_reciprocity_one_mod_four (a := n) (b := 3) h ⟨1, by norm_num⟩
    rw [if_pos h, one_mul, ← hmod]
    simpa using hr.symm
  · have hr := jacobiSym.quadratic_reciprocity_three_mod_four (a := n) (b := 3) h (by norm_num)
    rw [if_neg (by omega), ← hmod]
    have : jacobiSym (3 : ℤ) n = -jacobiSym (n : ℤ) 3 := by
      rw [hr]
      simp
    rw [this]
    ring

lemma legendre_two_eq (h13 : 13 ≤ ℓ) {t : ℕ} (ht : 24 ∣ t + jj ℓ) :
    jacobiSym ((2 : ℕ) : ℤ) t = legendreSym ℓ 2 := by
  have hodd := (prime_ge h13).1
  have htodd : Odd t := by
    rw [Nat.odd_iff]
    unfold jj at ht
    omega
  have h8 : ((t : ℕ) : ZMod 8) = -((ℓ : ℕ) : ZMod 8) := by
    have : 8 ∣ t + ℓ := by
      unfold jj at ht
      omega
    have h0 : ((t + ℓ : ℕ) : ZMod 8) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr this
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hχ : ∀ x : ZMod 8, ZMod.χ₈ (-x) = ZMod.χ₈ x := by decide
  have hne2 : ℓ ≠ 2 := by omega
  rw [show ((2 : ℕ) : ℤ) = 2 from rfl, jacobiSym.at_two htodd, legendreSym.at_two hne2, h8, hχ]

lemma legendre_three_eq (h13 : 13 ≤ ℓ) {t : ℕ} (ht : 24 ∣ t + jj ℓ) :
    jacobiSym ((3 : ℕ) : ℤ) t = legendreSym ℓ 3 := by
  obtain ⟨h2, h3⟩ := prime_ge h13
  unfold jj at ht
  have ht2 : ¬ 2 ∣ t := by omega
  have ht3 : ¬ 3 ∣ t := by omega
  have hl2 : ¬ 2 ∣ ℓ := by omega
  have hl3 : ¬ 3 ∣ ℓ := by omega
  have hl : legendreSym ℓ 3 = jacobiSym 3 ℓ := jacobiSym.legendreSym.to_jacobiSym ℓ 3
  rw [hl, show ((3 : ℕ) : ℤ) = 3 from rfl, jacobi_three ht2 ht3, jacobi_three hl2 hl3]
  have h4 : (t % 4 = 1 ∧ ℓ % 4 = 3) ∨ (t % 4 = 3 ∧ ℓ % 4 = 1) := by omega
  have h3' : (t % 3 = 1 ∧ ℓ % 3 = 2) ∨ (t % 3 = 2 ∧ ℓ % 3 = 1) := by omega
  rcases h4 with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases h3' with ⟨c, d⟩ | ⟨c, d⟩ <;> simp [a, b, c, d]

lemma psi_two_eq (h13 : 13 ≤ ℓ) {t : ℕ} (ht : 24 ∣ t + jj ℓ) : psi t (halfWt ℓ) 2 = eig2 ℓ := by
  have he : halfWt ℓ - 1 = (ℓ - 5) / 2 := by unfold halfWt; omega
  rw [psi, legendre_two_eq h13 ht, he, eig2]
  rfl

lemma psi_three_eq (h13 : 13 ≤ ℓ) {t : ℕ} (ht : 24 ∣ t + jj ℓ) : psi t (halfWt ℓ) 3 = eig3 ℓ := by
  have he : halfWt ℓ - 1 = (ℓ - 5) / 2 := by unfold halfWt; omega
  rw [psi, legendre_three_eq h13 ht, he, eig3]
  rfl

/-- The index transforms correctly under `e ↦ ℓ e`. -/
lemma latIndex_ell (h13 : 13 ≤ ℓ) {t e : ℕ} (ht : 24 ∣ t + jj ℓ) (h2 : ¬ 2 ∣ e) (h3 : ¬ 3 ∣ e) :
    latIndex ℓ t (ℓ * e) = ℓ ^ 2 * latIndex ℓ t e - jj ℓ * δ ℓ := by
  have h1 := h24 h13
  have hs := sq_mod_24 h2 h3
  have hd : 24 ∣ t * e ^ 2 + jj ℓ := by
    obtain ⟨c, hc⟩ := ht
    have hq : e ^ 2 = 24 * (e ^ 2 / 24) + 1 := by omega
    refine ⟨t * (e ^ 2 / 24) + c, ?_⟩
    calc t * e ^ 2 + jj ℓ = t * (24 * (e ^ 2 / 24) + 1) + jj ℓ := by rw [← hq]
      _ = 24 * (t * (e ^ 2 / 24)) + (t + jj ℓ) := by ring
      _ = _ := by rw [hc]; ring
  obtain ⟨m, hm⟩ := hd
  have hidx : latIndex ℓ t e = m := by
    unfold latIndex
    rw [hm]
    simp
  rw [hidx]
  have hge : jj ℓ * δ ℓ ≤ ℓ ^ 2 * m := by
    have e1 : ℓ ^ 2 * (24 * m) = ℓ ^ 2 * (t * e ^ 2) + ℓ ^ 2 * jj ℓ := by rw [← hm]; ring
    have e2 : ℓ ^ 2 * jj ℓ = 24 * (jj ℓ * δ ℓ) + jj ℓ := by rw [← h1]; ring
    have h5 : 24 * (jj ℓ * δ ℓ) ≤ 24 * (ℓ ^ 2 * m) := by
      calc 24 * (jj ℓ * δ ℓ) ≤ ℓ ^ 2 * (t * e ^ 2) + (24 * (jj ℓ * δ ℓ) + jj ℓ) := by omega
        _ = 24 * (ℓ ^ 2 * m) := by rw [← e2, ← e1]; ring
    exact Nat.le_of_mul_le_mul_left h5 (by norm_num)
  unfold latIndex
  apply Nat.div_eq_of_eq_mul_right (by norm_num)
  have e1 : ℓ ^ 2 * (24 * m) = ℓ ^ 2 * (t * e ^ 2) + ℓ ^ 2 * jj ℓ := by rw [← hm]; ring
  have e2 : ℓ ^ 2 * jj ℓ = 24 * (jj ℓ * δ ℓ) + jj ℓ := by rw [← h1]; ring
  rw [Nat.mul_sub]
  have e3 : t * (ℓ * e) ^ 2 = ℓ ^ 2 * (t * e ^ 2) := by ring
  have e4 : 24 * (ℓ ^ 2 * m) = ℓ ^ 2 * (24 * m) := by ring
  rw [e3, e4, e1, e2]
  omega

/-- `U_ℓ` kills the lift modulo `ℓ` when `U_{ℓ²}` kills the form. -/
lemma lift_ell_dvd (h13 : 13 ≤ ℓ) {t : ℕ} (ht : 24 ∣ t + jj ℓ) {A : PowerSeries ℤ}
    (hU : ∀ m, (ℓ : ℤ) ∣ A.coeff (ℓ ^ 2 * m - jj ℓ * δ ℓ)) (n : ℕ) :
    (ℓ : ℤ) ∣ (liftSeries ℓ t A).coeff (ℓ * n) := by
  rw [coeff_liftSeries]
  refine Finset.dvd_sum fun x hx => ?_
  have hxm := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hlam : halfWt ℓ - 1 ≠ 0 := by unfold halfWt; omega
  by_cases hd : ℓ ∣ x.1
  · apply Dvd.dvd.mul_right
    unfold psi
    apply Dvd.dvd.mul_left
    exact (Int.natCast_dvd_natCast.mpr hd).trans (dvd_pow_self _ hlam)
  · have he : ℓ ∣ x.2 := (hℓ.out.dvd_mul.mp (Dvd.intro n hxm.symm)).resolve_left hd
    obtain ⟨e, he⟩ := he
    apply Dvd.dvd.mul_left
    by_cases h2 : 2 ∣ e
    · rw [he, chi12_eq_zero_of_two (h2.mul_left ℓ), zero_mul]
      exact dvd_zero _
    by_cases h3 : 3 ∣ e
    · rw [he, chi12_eq_zero_of_three (h3.mul_left ℓ), zero_mul]
      exact dvd_zero _
    apply Dvd.dvd.mul_left
    rw [he, latIndex_ell h13 ht h2 h3]
    exact hU _

/-- Triangularity: a lift vanishing modulo `ℓ` has vanishing terms `(12/e) a(te²)`. -/
lemma chi_coeff_dvd {t : ℕ} (A : PowerSeries ℤ) (d : ℤ)
    (h : ∀ n, d ∣ (liftSeries ℓ t A).coeff n) (e : ℕ) (he : e ≠ 0) :
    d ∣ chi12 e * A.coeff (latIndex ℓ t e) := by
  classical
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    have hb := h e
    rw [coeff_liftSeries] at hb
    have hmem : ((1, e) : ℕ × ℕ) ∈ e.divisorsAntidiagonal :=
      Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul e, he⟩
    rw [← Finset.add_sum_erase _ _ hmem] at hb
    have hone : psi t (halfWt ℓ) 1 = 1 := by simp [psi]
    simp only [hone, one_mul] at hb
    refine (dvd_add_left (Finset.dvd_sum fun x hx => ?_)).mp hb
    obtain ⟨hne, hx'⟩ := Finset.mem_erase.mp hx
    obtain ⟨hxm, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx'
    have hx20 : x.2 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hxm
      exact he hxm.symm
    have hx10 : x.1 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hxm
      exact he hxm.symm
    have hx1 : x.1 ≠ 1 := by
      intro h1
      apply hne
      apply Prod.ext h1
      simpa [h1] using hxm
    have hlt : x.2 < e := by
      rw [← hxm]
      have : 2 ≤ x.1 := by omega
      nlinarith [Nat.pos_of_ne_zero hx20]
    exact (ih x.2 hlt hx20).mul_left _

/-- Every lattice index occurs as `te²`, with `t` squarefree and `e` prime to six. -/
lemma exists_index (h13 : 13 ≤ ℓ) {m : ℕ} (hm : m ≠ 0) :
    ∃ t e : ℕ, Squarefree t ∧ 24 ∣ t + jj ℓ ∧ ¬ 2 ∣ e ∧ ¬ 3 ∣ e ∧ e ≠ 0 ∧ latIndex ℓ t e = m := by
  have hjm := ell_mod (ℓ := ℓ) h13
  have hj24 : jj ℓ ≤ 23 := by rcases hjm with h | h | h | h | h | h | h | h <;> omega
  let n := 24 * m - jj ℓ
  have hn : n + jj ℓ = 24 * m := by
    have : jj ℓ ≤ 24 * m := by omega
    omega
  obtain ⟨t, e, hte, hsf⟩ := Nat.sq_mul_squarefree n
  have hn2 : ¬ 2 ∣ n := by
    rcases hjm with h | h | h | h | h | h | h | h <;> omega
  have hn3 : ¬ 3 ∣ n := by
    rcases hjm with h | h | h | h | h | h | h | h <;> omega
  have he2 : ¬ 2 ∣ e := fun h => hn2 (by
    rw [← hte]
    exact (h.trans (dvd_pow_self e two_ne_zero)).mul_right t)
  have he3 : ¬ 3 ∣ e := fun h => hn3 (by
    rw [← hte]
    exact (h.trans (dvd_pow_self e two_ne_zero)).mul_right t)
  have hs := sq_mod_24 he2 he3
  have hte' : t * e ^ 2 + jj ℓ = 24 * m := by rw [mul_comm, hte, hn]
  refine ⟨t, e, hsf, ?_, he2, he3, fun h => he2 (h ▸ dvd_zero 2), ?_⟩
  · have hq : e ^ 2 = 24 * (e ^ 2 / 24) + 1 := by omega
    refine ⟨m - t * (e ^ 2 / 24), ?_⟩
    have : t * (24 * (e ^ 2 / 24) + 1) + jj ℓ = 24 * m := by rw [← hq]; exact hte'
    have h3 : 24 * (t * (e ^ 2 / 24)) + (t + jj ℓ) = 24 * m := by rw [← this]; ring
    omega
  · unfold latIndex
    rw [hte']
    simp

/-- **Theorem A from modularity of the lifts.** `U_{ℓ²}` is injective modulo `ℓ` on
`S_{(ℓ-2)/2}(SL₂ℤ, ν_η^{-ℓ})`, for every prime `ℓ ≥ 13`. -/
theorem theoremA_of_modularity (h13 : 13 ≤ ℓ) (HM : AADModularity ℓ) {a : PowerSeries ℤ}
    (ha : a ∈ intLattice ℓ)
    (hU : ∀ m, (ℓ : ℤ) ∣ (coordOf ℓ a).coeff (ℓ ^ 2 * m - jj ℓ * δ ℓ)) :
    ∀ m, (ℓ : ℤ) ∣ a.coeff m := by
  let A := coordOf ℓ a
  let ψ : ℤ →+* ZMod ℓ := Int.castRingHom (ZMod ℓ)
  have hlift : ∀ t : ℕ, Squarefree t → 24 ∣ t + jj ℓ → ∀ n, (ℓ : ℤ) ∣ (liftSeries ℓ t A).coeff n := by
    intro t hsf ht
    obtain ⟨g, hg⟩ := HM a ha t hsf ht
    set b := liftSeries ℓ t A with hb
    have hrep : BinaryRep (PowerSeries.map ψ b) ((ℓ - 3) / 2) :=
      binaryRep_of_reduced_modularForm (Int.castRingHom ℂ) (RingHom.injective_int _) ψ
        (halfWt ℓ) b g hg
    by_contra hne
    have hf0 : PowerSeries.map ψ b ≠ 0 := by
      intro h0
      apply hne
      intro n
      have := congrArg (PowerSeries.coeff n) h0
      rw [PowerSeries.coeff_map, map_zero] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
    have hU2 : U 2 (PowerSeries.map ψ b) =
        ((legendreSym ℓ 2 : ZMod ℓ) * (2 : ZMod ℓ) ^ ((ℓ - 5) / 2)) • PowerSeries.map ψ b := by
      rw [← map_U, hb, U_lift (Or.inl rfl), psi_two_eq h13 ht, map_int_smul]
      congr 1
      simp [eig2, ψ]
    have hU3 : U 3 (PowerSeries.map ψ b) =
        ((legendreSym ℓ 3 : ZMod ℓ) * (3 : ZMod ℓ) ^ ((ℓ - 5) / 2)) • PowerSeries.map ψ b := by
      rw [← map_U, hb, U_lift (Or.inr rfl), psi_three_eq h13 ht, map_int_smul]
      congr 1
      simp [eig3, ψ]
    apply U_ne_zero_of_binary_sign_eigenvalues ℓ h13 _ hrep hf0 hU2 hU3
    ext n
    rw [coeff_U, PowerSeries.coeff_map, map_zero]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (lift_ell_dvd h13 ht hU n)
  have hA : ∀ m, (ℓ : ℤ) ∣ A.coeff m := by
    intro m
    by_cases hm : m = 0
    · subst hm
      have := hU 0
      simpa using this
    obtain ⟨t, e, hsf, ht, he2, he3, he0, hidx⟩ := exists_index (ℓ := ℓ) h13 hm
    have hd := chi_coeff_dvd (t := t) A (ℓ : ℤ) (hlift t hsf ht) e he0
    rw [hidx] at hd
    rcases chi12_ne_zero he2 he3 with h | h
    · rwa [h, one_mul] at hd
    · rwa [h, neg_one_mul, dvd_neg] at hd
  intro m
  have hco := qfac_pow_coord (ℓ := ℓ) a
  choose c hc using hA
  have heq : A = (ℓ : ℤ) • PowerSeries.mk c := by
    ext n
    rw [map_zsmul, smul_eq_mul, hc, PowerSeries.coeff_mk]
  rw [← hco, show coordOf ℓ a = A from rfl, heq, smul_mul_assoc, map_zsmul, smul_eq_mul]
  exact dvd_mul_right _ _

/-- **Theorem A for Boylan–Webb's operator**, from modularity of the lifts. -/
theorem X_injective_of_modularity (h13 : 13 ≤ ℓ) (HM : AADModularity ℓ) {a : PowerSeries ℤ}
    (ha : a ∈ intLattice ℓ) (hX : Ψ ℓ (U ℓ (Φ ℓ * U ℓ (Dz ^ tt ℓ * a))) = 0) :
    Ψ ℓ a = 0 :=
  X_injective_of_U_injective h13 (fun _ hb hU => theoremA_of_modularity h13 HM hb hU) ha hX

end RamanujanTau.TheoremA.HalfIntegral
