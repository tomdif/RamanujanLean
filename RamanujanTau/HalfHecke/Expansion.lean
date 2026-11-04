import RamanujanTau.ThetaLift.HalfExpansion
import RamanujanTau.ThetaLift.EtaMultiplier
import RamanujanTau.ThetaLift.EtaProduct
import RamanujanTau.HalfHecke.Gauss

/-!
# The Hecke operator `T(Q²)` on `G/η` as a coset sum, and its `q`-expansion

For a level-one cusp form `G` of weight `k` put `F = G/η`. For a prime `Q ≥ 5` and a constant `cM`,

  `T F(z) = Q^{2k−3} F(Q²z) + cM Σ_{x mod Q} (x/Q) F(z + 24x/Q) + Q^{−2} Σ_{x mod Q²} F((z + 24x)/Q²)`.

These are the `Q² + Q` cosets of `Γ diag(1, Q²) Γ` (`d = 1`, `d = Q` with `Q ∤ b`, `d = Q²`), with the
translations scaled by `24` so that the `η`-multiplier on each coset is trivial or quadratic.

**`hasSum_TF`**: `e(z/24)·T F(z) = Σ_N B(N) qᴺ`, where, with `d = (Q²−1)/24` and `F = Σ c(N) q^{N−1/24}`,
`B(N) = c(Q²N − d) + cM·gQ·((24N−1)/Q)·c(N) + Q^{2k−3} c((N+d)/Q²)`.
The middle term comes from the twisted character sum `charSum`; the outer ones from
`Σ_{x mod Q²} e(xn/Q²) = Q²·[Q² ∣ n]`.
-/

set_option autoImplicit false

namespace RamanujanTau.HalfHecke
open Complex ModularForm Finset
open UpperHalfPlane hiding I
open RamanujanTau.ThetaLift
open scoped Real MatrixGroups

noncomputable section

local notation "𝕢" => Function.Periodic.qParam

variable {k : ℤ} (G : CuspForm 𝒮ℒ k)

/-- `G` as a function on `ℂ`. -/
def Gc (z : ℂ) : ℂ := G (ofComplex z)

/-- `F = G/η`. -/
def Fc (z : ℂ) : ℂ := Gc G z / η z

/-- `e(x) = exp(2πix)`. -/
def ee (x : ℂ) : ℂ := cexp (2 * π * I * x)

lemma ee_add (x y : ℂ) : ee (x + y) = ee x * ee y := by
  unfold ee; rw [← Complex.exp_add]; ring_nf

lemma ee_congr {x y : ℂ} (h : x = y) : ee x = ee y := by rw [h]

/-- The expansion `F(w) = Σ c(m) e(w(24m − 1)/24)`. -/
lemma hasSum_Fc (w : ℂ) (hw : 0 < w.im) :
    HasSum (fun m : ℕ => cA G 1 m * ee (w * (24 * m - 1) / 24)) (Fc G w) := by
  set tw : ℍ := ⟨w, hw⟩
  have h1 := hasSum_hP G 1 tw
  have h2 := cusp_div_eta G 1 tw
  have hG : Gc G w = G tw := by
    unfold Gc; congr 1; exact ofComplex_apply_of_im_pos hw
  have hF : Fc G w = (𝕢 (24 : ℝ) w)⁻¹ * hP G 1 tw := by
    rw [Fc, hG]; simpa using h2
  rw [hF]
  refine (h1.mul_left ((𝕢 (24 : ℝ) w)⁻¹)).congr_fun fun m => ?_
  simp only [Function.Periodic.qParam, ee]
  have htw : (tw : ℂ) = w := rfl
  rw [htw, ← Complex.exp_neg, ← Complex.exp_nat_mul, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

variable (Q : ℕ) [hQ : Fact Q.Prime]

/-- `d = (Q² − 1)/24`. -/
def dQ : ℕ := (Q ^ 2 - 1) / 24

/-- The coset sum. -/
def TF (cM : ℂ) (z : ℂ) : ℂ :=
  (Q : ℂ) ^ (2 * k - 3) * Fc G ((Q : ℂ) ^ 2 * z)
  + cM * ∑ x : ZMod Q, chiQ Q x * Fc G (z + 24 * (x.val : ℂ) / Q)
  + ((Q : ℂ) ^ 2)⁻¹ * ∑ x : ZMod (Q ^ 2), Fc G ((z + 24 * (x.val : ℂ)) / (Q : ℂ) ^ 2)

/-- The coefficients of `e(z/24)·T F`. -/
def Bc (cM : ℂ) (N : ℕ) : ℂ :=
  (if dQ Q ≤ Q ^ 2 * N then cA G 1 (Q ^ 2 * N - dQ Q) else 0)
  + cM * gQ Q * chiQ Q ((24 * (N : ℤ) - 1 : ℤ) : ZMod Q) * cA G 1 N
  + (if Q ^ 2 ∣ N + dQ Q then (Q : ℂ) ^ (2 * k - 3) * cA G 1 ((N + dQ Q) / Q ^ 2) else 0)

/-! ### Arithmetic of `Q` -/

section Arith
variable {Q}

lemma Q_ge (hQ5 : 5 ≤ Q) : 24 ∣ Q ^ 2 - 1 := by
  have h2 : ¬ 2 ∣ Q := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hQ.out).mp h; omega
  have h3 : ¬ 3 ∣ Q := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hQ.out).mp h; omega
  have h := int_sq_sub_one h2 h3
  have h1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have : ((Q ^ 2 - 1 : ℕ) : ℤ) = (Q : ℤ) ^ 2 - 1 := by push_cast [Nat.cast_sub h1]; ring
  rw [← this] at h
  exact_mod_cast h

lemma dQ_spec (hQ5 : 5 ≤ Q) : 24 * dQ Q + 1 = Q ^ 2 := by
  have h := Q_ge hQ5
  have h1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold dQ; omega

lemma dQ_pos (hQ5 : 5 ≤ Q) : 0 < dQ Q := by
  have := dQ_spec hQ5
  have : 25 ≤ Q ^ 2 := by nlinarith
  omega

lemma dQ_lt (hQ5 : 5 ≤ Q) : dQ Q < Q ^ 2 := by
  have := dQ_spec hQ5; omega

lemma coprime24 (hQ5 : 5 ≤ Q) : Nat.Coprime 24 (Q ^ 2) := by
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hQ.out]
  intro h
  have : Q ≤ 24 := Nat.le_of_dvd (by norm_num) h
  interval_cases Q <;> norm_num at h <;> exact absurd hQ.out (by norm_num)

/-- `Q² ∣ 24m − 1 ⟺ Q² ∣ m + d`. -/
lemma dvd_iff (hQ5 : 5 ≤ Q) (m : ℕ) :
    ((Q : ℤ) ^ 2 ∣ 24 * (m : ℤ) - 1) ↔ Q ^ 2 ∣ m + dQ Q := by
  have hs := dQ_spec hQ5
  have e : (24 : ℤ) * ((m + dQ Q : ℕ) : ℤ) = (24 * (m : ℤ) - 1) + ((Q ^ 2 : ℕ) : ℤ) := by
    push_cast; have : ((24 * dQ Q + 1 : ℕ) : ℤ) = ((Q ^ 2 : ℕ) : ℤ) := by rw [hs]
    push_cast at this; linarith
  constructor
  · intro h
    have h2 : ((Q ^ 2 : ℕ) : ℤ) ∣ 24 * ((m + dQ Q : ℕ) : ℤ) := by
      rw [e]; exact dvd_add (by exact_mod_cast h) dvd_rfl
    have h3 := Int.natCast_dvd_natCast.mp (by exact_mod_cast h2 : ((Q ^ 2 : ℕ) : ℤ) ∣ ((24 * (m + dQ Q) : ℕ) : ℤ))
    exact (Nat.Coprime.dvd_of_dvd_mul_left (coprime24 hQ5).symm h3)
  · intro h
    have h2 : ((Q ^ 2 : ℕ) : ℤ) ∣ 24 * ((m + dQ Q : ℕ) : ℤ) :=
      dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr h) _
    rw [e] at h2
    have := (dvd_add_left (dvd_refl ((Q ^ 2 : ℕ) : ℤ))).mp h2
    exact_mod_cast this

end Arith

/-! ### The three pieces -/

variable {G}

/-- The `d = 1` coset. -/
lemma hasSum_V (hQ5 : 5 ≤ Q) (hc0 : cA G 1 0 = 0) (t : ℍ) :
    HasSum (fun N : ℕ => (if Q ^ 2 ∣ N + dQ Q then cA G 1 ((N + dQ Q) / Q ^ 2) else 0) * ee (t * N))
      (ee (t / 24) * Fc G ((Q : ℂ) ^ 2 * t)) := by
  have hw : 0 < ((Q : ℂ) ^ 2 * t).im := by
    have : ((Q : ℂ) ^ 2 * t).im = (Q : ℝ) ^ 2 * t.im := by
      simp [pow_two, Complex.mul_im, Complex.mul_re]
    rw [this]; exact mul_pos (by have := hQ.out.pos; positivity) t.im_pos
  have h := (hasSum_Fc G _ hw).mul_left (ee (t / 24))
  set g : ℕ → ℕ := fun m => Q ^ 2 * m - dQ Q with hg
  have hs := dQ_spec hQ5
  have hd0 := dQ_pos hQ5
  have hdl := dQ_lt hQ5
  have hginj : Function.Injective g := by
    intro m n hmn
    simp only [hg] at hmn
    rcases Nat.eq_zero_or_pos m with hm | hm <;> rcases Nat.eq_zero_or_pos n with hn | hn
    · omega
    · subst hm; simp at hmn
      have : Q ^ 2 ≤ Q ^ 2 * n := Nat.le_mul_of_pos_right _ hn
      omega
    · subst hn; simp at hmn
      have : Q ^ 2 ≤ Q ^ 2 * m := Nat.le_mul_of_pos_right _ hm
      omega
    · have h1 : Q ^ 2 ≤ Q ^ 2 * n := Nat.le_mul_of_pos_right _ hn
      have h2 : Q ^ 2 ≤ Q ^ 2 * m := Nat.le_mul_of_pos_right _ hm
      have : Q ^ 2 * m = Q ^ 2 * n := by omega
      exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  set f : ℕ → ℂ := fun N => (if Q ^ 2 ∣ N + dQ Q then cA G 1 ((N + dQ Q) / Q ^ 2) else 0) * ee (t * N)
  have hzero : ∀ N, N ∉ Set.range g → f N = 0 := by
    intro N hN
    simp only [f]
    split_ifs with hdv
    · exfalso; apply hN
      obtain ⟨m, hm⟩ := hdv
      exact ⟨m, by simp only [hg]; omega⟩
    · simp
  rw [← hginj.hasSum_iff hzero]
  refine h.congr_fun fun m => ?_
  simp only [Function.comp, f, hg]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have : ¬ Q ^ 2 ∣ Q ^ 2 * 0 - dQ Q + dQ Q := by
      simp only [mul_zero, zero_tsub, zero_add]
      exact Nat.not_dvd_of_pos_of_lt hd0 hdl
    rw [if_neg this, hc0]; simp
  · have hle : dQ Q ≤ Q ^ 2 * m := le_trans hdl.le (Nat.le_mul_of_pos_right _ hm)
    have e1 : Q ^ 2 * m - dQ Q + dQ Q = Q ^ 2 * m := Nat.sub_add_cancel hle
    rw [e1, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (by positivity)]
    rw [mul_left_comm, ← ee_add]
    congr 1
    apply ee_congr
    rw [Nat.cast_sub hle]
    have : (Q : ℂ) ^ 2 = 24 * (dQ Q : ℂ) + 1 := by exact_mod_cast hs.symm
    push_cast
    rw [this]
    ring

lemma ee_zmod (M : ℕ) [NeZero M] (x : ZMod M) (n : ℤ) :
    ee ((x.val : ℂ) * n / M) = ZMod.stdAddChar (x * (n : ZMod M)) := by
  have e : x * (n : ZMod M) = (((x.val : ℤ) * n : ℤ) : ZMod M) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [e, ZMod.stdAddChar_coe, ee]
  congr 1; push_cast; ring

lemma im_pos_add (t : ℍ) (r : ℝ) : 0 < ((t : ℂ) + r).im := by simpa using t.im_pos

/-- The `d = Q` cosets: the Gauss sum. -/
lemma hasSum_M (hQ5 : 5 ≤ Q) (t : ℍ) :
    HasSum (fun N : ℕ => gQ Q * chiQ Q ((24 * (N : ℤ) - 1 : ℤ) : ZMod Q) * cA G 1 N * ee (t * N))
      (ee (t / 24) * ∑ x : ZMod Q, chiQ Q x * Fc G (t + 24 * (x.val : ℂ) / Q)) := by
  have hw : ∀ x : ZMod Q, 0 < ((t : ℂ) + 24 * (x.val : ℂ) / Q).im := by
    intro x
    have e : (t : ℂ) + 24 * (x.val : ℂ) / Q = (t : ℂ) + ((24 * (x.val : ℝ) / Q : ℝ) : ℂ) := by
      push_cast; ring
    rw [e]; exact im_pos_add t _
  have h := hasSum_sum (s := Finset.univ) fun x _ =>
    ((hasSum_Fc G _ (hw x)).mul_left (ee (t / 24) * chiQ Q x))
  have hQ0 : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.out.ne_zero
  rw [Finset.mul_sum]
  convert h using 1
  · funext m
    have e : ∀ x : ZMod Q, ee (t / 24) * chiQ Q x *
        (cA G 1 m * ee (((t : ℂ) + 24 * (x.val : ℂ) / Q) * (24 * m - 1) / 24)) =
        cA G 1 m * ee (t * m) * (chiQ Q x * ZMod.stdAddChar (x * ((24 * (m : ℤ) - 1 : ℤ) : ZMod Q))) := by
      intro x
      rw [← ee_zmod]
      have : ee (t / 24) * ee (((t : ℂ) + 24 * (x.val : ℂ) / Q) * (24 * m - 1) / 24) =
          ee (t * m) * ee ((x.val : ℂ) * ((24 * (m : ℤ) - 1 : ℤ) : ℂ) / Q) := by
        rw [← ee_add, ← ee_add]; apply ee_congr; push_cast; field_simp; ring
      linear_combination (cA G 1 m * chiQ Q x) * this
    rw [Finset.sum_congr rfl fun x _ => e x, ← Finset.mul_sum, charSum Q (by omega)]
    ring
  · refine Finset.sum_congr rfl fun x _ => ?_; ring

/-- The `d = Q²` cosets: `Σ_{x mod Q²} e(xn/Q²) = Q²·[Q² ∣ n]`. -/
lemma hasSum_U (hQ5 : 5 ≤ Q) (hc0 : cA G 1 0 = 0) (t : ℍ) :
    HasSum (fun N : ℕ => (if dQ Q ≤ Q ^ 2 * N then cA G 1 (Q ^ 2 * N - dQ Q) else 0) * ee (t * N))
      (ee (t / 24) * (((Q : ℂ) ^ 2)⁻¹ *
        ∑ x : ZMod (Q ^ 2), Fc G (((t : ℂ) + 24 * (x.val : ℂ)) / (Q : ℂ) ^ 2))) := by
  have hQ0 : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.out.ne_zero
  haveI : NeZero (Q ^ 2) := ⟨pow_ne_zero _ hQ.out.ne_zero⟩
  have hs := dQ_spec hQ5
  have hd0 := dQ_pos hQ5
  have hdl := dQ_lt hQ5
  have hw : ∀ x : ZMod (Q ^ 2), 0 < (((t : ℂ) + 24 * (x.val : ℂ)) / (Q : ℂ) ^ 2).im := by
    intro x
    have e : (((t : ℂ) + 24 * (x.val : ℂ)) / (Q : ℂ) ^ 2) =
        (((t : ℂ) + ((24 * x.val : ℕ) : ℝ)) * (((Q : ℝ) ^ 2)⁻¹ : ℝ)) := by
      push_cast; ring
    rw [e, Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero]
    have := im_pos_add t ((24 * x.val : ℕ) : ℝ)
    have hq : (0 : ℝ) < ((Q : ℝ) ^ 2)⁻¹ := by have := hQ.out.pos; positivity
    rw [zero_add]; exact mul_pos this hq
  have h := hasSum_sum (s := Finset.univ) fun x _ =>
    ((hasSum_Fc G _ (hw x)).mul_left (ee (t / 24) * ((Q : ℂ) ^ 2)⁻¹))
  set u : ℕ → ℂ := fun m => if Q ^ 2 ∣ m + dQ Q then cA G 1 m * ee (t * ((m + dQ Q) / Q ^ 2 : ℕ)) else 0
    with hu
  have hU : HasSum u (ee (t / 24) * (((Q : ℂ) ^ 2)⁻¹ *
        ∑ x : ZMod (Q ^ 2), Fc G (((t : ℂ) + 24 * (x.val : ℂ)) / (Q : ℂ) ^ 2))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    convert h using 1
    · funext m
      have e : ∀ x : ZMod (Q ^ 2), ee (t / 24) * ((Q : ℂ) ^ 2)⁻¹ *
          (cA G 1 m * ee ((((t : ℂ) + 24 * (x.val : ℂ)) / (Q : ℂ) ^ 2) * (24 * m - 1) / 24)) =
          ((Q : ℂ) ^ 2)⁻¹ * cA G 1 m * ee (t * ((m : ℂ) + dQ Q) / (Q : ℂ) ^ 2) *
            ZMod.stdAddChar (x * ((24 * (m : ℤ) - 1 : ℤ) : ZMod (Q ^ 2))) := by
        intro x
        have e2 := ee_zmod (Q ^ 2) x (24 * (m : ℤ) - 1)
        rw [← e2]
        have hdc : (Q : ℂ) ^ 2 = 24 * (dQ Q : ℂ) + 1 := by exact_mod_cast hs.symm
        have : ee (t / 24) * ee ((((t : ℂ) + 24 * (x.val : ℂ)) / (Q : ℂ) ^ 2) * (24 * m - 1) / 24) =
            ee (t * ((m : ℂ) + dQ Q) / (Q : ℂ) ^ 2) *
              ee ((x.val : ℂ) * ((24 * (m : ℤ) - 1 : ℤ) : ℂ) / ((Q ^ 2 : ℕ) : ℂ)) := by
          have hD : (dQ Q : ℂ) = ((Q : ℂ) ^ 2 - 1) / 24 := by rw [hdc]; ring
          rw [← ee_add, ← ee_add]; apply ee_congr; push_cast
          rw [hD]; field_simp; ring
        linear_combination (((Q : ℂ) ^ 2)⁻¹ * cA G 1 m) * this
      rw [Finset.sum_congr rfl fun x _ => e x, ← Finset.mul_sum,
        AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar _), ZMod.card]
      simp only [hu]
      by_cases hdv : Q ^ 2 ∣ m + dQ Q
      · have hz : (((24 * (m : ℤ) - 1 : ℤ)) : ZMod (Q ^ 2)) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact (dvd_iff hQ5 m).mpr hdv
        rw [if_pos hdv, if_pos hz]
        obtain ⟨n, hn⟩ := hdv
        rw [hn, Nat.mul_div_cancel_left _ (by positivity)]
        have : ((m : ℂ) + dQ Q) = (Q : ℂ) ^ 2 * n := by exact_mod_cast hn
        rw [this]
        field_simp
        push_cast; ring
      · have hz : (((24 * (m : ℤ) - 1 : ℤ)) : ZMod (Q ^ 2)) ≠ 0 := by
          rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact fun h => hdv ((dvd_iff hQ5 m).mp h)
        rw [if_neg hdv, if_neg hz]; ring
    · exact Finset.sum_congr rfl fun x _ => by ring
  set g : ℕ → ℕ := fun N => Q ^ 2 * N - dQ Q with hg
  have hginj : Function.Injective g := by
    intro m n hmn
    simp only [hg] at hmn
    rcases Nat.eq_zero_or_pos m with hm | hm <;> rcases Nat.eq_zero_or_pos n with hn | hn
    · omega
    · subst hm; simp at hmn
      have : Q ^ 2 ≤ Q ^ 2 * n := Nat.le_mul_of_pos_right _ hn
      omega
    · subst hn; simp at hmn
      have : Q ^ 2 ≤ Q ^ 2 * m := Nat.le_mul_of_pos_right _ hm
      omega
    · have h1 : Q ^ 2 ≤ Q ^ 2 * n := Nat.le_mul_of_pos_right _ hn
      have h2 : Q ^ 2 ≤ Q ^ 2 * m := Nat.le_mul_of_pos_right _ hm
      have : Q ^ 2 * m = Q ^ 2 * n := by omega
      exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have hzero : ∀ m, m ∉ Set.range g → u m = 0 := by
    intro m hm
    simp only [hu]
    split_ifs with hdv
    · exfalso; apply hm
      obtain ⟨n, hn⟩ := hdv
      exact ⟨n, by simp only [hg]; omega⟩
    · rfl
  rw [← hginj.hasSum_iff hzero] at hU
  refine hU.congr_fun fun N => ?_
  simp only [Function.comp, hu, hg]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : ¬ Q ^ 2 ∣ Q ^ 2 * 0 - dQ Q + dQ Q := by
      simp only [mul_zero, zero_tsub, zero_add]
      exact Nat.not_dvd_of_pos_of_lt hd0 hdl
    rw [if_neg this, if_neg (by simp; omega)]; simp
  · have hle : dQ Q ≤ Q ^ 2 * N := le_trans hdl.le (Nat.le_mul_of_pos_right _ hN)
    have e1 : Q ^ 2 * N - dQ Q + dQ Q = Q ^ 2 * N := Nat.sub_add_cancel hle
    rw [if_pos hle, e1, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (by positivity)]

/-- **The `q`-expansion of the coset sum**: `e(z/24)·T F(z) = Σ_N B(N) qᴺ`. -/
theorem hasSum_TF (hQ5 : 5 ≤ Q) (hc0 : cA G 1 0 = 0) (cM : ℂ) (t : ℍ) :
    HasSum (fun N : ℕ => Bc G Q cM N * ee (t * N)) (ee (t / 24) * TF G Q cM t) := by
  have hV := (hasSum_V Q hQ5 hc0 t).mul_left ((Q : ℂ) ^ (2 * k - 3))
  have hM := (hasSum_M (G := G) Q hQ5 t).mul_left cM
  have hU := hasSum_U Q hQ5 hc0 t
  convert (hU.add hM).add hV using 1
  · funext N; simp only [Bc]; split_ifs <;> ring
  · unfold TF; ring

end

end RamanujanTau.HalfHecke
