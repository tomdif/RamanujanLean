/-
# Sharp prime-power Kloosterman bound for odd exponents (stationary phase)

For `p` an odd prime, `k = 2j+1 ≥ 3` and any `b`:  `|S(1,b;p^k)| ≤ 4 p^{k/2}`.

Proof (elementary, no Gauss-sum evaluation). Put `x = p^j`, so `x³ = 0` in `ZMod p^k`.
For every `t`, `u ↦ u(1+xt)` permutes the units, and `(1+xt)⁻¹ = 1 - xt + x²t²`, so
`u(1+xt) + b ū(1+xt)⁻¹ = f(u) + t·x(u - bū) + t²·x² bū`. Averaging over `t` gives
`p^k S = ∑_u ψ(f(u)) Q(x(u-bū), x² bū)`, `Q(A,B) = ∑_t ψ(tA + t²B)`.
Squaring and shifting `t = s + h`: `|Q(A,B)|² = p^k ∑_{h : 2hB = 0} ψ(hA + h²B)`.
For `B = x² w`, `w` a unit (`p ∤ b`), the condition is `x²h = 0` (then `h²B = 0`), the set of such `h`
is invariant under `h ↦ h + p` and has at most `p^{k-1}` elements, so
`|Q|² ≤ p^{2k-1}` if `p^{j+1}(u - bū) = 0` and `Q = 0` otherwise.
At most `4 p^{j+1}` units satisfy `p^{j+1}(u² - b) = 0` (`card_sqrt_le`), so
`|S| ≤ 4 p^{j+1} p^{k-1/2} / p^k = 4 p^{k/2}`. If `p ∣ b` that set is empty and `S = 0`.
-/
import RamanujanTau.TauBound.KlPrimePow

set_option autoImplicit false

namespace RamanujanTau.WeilKloosterman

open Complex RamanujanTau.TauBound
open scoped ComplexConjugate

section Quad

variable {N : ℕ} [NeZero N]

/-- The quadratic exponential sum `Q(A,B) = ∑_t ψ(tA + t²B)` on `ZMod N`. -/
noncomputable def qsum (A B : ZMod N) : ℂ :=
  ∑ t : ZMod N, ZMod.stdAddChar (t * A + t ^ 2 * B)

lemma conj_psi (x : ZMod N) : conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv, ← Complex.inv_eq_conj (norm_stdAddChar N x)]

lemma sum_psi_mul' (y : ZMod N) :
    ∑ s : ZMod N, ZMod.stdAddChar (s * y) = if y = 0 then (N : ℂ) else 0 := by
  classical
  rw [AddChar.sum_mulShift y (ZMod.isPrimitive_stdAddChar N)]
  simp [ZMod.card]

/-- `|Q(A,B)|² = N ∑_{h : 2hB = 0} ψ(hA + h²B)`. -/
theorem qsum_normSq (A B : ZMod N) :
    ((‖qsum A B‖ ^ 2 : ℝ) : ℂ) = (N : ℂ) * ∑ h : ZMod N,
      if 2 * h * B = 0 then ZMod.stdAddChar (h * A + h ^ 2 * B) else 0 := by
  classical
  have hn : ((‖qsum A B‖ ^ 2 : ℝ) : ℂ) = qsum A B * conj (qsum A B) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hn, qsum, map_sum, Finset.sum_mul_sum]
  simp only [conj_psi]
  rw [Finset.sum_comm]
  have hrow : ∀ s : ZMod N, ∑ t : ZMod N, ZMod.stdAddChar (t * A + t ^ 2 * B) *
      ZMod.stdAddChar (-(s * A + s ^ 2 * B)) = ∑ h : ZMod N,
        ZMod.stdAddChar (h * A + h ^ 2 * B) * ZMod.stdAddChar (s * (2 * h * B)) := by
    intro s
    refine (Fintype.sum_equiv (Equiv.addRight s) _ _ (fun h => ?_)).symm
    simp only [Equiv.coe_addRight]
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1; ring
  simp_rw [hrow]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [← Finset.mul_sum, sum_psi_mul']
  split_ifs <;> simp [mul_comm]

end Quad

section OddPow

variable {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (j : ℕ) (hj : 1 ≤ j)

include hp hp2 in
lemma two_isUnit (k : ℕ) : IsUnit ((2 : ℕ) : ZMod (p ^ k)) := by
  rw [ZMod.isUnit_iff_coprime]
  refine Nat.Coprime.pow_right _ ?_
  exact (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)

include hp in
/-- At most `p^{k-1}` elements `h` of `ZMod p^k` satisfy `p^{k-1} h = 0`. -/
lemma card_ker_le (k : ℕ) (hk : 1 ≤ k) [NeZero (p ^ k)] :
    (Finset.univ.filter (fun h : ZMod (p ^ k) => (p : ZMod (p ^ k)) ^ (k - 1) * h = 0)).card ≤
      p ^ (k - 1) := by
  classical
  refine le_trans (Finset.card_le_card (fun h hh => ?_)) (card_transl_le k 1 0 (p := p))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
  set H : ℤ := (h.val : ℤ)
  have hH : ((H : ℤ) : ZMod (p ^ k)) = h := by simp [H]
  have hz : ((((p : ℤ) ^ (k - 1) * H : ℤ)) : ZMod (p ^ k)) = 0 := by
    push_cast; rw [hH]; exact hh
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  have hpk : ((p ^ k : ℕ) : ℤ) = (p : ℤ) ^ (k - 1) * p := by
    push_cast; rw [← pow_succ]; congr 1; omega
  rw [hpk] at hz
  have hdv : (p : ℤ) ∣ H := (mul_dvd_mul_iff_left (by have := hp.pos; positivity)).mp hz
  rw [← hH]
  exact mem_transl k hp.pos 1 hk 0 H (by simpa using hdv)

end OddPow

/-- **Sharp odd prime-power Kloosterman bound**: `|S(1,b;p^{2j+1})| ≤ 4 (p^{2j+1})^{1/2}`
for odd primes `p` and `j ≥ 1`. -/
theorem norm_kl_primePow_odd_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {j k : ℕ} (hj : 1 ≤ j)
    (hk : k = 2 * j + 1) [NeZero (p ^ k)] (b : ZMod (p ^ k)) :
    ‖kl (p ^ k) 1 b‖ ≤ 4 * Real.sqrt ((p : ℝ) ^ k) := by
  classical
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  -- the set F of units with `p^{j+1}(u² - b) = 0`
  set F := Finset.univ.filter (fun u : (ZMod (p ^ k))ˣ =>
      (p : ZMod (p ^ k)) ^ (j + 1) * ((u : ZMod (p ^ k)) ^ 2 - b) = 0) with hF
  have hFcard : F.card ≤ 4 * p ^ (j + 1) := card_sqrt_le hp k (by omega) (j + 1) (by omega) b
  have hcond : ∀ u : (ZMod (p ^ k))ˣ, (p : ZMod (p ^ k)) ^ (j + 1) *
      ((u : ZMod (p ^ k)) - b * ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))) = 0 ↔ u ∈ F := by
    intro u
    have hu : ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) * u = 1 := by simp
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have : (p : ZMod (p ^ k)) ^ (j + 1) * ((u : ZMod (p ^ k)) ^ 2 - b) =
          (p : ZMod (p ^ k)) ^ (j + 1) * ((u : ZMod (p ^ k)) -
            b * ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))) * u := by
        linear_combination ((p : ZMod (p ^ k)) ^ (j + 1) * b) * hu
      rw [this, h, zero_mul]
    · intro h
      have : (p : ZMod (p ^ k)) ^ (j + 1) * ((u : ZMod (p ^ k)) -
            b * ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))) =
          (p : ZMod (p ^ k)) ^ (j + 1) * ((u : ZMod (p ^ k)) ^ 2 - b) *
            ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) := by
        linear_combination (-((p : ZMod (p ^ k)) ^ (j + 1) * (u : ZMod (p ^ k)))) * hu
      rw [this, h, zero_mul]
  by_cases hb : IsUnit b
  swap
  · -- `p ∣ b`: the averaging bound with `x = p^{j+1}` and an empty `F`
    set x : ZMod (p ^ k) := (p : ZMod (p ^ k)) ^ (j + 1)
    have hx : x * x = 0 := by
      have : x * x = ((p ^ (2 * (j + 1)) : ℕ) : ZMod (p ^ k)) := by
        simp only [x]; push_cast; ring
      rw [this, ZMod.natCast_eq_zero_iff]
      exact Nat.pow_dvd_pow p (by omega)
    refine (norm_kl_le_card x hx 1 b).trans ?_
    have hempty : Finset.univ.filter (fun u : (ZMod (p ^ k))ˣ =>
        x * (1 * (u : ZMod (p ^ k)) - b * ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))) = 0) = ∅ := by
      refine Finset.filter_false_of_mem (fun u _ hu0 => ?_)
      rw [one_mul, hcond u] at hu0
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hu0
      -- integers
      have hbv : p ∣ b.val := by
        have hb' : ¬ IsUnit ((b.val : ℕ) : ZMod (p ^ k)) := by simpa using hb
        rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega)] at hb'
        by_contra hcon
        exact hb' ((Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hcon))
      set U : ℤ := ((u : ZMod (p ^ k)).val : ℤ)
      set B : ℤ := (b.val : ℤ)
      have hUc : ((U : ℤ) : ZMod (p ^ k)) = u := by simp [U]
      have hBc : ((B : ℤ) : ZMod (p ^ k)) = b := by simp [B]
      have hz : ((((p : ℤ) ^ (j + 1) * (U ^ 2 - B) : ℤ)) : ZMod (p ^ k)) = 0 := by
        push_cast; rw [hUc, hBc]; exact hu0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
      have hpk : ((p ^ k : ℕ) : ℤ) = (p : ℤ) ^ (j + 1) * ((p : ℤ) ^ (j - 1) * p) := by
        push_cast; rw [← pow_succ, ← pow_add]; congr 1; omega
      rw [hpk] at hz
      have h1 : (p : ℤ) ^ (j - 1) * p ∣ U ^ 2 - B :=
        (mul_dvd_mul_iff_left (by positivity)).mp hz
      have h2 : (p : ℤ) ∣ U ^ 2 - B := (Dvd.intro_left _ rfl).trans h1
      have h3 : (p : ℤ) ∣ B := Int.natCast_dvd_natCast.mpr hbv
      have h4 : (p : ℤ) ∣ U ^ 2 := by
        have := dvd_add h2 h3; simpa using this
      have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      exact not_dvd_val_unit hp k (by omega) u (hpz.dvd_of_dvd_pow h4)
    rw [hempty]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  -- `b` a unit: stationary phase
  set x : ZMod (p ^ k) := (p : ZMod (p ^ k)) ^ j with hxdef
  have hx3 : x ^ 3 = 0 := by
    have : x ^ 3 = ((p ^ (3 * j) : ℕ) : ZMod (p ^ k)) := by
      simp only [x]; push_cast; ring
    rw [this, ZMod.natCast_eq_zero_iff]
    exact Nat.pow_dvd_pow p (by omega)
  have hx2p : x ^ 2 * (p : ZMod (p ^ k)) = 0 := by
    have : x ^ 2 * (p : ZMod (p ^ k)) = ((p ^ k : ℕ) : ZMod (p ^ k)) := by
      simp only [x, hk]; push_cast; ring
    rw [this, ZMod.natCast_self]
  have hxk1 : x ^ 2 = (p : ZMod (p ^ k)) ^ (k - 1) := by
    simp only [x, hk]; rw [← pow_mul]; congr 1; omega
  let ε : ZMod (p ^ k) → (ZMod (p ^ k))ˣ := fun t =>
    ⟨1 + x * t, 1 - x * t + x ^ 2 * t ^ 2, by linear_combination t ^ 3 * hx3,
      by linear_combination t ^ 3 * hx3⟩
  set f : (ZMod (p ^ k))ˣ → ZMod (p ^ k) := fun u =>
    (u : ZMod (p ^ k)) + b * ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))
  set g : (ZMod (p ^ k))ˣ → ZMod (p ^ k) := fun u =>
    (u : ZMod (p ^ k)) - b * ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))
  set w : (ZMod (p ^ k))ˣ → ZMod (p ^ k) := fun u =>
    b * ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))
  have hshift : ∀ t : ZMod (p ^ k), kl (p ^ k) 1 b = ∑ u : (ZMod (p ^ k))ˣ,
      ZMod.stdAddChar (f u) * ZMod.stdAddChar (t * (x * g u) + t ^ 2 * (x ^ 2 * w u)) := by
    intro t
    unfold kl
    refine (Fintype.sum_equiv (Equiv.mulRight (ε t)) _ _ (fun u => ?_)).symm
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp only [Equiv.coe_mulRight, Units.val_mul, mul_inv_rev, ε, Units.inv_mk, f, g, w]
    ring
  have hN : ((p ^ k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne (p ^ k))
  have hmain : ((p ^ k : ℕ) : ℂ) * kl (p ^ k) 1 b =
      ∑ u : (ZMod (p ^ k))ˣ, ZMod.stdAddChar (f u) * qsum (x * g u) (x ^ 2 * w u) := by
    have hsum : ((p ^ k : ℕ) : ℂ) * kl (p ^ k) 1 b = ∑ t : ZMod (p ^ k), kl (p ^ k) 1 b := by
      rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    rw [hsum]
    conv_lhs => rw [Finset.sum_congr rfl (fun t _ => hshift t)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [qsum, Finset.mul_sum]
  -- the bound on `Q`
  have h2u : IsUnit (2 : ZMod (p ^ k)) := by simpa using two_isUnit hp hp2 k
  have hQ : ∀ u : (ZMod (p ^ k))ˣ, ‖qsum (x * g u) (x ^ 2 * w u)‖ ≤
      if u ∈ F then Real.sqrt ((p : ℝ) ^ (2 * k - 1)) else 0 := by
    intro u
    have hwu : IsUnit (w u) := by
      simp only [w]; exact hb.mul (Units.isUnit _)
    -- reduce the inner condition
    have hcondh : ∀ h : ZMod (p ^ k), (2 * h * (x ^ 2 * w u) = 0 ↔ x ^ 2 * h = 0) := by
      intro h
      constructor
      · intro hh
        have : (x ^ 2 * h) * (2 * w u) = 0 := by linear_combination hh
        exact (h2u.mul hwu).mul_left_eq_zero.mp this
      · intro hh; linear_combination (2 * w u) * hh
    set A := x * g u
    set T : ℂ := ∑ h : ZMod (p ^ k), if x ^ 2 * h = 0 then ZMod.stdAddChar (h * A) else 0
    have hQT : ((‖qsum A (x ^ 2 * w u)‖ ^ 2 : ℝ) : ℂ) = ((p ^ k : ℕ) : ℂ) * T := by
      rw [qsum_normSq]
      congr 1
      refine Finset.sum_congr rfl (fun h _ => ?_)
      by_cases hh : x ^ 2 * h = 0
      · rw [if_pos ((hcondh h).mpr hh), if_pos hh]
        congr 1
        have : h ^ 2 * (x ^ 2 * w u) = h * w u * (x ^ 2 * h) := by ring
        rw [this, hh, mul_zero, add_zero]
      · rw [if_neg (fun h' => hh ((hcondh h).mp h')), if_neg hh]
    -- translation invariance by `p`
    have hTshift : ZMod.stdAddChar ((p : ZMod (p ^ k)) * A) * T = T := by
      simp only [T]
      rw [Finset.mul_sum]
      refine (Fintype.sum_equiv (Equiv.addRight (p : ZMod (p ^ k))) _ _ (fun h => ?_))
      simp only [Equiv.coe_addRight]
      have e : x ^ 2 * (h + p) = x ^ 2 * h := by linear_combination hx2p
      rw [e]
      split_ifs
      · rw [← AddChar.map_add_eq_mul]; congr 1; ring
      · simp
    have hTcard : ‖T‖ ≤ (p : ℝ) ^ (k - 1) := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ h : ZMod (p ^ k), ‖if x ^ 2 * h = 0 then ZMod.stdAddChar (h * A) else 0‖ ≤
          if x ^ 2 * h = 0 then (1 : ℝ) else 0 := by
        intro h; split_ifs <;> simp
      refine (Finset.sum_le_sum (fun h _ => this h)).trans ?_
      rw [Finset.sum_boole]
      have hc := card_ker_le hp k (by omega)
      simp only [← hxk1] at hc
      exact_mod_cast hc
    have hnormQ : ‖qsum A (x ^ 2 * w u)‖ ^ 2 = (p : ℝ) ^ k * ‖T‖ := by
      have := congrArg norm hQT
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_mul,
        Complex.norm_natCast] at this
      rw [this]; push_cast; ring
    by_cases hu : u ∈ F
    · rw [if_pos hu]
      refine Real.le_sqrt_of_sq_le ?_
      rw [hnormQ]
      calc (p : ℝ) ^ k * ‖T‖ ≤ (p : ℝ) ^ k * (p : ℝ) ^ (k - 1) := by gcongr
        _ = (p : ℝ) ^ (2 * k - 1) := by rw [← pow_add]; congr 1; omega
    · rw [if_neg hu]
      have hpA : (p : ZMod (p ^ k)) * A ≠ 0 := by
        intro h0
        apply hu
        rw [← hcond u]
        have : (p : ZMod (p ^ k)) ^ (j + 1) * g u = (p : ZMod (p ^ k)) * A := by
          simp only [A, x]; ring
        simpa [g] using this.trans h0
      have hne : ZMod.stdAddChar ((p : ZMod (p ^ k)) * A) ≠ 1 := by
        intro h1
        apply hpA
        rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := p ^ k))] at h1
        exact ZMod.injective_stdAddChar h1
      have hT0 : T = 0 := by
        have : (1 - ZMod.stdAddChar ((p : ZMod (p ^ k)) * A)) * T = 0 := by
          linear_combination -hTshift
        rcases mul_eq_zero.mp this with h | h
        · exact absurd (by linear_combination -h) hne
        · exact h
      have : ‖qsum A (x ^ 2 * w u)‖ ^ 2 = 0 := by rw [hnormQ, hT0, norm_zero, mul_zero]
      simpa using this
  -- assemble
  have hle : (p : ℝ) ^ k * ‖kl (p ^ k) 1 b‖ ≤
      (F.card : ℝ) * Real.sqrt ((p : ℝ) ^ (2 * k - 1)) := by
    have h0 := congrArg norm hmain
    rw [norm_mul, Complex.norm_natCast] at h0
    push_cast at h0
    rw [h0]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ u : (ZMod (p ^ k))ˣ, ‖ZMod.stdAddChar (f u) * qsum (x * g u) (x ^ 2 * w u)‖
        ≤ ∑ u : (ZMod (p ^ k))ˣ, (if u ∈ F then Real.sqrt ((p : ℝ) ^ (2 * k - 1)) else 0) := by
          refine Finset.sum_le_sum (fun u _ => ?_)
          rw [norm_mul, norm_stdAddChar, one_mul]; exact hQ u
      _ = (F.card : ℝ) * Real.sqrt ((p : ℝ) ^ (2 * k - 1)) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          have hfilt : Finset.univ.filter (fun u : (ZMod (p ^ k))ˣ => u ∈ F) = F := by
            ext u; simp
          rw [hfilt]
  -- numerics: `4 p^{j+1} √(p^{2k-1}) = 4 p^k √(p^k)`
  have hsq : (p : ℝ) ^ (j + 1) * Real.sqrt ((p : ℝ) ^ (2 * k - 1)) =
      (p : ℝ) ^ k * Real.sqrt ((p : ℝ) ^ k) := by
    have e1 : (p : ℝ) ^ (2 * k - 1) = ((p : ℝ) ^ j) ^ 2 * (p : ℝ) ^ k := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    have e2 : (p : ℝ) ^ k = (p : ℝ) ^ (j + 1) * (p : ℝ) ^ j := by
      rw [← pow_add]; congr 1; omega
    rw [e1, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    calc (p : ℝ) ^ (j + 1) * ((p : ℝ) ^ j * Real.sqrt ((p : ℝ) ^ k))
        = ((p : ℝ) ^ (j + 1) * (p : ℝ) ^ j) * Real.sqrt ((p : ℝ) ^ k) := by ring
      _ = _ := by rw [← e2]
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
  refine le_of_mul_le_mul_left ?_ hpk
  calc (p : ℝ) ^ k * ‖kl (p ^ k) 1 b‖ ≤ (F.card : ℝ) * Real.sqrt ((p : ℝ) ^ (2 * k - 1)) := hle
    _ ≤ (4 * (p : ℝ) ^ (j + 1)) * Real.sqrt ((p : ℝ) ^ (2 * k - 1)) := by
        gcongr; exact_mod_cast hFcard
    _ = (p : ℝ) ^ k * (4 * Real.sqrt ((p : ℝ) ^ k)) := by rw [mul_assoc, hsq]; ring

end RamanujanTau.WeilKloosterman
