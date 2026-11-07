/-
# Region A: the key inequality on a compact range `u ∈ [p₀/2^12, p₁/2^12]` by a kernel-checked cover

With `σ_i = σ_{Zs i}(x)`, `x = π e^{2u}`, the derivative of `R = −Φ'/(uΦ)` has the sign of
`QR u σ₀ σ₁ σ₂ = σ₀(2σ₁ − uσ₂) + uσ₁²`.  Splitting `σ_i = pe (Zs i) x + τ_i` (the `k = 1` term exactly)
gives `QR = Q0R u x + crossR …` where `Q0R u x = x²(32x³(2u−1) + 4x²(42−48u) + 240x(u−1) + 90)` is the
exact `k = 1` contribution (an explicit exponential polynomial) and `crossR` involves the tails `τ_i`
(enclosed by `tauIv`, two exact terms plus a geometric tail).  `cellA p q = true` certifies `QR > 0`
on `[p/2^12, q/2^12]` (**`cellA_sound`**), and **`coverA_sound`** chains cells.
-/
import RamanujanTau.GORZXiEff.CVSigma

set_option autoImplicit false

namespace GORZXiEff.CV

open Real Set Finset GORZXiEff JensenThreshold.Tail JensenThreshold.Tail.Iv

lemma Zs_two : Zs 2 = [0, -75, 330, -224, 32] := by decide

noncomputable def QR (u s0 s1 s2 : ℝ) : ℝ := s0 * (2 * s1 - u * s2) + u * s1 ^ 2

noncomputable def Q0R (u x : ℝ) : ℝ :=
  x ^ 2 * (32 * x ^ 3 * (2 * u - 1) + 4 * x ^ 2 * (42 - 48 * u) + 240 * x * (u - 1) + 90)

noncomputable def crossR (u P0 P1 P2 t0 t1 t2 : ℝ) : ℝ :=
  P0 * (2 * t1 - u * t2) + t0 * (2 * P1 - u * P2) + t0 * (2 * t1 - u * t2) + u * (2 * P1 * t1 + t1 ^ 2)

lemma QR_split (u x t0 t1 t2 : ℝ) :
    QR u (pe (Zs 0) x + t0) (pe (Zs 1) x + t1) (pe (Zs 2) x + t2) =
      Q0R u x + crossR u (pe (Zs 0) x) (pe (Zs 1) x) (pe (Zs 2) x) t0 t1 t2 := by
  rw [Zs_one, Zs_two]
  simp only [Zs, QR, Q0R, crossR, pe_cons, pe_nil]
  push_cast; ring

def Q0Iv (U X : Iv) : Iv :=
  X.pow 2 * (ofInt 32 * X.pow 3 * (ofInt 2 * U - oneI) + ofInt 4 * X.pow 2 * (ofInt 42 - ofInt 48 * U) +
    ofInt 240 * X * (U - oneI) + ofInt 90)

def crossIv (U P0 P1 P2 T0 T1 T2 : Iv) : Iv :=
  P0 * (ofInt 2 * T1 - U * T2) + T0 * (ofInt 2 * P1 - U * P2) + T0 * (ofInt 2 * T1 - U * T2) +
    U * (ofInt 2 * P1 * T1 + T1.pow 2)

lemma mem_ofNat' (n : ℕ) : ((n : ℤ) : ℝ) ∈ᵢ ofInt (n : ℤ) := mem_ofInt _

lemma mem_Q0Iv {u x : ℝ} {U X : Iv} (hu : u ∈ᵢ U) (hx : x ∈ᵢ X) : Q0R u x ∈ᵢ Q0Iv U X := by
  have h := mem_mul (mem_pow hx 2) (mem_add (mem_add (mem_add
    (mem_mul (mem_mul (mem_ofInt 32) (mem_pow hx 3)) (mem_sub (mem_mul (mem_ofInt 2) hu) mem_oneI))
    (mem_mul (mem_mul (mem_ofInt 4) (mem_pow hx 2)) (mem_sub (mem_ofInt 42) (mem_mul (mem_ofInt 48) hu))))
    (mem_mul (mem_mul (mem_ofInt 240) hx) (mem_sub hu mem_oneI))) (mem_ofInt 90))
  unfold Q0R Q0Iv
  convert h using 1

lemma mem_crossIv {u P0 P1 P2 t0 t1 t2 : ℝ} {U IP0 IP1 IP2 T0 T1 T2 : Iv} (hu : u ∈ᵢ U)
    (h0 : P0 ∈ᵢ IP0) (h1 : P1 ∈ᵢ IP1) (h2 : P2 ∈ᵢ IP2) (g0 : t0 ∈ᵢ T0) (g1 : t1 ∈ᵢ T1) (g2 : t2 ∈ᵢ T2) :
    crossR u P0 P1 P2 t0 t1 t2 ∈ᵢ crossIv U IP0 IP1 IP2 T0 T1 T2 := by
  have h := mem_add (mem_add (mem_add
    (mem_mul h0 (mem_sub (mem_mul (mem_ofInt 2) g1) (mem_mul hu g2)))
    (mem_mul g0 (mem_sub (mem_mul (mem_ofInt 2) h1) (mem_mul hu h2))))
    (mem_mul g0 (mem_sub (mem_mul (mem_ofInt 2) g1) (mem_mul hu g2))))
    (mem_mul hu (mem_add (mem_mul (mem_mul (mem_ofInt 2) h1) g1) (mem_pow g1 2)))
  unfold crossR crossIv
  convert h using 1

/-- the interval for `QR` on the cell `[p/2^12, q/2^12]`. -/
def QIvA (p q : ℤ) : Iv :=
  Q0Iv (uCell p q) (xCell p q) +
    crossIv (uCell p q) (peIv (Zs 0) (xCell p q)) (peIv (Zs 1) (xCell p q)) (peIv (Zs 2) (xCell p q))
      (tauIv (Zs 0) (xCell p q) 3) (tauIv (Zs 1) (xCell p q) 3) (tauIv (Zs 2) (xCell p q) 3)

def cellA (p q : ℤ) : Bool := decide (0 ≤ p) && decide (q ≤ 2 ^ 20) && decide (0 < (QIvA p q).lo)

lemma pi_gt_three' : (3 : ℝ) < π := pi_gt_three

lemma xOf_ge_three {u : ℝ} (hu : 0 ≤ u) : 3 ≤ xOf u := by
  unfold xOf
  have : 1 ≤ rexp (2 * u) := one_le_exp (by linarith)
  nlinarith [pi_gt_three]

/-- the geometric-tail condition for `k₁ = 3`, `x ≥ 3`, polynomials of length `≤ 5`. -/
lemma hcond3 {n : ℕ} (hn : n ≤ 5) :
    2 * ((((3 : ℕ) : ℝ) + 2) / (((3 : ℕ) : ℝ) + 1)) ^ (2 * n) ≤ rexp ((2 * ((3 : ℕ) : ℝ) + 3) * 3) := by
  have e1 : (((3 : ℕ) : ℝ) + 2) / (((3 : ℕ) : ℝ) + 1) = 5 / 4 := by norm_num
  have e2 : (2 * ((3 : ℕ) : ℝ) + 3) * 3 = 27 := by norm_num
  rw [e1, e2]
  have h1 : ((5 : ℝ) / 4) ^ (2 * n) ≤ (5 / 4) ^ 10 := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 := add_one_le_exp (27 : ℝ)
  have h3 : ((5 : ℝ) / 4) ^ 10 ≤ 10 := by norm_num
  linarith

lemma QR_pos_of_mem {u : ℝ} {I : Iv} (h : QR u (sig (Zs 0) (xOf u)) (sig (Zs 1) (xOf u)) (sig (Zs 2) (xOf u)) ∈ᵢ I)
    (hI : 0 < I.lo) : 0 < QR u (sig (Zs 0) (xOf u)) (sig (Zs 1) (xOf u)) (sig (Zs 2) (xOf u)) :=
  pos_of_mem h hI

theorem cellA_sound {p q : ℤ} (h : cellA p q = true) {u : ℝ} (hu1 : (p : ℝ) / 2 ^ 12 ≤ u)
    (hu2 : u ≤ (q : ℝ) / 2 ^ 12) :
    0 < QR u (sig (Zs 0) (xOf u)) (sig (Zs 1) (xOf u)) (sig (Zs 2) (xOf u)) := by
  simp only [cellA, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hp, hq⟩, hpos⟩ := h
  have hu0 : 0 ≤ u := le_trans (by positivity) hu1
  have hX := mem_xCell hp hq hu1 hu2
  have hU := mem_uCell hu1 hu2
  have hx3 := xOf_ge_three hu0
  have hxp := xOf_pos u
  have hlen : ∀ i ≤ 2, (Zs i).length ≤ 5 := by decide
  have ht : ∀ i ≤ 2, (sig (Zs i) (xOf u) - pe (Zs i) (xOf u)) ∈ᵢ tauIv (Zs i) (xCell p q) 3 :=
    fun i hi => mem_tauIv (Zs i) (by norm_num) hx3 hX 3 (by norm_num) (hcond3 (hlen i hi)) hxp
  have key := mem_add (mem_Q0Iv hU hX) (mem_crossIv hU (mem_peIv hX (Zs 0)) (mem_peIv hX (Zs 1))
    (mem_peIv hX (Zs 2)) (ht 0 (by norm_num)) (ht 1 (by norm_num)) (ht 2 (by norm_num)))
  rw [← QR_split] at key
  simp only [add_sub_cancel] at key
  exact pos_of_mem key hpos

/-! ## chaining cells -/

def allCells (cell : ℤ → ℤ → Bool) : List ℤ → Bool
  | a :: b :: rest => cell a b && allCells cell (b :: rest)
  | _ => true

def lastZ : ℤ → List ℤ → ℤ
  | b, [] => b
  | _, c :: r => lastZ c r

theorem cover_sound {P : ℝ → Prop} (cell : ℤ → ℤ → Bool)
    (hcell : ∀ p q, cell p q = true → ∀ u : ℝ, (p : ℝ) / 2 ^ 12 ≤ u → u ≤ (q : ℝ) / 2 ^ 12 → P u) :
    ∀ (rest : List ℤ) (a b : ℤ), allCells cell (a :: b :: rest) = true → ∀ u : ℝ,
      (a : ℝ) / 2 ^ 12 ≤ u → u ≤ (lastZ b rest : ℝ) / 2 ^ 12 → P u := by
  intro rest
  induction rest with
  | nil =>
    intro a b h u h1 h2
    simp only [allCells, Bool.and_true] at h
    exact hcell a b h u h1 h2
  | cons c r ih =>
    intro a b h u h1 h2
    rw [allCells, Bool.and_eq_true] at h
    by_cases hb : u ≤ (b : ℝ) / 2 ^ 12
    · exact hcell a b h.1 u h1 hb
    · exact ih b c h.2 u (le_of_lt (not_le.1 hb)) h2

end GORZXiEff.CV
