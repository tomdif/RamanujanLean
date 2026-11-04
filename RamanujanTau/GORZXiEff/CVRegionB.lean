/-
# Region B: the key inequality near `u = 0` by an even Taylor model

Near `0` every term of `Φ = Σ_k φ_k` contributes `≍ 1/u` to `R = −Φ'/(uΦ)`, and the cancellation comes from
the evenness of `Φ` (`Phi_odd_zero`).  With `c_i = Φ^{(i)}(0)` (`c_odd = 0`) and `|Φ^{(10)}| ≤ M` on
`[0, u₀]` (`u₀ = 737/2^12`), Taylor's theorem (`JensenThreshold.Tail.taylor_bounds`) gives
`Φ = Ph(u)`, `Φ' = u V(u)`, `Φ' − uΦ'' = u³ W(u)` with explicit even polynomials plus `θ_i u^j` remainders,
so `G := Φ(Φ' − uΦ'') + uΦ'² = u³ (Ph·W + V²)`.  The constants `c_i` and the bound `M` are certified
by interval arithmetic (`cB_mem`, `cellM_sound`), and `Ph·W + V² > 0` by a cover (`cellB_sound`).
-/
import RamanujanTau.GORZXiEff.CVRegionA
import RamanujanTau.GORZXiEff.CVEven
import RamanujanTau.JensenThreshold.Tail.Calculus

set_option autoImplicit false

namespace GORZXiEff.CV

open Real Set Finset GORZXiEff JensenThreshold.Tail JensenThreshold.Tail.Iv

/-! ## `e^{t/2}` on a cell, and `Φ^{(i)}` on a cell -/

def halfZ (p : ℤ) : ℤ := p * 2 ^ 179

def hCell (p q : ℤ) : Iv := ⟨(expPt (halfZ p)).lo, (expPt (halfZ q)).hi⟩

lemma mem_hCell {p q : ℤ} (hp : 0 ≤ p) (hq : q ≤ 2 ^ 20) {u : ℝ} (hu1 : (p : ℝ) / 2 ^ 12 ≤ u)
    (hu2 : u ≤ (q : ℝ) / 2 ^ 12) : rexp (u / 2) ∈ᵢ hCell p q := by
  have hpq : p ≤ q := by
    have := le_trans hu1 hu2
    have : (p : ℝ) ≤ q := by rwa [div_le_div_iff_of_pos_right (by positivity)] at this
    exact_mod_cast this
  have hB : ∀ r : ℤ, 0 ≤ r → r ≤ 2 ^ 20 → halfZ r ≤ BE := by
    intro r h0 h1; unfold halfZ BE S mE; nlinarith
  have m1 := mem_expPt (by unfold halfZ; positivity) (hB p hp (by omega))
  have m2 := mem_expPt (by unfold halfZ; omega) (hB q (by omega) hq)
  have e : ∀ r : ℤ, ((halfZ r : ℤ) : ℝ) / S = ((r : ℝ) / 2 ^ 12) / 2 := by
    intro r; unfold halfZ S; push_cast; field_simp; ring
  rw [e] at m1 m2
  exact ⟨le_trans m1.1 (exp_le_exp.2 (by linarith)), le_trans (exp_le_exp.2 (by linarith)) m2.2⟩

/-- the geometric-tail condition for `k₁ = 7`, `x ≥ 3`, polynomials of length `≤ 13`. -/
lemma hcond7 {n : ℕ} (hn : n ≤ 13) :
    2 * ((((7 : ℕ) : ℝ) + 2) / (((7 : ℕ) : ℝ) + 1)) ^ (2 * n) ≤ rexp ((2 * ((7 : ℕ) : ℝ) + 3) * 3) := by
  have e1 : (((7 : ℕ) : ℝ) + 2) / (((7 : ℕ) : ℝ) + 1) = 9 / 8 := by norm_num
  have e2 : (2 * ((7 : ℕ) : ℝ) + 3) * 3 = 51 := by norm_num
  rw [e1, e2]
  have h1 : ((9 : ℝ) / 8) ^ (2 * n) ≤ (9 / 8) ^ 26 := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 := add_one_le_exp (51 : ℝ)
  have h3 : ((9 : ℝ) / 8) ^ 26 ≤ 22 := by norm_num
  linarith

lemma Zs_len (i : ℕ) : (Zs i).length = i + 3 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have : ∀ l : List ℤ, l ≠ [] → (stepZ l).length = l.length + 1 := by
      intro l hl
      have hA : ∀ a b : List ℤ, (addL a b).length = max a.length b.length := by
        intro a b
        induction a generalizing b with
        | nil => simp [addL]
        | cons x a iha =>
          cases b with
          | nil => simp [addL]
          | cons y b => simp [addL, iha]
      have hD : ∀ a : List ℤ, (dL a).length ≤ a.length := by
        intro a
        induction a with
        | nil => simp [dL]
        | cons x a iha => simp only [dL, hA, List.length_cons]; omega
      simp only [stepZ, hA, List.length_cons, smulL, List.length_map]
      have := hD l
      omega
    rw [Zs, this (Zs i) (by rw [← List.length_pos_iff, ih]; omega), ih]

/-- the lists `Zs i` (`i ≤ 10`) as literals (so that the kernel does not recompute `stepZ`). -/
def Zl : ℕ → List ℤ
  | 0 => [0, -3, 2]
  | 1 => [0, -15, 30, -8]
  | 2 => [0, -75, 330, -224, 32]
  | 3 => [0, -375, 3270, -4232, 1440, -128]
  | 4 => [0, -1875, 30930, -68096, 41408, -8448, 512]
  | 5 => [0, -9375, 285870, -1008968, 976320, -343040, 46592, -2048]
  | 6 => [0, -46875, 2610330, -14260064, 20633312, -11109120, 2536960, -245760, 8192]
  | 7 => [0, -234375, 23680470, -195822152, 407806560, -315824768, 107860480, -17274880, 1253376, -32768]
  | 8 => [0, -1171875, 214061730, -2640409856, 7716000128, -8263546368, 3959811072, -932413440, 110460928, -6225920, 131072]
  | 9 => [0, -5859375, 1931243070, -35181575048, 141733641600, -204398474240, 132049462272, -42879234048, 7374864384, -672202752, 30277632, -524288]
  | 10 => [0, -29296875, 17404625130, -465085447904, 2550198207392, -4859302525440, 4118830453760, -1771695636480, 414887460864, -54370959360, 3930193920, -144703488, 2097152]
  | _ => []

lemma Zs_eq_Zl {i : ℕ} (hi : i ≤ 10) : Zs i = Zl i := by
  have h : ∀ i < 10, stepZ (Zl i) = Zl (i + 1) := by decide
  induction i with
  | zero => rfl
  | succ i ih => rw [Zs, ih (by omega), h i (by omega)]

/-- enclosure of `Φ^{(i)}(t)` on the cell `[p/2^12, q/2^12]`. -/
def phiIvB (i : ℕ) (p q : ℤ) : Iv :=
  hCell p q * expNeg (xCell p q) * sigIv (Zl i) (xCell p q) 7 * ofFrac 1 (2 ^ i)

lemma Phi_eq_sig (i : ℕ) (u : ℝ) :
    Phi i u = rexp (u / 2) * rexp (-xOf u) * sig (Zs i) (xOf u) * ((1 : ℤ) / ((2 ^ i : ℤ) : ℝ)) := by
  unfold Phi; rw [Ser_eq_sig]; push_cast; ring

theorem mem_phiIvB {i : ℕ} (hi : i ≤ 10) {p q : ℤ} (hp : 0 ≤ p) (hq : q ≤ 2 ^ 20) {u : ℝ}
    (hu1 : (p : ℝ) / 2 ^ 12 ≤ u) (hu2 : u ≤ (q : ℝ) / 2 ^ 12) : Phi i u ∈ᵢ phiIvB i p q := by
  have hu0 : 0 ≤ u := le_trans (by positivity) hu1
  have hX := mem_xCell hp hq hu1 hu2
  rw [Phi_eq_sig, Zs_eq_Zl hi]
  exact mem_mul (mem_mul (mem_mul (mem_hCell hp hq hu1 hu2) (mem_expNeg (xOf_pos u).le hX))
    (mem_sigIv (Zl i) (by norm_num) (xOf_ge_three hu0) hX 7
      (hcond7 (by rw [← Zs_eq_Zl hi, Zs_len]; omega)) (xOf_pos u)))
    (mem_ofFrac 1 (2 ^ i) (by positivity))

/-- enclosure of `c_i = Φ^{(i)}(0)`. -/
def cB (i : ℕ) : Iv := expNeg piIv * sigIv (Zl i) piIv 7 * ofFrac 1 (2 ^ i)

theorem mem_cB {i : ℕ} (hi : i ≤ 10) : Phi i 0 ∈ᵢ cB i := by
  have hx : xOf 0 = π := by simp [xOf]
  rw [Phi_eq_sig, hx, Zs_eq_Zl hi]
  have h := mem_mul (mem_mul (mem_expNeg pi_pos.le mem_piIv)
    (mem_sigIv (Zl i) (by norm_num) pi_gt_three.le mem_piIv 7
      (hcond7 (by rw [← Zs_eq_Zl hi, Zs_len]; omega)) pi_pos))
    (mem_ofFrac 1 (2 ^ i) (by positivity))
  convert h using 1; simp

/-! ## the bound on `Φ^{(10)}` -/

/-- `M = 8·10⁹`. -/
def Mb : ℤ := 8000000000

def cellM (p q : ℤ) : Bool :=
  decide (0 ≤ p) && decide (q ≤ 2 ^ 20) && decide (-Mb * S ≤ (phiIvB 10 p q).lo) &&
    decide ((phiIvB 10 p q).hi ≤ Mb * S)

theorem cellM_sound {p q : ℤ} (h : cellM p q = true) (u : ℝ) (hu1 : (p : ℝ) / 2 ^ 12 ≤ u)
    (hu2 : u ≤ (q : ℝ) / 2 ^ 12) : -(Mb : ℝ) ≤ Phi 10 u ∧ Phi 10 u ≤ Mb := by
  simp only [cellM, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hp, hq⟩, h1⟩, h2⟩ := h
  have hm := mem_phiIvB le_rfl hp hq hu1 hu2
  have hS := S_posR
  constructor
  · have : ((-Mb * S : ℤ) : ℝ) / S ≤ ((phiIvB 10 p q).lo : ℝ) / S :=
      div_le_div_of_nonneg_right (by exact_mod_cast h1) hS.le
    have e : ((-Mb * S : ℤ) : ℝ) / S = -(Mb : ℝ) := by push_cast; field_simp
    linarith [hm.1]
  · have : ((phiIvB 10 p q).hi : ℝ) / S ≤ ((Mb * S : ℤ) : ℝ) / S :=
      div_le_div_of_nonneg_right (by exact_mod_cast h2) hS.le
    have e : ((Mb * S : ℤ) : ℝ) / S = (Mb : ℝ) := by push_cast; field_simp
    linarith [hm.2]

/-! ## the Taylor model -/

def fct (n : ℕ) : ℤ := (Nat.factorial n : ℤ)

def IMb : Iv := ⟨-Mb * S, Mb * S⟩

lemma mem_IMb {θ : ℝ} (h1 : -(Mb : ℝ) ≤ θ) (h2 : θ ≤ Mb) : θ ∈ᵢ IMb := by
  have hS := S_posR
  unfold IMb Iv.mem
  constructor
  · have e : ((-Mb * S : ℤ) : ℝ) / S = -(Mb : ℝ) := by push_cast; field_simp
    rw [e]; exact h1
  · have e : ((Mb * S : ℤ) : ℝ) / S = (Mb : ℝ) := by push_cast; field_simp
    rw [e]; exact h2

def gBIv (C0 C2 C4 C6 C8 IM U : Iv) : Iv :=
  (C0 + C2 * U.pow 2 * ofFrac 1 2 + C4 * U.pow 4 * ofFrac 1 24 + C6 * U.pow 6 * ofFrac 1 720 +
    C8 * U.pow 8 * ofFrac 1 40320 + IM * (U.pow 10 * ofFrac 1 (fct 10))) *
  (C4 * ofFrac (-1) 3 + C6 * U.pow 2 * ofFrac (-1) 30 + C8 * U.pow 4 * ofFrac (-1) 840 +
    IM * (U.pow 6 * ofFrac 1 (fct 9)) - IM * (U.pow 6 * ofFrac 1 (fct 8))) +
  (C2 + C4 * U.pow 2 * ofFrac 1 6 + C6 * U.pow 4 * ofFrac 1 120 + C8 * U.pow 6 * ofFrac 1 5040 +
    IM * (U.pow 8 * ofFrac 1 (fct 9))) *
  (C2 + C4 * U.pow 2 * ofFrac 1 6 + C6 * U.pow 4 * ofFrac 1 120 + C8 * U.pow 6 * ofFrac 1 5040 +
    IM * (U.pow 8 * ofFrac 1 (fct 9)))

noncomputable def gBR (c0 c2 c4 c6 c8 θ0 θ1 θ2 u : ℝ) : ℝ :=
  (c0 + c2 * u ^ 2 * (1 / 2) + c4 * u ^ 4 * (1 / 24) + c6 * u ^ 6 * (1 / 720) +
    c8 * u ^ 8 * (1 / 40320) + θ0 * (u ^ 10 * (1 / (Nat.factorial 10 : ℝ)))) *
  (c4 * (-1 / 3) + c6 * u ^ 2 * (-1 / 30) + c8 * u ^ 4 * (-1 / 840) +
    θ1 * (u ^ 6 * (1 / (Nat.factorial 9 : ℝ))) - θ2 * (u ^ 6 * (1 / (Nat.factorial 8 : ℝ)))) +
  (c2 + c4 * u ^ 2 * (1 / 6) + c6 * u ^ 4 * (1 / 120) + c8 * u ^ 6 * (1 / 5040) +
    θ1 * (u ^ 8 * (1 / (Nat.factorial 9 : ℝ)))) ^ 2

lemma mem_fr (p q : ℤ) (hq : 0 < q) : ((p : ℝ) / q) ∈ᵢ ofFrac p q := mem_ofFrac p q hq

lemma mem_gBIv {c0 c2 c4 c6 c8 θ0 θ1 θ2 u : ℝ} {C0 C2 C4 C6 C8 U : Iv}
    (h0 : c0 ∈ᵢ C0) (h2 : c2 ∈ᵢ C2) (h4 : c4 ∈ᵢ C4) (h6 : c6 ∈ᵢ C6) (h8 : c8 ∈ᵢ C8)
    (g0 : θ0 ∈ᵢ IMb) (g1 : θ1 ∈ᵢ IMb) (g2 : θ2 ∈ᵢ IMb) (hu : u ∈ᵢ U) :
    gBR c0 c2 c4 c6 c8 θ0 θ1 θ2 u ∈ᵢ gBIv C0 C2 C4 C6 C8 IMb U := by
  have f10 := mem_fr 1 (fct 10) (by unfold fct; positivity)
  have f9 := mem_fr 1 (fct 9) (by unfold fct; positivity)
  have f8 := mem_fr 1 (fct 8) (by unfold fct; positivity)
  have hV := mem_add (mem_add (mem_add (mem_add h2 (mem_mul (mem_mul h4 (mem_pow hu 2)) (mem_fr 1 6 (by norm_num))))
      (mem_mul (mem_mul h6 (mem_pow hu 4)) (mem_fr 1 120 (by norm_num))))
      (mem_mul (mem_mul h8 (mem_pow hu 6)) (mem_fr 1 5040 (by norm_num))))
      (mem_mul g1 (mem_mul (mem_pow hu 8) f9))
  have hP := mem_add (mem_add (mem_add (mem_add (mem_add h0
      (mem_mul (mem_mul h2 (mem_pow hu 2)) (mem_fr 1 2 (by norm_num))))
      (mem_mul (mem_mul h4 (mem_pow hu 4)) (mem_fr 1 24 (by norm_num))))
      (mem_mul (mem_mul h6 (mem_pow hu 6)) (mem_fr 1 720 (by norm_num))))
      (mem_mul (mem_mul h8 (mem_pow hu 8)) (mem_fr 1 40320 (by norm_num))))
      (mem_mul g0 (mem_mul (mem_pow hu 10) f10))
  have hW := mem_sub (mem_add (mem_add (mem_add (mem_mul h4 (mem_fr (-1) 3 (by norm_num)))
      (mem_mul (mem_mul h6 (mem_pow hu 2)) (mem_fr (-1) 30 (by norm_num))))
      (mem_mul (mem_mul h8 (mem_pow hu 4)) (mem_fr (-1) 840 (by norm_num))))
      (mem_mul g1 (mem_mul (mem_pow hu 6) f9)))
      (mem_mul g2 (mem_mul (mem_pow hu 6) f8))
  have h := mem_add (mem_mul hP hW) (mem_mul hV hV)
  unfold gBR gBIv
  convert h using 1
  simp only [fct]; push_cast; ring

/-- `θ` with `ρ = θ w`, `|θ| ≤ M`. -/
lemma exists_theta {ρ w M : ℝ} (hw : 0 ≤ w) (hM : 0 ≤ M) (h1 : -M * w ≤ ρ) (h2 : ρ ≤ M * w) :
    ∃ θ, -M ≤ θ ∧ θ ≤ M ∧ ρ = θ * w := by
  rcases hw.lt_or_eq with hw | hw
  · refine ⟨ρ / w, ?_, ?_, by field_simp⟩
    · rw [le_div_iff₀ hw]; linarith
    · rw [div_le_iff₀ hw]; linarith
  · subst hw
    refine ⟨0, by linarith, hM, ?_⟩
    have : ρ = 0 := by nlinarith
    simp [this]

def u0B : ℤ := 737

/-- the key quantity `G = Φ(Φ' − uΦ'') + uΦ'²` (`R' = G/(uΦ)²`). -/
noncomputable def Gfun (u : ℝ) : ℝ := Phi 0 u * (Phi 1 u - u * Phi 2 u) + u * Phi 1 u ^ 2

theorem G_eq_gBR (hM : ∀ t, 0 ≤ t → t ≤ (u0B : ℝ) / 2 ^ 12 → -(Mb : ℝ) ≤ Phi 10 t ∧ Phi 10 t ≤ Mb)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ (u0B : ℝ) / 2 ^ 12) :
    ∃ θ0 θ1 θ2 : ℝ, θ0 ∈ᵢ IMb ∧ θ1 ∈ᵢ IMb ∧ θ2 ∈ᵢ IMb ∧
      Gfun u = u ^ 3 * gBR (Phi 0 0) (Phi 2 0) (Phi 4 0) (Phi 6 0) (Phi 8 0) θ0 θ1 θ2 u := by
  have hMp : (0 : ℝ) ≤ Mb := by unfold Mb; norm_num
  have hd : ∀ i, ∀ t, 0 ≤ t → HasDerivAt (Phi i) (Phi (i + 1) t) t := fun i t _ => hasDerivAt_Phi i t
  have hb0 := taylor_bounds (fun i => Phi i) 10 (fun i _ t ht => hd i t ht) hM hu0 hu
  have hb1 := taylor_bounds (fun i => Phi (i + 1)) 9 (fun i _ t ht => hd (i + 1) t ht) hM hu0 hu
  have hb2 := taylor_bounds (fun i => Phi (i + 2)) 8 (fun i _ t ht => hd (i + 2) t ht) hM hu0 hu
  have z1 : Phi 1 0 = 0 := Phi_odd_zero 0
  have z3 : Phi 3 0 = 0 := Phi_odd_zero 1
  have z5 : Phi 5 0 = 0 := Phi_odd_zero 2
  have z7 : Phi 7 0 = 0 := Phi_odd_zero 3
  have z9 : Phi 9 0 = 0 := Phi_odd_zero 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hb0 hb1 hb2
  norm_num [z1, z3, z5, z7, z9, Nat.factorial] at hb0 hb1 hb2
  obtain ⟨θ0, a0, b0, e0⟩ := exists_theta (w := u ^ 10 * (1 / (Nat.factorial 10 : ℝ)))
    (ρ := Phi 0 u - (Phi 0 0 + Phi 2 0 * u ^ 2 / 2 + Phi 4 0 * u ^ 4 / 24 + Phi 6 0 * u ^ 6 / 720 +
      Phi 8 0 * u ^ 8 / 40320)) (by positivity) hMp
    (by norm_num [Nat.factorial]; linarith [hb0.1]) (by norm_num [Nat.factorial]; linarith [hb0.2])
  obtain ⟨θ1, a1, b1, e1⟩ := exists_theta (w := u ^ 9 * (1 / (Nat.factorial 9 : ℝ)))
    (ρ := Phi 1 u - (Phi 2 0 * u + Phi 4 0 * u ^ 3 / 6 + Phi 6 0 * u ^ 5 / 120 + Phi 8 0 * u ^ 7 / 5040))
    (by positivity) hMp
    (by norm_num [Nat.factorial]; linarith [hb1.1]) (by norm_num [Nat.factorial]; linarith [hb1.2])
  obtain ⟨θ2, a2, b2, e2⟩ := exists_theta (w := u ^ 8 * (1 / (Nat.factorial 8 : ℝ)))
    (ρ := Phi 2 u - (Phi 2 0 + Phi 4 0 * u ^ 2 / 2 + Phi 6 0 * u ^ 4 / 24 + Phi 8 0 * u ^ 6 / 720))
    (by positivity) hMp
    (by norm_num [Nat.factorial]; linarith [hb2.1]) (by norm_num [Nat.factorial]; linarith [hb2.2])
  refine ⟨θ0, θ1, θ2, mem_IMb a0 b0, mem_IMb a1 b1, mem_IMb a2 b2, ?_⟩
  have E0 : Phi 0 u = Phi 0 0 + Phi 2 0 * u ^ 2 / 2 + Phi 4 0 * u ^ 4 / 24 + Phi 6 0 * u ^ 6 / 720 +
      Phi 8 0 * u ^ 8 / 40320 + θ0 * (u ^ 10 * (1 / (Nat.factorial 10 : ℝ))) := by
    linarith [e0]
  have E1 : Phi 1 u = Phi 2 0 * u + Phi 4 0 * u ^ 3 / 6 + Phi 6 0 * u ^ 5 / 120 + Phi 8 0 * u ^ 7 / 5040 +
      θ1 * (u ^ 9 * (1 / (Nat.factorial 9 : ℝ))) := by
    linarith [e1]
  have E2 : Phi 2 u = Phi 2 0 + Phi 4 0 * u ^ 2 / 2 + Phi 6 0 * u ^ 4 / 24 + Phi 8 0 * u ^ 6 / 720 +
      θ2 * (u ^ 8 * (1 / (Nat.factorial 8 : ℝ))) := by
    linarith [e2]
  unfold Gfun gBR
  rw [E0, E1, E2]
  norm_num [Nat.factorial]
  ring

/-! ## the cover cells -/

def cellB (p q : ℤ) : Bool :=
  decide (0 ≤ p) && decide (q ≤ u0B) &&
    decide (0 < (gBIv (cB 0) (cB 2) (cB 4) (cB 6) (cB 8) IMb (uCell p q)).lo)

theorem cellB_sound (hM : ∀ t, 0 ≤ t → t ≤ (u0B : ℝ) / 2 ^ 12 → -(Mb : ℝ) ≤ Phi 10 t ∧ Phi 10 t ≤ Mb)
    {p q : ℤ} (h : cellB p q = true) (u : ℝ) (hu1 : (p : ℝ) / 2 ^ 12 ≤ u)
    (hu2 : u ≤ (q : ℝ) / 2 ^ 12) (hu : 0 < u) : 0 < Gfun u := by
  simp only [cellB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hp, hq⟩, hpos⟩ := h
  have hq' : (q : ℝ) ≤ u0B := by exact_mod_cast hq
  have huB : u ≤ (u0B : ℝ) / 2 ^ 12 := le_trans hu2 (by gcongr)
  obtain ⟨θ0, θ1, θ2, g0, g1, g2, hG⟩ := G_eq_gBR hM hu.le huB
  have hm := mem_gBIv (mem_cB (i := 0) (by norm_num)) (mem_cB (i := 2) (by norm_num))
    (mem_cB (i := 4) (by norm_num)) (mem_cB (i := 6) (by norm_num)) (mem_cB (i := 8) (by norm_num))
    g0 g1 g2 (mem_uCell hu1 hu2)
  rw [hG]
  exact mul_pos (pow_pos hu 3) (pos_of_mem hm hpos)

end GORZXiEff.CV
