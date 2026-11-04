/-
# Soundness of the box intervals, part 2: `γ_k`, `G(x)`, and hyperbolicity

**`box_sound`** : if `checkBox d K N B = true`, the Newton identity holds in degree `d`, and
`t₀ = U(n)^{-1/2} ∈ [B.tl, B.th]` with `n ≥ 2`, then `J^{d,n}` is hyperbolic.
-/
import RamanujanTau.JensenThreshold.Tail.Box1
import RamanujanTau.JensenThreshold.Basic

set_option autoImplicit false

namespace JensenThreshold.Tail

open Real Iv Finset Rademacher Polynomial

/-- The Newton forward-difference identity in degree `d`. -/
def NewtonId (d : ℕ) : Prop := ∀ (w : ℕ → ℝ) (Z : ℝ),
  ∑ j ∈ range (d + 1), (d.choose j : ℝ) * w j * (Z - 1) ^ j =
    ∑ k ∈ range (d + 1), (d.choose k : ℝ) * (∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * w j) *
      (Z - 1) ^ k * Z ^ (d - k)

noncomputable def wv (n j : ℕ) : ℝ := (pc (n + j) : ℝ) * Real.exp (-(Av (uk 1 n)) * j) / Mmain n
noncomputable def εv (n j : ℕ) : ℝ := (pc (n + j) : ℝ) / Mmain (n + j) - 1
noncomputable def Δv (n k : ℕ) : ℝ := ∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * wv n j
noncomputable def gamv (n k : ℕ) : ℝ := Δv n k / δv (uk 1 n) ^ k

lemma Dki_cast (k i : ℕ) : (Dki k i : ℝ) = ∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * (j : ℝ) ^ i := by
  unfold Dki
  rw [sum_range_eq_list]
  induction (List.range (k + 1)) with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons]; push_cast at ih ⊢; rw [ih]

lemma CjK_cast (k K : ℕ) : (CjK k K : ℝ) = ∑ j ∈ range (k + 1), (k.choose j : ℝ) * (j : ℝ) ^ K := by
  unfold CjK
  rw [sum_range_eq_list]
  induction (List.range (k + 1)) with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons]; push_cast at ih ⊢; rw [ih]

section
variable {d K N : ℕ} {B : BoxD} (hB : BoxOK d K N B) {n : ℕ} (hn : 2 ≤ n) (hU0 : 1 < uk 1 n)
  (ht : t0v (uk 1 n) ∈ᵢ bIt B)
include hB hn hU0 ht

lemma hU_n (j : ℕ) : 1 < uk 1 (n + j) := by
  rw [← Us_uk (by omega) j hU0]; exact one_lt_Us hU0 (by positivity)

lemma wv_eq (j : ℕ) : wv n j = Real.exp (φv (uk 1 n) 0 j) * (1 + εv n j) := by
  have hj := hU_n hB hn hU0 ht j
  have h0 : 1 < uk 1 (n + 0) := by simpa using hU0
  unfold wv εv φv
  simp only [if_true]
  have e1 : fch (uk 1 n) 0 (j : ℝ) = Fn (uk 1 (n + j)) := by
    simp [fch, Us_uk (by omega) j hU0]
  have e0 : fch (uk 1 n) 0 0 = Fn (uk 1 n) := by simp [fch, Us_zero hU0]
  rw [e1, e0, Real.exp_sub, Real.exp_sub, Mmain_eq_exp hj, Mmain_eq_exp hU0]
  have hK := Kc_pos
  have : Real.exp (Av (uk 1 n) * j) = (Real.exp (-(Av (uk 1 n)) * j))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [this]
  field_simp
  ring

lemma g_le_one (j : ℕ) (hj : j ≤ d) : Real.exp (φv (uk 1 n) 0 j) ≤ 1 := by
  have h := m_Phis hB hU0 ht 0 (by omega) (j : ℝ) (by positivity) (by exact_mod_cast hj)
  have := nonpos_of_mem h hB.phi0
  simp only [Φv, pow_zero, div_one] at this
  exact Real.exp_le_one_iff.mpr this

/-- Taylor remainder for `g = e^φ` at the nodes. -/
lemma taylor_g (j : ℕ) (hj : j ≤ d) :
    |Real.exp (φv (uk 1 n) 0 j) - ∑ i ∈ range K, gs (φv (uk 1 n)) i 0 * (j : ℝ) ^ i / (i.factorial : ℝ)| ≤
      (bMK d K B : ℝ) / S * δv (uk 1 n) ^ K * (j : ℝ) ^ K / (K.factorial : ℝ) := by
  set U0 := uk 1 n
  have hq2 := okQ2 hB
  have hc := c2v_pos hB hU0 ht
  have hδ := δv_pos hU0 hq2 hc
  have hchain : ∀ i < K, ∀ t, 0 ≤ t → HasDerivAt (gs (φv U0) i) (gs (φv U0) (i + 1) t) t :=
    fun i hi t ht' => gs_hasDerivAt (φv U0) (K + 1) (fun i _ t ht => φv_chain hU0 i ht) i (by omega) t ht'
  set M := (bMK d K B : ℝ) / S * δv U0 ^ K
  have hb : ∀ t, 0 ≤ t → t ≤ (d : ℝ) → -M ≤ gs (φv U0) K t ∧ gs (φv U0) K t ≤ M := by
    intro t h1 h2
    have hg := m_gs hB hU0 ht h1 h2
    have hs := gs_scale (φv U0) hδ.ne' K t
    have e : gs (φv U0) K t = gs (Φv U0) K t * δv U0 ^ K := by
      have : gs (Φv U0) K t = gs (fun i t => φv U0 i t / δv U0 ^ i) K t := rfl
      rw [this, hs]; field_simp
    rw [e]
    have hp : 0 < δv U0 ^ K := by positivity
    have := abs_le.mp hg
    constructor <;> nlinarith [this.1, this.2]
  have := taylor_bounds (gs (φv U0)) K hchain hb (x := (j : ℝ)) (by positivity) (by exact_mod_cast hj)
  rw [gs_zero] at this
  simp only [neg_mul, neg_div] at this
  rw [abs_le]
  exact ⟨this.1, this.2⟩


lemma eps_basic (j : ℕ) :
    |εv n j| ≤ 2 * uk 1 (n + j) ^ 3 / (uk 1 (n + j) - 1) * Real.exp (-(uk 1 (n + j) / 2)) := by
  have := rel_err (m := n + j) (by omega) (hU_n hB hn hU0 ht j)
  simpa [εv, pc, HardyRamanujan.p] using this

/-- the uniform bound on `2^k |ε|/δ^k`. -/
lemma eps_scaled (hth2 : t0v (uk 1 n) ≤ (B.thp : ℝ) / B.thq) (k : ℕ) (hk : k ≤ d) (j : ℕ) (hj : j ≤ k) :
    2 ^ k * |εv n j| / δv (uk 1 n) ^ k ≤ (bEk d N B k : ℝ) / S := by
  set U0 := uk 1 n
  have hq2 := okQ2 hB
  have hc := c2v_pos hB hU0 ht
  have hδ := δv_pos hU0 hq2 hc
  have hj' : (j : ℝ) ≤ d := by exact_mod_cast (le_trans hj hk)
  have hUj : uk 1 (n + j) = Us U0 j := (Us_uk (by omega) j hU0).symm
  have hUj1 : 1 < uk 1 (n + j) := hU_n hB hn hU0 ht j
  have hUjge : U0 ≤ uk 1 (n + j) := by rw [hUj]; exact U0_le_Us hU0 (by positivity)
  have heps := eps_basic hB hn hU0 ht j
  have hδk : 0 < δv U0 ^ k := by positivity
  unfold bEk
  split_ifs with hfin
  · -- finite box
    obtain ⟨hU01, hexp, hdel, hu0⟩ := hB.fin hfin
    set ρ := Real.sqrt (1 + aC * d * t0v U0 ^ 4)
    have hρ := m_rho hB hU0 ht (d := d)
    have hUjle : uk 1 (n + j) ≤ U0 * ρ := by rw [hUj]; exact Us_le_rho hB hU0 ht (by positivity) hj'
    set Sx := ∑ i ∈ range N, (U0 / 2) ^ i / (i.factorial : ℝ)
    have hSmem : Sx ∈ᵢ bIexps N B := by
      unfold bIexps
      apply mem_sumIv
      intro i _
      have hU0m : U0 ∈ᵢ bIU0 B := by
        have := mem_inv (m_u0 hB hU0 ht) hu0; simpa using this
      have := mem_powFact (mem_mul hU0m (mem_ofFrac 1 2 (by norm_num))) i
      convert this using 2; push_cast; ring
    have hSpos : 0 < Sx := pos_of_mem hSmem hexp
    have hexpb : Real.exp (-(uk 1 (n + j) / 2)) ≤ Sx⁻¹ := by
      calc Real.exp (-(uk 1 (n + j) / 2)) ≤ Real.exp (-(U0 / 2)) := Real.exp_le_exp.mpr (by linarith)
        _ ≤ Sx⁻¹ := exp_neg_le_inv_sum (by linarith) N hSpos
    set E := 2 * (U0 * ρ) ^ 3 * (U0 - 1)⁻¹ * Sx⁻¹
    have hE : |εv n j| ≤ E := by
      refine le_trans heps ?_
      have h1 : uk 1 (n + j) ^ 3 ≤ (U0 * ρ) ^ 3 := pow_le_pow_left₀ (by linarith) hUjle 3
      have h2 : (uk 1 (n + j) - 1)⁻¹ ≤ (U0 - 1)⁻¹ := inv_anti₀ (by linarith) (by linarith)
      have h3 : 0 ≤ Real.exp (-(uk 1 (n + j) / 2)) := (Real.exp_pos _).le
      have h4 : 0 < (U0 - 1)⁻¹ := inv_pos.mpr (by linarith)
      calc 2 * uk 1 (n + j) ^ 3 / (uk 1 (n + j) - 1) * Real.exp (-(uk 1 (n + j) / 2))
          = 2 * uk 1 (n + j) ^ 3 * (uk 1 (n + j) - 1)⁻¹ * Real.exp (-(uk 1 (n + j) / 2)) := by ring
        _ ≤ 2 * (U0 * ρ) ^ 3 * (U0 - 1)⁻¹ * Sx⁻¹ := by
          have : 0 ≤ uk 1 (n + j) ^ 3 := by positivity
          have : 0 ≤ (uk 1 (n + j) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
          gcongr
    have hmem : 2 ^ k * E * (δv U0)⁻¹ ^ k ∈ᵢ ofInt (2 ^ k) * bepsF d N B * (bdel B).inv.pow k := by
      have hU0m : U0 ∈ᵢ bIU0 B := by
        have := mem_inv (m_u0 hB hU0 ht) hu0; simpa using this
      refine mem_mul (mem_mul (mem_ofInt' _ (by push_cast; ring)) ?_) (mem_pow (mem_inv (m_del hB hU0 ht) hdel) k)
      unfold bepsF
      exact mem_mul (mem_mul (mem_mul (mem_ofInt' _ (by norm_num)) (mem_pow (mem_mul hU0m hρ) 3))
        (mem_inv (mem_sub hU0m mem_oneI) hU01)) (mem_inv hSmem hexp)
    calc 2 ^ k * |εv n j| / δv U0 ^ k ≤ 2 ^ k * E / δv U0 ^ k :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by positivity)) hδk.le
      _ = 2 ^ k * E * (δv U0)⁻¹ ^ k := by rw [inv_pow]; ring
      _ ≤ _ := hmem.2
  · -- infinite box
    have htp : B.tlp = 0 := by have := hB.tlp; omega
    have hN2 : 2 ≤ N := by have := hB.dN; omega
    have ht0 := t0v_pos hU0
    set th : ℝ := (B.thp : ℝ) / B.thq
    have hthq : (0 : ℝ) < B.thq := by exact_mod_cast hB.thq
    have hthp : (0 : ℝ) < B.thp := by exact_mod_cast hB.thp
    have hth : 0 < th := div_pos hthp hthq
    have ht0th : t0v U0 ≤ th := hth2
    -- |ε_j| ≤ 4 N! 2^N t0^{2N-4}
    have hE : |εv n j| ≤ 4 * (N.factorial : ℝ) * 2 ^ N * t0v U0 ^ (2 * N - 4) := by
      refine le_trans heps ?_
      set Uj := uk 1 (n + j)
      have hUj0 : 0 < Uj := by linarith
      have hx := exp_neg_le_pow (x := Uj / 2) (by linarith) N
      have h2 : 2 * Uj ^ 3 / (Uj - 1) ≤ 4 * Uj ^ 2 := by
        rw [div_le_iff₀ (by linarith)]
        have : 2 ≤ Uj := by
          have h4 : (4 : ℝ) ≤ U0 := by
            have hsq := t0v_sq hU0
            have : t0v U0 ^ 2 ≤ (1 / 2) ^ 2 := by
              have hhalf : th ≤ 1 / 2 := by
                rw [div_le_iff₀ hthq]; have := hB.half; push_cast; have : (2 * B.thp : ℝ) ≤ B.thq := by exact_mod_cast this
                linarith
              exact pow_le_pow_left₀ ht0.le (le_trans ht0th hhalf) 2
            rw [hsq] at this
            have hU0pos : 0 < U0 := by linarith
            rw [inv_le_comm₀ hU0pos (by norm_num)] at this; norm_num at this; linarith
          linarith
        nlinarith
      have h3 : Uj ^ 2 * ((N.factorial : ℝ) * ((Uj / 2) ^ N)⁻¹) ≤ (N.factorial : ℝ) * 2 ^ N * (U0 ^ (N - 2))⁻¹ := by
        have e : Uj ^ 2 * ((N.factorial : ℝ) * ((Uj / 2) ^ N)⁻¹) = (N.factorial : ℝ) * 2 ^ N * (Uj ^ (N - 2))⁻¹ := by
          rw [div_pow]
          have : Uj ^ N = Uj ^ 2 * Uj ^ (N - 2) := by rw [← pow_add]; congr 1; omega
          rw [this]; field_simp
        rw [e]
        have : U0 ^ (N - 2) ≤ Uj ^ (N - 2) := pow_le_pow_left₀ (by linarith) hUjge _
        have hpos : 0 < U0 ^ (N - 2) := by positivity
        gcongr
      have e2 : (U0 ^ (N - 2))⁻¹ = t0v U0 ^ (2 * N - 4) := by
        rw [show 2 * N - 4 = 2 * (N - 2) by omega, pow_mul, t0v_sq hU0, inv_pow]
      calc 2 * Uj ^ 3 / (Uj - 1) * Real.exp (-(Uj / 2)) ≤ 4 * Uj ^ 2 * ((N.factorial : ℝ) * ((Uj / 2) ^ N)⁻¹) := by
            gcongr
        _ = 4 * (Uj ^ 2 * ((N.factorial : ℝ) * ((Uj / 2) ^ N)⁻¹)) := by ring
        _ ≤ 4 * ((N.factorial : ℝ) * 2 ^ N * (U0 ^ (N - 2))⁻¹) := by gcongr
        _ = _ := by rw [e2]; ring
    have hdk : δv U0 ^ k = (aC / 2 * Real.sqrt (c2v U0)) ^ k * t0v U0 ^ (3 * k) := by
      rw [δv_eq hU0 hq2 hc.le]; rw [mul_pow, mul_pow, mul_pow, ← pow_mul]; ring
    have hexpo : 2 * N - 4 = (2 * N - 4 - 3 * k) + 3 * k := by have := hB.dN; omega
    have hsc : 0 < aC / 2 * Real.sqrt (c2v U0) := by have := aC_pos; have := Real.sqrt_pos.mpr hc; positivity
    -- target real value inside the interval
    set V := 2 ^ k * 4 * (∏ i ∈ range N, (2 * ((i : ℝ) + 1) * th ^ 2)) * (th⁻¹) ^ (4 + 3 * k) *
      ((aC / 2 * Real.sqrt (c2v U0))⁻¹) ^ k
    have hmem : V ∈ᵢ ofInt (2 ^ k * 4) * prodT (ofFrac B.thp B.thq) N * (ofFrac B.thq B.thp).pow (4 + 3 * k) *
        ((Ia2 * bsq B).inv).pow k := by
      refine mem_mul (mem_mul (mem_mul (mem_ofInt' _ (by push_cast; ring)) (mem_prodT (mem_ofFrac _ _ hB.thq) N))
        (mem_pow (mem_ofFrac' B.thq B.thp hB.thp (by simp [th])) _)) (mem_pow (mem_inv ?_ hB.asq) k)
      exact mem_mul mem_Ia2 (m_sq hB hU0 ht)
    have hV : V = 2 ^ k * 4 * (2 ^ N * (N.factorial : ℝ)) * th ^ (2 * N - 4 - 3 * k) *
        ((aC / 2 * Real.sqrt (c2v U0))⁻¹) ^ k := by
      simp only [V]; rw [prod_two_mul]
      have : th ^ (2 * N) * (th⁻¹) ^ (4 + 3 * k) = th ^ (2 * N - 4 - 3 * k) := by
        have key : th ^ (2 * N) = th ^ (2 * N - 4 - 3 * k) * th ^ (4 + 3 * k) := by
          rw [← pow_add]; congr 1; have := hB.dN; omega
        rw [key, mul_assoc, ← mul_pow, mul_inv_cancel₀ hth.ne', one_pow, mul_one]
      calc _ = 2 ^ k * 4 * (2 ^ N * (N.factorial : ℝ)) * (th ^ (2 * N) * (th⁻¹) ^ (4 + 3 * k)) *
            ((aC / 2 * Real.sqrt (c2v U0))⁻¹) ^ k := by ring
        _ = _ := by rw [this]
    calc 2 ^ k * |εv n j| / δv U0 ^ k
        ≤ 2 ^ k * (4 * (N.factorial : ℝ) * 2 ^ N * t0v U0 ^ (2 * N - 4)) / δv U0 ^ k := by gcongr
      _ = 2 ^ k * 4 * (2 ^ N * (N.factorial : ℝ)) * t0v U0 ^ (2 * N - 4 - 3 * k) *
            ((aC / 2 * Real.sqrt (c2v U0))⁻¹) ^ k := by
          rw [hdk]
          generalize hm : 2 * N - 4 - 3 * k = m at hexpo ⊢
          rw [hexpo, pow_add]
          have : 0 < t0v U0 ^ (3 * k) := by positivity
          rw [inv_pow]
          field_simp
      _ ≤ V := by
          rw [hV]
          have : t0v U0 ^ (2 * N - 4 - 3 * k) ≤ th ^ (2 * N - 4 - 3 * k) := pow_le_pow_left₀ ht0.le ht0th _
          have : 0 ≤ ((aC / 2 * Real.sqrt (c2v U0))⁻¹) ^ k := by positivity
          gcongr
      _ ≤ _ := hmem.2


lemma gam_mem (hth2 : t0v (uk 1 n) ≤ (B.thp : ℝ) / B.thq) (k : ℕ) (hk : k ≤ d) :
    gamv n k ∈ᵢ bgam d K N B k := by
  set U0 := uk 1 n
  have hq2 := okQ2 hB
  have hc := c2v_pos hB hU0 ht
  have hδ := δv_pos hU0 hq2 hc
  have hδk : 0 < δv U0 ^ k := by positivity
  have hKk : k ≤ K := by have := hB.dK; omega
  set g : ℕ → ℝ := fun j => Real.exp (φv U0 0 j)
  set a : ℕ → ℝ := fun i => gs (φv U0) i 0
  set P : ℕ → ℝ := fun j => ∑ i ∈ range K, a i * (j : ℝ) ^ i / (i.factorial : ℝ)
  set c : ℕ → ℝ := fun j => (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ)
  have hsplit : Δv n k = ∑ j ∈ range (k + 1), c j * P j + ∑ j ∈ range (k + 1), c j * (g j - P j) +
      ∑ j ∈ range (k + 1), c j * (g j * εv n j) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    unfold Δv
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [wv_eq hB hn hU0 ht j]; simp only [c, g]; ring
  have hgam : gamv n k = (∑ j ∈ range (k + 1), c j * P j) / δv U0 ^ k +
      (∑ j ∈ range (k + 1), c j * (g j - P j)) / δv U0 ^ k +
      (∑ j ∈ range (k + 1), c j * (g j * εv n j)) / δv U0 ^ k := by
    unfold gamv; rw [hsplit]; ring
  rw [hgam]
  unfold bgam
  refine mem_add (mem_add ?_ ?_) ?_
  · -- the Taylor main part
    have hT1 : ∑ j ∈ range (k + 1), c j * P j = ∑ i ∈ range K, a i / (i.factorial : ℝ) * (Dki k i : ℝ) := by
      simp only [P, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Dki_cast, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [c]; ring
    have hsplitK := Finset.sum_range_add (fun i => a i / (i.factorial : ℝ) * (Dki k i : ℝ)) k (K - k)
    rw [show k + (K - k) = K by omega] at hsplitK
    rw [hT1, hsplitK]
    have hz : ∑ i ∈ range k, a i / (i.factorial : ℝ) * (Dki k i : ℝ) = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hB.dki k hk i (Finset.mem_range.mp hi)]; simp
    rw [hz, zero_add, Finset.sum_div]
    unfold bmain
    apply mem_sumIv
    intro i' hi'
    have hs := gs_scale (φv U0) hδ.ne' (k + i') 0
    have hga : a (k + i') = gs (Φv U0) (k + i') 0 * δv U0 ^ (k + i') := by
      have : gs (Φv U0) (k + i') 0 = gs (fun i t => φv U0 i t / δv U0 ^ i) (k + i') 0 := rfl
      simp only [a]; rw [this, hs]; field_simp
    have e : a (k + i') / ((k + i').factorial : ℝ) * (Dki k (k + i') : ℝ) / δv U0 ^ k =
        (Dki k (k + i') : ℝ) / ((k + i').factorial : ℝ) * δv U0 ^ i' * gs (Φv U0) (k + i') 0 := by
      rw [hga, pow_add]; field_simp
    rw [e]
    refine mem_mul (mem_mul (mem_ofFrac' _ _ (by exact_mod_cast Nat.factorial_pos _) (by push_cast; rfl))
      (mem_pow (m_del hB hU0 ht) i')) (m_g0 hB hU0 ht (k + i') (by omega))
  · -- the Taylor remainder
    apply mem_symm
    have hR : ∀ j ∈ range (k + 1), |c j * (g j - P j)| ≤
        (k.choose j : ℝ) * ((bMK d K B : ℝ) / S * δv U0 ^ K * (j : ℝ) ^ K / (K.factorial : ℝ)) := by
      intro j hj
      have hj' : j ≤ d := by have := Finset.mem_range.mp hj; omega
      have hc' : |c j| = (k.choose j : ℝ) := by
        simp only [c, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
      rw [abs_mul (c j), hc']
      exact mul_le_mul_of_nonneg_left (taylor_g hB hn hU0 ht j hj') (by positivity)
    have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hR)
    have hval : ∑ j ∈ range (k + 1), (k.choose j : ℝ) * ((bMK d K B : ℝ) / S * δv U0 ^ K * (j : ℝ) ^ K /
        (K.factorial : ℝ)) = (CjK k K : ℝ) / (K.factorial : ℝ) * δv U0 ^ K * ((bMK d K B : ℝ) / S) := by
      rw [CjK_cast, Finset.sum_div, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_; ring
    rw [hval] at hsum
    have hmem : (CjK k K : ℝ) / (K.factorial : ℝ) * δv U0 ^ (K - k) * ((bMK d K B : ℝ) / S) ∈ᵢ
        ofFrac (CjK k K) (K.factorial) * (bdel B).pow (K - k) * (⟨bMK d K B, bMK d K B⟩ : Iv) :=
      mem_mul (mem_mul (mem_ofFrac' _ _ (by exact_mod_cast Nat.factorial_pos _) (by push_cast; rfl))
        (mem_pow (m_del hB hU0 ht) _)) ⟨le_rfl, le_rfl⟩
    rw [abs_div, abs_of_pos hδk, div_le_iff₀ hδk]
    refine le_trans hsum ?_
    have e : (CjK k K : ℝ) / (K.factorial : ℝ) * δv U0 ^ K * ((bMK d K B : ℝ) / S) =
        (CjK k K : ℝ) / (K.factorial : ℝ) * δv U0 ^ (K - k) * ((bMK d K B : ℝ) / S) * δv U0 ^ k := by
      rw [show K = (K - k) + k by omega, pow_add]; simp only [show K - k + k - k = K - k by omega]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hmem.2 hδk.le
  · -- the error part
    apply mem_symm
    have hE : ∀ j ∈ range (k + 1), |c j * (g j * εv n j)| ≤ (k.choose j : ℝ) * |εv n j| := by
      intro j hj
      have hj' : j ≤ d := by have := Finset.mem_range.mp hj; omega
      have hg1 := g_le_one hB hn hU0 ht j hj'
      have hg0 : 0 ≤ g j := (Real.exp_pos _).le
      have hc' : |c j| = (k.choose j : ℝ) := by
        simp only [c, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
      rw [abs_mul (c j), abs_mul (g j), abs_of_nonneg hg0, hc']
      have : g j * |εv n j| ≤ |εv n j| := by nlinarith [abs_nonneg (εv n j)]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hE)
    rw [abs_div, abs_of_pos hδk, div_le_iff₀ hδk]
    refine le_trans hsum ?_
    have hb : ∀ j ∈ range (k + 1), (k.choose j : ℝ) * |εv n j| ≤
        (k.choose j : ℝ) * ((bEk d N B k : ℝ) / S * δv U0 ^ k / 2 ^ k) := by
      intro j hj
      have := eps_scaled hB hn hU0 ht hth2 k hk j (Finset.mem_range.mp hj |> Nat.lt_succ_iff.mp)
      have h2 : (0 : ℝ) < 2 ^ k := by positivity
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [le_div_iff₀ h2]
      rw [div_le_iff₀ hδk] at this; linarith
    refine le_trans (Finset.sum_le_sum hb) (le_of_eq ?_)
    rw [← Finset.sum_mul]
    have : ∑ j ∈ range (k + 1), (k.choose j : ℝ) = 2 ^ k := by
      have := Nat.sum_range_choose k; exact_mod_cast this
    rw [this]; field_simp


lemma G_mem (hth2 : t0v (uk 1 n) ≤ (B.thp : ℝ) / B.thq) (x : ℤ × ℤ) (hx : 0 < x.2) :
    (∑ k ∈ range (d + 1), (d.choose k : ℝ) * gamv n k * ((x.1 : ℝ) / x.2) ^ (d - k) *
      (δv (uk 1 n) * ((x.1 : ℝ) / x.2) - 1) ^ k) ∈ᵢ bG d K N B x := by
  unfold bG
  apply mem_sumIv
  intro k hk
  have hx' := mem_ofFrac x.1 x.2 hx
  exact mem_mul (mem_mul (mem_mul (mem_ofInt' _ (by push_cast; rfl)) (gam_mem hB hn hU0 ht hth2 k (by omega)))
    (mem_pow hx' _)) (mem_pow (mem_sub (mem_mul (m_del hB hU0 ht) hx') mem_oneI) k)

lemma eval_jensen_eq (hNew : NewtonId d) (xr : ℝ) :
    (jensen d n).eval (Real.exp (-(Av (uk 1 n))) * (δv (uk 1 n) * xr - 1)) =
      Mmain n * δv (uk 1 n) ^ d * ∑ k ∈ range (d + 1), (d.choose k : ℝ) * gamv n k * xr ^ (d - k) *
        (δv (uk 1 n) * xr - 1) ^ k := by
  have hq2 := okQ2 hB
  have hc := c2v_pos hB hU0 ht
  have hδ := δv_pos hU0 hq2 hc
  have hM : 0 < Mmain n := by rw [Mmain_eq_exp hU0]; have := Kc_pos; positivity
  rw [eval_jensen]
  have h1 : ∀ j ∈ range (d + 1), (d.choose j : ℝ) * (pc (n + j) : ℝ) *
      (Real.exp (-(Av (uk 1 n))) * (δv (uk 1 n) * xr - 1)) ^ j = Mmain n * ((d.choose j : ℝ) * wv n j * (δv (uk 1 n) * xr - 1) ^ j) := by
    intro j _
    unfold wv
    rw [mul_pow, ← Real.exp_nat_mul]
    have : (j : ℝ) * -(Av (uk 1 n)) = -(Av (uk 1 n)) * j := by ring
    rw [this]; field_simp
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, hNew (wv n) (δv (uk 1 n) * xr), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ d := by have := Finset.mem_range.mp hk; omega
  have hΔ : (∑ j ∈ range (k + 1), (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * wv n j) = gamv n k * δv (uk 1 n) ^ k := by
    unfold gamv Δv; field_simp
  rw [hΔ]
  have : δv (uk 1 n) ^ d = δv (uk 1 n) ^ k * δv (uk 1 n) ^ (d - k) := by rw [← pow_add]; congr 1; omega
  rw [this, mul_pow]; ring

end

/-- **Soundness of one box**: a successful `checkBox` certifies hyperbolicity of `J^{d,n}` for every
`n ≥ 2` with `U(n)^{-1/2} ∈ [B.tl, B.th]`. -/
theorem box_sound {d K N : ℕ} (hNew : NewtonId d) {B : BoxD} (hc : checkBox d K N B = true) {n : ℕ}
    (hn : 2 ≤ n) (ht1 : (B.tlp : ℝ) / B.tlq ≤ t0v (uk 1 n)) (ht2 : t0v (uk 1 n) ≤ (B.thp : ℝ) / B.thq) :
    Hyperbolic (jensen d n) := by
  have hB := boxOK_of_check hc
  have hU0pos : 0 < uk 1 n := uk1_pos (by omega)
  have hthq : (0 : ℝ) < B.thq := by exact_mod_cast hB.thq
  have htlq : (0 : ℝ) < B.tlq := by exact_mod_cast hB.tlq
  have hU0 : 1 < uk 1 n := by
    have hhalf : (B.thp : ℝ) / B.thq ≤ 1 / 2 := by
      rw [div_le_iff₀ hthq]; have : (2 * B.thp : ℝ) ≤ B.thq := by exact_mod_cast hB.half
      linarith
    have h0 : 0 < t0v (uk 1 n) := by unfold t0v; have := Real.sqrt_pos.mpr hU0pos; positivity
    have hle : t0v (uk 1 n) ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ h0.le (le_trans ht2 hhalf) 2
    have hsq : t0v (uk 1 n) ^ 2 = (uk 1 n)⁻¹ := by unfold t0v; rw [inv_pow, Real.sq_sqrt hU0pos.le]
    rw [hsq, inv_le_comm₀ hU0pos (by norm_num)] at hle
    norm_num at hle; linarith
  have ht : t0v (uk 1 n) ∈ᵢ bIt B := by
    refine ⟨le_trans (mem_ofFrac B.tlp B.tlq hB.tlq).1 ht1, le_trans ht2 (mem_ofFrac B.thp B.thq hB.thq).2⟩
  set U0 := uk 1 n
  have hq2 := okQ2 hB
  have hc2 := c2v_pos hB hU0 ht
  have hδ := δv_pos hU0 hq2 hc2
  have hM : 0 < Mmain n := by rw [Mmain_eq_exp hU0]; have := Kc_pos; positivity
  set p : ℕ → ℤ × ℤ := fun i => B.pts.getD i (0, 1)
  have hden : ∀ i ≤ d, 0 < (p i).2 := by
    intro i hi
    have hlen := hB.len
    simp only [p]
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hB.den _ (List.getElem_mem _)
  set xr : ℕ → ℝ := fun i => ((p i).1 : ℝ) / (p i).2
  set XX : ℕ → ℝ := fun i => Real.exp (-(Av U0)) * (δv U0 * xr i - 1)
  set Gv : ℕ → ℝ := fun i => ∑ k ∈ range (d + 1), (d.choose k : ℝ) * gamv n k * xr i ^ (d - k) *
    (δv U0 * xr i - 1) ^ k
  have heval : ∀ i, (jensen d n).eval (XX i) = Mmain n * δv U0 ^ d * Gv i :=
    fun i => eval_jensen_eq hB hn hU0 ht hNew (xr i)
  have hsignG : ∀ i ≤ d, (if (d - i) % 2 = 0 then 0 < Gv i else Gv i < 0) := by
    intro i hi
    have hm := G_mem hB hn hU0 ht ht2 (p i) (hden i hi)
    have hs := hB.sign i hi
    unfold signOK at hs
    split_ifs at hs ⊢ with hpar
    · exact pos_of_mem hm (by simpa using hs)
    · exact neg_of_mem hm (by simpa using hs)
  apply hyperbolic_of_alternating (jensen d n) d (natDegree_jensen_le d n) XX
  · intro i hi
    have hm := hB.mono i hi
    have d1 := hden i (by omega)
    have d2 := hden (i + 1) (by omega)
    have hx : xr i < xr (i + 1) := by
      simp only [xr]
      rw [div_lt_div_iff₀ (by exact_mod_cast d1) (by exact_mod_cast d2)]
      exact_mod_cast hm
    simp only [XX]
    have := mul_lt_mul_of_pos_left hx hδ
    exact mul_lt_mul_of_pos_left (by linarith) (Real.exp_pos _)
  · intro i hi
    rw [heval, heval]
    have g1 := hsignG i (by omega)
    have g2 := hsignG (i + 1) (by omega)
    have hpos : 0 < (Mmain n * δv U0 ^ d) ^ 2 := by positivity
    have hGG : Gv i * Gv (i + 1) < 0 := by
      have hpar : (d - i) % 2 = 0 ↔ ¬ (d - (i + 1)) % 2 = 0 := by omega
      split_ifs at g1 g2 with h1 h2 h2
      · exact absurd h2 (hpar.mp h1)
      · exact mul_neg_of_pos_of_neg g1 g2
      · exact mul_neg_of_neg_of_pos g1 g2
      · exact absurd (hpar.mpr h2) h1
    calc Mmain n * δv U0 ^ d * Gv i * (Mmain n * δv U0 ^ d * Gv (i + 1))
        = (Mmain n * δv U0 ^ d) ^ 2 * (Gv i * Gv (i + 1)) := by ring
      _ < 0 := mul_neg_of_pos_of_neg hpos hGG

end JensenThreshold.Tail
