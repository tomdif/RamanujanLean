/-
# Assembly: Rademacher's convergent series

`p(n) = pieceSum` (exact, `farey_decomp`). Each piece is `c_{h,k}·FL(k)` up to `bnd(k)`, where
`c_{h,k} = ω_{h,k}e^{−2πinh/k}/k` and `FL(k) = ∫_ℝ W(k+iu) du`. Summing over `F_N` gives
`Σ_{k≤N} A_k(n) FL(k)/k` with total error `≤ C(1+log N)/√N + C'N^{−1/2} → 0`.
-/
import RamanujanTau.Rademacher.Chord

set_option autoImplicit false

namespace Rademacher
open Complex HardyRamanujan Filter Metric MeasureTheory Set
open scoped Real Topology

noncomputable section

/-- the full-line integral `FL(k)`. -/
def FL (k n : ℕ) : ℂ := ∫ u : ℝ, Wf k n ((k : ℂ) + u * I)

/-- `c_{h,k} = ω_{h,k} e^{−2πinh/k}/k`. -/
def cx (n h k : ℕ) : ℂ := omega h k * cexp (-(2 * π * I * n * h / k)) / k

/-- the per-piece error bound. -/
def bnd (n N k : ℕ) : ℝ := (1 / k) * (Cn n * (4 * π / (k * √N)) + CE n * (√2 / N) ^ (1 / 2 : ℝ) * (2 * √2 / N))

lemma norm_cx {n h k : ℕ} (hk : 0 < k) (hcop : Nat.Coprime h k) : ‖cx n h k‖ = 1 / k := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  rw [cx, norm_div, norm_mul, (omega_spec hk hcop).1, norm_exp, Complex.norm_natCast]
  have : (-(2 * π * I * n * h / k)).re = 0 := by
    rw [show -(2 * π * I * n * h / k) = ((-(2 * π * n * h / k)) : ℝ) * I by push_cast; ring, re_ofReal_mul]
    simp
  rw [this, Real.exp_zero, one_mul]

lemma Ef_cont {h' : ℤ} {k n : ℕ} (hk : 0 < k) : Continuous fun u : ℝ => Ef h' k n ((k : ℂ) + u * I) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  refine continuous_iff_continuousAt.mpr fun u => ?_
  exact ((differentiableAt_Ef hk (by simpa using hkr)).continuousAt).comp (by fun_prop)

/-- **one piece**. -/
lemma piece_approx {n h k kp kn N : ℕ} (hk : 0 < k) (hn : 1 ≤ n) (hN : 1 ≤ N) (hkN : k ≤ N) (hkp1 : kp ≤ N)
    (hkn1 : kn ≤ N) (hkp : N < k + kp) (hkn : N < k + kn) (hcop : Nat.Coprime h k)
    (hh' : (k : ℤ) ∣ h * kn + 1) :
    ‖piece n h k kp kn - cx n h k * FL k n‖ ≤ bnd n N k := by
  have hint : ∀ u : ℝ, fI n (τc h k u) * dτc k u =
      cx n h k * (Wf k n ((k : ℂ) + u * I) + Ef (kn : ℤ) k n ((k : ℂ) + u * I)) := by
    intro u
    rw [integrand_eq hk hcop (h' := kn) (by exact_mod_cast hh') u, cx, Ef]
    ring
  have hW := (Wf_cont (n := n) hk).intervalIntegrable (μ := volume) (-(kp : ℝ)) kn
  have hE := (Ef_cont (h' := (kn : ℤ)) (n := n) hk).intervalIntegrable (μ := volume) (-(kp : ℝ)) kn
  have hp : piece n h k kp kn = cx n h k * ((∫ u in (-(kp : ℝ))..(kn : ℝ), Wf k n ((k : ℂ) + u * I)) +
      ∫ u in (-(kp : ℝ))..(kn : ℝ), Ef (kn : ℤ) k n ((k : ℂ) + u * I)) := by
    rw [piece]; simp only [hint]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hW hE]
  rw [hp, FL, show cx n h k * ((∫ u in (-(kp : ℝ))..(kn : ℝ), Wf k n ((k : ℂ) + u * I)) +
      ∫ u in (-(kp : ℝ))..(kn : ℝ), Ef (kn : ℤ) k n ((k : ℂ) + u * I)) - cx n h k * ∫ u : ℝ, Wf k n ((k : ℂ) + u * I)
      = cx n h k * (((∫ u in (-(kp : ℝ))..(kn : ℝ), Wf k n ((k : ℂ) + u * I)) - ∫ u : ℝ, Wf k n ((k : ℂ) + u * I)) +
      ∫ u in (-(kp : ℝ))..(kn : ℝ), Ef (kn : ℤ) k n ((k : ℂ) + u * I)) by ring]
  rw [norm_mul, norm_cx hk hcop, bnd]
  gcongr
  exact (norm_add_le _ _).trans (add_le_add (tail_bound hk hn hN hkp hkn)
    (err_bound hk hn hN hkN hkp1 hkn1 hkp hkn _))

/-- the hypotheses on a Farey chain. -/
def Good (N : ℕ) (z : ℕ × ℕ) : Prop := 0 < z.2 ∧ z.2 ≤ N ∧ Nat.Coprime z.1 z.2

/-- **the whole chain**. -/
lemma pieceSum_approx (n N : ℕ) (hn : 1 ≤ n) (hN : 1 ≤ N) : ∀ (rest : List (ℕ × ℕ)) (kp : ℕ) (x : ℕ × ℕ),
    List.IsChain (Farey.Nb N) (x :: rest) → (∀ z ∈ x :: rest, Good N z) → kp ≤ N → N < x.2 + kp →
    ‖pieceSum n kp (x :: rest) - (((x :: rest).dropLast).map fun y => cx n y.1 y.2 * FL y.2 n).sum‖ ≤
      (((x :: rest).dropLast).map fun y => bnd n N y.2).sum := by
  intro rest
  induction rest with
  | nil => intro kp x _ _ _ _; simp [pieceSum]
  | cons y rest ih =>
    intro kp x hc hg hkp1 hkp
    rw [List.isChain_cons_cons] at hc
    have hx := hg x (by simp)
    have hy := hg y (by simp)
    have ih' := ih x.2 y hc.2 (fun z hz => hg z (List.mem_cons_of_mem _ hz)) hx.2.1 (by have := hc.1.2; omega)
    rw [pieceSum, List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _), List.map_cons, List.sum_cons,
      List.map_cons, List.sum_cons]
    have hp := piece_approx (n := n) (h := x.1) hx.1 hn hN hx.2.1 hkp1 hy.2.1 (by omega) (by have := hc.1.2; omega)
      hx.2.2 (by
        have h1 : x.2 * y.1 = x.1 * y.2 + 1 := hc.1.1
        exact ⟨y.1, by push_cast; linarith [show ((x.2 : ℤ) * y.1) = x.1 * y.2 + 1 by exact_mod_cast h1]⟩)
    calc ‖piece n x.1 x.2 kp y.2 + pieceSum n x.2 (y :: rest) -
          (cx n x.1 x.2 * FL x.2 n + (((y :: rest).dropLast).map fun y => cx n y.1 y.2 * FL y.2 n).sum)‖
        = ‖(piece n x.1 x.2 kp y.2 - cx n x.1 x.2 * FL x.2 n) + (pieceSum n x.2 (y :: rest) -
          (((y :: rest).dropLast).map fun y => cx n y.1 y.2 * FL y.2 n).sum)‖ := by congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hp ih')

/-! ### the Farey list as a finset -/

/-- the reduced fractions `h/k`, `0 ≤ h < k ≤ N`. -/
def Frac (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 N).biUnion fun k => ((Finset.range k).filter fun h => Nat.Coprime h k).map
    ⟨fun h => (h, k), fun a b h => by simpa using h⟩

lemma mem_Frac {N : ℕ} {z : ℕ × ℕ} : z ∈ Frac N ↔ 1 ≤ z.2 ∧ z.2 ≤ N ∧ z.1 < z.2 ∧ Nat.Coprime z.1 z.2 := by
  obtain ⟨h, k⟩ := z
  simp only [Frac, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_map, Finset.mem_filter, Finset.mem_range,
    Function.Embedding.coeFn_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨k', ⟨h1, h2⟩, h', ⟨h3, h4⟩, rfl, rfl⟩; exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨k, ⟨h1, h2⟩, h, ⟨h3, h4⟩, rfl, rfl⟩

lemma fracList_mem {N : ℕ} (hN : 1 ≤ N) (z : ℕ × ℕ) : z ∈ (0, 1) :: Farey.sb N 0 1 1 1 ↔ z ∈ Frac N := by
  rw [mem_Frac, List.mem_cons]
  constructor
  · rintro (rfl | hz)
    · exact ⟨le_rfl, hN, one_pos, by norm_num⟩
    · obtain ⟨q1, q2, q3, q4, q5⟩ := Farey.mem_sb N 0 1 1 1 (by norm_num) z hz
      exact ⟨q3, q4, by omega, q5⟩
  · rintro ⟨h1, h2, h3, h4⟩
    by_cases h0 : z.1 = 0
    · left
      have : z.2 = 1 := by rw [h0] at h4; simpa using h4
      ext <;> simp [h0, this]
    · right
      exact Farey.complete N 0 1 1 1 (by norm_num) one_pos one_pos z.1 z.2 (by omega) h2 h4 (by omega) (by omega)

lemma fracList_nodup (N : ℕ) : ((0, 1) :: Farey.sb N 0 1 1 1).Nodup := by
  refine List.nodup_cons.mpr ⟨fun h => ?_, Farey.nodup N 0 1 1 1 (by norm_num)⟩
  have := (Farey.mem_sb N 0 1 1 1 (by norm_num) _ h).1
  simp at this

lemma fracList_sum {N : ℕ} (hN : 1 ≤ N) {M : Type*} [AddCommMonoid M] (g : ℕ × ℕ → M) :
    (((0, 1) :: Farey.sb N 0 1 1 1).map g).sum = ∑ z ∈ Frac N, g z := by
  rw [← List.sum_toFinset g (fracList_nodup N)]
  congr 1
  ext z; rw [List.mem_toFinset, fracList_mem hN]

lemma Frac_sum {N : ℕ} {M : Type*} [AddCommMonoid M] (g : ℕ × ℕ → M) :
    ∑ z ∈ Frac N, g z = ∑ k ∈ Finset.Icc 1 N, ∑ h ∈ (Finset.range k).filter (fun h => Nat.Coprime h k), g (h, k) := by
  rw [Frac, Finset.sum_biUnion]
  · simp
  · intro k _ k' _ hkk'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro z hz hz'
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hz hz'
    obtain ⟨_, _, rfl⟩ := hz
    obtain ⟨_, _, h⟩ := hz'
    exact hkk' (congrArg Prod.snd h).symm

lemma fareyList_dropLast (N : ℕ) : (fareyList N).dropLast = (0, 1) :: Farey.sb N 0 1 1 1 := by
  rw [fareyList, ← List.cons_append, List.dropLast_concat]

lemma fareyList_good {N : ℕ} (hN : 1 ≤ N) : ∀ z ∈ fareyList N, Good N z := by
  intro z hz
  simp only [fareyList, List.mem_cons, List.mem_append] at hz
  rcases hz with rfl | hz | hz
  · exact ⟨one_pos, hN, by norm_num⟩
  · obtain ⟨_, _, q3, q4, q5⟩ := Farey.mem_sb N 0 1 1 1 (by norm_num) z hz
    exact ⟨q3, q4, q5⟩
  · rcases hz with rfl | h
    · exact ⟨one_pos, hN, by norm_num⟩
    · simp at h

/-- **the approximation of `p(n)`**. -/
theorem approx (n N : ℕ) (hn : 1 ≤ n) (hN : 1 ≤ N) :
    ‖(p n : ℂ) - ∑ k ∈ Finset.Icc 1 N, Ak k n * (FL k n / k)‖ ≤ ∑ k ∈ Finset.Icc 1 N, k * bnd n N k := by
  have h1 := pieceSum_approx n N hn hN _ N (0, 1) (farey_chain N) (fareyList_good hN) le_rfl (by simp)
  rw [← fareyList, ← farey_decomp n N hN, fareyList_dropLast, fracList_sum hN, fracList_sum hN, Frac_sum,
    Frac_sum] at h1
  have e : ∑ k ∈ Finset.Icc 1 N, ∑ h ∈ (Finset.range k).filter (fun h => Nat.Coprime h k), cx n h k * FL k n =
      ∑ k ∈ Finset.Icc 1 N, Ak k n * (FL k n / k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Ak, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [cx]; ring
  rw [e] at h1
  refine h1.trans (Finset.sum_le_sum fun k hk => ?_)
  have hb : 0 ≤ bnd n N k := by
    unfold bnd
    have := mul_nonneg (Real.exp_pos (2 * π * n + π / 12)).le S0_nonneg
    have : 0 ≤ Cn n := (Real.exp_pos _).le
    positivity
  simp only
  rw [Finset.sum_const, nsmul_eq_mul]
  gcongr
  calc ((Finset.range k).filter fun h => Nat.Coprime h k).card ≤ (Finset.range k).card :=
        Finset.card_filter_le _ _
    _ = k := by simp

/-! ### the limit -/

lemma sum_bnd {n N : ℕ} (hN : 1 ≤ N) : ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * bnd n N k ≤
    Cn n * (4 * π) * ((1 + Real.log N) / √N) + CE n * (2 * √2) * (√2 / N) ^ (1 / 2 : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have e : ∀ k ∈ Finset.Icc 1 N, (k : ℝ) * bnd n N k =
      Cn n * (4 * π) / √N * (k : ℝ)⁻¹ + CE n * (√2 / N) ^ (1 / 2 : ℝ) * (2 * √2 / N) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    unfold bnd
    field_simp
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
    nsmul_eq_mul]
  have hH : ∑ k ∈ Finset.Icc 1 N, ((k : ℝ))⁻¹ ≤ 1 + Real.log N := by
    have := harmonic_le_one_add_log N
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    exact this
  have hC : 0 ≤ Cn n * (4 * π) / √N := by have : 0 ≤ Cn n := (Real.exp_pos _).le; positivity
  calc Cn n * (4 * π) / √N * ∑ k ∈ Finset.Icc 1 N, ((k : ℝ))⁻¹ +
        ((N + 1 - 1 : ℕ) : ℝ) * (CE n * (√2 / N) ^ (1 / 2 : ℝ) * (2 * √2 / N))
      ≤ Cn n * (4 * π) / √N * (1 + Real.log N) +
        ((N + 1 - 1 : ℕ) : ℝ) * (CE n * (√2 / N) ^ (1 / 2 : ℝ) * (2 * √2 / N)) := by gcongr
    _ = _ := by
        rw [show N + 1 - 1 = N by omega]
        field_simp

lemma tendsto_bound (n : ℕ) : Tendsto (fun N : ℕ => Cn n * (4 * π) * ((1 + Real.log N) / √N) +
    CE n * (2 * √2) * (√2 / N) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => (1 + Real.log x) / √x) atTop (𝓝 0) := by
    have hlog : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    have hinv : Tendsto (fun x : ℝ => 1 / √x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
    have := hinv.add hlog
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.sqrt_eq_rpow, add_div]
  have h2 : Tendsto (fun N : ℕ => (√2 / N) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ => √2 / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have := this.rpow_const (p := 1 / 2) (Or.inr (by norm_num))
    simpa [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] using this
  have := ((h1.comp tendsto_natCast_atTop_atTop).const_mul (Cn n * (4 * π))).add (h2.const_mul (CE n * (2 * √2)))
  simpa using this

/-- **Rademacher's formula** (convergent-series form): `Σ_{k≤N} A_k(n)·FL(k)/k → p(n)`. -/
theorem rademacher_tendsto (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, Ak k n * (FL k n / k)) atTop (𝓝 (p n : ℂ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ (tendsto_bound n)
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [norm_sub_rev]
  exact (approx n N hn hN).trans (sum_bnd hN)

end

end Rademacher
