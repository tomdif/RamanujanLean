/-
# `XiKernelHyp` holds: GORZ Theorem 1 for the Riemann Ξ-function, unconditionally

For `n ≥ 2` put `M = 2n − 2`, `c = cRoot M` (`(πe^c − ¼)c = M`), `λ₁ = πe^{c−1}`, `ε = λ₁^{−1/2}/c`,
`η = ε + 1/n`.  Then `nε² ≤ e/c → 0`, so `√n η → 0`.  With `μ_l` the normalized moments,

  `B(n+j) = 32 C(2n,2) F(M) c^{2j} · W(j)`,  `W(j) = A(j) E₀(j) − κ E₂(j)`,

`A(j) = C(2n+2j,2)/C(2n,2)`, `E_a(j) = Σ_{l≤2k+2} C(2j+a,l) μ_l`, `κ = c²/(32C(2n,2)) ≤ 1/n`.  Every
piece is a small-coefficient polynomial in `j` (`|μ_l| ≤ K_l ε^l`), so `|Δ^k log B(n)| ≤ Λ_k η^k`
(`abs_dlog_of_SP`), hence `√n^k Δ^k log B(n) → 0`.

* **`xiKernelHyp_holds : XiKernelHyp`**
* **`xi_gorz_unconditional`** : GORZ Theorem 1 for Mathlib's `completedRiemannZeta`, no hypotheses.
-/
import RamanujanTau.GORZXi.XiKernel
import RamanujanTau.GORZXi.XiTaylor

set_option autoImplicit false

namespace GORZXi

open Real Set MeasureTheory Filter Topology JensenThreshold

/-! ## the scales -/

noncomputable def cN (n : ℕ) : ℝ := cRoot (2 * n - 2)
noncomputable def epsN (n : ℕ) : ℝ := (Real.sqrt (π * rexp (cN n - 1)))⁻¹ / cN n
noncomputable def etaN (n : ℕ) : ℝ := epsN n + 1 / (n : ℝ)

lemma tendsto_two_mul_sub : Tendsto (fun n : ℕ => 2 * n - 2) atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨b + 2, fun n hn => by omega⟩

lemma rootData_N : ∀ᶠ n : ℕ in atTop, RootData (2 * n - 2 - 1) (cN n) ∧
    cN n ^ 4 ≤ (((2 * n - 2 : ℕ) : ℝ) + 1) / 4 :=
  tendsto_two_mul_sub.eventually rootData_ev

lemma cRoot_ge_one (M : ℕ) : 1 ≤ cRoot M := by
  unfold cRoot; split_ifs with h
  · exact h.choose_spec.1
  · exact le_rfl

lemma epsN_nonneg (n : ℕ) : 0 ≤ epsN n := by
  have := cRoot_ge_one (2 * n - 2)
  unfold epsN cN; positivity

/-- `n ε² ≤ 3/c`. -/
lemma n_epsN_sq : ∀ᶠ n : ℕ in atTop, (n : ℝ) * epsN n ^ 2 ≤ 3 / cN n := by
  filter_upwards [rootData_N, eventually_ge_atTop 2] with n ⟨hr, _⟩ hn
  have hc := hr.one_le
  have hc0 : 0 < cN n := by linarith
  have hM : ((2 * n - 2 - 1 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hroot := hr.root
  rw [hM] at hroot
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold epsN
  set c := cN n
  have hl : 0 < π * rexp (c - 1) := by positivity
  rw [div_pow, inv_pow, Real.sq_sqrt hl.le]
  have hec : rexp (c - 1) = rexp c / rexp 1 := by rw [exp_sub]
  have he : rexp 1 < 3 := by linarith [exp_one_lt_d9]
  have hroot' : π * rexp c * c = 2 * (n : ℝ) - 2 + c / 4 := by linarith
  rw [hec]
  have hpc : 0 < π * rexp c * c := by positivity
  have key : (n : ℝ) * rexp 1 ≤ 3 * (π * rexp c * c) := by
    rw [hroot']; nlinarith
  rw [show (n : ℝ) * ((π * (rexp c / rexp 1))⁻¹ / c ^ 2) = (n : ℝ) * rexp 1 / (π * rexp c * c) / c by
    field_simp]
  gcongr
  rw [div_le_iff₀ hpc]; linarith

lemma tendsto_sqrt_etaN : Tendsto (fun n : ℕ => Real.sqrt n * etaN n) atTop (𝓝 0) := by
  have hc : Tendsto cN atTop atTop := cRoot_tendsto.comp tendsto_two_mul_sub
  have hb : Tendsto (fun n : ℕ => Real.sqrt (3 / cN n)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp (tendsto_const_nhds (x := (3 : ℝ)).div_atTop hc)
    rw [Real.sqrt_zero] at this; exact this
  have h1 : Tendsto (fun n : ℕ => Real.sqrt n * epsN n) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => mul_nonneg (Real.sqrt_nonneg _) (epsN_nonneg n))
      ?_ hb
    filter_upwards [n_epsN_sq] with n hn
    have h0 : 0 ≤ Real.sqrt n * epsN n := mul_nonneg (Real.sqrt_nonneg _) (epsN_nonneg n)
    rw [← Real.sqrt_sq h0]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]; exact hn
  have h2 : Tendsto (fun n : ℕ => Real.sqrt n * (1 / (n : ℝ))) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hp : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hs : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg n)
    show (Real.sqrt n)⁻¹ = Real.sqrt n * (1 / (n : ℝ))
    calc (Real.sqrt n)⁻¹ = Real.sqrt n / (Real.sqrt n * Real.sqrt n) := by field_simp
      _ = _ := by rw [hs]; ring
  have := h1.add h2
  rw [add_zero] at this
  exact this.congr fun n => by simp only [etaN]; ring

lemma etaN_nonneg (n : ℕ) : 0 ≤ etaN n := add_nonneg (epsN_nonneg n) (by positivity)

lemma tendsto_etaN : Tendsto etaN atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall etaN_nonneg) ?_ tendsto_sqrt_etaN
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  nlinarith [etaN_nonneg n]

/-! ## small-coefficient pieces -/

lemma SP.zero_fun (K : ℕ) (η C : ℝ) (p : ℕ) : SP K η C 0 p (fun _ => 0) :=
  ⟨Empty, inferInstance, fun _ => 0, fun _ => p, by simp, fun _ => le_rfl, fun i => i.elim,
    fun j _ => by simp⟩

lemma SP.sum_range {K : ℕ} {η C : ℝ} {N p : ℕ} (f : ℕ → ℕ → ℝ) :
    ∀ L, (∀ l < L, SP K η C N p (f l)) → SP K η C (L * N) p (fun j => ∑ l ∈ Finset.range L, f l j)
  | 0, _ => by simpa using SP.zero_fun K η C p
  | L + 1, h => by
    have := (SP.sum_range f L fun l hl => h l (by omega)).add (h L (by omega))
    simpa [Finset.sum_range_succ, Nat.succ_mul] using this

/-- the uniform coefficient constant. -/
noncomputable def Ksum (L a : ℕ) : ℝ := ∑ l ∈ Finset.range (L + 1), (1 + 2 * Bcst l) * Cpoly l a

lemma Ksum_nonneg (L a : ℕ) : 0 ≤ Ksum L a :=
  Finset.sum_nonneg fun l _ => mul_nonneg (by linarith [Bcst_nonneg l]) (Cpoly_nonneg l a)

/-- `E_a(j) = Σ_{l≤L} C(2j+a,l) μ_l`. -/
noncomputable def Efun (M : ℕ) (c : ℝ) (L a j : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (L + 1), ((2 * j + a).choose l : ℝ) * muX M c l

lemma SP_E {m : ℕ} {c : ℝ} (hc : RootData m c) (K L a : ℕ) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hε : (Real.sqrt (π * rexp (c - 1)))⁻¹ / c ≤ η) :
    SP K η (Ksum L a) ((L + 1) * (L + 1)) 0 (Efun (m + 1) c L a) := by
  have hc0 : 0 < c := by linarith [hc.one_le]
  have hε0 : 0 ≤ (Real.sqrt (π * rexp (c - 1)))⁻¹ / c := by positivity
  refine (SP.sum_range (fun l j => ((2 * j + a).choose l : ℝ) * muX (m + 1) c l) (L + 1) fun l hl => ?_)
  have hB : 0 ≤ 1 + 2 * Bcst l := by linarith [Bcst_nonneg l]
  have hr : |muX (m + 1) c l| ≤ (1 + 2 * Bcst l) * η ^ l :=
    (abs_muX_le hc l).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε0 hε l) hB)
  refine (SP_choose K a l hη0 hη1 hB hr).mono ?_ (by omega) le_rfl hη0
  exact Finset.single_le_sum (f := fun l => (1 + 2 * Bcst l) * Cpoly l a)
    (fun l _ => mul_nonneg (by linarith [Bcst_nonneg l]) (Cpoly_nonneg l a)) (Finset.mem_range.mpr hl)

/-- `A(j) = C(2n+2j,2)/C(2n,2)`. -/
noncomputable def Afun (n j : ℕ) : ℝ := ((2 * (n + j)).choose 2 : ℝ) / ((2 * n).choose 2 : ℝ)

lemma SP_A (K : ℕ) {n : ℕ} (hn : 1 ≤ n) {η : ℝ} (hη : 1 / (n : ℝ) ≤ η) : SP K η 4 3 0 (Afun n) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hη0 : 0 ≤ η := le_trans (by positivity) hη
  have hd : 0 < (n : ℝ) * (2 * n - 1) := by nlinarith
  obtain ⟨a1, ha1d⟩ : ∃ a1 : ℝ, a1 = (4 * n - 1) / ((n : ℝ) * (2 * n - 1)) := ⟨_, rfl⟩
  obtain ⟨a2, ha2d⟩ : ∃ a2 : ℝ, a2 = 2 / ((n : ℝ) * (2 * n - 1)) := ⟨_, rfl⟩
  have ha1 : |a1| ≤ 4 * η ^ 1 := by
    rw [ha1d, abs_of_nonneg (div_nonneg (by linarith) hd.le), pow_one, div_le_iff₀ hd]
    have : 4 / (n : ℝ) ≤ 4 * η := by rw [show 4 / (n : ℝ) = 4 * (1 / n) by ring]; gcongr
    rw [div_le_iff₀ (by linarith)] at this
    nlinarith
  have ha2 : |a2| ≤ 4 * η ^ 2 := by
    rw [ha2d, abs_of_nonneg (div_nonneg (by norm_num) hd.le), div_le_iff₀ hd]
    have h1 : (1 / (n : ℝ)) ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (by positivity) hη 2
    rw [div_pow, one_pow, div_le_iff₀ (by positivity)] at h1
    nlinarith
  have h := (((SP.const (K := K) (η := η) (C := 4) 1 (by norm_num)).add
    ((SP.monom (K := K) a1 1 ha1).mono le_rfl le_rfl (Nat.zero_le _) hη0)).add
    ((SP.monom (K := K) a2 2 ha2).mono le_rfl le_rfl (Nat.zero_le _) hη0))
  refine h.congr fun j _ => ?_
  simp only [Afun, Nat.cast_choose_two]
  push_cast
  have hdd : (n : ℝ) * (2 * n - 1) ≠ 0 := hd.ne'
  have e1 : a1 * ((n : ℝ) * (2 * n - 1)) = 4 * n - 1 := by rw [ha1d]; exact div_mul_cancel₀ _ hdd
  have e2 : a2 * ((n : ℝ) * (2 * n - 1)) = 2 := by rw [ha2d]; exact div_mul_cancel₀ _ hdd
  rw [eq_div_iff (by nlinarith)]
  linear_combination (j : ℝ) * e1 + (j : ℝ) ^ 2 * e2

/-! ## the representation of `B(n+j)` -/

lemma B_repr (L : ℕ) {n m : ℕ} (hm : 2 * n - 2 = m + 1) {c : ℝ} (hc0 : c ≠ 0) {j : ℕ}
    (hj : 2 * j + 2 ≤ L) :
    BXi (n + j) = (FXi (m + 1) * (32 * ((2 * n).choose 2 : ℝ))) * (c ^ 2) ^ j *
      (Afun n j * Efun (m + 1) c L 0 j + (-(c ^ 2 / (32 * ((2 * n).choose 2 : ℝ)))) * Efun (m + 1) c L 2 j) := by
  have hn : 2 ≤ n := by omega
  have hC : (0 : ℝ) < ((2 * n).choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have e1 : 2 * (n + j) - 2 = (m + 1) + 2 * j := by omega
  have e2 : 2 * (n + j) = (m + 1) + (2 * j + 2) := by omega
  have f1 := FXi_add (m + 1) hc0 (i := 2 * j) (L := L) (by omega)
  have f2 := FXi_add (m + 1) hc0 (i := 2 * j + 2) (L := L) hj
  simp only [BXi]
  rw [show FXi (2 * (n + j) - 2) = FXi (m + 1 + 2 * j) by rw [e1],
    show FXi (2 * (n + j)) = FXi (m + 1 + (2 * j + 2)) by rw [e2], f1, f2]
  simp only [Afun, Efun, add_zero]
  field_simp
  ring

/-! ## the bound -/

theorem dlog_BXi_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ Λ : ℝ, ∀ᶠ n : ℕ in atTop, 0 < BXi n ∧ |dlog BXi n k| ≤ Λ * etaN n ^ k := by
  set L := 2 * k + 2
  set C2 := Ksum L 0
  set C3 := Ksum L 2
  set N2 := (L + 1) * (L + 1)
  set Cw := 4 * C2 + C3
  set Nw := 3 * N2 + N2
  have hC2 := Ksum_nonneg L 0
  have hC3 := Ksum_nonneg L 2
  refine ⟨logConst k k Nw (2 * Cw), ?_⟩
  have hsmall : ∀ᶠ n : ℕ in atTop, etaN n ≤ 1 ∧ (k : ℝ) * etaN n ≤ 1 ∧
      (Nw : ℝ) * (2 * Cw) * ((k : ℝ) * etaN n) ≤ 1 / 2 := by
    have h := tendsto_etaN
    have hk' := (h.const_mul ((Nw : ℝ) * (2 * Cw) * k)).eventually (gt_mem_nhds (by norm_num : (0:ℝ) * 0 < 1 / 2) |>
      fun _ => Iio_mem_nhds (by simp : (Nw : ℝ) * (2 * Cw) * k * 0 < 1 / 2))
    have h1 := h.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
    have h2 := (h.const_mul (k : ℝ)).eventually (Iic_mem_nhds (by simp : (k : ℝ) * 0 < 1))
    filter_upwards [h1, h2, hk'] with n a b d
    refine ⟨a, b, ?_⟩
    have : (Nw : ℝ) * (2 * Cw) * k * etaN n < 1 / 2 := d
    nlinarith
  filter_upwards [rootData_N, eventually_ge_atTop 2, hsmall,
    eventually_ge_atTop (⌈2 * ((N2 : ℝ) * C3)⌉₊ + 1)] with n ⟨hr, hc4⟩ hn ⟨hη1, hkη, hsm⟩ hnbig
  obtain ⟨m, hm⟩ : ∃ m, 2 * n - 2 = m + 1 := ⟨2 * n - 3, by omega⟩
  have hm' : 2 * n - 2 - 1 = m := by omega
  rw [hm'] at hr
  set c := cN n with hcdef
  have hc1 := hr.one_le
  have hc0 : 0 < c := by linarith
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set η := etaN n
  have hη0 : 0 ≤ η := etaN_nonneg n
  have hεη : (Real.sqrt (π * rexp (c - 1)))⁻¹ / c ≤ η := by
    show epsN n ≤ etaN n; unfold etaN; have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  have hnη : 1 / (n : ℝ) ≤ η := by
    show 1 / (n : ℝ) ≤ etaN n; unfold etaN; linarith [epsN_nonneg n]
  have hE0 := SP_E hr k L 0 hη0 hη1 hεη
  have hE2 := SP_E hr k L 2 hη0 hη1 hεη
  have hA := SP_A k (by omega : 1 ≤ n) hnη
  have hCh : (0 : ℝ) < ((2 * n).choose 2 : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  set κ := c ^ 2 / (32 * ((2 * n).choose 2 : ℝ)) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  -- `κ ≤ 1/n`
  have hκn : κ ≤ 1 / (n : ℝ) := by
    have hM : (((2 * n - 2 : ℕ) : ℝ) + 1) = 2 * (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hM] at hc4
    have hc2 : c ^ 2 ≤ c ^ 4 := pow_le_pow_right₀ hc1 (by norm_num)
    have hch : ((2 * n).choose 2 : ℝ) = (n : ℝ) * (2 * n - 1) := by
      rw [Nat.cast_choose_two]; push_cast; ring
    rw [hκ, hch, div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith
  have hκ1 : |(-κ)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg hκ0]
    exact hκn.trans (by rw [div_le_one (by linarith)]; linarith)
  have hAE := hA.mul hE0
  have hKE := hE2.smul (-κ) hκ1
  have hW := (hAE.mono (C₁ := Cw) (by simp only [Cw]; linarith) le_rfl le_rfl hη0).add
    (hKE.mono (C₁ := Cw) (by simp only [Cw]; linarith) le_rfl le_rfl hη0)
  set W : ℕ → ℝ := fun j => Afun n j * Efun (m + 1) c L 0 j + (-κ) * Efun (m + 1) c L 2 j with hWdef
  have hq := hW.sub_zero' (by simp only [Cw]; positivity) hη0
  -- `W(0) ≥ 1/2`
  have hA0 : Afun n 0 = 1 := by simp only [Afun, add_zero]; exact div_self hCh.ne'
  have hE00 : Efun (m + 1) c L 0 0 = 1 := by
    simp only [Efun, mul_zero, zero_add]
    rw [Finset.sum_eq_single 0 (fun l _ hl => by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)
      (by simp)]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, muX, pow_zero, mul_one]
    rw [← FXi_eq]; exact div_self (FXi_pos _).ne'
  have hE20 : |Efun (m + 1) c L 2 0| ≤ N2 * C3 := by
    have := abs_SP_le hE2 hη0 hkη hC3 (Nat.zero_le k)
    rwa [pow_zero, mul_one] at this
  have hw0 : 1 / 2 ≤ W 0 := by
    simp only [hWdef, hA0, hE00, one_mul]
    have hnb : 2 * ((N2 : ℝ) * C3) ≤ n := by
      have := Nat.le_ceil (2 * ((N2 : ℝ) * C3))
      have h' : ((⌈2 * ((N2 : ℝ) * C3)⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hnbig
      push_cast at h'; linarith
    have h1 : κ * |Efun (m + 1) c L 2 0| ≤ 1 / 2 := by
      calc κ * |Efun (m + 1) c L 2 0| ≤ (1 / (n : ℝ)) * (N2 * C3) :=
            mul_le_mul hκn hE20 (abs_nonneg _) (by positivity)
        _ ≤ 1 / 2 := by rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith)]; linarith
    have h3 := mul_le_mul_of_nonneg_left (le_abs_self (Efun (m + 1) c L 2 0)) hκ0
    linarith
  have hβ : ∀ j ≤ k, BXi (n + j) = (FXi (m + 1) * (32 * ((2 * n).choose 2 : ℝ))) * (c ^ 2) ^ j *
      (W 0 + (W j - W 0)) := by
    intro j hj
    rw [B_repr L hm hc0.ne' (by omega)]
    simp only [hWdef]; ring
  have hP : 0 < FXi (m + 1) * (32 * ((2 * n).choose 2 : ℝ)) := by
    have := FXi_pos (m + 1); positivity
  refine ⟨?_, ?_⟩
  · have := hβ 0 (Nat.zero_le _)
    rw [add_zero, pow_zero, mul_one, sub_self, add_zero] at this
    rw [this]; exact mul_pos hP (by linarith)
  · exact abs_dlog_of_SP BXi n hq hk le_rfl hP (by positivity) hw0 hβ hη0 (by simp only [Cw]; positivity)
      hkη hsm

/-- **`XiKernelHyp` holds.** -/
theorem xiKernelHyp_holds : XiKernelHyp := by
  refine ⟨?_, fun k hk => ?_⟩
  · obtain ⟨Λ, h⟩ := dlog_BXi_bound 2 le_rfl
    exact h.mono fun n hn => hn.1
  · obtain ⟨Λ, h⟩ := dlog_BXi_bound k hk
    have hlim : Tendsto (fun n : ℕ => |Λ| * (Real.sqrt n * etaN n) ^ k) atTop (𝓝 0) := by
      have := (tendsto_sqrt_etaN.pow k).const_mul |Λ|
      rwa [zero_pow (by omega), mul_zero] at this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [h] with n ⟨_, hn⟩
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
    calc Real.sqrt n ^ k * |dlog BXi n k| ≤ Real.sqrt n ^ k * (|Λ| * etaN n ^ k) :=
          mul_le_mul_of_nonneg_left (hn.trans (mul_le_mul_of_nonneg_right (le_abs_self Λ)
            (pow_nonneg (etaN_nonneg n) k))) (by positivity)
      _ = _ := by ring

/-- **GORZ Theorem 1 for the Riemann Ξ-function, unconditionally**: for every `d`, with
`γ(n)` the Taylor coefficients of `(−1+4z²)Λ(1/2+z) = Σ γ(n) z^{2n}/n!` (Mathlib's `completedRiemannZeta`),
`δ(n) = (2n)^{−1/2}` and `E(n) = γ(n+1)/γ(n)`, the renormalized Jensen polynomials converge to the Hermite
polynomial `H_d` coefficientwise and uniformly on compacts, and `J^{d,n}_γ` is hyperbolic for all large `n`. -/
theorem xi_gorz_unconditional (d : ℕ) :
    (∀ i, Tendsto (fun n => (Jhat gammaMathlib (fun n => gammaMathlib (n + 1) / gammaMathlib n) δXi d n).coeff i)
      atTop (𝓝 ((GORZ.H d).coeff i))) ∧
    (∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
      (fun n x => (Jhat gammaMathlib (fun n => gammaMathlib (n + 1) / gammaMathlib n) δXi d n).eval x)
      (fun x => (GORZ.H d).eval x) atTop K) ∧
    (∀ᶠ n in atTop, Hyperbolic (jensenSeq gammaMathlib d n)) :=
  xi_gorz_mathlib xiKernelHyp_holds d

end GORZXi
