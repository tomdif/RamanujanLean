import RamanujanTau.ThetaLift.Automorphy
import RamanujanTau.ThetaLift.CosetBridge

/-!
# Folding the kernel

The kernel, multiplied by `v^(λ+1/2) conj 𝔽`, is a sum over the cosets of translates of the function on
the strip.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex MeasureTheory
open UpperHalfPlane hiding I
open scoped Real ComplexConjugate MatrixGroups ModularForm
open Rademacher ModularForm

noncomputable section

/-- The quadratic character. -/
def jN (N : ℕ) (a : ℤ) : ℂ := ((jacobiSym a N : ℤ) : ℂ)

lemma norm_jN_le (N : ℕ) (a : ℤ) : ‖jN N a‖ ≤ 1 := by
  unfold jN
  rcases eq_or_ne N 0 with rfl | hN
  · simp [jacobiSym]
  haveI : NeZero N := ⟨hN⟩
  rcases jacobiSym.trichotomy a N with h | h | h <;> simp [h]

lemma jN_mul (N : ℕ) (a b : ℤ) : jN N (a * b) = jN N a * jN N b := by
  unfold jN
  rw [jacobiSym.mul_left]
  push_cast
  rfl

lemma coprime_of_jN {N : ℕ} (hN : 0 < N) {a : ℤ} (h : jN N a ≠ 0) : IsCoprime a (N : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hc
  apply h
  have h0 : jacobiSym a N = 0 := jacobiSym.eq_zero_iff.mpr ⟨hN.ne', hc⟩
  simp [jN, h0]

variable {k' : ℤ} (G : CuspForm 𝒮ℒ k') (j : ℕ) {N : ℕ} (hN : 0 < N) (lam : ℕ) (ξ y : ℝ) {w : ℕ}

/-- The data of the kernel at `z`. -/
def kd (hy : 0 < y) (N : ℕ) (hN : 0 < N) (ξ : ℝ) (z : ℍ) : KData where
  N := N
  z := z
  ξ := ξ
  y := y
  σ := 0
  hN := hN.ne'
  hz := z.2
  hy := hy

/-- The factor of the integrand on the fundamental domain. -/
def cV' (lam : ℕ) (hN : 0 < N) (z : ℍ) : ℂ :=
  ((z.im ^ ((lam : ℝ) + 1 / 2) : ℝ) : ℂ) * conj (fF G j hN z)

/-- The total sum at a lattice point, with `(0,0)` removed. -/
def fP (hy : 0 < y) (z : ℍ) (p : ℤ × ℤ) : ℂ :=
  open Classical in
  if p = (0, 0) then 0 else
    jN N p.1 * iteratedDeriv lam (fun s => ((kd y hy N hN ξ z).atσ s).dF p.1 p.2) 0

/-- The sign function on `g`. -/
def psiG (N : ℕ) (g : ℤ) : ℂ := if g = 0 then 0 else jN N (-g)

lemma bMap_ne (r : cosetN N) (g : {g : ℤ // g ≠ 0}) : bMap r g ≠ (0, 0) := by
  intro h
  simp only [bMap, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hg := g.2
  have hd : gamR r 1 1 = 0 := by
    have h3 : (g : ℤ) * gamR r 1 1 = 0 := by linarith
    exact (mul_eq_zero.mp h3).resolve_left hg
  have hc0 : gamR r 1 0 / (N : ℤ) = 0 := (mul_eq_zero.mp h2).resolve_left hg
  have hc : gamR r 1 0 = 0 := by
    have := Int.mul_ediv_cancel' (dvd_of_mem N (gamR_mem r))
    rw [hc0, mul_zero] at this
    exact this.symm
  obtain ⟨u, v, huv⟩ := bottom_coprime (gamR r)
  rw [hc, hd] at huv
  simp at huv

include hN in
/-- **The term of the sum at `bMap r g`.** -/
theorem term_fold (ht2 : ¬ 2 ∣ N) (ht3 : ¬ 3 ∣ N) (htj : 24 ∣ N + j) (hjw : j + 1 = 2 * w)
    (hk : k' = ((lam + w : ℕ) : ℤ)) (hy : 0 < y) (z : ℍ) (r : cosetN N) (g : {g : ℤ // g ≠ 0}) :
    cV' G j lam hN z * fP hN lam ξ y hy z (bMap r g) =
      (chiZ N : ℂ) * (sqrt (z : ℂ) * e24 (-3)) *
        (psiG N g * Hg G j hN lam ξ y g (gamR r • z)) := by
  have hg := g.2
  set γ := gamR r with hγ
  have hmem := dvd_of_mem N (gamR_mem r)
  have hA := autom G j hN (lam := lam) (w := w) ht2 ht3 htj hjw hk γ hmem z
  have hT := (kd y hy N hN ξ z).dF_taylor γ g (bMap r g).1 (bMap r g).2 hg
    (by
      change (N : ℤ) * ((g : ℤ) * (γ 1 0 / N)) = g * γ 1 0
      rw [← hγ] at *
      linear_combination (g : ℤ) * Int.mul_ediv_cancel' hmem)
    rfl lam
  have hT' : iteratedDeriv lam (fun s => ((kd y hy N hN ξ z).atσ s).dF (bMap r g).1 (bMap r g).2) 0 =
      (chiZ N : ℂ) * (sqrt (z : ℂ) * e24 (-3)) * (η (z : ℂ) / η (mob γ z)) * (lin γ z)⁻¹ ^ lam *
        hFz lam ξ y g (γ • z) := by
    rw [hT]
    unfold hFz
    rw [← mob_eq]
    rfl
  have hJ : jN N (bMap r g).1 = jN N (-(g : ℤ)) * ((jacobiSym (γ 1 1) N : ℤ) : ℂ) := by
    change jN N (-(g : ℤ) * γ 1 1) = _
    rw [jN_mul]
    rfl
  unfold fP
  rw [if_neg (bMap_ne r g), hJ, hT']
  unfold psiG Hg cV'
  rw [if_neg hg]
  linear_combination ((chiZ N : ℂ) * (sqrt (z : ℂ) * e24 (-3)) * jN N (-(g : ℤ)) *
    hFz lam ξ y g (γ • z)) * hA

/-- The original family is summable. -/
lemma summable_fP (hy : 0 < y) (z : ℍ) : Summable (fP hN lam ξ y hy z) := by
  have h := ((kd y hy N hN ξ z).taylor_dual (jN N) (norm_jN_le N) lam).summable
  refine Summable.of_norm_bounded h.norm fun p => ?_
  unfold fP
  split_ifs
  · simp only [norm_zero]
    positivity
  · exact le_refl _

/-- **Folding the sum over lattice points.** -/
theorem fold_sum (ht2 : ¬ 2 ∣ N) (ht3 : ¬ 3 ∣ N) (htj : 24 ∣ N + j) (hjw : j + 1 = 2 * w)
    (hk : k' = ((lam + w : ℕ) : ℤ)) (hy : 0 < y) (z : ℍ) :
    cV' G j lam hN z * ∑' p : ℤ × ℤ, fP hN lam ξ y hy z p =
      (chiZ N : ℂ) * (sqrt (z : ℂ) * e24 (-3)) *
        ∑' r : cosetN N, fTot G j hN lam ξ y (psiG N) (r.out⁻¹ • z) := by
  have hS := summable_fP hN lam ξ y hy z
  have hinj := bMap_inj (N := N) hN
  have hsupp : Function.support (fP hN lam ξ y hy z) ⊆
      Set.range fun p : cosetN N × {g : ℤ // g ≠ 0} => bMap p.1 p.2 := by
    intro p hp
    have hp' : fP hN lam ξ y hy z p ≠ 0 := hp
    unfold fP at hp'
    split_ifs at hp' with h0
    · exact absurd rfl hp'
    · have hc := coprime_of_jN hN (left_ne_zero_of_mul hp')
      obtain ⟨r, g, hrg⟩ := bMap_surj hN (a := p.1) (m := p.2) hc h0
      exact ⟨(r, g), hrg⟩
  rw [← hinj.tsum_eq hsupp, ← tsum_mul_left]
  have hS2 : Summable fun q : cosetN N × {g : ℤ // g ≠ 0} =>
      cV' G j lam hN z * fP hN lam ξ y hy z (bMap q.1 q.2) :=
    (hS.comp_injective hinj).mul_left _
  rw [hS2.tsum_prod' fun r => hS2.prod_factor r, ← tsum_mul_left]
  refine tsum_congr fun r => ?_
  simp only [term_fold G j hN lam ξ y ht2 ht3 htj hjw hk hy z r]
  rw [tsum_mul_left]
  congr 1
  unfold fTot
  rw [smul_gamR]
  have hsub : Function.support (fun g : ℤ => psiG N g * Hg G j hN lam ξ y g (gamR r • z)) ⊆
      {g : ℤ | g ≠ 0} := by
    intro g hg h0
    apply hg
    have h0' : g = 0 := h0
    simp [h0', psiG]
  exact tsum_subtype_eq_of_support_subset hsub

/-- The seed under translation. -/
lemma hFz_T (g : ℤ) (z : ℍ) : hFz lam ξ y g (ModularGroup.T • z) = e24 1 * hFz lam ξ y g z := by
  have hcoe : ((ModularGroup.T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
    have := UpperHalfPlane.modular_T_smul z
    rw [this]
    simp [add_comm]
  unfold hFz
  rw [hcoe]
  have hf : seed ξ y g ((z : ℂ) + 1) = fun s => e24 1 * seed ξ y g (z : ℂ) s := by
    funext s
    unfold seed
    rw [chiTheta_add_one]
    simp only [add_im, one_im, add_zero]
    ring
  rw [hf, iteratedDeriv_const_mul_field]

include hN in
/-- **The integrand is invariant under translation.** -/
theorem Hg_T (ht2 : ¬ 2 ∣ N) (ht3 : ¬ 3 ∣ N) (htj : 24 ∣ N + j) (hjw : j + 1 = 2 * w)
    (hk : k' = ((lam + w : ℕ) : ℤ)) (g : ℤ) (z : ℍ) :
    Hg G j hN lam ξ y g (ModularGroup.T • z) = Hg G j hN lam ξ y g z := by
  have hmem : (N : ℤ) ∣ ModularGroup.T 1 0 := dvd_of_mem N (T_mem N)
  have hA := autom G j hN (lam := lam) (w := w) ht2 ht3 htj hjw hk ModularGroup.T hmem z
  have hlin : lin ModularGroup.T (z : ℂ) = 1 := by
    simp [lin, ModularGroup.T]
  have hmob : mob ModularGroup.T (z : ℂ) = (z : ℂ) + 1 := by
    simp [mob, ModularGroup.T]
  have hd : ModularGroup.T 1 1 = 1 := by simp [ModularGroup.T]
  have hη : η ((z : ℂ) + 1) = e24 1 * η (z : ℂ) := by
    have := eta_add_int 1 (z : ℂ)
    simpa using this
  have hη0 : η (z : ℂ) ≠ 0 := eta_ne_zero z.2
  have he : e24 1 ≠ 0 := e24_ne_zero 1
  rw [hlin, hmob, hd, hη, jacobiSym.one_left] at hA
  have hquot : η (z : ℂ) / (e24 1 * η (z : ℂ)) = (e24 1)⁻¹ := by
    field_simp
  rw [hquot] at hA
  unfold Hg
  rw [hFz_T]
  have hB : ((((ModularGroup.T • z : ℍ).im) ^ ((lam : ℝ) + 1 / 2) : ℝ) : ℂ) * conj (fF G j hN (ModularGroup.T • z)) =
      ((z.im ^ ((lam : ℝ) + 1 / 2) : ℝ) : ℂ) * conj (fF G j hN z) * (e24 1)⁻¹ := by
    rw [← hA]
    simp
  calc _ = (((((ModularGroup.T • z : ℍ).im) ^ ((lam : ℝ) + 1 / 2) : ℝ) : ℂ) *
        conj (fF G j hN (ModularGroup.T • z))) * (e24 1 * hFz lam ξ y g z) := by ring
    _ = _ := by
      rw [hB]
      field_simp

include hN in
/-- The total integrand is invariant under the translations. -/
theorem fTot_inv (ht2 : ¬ 2 ∣ N) (ht3 : ¬ 3 ∣ N) (htj : 24 ∣ N + j) (hjw : j + 1 = 2 * w)
    (hk : k' = ((lam + w : ℕ) : ℤ)) (ψg : ℤ → ℂ) (a : tSub (T_mem N)) (x : ℍ) :
    fTot G j hN lam ξ y ψg ((a : pSub (gN N))⁻¹ • x) = fTot G j hN lam ξ y ψg x := by
  have hT : ∀ z : ℍ, fTot G j hN lam ξ y ψg (ModularGroup.T • z) = fTot G j hN lam ξ y ψg z := by
    intro z
    unfold fTot
    exact tsum_congr fun g => by rw [Hg_T G j hN lam ξ y ht2 ht3 htj hjw hk]
  have hstep : ∀ z : ℍ, fTot G j hN lam ξ y ψg ((tEl (T_mem N) : pSub (gN N)) • z) =
      fTot G j hN lam ξ y ψg z := hT
  have hpow : ∀ (n : ℤ) (z : ℍ), fTot G j hN lam ξ y ψg (((tEl (T_mem N)) ^ n : pSub (gN N)) • z) =
      fTot G j hN lam ξ y ψg z := by
    intro n
    induction n using Int.induction_on with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [zpow_add_one, mul_smul, ih, hstep]
    | pred n ih =>
      intro z
      rw [zpow_sub_one, mul_smul, ih]
      have := hstep ((tEl (T_mem N) : pSub (gN N))⁻¹ • z)
      rw [smul_inv_smul] at this
      exact this.symm
  obtain ⟨_, n, rfl⟩ := a
  have e : ((tEl (T_mem N) ^ n : pSub (gN N)))⁻¹ = (tEl (T_mem N)) ^ (-n) := (zpow_neg _ n).symm
  change fTot G j hN lam ξ y ψg (((tEl (T_mem N) ^ n : pSub (gN N)))⁻¹ • x) = _
  rw [e, hpow]

/-- The positive parameters of the kernel at `z`. -/
def kvt (N : ℕ) (z : ℍ) : ℝ := z.im / (N * Complex.normSq (z : ℂ))

/-- The conjugate point of the kernel at `z`. -/
def kZc (N : ℕ) (z : ℍ) : ℂ := -1 / (N * conj (z : ℂ))

/-- The factor making the kernel independent of the choice of branch. -/
def qZ (N lam : ℕ) (z : ℍ) : ℂ :=
  (I / (N * (z : ℂ))) ^ lam * ((√(kvt N z / (6 * N)) : ℝ) : ℂ) * (sqrt (z : ℂ))⁻¹

/-- **The integrand on the fundamental domain.** -/
def phiI (lam : ℕ) (w' : ℂ) (z : ℍ) : ℂ :=
  cV' G j lam hN z * qZ N lam z * kernel (jN N) N (kvt N z) (kZc N z) lam w'

/-- The factor which remains after folding. -/
lemma constant_identity (hy : 0 < y) (z : ℍ) :
    qZ N lam z * ((y ^ (2 * lam) : ℝ) : ℂ)⁻¹ * ((kd y hy N hN ξ z).sc ^ lam)⁻¹ *
        ((√(π / (kd y hy N hN ξ z).κ) : ℝ) : ℂ) * sqrt (z : ℂ) =
      (((y ^ lam)⁻¹ * y : ℝ) : ℂ) := by
  set D := kd y hy N hN ξ z with hD
  have hz : (z : ℂ) ≠ 0 := D.z_ne
  have hNC : (N : ℂ) ≠ 0 := D.N_ne
  have hyC : (y : ℂ) ≠ 0 := D.y_ne
  have hπ := Real.pi_pos
  have hκ : 0 < D.κ := D.κ_pos
  have hvt : 0 < D.vt := D.vt_pos
  have hNR : (0 : ℝ) < N := D.NR_pos
  have hvtEq : kvt N z = D.vt := rfl
  have hsqrt : sqrt (z : ℂ) ≠ 0 := by
    rw [sqrt_exp_half hz]
    exact Complex.exp_ne_zero _
  set A : ℂ := I / (N * (z : ℂ)) with hA
  have hA0 : A ≠ 0 := div_ne_zero I_ne_zero (mul_ne_zero hNC hz)
  have hsc : D.sc = A / y := by
    change I / ((N : ℂ) * (z : ℂ) * y) = _
    rw [hA]
    field_simp
  have hroot : √(kvt N z / (6 * N)) * √(π / D.κ) = y := by
    rw [← Real.sqrt_mul (by rw [hvtEq]; positivity)]
    have h1 : kvt N z / (6 * N) * (π / D.κ) = y ^ 2 := by
      rw [hvtEq]
      have hm := D.κ_mul
      change D.κ * (6 * (N : ℝ) * y ^ 2) = π * D.vt at hm
      field_simp
      nlinarith [hm]
    rw [h1, Real.sqrt_sq hy.le]
  have hroot' : ((√(kvt N z / (6 * N)) : ℝ) : ℂ) * ((√(π / D.κ) : ℝ) : ℂ) = y := by
    exact_mod_cast hroot
  unfold qZ
  rw [← hA, hsc, div_pow A]
  push_cast
  have hAp := pow_ne_zero lam hA0
  have hyp := pow_ne_zero lam hyC
  rw [pow_mul' (y : ℂ) 2 lam]
  calc _ = (((√(kvt N z / (6 * N)) : ℝ) : ℂ) * ((√(π / D.κ) : ℝ) : ℂ)) * ((y : ℂ) ^ lam)⁻¹ := by
        field_simp
    _ = _ := by
      rw [hroot']
      ring

/-- **The integrand on the fundamental domain, after folding.** -/
theorem phiI_eq (ht2 : ¬ 2 ∣ N) (ht3 : ¬ 3 ∣ N) (htj : 24 ∣ N + j) (hjw : j + 1 = 2 * w)
    (hk : k' = ((lam + w : ℕ) : ℤ)) (hψ0 : jN N 0 = 0) (hy : 0 < y) (z : ℍ) :
    phiI G j hN lam ((ξ : ℂ) + y * I) z =
      (((y ^ lam)⁻¹ * y : ℝ) : ℂ) * ((chiZ N : ℂ) * e24 (-3)) *
        ∑' r : cosetN N, fTot G j hN lam ξ y (psiG N) (r.out⁻¹ • z) := by
  set D := kd y hy N hN ξ z with hD
  have hfold := fold_sum G j hN lam ξ y ht2 ht3 htj hjw hk hy z
  have hexp := D.kernel_expand (jN N) (norm_jN_le N) lam
  have hsum : ∑' p : ℤ × ℤ, jN N p.1 * iteratedDeriv lam (fun s => (D.atσ s).dF p.1 p.2) 0 =
      ∑' p : ℤ × ℤ, fP hN lam ξ y hy z p := by
    refine tsum_congr fun p => ?_
    unfold fP
    split_ifs with h0
    · rw [h0]
      simp [hψ0]
    · rfl
  rw [hsum] at hexp
  have hsc0 : D.sc ≠ 0 := by
    have hz := D.z_ne
    have hN' := D.N_ne
    have hy' := D.y_ne
    exact div_ne_zero I_ne_zero (mul_ne_zero (mul_ne_zero hN' hz) hy')
  have hscp := pow_ne_zero lam hsc0
  have hS : ∑' x : ℤ × ℤ × ℤ, kTerm (jN N) N (kvt N z) (kZc N z) lam ((ξ : ℂ) + y * I) x =
      (D.sc ^ lam)⁻¹ * (((√(π / D.κ) : ℝ) : ℂ) * ∑' p : ℤ × ℤ, fP hN lam ξ y hy z p) := by
    rw [← hexp, ← mul_assoc, inv_mul_cancel₀ hscp, one_mul]
    rfl
  have hc := constant_identity hN lam ξ y hy z
  have him : ((ξ : ℂ) + y * I).im = y := by simp
  unfold phiI kernel
  rw [him, hS]
  push_cast at hc ⊢
  calc _ = (qZ N lam z * ((y : ℂ) ^ (2 * lam))⁻¹ * (D.sc ^ lam)⁻¹ * ((√(π / D.κ) : ℝ) : ℂ)) *
        (cV' G j lam hN z * ∑' p : ℤ × ℤ, fP hN lam ξ y hy z p) := by ring
    _ = _ := by
      rw [hfold]
      calc _ = (qZ N lam z * ((y : ℂ) ^ (2 * lam))⁻¹ * (D.sc ^ lam)⁻¹ * ((√(π / D.κ) : ℝ) : ℂ) *
            sqrt (z : ℂ)) * ((chiZ N : ℂ) * e24 (-3) *
              ∑' r : cosetN N, fTot G j hN lam ξ y (psiG N) (r.out⁻¹ • z)) := by ring
        _ = _ := by
          rw [hc]
          ring

/-- **The value of the integral over the fundamental domain.** -/
theorem phi_value (hlam : lam ≠ 0) (hj : j < 24) (hNj : (24 : ℤ) ∣ (N : ℤ) * j + 1)
    (ht2 : ¬ 2 ∣ N) (ht3 : ¬ 3 ∣ N) (htj : 24 ∣ N + j) (hjw : j + 1 = 2 * w)
    (hk : k' = ((lam + w : ℕ) : ℤ)) (hψ0 : jN N 0 = 0)
    (hneg : ∀ g, jN N (-g) = (-1) ^ lam * jN N g) (hy : 0 < y) :
    ∫ z in domainOf (gN N), phiI G j hN lam ((ξ : ℂ) + y * I) z =
      ((chiZ N : ℂ) * e24 (-3)) * (2 * (-1) ^ lam * (c0 lam : ℂ)) * lamSum G j (N := N) (jN N) lam ξ y := by
  have hF := isFundamentalDomain_domainOf (gN N) (neg_one_mem N)
  have hSt := exactDomain_strip (T_mem N)
  have hψg : (fun g : ℤ => if g = 0 then (0 : ℂ) else jN N (-g)) = psiG N := rfl
  have hg1 : ∀ g, ‖psiG N g‖ ≤ 1 := by
    intro g
    unfold psiG
    split_ifs
    · simp
    · exact norm_jN_le N _
  have hg0 : psiG N 0 = 0 := by simp [psiG]
  obtain ⟨-, hint, -⟩ := strip_total G j hN lam ξ y (hj := hj) hy hg1 hg0
  have hunf := unfold_integral hF hSt measurableSet_stripSet hint
    (fTot_inv G j hN lam ξ y ht2 ht3 htj hjw hk (psiG N))
  have hclosed := strip_closed G j hN lam ξ y hlam (hj := hj) hNj hy (norm_jN_le N) hneg
  rw [hψg] at hclosed
  simp only [phiI_eq G j hN lam ξ y ht2 ht3 htj hjw hk hψ0 hy]
  rw [integral_const_mul, ← hunf.2, hclosed]
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  push_cast
  field_simp


/-- The character is invariant under the action on `a`. -/
lemma jN_inv (a A k : ℤ) (hA : IsCoprime A (N : ℤ)) : jN N (a * A ^ 2 + N * k) = jN N a := by
  unfold jN
  have h1 : (a * A ^ 2 + (N : ℤ) * k) % (N : ℤ) = (a * A ^ 2) % (N : ℤ) := by
    rw [Int.add_mul_emod_self_left]
  rw [jacobiSym.mod_left' h1, jacobiSym.mul_left,
    jacobiSym.sq_one' (Int.isCoprime_iff_gcd_eq_one.mp hA), mul_one]

lemma chiZ_ne_zero {N : ℕ} (ht2 : ¬ 2 ∣ N) (ht3 : ¬ 3 ∣ N) : chiZ (N : ℤ) ≠ 0 := by
  have hm : ((N : ℤ) % 12) = 1 ∨ ((N : ℤ) % 12) = 5 ∨ ((N : ℤ) % 12) = 7 ∨ ((N : ℤ) % 12) = 11 := by
    omega
  unfold chiZ
  rcases hm with h | h | h | h <;> rw [h] <;> norm_num

include hN in
/-- **The double sum is a modular object on `Γ₀(6N)`.** -/
theorem lamSum_covariant (hlam : lam ≠ 0) (hj : j < 24) (hNj : (24 : ℤ) ∣ (N : ℤ) * j + 1)
    (ht2 : ¬ 2 ∣ N) (ht3 : ¬ 3 ∣ N) (htj : 24 ∣ N + j) (hjw : j + 1 = 2 * w)
    (hk : k' = ((lam + w : ℕ) : ℤ)) (hψ0 : jN N 0 = 0)
    (hneg : ∀ g, jN N (-g) = (-1) ^ lam * jN N g) (γ : SL(2, ℤ)) {E : ℤ}
    (hE : γ 1 0 = 6 * N * E) {t : ℂ} (ht : 0 < t.im) :
    lamSum G j (N := N) (jN N) lam (mob γ t).re (mob γ t).im =
      lin γ t ^ (2 * lam) * lamSum G j (N := N) (jN N) lam t.re t.im := by
  have hNZ : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hγt : 0 < (mob γ t).im := mob_im_pos γ ht
  have e1 : (((mob γ t).re : ℝ) : ℂ) + ((mob γ t).im : ℝ) * I = mob γ t := Complex.re_add_im _
  have e2 : ((t.re : ℝ) : ℂ) + (t.im : ℝ) * I = t := Complex.re_add_im _
  have h1 := phi_value G j hN lam (mob γ t).re (mob γ t).im hlam hj hNj ht2 ht3 htj hjw hk hψ0 hneg hγt
  have h2 := phi_value G j hN lam t.re t.im hlam hj hNj ht2 ht3 htj hjw hk hψ0 hneg ht
  rw [e1] at h1
  rw [e2] at h2
  have hcov : ∀ z : ℍ, phiI G j hN lam (mob γ t) z = lin γ t ^ (2 * lam) * phiI G j hN lam t z := by
    intro z
    unfold phiI
    rw [kernel_covariant (jN N) (N : ℤ) hNZ _ _ lam (fun a A k hA => jN_inv a A k hA) γ hE ht]
    ring
  simp only [hcov] at h1
  rw [integral_const_mul, h2] at h1
  have hc : ((chiZ N : ℂ) * e24 (-3)) * (2 * (-1) ^ lam * (c0 lam : ℂ)) ≠ 0 := by
    have hχ : ((chiZ N : ℤ) : ℂ) ≠ 0 := by exact_mod_cast chiZ_ne_zero ht2 ht3
    have he := e24_ne_zero (-3)
    have h6 : (0 : ℝ) < √6 := Real.sqrt_pos.mpr (by norm_num)
    have hc0 : (c0 lam : ℂ) ≠ 0 := by
      have : (0 : ℝ) < c0 lam := by
        unfold c0
        positivity
      exact_mod_cast this.ne'
    have hs : ((-1 : ℂ) ^ lam) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact mul_ne_zero (mul_ne_zero hχ he) (mul_ne_zero (mul_ne_zero two_ne_zero hs) hc0)
  apply mul_left_cancel₀ hc
  rw [← h1]
  ring

end

end RamanujanTau.ThetaLift
