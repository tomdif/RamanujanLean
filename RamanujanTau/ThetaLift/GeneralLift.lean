import RamanujanTau.ThetaLift.Final

/-!
# The Shimura lift for every `G/η^j`

`ThetaLift.Final` proves modularity for the family attached to one prime `ℓ`. Nothing in the theta kernel depends on `ℓ`.
For `j < 24` prime to `6`, an even weight `k' = λ + (j+1)/2`, and a level one cusp form `G` with integer coefficients, the explicit lift of
`G/η^j` at any squarefree `t ≡ -j (mod 24)` is a modular form of weight `2λ` on `Γ₀(6)`. The parity condition
`(-1/t) = (-1)^λ` follows from `k'` being even.
-/

set_option autoImplicit false

namespace RamanujanTau.ThetaLift
open Complex
open UpperHalfPlane hiding I
open ModularForm CongruenceSubgroup Rademacher
open RamanujanTau.TheoremA RamanujanTau.TheoremA.HalfIntegral RamanujanTau.TheoremA.SignLattice BoylanWebb
open scoped Real ComplexConjugate MatrixGroups Topology

noncomputable section

/-- The coordinate `G ↦ G·(q;q)_∞^{-j}`. -/
def genCoord (j : ℕ) (a : PowerSeries ℤ) : PowerSeries ℤ := a * MockTheta5.JTP.partitionGF ^ j

/-- The explicit lift of weight `2λ`. -/
def genLift (j lam t : ℕ) (A : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => ∑ x ∈ n.divisorsAntidiagonal,
    psi t lam x.1 * (chi12 x.2 * A.coeff ((t * x.2 ^ 2 + j) / 24))

variable {j lam : ℕ} {k' : ℤ}

lemma coeff_genLift (t : ℕ) (A : PowerSeries ℤ) (n : ℕ) :
    ((PowerSeries.map (Int.castRingHom ℂ) (genLift j lam t A)).coeff n : ℂ) =
      bC lam t j (fun m => A.coeff m) n := by
  rw [PowerSeries.coeff_map, genLift, PowerSeries.coeff_mk, map_sum]
  unfold bC
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold eT psi jN latI
  rw [chi12_eq_chiZ]
  simp only [eq_intCast]
  push_cast
  ring

/-- The arithmetic of the parameters. -/
structure GenData (j lam t : ℕ) (k' : ℤ) where
  hj : j < 24
  ht2 : ¬ 2 ∣ t
  ht3 : ¬ 3 ∣ t
  hNj : (24 : ℤ) ∣ (t : ℤ) * j + 1
  hjw : j + 1 = 2 * ((j + 1) / 2)
  hk : k' = ((lam + (j + 1) / 2 : ℕ) : ℤ)
  hlam : lam ≠ 0
  hneg : ∀ g, jN t (-g) = (-1) ^ lam * jN t g

/-- The arithmetic facts hold. -/
def genData (hj24 : j < 24) (hj2 : ¬ 2 ∣ j) (hj3 : ¬ 3 ∣ j) (hlam2 : 2 ≤ lam)
    (hk0 : k' = ((lam + (j + 1) / 2 : ℕ) : ℤ)) (hev : Even (lam + (j + 1) / 2)) {t : ℕ} (ht : 24 ∣ t + j) :
    GenData j lam t k' := by
  have ht2 : ¬ 2 ∣ t := by omega
  have ht3 : ¬ 3 ∣ t := by omega
  refine ⟨hj24, ht2, ht3, ?_, by omega, hk0, by omega, ?_⟩
  · obtain ⟨u, hu⟩ := ht
    have hsq := sq_mod_24 hj2 hj3
    obtain ⟨v, hv⟩ : (24 : ℤ) ∣ ((j : ℤ) ^ 2 - 1) := by
      have h : ((j ^ 2 : ℕ) : ℤ) % 24 = 1 := by exact_mod_cast hsq
      push_cast at h
      generalize (j : ℤ) ^ 2 = s at h ⊢
      omega
    refine ⟨u * j - v, ?_⟩
    have hu' : (t : ℤ) + j = 24 * u := by exact_mod_cast hu
    linear_combination (j : ℤ) * hu' - hv
  · intro g
    have hodd : Odd t := Nat.odd_iff.mpr (by omega)
    have hev' := Nat.even_iff.mp hev
    have hm : jN t (-1) = (-1) ^ lam := by
      unfold jN
      rw [jacobiSym.at_neg_one hodd]
      rcases (by omega : j % 4 = 1 ∨ j % 4 = 3) with h | h
      · have ht4 : t % 4 = 3 := by omega
        have hodd2 : Odd lam := Nat.odd_iff.mpr (by omega)
        rw [ZMod.χ₄_nat_three_mod_four ht4, hodd2.neg_one_pow]
        simp
      · have ht4 : t % 4 = 1 := by omega
        have heven : Even lam := Nat.even_iff.mpr (by omega)
        rw [ZMod.χ₄_nat_one_mod_four ht4, heven.neg_one_pow]
        simp
    have e : -g = -1 * g := by ring
    rw [e, jN_mul, hm]

/-- The double sum is holomorphic. -/
theorem gen_lamSum_differentiableAt (hj24 : j < 24) (hj2 : ¬ 2 ∣ j) (hj3 : ¬ 3 ∣ j) (hlam2 : 2 ≤ lam)
    (hk0 : k' = ((lam + (j + 1) / 2 : ℕ) : ℤ)) (hev : Even (lam + (j + 1) / 2)) {a : PowerSeries ℤ} (G : CuspForm 𝒮ℒ k')
    (hG : PowerSeries.map (Int.castRingHom ℂ) a = qExpansion (1 : ℝ) G) {t : ℕ} (hN : 0 < t)
    (hsf : Squarefree t) (ht : 24 ∣ t + j) {w : ℂ} (hw : 0 < w.im) :
    DifferentiableAt ℂ
      (fun w : ℂ => lamSum G (j) (N := t) (jN t) (lam) w.re w.im) w := by
  obtain ⟨hj, ht2, ht3, hNj, hjw, hk, hlam, hneg⟩ := genData hj24 hj2 hj3 hlam2 hk0 hev ht
  set A : ℕ → ℤ := fun m => (genCoord j a).coeff m with hAdef
  have hA : ∀ m, cA G (j) m = ((A m : ℤ) : ℂ) := by
    intro m
    have h := qExp_hP G (j) hG
    have e : genCoord j a = a * MockTheta5.JTP.partitionGF ^ j := by
      rfl
    unfold cA
    rw [h, PowerSeries.coeff_map]
    simp [hAdef, e]
  obtain ⟨C, E, hAb⟩ := coord_bound G hj hA
  obtain ⟨Cb, hCb0, hCb⟩ := sum_bound (A := A) hlam hAb t (j)
  set b : ℕ → ℂ := bC (lam) t (j) A with hb
  have hbb : ∀ n : ℕ, 1 ≤ n → ‖b n‖ ≤ Cb * (n : ℝ) ^ (lam + 2 * E) := fun n hn =>
    (norm_sum_le _ _).trans (hCb n hn)
  have hqeq : ∀ s : ℂ, qN t s.re s.im = cexp (2 * π * I * t * s) := by
    intro s
    unfold qN
    rw [Complex.re_add_im]
  have hq1 : ‖cexp (2 * π * I * t * w)‖ < 1 := by
    rw [← hqeq]
    exact norm_qN_lt hN hw w.re
  have hd : DifferentiableAt ℂ (qS b) (cexp (2 * π * I * t * w)) := by
    refine (qS_diff b hbb).differentiableAt (Metric.isOpen_ball.mem_nhds ?_)
    simpa using hq1
  have hcomp : DifferentiableAt ℂ (fun s : ℂ => (chiZ (t : ℤ) : ℂ) * qS b (cexp (2 * π * I * t * s))) w := by
    have hinner : DifferentiableAt ℂ (fun s : ℂ => cexp (2 * π * I * t * s)) w := by fun_prop
    exact (DifferentiableAt.comp w hd hinner).const_mul _
  refine hcomp.congr_of_eventuallyEq ?_
  have hopen : {s : ℂ | 0 < s.im} ∈ 𝓝 w :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hw
  filter_upwards [hopen] with s hs
  rw [lamSum_eq G (j) (A := A) hlam hN hsf ht hA hAb s.re hs, hqeq]
  rfl

/-- **The lift is modular, once the double sum is covariant.** -/
theorem gen_raised_of_covariant (hj24 : j < 24) (hj2 : ¬ 2 ∣ j) (hj3 : ¬ 3 ∣ j) (hlam2 : 2 ≤ lam)
    (hk0 : k' = ((lam + (j + 1) / 2 : ℕ) : ℤ)) (hev : Even (lam + (j + 1) / 2)) {a : PowerSeries ℤ} (G : CuspForm 𝒮ℒ k')
    (hG : PowerSeries.map (Int.castRingHom ℂ) a = qExpansion (1 : ℝ) G) {t : ℕ}
    (hsf : Squarefree t) (ht : 24 ∣ t + j) [NeZero t] [NeZero (6 * t)]
    (hcov : ∀ (γ : SL(2, ℤ)) {E : ℤ}, γ 1 0 = 6 * (t : ℤ) * E → ∀ {w : ℂ}, 0 < w.im →
      lamSum G (j) (N := t) (jN t) (lam) (mob γ w).re (mob γ w).im =
        lin γ w ^ (2 * lam) * lamSum G (j) (N := t) (jN t) (lam) w.re w.im) :
    ∃ g : ModularForm (Gamma0 (6 * t) : Subgroup (GL (Fin 2) ℝ)) ((2 * lam : ℕ) : ℤ),
      qExpansion 1 g = PowerSeries.expand t (NeZero.ne t)
        (PowerSeries.map (Int.castRingHom ℂ) (genLift j lam t (genCoord j a))) := by
  have hN : 0 < t := Nat.pos_of_ne_zero (NeZero.ne t)
  obtain ⟨hj, ht2, ht3, hNj, hjw, hk, hlam, hneg⟩ := genData hj24 hj2 hj3 hlam2 hk0 hev ht
  set w := (j + 1) / 2 with hwdef
  set A : ℕ → ℤ := fun m => (genCoord j a).coeff m with hAdef
  have hA : ∀ m, cA G j m = ((A m : ℤ) : ℂ) := by
    intro m
    have h := qExp_hP G j hG
    unfold cA
    have e : genCoord j a = a * MockTheta5.JTP.partitionGF ^ j := by
      rfl
    rw [h, PowerSeries.coeff_map]
    simp [hAdef, e]
  obtain ⟨C, E, hAb⟩ := coord_bound G hj hA
  obtain ⟨Cb, hCb0, hCb⟩ := sum_bound (A := A) hlam hAb t j
  set b : ℕ → ℂ := bC lam t j A with hb
  have hmap : PowerSeries.map (Int.castRingHom ℂ) (genLift j lam t (genCoord j a)) = PowerSeries.mk b := by
    ext n
    rw [PowerSeries.coeff_mk]
    exact coeff_genLift t (genCoord j a) n
  rw [hmap]
  set c : ℕ → ℂ := fun k => (PowerSeries.expand t (NeZero.ne t) (PowerSeries.mk b)).coeff k with hc
  have hcbd : ∀ k : ℕ, 1 ≤ k → ‖c k‖ ≤ Cb * (k : ℝ) ^ (lam + 2 * E) := by
    intro k hk
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    by_cases hd : t ∣ k
    · obtain ⟨n, rfl⟩ := hd
      have hn : 1 ≤ n := by
        by_contra h0
        have : n = 0 := by omega
        simp [this] at hk
      have h1 : c (t * n) = b n := by
        simp only [hc]
        rw [PowerSeries.coeff_expand_mul, PowerSeries.coeff_mk]
      rw [h1]
      have h2 : ‖b n‖ ≤ Cb * (n : ℝ) ^ (lam + 2 * E) := (norm_sum_le _ _).trans (hCb n hn)
      refine h2.trans ?_
      have hle : (n : ℝ) ≤ ((t * n : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_mul_of_pos_left n hN
      gcongr
    · have h1 : c k = 0 := by
        simp only [hc]
        exact PowerSeries.coeff_expand_of_not_dvd t (NeZero.ne t) _ hd
      rw [h1, norm_zero]
      positivity
  have hval : ∀ z : ℍ, lamSum G j (N := t) (jN t) lam (z : ℂ).re (z : ℂ).im =
      (chiZ (t : ℤ) : ℂ) * fS c z := by
    intro z
    rw [lamSum_eq G j (A := A) hlam hN hsf ht hA hAb _ z.2]
    congr 1
    exact (fS_eq hN b z).symm
  have hχ : ((chiZ (t : ℤ) : ℤ) : ℂ) ≠ 0 := by exact_mod_cast chiZ_ne_zero ht2 ht3
  have hinv : ∀ ε : SL(2, ℤ), ((6 * t : ℕ) : ℤ) ∣ ε 1 0 →
      fS c ∣[((2 * lam : ℕ) : ℤ)] ε = fS c := by
    rintro ε ⟨E', hE'⟩
    ext z
    rw [ModularForm.SL_slash_apply]
    have hE : ε 1 0 = 6 * (t : ℤ) * E' := by rw [hE']; push_cast; rfl
    have h := hcov ε hE z.2
    have hmob : mob ε (z : ℂ) = ((ε • z : ℍ) : ℂ) := mob_eq ε z
    rw [hmob, hval, hval] at h
    have hden : denom ε z = lin ε (z : ℂ) := by simp [denom, lin]
    rw [hden]
    have hj' : lin ε (z : ℂ) ≠ 0 := denom_ne_zero' ε z.2
    have h2 := mul_left_cancel₀ hχ (h.trans (by ring :
      lin ε (z : ℂ) ^ (2 * lam) * ((chiZ (t : ℤ) : ℂ) * fS c z) =
        (chiZ (t : ℤ) : ℂ) * (lin ε (z : ℂ) ^ (2 * lam) * fS c z)))
    rw [h2, zpow_neg, zpow_natCast]
    field_simp
  obtain ⟨g, hg⟩ := exists_form c (k := 2 * lam) (M := 6 * t) hcbd hinv
  refine ⟨g, ?_⟩
  rw [hg]
  ext k
  simp [hc]

/-- **`AADRaisedModularity` for `t ≠ 1`.** -/
theorem gen_raised_of_ne_one (hj24 : j < 24) (hj2 : ¬ 2 ∣ j) (hj3 : ¬ 3 ∣ j) (hlam2 : 2 ≤ lam)
    (hk0 : k' = ((lam + (j + 1) / 2 : ℕ) : ℤ)) (hev : Even (lam + (j + 1) / 2)) {a : PowerSeries ℤ} (G : CuspForm 𝒮ℒ k')
    (hG : PowerSeries.map (Int.castRingHom ℂ) a = qExpansion (1 : ℝ) G) {t : ℕ}
    (hsf : Squarefree t) (ht : 24 ∣ t + j) (ht1 : t ≠ 1) [NeZero t] [NeZero (6 * t)] :
    ∃ g : ModularForm (Gamma0 (6 * t) : Subgroup (GL (Fin 2) ℝ)) ((2 * lam : ℕ) : ℤ),
      qExpansion 1 g = PowerSeries.expand t (NeZero.ne t)
        (PowerSeries.map (Int.castRingHom ℂ) (genLift j lam t (genCoord j a))) := by
  have hN : 0 < t := Nat.pos_of_ne_zero (NeZero.ne t)
  obtain ⟨hj, ht2, ht3, hNj, hjw, hk, hlam, hneg⟩ := genData hj24 hj2 hj3 hlam2 hk0 hev ht
  have hψ0 : jN t 0 = 0 := by
    unfold jN
    have h0 : jacobiSym 0 t = 0 := jacobiSym.eq_zero_iff.mpr ⟨hN.ne', by simpa using ht1⟩
    simp [h0]
  refine gen_raised_of_covariant hj24 hj2 hj3 hlam2 hk0 hev G hG hsf ht fun γ E hE w hw => ?_
  exact lamSum_covariant G (j) hN (lam) hlam hj hNj ht2 ht3 ht hjw hk hψ0 hneg γ hE hw

/-- **`AADRaisedModularity` for `t = 1`.** -/
theorem gen_raised_of_one (hj24 : j < 24) (hj2 : ¬ 2 ∣ j) (hj3 : ¬ 3 ∣ j) (hlam2 : 2 ≤ lam)
    (hk0 : k' = ((lam + (j + 1) / 2 : ℕ) : ℤ)) (hev : Even (lam + (j + 1) / 2)) {a : PowerSeries ℤ} (G : CuspForm 𝒮ℒ k')
    (hG : PowerSeries.map (Int.castRingHom ℂ) a = qExpansion (1 : ℝ) G)
    (ht : 24 ∣ 1 + j) [NeZero (1 : ℕ)] [NeZero (6 * 1 : ℕ)] :
    ∃ g : ModularForm (Gamma0 (6 * 1) : Subgroup (GL (Fin 2) ℝ)) ((2 * lam : ℕ) : ℤ),
      qExpansion 1 g = PowerSeries.expand 1 (NeZero.ne 1)
        (PowerSeries.map (Int.castRingHom ℂ) (genLift j lam 1 (genCoord j a))) := by
  obtain ⟨hj, ht2, ht3, hNj, hjw, hk, hlam, hneg⟩ := genData hj24 hj2 hj3 hlam2 hk0 hev ht
  obtain ⟨μ, hμ⟩ : ∃ μ, lam = μ + 1 := ⟨lam - 1, by omega⟩
  have hμ0 : μ ≠ 0 := by omega
  refine gen_raised_of_covariant hj24 hj2 hj3 hlam2 hk0 hev G hG squarefree_one ht fun γ E hE w hw => ?_
  have hT : ∀ t : ℂ, 0 < t.im → DifferentiableAt ℂ
      (fun t : ℂ => lamSum G (j) (N := 1) (jN 1) (μ + 1) t.re t.im) t := by
    intro t ht'
    have := gen_lamSum_differentiableAt hj24 hj2 hj3 hlam2 hk0 hev G hG one_pos squarefree_one ht ht'
    rwa [hμ] at this
  rw [hμ] at hk hneg ⊢
  have h := defect_one G (j) μ hμ0 hj hNj ht hjw hk hneg hT γ hE hw
  unfold defectT at h
  exact sub_eq_zero.mp h

/-- **Modularity of the lift of `G/η^j`, on `Γ₀(6t)`.** -/
theorem gen_raised (hj24 : j < 24) (hj2 : ¬ 2 ∣ j) (hj3 : ¬ 3 ∣ j) (hlam2 : 2 ≤ lam)
    (hk0 : k' = ((lam + (j + 1) / 2 : ℕ) : ℤ)) (hev : Even (lam + (j + 1) / 2))
    {a : PowerSeries ℤ} (G : CuspForm 𝒮ℒ k')
    (hG : PowerSeries.map (Int.castRingHom ℂ) a = qExpansion (1 : ℝ) G) {t : ℕ}
    (hsf : Squarefree t) (ht : 24 ∣ t + j) [NeZero t] [NeZero (6 * t)] :
    ∃ g : ModularForm (Gamma0 (6 * t) : Subgroup (GL (Fin 2) ℝ)) ((2 * lam : ℕ) : ℤ),
      qExpansion 1 g = PowerSeries.expand t (NeZero.ne t)
        (PowerSeries.map (Int.castRingHom ℂ) (genLift j lam t (genCoord j a))) := by
  by_cases ht1 : t = 1
  · subst ht1
    exact gen_raised_of_one hj24 hj2 hj3 hlam2 hk0 hev G hG ht
  · exact gen_raised_of_ne_one hj24 hj2 hj3 hlam2 hk0 hev G hG hsf ht ht1

/-- **The Shimura lift of `G/η^j` is a modular form of weight `2λ` on `Γ₀(6)`.** -/
theorem gen_modular (hj24 : j < 24) (hj2 : ¬ 2 ∣ j) (hj3 : ¬ 3 ∣ j) (hlam2 : 2 ≤ lam)
    (hk0 : k' = ((lam + (j + 1) / 2 : ℕ) : ℤ)) (hev : Even (lam + (j + 1) / 2))
    {a : PowerSeries ℤ} (G : CuspForm 𝒮ℒ k')
    (hG : PowerSeries.map (Int.castRingHom ℂ) a = qExpansion (1 : ℝ) G) {t : ℕ}
    (hsf : Squarefree t) (ht : 24 ∣ t + j) :
    ∃ f : ModularForm (Gamma0 6 : Subgroup (GL (Fin 2) ℝ)) ((2 * lam : ℕ) : ℤ),
      PowerSeries.map (Int.castRingHom ℂ) (genLift j lam t (genCoord j a)) = qExpansion 1 f := by
  haveI : NeZero t := ⟨hsf.ne_zero⟩
  haveI : NeZero (6 * t) := ⟨mul_ne_zero (by norm_num) hsf.ne_zero⟩
  obtain ⟨g, hg⟩ := gen_raised hj24 hj2 hj3 hlam2 hk0 hev G hG hsf ht
  obtain ⟨f, hf⟩ := LevelLowering.exists_lowered (M := 6) (t := t) g _ hg
  exact ⟨f, hf.symm⟩

end

end RamanujanTau.ThetaLift
