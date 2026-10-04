/-
# The q-expansion of `T_p f`, and Mordell's theorem for `t`

For a level-one cusp form `f = Σ aₙqⁿ` of weight `k` and a prime `p`,

  `T_p f = Σ (a_{pm} + p^{k−1}·[p ∣ m]·a_{m/p}) q^m`   (`hasSum_hecke`, `qExpansion_hecke`).

The `f(pz)` term contributes `Σ aₙ q^{pn}`. In the averaged translates, the root-of-unity sum
`Σ_{j<p} ζ^{jn} = p·[p ∣ n]` keeps exactly the terms `a_{pm} q^m`.

With weight `12` this builds a `HeckeData` term (`heckeData`). So `TauHeckeMaster` — and with it
`t(mn) = t(m)t(n)` for coprime `m, n` and the Hecke recurrence — holds **unconditionally**.
-/
import RamanujanTau.HeckeForm
import RamanujanTau.HeckeOperator
import RamanujanTau.DiscriminantQExpansion
import RamanujanTau.TauBridge

set_option autoImplicit false

namespace RamanujanTau.Hecke
open Complex UpperHalfPlane ModularForm Filter Finset Function
open scoped MatrixGroups ModularForm Topology Manifold Real

local notation "𝕢" => Periodic.qParam

variable {k : ℤ}

/-- the q-expansion series of a level-one cusp form, read at any point of the upper half plane. -/
lemma hasSum_cusp (f : CuspForm 𝒮ℒ k) {w : ℂ} (hw : 0 < w.im) :
    HasSum (fun n => (qExpansion 1 f).coeff n * 𝕢 1 w ^ n) (f (ofComplex w)) := by
  have h := hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
    (ModularFormClass.holo f) (CuspFormClass.zero_at_infty f).isBoundedAtImInfty (ofComplex w)
  rw [ofComplex_apply_of_im_pos hw] at h ⊢
  simpa [smul_eq_mul] using h

lemma qP_mul (p : ℕ) (z : ℂ) : 𝕢 1 (p * z) = 𝕢 1 z ^ p := by
  simp only [Periodic.qParam, ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]; ring_nf

lemma qP_shift (p j : ℕ) (z : ℂ) :
    𝕢 1 ((z + j) / p) = 𝕢 1 (z / p) * cexp (2 * π * Complex.I / p) ^ j := by
  simp only [Periodic.qParam, ofReal_one, div_one]
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]; ring_nf

variable (p : ℕ) [hp : Fact p.Prime]

lemma root_sum (n : ℕ) :
    ∑ j ∈ range p, (cexp (2 * π * Complex.I / p) ^ j) ^ n = if p ∣ n then (p : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp p hp.out.ne_zero
  simp_rw [← pow_mul, mul_comm _ n, pow_mul]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd n).mpr h]; simp
  · have hc : n.Coprime p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr h))
    exact (hζ.pow_of_coprime n hc).geom_sum_eq_zero hp.out.one_lt

/-- reindexing a series supported on multiples of `p`. -/
lemma hasSum_mul_reindex {F : ℕ → ℂ} {s : ℂ} (hF : ∀ n, ¬ p ∣ n → F n = 0) :
    HasSum (fun m => F (p * m)) s ↔ HasSum F s := by
  have hinj : Injective (fun m : ℕ => p * m) := fun a b h => Nat.eq_of_mul_eq_mul_left hp.out.pos h
  refine hinj.hasSum_iff (fun n hn => hF n fun ⟨m, hm⟩ => hn ⟨m, hm.symm⟩)

/-- **The q-expansion of `T_p f`.** -/
theorem hasSum_hecke (f : CuspForm 𝒮ℒ k) (t : ℍ) :
    HasSum (fun m => ((qExpansion 1 f).coeff (p * m) +
      (p : ℂ) ^ (k - 1) * (if p ∣ m then (qExpansion 1 f).coeff (m / p) else 0)) * 𝕢 1 t ^ m)
      (heckeCusp p f t) := by
  set a := fun n => (qExpansion 1 f).coeff n
  have hpos := hp.out.pos
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hz := t.im_pos
  -- the `f(pz)` part
  have hA : HasSum (fun m => (if p ∣ m then a (m / p) else 0) * 𝕢 1 t ^ m) (f (ofComplex (p * (t : ℂ)))) := by
    rw [← hasSum_mul_reindex p (fun n hn => by simp [hn])]
    have h0 := hasSum_cusp f (im_nat_mul hz hpos)
    simp_rw [qP_mul, ← pow_mul] at h0
    convert h0 using 2 with m
    simp [Nat.mul_div_cancel_left m hpos, a]
  -- the averaged translates
  have hB : HasSum (fun m => (p : ℂ) * a (p * m) * 𝕢 1 t ^ m)
      (∑ j ∈ range p, f (ofComplex (((t : ℂ) + j) / p))) := by
    have h0 := hasSum_sum (s := range p) fun j _ => hasSum_cusp f (im_div_nat (j := j) hz hpos)
    have e : ∀ n, ∑ j ∈ range p, (qExpansion 1 f).coeff n * 𝕢 1 (((t : ℂ) + j) / p) ^ n
        = a n * 𝕢 1 ((t : ℂ) / p) ^ n * (if p ∣ n then (p : ℂ) else 0) := fun n => by
      simp_rw [qP_shift, mul_pow, ← mul_sum, root_sum, a]; ring
    simp_rw [e] at h0
    rw [← hasSum_mul_reindex p (fun n hn => by simp [hn])] at h0
    convert h0 using 2 with m
    have : 𝕢 1 ((t : ℂ) / p) ^ (p * m) = 𝕢 1 t ^ m := by
      rw [pow_mul, ← qP_mul, mul_div_cancel₀ _ hp0]
    rw [this, if_pos (dvd_mul_right p m)]; ring
  have := (hA.mul_left ((p : ℂ) ^ (k - 1))).add (hB.mul_left (p : ℂ)⁻¹)
  convert this using 1
  funext m; field_simp; ring

/-- **The Hecke action on q-expansion coefficients.** -/
theorem qExpansion_hecke (f : CuspForm 𝒮ℒ k) (m : ℕ) :
    (qExpansion 1 (heckeCusp p f)).coeff m = (qExpansion 1 f).coeff (p * m) +
      (p : ℂ) ^ (k - 1) * (if p ∣ m then (qExpansion 1 f).coeff (m / p) else 0) := by
  have h := ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL
    (fun t => by simpa [smul_eq_mul] using hasSum_hecke p f t) m
  rw [mul_ite, mul_zero]; exact h.symm

/-- `T_p` as a ℂ-linear endomorphism. -/
noncomputable def heckeLin : CuspForm 𝒮ℒ k →ₗ[ℂ] CuspForm 𝒮ℒ k where
  toFun := heckeCusp p
  map_add' f g := by
    ext t
    simp only [heckeCusp_apply, heckeH, heckeFun, CuspForm.add_apply, Function.comp_apply, sum_add_distrib]
    ring
  map_smul' c f := by
    ext t
    change heckeH p (c • f) t = c * heckeH p f t
    have e : ∀ x, (c • f) x = c * f x := fun _ => rfl
    simp only [heckeH, heckeFun, Function.comp_apply, e]
    rw [← Finset.mul_sum]; ring

end RamanujanTau.Hecke

namespace RamanujanTau
open Hecke ModularForm UpperHalfPlane
open scoped MatrixGroups

/-- the Hecke operators, `T_p` for primes `p` (and `0` otherwise). -/
noncomputable def heckeT (p : ℕ) : Module.End ℂ (CuspForm 𝒮ℒ 12) :=
  if hp : p.Prime then (haveI := Fact.mk hp; heckeLin p) else 0

/-- **A genuine `HeckeData` term**: constructed Hecke operators with their q-expansion action. -/
noncomputable def heckeData : HeckeData where
  T := heckeT
  coeff f n := (qExpansion 1 f).coeff n
  coeff_smul c f n := by
    have h := qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL) c
    rw [show ((c • f : CuspForm 𝒮ℒ 12) : ℍ → ℂ) = c • (f : ℍ → ℂ) from rfl, h]
    simp
  coeff_discriminant n := by
    rw [tau_eq_tauPS, ← DiscriminantBridge.qExpansion_discriminant_coeff]; rfl
  hecke_action {p} hp f n := by
    haveI := Fact.mk hp
    simp only [heckeT, dif_pos hp]
    rw [show (heckeLin p f) = heckeCusp p f from rfl, qExpansion_hecke]
    norm_num
    split_ifs <;> rfl

/-- **Mordell (1917), unconditionally**: the master Hecke identity for `t`. -/
instance tauHeckeMaster : TauHeckeMaster := heckeData.tauHeckeMaster

/-- **Mordell's theorem**: `τ(mn) = τ(m)τ(n)` for coprime `m, n` (unconditional). -/
theorem tau_mul_coprime {m n : ℕ} (h : m.Coprime n) : τ (m * n) = τ m * τ n :=
  TauMultiplicative.mul_coprime h

/-- the Hecke recurrence `τ(p^{r+1}) = τ(p)τ(p^r) − p¹¹τ(p^{r−1})` (unconditional). -/
theorem tau_hecke_recurrence {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : 1 ≤ r) :
    τ (p ^ (r + 1)) = τ p * τ (p ^ r) - (p : ℤ) ^ 11 * τ (p ^ (r - 1)) :=
  TauHeckeRecurrence.hecke hp r hr

/-- the master identity `τ(p)τ(n) = τ(pn) + p¹¹[p ∣ n]τ(n/p)` (unconditional). -/
theorem tau_master {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 1 ≤ n) :
    τ p * τ n = τ (p * n) + (if p ∣ n then (p : ℤ) ^ 11 * τ (n / p) else 0) :=
  TauHeckeMaster.master hp n hn

end RamanujanTau
