import RamanujanTau.FiniteArithmetic.Rank2Lift

/-!
# Rank two: the contracting error modulo `ℓ²`

`obs = Σ wₖ a_{k+1}` is a coefficient functional that kills `U` of the double-cusp plane
modulo `ℓ` (`hkill`). For `F` in the first even envelope, `obs(Y F)` modulo `ℓ²` depends only
on the reduction of `F`: it is `ℓ Σ cᵢ zᵢ` with `zᵢ = obs(Y f̃ᵢ)/ℓ` (`obs_Y`). If moreover
`D F ≡ 0 (mod ℓ)`, the observation is multiplied by a scalar `θ` (`divided_step`).
This generalizes `Error29` and `ErrorDynamics29` to a three-form basis.
-/
set_option autoImplicit false

namespace RamanujanTau.FiniteArithmetic.Rank2
open PowerSeries BoylanWebb AtkinOBrien AtkinOBrienFinal

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- The observation `F ↦ Σ wₖ a_{k+1}(F)`. -/
noncomputable def obs (w : Fin 3 → ℤ) : PS ℓ →ₗ[ℤ_[ℓ]] ℤ_[ℓ] :=
  ∑ k : Fin 3, ((w k : ℤ) : ℤ_[ℓ]) • PowerSeries.coeff (k.val + 1)

lemma obs_apply (w : Fin 3 → ℤ) (F : PS ℓ) :
    obs w F = ∑ k : Fin 3, ((w k : ℤ) : ℤ_[ℓ]) * coeff (k.val + 1) F := by
  simp [obs]

lemma obs_reduce (w : Fin 3 → ℤ) (F : PS ℓ) : PadicInt.toZMod (obs w F) =
    ∑ k : Fin 3, ((w k : ℤ) : ZMod ℓ) * coeff (k.val + 1) (PowerSeries.map (PadicInt.toZMod (p := ℓ)) F) := by
  rw [obs_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_intCast, coeff_map]

noncomputable def Yop : Module.End ℤ_[ℓ] (PS ℓ) := (Ulin ℓ).comp (Dlin ℓ)

/-- The mod-`ℓ²` data. -/
structure Data2 (ℓ : ℕ) [Fact ℓ.Prime] extends Data ℓ where
  P : Fin 3 → Poly ℓ
  hP : ∀ i, ModP.Iso (P i) (ℓ - 1)
  hev : ∀ i, ModP.ev ℤ_[ℓ] (P i) = PowerSeries.map (Int.castRingHom ℤ_[ℓ]) (f i)
  hBinvB : ∀ i j, ∑ k, Binv i k * B k j = if i = j then 1 else 0
  w : Fin 3 → ℤ
  lam : ZMod ℓ
  /-- `ω U = λ B₀`, with `ωⱼ = Σₖ wₖ B k j`: `obs ∘ U` kills the double-cusp plane. -/
  hkill : ∀ i, ∑ j, (∑ k, ((w k : ℤ) : ZMod ℓ) * B k j) * Umat j i = lam * B 0 i
  z : Fin 3 → ℤ
  hz : ∀ i, ∃ t : ℤ_[ℓ], obs w (Yop (PowerSeries.map (Int.castRingHom ℤ_[ℓ]) (f i) *
    Einv ℓ hℓ5)) = (ℓ : ℤ_[ℓ]) * ((z i : ℤ_[ℓ]) + ℓ * t)
  θ : ZMod ℓ
  μ : Fin 3 → ZMod ℓ
  hθ : ∀ i, ((z i : ℤ) : ZMod ℓ) = θ * (∑ k, ((w k : ℤ) : ZMod ℓ) * B k i) + ∑ j, μ j * Dmat j i

namespace Data2
variable (D : Data2 ℓ)

/-- `ωᵢ = obs(fᵢ)` modulo `ℓ`. -/
def ω (i : Fin 3) : ZMod ℓ := ∑ k, ((D.w k : ℤ) : ZMod ℓ) * D.B k i

noncomputable def fLift (i : Fin 3) : PS ℓ :=
  PowerSeries.map (Int.castRingHom ℤ_[ℓ]) (D.f i) * Einv ℓ D.hℓ5

lemma obsBar_comb (e : Fin 3 → ZMod ℓ) :
    ∑ k : Fin 3, ((D.w k : ℤ) : ZMod ℓ) * coeff (k.val + 1) (D.comb e) = ∑ i, D.ω i * e i := by
  simp only [Data.coeff_comb, ω, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

lemma comb_zero_iff (v : Fin 3 → ZMod ℓ) (h : D.comb v = 0) : v = 0 := by
  have hl : ∀ k : Fin 3, ∑ i, D.B k i * v i = 0 := fun k => by
    rw [← D.coeff_comb, h, map_zero]
  ext i
  have : v i = ∑ k, D.Binv i k * (∑ j, D.B k j * v j) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ j, ∑ k, D.Binv i k * (D.B k j * v j) = (if i = j then 1 else 0) * v j := fun j => by
      rw [← D.hBinvB i j, Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
    simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [this]; simp [hl]

lemma comb_inj {v v' : Fin 3 → ZMod ℓ} (h : D.comb v = D.comb v') : v = v' := by
  have h0 : D.comb (v + (-1 : ZMod ℓ) • v') = 0 := by
    rw [D.comb_add, D.comb_smul, h, map_neg, map_one]; ring
  have := D.comb_zero_iff _ h0
  ext i; have hi := congrFun this i; simp at hi; linear_combination hi

variable (h29 : 29 ≤ ℓ) (h24 : 24 * δ ℓ + 1 = ℓ ^ 2)

/-! ### Lifts and decomposition -/

theorem fraction_env (P : Poly ℓ) (hP : ModP.Iso P (ℓ - 1)) :
    Env ℓ D.hℓ5 1 (α ℓ) (ModP.ev ℤ_[ℓ] P * Einv ℓ D.hℓ5) := by
  intro N
  obtain ⟨c, hc, hc0, hDv⟩ := DBound.decompN D.hℓ5 N 1 P (by simpa using hP)
  refine ⟨2, c, hc, by simpa only [pow_one] using hDv, fun i => ?_⟩
  by_cases hi : i ≤ 1
  · have hα : α ℓ i ≤ 1 := by
      interval_cases i
      · exact (α_zero_le D.hℓ5)
      · unfold α
        rw [Int.ceil_le]
        have : (0 : ℚ) < (ℓ : ℚ) + 1 := by positivity
        rw [div_le_iff₀ this]
        push_cast; linarith
    have he : (max 0 (α ℓ i - 1)).toNat = 0 := by omega
    rw [he]
    exact ⟨c i, by simp⟩
  · rw [hc0 i (by omega)]
    exact Dvd_zero _

lemma fLift_env (i : Fin 3) : Env ℓ D.hℓ5 1 (α ℓ) (D.fLift i) := by
  have h := D.fraction_env (D.P i) (D.hP i)
  rwa [D.hev i] at h

lemma fLift_cusp (i : Fin 3) : coeff 0 (D.fLift i) = 0 := by
  rw [fLift, coeff_zero_eq_constantCoeff, map_mul, ← coeff_zero_eq_constantCoeff, coeff_map,
    D.cusp i, map_zero, zero_mul]

lemma fLift_reduce (i : Fin 3) :
    PowerSeries.map (PadicInt.toZMod (p := ℓ)) (D.fLift i) = Ψ ℓ (D.f i) := by
  rw [fLift, map_mul, map_map_int, map_Einv, mul_one]

lemma map_sum_lift (c : Fin 3 → ℤ_[ℓ]) :
    PowerSeries.map (PadicInt.toZMod (p := ℓ)) (∑ i, c i • D.fLift i) =
      D.comb (fun i => PadicInt.toZMod (c i)) := by
  simp only [map_sum, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, D.fLift_reduce, Data.comb]

include h29 in
/-- Every cusp in the first even envelope has three coordinates and a divided tail. -/
theorem decompose (F : PS ℓ) (hF : F ∈ envSub D.hℓ5 1 (α ℓ)) :
    ∃ c : Fin 3 → ℤ_[ℓ], ∃ R : PS ℓ, Env ℓ D.hℓ5 2 (α ℓ) R ∧
      F = ∑ i, c i • D.fLift i + (ℓ : ℤ_[ℓ]) • R := by
  obtain ⟨a, ha, he⟩ := envelope_reduction D.hℓ5 (α ℓ)
    (fun i hi => (envelopes_ge_two (by omega : 13 ≤ ℓ) i hi).1) F hF.2
  have ha0 : coeff 0 (Ψ ℓ a) = 0 := by rw [he, coeff_map, hF.1, map_zero]
  set e : Fin 3 → ZMod ℓ := fun i => ∑ k : Fin 3, D.Binv i k * coeff (k.val + 1) (Ψ ℓ a)
  have hae : Ψ ℓ a = D.comb e := D.cusp_eq a ha ha0
  let c : Fin 3 → ℤ_[ℓ] := fun i => ((e i).val : ℕ)
  have hc : (fun i => PadicInt.toZMod (c i)) = e := funext fun i => lift_val (e i)
  obtain ⟨R, hR⟩ := PS_dvd_of_map (F - ∑ i, c i • D.fLift i) (by
    rw [map_sub, D.map_sum_lift, hc, ← hae, he, sub_self])
  have hm : F - ∑ i, c i • D.fLift i ∈ envSub D.hℓ5 1 (α ℓ) := by
    refine (envSub _ _ _).sub_mem hF (Submodule.sum_mem _ fun i _ => ?_)
    exact (envSub _ _ _).smul_mem _ ⟨D.fLift_cusp i, D.fLift_env i⟩
  refine ⟨c, R, ?_, ?_⟩
  · simpa using env_div D.hℓ5 1 (α ℓ) hm.2 hR
  · rw [← hR]; abel

/-! ### The tail and the observation -/

include h29 h24 in
/-- `obs ∘ Y` kills the divided tail modulo `ℓ`. -/
theorem tail_killed (R : PS ℓ) (hR : Env ℓ D.hℓ5 2 (α ℓ) R) :
    PadicInt.toZMod (obs D.w (Yop R)) = 0 := by
  have hD := D_env D.hℓ5 (by omega) (bounds h29).2 2 le_rfl R hR
  obtain ⟨a, ha, he⟩ := envelope_reduction D.hℓ5 (β ℓ)
    (fun i hi => (envelopes_ge_two (by omega : 13 ≤ ℓ) i hi).2) _ hD
  have ha0 : coeff 0 (Ψ ℓ a) = 0 := by rw [he, coeff_map, D_coeff_low h29 _ 0 (by decide), map_zero]
  have ha1 : coeff 1 (Ψ ℓ a) = 0 := by rw [he, coeff_map, D_coeff_low h29 _ 1 (by decide), map_zero]
  set e : Fin 3 → ZMod ℓ := fun i => ∑ k : Fin 3, D.Binv i k * coeff (k.val + 1) (Ψ ℓ a)
  have hae : Ψ ℓ a = D.comb e := D.cusp_eq a ha ha0
  have hl0 : ∑ i, D.B 0 i * e i = 0 := by
    rw [← D.coeff_comb e 0, ← hae]; exact ha1
  rw [obs_reduce]
  change ∑ k : Fin 3, _ * coeff _ (PowerSeries.map _ (U ℓ (Dlin ℓ R))) = 0
  rw [map_U, ← he, hae, D.U_comb, D.obsBar_comb]
  simp only [mv, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ j, ∑ i, D.ω i * (D.Umat i j * e j) = D.lam * D.B 0 j * e j := fun j => by
    rw [← D.hkill j, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by simp only [ω]; ring
  simp only [this]
  rw [show ∑ j, D.lam * D.B 0 j * e j = D.lam * ∑ j, D.B 0 j * e j by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring, hl0, mul_zero]

lemma exists_of_toZMod {x : ℤ_[ℓ]} (h : PadicInt.toZMod x = 0) : ∃ s, x = (ℓ : ℤ_[ℓ]) * s := by
  have hm : x ∈ RingHom.ker (PadicInt.toZMod (p := ℓ)) := h
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
  have := (PadicInt.mem_nonunits.mp hm)
  rw [PadicInt.norm_lt_one_iff_dvd] at this
  obtain ⟨s, hs⟩ := this
  exact ⟨s, hs⟩

include h29 h24 in
/-- `obs(Y F) = ℓ (Σ cᵢ zᵢ + ℓ w)`. -/
theorem obs_Y (F R : PS ℓ) (c : Fin 3 → ℤ_[ℓ]) (hR : Env ℓ D.hℓ5 2 (α ℓ) R)
    (h : F = ∑ i, c i • D.fLift i + (ℓ : ℤ_[ℓ]) • R) :
    ∃ w' : ℤ_[ℓ], obs D.w (Yop F) = (ℓ : ℤ_[ℓ]) * (∑ i, c i * (D.z i : ℤ_[ℓ]) + ℓ * w') := by
  obtain ⟨s, hs⟩ := exists_of_toZMod (D.tail_killed h29 h24 R hR)
  choose t ht using D.hz
  refine ⟨∑ i, c i * t i + s, ?_⟩
  rw [h, map_add, map_sum, map_add, map_sum, map_smul, map_smul, smul_eq_mul, hs]
  simp only [map_smul, smul_eq_mul]
  have : ∀ i, c i * obs D.w (Yop (D.fLift i)) = c i * ((ℓ : ℤ_[ℓ]) * ((D.z i : ℤ_[ℓ]) + ℓ * t i)) :=
    fun i => by rw [← ht i]; rfl
  have key : ∑ i, c i * ((ℓ : ℤ_[ℓ]) * ((D.z i : ℤ_[ℓ]) + ℓ * t i)) =
      ℓ * ∑ i, c i * (D.z i : ℤ_[ℓ]) + ℓ * (ℓ * ∑ i, c i * t i) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun i _ => this i, key]
  ring

end Data2

end RamanujanTau.FiniteArithmetic.Rank2
