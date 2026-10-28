/-
# Integrality of a homomorphism `G → F_{E''}` from integrality of `w_{E''} ∘ θ`

`K` ultrametric of characteristic `0` with `‖2‖ = ‖3‖ = 1`, `𝒪 = integers K`, `G` a formal group over
`𝒪`, `E'' : y² = x³ + Ax + B` over `K`, `θ : G_K → F_{E''}` a homomorphism over `K` with `θ'(0) = 1`.

**`integral_of_w`**: if `w_{E''}(θ(T)) = T³ · ε(T)` with `ε ∈ 𝒪⟦T⟧`, then `θ ∈ 𝒪⟦T⟧`
(and `A, B ∈ 𝒪`). Proof: put `ζ = (T³ ε)^{1/3} ∈ 𝒪⟦T⟧` and `Ω = w_{E''}^{1/3} ∈ K⟦z⟧`, so `Ω ∘ θ = ζ`.
The invariant differentials give `Ω' · Ψ_{E''} = g(Ω)` with `g = (ζ' Ψ_G) ∘ ζ⁻¹ ∈ 𝒪⟦s⟧`, and
`coeffs_g` reads off `A = -3 g₄`, `B = -(3/2) g₆`. Then `Ω` is integral, and `θ = Ω⁻¹ ∘ ζ`.
-/
import RamanujanTau.VeluDescent.Omega
import RamanujanTau.VeluLubin.Formal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace VeluDescent
open MvPowerSeries EllipticFormal VeluLubin EllipticI2

/-! ### Generic helpers -/

section Generic
variable {R : Type*} [CommRing R]

local notation "R1" => MvPowerSeries Unit R

/-- a compositional inverse of a series with unit Lie derivative. -/
lemma exists_inv (f : R1) (h0 : constantCoeff f = 0)
    (h1 : IsUnit (coeff (Finsupp.single () 1) f)) :
    ∃ g : R1, constantCoeff g = 0 ∧ sb f g = X () ∧ sb g f = X () := by
  have h1' : IsUnit (PowerSeries.coeff 1 (f : PowerSeries R)) := h1
  refine ⟨PowerSeries.substInvOfIsUnit (f : PowerSeries R) h1',
    PowerSeries.constantCoeff_substInvOfIsUnit _ _, ?_, ?_⟩
  · have := PowerSeries.subst_substInvOfIsUnit_left (f : PowerSeries R) h0 h1'
    rw [PowerSeries.subst_def] at this; exact this
  · have := PowerSeries.subst_substInvOfIsUnit_right (f : PowerSeries R) h0 h1'
    rw [PowerSeries.subst_def] at this; exact this

lemma sb_inj {f g : R1} (hf0 : constantCoeff f = 0) (hg0 : constantCoeff g = 0) (hgf : sb g f = X ())
    {u u' : R1} (h : sb f u = sb f u') : u = u' := by
  have e : ∀ u : R1, sb g (sb f u) = u := fun u => by
    rw [sb_sb hg0 hf0, hgf, X_sb]
  rw [← e u, ← e u', h]

lemma sb_mul'' {a : R1} (ha : constantCoeff a = 0) (f g : R1) : sb a (f * g) = sb a f * sb a g :=
  subst_mul (FGL.hs (hc ha)) f g

lemma sb_pow'' {a : R1} (ha : constantCoeff a = 0) (f : R1) (n : ℕ) : sb a (f ^ n) = sb a f ^ n := by
  rw [sb, ← coe_substAlgHom (FGL.hs (hc ha)), map_pow, coe_substAlgHom]

lemma map_v_gen {S : Type*} [CommRing S] (W : WeierstrassCurve R) (f : R →+* S) :
    PowerSeries.map f (v W) = v (W.map f) := by
  have h := map_w W f
  rw [w_eq_X3_mul_v, w_eq_X3_mul_v, map_mul, map_pow, PowerSeries.map_X] at h
  ext n
  have := congrArg (PowerSeries.coeff (n + 3)) h
  rwa [PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_X_pow_mul] at this

lemma X_dvd_of_cc {f : R1} (h : constantCoeff f = 0) : ∃ m : R1, f = X () * m := by
  have : (PowerSeries.X : PowerSeries R) ∣ (f : PowerSeries R) := PowerSeries.X_dvd_iff.2 h
  obtain ⟨m, hm⟩ := this
  exact ⟨m, hm⟩

lemma coeff_one_X_mul (m : R1) : coeff (Finsupp.single () 1) (X () * m) = constantCoeff m := by
  show PowerSeries.coeff 1 (PowerSeries.X * (m : PowerSeries R)) = _
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]; rfl

lemma Psi_map {S : Type*} [CommRing S] (G : FormalGroup R) (f : R →+* S) :
    FGL.Ψ (G.map f) (FGL.T : MvPowerSeries Unit S) =
      MvPowerSeries.map f (FGL.Ψ G (FGL.T : R1)) := by
  rw [FGL.Ψ, FGL.Ψ, FormalGroup.map_toPowerSeries, map_subst (FGL.hs FGL.cc_T0), pd_map']
  congr 1
  funext i; fin_cases i <;> simp [FGL.T]

end Generic

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CharZero K] [DecidableEq K]

local notation "𝒪" => CanonicalIsogeny.integers K
local notation "ι" => Subring.subtype (CanonicalIsogeny.integers K)

lemma isUnit_of_norm_one {x : 𝒪} (h : ‖(x : K)‖ = 1) : IsUnit x := by
  have hx : (x : K) ≠ 0 := by intro e; rw [e, norm_zero] at h; exact zero_ne_one h
  have hi : ‖(x : K)⁻¹‖ ≤ 1 := by rw [norm_inv, h, inv_one]
  refine ⟨⟨x, ⟨(x : K)⁻¹, hi⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
  · simp [hx]
  · simp [hx]

/-- **integrality of `θ` from integrality of `w ∘ θ`**. -/
theorem integral_of_w (G : FormalGroup 𝒪) (A B : K) (θ' : MvPowerSeries Unit K)
    (hθ : Hom (G.map ι) (formalGroup (shortO A B)) θ') (hlie : coeff (Finsupp.single () 1) θ' = 1)
    (ε : MvPowerSeries Unit 𝒪)
    (hw : sb θ' (w (shortO A B) : MvPowerSeries Unit K) = X () ^ 3 * MvPowerSeries.map ι ε)
    (h2 : ‖(2 : K)‖ = 1) (h3 : ‖(3 : K)‖ = 1) :
    ∃ θ : MvPowerSeries Unit 𝒪, MvPowerSeries.map ι θ = θ' := by
  have h3K : (3 : K) ≠ 0 := by intro e; rw [e, norm_zero] at h3; exact zero_ne_one h3
  have h3u : IsUnit (3 : K) := Ne.isUnit h3K
  have h3O : IsUnit (3 : 𝒪) := isUnit_of_norm_one (by simpa using h3)
  have hθ0 : constantCoeff θ' = 0 := hθ.1
  obtain ⟨m, hm⟩ := X_dvd_of_cc hθ0
  have hm1 : constantCoeff m = 1 := by rw [← coeff_one_X_mul, ← hm, hlie]
  obtain ⟨θi, hθi0, -, hθiθ⟩ := exists_inv θ' hθ0 (by rw [hlie]; exact isUnit_one)
  have inj := fun {u u' : MvPowerSeries Unit K} (h : sb θ' u = sb θ' u') => sb_inj hθ0 hθi0 hθiθ h
  set v'' : MvPowerSeries Unit K := (v (shortO A B) : MvPowerSeries Unit K)
  have hv1 : constantCoeff v'' = 1 := cc_v _
  have hwv : (w (shortO A B) : MvPowerSeries Unit K) = X () ^ 3 * v'' := w_eq_X3_mul_v _
  -- `m³ · v''(θ) = ε`
  have hε : m ^ 3 * sb θ' v'' = MvPowerSeries.map ι ε := by
    have e : θ' ^ 3 = X () ^ 3 * m ^ 3 := by rw [hm]; ring
    rw [hwv, sb_mul'' hθ0, sb_pow'' hθ0, sb_X hθ0, e] at hw
    have hX : (X () ^ 3 : MvPowerSeries Unit K) ≠ 0 := pow_ne_zero 3 T_ne_zero
    apply mul_left_cancel₀ hX
    rw [← hw]; ring
  have hε1 : constantCoeff ε = 1 := by
    have := congrArg constantCoeff hε
    rw [map_mul, map_pow, hm1, one_pow, one_mul, sb, FGL.cc_subst _ (hc hθ0), hv1,
      constantCoeff_map] at this
    apply Subtype.val_injective
    simpa using this.symm
  -- cube roots
  obtain ⟨cε, hcε, hcε1⟩ := exists_cube_root h3O ε hε1
  obtain ⟨c'', hc'', hc''1⟩ := exists_cube_root h3u v'' hv1
  set ζ₀ : MvPowerSeries Unit 𝒪 := X () * cε
  set Ω : MvPowerSeries Unit K := X () * c''
  have hΩ0 : constantCoeff Ω = 0 := by simp [Ω]
  have hζ0 : constantCoeff ζ₀ = 0 := by simp [ζ₀]
  have hζ : sb θ' Ω = MvPowerSeries.map ι ζ₀ := by
    have hu : m * sb θ' c'' = MvPowerSeries.map ι cε := by
      refine cube_root_unique h3K ?_ ?_ ?_
      · rw [map_mul, hm1, one_mul, sb, FGL.cc_subst _ (hc hθ0), hc''1]
      · rw [constantCoeff_map, hcε1, map_one]
      · rw [mul_pow, ← sb_pow'' hθ0, hc'', hε, ← map_pow, hcε]
    rw [sb_mul'' hθ0, sb_X hθ0, map_mul, map_X, ← hu, ← mul_assoc, ← hm]
  -- the inverse of `ζ₀`
  obtain ⟨ζi, hζi0, hζζi, -⟩ := exists_inv ζ₀ hζ0 (by
    rw [coeff_one_X_mul, hcε1]; exact isUnit_one)
  set g₀ : MvPowerSeries Unit 𝒪 := sb ζi (pd () ζ₀ * FGL.Ψ G (FGL.T : MvPowerSeries Unit 𝒪))
  -- `Ω' · Ψ_{E''} = g(Ω)`
  have hrel : pd () Ω * FGL.Ψ (formalGroup (shortO A B)) (FGL.T : MvPowerSeries Unit K) =
      sb Ω (MvPowerSeries.map ι g₀) := by
    apply inj
    have hinv := FGL.hom_invariant (G.map ι) (formalGroup (shortO A B)) θ' hθ0 hθ.2
    rw [hlie, map_one, mul_one] at hinv
    have hpd : pd () (sb θ' Ω) = sb θ' (pd () Ω) * pd () θ' := by
      rw [sb, pd_subst (hc hθ0), Fintype.sum_unique]
    have L1 : sb θ' (pd () Ω * FGL.Ψ (formalGroup (shortO A B)) (FGL.T : MvPowerSeries Unit K)) =
        sb θ' (pd () Ω) * FGL.Ψ (formalGroup (shortO A B)) θ' := by
      rw [sb_mul'' hθ0]; congr 1; exact subst_Ψ' _ hθ0
    have L2 : sb θ' (pd () Ω) * FGL.Ψ (formalGroup (shortO A B)) θ' =
        pd () (sb θ' Ω) * FGL.Ψ (G.map ι) (FGL.T : MvPowerSeries Unit K) := by
      rw [← hinv, hpd]; ring
    have L3 : pd () (sb θ' Ω) * FGL.Ψ (G.map ι) (FGL.T : MvPowerSeries Unit K) =
        MvPowerSeries.map ι (pd () ζ₀ * FGL.Ψ G (FGL.T : MvPowerSeries Unit 𝒪)) := by
      rw [hζ, Psi_map, ← pd_map', ← map_mul]
    have R1 : sb θ' (sb Ω (MvPowerSeries.map ι g₀)) =
        MvPowerSeries.map ι (pd () ζ₀ * FGL.Ψ G (FGL.T : MvPowerSeries Unit 𝒪)) := by
      rw [sb_sb hθ0 hΩ0, hζ, ← map_sb ι hζ0, sb_sb hζ0 hζi0, hζζi, X_sb]
    exact L1.trans (L2.trans (L3.trans R1.symm))
  obtain ⟨hg4, hg6⟩ := coeffs_g A B h3K (c := c'') hc'' hc''1 (MvPowerSeries.map ι g₀) hrel
  rw [show PowerSeries.coeff 4 (MvPowerSeries.map ι g₀ : PowerSeries K) =
    ((PowerSeries.coeff 4 (g₀ : PowerSeries 𝒪) : 𝒪) : K) from rfl] at hg4
  rw [show PowerSeries.coeff 6 (MvPowerSeries.map ι g₀ : PowerSeries K) =
    ((PowerSeries.coeff 6 (g₀ : PowerSeries 𝒪) : 𝒪) : K) from rfl] at hg6
  have hA : ‖A‖ ≤ 1 := by
    have e : A = -3 * ((PowerSeries.coeff 4 (g₀ : PowerSeries 𝒪) : 𝒪) : K) := by
      rw [hg4]; field_simp
    rw [e, norm_mul, norm_neg, h3, one_mul]
    exact (PowerSeries.coeff 4 (g₀ : PowerSeries 𝒪)).2
  have hB : ‖B‖ ≤ 1 := by
    have h2K : (2 : K) ≠ 0 := by intro e; rw [e, norm_zero] at h2; exact zero_ne_one h2
    have e : B = -(3 / 2) * ((PowerSeries.coeff 6 (g₀ : PowerSeries 𝒪) : 𝒪) : K) := by
      rw [hg6]; field_simp
    rw [e, norm_mul, norm_neg, norm_div, h3, h2, div_one, one_mul]
    exact (PowerSeries.coeff 6 (g₀ : PowerSeries 𝒪)).2
  -- the integral model and `Ω` over `𝒪`
  set W₀ : WeierstrassCurve 𝒪 := shortO ⟨A, hA⟩ ⟨B, hB⟩
  have hW₀ : W₀.map ι = shortO A B := by ext <;> simp [W₀, shortO]
  have hvmap : MvPowerSeries.map ι (v W₀ : MvPowerSeries Unit 𝒪) = v'' := by
    show PowerSeries.map ι (v W₀) = v (shortO A B)
    rw [map_v_gen, hW₀]
  obtain ⟨c₀, hc₀, hc₀1⟩ := exists_cube_root h3O (v W₀ : MvPowerSeries Unit 𝒪) (cc_v _)
  have hcc : MvPowerSeries.map ι c₀ = c'' := by
    refine cube_root_unique h3K ?_ hc''1 ?_
    · rw [constantCoeff_map, hc₀1, map_one]
    · rw [← map_pow, hc₀, hvmap, hc'']
  set Ω₀ : MvPowerSeries Unit 𝒪 := X () * c₀
  have hΩ₀0 : constantCoeff Ω₀ = 0 := by simp [Ω₀]
  have hΩmap : MvPowerSeries.map ι Ω₀ = Ω := by simp only [Ω₀, Ω, map_mul, map_X, hcc]
  obtain ⟨Ωi, hΩi0, hΩΩi, -⟩ := exists_inv Ω₀ hΩ₀0 (by
    rw [coeff_one_X_mul, hc₀1]; exact isUnit_one)
  refine ⟨sb ζ₀ Ωi, ?_⟩
  rw [map_sb ι hζ0, ← hζ, ← sb_sb hθ0 hΩ0, ← hΩmap, ← map_sb ι hΩ₀0, hΩΩi, map_X, sb_X hθ0]

end VeluDescent
