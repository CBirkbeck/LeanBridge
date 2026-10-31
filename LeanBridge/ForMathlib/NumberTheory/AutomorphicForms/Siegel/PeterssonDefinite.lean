import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.PeterssonDecomposition

/-!
# The Petersson product is definite

The Petersson product `⟨f, g⟩ = ∫_𝔉 b(ρ(Im τ) f(τ), g(τ)) det(Im τ)^{-g-1} dX dY` of Siegel modular
forms of weight `ρ` on `Γ` is definite as soon as the integrals converge, `Γ` has a fundamental
domain `𝔉` and `b(ρ(Y) v, v) > 0` for `v ≠ 0` and `Y = Im τ`: if `⟨f, f⟩ = 0`, the nonnegative
integrand vanishes almost everywhere on `𝔉`, hence on `ℋ_g` by its invariance under `Γ`, so `f`
vanishes almost everywhere, and everywhere, being holomorphic. In scalar weight `k` with
`b(v, w) = v w̄`, `b(ρ(Y) v, v) = det(Y)^k |v|²`. So the decomposition
`S_k(K(N)) = S_k^old(K(N)) ⊕ S_k^new(K(N))` of the paramodular cusp forms of scalar weight (LMFDB
`mf.siegel.newspace`, `mf.siegel.newform`) holds as soon as `S_k(K(N))` is finite-dimensional,
`K(N)` has a fundamental domain and the Petersson integrals of cusp forms converge, three theorems
which are not proved here.

## Main results

* `SiegelUpperHalfSpace.IsHolomorphic.eq_zero_of_ae_eq_zero`: a holomorphic function on `ℋ_g`
  vanishing almost everywhere for the invariant measure vanishes.
* `SiegelUpperHalfSpace.IsPeterssonDefinite.of_integrableOn`: the Petersson product is definite on
  modular forms whose Petersson integrals converge.
* `SiegelUpperHalfSpace.flip_innerₛₗ_detPowerRep_pos`: the Petersson form is positive in scalar
  weight.
* `SiegelUpperHalfSpace.isPeterssonDefinite_paramodularCuspForms_detPowerRep`: the Petersson
  product of paramodular cusp forms of scalar weight is definite.
* `SiegelUpperHalfSpace.disjoint_paramodularOldSubspace_paramodularNewSubspace_detPowerRep`,
  `SiegelUpperHalfSpace.paramodularOldSubspace_sup_paramodularNewSubspace_detPowerRep` (LMFDB
  `mf.siegel.newspace`, `mf.siegel.newform`): `S_k(K(N)) = S_k^old(K(N)) ⊕ S_k^new(K(N))`.
-/

open Matrix Complex MeasureTheory Set

open scoped ComplexConjugate ComplexOrder ENNReal Pointwise

namespace SiegelUpperHalfSpace

variable {l : Type*}

private lemma symmetrize_ofSymCoords (x : Sym2 l → ℂ) :
    symmetrize (ofSymCoords x) = ofSymCoords x := by
  ext i j
  have e : (2⁻¹ : ℂ) * (x s(i, j) + x s(j, i)) = x s(i, j) := by
    rw [Sym2.eq_swap]
    ring1
  exact e

private lemma posDef_symmetrize_ofSymCoords {x : Sym2 l → ℂ} (hx : x ∈ coordSet l) :
    ((symmetrize (ofSymCoords x)).map im).PosDef := by
  rw [symmetrize_ofSymCoords]
  exact hx

private lemma extend_ofSymCoords (u : SiegelUpperHalfSpace l → ℂ) {x : Sym2 l → ℂ}
    (hx : x ∈ coordSet l) : extend u (ofSymCoords x) = u (ofCoords x hx) := by
  unfold extend
  rw [dite_eq_left (posDef_symmetrize_ofSymCoords hx)]
  exact congrArg u <| SiegelUpperHalfSpace.ext <| symmetrize_ofSymCoords x

variable [Fintype l] [DecidableEq l] {V : Type*} [AddCommGroup V] [Module ℂ V]
    {f : SiegelUpperHalfSpace l → V}

private lemma coordDensity_ne_zero {x : Sym2 l → ℂ} (hx : x ∈ coordSet l) :
    coordDensity l x ≠ 0 := by
  rw [coordDensity, Ne, ENNReal.ofReal_eq_zero, not_le]
  exact inv_pos.mpr <| pow_pos (PosDef.det_pos hx) _

private lemma measurable_coordDensity : Measurable (coordDensity l) := by
  unfold coordDensity
  fun_prop

/-- **A holomorphic function on `ℋ_g` vanishing almost everywhere vanishes**, for the invariant
measure: in the coordinates `τ_ij`, `i ≤ j`, the set where a coordinate `φ ∘ f` does not vanish is
open, and null for the Lebesgue measure, the density `det(Y)^{-g-1}` being positive. -/
lemma IsHolomorphic.eq_zero_of_ae_eq_zero (hf : IsHolomorphic f)
    (h : ∀ᵐ τ ∂invariantMeasure l, f τ = 0) : f = 0 := by
  funext τ
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (f τ)).mp fun φ ↦ ?_
  have hcont : ContinuousOn (fun x ↦ extend (φ ∘ f) (ofSymCoords x)) (coordSet l) :=
    (hf φ).continuousOn.comp (continuous_pi fun i ↦ continuous_pi fun j ↦
      continuous_apply s(i, j)).continuousOn fun _ hx ↦ posDef_symmetrize_ofSymCoords hx
  have hU : IsOpen (coordSet l ∩ (fun x ↦ extend (φ ∘ f) (ofSymCoords x)) ⁻¹' {0}ᶜ) :=
    hcont.isOpen_inter_preimage isOpen_coordSet isOpen_compl_singleton
  have hτ (τ' : SiegelUpperHalfSpace l) : ofCoords τ'.toCoords (toCoords_mem_coordSet τ') = τ' :=
    SiegelUpperHalfSpace.ext <| ofSymCoords_toCoords τ'
  have himage : toCoords '' {τ' | φ (f τ') ≠ 0} =
      coordSet l ∩ (fun x ↦ extend (φ ∘ f) (ofSymCoords x)) ⁻¹' {0}ᶜ := by
    ext x
    refine ⟨?_, fun hx ↦ ⟨ofCoords x hx.1, ?_, toCoords_ofCoords x hx.1⟩⟩
    · rintro ⟨τ', hτ', rfl⟩
      refine ⟨toCoords_mem_coordSet τ', ?_⟩
      rwa [mem_preimage, mem_compl_singleton_iff, extend_ofSymCoords _ (toCoords_mem_coordSet τ'),
        Function.comp_apply, hτ]
    · have hx' : extend (φ ∘ f) (ofSymCoords x) ≠ 0 := hx.2
      rwa [extend_ofSymCoords _ hx.1] at hx'
  have hsub : {τ' | φ (f τ') ≠ 0} ⊆ {τ' | ¬f τ' = 0} := fun τ' hτ' hfτ' ↦ hτ' <| by
    rw [hfτ', map_zero]
  have hnull : invariantMeasure l {τ' | φ (f τ') ≠ 0} = 0 :=
    measure_mono_null hsub (ae_iff.mp h)
  rw [invariantMeasure_apply, himage,
    setLIntegral_eq_zero_iff hU.measurableSet measurable_coordDensity] at hnull
  have hvol : volume (coordSet l ∩ (fun x ↦ extend (φ ∘ f) (ofSymCoords x)) ⁻¹' {0}ᶜ) = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr <| hnull.mono fun x hx hxU ↦
      coordDensity_ne_zero hxU.1 (hx hxU)
  by_contra hne
  have hmem : τ.toCoords ∈ coordSet l ∩ (fun x ↦ extend (φ ∘ f) (ofSymCoords x)) ⁻¹' {0}ᶜ :=
    himage ▸ ⟨τ, hne, rfl⟩
  rw [(hU.measure_eq_zero_iff volume).mp hvol] at hmem
  exact hmem

variable {Γ : Subgroup (symplecticGroup l ℚ)} {ρ : Representation ℂ (GL l ℂ) V}
    {b : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {S : Submodule ℂ (SiegelUpperHalfSpace l → V)}

private lemma apply_smul_eq_zero_iff (hf : f ∈ modularForms ρ Γ 1) {γ : symplecticGroup l ℚ}
    (hγ : γ ∈ Γ) (τ : SiegelUpperHalfSpace l) :
    f (SymplecticGroup.map (algebraMap ℚ ℝ) γ • τ) = 0 ↔ f τ = 0 := by
  rw [hf.2 ⟨γ, hγ⟩ τ, MonoidHom.one_apply, Units.val_one, one_smul]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  rw [← ρ.inv_self_apply (denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) γ) τ) (f τ), h,
    map_zero]

/-- **The Petersson product is definite on modular forms**: on a space `S` of Siegel modular forms
of weight `ρ` on `Γ` with trivial character whose Petersson integrals converge, `⟨f, f⟩ = 0` only
for `f = 0`, provided `Γ` has a fundamental domain and `b(ρ(Im τ) v, v) > 0` for `v ≠ 0`, as for a
positive definite admissible `b` (for scalar weight, `flip_innerₛₗ_detPowerRep_pos`). Indeed the
integrand `b(ρ(Im τ) f(τ), f(τ))` is then nonnegative, so it vanishes almost everywhere on the
fundamental domain, hence almost everywhere by its invariance under `Γ`, and so does `f`, which is
holomorphic, hence vanishes. The convergence of the integrals and the existence of a fundamental
domain are theorems for the cusp forms on an arithmetic `Γ`, which are not proved here. -/
lemma IsPeterssonDefinite.of_integrableOn (hpos : ∀ τ (v : V), v ≠ 0 → 0 < b (ρ (imGL τ) v) v)
    (hF : ∃ F, IsFundamentalDomain (transformationGroup Γ) F (invariantMeasure l))
    (hS : S ≤ modularForms ρ Γ 1)
    (hint : ∀ f g, f ∈ S → g ∈ S →
      IntegrableOn (peterssonIntegrand ρ b f g) (fundamentalDomain Γ) (invariantMeasure l)) :
    IsPeterssonDefinite Γ ρ b S where
  integrableOn := hint
  eq_zero f hf h0 := by
    have hFD :
        IsFundamentalDomain (transformationGroup Γ) (fundamentalDomain Γ) (invariantMeasure l) := by
      rw [fundamentalDomain, dite_eq_left hF]
      exact hF.choose_spec
    have hI (τ : SiegelUpperHalfSpace l) : 0 ≤ peterssonIntegrand ρ b f f τ := by
      by_cases hfτ : f τ = 0
      · simp [peterssonIntegrand_apply, hfτ]
      · exact (hpos τ (f τ) hfτ).le
    have hre :
        ∫ τ in fundamentalDomain Γ, (peterssonIntegrand ρ b f f τ).re ∂invariantMeasure l = 0 :=
      (integral_re (hint f f hf hf)).trans <| by
        rw [← peterssonProduct, h0, map_zero]
    rw [integral_eq_zero_iff_of_nonneg (fun τ ↦ (nonneg_iff.mp (hI τ)).1)
      (hint f f hf hf).re] at hre
    have hae : ∀ᵐ τ ∂(invariantMeasure l).restrict (fundamentalDomain Γ), f τ = 0 :=
      hre.mono fun τ hτ ↦ by
        by_contra hfτ
        exact (pos_iff.mp (hpos τ (f τ) hfτ)).1.ne' hτ
    have hzero : invariantMeasure l ({τ | f τ ≠ 0} ∩ fundamentalDomain Γ) = 0 := by
      rw [← Measure.restrict_apply₀' hFD.nullMeasurableSet]
      exact ae_iff.mp hae
    have hsub (g : transformationGroup Γ) : g • {τ | f τ ≠ 0} ⊆ {τ | f τ ≠ 0} := by
      rcases g with ⟨_, γ, hγ, rfl⟩
      rw [smul_set_subset_iff]
      intro τ hτ
      exact (apply_smul_eq_zero_iff (hS hf) hγ τ).not.mpr hτ
    exact (hS hf).1.eq_zero_of_ae_eq_zero <| ae_iff.mpr <| hFD.measure_zero_of_invariant _
      (fun g ↦ (hsub g).antisymm <| subset_smul_set_iff.mpr <| hsub g⁻¹) hzero

variable (k : ℤ) {n : ℕ}

/-- **The Petersson form is positive in scalar weight `k`**: for `ρ = det^k` and the form
`b(v, w) = v w̄`, Mathlib's `(innerₛₗ ℂ).flip`, `b(ρ(Im τ) v, v) = det(Im τ)^k |v|² > 0` for
`v ≠ 0`. -/
lemma flip_innerₛₗ_detPowerRep_pos (τ : SiegelUpperHalfSpace (Fin n)) {v : ℂ} (hv : v ≠ 0) :
    0 < (innerₛₗ ℂ).flip (TauCeti.detPowerRep ℂ n k (imGL τ) v) v := by
  have h : (innerₛₗ ℂ).flip (TauCeti.detPowerRep ℂ n k (imGL τ) v) v =
      ((τ.val.map im).det : ℂ) ^ k * v * conj v :=
    peterssonIntegrand_detPowerRep k τ (fun _ ↦ v) (fun _ ↦ v)
  rw [h, mul_assoc, mul_conj, ← ofReal_zpow, ← ofReal_mul, zero_lt_real]
  exact mul_pos (zpow_pos τ.posDef_im.det_pos k) (normSq_pos.mpr hv)

variable {k} {N : ℕ+}

/-- **The Petersson product of paramodular cusp forms of scalar weight is definite**: for
`b(v, w) = v w̄`, `⟨F, F⟩ = 0` only for `F = 0` in `S_k(K(N))`, provided `K(N)` has a fundamental
domain and the Petersson integrals of cusp forms converge, theorems which are not proved here. -/
lemma isPeterssonDefinite_paramodularCuspForms_detPowerRep
    (hF : ∃ F, IsFundamentalDomain (transformationGroup (paramodularLevel N)) F
      (invariantMeasure (Fin 2)))
    (hint : ∀ f g, f ∈ paramodularCuspForms (TauCeti.detPowerRep ℂ 2 k) N →
      g ∈ paramodularCuspForms (TauCeti.detPowerRep ℂ 2 k) N →
        IntegrableOn (peterssonIntegrand (TauCeti.detPowerRep ℂ 2 k) (innerₛₗ ℂ).flip f g)
          (fundamentalDomain (paramodularLevel N)) (invariantMeasure (Fin 2))) :
    IsPeterssonDefinite (paramodularLevel N) (TauCeti.detPowerRep ℂ 2 k) (innerₛₗ ℂ).flip
      (paramodularCuspForms (TauCeti.detPowerRep ℂ 2 k) N) :=
  IsPeterssonDefinite.of_integrableOn (fun τ _ hv ↦ flip_innerₛₗ_detPowerRep_pos k τ hv) hF
    (cuspForms_le_modularForms _ _ 1) hint

/-- **No nonzero paramodular cusp form of scalar weight is both old and new** (LMFDB
`mf.siegel.newspace`, `mf.siegel.newform`): `S_k^old(K(N)) ∩ S_k^new(K(N)) = 0` for the Petersson
inner product, provided `K(N)` has a fundamental domain and the Petersson integrals of cusp forms
converge, theorems which are not proved here. -/
lemma disjoint_paramodularOldSubspace_paramodularNewSubspace_detPowerRep
    (hF : ∃ F, IsFundamentalDomain (transformationGroup (paramodularLevel N)) F
      (invariantMeasure (Fin 2)))
    (hint : ∀ f g, f ∈ paramodularCuspForms (TauCeti.detPowerRep ℂ 2 k) N →
      g ∈ paramodularCuspForms (TauCeti.detPowerRep ℂ 2 k) N →
        IntegrableOn (peterssonIntegrand (TauCeti.detPowerRep ℂ 2 k) (innerₛₗ ℂ).flip f g)
          (fundamentalDomain (paramodularLevel N)) (invariantMeasure (Fin 2))) :
    Disjoint (paramodularOldSubspace (TauCeti.detPowerRep ℂ 2 k) N)
      (paramodularNewSubspace (TauCeti.detPowerRep ℂ 2 k) N (innerₛₗ ℂ).flip) :=
  disjoint_paramodularOldSubspace_paramodularNewSubspace <|
    isPeterssonDefinite_paramodularCuspForms_detPowerRep hF hint

/-- **The paramodular cusp forms of scalar weight are the direct sum of the old and new forms**
(LMFDB `mf.siegel.newspace`, `mf.siegel.newform`): `S_k(K(N)) = S_k^old(K(N)) ⊕ S_k^new(K(N))` for
the Petersson inner product, provided `S_k(K(N))` is finite-dimensional, `K(N)` has a fundamental
domain and the Petersson integrals of cusp forms converge, theorems which are not proved here. -/
lemma paramodularOldSubspace_sup_paramodularNewSubspace_detPowerRep
    [FiniteDimensional ℂ (paramodularCuspForms (TauCeti.detPowerRep ℂ 2 k) N)]
    (hF : ∃ F, IsFundamentalDomain (transformationGroup (paramodularLevel N)) F
      (invariantMeasure (Fin 2)))
    (hint : ∀ f g, f ∈ paramodularCuspForms (TauCeti.detPowerRep ℂ 2 k) N →
      g ∈ paramodularCuspForms (TauCeti.detPowerRep ℂ 2 k) N →
        IntegrableOn (peterssonIntegrand (TauCeti.detPowerRep ℂ 2 k) (innerₛₗ ℂ).flip f g)
          (fundamentalDomain (paramodularLevel N)) (invariantMeasure (Fin 2))) :
    paramodularOldSubspace (TauCeti.detPowerRep ℂ 2 k) N ⊔
      paramodularNewSubspace (TauCeti.detPowerRep ℂ 2 k) N (innerₛₗ ℂ).flip =
        paramodularCuspForms (TauCeti.detPowerRep ℂ 2 k) N :=
  paramodularOldSubspace_sup_paramodularNewSubspace <|
    isPeterssonDefinite_paramodularCuspForms_detPowerRep hF hint

end SiegelUpperHalfSpace
