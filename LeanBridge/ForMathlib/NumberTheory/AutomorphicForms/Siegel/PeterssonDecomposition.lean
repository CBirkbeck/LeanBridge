import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularNewform

/-!
# The decomposition of paramodular cusp forms into old and new forms

On a finite-dimensional space `S` of functions `ℋ_g → V` on which the Petersson product of a
subgroup `Γ` is definite, every subspace `W ⊆ S` is complemented by its Petersson orthogonal
complement `W^⊥` in `S`: `W ∩ W^⊥ = 0` since a form orthogonal to itself vanishes, and
`dim W^⊥ ≥ dim S - dim W` since `W^⊥` is the kernel of `f ↦ (⟨f, w_i⟩)_i` for a basis `(w_i)` of
`W`. This is the linear algebra behind the decomposition
`S_ρ(K(N)) = S_ρ^old(K(N)) ⊕ S_ρ^new(K(N))` of the paramodular cusp forms into old and new forms
(LMFDB `mf.siegel.newspace`, `mf.siegel.newform`).

For the paramodular cusp forms `S_ρ(K(N))`, with a positive definite admissible Hermitian form `b`
on `V`, the hypotheses are theorems which are not proved here: `S_ρ(K(N))` is finite-dimensional,
the Petersson integral of two cusp forms converges absolutely, and `⟨F, F⟩ > 0` for a nonzero cusp
form `F`, its integrand `b(ρ(Im τ) F(τ), F(τ))` being nonnegative and continuous. They enter as
the hypotheses `FiniteDimensional ℂ (paramodularCuspForms ρ N)` and
`SiegelUpperHalfSpace.IsPeterssonDefinite`.

## Main definitions

* `SiegelUpperHalfSpace.IsPeterssonDefinite`: the Petersson integrals of a space of functions
  converge and its Petersson product is definite.

## Main results

* `SiegelUpperHalfSpace.disjoint_peterssonOrthogonal`: a subspace meets its Petersson orthogonal
  complement in `0`.
* `SiegelUpperHalfSpace.sup_peterssonOrthogonal`: a subspace and its Petersson orthogonal
  complement in a finite-dimensional space span it.
* `SiegelUpperHalfSpace.disjoint_paramodularOldSubspace_paramodularNewSubspace` (LMFDB
  `mf.siegel.newspace`, `mf.siegel.newform`): `S_ρ^old(K(N)) ∩ S_ρ^new(K(N)) = 0`.
* `SiegelUpperHalfSpace.paramodularOldSubspace_sup_paramodularNewSubspace` (LMFDB
  `mf.siegel.newspace`, `mf.siegel.newform`): `S_ρ^old(K(N)) + S_ρ^new(K(N)) = S_ρ(K(N))`.
-/

open MeasureTheory

open scoped ComplexConjugate

namespace SiegelUpperHalfSpace

section Orthogonal

variable {l : Type*} [Fintype l] [DecidableEq l] (Γ : Subgroup (Matrix.symplecticGroup l ℚ))
    {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL l ℂ) V)
    (b : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (S : Submodule ℂ (SiegelUpperHalfSpace l → V))

/-- The **Petersson product is definite** on a space `S` of functions `ℋ_g → V`, for a subgroup
`Γ` of `Sp(2g, ℚ)` and a sesquilinear form `b` on `V`: for all `f, g ∈ S` the Petersson integrand
`b(ρ(Im τ) f(τ), g(τ))` is integrable over the chosen fundamental domain of `Γ`
(`SiegelUpperHalfSpace.fundamentalDomain`), and the Petersson product `⟨f, f⟩` of `f ∈ S` with
itself vanishes only for `f = 0`. For the cusp forms `S = S_ρ(Γ)` on an arithmetic subgroup `Γ`
and a positive definite admissible Hermitian form `b`, this is a theorem (the integral converges
absolutely for cusp forms, and the integrand of `⟨f, f⟩` is nonnegative and continuous), which is
not proved here. -/
structure IsPeterssonDefinite : Prop where
  integrableOn (f g : SiegelUpperHalfSpace l → V) : f ∈ S → g ∈ S →
    IntegrableOn (peterssonIntegrand ρ b f g) (fundamentalDomain Γ) (invariantMeasure l)
  eq_zero (f : SiegelUpperHalfSpace l → V) : f ∈ S → peterssonProduct Γ ρ b f f = 0 → f = 0

variable {ρ b} (f g g' : SiegelUpperHalfSpace l → V)

lemma peterssonIntegrand_add_right : peterssonIntegrand ρ b f (g + g') =
    peterssonIntegrand ρ b f g + peterssonIntegrand ρ b f g' := by
  ext τ
  simp [peterssonIntegrand_apply]

lemma peterssonIntegrand_smul_right (c : ℂ) :
    peterssonIntegrand ρ b f (c • g) = conj c • peterssonIntegrand ρ b f g := by
  ext τ
  simp [peterssonIntegrand_apply]

variable {Γ S} {W : Submodule ℂ (SiegelUpperHalfSpace l → V)}

variable {f g} in
/-- The linear form `f ↦ ⟨f, g⟩` on `S`, for `g ∈ S`. -/
private noncomputable def peterssonLeft (h : IsPeterssonDefinite Γ ρ b S) (hg : g ∈ S) :
    S →ₗ[ℂ] ℂ where
  toFun f := peterssonProduct Γ ρ b f g
  map_add' f f' := by
    rw [Submodule.coe_add, peterssonProduct, peterssonIntegrand_add_left]
    simp only [Pi.add_apply]
    rw [integral_add (h.integrableOn f g f.2 hg) (h.integrableOn f' g f'.2 hg), ← peterssonProduct,
      ← peterssonProduct]
  map_smul' c f := by
    rw [Submodule.coe_smul, peterssonProduct, peterssonIntegrand_smul_left]
    simp only [Pi.smul_apply]
    rw [integral_smul, ← peterssonProduct, RingHom.id_apply]

variable {f} in
/-- The conjugate-linear form `g ↦ ⟨f, g⟩` on `W ⊆ S`, for `f ∈ S`. -/
private noncomputable def peterssonRight (h : IsPeterssonDefinite Γ ρ b S) (hW : W ≤ S)
    (hf : f ∈ S) : W →ₗ⋆[ℂ] ℂ where
  toFun g := peterssonProduct Γ ρ b f g
  map_add' g g' := by
    rw [Submodule.coe_add, peterssonProduct, peterssonIntegrand_add_right]
    simp only [Pi.add_apply]
    rw [integral_add (h.integrableOn f g hf (hW g.2)) (h.integrableOn f g' hf (hW g'.2)),
      ← peterssonProduct, ← peterssonProduct]
  map_smul' c g := by
    rw [Submodule.coe_smul, peterssonProduct, peterssonIntegrand_smul_right]
    simp only [Pi.smul_apply]
    rw [integral_smul, ← peterssonProduct]

/-- **A subspace meets its Petersson orthogonal complement in `0`** when the Petersson product is
definite: a form orthogonal to itself vanishes. -/
lemma disjoint_peterssonOrthogonal (h : IsPeterssonDefinite Γ ρ b S) (hW : W ≤ S) :
    Disjoint W (peterssonOrthogonal Γ ρ b S W) :=
  Submodule.disjoint_def.mpr fun f hfW hf ↦ h.eq_zero f (hW hfW) (hf.2 f hfW).2

/-- **A subspace and its Petersson orthogonal complement span the space**: for `W ⊆ S` with `S`
finite-dimensional and a definite Petersson product on `S`, `W + W^⊥ = S`, the orthogonal
complement `W^⊥` being the kernel of `f ↦ (⟨f, w_i⟩)_i` for a basis `(w_i)` of `W`. -/
lemma sup_peterssonOrthogonal [FiniteDimensional ℂ S] (h : IsPeterssonDefinite Γ ρ b S)
    (hW : W ≤ S) : W ⊔ peterssonOrthogonal Γ ρ b S W = S := by
  have hP : peterssonOrthogonal Γ ρ b S W ≤ S :=
    fun _ hf ↦ hf.1
  have : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hW
  have : FiniteDimensional ℂ (peterssonOrthogonal Γ ρ b S W) := Submodule.finiteDimensional_of_le hP
  let w : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W := Module.finBasis ℂ W
  let φ : S →ₗ[ℂ] Fin (Module.finrank ℂ W) → ℂ :=
    LinearMap.pi fun i ↦ peterssonLeft h (hW (w i).2)
  have hker : (LinearMap.ker φ).map S.subtype ≤ peterssonOrthogonal Γ ρ b S W := by
    rintro _ ⟨f, hf, rfl⟩
    have h0 : peterssonRight h hW f.2 = 0 :=
      w.ext fun i ↦ congrFun hf i
    exact ⟨f.2, fun g hg ↦ ⟨h.integrableOn f g f.2 (hW hg),
      LinearMap.congr_fun h0 ⟨g, hg⟩⟩⟩
  have hrange : Module.finrank ℂ (LinearMap.range φ) ≤ Module.finrank ℂ W :=
    (Submodule.finrank_le _).trans (Module.finrank_fin_fun ℂ).le
  have hdim : Module.finrank ℂ ↥(W ⊔ peterssonOrthogonal Γ ρ b S W) =
      Module.finrank ℂ W + Module.finrank ℂ (peterssonOrthogonal Γ ρ b S W) := by
    rw [← Submodule.finrank_sup_add_finrank_inf_eq, (disjoint_peterssonOrthogonal h hW).eq_bot,
      finrank_bot, add_zero]
  refine Submodule.eq_of_le_of_finrank_le (sup_le hW hP) ?_
  rw [hdim, ← φ.finrank_range_add_finrank_ker, ← Submodule.finrank_map_subtype_eq]
  exact add_le_add hrange (Submodule.finrank_mono hker)

end Orthogonal

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin 2) ℂ) V} {N : ℕ+}
    {b : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

/-- **No nonzero paramodular cusp form is both old and new** (LMFDB `mf.siegel.newspace`,
`mf.siegel.newform`): `S_ρ^old(K(N)) ∩ S_ρ^new(K(N)) = 0`, when the Petersson product of
`S_ρ(K(N))` is definite (`SiegelUpperHalfSpace.IsPeterssonDefinite`, a theorem for a positive
definite admissible `b` which is not proved here). -/
lemma disjoint_paramodularOldSubspace_paramodularNewSubspace
    (h : IsPeterssonDefinite (paramodularLevel N) ρ b (paramodularCuspForms ρ N)) :
    Disjoint (paramodularOldSubspace ρ N) (paramodularNewSubspace ρ N b) :=
  disjoint_peterssonOrthogonal h (paramodularOldSubspace_le ρ N)

/-- **The paramodular cusp forms are the sum of the old and new forms** (LMFDB
`mf.siegel.newspace`, `mf.siegel.newform`): `S_ρ(K(N)) = S_ρ^old(K(N)) + S_ρ^new(K(N))`, the sum
being direct (`disjoint_paramodularOldSubspace_paramodularNewSubspace`), when `S_ρ(K(N))` is
finite-dimensional and its Petersson product is definite
(`SiegelUpperHalfSpace.IsPeterssonDefinite`), theorems for a positive definite admissible `b` which
are not proved here. -/
lemma paramodularOldSubspace_sup_paramodularNewSubspace
    [FiniteDimensional ℂ (paramodularCuspForms ρ N)]
    (h : IsPeterssonDefinite (paramodularLevel N) ρ b (paramodularCuspForms ρ N)) :
    paramodularOldSubspace ρ N ⊔ paramodularNewSubspace ρ N b = paramodularCuspForms ρ N :=
  sup_peterssonOrthogonal h (paramodularOldSubspace_le ρ N)

end SiegelUpperHalfSpace
