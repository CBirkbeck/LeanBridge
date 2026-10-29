import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.EnhancedGroup
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# Elliptic points of the Shimura curve `X_H`

Let `(O, μ)` be a polarized order in an indefinite division quaternion algebra `B` over `ℚ`, with a
fixed embedding `ι : B → M₂(ℝ)`, through which `B^×` acts on `ℋ^± = ℂ ∖ ℝ` by Möbius
transformations, and let `H` be an open subgroup of level `N` of the enhanced group
`Aut_{±μ}(O) ⋉ Ô^×`. The complex points of the Shimura curve `X_H` are
`H \ X(O;N)^big(ℂ) = B^× \ (ℋ^± × B̂^×) / K_H`, where `H` acts on `B̂^×` by right multiplication
through `f(w, x) = w x` (the `f` of LMFDB `shimcurve.is_coarse`, on `Ô^×`) and `K_H ⊆ B̂^×` is the
inverse image of `f(H)`, which contains `Γ(Ô, N)` and `ℚ^×`. The geometric component through the
points `[τ, 1]`, `τ` in the upper half-plane `ℍ`, is `Γ_H^+ \ ℍ`, for `Γ_H^+` the elements of
positive reduced norm of `B^× ∩ K_H`. Since `B^× ∩ Ô^× = O^×`, the group `(B^× ∩ K_H) / ℚ^×` is the
image `Γ_H` under `f : Aut_{±μ}(O) ⋉ O^× → N_{B^×}(O) / ℚ^×` of the inverse image of `H` in
`Aut_{±μ}(O) ⋉ O^×`.

An elliptic point is a point with nontrivial stabilizer. On this component it is the orbit of a
point `τ` of `ℍ` fixed by an element of `Γ_H^+` that is not a scalar: the scalars `ℚ^×` act
trivially (`Subalgebra.smul_eq_self_of_mem_normalizerRatUnits`), and for a quaternion algebra `B`
they are the only elements doing so (not proved). This is the analogue for Shimura curves of the
elliptic points `Matrix.GeneralLinearGroup.ellipticPoints` of a modular curve, through
`Γ_H = H ∩ SL₂(ℤ)`. The other geometric components, `Γ_b^+ \ ℍ` for `Γ_b^+` the elements of
positive norm of `B^× ∩ b K_H b⁻¹` and the other double cosets `B^× b K_H`, are not covered, nor is
the fact that the stabilizers are finite of order `2`, `3`, `4` or `6`.

As in `LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.EnhancedGroup`, `B` is any `ℚ`-algebra, `O`
any subring, `μ` any element, `H` any subgroup of the enhanced group and `ι` any `ℚ`-algebra map.

## Main definitions

* `Subalgebra.unitsToCompletedUnits`: the diagonal embedding `O^× → Ô^×`.
* `Subalgebra.enhancedGroupOfUnits`: the embedding of `Aut_{±μ}(O) ⋉ O^×` into the enhanced group.
* `Subalgebra.shimuraGamma`: the group `Γ_H ⊆ N_{B^×}(O) / ℚ^×`.
* `Subalgebra.shimuraGammaPlus`: the group of elements of `N_{B^×}(O)` of positive norm whose class
  lies in `Γ_H`, acting on `ℍ` through `ι`.
* `Subalgebra.shimuraEllipticPoints` (LMFDB `shimcurve.elliptic_points`): the elliptic points of
  `X_H` on the geometric component `Γ_H^+ \ ℍ`.

## Main results

* `Subalgebra.smul_eq_self_of_mem_normalizerRatUnits`: the scalars act trivially on `ℍ`.
* `Subalgebra.quotientMk_mem_shimuraEllipticPoints_iff`: the orbit of `τ` is an elliptic point
  exactly when some element of `Γ_H^+` other than a scalar fixes `τ`.
-/

open Matrix MulAction UpperHalfPlane

namespace Subalgebra

variable {B : Type*} [Ring B] (O : Subalgebra ℤ B)

open Ideal renaming Quotient.mk → quotientMk in
/-- The diagonal embedding `O^× → Ô^× = lim_N (O/NO)^×` of the units of a subring `O`, sending a
unit to the family of its reductions modulo the positive integers `N`. -/
noncomputable def unitsToCompletedUnits : Oˣ →* O.completedUnits :=
  (MonoidHom.pi fun _ ↦ Units.map (quotientMk _).toMonoidHom).codRestrict _
    fun _ _ _ _ ↦ Units.ext rfl

variable [Algebra ℚ B] (μ : B)

/-- The embedding `Aut_{±μ}(O) ⋉ O^× → Aut_{±μ}(O) ⋉ Ô^×` of the semidirect products, by the
diagonal embedding `O^× → Ô^×`, which commutes with the conjugation actions of `Aut_{±μ}(O)`. -/
noncomputable def enhancedGroupOfUnits :
    Oˣ ⋊[O.autPmMuUnitsAction μ] O.autPmMu μ →* O.EnhancedGroup μ :=
  SemidirectProduct.map O.unitsToCompletedUnits (MonoidHom.id _) fun _ ↦
    MonoidHom.ext fun _ ↦ Subtype.ext <| funext fun _ ↦ Units.ext rfl

variable (H : Subgroup (O.EnhancedGroup μ))

/-- The group `Γ_H ⊆ N_{B^×}(O) / ℚ^×` of a subgroup `H` of the enhanced group
`Aut_{±μ}(O) ⋉ Ô^×`: the image under `f : Aut_{±μ}(O) ⋉ O^× → N_{B^×}(O) / ℚ^×`, `(w, x) ↦ w x`,
of the inverse image of `H` in `Aut_{±μ}(O) ⋉ O^×`. It is `(B^× ∩ K_H) / ℚ^×` for the inverse image
`K_H ⊆ B̂^×` of `f(H)`, the group of the points `[τ, 1]` of the Shimura curve `X_H`. -/
noncomputable def shimuraGamma : Subgroup O.NormalizerModScalars :=
  (H.comap (O.enhancedGroupOfUnits μ)).map (O.autPmMuMul μ)

variable (ι : B →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)

/-- The homomorphism `N_{B^×}(O) → GL₂(ℝ)` given by a `ℚ`-algebra map `ι : B → M₂(ℝ)`, the fixed
embedding of an indefinite quaternion algebra `B`. -/
noncomputable def normalizerToGL : O.unitsNormalizer →* GL (Fin 2) ℝ :=
  (Units.map ι.toMonoidHom).comp O.unitsNormalizer.subtype

/-- The group `Γ_H^+` of the elements of `N_{B^×}(O)` of positive norm, for the embedding
`ι : B → M₂(ℝ)`, whose class in `N_{B^×}(O) / ℚ^×` lies in `Γ_H`. It acts on the upper half-plane
`ℍ` by Möbius transformations through `ι`, and the geometric component of the Shimura curve `X_H`
through the points `[τ, 1]` is `Γ_H^+ \ ℍ`. It contains the scalars `ℚ^×`, which act trivially. -/
noncomputable def shimuraGammaPlus : Subgroup O.unitsNormalizer :=
  (O.shimuraGamma μ H).comap (QuotientGroup.mk' _) ⊓ (GLPos (Fin 2) ℝ).comap (O.normalizerToGL ι)

noncomputable instance : MulAction (O.shimuraGammaPlus μ H ι) ℍ :=
  compHom ℍ ((O.normalizerToGL ι).comp (O.shimuraGammaPlus μ H ι).subtype)

/-- The **elliptic points** (LMFDB `shimcurve.elliptic_points`) of the Shimura curve `X_H` of a
subgroup `H` of the enhanced group `Aut_{±μ}(O) ⋉ Ô^×`, on its geometric component `Γ_H^+ \ ℍ`
through the points `[τ, 1]`, for the embedding `ι : B → M₂(ℝ)`: the points with nontrivial
stabilizer, that is the orbits of the points `τ` of `ℍ` fixed by an element of `Γ_H^+` which is not
a scalar, the scalars acting trivially. -/
noncomputable def shimuraEllipticPoints : Set (orbitRel.Quotient (O.shimuraGammaPlus μ H ι) ℍ) :=
  Quotient.mk _ '' {τ | ∃ γ : O.shimuraGammaPlus μ H ι, γ • τ = τ ∧
    (γ : O.unitsNormalizer) ∉ O.normalizerRatUnits}

variable {O μ H ι} (τ : ℍ)

/-- **The scalars act trivially on the upper half-plane**: an element of `Γ_H^+` in `ℚ^×` is sent
by `ι` to a scalar matrix. -/
lemma smul_eq_self_of_mem_normalizerRatUnits {γ : O.shimuraGammaPlus μ H ι}
    (hγ : (γ : O.unitsNormalizer) ∈ O.normalizerRatUnits) : γ • τ = τ := by
  rcases Subgroup.mem_subgroupOf.mp hγ with ⟨q, hq⟩
  have h :
      O.normalizerToGL ι γ = GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap ℚ ℝ) q) := by
    ext i j
    simp [normalizerToGL, ← hq]
    rfl
  rw [compHom_smul_def]
  exact h ▸ glScalar_smul _ τ

/-- **Being an elliptic point is a property of the orbit**: the orbit of `τ` is an elliptic point of
`X_H` exactly when some element of `Γ_H^+` other than a scalar fixes `τ`, the stabilizers of the
points of an orbit being conjugate. -/
lemma quotientMk_mem_shimuraEllipticPoints_iff :
    (Quotient.mk _ τ : orbitRel.Quotient (O.shimuraGammaPlus μ H ι) ℍ) ∈
    O.shimuraEllipticPoints μ H ι ↔ ∃ γ : O.shimuraGammaPlus μ H ι, γ • τ = τ ∧
    (γ : O.unitsNormalizer) ∉ O.normalizerRatUnits := by
  refine ⟨?_, fun h ↦ ⟨τ, h, rfl⟩⟩
  rintro ⟨τ', ⟨γ, hγ, hγN⟩, h⟩
  rcases Quotient.exact h with ⟨δ, hδ⟩
  have hδ' : δ • τ = τ' := hδ
  refine ⟨δ⁻¹ * γ * δ, ?_, fun hN ↦ hγN ?_⟩
  · rw [mul_smul, mul_smul, hδ', hγ, ← hδ', inv_smul_smul]
  · simpa [mul_assoc] using (inferInstance : O.normalizerRatUnits.Normal).conj_mem _ hN δ

end Subalgebra
