import LeanBridge.ForMathlib.NumberTheory.LocalField.ExtensionRamificationPolygon
import LeanBridge.ForMathlib.NumberTheory.LocalField.ExtensionSubfamily
import LeanBridge.ForMathlib.NumberTheory.LocalField.ResidualPolynomialTransport
import Mathlib.Order.Setoid.Partition

/-!
# Residual polynomials across a family, and its subfamilies

Let `K` be a `p`-adic field, `I = (r_1, …, r_w)_ε^f` a Herbrand invariant at the residue
characteristic of `K`, `K_f` the unramified extension of `K` of degree `f` inside `K̄`, and `I / K`
the family of `I` (LMFDB `lf.family_polynomial`): the `K`-isomorphism classes of the extensions `E`
of `K` inside `K̄` with Herbrand invariant `I`. Each such `E` contains `K_f` and is totally ramified
over it, so its residual polynomials at a uniformiser `α` (LMFDB `lf.residual_polynomials`), those
of `E / E^un`, are polynomials over the residue field of `E`, which the inclusion `K_f ⊆ E`
identifies with the residue field of `K_f`. Read over the residue field of `K_f`, the equivalence
class of residual polynomials of `E` at `α` is the orbit of its pairs `(h_i, A_i)` under the residue
units, and it does not depend on `α`; all the members of `I / K` have the same `h_i`, the
ramification polygon being that of `I`.

A `K`-isomorphism `σ : E ≃ E'` of members of `I / K` restricts to an automorphism of `K_f`, which
acts on the residue field of `K_f` by a power of Frobenius `x ↦ x ^ (q ^ n)`, and every element of
`Gal(K_f / K)` arises so, from an automorphism of `K̄`. Through the transport of the residual
polynomials along `σ`, the class of `E'` at `σ α`, read over the residue field of `K_f`, is the
image of the class of `E` at `α` under that power of Frobenius. So for `f > 1` the members of one
element of `I / K` can have classes that differ by a power of Frobenius; for `f = 1` they agree.

LMFDB `lf.subfamily` defines the subfamily of `I / K` corresponding to a class `𝒜` as the elements
of `I / K` whose list of residual polynomials is in `𝒜`. The definition
`IsNonarchimedeanLocalField.HerbrandInvariant.subfamily` reads this with some member and some
uniformiser, `IsNonarchimedeanLocalField.HerbrandInvariant.galoisSubfamily` reads it up to the
action of `Gal(K_f / K)` on the coefficients. The two readings give the same subfamily, for every
`𝒜` and every `f`; for a class `𝒜` of a member, membership is decided at any member and any
uniformiser, literally for `f = 1` and up to `Gal(K_f / K)` in general; and the subfamilies of the
classes of the members partition `I / K`.

## Main definitions

* `IsNonarchimedeanLocalField.restrictUnramifiedExtension`: the restriction to `K_f` of a
  `K`-isomorphism of extensions of `K` inside `K̄`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.residueFieldEquiv`: the residue map of
  `K_f ⊆ E`, an isomorphism for a member `E` of `I / K`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.residualPairsOver` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.residualClass` (LMFDB
  `lf.residual_polynomials`, `lf.subfamily`): the pairs `(h_i, A_i)` and the class of residual
  polynomials of a member of `I / K`, read over the residue field of `K_f`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.galoisSubfamily` (LMFDB `lf.subfamily`): the
  subfamily corresponding to `𝒜` up to the action of `Gal(K_f / K)`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.subfamilies` (LMFDB `lf.subfamily`): the
  subfamilies of the classes of the members of `I / K`.

## Main results

* `IsNonarchimedeanLocalField.exists_restrictUnramifiedExtension_eq`: every element of
  `Gal(K_f / K)` is the restriction of a `K`-isomorphism from a member onto another.
* `IsNonarchimedeanLocalField.exists_residueFieldHom_eq_pow`: an element of `Gal(K_f / K)` acts on
  the residue field of `K_f` by a power of Frobenius.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.residualClass_eq_residualActOrbit`:
  the class of a member, read over `K_f`, is an orbit of the residue units.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.residualPairsOver_algEquiv` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.residualClass_algEquiv` (LMFDB
  `lf.residual_polynomials`, `lf.subfamily`): along a `K`-isomorphism the pairs and the class, read
  over `K_f`, change by the power of Frobenius induced on `K_f`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.mk_mem_subfamily_residualClass_iff` (LMFDB
  `lf.subfamily`): a member lies in the subfamily of a class exactly when its class is the image of
  that class under an element of `Gal(K_f / K)`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.subfamily_eq_galoisSubfamily` (LMFDB
  `lf.subfamily`): the two readings give the same subfamily.
* `IsNonarchimedeanLocalField.HerbrandInvariant.subfamily_image_map_residueFieldHom` (LMFDB
  `lf.subfamily`): a subfamily depends only on the orbit of its class under `Gal(K_f / K)`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.mk_mem_subfamily_residualClass_iff_of_f_eq_one` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.mk_mem_galoisSubfamily_residualClass_iff` (LMFDB
  `lf.subfamily`): the condition, literal for `f = 1` and up to `Gal(K_f / K)` in general, depends
  neither on the member nor on the uniformiser.
* `IsNonarchimedeanLocalField.HerbrandInvariant.isPartition_subfamilies` (LMFDB `lf.subfamily`,
  `lf.field.label`): the subfamilies partition `I / K`.

## References

* J. Guàrdia, J. W. Jones, K. Keating, S. Pauli, D. P. Roberts and D. Roe, *Families of p-adic
  fields*, arXiv:2507.02360, §1.2 and §4.1.
* S. Pauli and B. Sinclair, *Enumerating extensions of (π)-adic fields with given invariants*,
  Int. J. Number Theory 13 (2017); arXiv:1504.06671, Section 4.
-/

open Polynomial TauCeti ValuativeRel

open IntermediateField (inclusion)

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace IsNonarchimedeanLocalField

section Twist

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {E E' : IntermediateField K (AlgebraicClosure K)} (f : ℕ) (σ : E ≃ₐ[K] E')

/-- The **restriction to `K_f`** of a `K`-isomorphism `σ : E ≃ E'` of extensions of a
nonarchimedean local field `K` inside `K̄`: the restriction to the unramified extension `K_f` of `K`
of degree `f` inside `K̄`, which is normal, of an automorphism of `K̄` extending `σ`. When `K_f ⊆ E`
it is the restriction of `σ` to `K_f`. -/
noncomputable def restrictUnramifiedExtension :
    Gal(unramifiedExtension K (AlgebraicClosure K) f/K) :=
  (σ.toAlgHom.liftNormal (AlgebraicClosure K)).restrictNormal' _

lemma coe_restrictUnramifiedExtension_apply (h : unramifiedExtension K (AlgebraicClosure K) f ≤ E)
    (x : unramifiedExtension K (AlgebraicClosure K) f) :
    (restrictUnramifiedExtension f σ x : AlgebraicClosure K) = σ (inclusion h x) :=
  ((σ.toAlgHom.liftNormal (AlgebraicClosure K)).restrictNormal_commutes _ x).trans
    (σ.toAlgHom.liftNormal_commutes (AlgebraicClosure K) (inclusion h x))

lemma restrictUnramifiedExtension_equivMap (h : unramifiedExtension K (AlgebraicClosure K) f ≤ E)
    (g : Gal(AlgebraicClosure K/K)) : restrictUnramifiedExtension f
      (E.equivMap (g : AlgebraicClosure K →ₐ[K] AlgebraicClosure K)) =
      AlgEquiv.restrictNormalHom _ g :=
  AlgEquiv.ext fun x ↦ Subtype.ext <| (coe_restrictUnramifiedExtension_apply f _ h x).trans
    (AlgEquiv.restrictNormalHom_apply _ g x).symm

variable [FiniteDimensional K E] [FiniteDimensional K E']

/-- **Every automorphism of `K_f` is the restriction of a `K`-isomorphism of extensions**: for a
finite extension `E` of `K` inside `K̄` containing the unramified extension `K_f` of degree `f`,
every `K`-automorphism `g` of `K_f` is the restriction to `K_f` of a `K`-isomorphism from `E` onto
its image under an automorphism of `K̄` extending `g`. -/
lemma exists_restrictUnramifiedExtension_eq (h : unramifiedExtension K (AlgebraicClosure K) f ≤ E)
    (g : Gal(unramifiedExtension K (AlgebraicClosure K) f/K)) :
    ∃ (L : FiniteExtension K) (τ : E ≃ₐ[K] L.1), restrictUnramifiedExtension f τ = g := by
  rcases AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) g with ⟨g', rfl⟩
  exact ⟨⟨_, (E.equivMap (g' : AlgebraicClosure K →ₐ[K] AlgebraicClosure K)).toLinearEquiv
    |>.finiteDimensional⟩, _, restrictUnramifiedExtension_equivMap f h g'⟩

lemma residueFieldHom_comp_inclusion (h : unramifiedExtension K (AlgebraicClosure K) f ≤ E)
    (h' : unramifiedExtension K (AlgebraicClosure K) f ≤ E') : σ.toAlgHom.residueFieldHom.comp
      (inclusion h).residueFieldHom = (inclusion h').residueFieldHom.comp
        (restrictUnramifiedExtension f σ).toAlgHom.residueFieldHom := by
  rw [← AlgHom.residueFieldHom_comp, ← AlgHom.residueFieldHom_comp]
  congr 1
  exact AlgHom.ext fun x ↦ Subtype.ext (coe_restrictUnramifiedExtension_apply f σ h x).symm

end Twist

section Frobenius

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {f : ℕ} (g : Gal(unramifiedExtension K (AlgebraicClosure K) f/K))
  (S : Set (List 𝓀[unramifiedExtension K (AlgebraicClosure K) f][X]))

/-- **The automorphisms of the residue field of `K_f` are the powers of Frobenius**: every
`K`-automorphism `g` of the unramified extension `K_f` of degree `f` of a nonarchimedean local field
`K` inside `K̄` acts on the residue field of `K_f` by `x ↦ x ^ (q ^ n)` for some `n`, where `q` is
the cardinality of the residue field of `K`. -/
lemma exists_residueFieldHom_eq_pow :
    ∃ n : ℕ, ∀ x, g.toAlgHom.residueFieldHom x = x ^ Nat.card 𝓀[K] ^ n := by
  let _ : Fintype 𝓀[K] := Fintype.ofFinite _
  have hbij : Function.Bijective g.toAlgHom.residueFieldHom :=
    Finite.injective_iff_bijective.mp g.toAlgHom.residueFieldHom.injective
  rcases (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow 𝓀[K]
    𝓀[unramifiedExtension K (AlgebraicClosure K) f]).2 (AlgEquiv.ofBijective _ hbij) with ⟨n, hn⟩
  refine ⟨n, fun x ↦ ?_⟩
  rw [← AlgEquiv.ofBijective_apply _ hbij, ← hn, AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, Fintype.card_eq_nat_card]

lemma eq_one_of_f_eq_one (hf : f = 1) : g = 1 := by
  have hbot : unramifiedExtension K (AlgebraicClosure K) f = ⊥ :=
    IntermediateField.finrank_eq_one_iff.mp ((finrank_unramifiedExtension (by omega)).trans hf)
  refine AlgEquiv.ext fun x ↦ ?_
  have hx₀ : (x : AlgebraicClosure K) ∈ (⊥ : IntermediateField K (AlgebraicClosure K)) := by
    rw [← hbot]
    exact x.2
  rcases IntermediateField.mem_bot.mp hx₀ with ⟨c, hc⟩
  have hx : x = algebraMap K (unramifiedExtension K (AlgebraicClosure K) f) c :=
    Subtype.ext hc.symm
  rw [hx, AlgEquiv.commutes, AlgEquiv.one_apply]

variable (f) in
lemma image_map_residueFieldHom_image_map
    (g' : Gal(unramifiedExtension K (AlgebraicClosure K) f/K)) : List.map
      (map (g.toAlgHom.residueFieldHom : 𝓀[unramifiedExtension K (AlgebraicClosure K) f] →+*
        𝓀[unramifiedExtension K (AlgebraicClosure K) f])) '' (List.map (map
          (g'.toAlgHom.residueFieldHom : 𝓀[unramifiedExtension K (AlgebraicClosure K) f] →+*
            𝓀[unramifiedExtension K (AlgebraicClosure K) f])) '' S) = List.map (map
      ((g * g').toAlgHom.residueFieldHom : 𝓀[unramifiedExtension K (AlgebraicClosure K) f] →+*
        𝓀[unramifiedExtension K (AlgebraicClosure K) f])) '' S := by
  have h : (g * g').toAlgHom = g.toAlgHom.comp g'.toAlgHom :=
    rfl
  rw [Set.image_image]
  refine Set.image_congr fun A _ ↦ ?_
  rw [List.map_map]
  refine List.map_congr_left fun B _ ↦ ?_
  rw [Function.comp_apply, map_map, h, AlgHom.residueFieldHom_comp]
  rfl

variable (f) in
lemma image_map_residueFieldHom_one : List.map (map
    ((1 : Gal(unramifiedExtension K (AlgebraicClosure K) f/K)).toAlgHom.residueFieldHom :
      _ →+* _)) '' S = S := by
  have h : (1 : Gal(unramifiedExtension K (AlgebraicClosure K) f/K)).toAlgHom = AlgHom.id K
      (unramifiedExtension K (AlgebraicClosure K) f) :=
    rfl
  conv_rhs => rw [← Set.image_id S]
  refine Set.image_congr fun A _ ↦ ?_
  refine (List.map_congr_left fun B _ ↦ ?_).trans A.map_id'
  rw [h, AlgHom.residueFieldHom_id]
  exact map_id

end Frobenius

lemma map_snd_residualPairs {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (ρ : L[X]) (α : L) :
    (residualPairs ρ α).map Prod.snd = residualPolynomials ρ α := by
  rw [residualPairs, residualPolynomials, List.map_map]
  rfl

lemma preimage_map_map_eq_image {F F' : Type*} [Field F] [Field F'] (e : F ≃+* F')
    (S : Set (List F'[X])) :
    List.map (map (e : F →+* F')) ⁻¹' S = List.map (map (e.symm : F' →+* F)) '' S := by
  have h₁ : ((e.symm : F' →+* F).comp (e : F →+* F')) = RingHom.id F := e.symm_comp
  have h₂ : ((e : F →+* F').comp (e.symm : F' →+* F)) = RingHom.id F' := e.comp_symm
  refine Set.ext fun A ↦ ⟨fun hA ↦ ⟨A.map (map (e : F →+* F')), hA, ?_⟩, ?_⟩
  · rw [List.map_map]
    exact (List.map_congr_left fun B _ ↦ by
      rw [Function.comp_apply, map_map, h₁, map_id, id]).trans A.map_id
  · rintro ⟨B, hB, rfl⟩
    rw [Set.mem_preimage, List.map_map]
    refine ((List.map_congr_left fun C _ ↦ ?_).trans B.map_id).symm ▸ hB
    rw [Function.comp_apply, map_map, h₂, map_id, id]

lemma algebraMap_residueField_eq {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {E : IntermediateField K (AlgebraicClosure K)}
    [FiniteDimensional K E] {f : ℕ} (h : unramifiedExtension K (AlgebraicClosure K) f ≤ E) :
    letI : Algebra (unramifiedExtension K (AlgebraicClosure K) f) E := (inclusion h).toAlgebra
    haveI : ValuativeExtension (unramifiedExtension K (AlgebraicClosure K) f) E :=
      (inclusion h).valuativeExtension
    algebraMap 𝓀[unramifiedExtension K (AlgebraicClosure K) f] 𝓀[E] =
      ((inclusion h).residueFieldHom : _ →+* _) := by
  refine RingHom.ext fun x ↦ ?_
  rcases IsLocalRing.residue_surjective x with ⟨x, rfl⟩
  rfl

namespace HerbrandInvariant

section Member

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] {p : ℕ} {I : HerbrandInvariant p} {E E' : IntermediateField K (AlgebraicClosure K)}
  [FiniteDimensional K E] [FiniteDimensional K E'] (hE : I.IsInvariantOf K E)
  (hE' : I.IsInvariantOf K E') (σ : E ≃ₐ[K] E') (α : E)

lemma IsInvariantOf.surjective_residueFieldHom : Function.Surjective
    (inclusion (unramifiedExtension_le_of_isInvariantOf hE)).residueFieldHom := by
  let _ : Algebra (unramifiedExtension K (AlgebraicClosure K) I.f) E :=
    (inclusion (unramifiedExtension_le_of_isInvariantOf hE)).toAlgebra
  have hv : ValuativeExtension (unramifiedExtension K (AlgebraicClosure K) I.f) E :=
    (inclusion (unramifiedExtension_le_of_isInvariantOf hE)).valuativeExtension
  have hs : IsScalarTower K (unramifiedExtension K (AlgebraicClosure K) I.f) E :=
    .of_algebraMap_eq fun _ ↦ rfl
  have hur : IsUnramified K (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    isUnramified_unramifiedExtension I.f_pos.ne'
  have htr : IsTotallyRamified (unramifiedExtension K (AlgebraicClosure K) I.f) E :=
    (IsUnramified.isTotallyRamified_iff_finrank_eq K _ E).mpr
      ((finrank_unramifiedExtension I.f_pos.ne').trans hE.1.symm)
  have hsurj :
      Function.Surjective (algebraMap 𝓀[unramifiedExtension K (AlgebraicClosure K) I.f] 𝓀[E]) :=
    (isTotallyRamified_iff_surjective_algebraMap_residueField _ E).mp htr
  rwa [algebraMap_residueField_eq] at hsurj

/-- The **isomorphism of the residue field of `K_f` with that of an extension `E` in `I / K`**, for
the unramified extension `K_f` of `K` of degree `f` inside `K̄`, `I = (r_1, …, r_w)_ε^f`: the map
of residue fields induced by the inclusion `K_f ⊆ E`, which is bijective since `E` is totally
ramified over `K_f`. -/
noncomputable def IsInvariantOf.residueFieldEquiv :
    𝓀[unramifiedExtension K (AlgebraicClosure K) I.f] ≃+* 𝓀[E] :=
  RingEquiv.ofBijective (inclusion (unramifiedExtension_le_of_isInvariantOf hE)).residueFieldHom
    ⟨(inclusion _).residueFieldHom.injective, hE.surjective_residueFieldHom⟩

lemma IsInvariantOf.coe_residueFieldEquiv :
    (hE.residueFieldEquiv : 𝓀[unramifiedExtension K (AlgebraicClosure K) I.f] →+* 𝓀[E]) =
      (inclusion (unramifiedExtension_le_of_isInvariantOf hE)).residueFieldHom :=
  RingHom.ext fun _ ↦ rfl

/-- The **pairs `(h_i, A_i)` of an extension `E` in `I / K` at `α`, read over the residue field of
`K_f`**: the numerators `h_i` of the slopes of the segments `S_1, …, S_ℓ` of the ramification
polygon of `E / E^un` at `α` and the residual polynomials `A_i` (LMFDB `lf.residual_polynomials`),
their coefficients carried to the residue field of `K_f` by the inverse of
`IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.residueFieldEquiv`. -/
noncomputable def IsInvariantOf.residualPairsOver :
    List (ℤ × 𝓀[unramifiedExtension K (AlgebraicClosure K) I.f][X]) :=
  (residualPairs (ramificationPolynomial (minpoly (unramifiedExtension K E (inertiaDegree K E)) α)
    α) α).map (Prod.map id (map (hE.residueFieldEquiv.symm : _ →+* _)))

/-- The **equivalence class of residual polynomials of an extension `E` in `I / K` at `α`, read over
the residue field of `K_f`** (LMFDB `lf.residual_polynomials`, `lf.subfamily`): the lists of
polynomials over the residue field of `K_f` whose image under the residue map of `K_f ⊆ E` lies in
the class `𝒜` of the residual polynomials of `E / E^un` at `α`. -/
noncomputable def IsInvariantOf.residualClass :
    Set (List 𝓀[unramifiedExtension K (AlgebraicClosure K) I.f][X]) :=
  List.map (map (hE.residueFieldEquiv : _ →+* _)) ⁻¹' residualPolynomialClass
    (unramifiedExtension K E (inertiaDegree K E))
    (ramificationPolynomial (minpoly (unramifiedExtension K E (inertiaDegree K E)) α) α) α

/-- **The class of residual polynomials of an extension in `I / K`, read over `K_f`, is an orbit**:
it is the orbit of the pairs `(h_i, A_i)` of `E` at `α`, read over the residue field of `K_f`,
under the units of that field. -/
lemma IsInvariantOf.residualClass_eq_residualActOrbit :
    hE.residualClass α = residualActOrbit _ (hE.residualPairsOver α) := by
  rw [IsInvariantOf.residualClass, residualPolynomialClass_eq_residualActOrbit
    ((isTotallyRamified_iff_surjective_algebraMap_residueField _ E).mp
      (isTotallyRamified_unramifiedExtension_inertiaDegree K E)), preimage_map_map_eq_image,
    image_map_residualActOrbit _ _ hE.residueFieldEquiv.symm.surjective]
  rfl

lemma IsInvariantOf.residualPolynomials_eq : residualPolynomials
    (ramificationPolynomial (minpoly (unramifiedExtension K E (inertiaDegree K E)) α) α) α =
    ((hE.residualPairsOver α).map Prod.snd).map (map (hE.residueFieldEquiv : _ →+* _)) := by
  rw [← map_snd_residualPairs, IsInvariantOf.residualPairsOver, List.map_map, List.map_map]
  refine List.map_congr_left fun hA _ ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, Prod.map_snd, map_map, RingEquiv.comp_symm, map_id]

lemma IsInvariantOf.residualPolynomials_mem_image_iff
    (𝒜 : Set (List 𝓀[unramifiedExtension K (AlgebraicClosure K) I.f][X])) : residualPolynomials
      (ramificationPolynomial (minpoly (unramifiedExtension K E (inertiaDegree K E)) α) α) α ∈
      List.map (map ((inclusion (unramifiedExtension_le_of_isInvariantOf hE)).residueFieldHom :
        _ →+* _)) '' 𝒜 ↔ (hE.residualPairsOver α).map Prod.snd ∈ 𝒜 := by
  rw [← hE.coe_residueFieldEquiv, hE.residualPolynomials_eq α]
  exact (List.map_injective_iff.mpr (map_injective _ hE.residueFieldEquiv.injective)).mem_set_image

lemma IsInvariantOf.residueFieldEquiv_symm_comp :
    (hE'.residueFieldEquiv.symm : 𝓀[E'] →+* 𝓀[unramifiedExtension K (AlgebraicClosure K) I.f]).comp
      (σ.toAlgHom.residueFieldHom : 𝓀[E] →+* 𝓀[E']) =
      ((restrictUnramifiedExtension I.f σ).toAlgHom.residueFieldHom :
        𝓀[unramifiedExtension K (AlgebraicClosure K) I.f] →+*
          𝓀[unramifiedExtension K (AlgebraicClosure K) I.f]).comp (hE.residueFieldEquiv.symm :
            𝓀[E] →+* 𝓀[unramifiedExtension K (AlgebraicClosure K) I.f]) := by
  refine RingHom.ext fun y ↦ ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_coe, RingHom.coe_coe, RingHom.coe_coe,
    RingHom.coe_coe, RingEquiv.symm_apply_eq]
  exact (congrArg _ (hE.residueFieldEquiv.apply_symm_apply y).symm).trans
    (AlgHom.congr_fun (residueFieldHom_comp_inclusion I.f σ
      (unramifiedExtension_le_of_isInvariantOf hE) (unramifiedExtension_le_of_isInvariantOf hE'))
        (hE.residueFieldEquiv.symm y))

/-- **The pairs of residual polynomials of an extension in `I / K` along a `K`-isomorphism, read
over `K_f`** (LMFDB `lf.residual_polynomials`): for a `K`-isomorphism `σ : E ≃ E'` of extensions in
`I / K` inside `K̄`, the pairs `(h_i, A_i)` of `E'` at `σ α`, read over the residue field of `K_f`,
are those of `E` at `α` with the automorphism of the residue field of `K_f` induced by the
restriction of `σ` to `K_f` applied to the coefficients: a power of Frobenius
(`IsNonarchimedeanLocalField.exists_residueFieldHom_eq_pow`). -/
lemma IsInvariantOf.residualPairsOver_algEquiv : hE'.residualPairsOver (σ α) =
    (hE.residualPairsOver α).map (Prod.map id
      (map ((restrictUnramifiedExtension I.f σ).toAlgHom.residueFieldHom : _ →+* _))) := by
  rw [IsInvariantOf.residualPairsOver, IsInvariantOf.residualPairsOver,
    ramificationPolynomial_minpoly_algEquiv, residualPairs_map_algEquiv, List.map_map, List.map_map]
  refine List.map_congr_left fun hA _ ↦ Prod.ext rfl ?_
  dsimp only [Function.comp_apply]
  exact (map_map _ _ _).trans ((congrArg (fun φ ↦ map φ hA.2)
    (hE.residueFieldEquiv_symm_comp hE' σ)).trans (map_map _ _ _).symm)

/-- **The class of residual polynomials of an extension in `I / K` along a `K`-isomorphism, read
over `K_f`** (LMFDB `lf.residual_polynomials`, `lf.subfamily`): for a `K`-isomorphism `σ : E ≃ E'`
of extensions in `I / K` inside `K̄`, the class of `E'` at `σ α` is the image of the class of `E` at
`α` under the automorphism of the residue field of `K_f` induced by the restriction of `σ` to `K_f`,
a power of Frobenius, applied to the coefficients. -/
lemma IsInvariantOf.residualClass_algEquiv : hE'.residualClass (σ α) = List.map
    (map ((restrictUnramifiedExtension I.f σ).toAlgHom.residueFieldHom : _ →+* _)) ''
      hE.residualClass α := by
  rw [hE'.residualClass_eq_residualActOrbit, hE.residualClass_eq_residualActOrbit,
    hE.residualPairsOver_algEquiv hE' σ, image_map_residualActOrbit _
      ((restrictUnramifiedExtension I.f σ).toAlgHom.residueFieldHom :
        𝓀[unramifiedExtension K (AlgebraicClosure K) I.f] →+*
          𝓀[unramifiedExtension K (AlgebraicClosure K) I.f])
      (Finite.injective_iff_surjective.mp
        (restrictUnramifiedExtension I.f σ).toAlgHom.residueFieldHom.injective)]

end Member

section Subfamily

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] {p : ℕ} (I : HerbrandInvariant p)
  (𝒜 : Set (List 𝓀[unramifiedExtension K (AlgebraicClosure K) I.f][X]))

/-- The **subfamily of `I / K` corresponding to `𝒜` up to the action of `Gal(K_f / K)`** (LMFDB
`lf.subfamily`, read with "is in `𝒜` up to the action of `Gal(K_f / K)` on the coefficients"): the
`K`-isomorphism classes in `I / K` of the extensions `E` inside `K̄` with a uniformiser `α` and an
automorphism `g` of `K_f / K` such that the list of residual polynomials of `E / E^un` at `α` is the
image of a list of `𝒜` under the automorphism of the residue field of `K_f` induced by `g`, read in
`E` through `K_f ⊆ E`. It is the subfamily `IsNonarchimedeanLocalField.HerbrandInvariant.subfamily`
(`IsNonarchimedeanLocalField.HerbrandInvariant.subfamily_eq_galoisSubfamily`). -/
def galoisSubfamily : ExtensionFamily K :=
  Quotient.mk _ '' {E : FiniteExtension K | haveI : FiniteDimensional K E.1 := E.2
    ∃ hE : I.IsInvariantOf K E.1, ∃ α : 𝒪[E.1], Irreducible α ∧
      ∃ g : Gal(unramifiedExtension K (AlgebraicClosure K) I.f/K),
      letI : Algebra (unramifiedExtension K (AlgebraicClosure K) I.f) E.1 :=
        (inclusion (unramifiedExtension_le_of_isInvariantOf hE)).toAlgebra
      haveI : ValuativeExtension (unramifiedExtension K (AlgebraicClosure K) I.f) E.1 :=
        (inclusion (unramifiedExtension_le_of_isInvariantOf hE)).valuativeExtension
      residualPolynomials (ramificationPolynomial
        (minpoly (unramifiedExtension K E.1 (inertiaDegree K E.1)) (α : E.1)) (α : E.1)) (α : E.1) ∈
          List.map (map (algebraMap 𝓀[unramifiedExtension K (AlgebraicClosure K) I.f] 𝓀[E.1])) ''
            (List.map (map (g.toAlgHom.residueFieldHom : _ →+* _)) '' 𝒜)}

/-- The **subfamilies of `I / K`** (LMFDB `lf.subfamily`): the subfamilies corresponding to the
equivalence classes of residual polynomials of the extensions in `I / K`, read over the residue
field of `K_f`. -/
def subfamilies : Set (ExtensionFamily K) :=
  {S | ∃ E : FiniteExtension K, haveI : FiniteDimensional K E.1 := E.2
    ∃ (hE : I.IsInvariantOf K E.1) (α : 𝒪[E.1]), Irreducible α ∧
      I.subfamily K (hE.residualClass α) = S}

/-- **The two readings of "whose list of residual polynomials is in `𝒜`" give the same subfamily**
(LMFDB `lf.subfamily`): for every set `𝒜` of lists of polynomials over the residue field of `K_f`
and every residue degree `f`, the subfamily of `I / K` defined with some member of a
`K`-isomorphism class and some uniformiser is the subfamily defined up to the action of
`Gal(K_f / K)` on the coefficients. If the list of `E` at `α` lies in the image of `𝒜` under `g`,
then the list of the image of `E` under an automorphism of `K̄` restricting to `g⁻¹` on `K_f` lies
in `𝒜`. -/
lemma subfamily_eq_galoisSubfamily : I.subfamily K 𝒜 = I.galoisSubfamily K 𝒜 := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨E, ⟨hE, α, hα, hmem⟩, rfl⟩
    exact ⟨E, ⟨hE, α, hα, 1, by rwa [image_map_residueFieldHom_one]⟩, rfl⟩
  · rintro _ ⟨E, ⟨hE, α, hα, g, hmem⟩, rfl⟩
    have hfin : FiniteDimensional K E.1 := E.2
    rcases exists_restrictUnramifiedExtension_eq I.f (unramifiedExtension_le_of_isInvariantOf hE)
      g⁻¹ with ⟨E', σ, hσ⟩
    have hfin' : FiniteDimensional K E'.1 := E'.2
    have hE' : I.IsInvariantOf K E'.1 :=
      hE.of_algEquiv σ
    refine ⟨E', ⟨hE', σ.integerRingEquiv α,
      (MulEquiv.irreducible_iff σ.integerRingEquiv).mpr hα, ?_⟩, Quotient.sound ⟨σ.symm⟩⟩
    rw [algebraMap_residueField_eq] at hmem
    rw [algebraMap_residueField_eq, hE'.residualPolynomials_mem_image_iff,
      AlgEquiv.coe_integerRingEquiv_apply, hE.residualPairsOver_algEquiv hE' σ, List.map_map,
      Prod.map_snd', ← List.map_map, hσ, ← image_map_residueFieldHom_one I.f 𝒜,
      ← inv_mul_cancel g, ← image_map_residueFieldHom_image_map]
    exact Set.mem_image_of_mem _ ((hE.residualPolynomials_mem_image_iff α _).mp hmem)

/-- **A subfamily depends only on the orbit of its class under `Gal(K_f / K)`** (LMFDB
`lf.subfamily`): for every set `𝒜` of lists of polynomials over the residue field of `K_f` and every
element `g` of `Gal(K_f / K)`, the subfamily of `I / K` corresponding to the image of `𝒜` under the
automorphism of the residue field induced by `g`, a power of Frobenius, is the subfamily
corresponding to `𝒜`. So the classes of residual polynomials of the members of one element of
`I / K`, which can differ by Frobenius for `f > 1`, give one subfamily. -/
lemma subfamily_image_map_residueFieldHom
    (g : Gal(unramifiedExtension K (AlgebraicClosure K) I.f/K)) : I.subfamily K (List.map (map
      (g.toAlgHom.residueFieldHom : _ →+* _)) '' 𝒜) = I.subfamily K 𝒜 := by
  rw [subfamily_eq_galoisSubfamily, subfamily_eq_galoisSubfamily]
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨E, ⟨hE, α, hα, g', hmem⟩, rfl⟩
    exact ⟨E, ⟨hE, α, hα, g' * g, by rwa [image_map_residueFieldHom_image_map] at hmem⟩, rfl⟩
  · rintro _ ⟨E, ⟨hE, α, hα, g', hmem⟩, rfl⟩
    refine ⟨E, ⟨hE, α, hα, g' * g⁻¹, ?_⟩, rfl⟩
    rwa [image_map_residueFieldHom_image_map, inv_mul_cancel_right]

end Subfamily

section Uniformiser

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] {p : ℕ} {I : HerbrandInvariant p} {E E₀ : IntermediateField K (AlgebraicClosure K)}
  [FiniteDimensional K E] [FiniteDimensional K E₀] (hE : I.IsInvariantOf K E)
  (hE₀ : I.IsInvariantOf K E₀) {α : 𝒪[E]} {α₀ : 𝒪[E₀]}

lemma IsInvariantOf.residualClass_eq_of_irreducible {α' : 𝒪[E]} (hα : Irreducible α)
    (hα' : Irreducible α') : hE.residualClass α' = hE.residualClass α := by
  have hsep : Algebra.IsSeparable (unramifiedExtension K E (inertiaDegree K E)) E :=
    Algebra.isSeparable_tower_top_of_isSeparable K _ E
  rw [IsInvariantOf.residualClass, IsInvariantOf.residualClass,
    residualPolynomialClass_eq_of_irreducible
      (isTotallyRamified_unramifiedExtension_inertiaDegree K E) hα hα']

lemma IsInvariantOf.map_fst_residualPairsOver (hp : ringChar 𝓀[K] = p) (hα : Irreducible α)
    (hα₀ : Irreducible α₀) :
    (hE.residualPairsOver α).map Prod.fst = (hE₀.residualPairsOver α₀).map Prod.fst := by
  rw [IsInvariantOf.residualPairsOver, IsInvariantOf.residualPairsOver, List.map_map, List.map_map,
    Prod.map_fst', Function.id_comp, Prod.map_fst', Function.id_comp]
  exact map_fst_residualPairs_eq_of_coeffEnvelope_eq (coeffEnvelope_eq_of_ramificationPolygonOf_eq
    ((hE.ramificationPolygonOf_minpoly hp hα).trans
      (hE₀.ramificationPolygonOf_minpoly hp hα₀).symm)) _ _

lemma IsInvariantOf.map_snd_residualPairsOver_mem_iff (hp : ringChar 𝓀[K] = p) (hα : Irreducible α)
    (hα₀ : Irreducible α₀) (g : Gal(unramifiedExtension K (AlgebraicClosure K) I.f/K)) :
    (hE.residualPairsOver α).map Prod.snd ∈ List.map (map (g.toAlgHom.residueFieldHom : _ →+* _)) ''
      hE₀.residualClass α₀ ↔ hE.residualClass α = List.map
        (map (g.toAlgHom.residueFieldHom : _ →+* _)) '' hE₀.residualClass α₀ := by
  have hg : Function.Surjective g.toAlgHom.residueFieldHom :=
    Finite.injective_iff_surjective.mp g.toAlgHom.residueFieldHom.injective
  rw [hE.residualClass_eq_residualActOrbit, hE₀.residualClass_eq_residualActOrbit,
    image_map_residualActOrbit _ (g.toAlgHom.residueFieldHom :
      𝓀[unramifiedExtension K (AlgebraicClosure K) I.f] →+*
        𝓀[unramifiedExtension K (AlgebraicClosure K) I.f]) hg]
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ map_snd_mem_residualActOrbit _⟩
  rw [← residualActOrbit_eq_of_mem h]
  congr 1
  refine List.zip_of_prod ?_ rfl
  rw [hE.map_fst_residualPairsOver hE₀ hp hα hα₀, List.map_map, Prod.map_fst', Function.id_comp]

lemma IsInvariantOf.map_snd_residualPairsOver_mem_iff_eq (hp : ringChar 𝓀[K] = p)
    (hα : Irreducible α) (hα₀ : Irreducible α₀) : (hE.residualPairsOver α).map Prod.snd ∈
      hE₀.residualClass α₀ ↔ hE.residualClass α = hE₀.residualClass α₀ := by
  rw [← image_map_residueFieldHom_one I.f (hE₀.residualClass α₀)]
  exact hE.map_snd_residualPairsOver_mem_iff hE₀ hp hα hα₀ 1

/-- **Which extensions lie in the subfamily of a class** (LMFDB `lf.subfamily`): let `E₀` and `E` be
extensions in the family `I / K` inside `K̄`, for `I = (r_1, …, r_w)_ε^f` at the residue
characteristic of `K`, with uniformisers `α₀` and `α`. The class of `E` lies in the subfamily of
`I / K` corresponding to the class `𝒜₀` of residual polynomials of `E₀` at `α₀`, read over the
residue field of `K_f`, exactly when the class of `E` at `α` is the image of `𝒜₀` under an
automorphism of the residue field induced by an element of `Gal(K_f / K)`, a power of Frobenius.
The members of `I / K` are the images of `E` under the automorphisms of `K̄`, which twist its class
by all these automorphisms, and two classes with the same slopes that meet are equal. -/
lemma mk_mem_subfamily_residualClass_iff (hp : ringChar 𝓀[K] = p) (hα : Irreducible α)
    (hα₀ : Irreducible α₀) : ⟦(⟨E, inferInstance⟩ : FiniteExtension K)⟧ ∈ I.subfamily K
      (hE₀.residualClass α₀) ↔ ∃ g : Gal(unramifiedExtension K (AlgebraicClosure K) I.f/K),
        hE.residualClass α = List.map (map (g.toAlgHom.residueFieldHom : _ →+* _)) ''
          hE₀.residualClass α₀ := by
  constructor
  · rintro ⟨E', ⟨hE', β, hβ, hmem⟩, hEE'⟩
    have hfin : FiniteDimensional K E'.1 := E'.2
    rcases Quotient.exact hEE' with ⟨σ⟩
    rw [algebraMap_residueField_eq] at hmem
    have hR' : hE'.residualClass β = hE₀.residualClass α₀ :=
      (hE'.map_snd_residualPairsOver_mem_iff_eq hE₀ hp hβ hα₀).mp
        ((hE'.residualPolynomials_mem_image_iff β _).mp hmem)
    have hσβ : Irreducible (σ.integerRingEquiv β) :=
      (MulEquiv.irreducible_iff σ.integerRingEquiv).mpr hβ
    refine ⟨restrictUnramifiedExtension I.f σ, ?_⟩
    rw [hE.residualClass_eq_of_irreducible hσβ hα, AlgEquiv.coe_integerRingEquiv_apply,
      hE'.residualClass_algEquiv hE σ, hR']
  · rintro ⟨g, hg⟩
    rcases exists_restrictUnramifiedExtension_eq I.f (unramifiedExtension_le_of_isInvariantOf hE)
      g⁻¹ with ⟨E', σ, hσ⟩
    have hfin : FiniteDimensional K E'.1 := E'.2
    have hE' : I.IsInvariantOf K E'.1 :=
      hE.of_algEquiv σ
    have hR : hE'.residualClass (σ α) = hE₀.residualClass α₀ := by
      rw [hE.residualClass_algEquiv hE' σ, hσ, hg, image_map_residueFieldHom_image_map,
        inv_mul_cancel, image_map_residueFieldHom_one]
    rw [← AlgEquiv.coe_integerRingEquiv_apply] at hR
    refine ⟨E', ⟨hE', σ.integerRingEquiv α,
      (MulEquiv.irreducible_iff σ.integerRingEquiv).mpr hα, ?_⟩, Quotient.sound ⟨σ.symm⟩⟩
    rw [algebraMap_residueField_eq]
    refine (hE'.residualPolynomials_mem_image_iff _ _).mpr ?_
    rw [← hR, hE'.residualClass_eq_residualActOrbit]
    exact map_snd_mem_residualActOrbit _

/-- **For `f = 1` the literal condition depends neither on the member nor on the uniformiser**
(LMFDB `lf.subfamily`): for a family `I / K` of residue degree `f = 1` and the class `𝒜₀` of
residual polynomials of an extension `E₀` in `I / K` at a uniformiser `α₀`, the class of an
extension `E` in `I / K` lies in the subfamily corresponding to `𝒜₀` exactly when the list of
residual polynomials of `E` at `α`, any uniformiser of `E`, lies in `𝒜₀`, for every member `E` of
the class. -/
lemma mk_mem_subfamily_residualClass_iff_of_f_eq_one (hp : ringChar 𝓀[K] = p) (hf : I.f = 1)
    (hα : Irreducible α) (hα₀ : Irreducible α₀) : ⟦(⟨E, inferInstance⟩ : FiniteExtension K)⟧ ∈
      I.subfamily K (hE₀.residualClass α₀) ↔ residualPolynomials (ramificationPolynomial
        (minpoly (unramifiedExtension K E (inertiaDegree K E)) (α : E)) (α : E)) α ∈ List.map
          (map ((inclusion (unramifiedExtension_le_of_isInvariantOf hE)).residueFieldHom :
            _ →+* _)) '' hE₀.residualClass α₀ := by
  rw [mk_mem_subfamily_residualClass_iff hE hE₀ hp hα hα₀, hE.residualPolynomials_mem_image_iff,
    hE.map_snd_residualPairsOver_mem_iff_eq hE₀ hp hα hα₀]
  refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun h ↦ ⟨1, by rwa [image_map_residueFieldHom_one]⟩⟩
  rwa [eq_one_of_f_eq_one g hf, image_map_residueFieldHom_one] at hg

/-- **Up to the action of `Gal(K_f / K)`, the condition depends neither on the member nor on the
uniformiser** (LMFDB `lf.subfamily`, read with "is in `𝒜` up to the action of `Gal(K_f / K)` on the
coefficients"): for a family `I / K` of any residue degree `f` and the class `𝒜₀` of residual
polynomials of an extension `E₀` in `I / K` at a uniformiser `α₀`, the class of an extension `E` in
`I / K` lies in the subfamily corresponding to `𝒜₀` up to `Gal(K_f / K)` exactly when the list of
residual polynomials of `E` at `α`, any uniformiser of `E`, lies in the image of `𝒜₀` under some
element of `Gal(K_f / K)`, for every member `E` of the class. -/
lemma mk_mem_galoisSubfamily_residualClass_iff (hp : ringChar 𝓀[K] = p) (hα : Irreducible α)
    (hα₀ : Irreducible α₀) : ⟦(⟨E, inferInstance⟩ : FiniteExtension K)⟧ ∈ I.galoisSubfamily K
      (hE₀.residualClass α₀) ↔ ∃ g : Gal(unramifiedExtension K (AlgebraicClosure K) I.f/K),
        residualPolynomials (ramificationPolynomial
          (minpoly (unramifiedExtension K E (inertiaDegree K E)) (α : E)) (α : E)) α ∈ List.map
            (map ((inclusion (unramifiedExtension_le_of_isInvariantOf hE)).residueFieldHom :
              𝓀[unramifiedExtension K (AlgebraicClosure K) I.f] →+* 𝓀[E])) ''
            (List.map (map (g.toAlgHom.residueFieldHom : _ →+* _)) '' hE₀.residualClass α₀) := by
  rw [← subfamily_eq_galoisSubfamily, mk_mem_subfamily_residualClass_iff hE hE₀ hp hα hα₀]
  exact exists_congr fun g ↦ ((hE.residualPolynomials_mem_image_iff α _).trans
    (hE.map_snd_residualPairsOver_mem_iff hE₀ hp hα hα₀ g)).symm

end Uniformiser

section Partition

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] {p : ℕ} {I : HerbrandInvariant p} {S S' : ExtensionFamily K} {c : ExtensionClass K}

lemma exists_mem_subfamilies (hp : ringChar 𝓀[K] = p) (hc : c ∈ I.family K) :
    ∃ S ∈ I.subfamilies K, c ∈ S := by
  rcases hc with ⟨E, hE, rfl⟩
  have hfin : FiniteDimensional K E.1 := E.2
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[E.1] with ⟨α, hα⟩
  exact ⟨_, ⟨E, hE, α, hα, rfl⟩, (mk_mem_subfamily_residualClass_iff hE hE hp hα hα).mpr
    ⟨1, (image_map_residueFieldHom_one _ _).symm⟩⟩

lemma eq_of_mem_subfamilies (hp : ringChar 𝓀[K] = p) (hS : S ∈ I.subfamilies K)
    (hS' : S' ∈ I.subfamilies K) (hc : c ∈ S) (hc' : c ∈ S') : S = S' := by
  have key {T T' : ExtensionFamily K} (hT : T ∈ I.subfamilies K) (hT' : T' ∈ I.subfamilies K)
      (hcT : c ∈ T) (hcT' : c ∈ T') : T ⊆ T' := by
    rcases hT with ⟨E₁, hE₁, α₁, hα₁, rfl⟩
    rcases hT' with ⟨E₂, hE₂, α₂, hα₂, rfl⟩
    have hfin₁ : FiniteDimensional K E₁.1 := E₁.2
    have hfin₂ : FiniteDimensional K E₂.1 := E₂.2
    rcases subfamily_subset_family K I _ hcT with ⟨E, hE, rfl⟩
    have hfin : FiniteDimensional K E.1 := E.2
    rcases IsDiscreteValuationRing.exists_irreducible 𝒪[E.1] with ⟨α, hα⟩
    rcases (mk_mem_subfamily_residualClass_iff hE hE₁ hp hα hα₁).mp hcT with ⟨g₁, hg₁⟩
    rcases (mk_mem_subfamily_residualClass_iff hE hE₂ hp hα hα₂).mp hcT' with ⟨g₂, hg₂⟩
    intro c' hc'
    rcases subfamily_subset_family K I _ hc' with ⟨E', hE', rfl⟩
    have hfin' : FiniteDimensional K E'.1 := E'.2
    rcases IsDiscreteValuationRing.exists_irreducible 𝒪[E'.1] with ⟨α', hα'⟩
    rcases (mk_mem_subfamily_residualClass_iff hE' hE₁ hp hα' hα₁).mp hc' with ⟨g, hg⟩
    refine (mk_mem_subfamily_residualClass_iff hE' hE₂ hp hα' hα₂).mpr ⟨g * g₁⁻¹ * g₂, ?_⟩
    rw [← image_map_residueFieldHom_image_map, ← hg₂, hg₁, image_map_residueFieldHom_image_map,
      inv_mul_cancel_right]
    exact hg
  exact (key hS hS' hc hc').antisymm (key hS' hS hc' hc)

/-- **The subfamilies partition the family** (LMFDB `lf.subfamily`, `lf.field.label`): for a family
`I / K` of extensions of a `p`-adic field `K`, at the residue characteristic of `K`, of any residue
degree `f`, the subfamilies corresponding to the classes of residual polynomials of the extensions
in `I / K` partition `I / K`: each is nonempty, and every element of `I / K` lies in exactly one of
them. Two members of `I / K` lie in the same subfamily exactly when their classes, read over the
residue field of `K_f`, differ by an element of `Gal(K_f / K)`. -/
lemma isPartition_subfamilies (hp : ringChar 𝓀[K] = p) : Setoid.IsPartition
    ((fun S ↦ ((↑) : I.family K → ExtensionClass K) ⁻¹' S) '' I.subfamilies K) := by
  refine ⟨?_, fun c ↦ ?_⟩
  · rintro ⟨S, ⟨E₀, hE₀, α₀, hα₀, rfl⟩, hS⟩
    have hfin : FiniteDimensional K E₀.1 := E₀.2
    have hmem : ⟦E₀⟧ ∈ I.subfamily K (hE₀.residualClass α₀) :=
      (mk_mem_subfamily_residualClass_iff hE₀ hE₀ hp hα₀ hα₀).mpr
        ⟨1, (image_map_residueFieldHom_one _ _).symm⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hS) (⟨_, E₀, hE₀, rfl⟩ : I.family K) hmem
  · rcases exists_mem_subfamilies hp c.2 with ⟨S, hS, hcS⟩
    refine ⟨_, ⟨⟨S, hS, rfl⟩, hcS⟩, ?_⟩
    rintro _ ⟨⟨S', hS', rfl⟩, hcS'⟩
    rw [eq_of_mem_subfamilies hp hS' hS hcS' hcS]

end Partition

end HerbrandInvariant

end IsNonarchimedeanLocalField
