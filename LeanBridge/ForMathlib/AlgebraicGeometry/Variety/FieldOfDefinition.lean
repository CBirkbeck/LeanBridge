import LeanBridge.ForMathlib.AlgebraicGeometry.Variety.Basic
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Order.Minimal

/-!
# Fields of definition and base change of varieties

The base change `V_L` of a variety `V` over a field `K` along a field extension `L / K` (LMFDB
`ag.base_change`) is the pullback of `V` along `Spec L ⟶ Spec K`, Mathlib's
`CategoryTheory.Over.pullback`; it is again a variety, over `L`.

The fields of definition of a variety `X` over a field `L` are the subfields `k₀ ⊆ L` such that
`X` is isomorphic over `L` to the base change of a variety over `k₀`. A minimal field of definition
is a minimal element of this set, and `X` is a base change if it has a field of definition other
than `L`, that is if `L` is not a minimal field of definition of `X`.

## Main definitions

* `AlgebraicGeometry.Scheme.fieldsOfDefinition` (LMFDB `ag.minimal_field`): the fields of
  definition of a variety.
* `AlgebraicGeometry.Scheme.IsMinimalFieldOfDefinition` (LMFDB `ag.minimal_field`).
* `AlgebraicGeometry.Scheme.IsBaseChangeFromSubfield` (LMFDB `ag.base_change`).

## Main results

* `AlgebraicGeometry.Scheme.mem_fieldsOfDefinition_pullback`: a subfield `k₀ ⊆ L` is a field of
  definition of the base change to `L` of any variety over `k₀`.
* `AlgebraicGeometry.Scheme.isUpperSet_fieldsOfDefinition`: a subfield containing a field of
  definition is a field of definition.
* `AlgebraicGeometry.Scheme.isBaseChangeFromSubfield_pullback`: the base change to `L` of a variety
  over a proper subfield of `L` is a base change.
* `AlgebraicGeometry.Scheme.top_mem_fieldsOfDefinition`: a variety over `L` is defined over `L`.
* `AlgebraicGeometry.Scheme.isBaseChangeFromSubfield_iff`: a variety over `L` is a base change if
  and only if `L` is not a minimal field of definition of it.
-/

namespace AlgebraicGeometry.Scheme

open CategoryTheory Limits

universe u

variable {L : Type u} [Field L] {X : Scheme.{u}} [X.Over (Spec (.of L))] {k₀ : Subfield L}
  (X₀ : Over (Spec (.of k₀))) [X₀.left.IsVarietyOver k₀]

variable (L X) in
/-- The **fields of definition** of a variety `X` over a field `L` (LMFDB `ag.minimal_field`): the
subfields `k₀ ⊆ L` for which there is a variety `X₀` over `k₀` whose base change `X₀ ×_{k₀} L` to
`L` is isomorphic to `X` over `L`. -/
def fieldsOfDefinition : Set (Subfield L) :=
  {k₀ | ∃ X₀ : Over (Spec (.of k₀)), X₀.left.IsVarietyOver k₀ ∧
    Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ L)))).obj X₀ ≅
    X.asOver (Spec (.of L)))}

/-- A subfield `k₀ ⊆ L` is a field of definition of the base change to `L` of any variety over
`k₀`. -/
lemma mem_fieldsOfDefinition_pullback : k₀ ∈ ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap k₀ L)))).obj X₀).left.fieldsOfDefinition L :=
  ⟨X₀, inferInstance, ⟨Over.isoMk (Iso.refl _)⟩⟩

/-- The fields of definition of a variety form an upper set: a subfield of `L` containing a field
of definition is a field of definition. -/
lemma isUpperSet_fieldsOfDefinition : IsUpperSet (X.fieldsOfDefinition L) := by
  rintro k₀ k₁ hle ⟨X₀, _, ⟨e⟩⟩
  let χ : Spec (.of k₁) ⟶ Spec (.of k₀) := Spec.map (CommRingCat.ofHom (Subfield.inclusion hle))
  have h : Spec.map (CommRingCat.ofHom (algebraMap k₁ L)) ≫ χ =
      Spec.map (CommRingCat.ofHom (algebraMap k₀ L)) := by
    rw [← Spec.map_comp]
    rfl
  exact ⟨(Over.pullback χ).obj X₀, inferInstance,
    ⟨((Over.pullbackComp _ χ).symm ≪≫ eqToIso (by simp only [h])).app X₀ ≪≫ e⟩⟩

variable (L X k₀) in
/-- A subfield `k₀ ⊆ L` is a **minimal field of definition** (LMFDB `ag.minimal_field`) of a variety
`X` over `L` if it is a field of definition of `X` that contains no other field of definition of
`X`. A variety may have several minimal fields of definition. -/
def IsMinimalFieldOfDefinition : Prop :=
  Minimal (· ∈ X.fieldsOfDefinition L) k₀

variable (L X) in
/-- A variety `X` over a field `L` **is a base change** (LMFDB `ag.base_change`) if it is isomorphic
over `L` to the base change of a variety defined over a proper subfield of `L`. -/
def IsBaseChangeFromSubfield : Prop :=
  ∃ k₀ ∈ X.fieldsOfDefinition L, k₀ ≠ ⊤

/-- The base change to `L` of a variety over a proper subfield of `L` is a base change. -/
lemma isBaseChangeFromSubfield_pullback (hk₀ : k₀ ≠ ⊤) : ((Over.pullback (Spec.map
    (CommRingCat.ofHom (algebraMap k₀ L)))).obj X₀).left.IsBaseChangeFromSubfield L :=
  ⟨k₀, mem_fieldsOfDefinition_pullback X₀, hk₀⟩

variable [X.IsVarietyOver L]

/-- A variety over `L` is defined over `L`: `L` is a field of definition of it. -/
lemma top_mem_fieldsOfDefinition : ⊤ ∈ X.fieldsOfDefinition L := by
  let φ : Spec (.of L) ⟶ Spec (.of (⊤ : Subfield L)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (⊤ : Subfield L) L))
  let ψ : Spec (.of (⊤ : Subfield L)) ⟶ Spec (.of L) :=
    Spec.map (CommRingCat.ofHom Subfield.topEquiv.symm.toRingHom)
  have h : φ ≫ ψ = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    rfl
  exact ⟨(Over.pullback ψ).obj (X.asOver (Spec (.of L))), inferInstance,
    ⟨((Over.pullbackComp φ ψ).symm ≪≫ eqToIso (by simp only [h]) ≪≫ Over.pullbackId).app _⟩⟩

/-- A variety over `L` is a base change if and only if `L` is not a minimal field of definition of
it. -/
lemma isBaseChangeFromSubfield_iff :
    X.IsBaseChangeFromSubfield L ↔ ¬X.IsMinimalFieldOfDefinition L ⊤ := by
  simp [IsBaseChangeFromSubfield, IsMinimalFieldOfDefinition, Minimal, top_mem_fieldsOfDefinition]

end AlgebraicGeometry.Scheme
