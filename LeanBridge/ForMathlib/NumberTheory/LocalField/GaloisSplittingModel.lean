import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.AdjoinRoot

/-!
# Galois splitting models of `p`-adic fields

A Galois splitting model of a finite extension `K` of `ℚ_p` is an irreducible polynomial
`f ∈ ℚ[x]` with `K ≅ ℚ_p[x]/(f)` whose Galois groups over `ℚ` and over `ℚ_p` are isomorphic. The
Galois group of `f` over `ℚ_p` always embeds in its Galois group over `ℚ`, by restriction to the
splitting field of `f` over `ℚ`; the condition says that this embedding is onto.

## Main definitions

* `Polynomial.Gal.restrictMap`: for a field extension `E/F` and `f ∈ F[x]`, the restriction from
  the Galois group of `f` over `E` to that over `F`.
* `Polynomial.IsGaloisSplittingModel` (LMFDB `lf.galois_splitting_model`).

## Main results

* `Polynomial.Gal.restrictMap_injective`: the restriction is injective.
* `Polynomial.Gal.nonempty_mulEquiv_iff_bijective_restrictMap`: the Galois groups of `f` over `F`
  and over `E` are isomorphic exactly when the restriction is bijective.
* `Polynomial.IsGaloisSplittingModel.irreducible_map`: a Galois splitting model stays irreducible
  over `ℚ_p`.
* `Polynomial.IsGaloisSplittingModel.finrank_eq`: its degree is the degree of `K` over `ℚ_p`.
-/

namespace Polynomial.Gal

variable {F : Type*} [Field F] (f : F[X]) (E : Type*) [Field E] [Algebra F E]

local instance : Fact ((f.map (algebraMap F (f.map (algebraMap F E)).SplittingField)).Splits) :=
  ⟨by simpa [map_map, ← IsScalarTower.algebraMap_eq] using
    SplittingField.splits (f.map (algebraMap F E))⟩

/-- The **restriction** from the Galois group of `f ∈ F[x]` over a field extension `E` of `F` to its
Galois group over `F`: an automorphism of the splitting field `L` of `f` over `E` fixing `E` fixes
`F`, and restricts to the splitting field of `f` over `F` inside `L`. -/
noncomputable def restrictMap : (f.map (algebraMap F E)).Gal →* f.Gal :=
  (restrict f (f.map (algebraMap F E)).SplittingField).comp (AlgEquiv.restrictScalarsHom F)

/-- **The restriction of Galois groups along a field extension is injective**: an automorphism of
the splitting field over `E` is determined by its action on the roots of `f`. -/
lemma restrictMap_injective : Function.Injective (restrictMap f E) :=
  (injective_iff_map_eq_one _).mpr fun σ hσ ↦ Gal.ext _ fun x hx ↦
    (restrict_smul (AlgEquiv.restrictScalarsHom F σ) ⟨x, by simpa using hx⟩).symm.trans <| by
      rw [show restrict f _ (AlgEquiv.restrictScalarsHom F σ) = 1 from hσ, one_smul]
      rfl

/-- **The Galois groups of `f` over `F` and over `E` are isomorphic exactly when the restriction is
bijective**, as the restriction is injective and the groups are finite. -/
lemma nonempty_mulEquiv_iff_bijective_restrictMap :
    Nonempty (f.Gal ≃* (f.map (algebraMap F E)).Gal) ↔ Function.Bijective (restrictMap f E) :=
  ⟨fun ⟨e⟩ ↦ (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨restrictMap_injective f E, Fintype.card_congr e.symm.toEquiv⟩,
    fun h ↦ ⟨(MulEquiv.ofBijective _ h).symm⟩⟩

end Polynomial.Gal

namespace Polynomial

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K]

/-- A **Galois splitting model** of a finite extension `K` of `ℚ_p` (LMFDB
`lf.galois_splitting_model`): an irreducible polynomial `f ∈ ℚ[x]` such that `K ≅ ℚ_p[x]/(f)` as
`ℚ_p`-algebras and the Galois group of `f` over `ℚ` is isomorphic to its Galois group over `ℚ_p`.
As the latter embeds in the former by restriction, the last condition says that the restriction
`Polynomial.Gal.restrictMap` is bijective
(`Polynomial.Gal.nonempty_mulEquiv_iff_bijective_restrictMap`). -/
structure IsGaloisSplittingModel (f : ℚ[X]) : Prop where
  /-- The polynomial is irreducible over `ℚ`. -/
  irreducible : Irreducible f
  /-- The field `K` is `ℚ_p[x]/(f)`. -/
  nonempty_algEquiv : Nonempty (K ≃ₐ[ℚ_[p]] AdjoinRoot (f.map (algebraMap ℚ ℚ_[p])))
  /-- The Galois groups of `f` over `ℚ` and over `ℚ_p` are isomorphic. -/
  nonempty_mulEquiv : Nonempty (f.Gal ≃* (f.map (algebraMap ℚ ℚ_[p])).Gal)

variable {p K} {f : ℚ[X]} (hf : IsGaloisSplittingModel p K f)
include hf

/-- **A Galois splitting model stays irreducible over `ℚ_p`**, as `ℚ_p[x]/(f)` is a field. -/
lemma IsGaloisSplittingModel.irreducible_map : Irreducible (f.map (algebraMap ℚ ℚ_[p])) :=
  hf.nonempty_algEquiv.elim fun e ↦
    AdjoinRoot.isField_iff_irreducible.mp <| e.symm.toMulEquiv.isField <| Field.toIsField K

/-- **The degree of a Galois splitting model is the degree of `K` over `ℚ_p`.** -/
lemma IsGaloisSplittingModel.finrank_eq : Module.finrank ℚ_[p] K = f.natDegree := by
  rcases hf.nonempty_algEquiv with ⟨e⟩
  rw [e.toLinearEquiv.finrank_eq, (AdjoinRoot.powerBasis hf.irreducible_map.ne_zero).finrank,
    AdjoinRoot.powerBasis_dim, natDegree_map]

end Polynomial
