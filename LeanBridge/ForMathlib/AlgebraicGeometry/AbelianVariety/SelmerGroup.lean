import Mathlib.Algebra.Module.ZMod
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import TauCeti.FieldTheory.GaloisCohomology.EmbeddingIndependence
import TauCeti.RepresentationTheory.Homological.ContCohomology.SelmerStructure
import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.GaloisCoefficients

/-!
# The Selmer groups and the 2-Selmer rank of an abelian variety

Let `A` be an abelian variety over a field `K`, with Galois cohomology taken in the discrete
`G_K`-modules `A(Kˢ)` and `A(Kˢ)[m]` (`TauCeti.AlgebraicGeometry.AbelianVariety.PointCoeff`,
`TauCeti.AlgebraicGeometry.AbelianVariety.TorsionCoeff`). Fix a family `(F i)` of field extensions
of `K`, each with a `K`-embedding `σ i : Kˢ → (F i)ˢ` of separable closures, along which a class
of `H¹(G_K, A[m])` restricts to `H¹(G_{F i}, A[m])`. The `m`-Selmer group relative to this family
is the group of classes of `H¹(G_K, A[m])` whose restriction to every `F i` vanishes in
`H¹(G_{F i}, A((F i)ˢ))`, that is lies in the image of the local Kummer map
`A(F i) / m A(F i) → H¹(G_{F i}, A[m])`, by the exactness of
`A(L) → A(L) → H¹(G_L, A[m]) → H¹(G_L, A(Lˢ))` when multiplication by `m` is onto `A(Lˢ)`, as it
is when `m` is invertible in `L`. It does not depend on the embeddings. For a number field `K` and
the family of its completions at all its places, finite and infinite, this is the `m`-Selmer group
`Sel_m(A / K)`, an elementary abelian `2`-group for `m = 2`, whose dimension over `𝔽₂` is the
`2`-Selmer rank of `A`.

## Main definitions

* `TauCeti.AlgebraicGeometry.AbelianVariety.torsionRes`: the restriction map
  `H¹(G_K, A[m]) → H¹(G_L, A[m])` along an embedding `Kˢ → Lˢ`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.kummerCondition`: the kernel of
  `H¹(G_L, A[m]) → H¹(G_L, A(Lˢ))`, the image of the local Kummer map.
* `TauCeti.AlgebraicGeometry.AbelianVariety.selmerStructure` and
  `TauCeti.AlgebraicGeometry.AbelianVariety.selmerGroup`: the Selmer structure and the `m`-Selmer
  group relative to a family of extensions.
* `TauCeti.AlgebraicGeometry.AbelianVariety.numberFieldSelmerGroup` (LMFDB `ag.selmer_group`): the
  `m`-Selmer group `Sel_m(A / K)` of an abelian variety over a number field.
* `TauCeti.AlgebraicGeometry.AbelianVariety.twoSelmerRank` (LMFDB `g2c.two_selmer_rank`): the
  `2`-Selmer rank, the dimension of `Sel_2(A / K)` over `𝔽₂`.

## Main results

* `TauCeti.AlgebraicGeometry.AbelianVariety.torsionRes_eq_torsionRes`: the restriction map does not
  depend on the embedding of separable closures.
* `TauCeti.AlgebraicGeometry.AbelianVariety.mem_selmerGroup_iff`: a class is Selmer exactly when its
  restriction to every `F i` lies in the image of the local Kummer map.
* `TauCeti.AlgebraicGeometry.AbelianVariety.selmerGroup_eq_selmerGroup`: the Selmer group does not
  depend on the embeddings of separable closures.
* `TauCeti.AlgebraicGeometry.AbelianVariety.mem_numberFieldSelmerGroup_iff`: the description of
  `Sel_m(A / K)` for any choice of embeddings.
* `TauCeti.AlgebraicGeometry.AbelianVariety.nsmul_eq_zero_of_torsionCoeff`: `H¹(G_L, A[m])` is
  killed by `m`, so `Sel_2(A / K)` is a vector space over `𝔽₂` (the instance
  `Module (ZMod 2) (A.numberFieldSelmerGroup 2)`).
* `TauCeti.AlgebraicGeometry.AbelianVariety.natCard_numberFieldSelmerGroup_two`: a finite
  `Sel_2(A / K)` has order `2` to the power of the `2`-Selmer rank.

That `Sel_m(A / K)` is finite, and that the `2`-Selmer rank minus the `2`-rank of the torsion of
`A(K)` bounds the Mordell–Weil rank of `A`, are not formalised.
-/

open AddSubgroup IsDedekindDomain NumberField TauCeti ContCohomology

universe u

namespace TauCeti.AlgebraicGeometry.AbelianVariety

variable {K : Type u} [Field K] (A : AbelianVariety K) {L : Type u} [Field L] [Algebra K L] (m : ℕ)

/-- `H¹(G_L, A(Lˢ)[m])` is killed by `m`, as `A(Lˢ)[m]` is. -/
lemma nsmul_eq_zero_of_torsionCoeff (c : H1 (AbsoluteGaloisGroup L) (A.TorsionCoeff L m)) :
    m • c = 0 := by
  induction c using QuotientAddGroup.induction_on with
  | H z =>
    have hz : m • z = 0 := Subtype.ext <| funext fun g ↦ torsionBy.nsmul (z.1 g)
    rw [← QuotientAddGroup.mk_nsmul, hz, QuotientAddGroup.mk_zero]

variable (τ τ' : SeparableClosure K →ₐ[K] SeparableClosure L)

/-- The **restriction** `H¹(G_K, A(Kˢ)[m]) → H¹(G_L, A(Lˢ)[m])` along a `K`-embedding
`τ : Kˢ → Lˢ` of separable closures, for a field extension `L` of `K`: the pullback along the map
`G_L → G_K` and the map `A(Kˢ)[m] → A(Lˢ)[m]` given by `τ`. It does not depend on `τ`
(`TauCeti.AlgebraicGeometry.AbelianVariety.torsionRes_eq_torsionRes`). -/
noncomputable def torsionRes : H1 (AbsoluteGaloisGroup K) (A.TorsionCoeff K m) →+
    H1 (AbsoluteGaloisGroup L) (A.TorsionCoeff L m) :=
  explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ) (A.torsionCoeffMap τ m)
    continuous_of_discreteTopology (A.torsionCoeffMap_smul τ m)

/-- The restriction `H¹(G_K, A[m]) → H¹(G_L, A[m])` does not depend on the embedding of separable
closures. -/
lemma torsionRes_eq_torsionRes : A.torsionRes m τ = A.torsionRes m τ' :=
  explicitMap1_absoluteGaloisGroupMap_eq (fun τ ↦ A.torsionCoeffMap τ m)
    (fun τ ↦ A.torsionCoeffMap_smul τ m) (fun τ ↦ A.torsionCoeffMap_comp τ m) τ τ'

variable (L) in
/-- The **local Kummer condition** at a field extension `L` of `K`: the kernel of the map
`H¹(G_L, A(Lˢ)[m]) → H¹(G_L, A(Lˢ))` induced by the inclusion `A(Lˢ)[m] → A(Lˢ)`. When
multiplication by `m` is onto `A(Lˢ)`, as it is when `m` is invertible in `L`, it is the image of
the local Kummer map `A(L) / m A(L) → H¹(G_L, A(Lˢ)[m])`, by the long exact sequence of
`0 → A(Lˢ)[m] → A(Lˢ) → A(Lˢ) → 0`. -/
noncomputable def kummerCondition : AddSubgroup (H1 (AbsoluteGaloisGroup L) (A.TorsionCoeff L m)) :=
  (explicitCoeff1 _ _ (A.torsionCoeffIncl L m) continuous_of_discreteTopology).ker

variable {ι : Type*} {F : ι → Type u} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
  (σ σ' : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (F i))
  {c : H1 (AbsoluteGaloisGroup K) (A.TorsionCoeff K m)}

/-- The **Selmer structure of the `m`-Selmer group** of an abelian variety `A` over `K`, relative to
a family of field extensions `F i` of `K` with `K`-embeddings `σ i : Kˢ → (F i)ˢ` of separable
closures: on `A(Kˢ)[m]`, localised along the restrictions to the `F i`
(`TauCeti.AlgebraicGeometry.AbelianVariety.torsionRes`), with the local Kummer conditions
(`TauCeti.AlgebraicGeometry.AbelianVariety.kummerCondition`). -/
noncomputable def selmerStructure : SelmerStructure (AbsoluteGaloisGroup K) (A.TorsionCoeff K m)
    (fun i ↦ AbsoluteGaloisGroup (F i)) (fun i ↦ A.TorsionCoeff (F i) m) where
  groupHom i := absoluteGaloisGroupMap (σ i)
  coeffHom i := A.torsionCoeffMap (σ i) m
  continuous_coeffHom _ := continuous_of_discreteTopology
  coeffHom_smul i := A.torsionCoeffMap_smul (σ i) m
  localCondition i := A.kummerCondition (F i) m

/-- The **`m`-Selmer group** of an abelian variety `A` over `K`, relative to a family of field
extensions `F i` of `K` with `K`-embeddings `σ i : Kˢ → (F i)ˢ` of separable closures: the classes
of `H¹(G_K, A(Kˢ)[m])` whose restriction to every `F i` lies in the local Kummer condition
(`TauCeti.AlgebraicGeometry.AbelianVariety.kummerCondition`), the image of the local Kummer map
`A(F i) / m A(F i) → H¹(G_{F i}, A[m])` when `m` is invertible in `K`. It does not depend on the
embeddings (`TauCeti.AlgebraicGeometry.AbelianVariety.selmerGroup_eq_selmerGroup`). -/
noncomputable def selmerGroup : AddSubgroup (H1 (AbsoluteGaloisGroup K) (A.TorsionCoeff K m)) :=
  (A.selmerStructure m σ).selmerGroup

/-- A class of `H¹(G_K, A[m])` is Selmer exactly when its restriction to every `F i` lies in the
local Kummer condition. -/
lemma mem_selmerGroup_iff :
    c ∈ A.selmerGroup m σ ↔ ∀ i, A.torsionRes m (σ i) c ∈ A.kummerCondition (F i) m :=
  SelmerStructure.mem_selmerGroup_iff _

/-- The `m`-Selmer group relative to a family of field extensions does not depend on the embeddings
of separable closures. -/
lemma selmerGroup_eq_selmerGroup : A.selmerGroup m σ = A.selmerGroup m σ' := by
  ext c
  simp only [mem_selmerGroup_iff, A.torsionRes_eq_torsionRes m (σ _) (σ' _)]

variable [NumberField K]

/-- The **`m`-Selmer group** `Sel_m(A / K)` (LMFDB `ag.selmer_group`) of an abelian variety `A`
over a number field `K`: the classes of `H¹(G_K, A(Kˢ)[m])` whose restriction to
`H¹(G_{K_v}, A[m])` lies in the image of the local Kummer map
`A(K_v) / m A(K_v) → H¹(G_{K_v}, A[m])`, that is vanishes in `H¹(G_{K_v}, A(K_vˢ))`, for every
place `v` of `K`, finite or infinite, where `K_v` is the completion of `K` at `v`
(`TauCeti.AlgebraicGeometry.AbelianVariety.kummerCondition`). The restrictions are taken along
embeddings `Kˢ → K_vˢ` of separable closures, whose choice does not matter
(`TauCeti.AlgebraicGeometry.AbelianVariety.mem_numberFieldSelmerGroup_iff`). It is finite (not
formalised here). The LMFDB also considers the Selmer group of an isogeny, which is not formalised
here. -/
noncomputable def numberFieldSelmerGroup :
    AddSubgroup (H1 (AbsoluteGaloisGroup K) (A.TorsionCoeff K m)) :=
  A.selmerGroup (F := fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K) m
    (fun _ ↦ IsSepClosed.lift) ⊓
    A.selmerGroup (F := fun v : InfinitePlace K ↦ v.Completion) m fun _ ↦ IsSepClosed.lift

/-- A class of `H¹(G_K, A[m])` lies in `Sel_m(A / K)` exactly when its restrictions to the
completions of `K` at all its finite and infinite places lie in the images of the local Kummer
maps, for any choice of embeddings of separable closures. -/
lemma mem_numberFieldSelmerGroup_iff (ρ : ∀ v : HeightOneSpectrum (𝓞 K), SeparableClosure K →ₐ[K]
    SeparableClosure (v.adicCompletion K)) (ρ' : ∀ v : InfinitePlace K, SeparableClosure K →ₐ[K]
    SeparableClosure v.Completion) : c ∈ A.numberFieldSelmerGroup m ↔
    (∀ v, A.torsionRes m (ρ v) c ∈ A.kummerCondition (v.adicCompletion K) m) ∧
    ∀ v, A.torsionRes m (ρ' v) c ∈ A.kummerCondition v.Completion m := by
  rw [numberFieldSelmerGroup, AddSubgroup.mem_inf, A.selmerGroup_eq_selmerGroup m _ ρ,
    A.selmerGroup_eq_selmerGroup m _ ρ', mem_selmerGroup_iff, mem_selmerGroup_iff]

noncomputable instance : Module (ZMod 2) (A.numberFieldSelmerGroup 2) :=
  AddCommGroup.zmodModule fun c ↦ Subtype.ext <| A.nsmul_eq_zero_of_torsionCoeff 2 c.1

/-- The **`2`-Selmer rank** (LMFDB `g2c.two_selmer_rank`) of an abelian variety `A` over a number
field `K`: the rank of its `2`-Selmer group `Sel_2(A / K)`
(`TauCeti.AlgebraicGeometry.AbelianVariety.numberFieldSelmerGroup`), its dimension as a vector
space over `𝔽₂`, as it is killed by `2`
(`TauCeti.AlgebraicGeometry.AbelianVariety.nsmul_eq_zero_of_torsionCoeff`). As `Sel_2(A / K)` is
finite (not formalised here), its order is `2` to the power of the `2`-Selmer rank
(`TauCeti.AlgebraicGeometry.AbelianVariety.natCard_numberFieldSelmerGroup_two`). The LMFDB
considers the Jacobians of genus `2` curves. -/
noncomputable def twoSelmerRank : ℕ :=
  Module.finrank (ZMod 2) (A.numberFieldSelmerGroup 2)

/-- A finite `2`-Selmer group has order `2` to the power of the `2`-Selmer rank. -/
lemma natCard_numberFieldSelmerGroup_two [Finite (A.numberFieldSelmerGroup 2)] :
    Nat.card (A.numberFieldSelmerGroup 2) = 2 ^ A.twoSelmerRank := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, twoSelmerRank]

end TauCeti.AlgebraicGeometry.AbelianVariety
