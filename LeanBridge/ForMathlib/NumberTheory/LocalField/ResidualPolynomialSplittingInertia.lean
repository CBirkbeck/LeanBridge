import LeanBridge.ForMathlib.NumberTheory.LocalField.NormalClosure
import LeanBridge.ForMathlib.NumberTheory.LocalField.ResidualPolynomialSplitting
import LeanBridge.ForMathlib.NumberTheory.LocalField.TameUnramifiedDegree

/-!
# The associated inertias divide the residue degree of the splitting field

Let `L / K` be a finite extension of nonarchimedean local fields, `L^un` its maximal unramified
subextension, over which `L` is totally ramified, `α` a uniformiser of `L` and `φ` its minimal
polynomial over `L^un`, which is Eisenstein. The knowl LMFDB `lf.associated_inertia` says that the
associated inertias of the segments of the ramification polygon of `φ`, the least common multiples
of the degrees of the irreducible factors of their residual polynomials, "are divisors of the
inertia degree of `φ`". This file proves it for the residue degree `f(N / L^un)` of the splitting
field `N` of `φ` over `L^un`, when `L / K` is separable, as every extension of `p`-adic fields is:
for the normal closure of `L / L^un` (`IsNonarchimedeanLocalField.NormalClosure`), a splitting
field of `φ`, by Ore's theorem, since the residual polynomials split over its residue field, whose
degree over that of `L` is `f(N / L) = f(N / L^un)`; and then for every splitting field of `φ`
over `L^un`, which is isomorphic to it.

Every other reading of "the inertia degree of `φ`" is a multiple of `f(N / L^un)`, and is proved
too: the residue degree `f(M / K)` of every finite extension `M` of `L` that is Galois over `L^un`,
such as `N` itself seen over `K`, and the residue degree of the Galois closure of `L / K`, the
Galois unramified degree (LMFDB `lf.unramified_degree`).

## Main results

* `IsNonarchimedeanLocalField.isSplittingField_normalClosure`: the normal closure of `L / L^un` is
  a splitting field of `φ` over `L^un`.
* `IsNonarchimedeanLocalField.dvd_inertiaDegree_of_mem_associatedInertias` (LMFDB
  `lf.associated_inertia`): the associated inertias divide `f(M / K)` for every finite extension
  `M` of `L` that is Galois over `L^un`.
* `IsNonarchimedeanLocalField.dvd_inertiaDegree_normalClosure_of_mem_associatedInertias` (LMFDB
  `lf.associated_inertia`): the associated inertias divide `f(N / L^un)` for the normal closure
  `N` of `L / L^un`.
* `IsNonarchimedeanLocalField.dvd_inertiaDegree_of_isSplittingField` (LMFDB
  `lf.associated_inertia`): the associated inertias divide `f(N / L^un)` for every splitting field
  `N` of `φ` over `L^un`.
* `IsNonarchimedeanLocalField.dvd_galoisUnramifiedDegree_of_mem_associatedInertias` (LMFDB
  `lf.associated_inertia`, `lf.unramified_degree`): the associated inertias divide the residue
  degree of the Galois closure of `L / K`.

## References

* O. Ore, *Newtonsche Polygone in der Theorie der algebraischen Körper*, Math. Ann. 99 (1928).
* S. Pauli and B. Sinclair, *Enumerating extensions of (π)-adic fields with given invariants*,
  Int. J. Number Theory 13 (2017); arXiv:1504.06671, Section 4.
-/

open IntermediateField Polynomial TauCeti ValuativeRel

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace IsNonarchimedeanLocalField

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] {α : 𝒪[L]} {a : ℕ}

/-- **The normal closure of `L / L^un` is the splitting field of `φ`**: for a finite extension
`L / K` of nonarchimedean local fields with maximal unramified subextension `L^un` and a
uniformiser `α` of `L`, the normal closure of `L / L^un` is a splitting field over `L^un` of the
minimal polynomial `φ` of `α` over `L^un`, as `L = L^un(α)`. -/
lemma isSplittingField_normalClosure (hα : Irreducible α) :
    IsSplittingField (unramifiedExtension K L (inertiaDegree K L))
      (NormalClosure (unramifiedExtension K L (inertiaDegree K L)) L)
        (minpoly (unramifiedExtension K L (inertiaDegree K L)) (α : L)) := by
  have hKL : IsTotallyRamified (unramifiedExtension K L (inertiaDegree K L)) L :=
    isTotallyRamified_unramifiedExtension_inertiaDegree K L
  have hfin : Module.Finite (unramifiedExtension K L (inertiaDegree K L)) L :=
    finite_of_valuativeExtension _ L
  have hgen : (unramifiedExtension K L (inertiaDegree K L))⟮(α : L)⟯ = ⊤ := by
    have h₁ : (unramifiedExtension K L (inertiaDegree K L))⟮algebraMap 𝒪[L] L α⟯ = ⊤ :=
      IntermediateField.adjoin_eq_top_of_algebra_adjoin_eq_top (hKL.adjoin_eq_top_of_irreducible hα)
    rwa [Algebra.algebraMap_ofSubsemiring_apply] at h₁
  have hcl : IsAlgClosure (unramifiedExtension K L (inertiaDegree K L)) (AlgebraicClosure L) :=
    .ofAlgebraic _ L (AlgebraicClosure L)
  set φ : (unramifiedExtension K L (inertiaDegree K L))[X] :=
    minpoly (unramifiedExtension K L (inertiaDegree K L)) (α : L)
  have hroot (x : AlgebraicClosure L) (hx : x ∈ φ.rootSet (AlgebraicClosure L)) :
      x ∈ normalClosure (unramifiedExtension K L (inertiaDegree K L)) L (AlgebraicClosure L) := by
    rw [normalClosure_eq_iSup_adjoin]
    exact le_iSup (fun y : L ↦ adjoin (unramifiedExtension K L (inertiaDegree K L))
      ((minpoly (unramifiedExtension K L (inertiaDegree K L)) y).rootSet (AlgebraicClosure L)))
        (α : L) (subset_adjoin _ _ hx)
  refine isSplittingField_iff.mpr ⟨splits_of_splits (IsAlgClosed.splits _) hroot,
    le_antisymm ?_ (adjoin_le_iff.mpr hroot)⟩
  rw [normalClosure_def]
  refine iSup_le fun f ↦ ?_
  rw [AlgHom.fieldRange_eq_map, ← hgen, adjoin_map, Set.image_singleton]
  refine adjoin_simple_le_iff.mpr (subset_adjoin _ _ (mem_rootSet.mpr ⟨minpoly.ne_zero
    (IsIntegral.of_finite _ _), ?_⟩))
  rw [aeval_algHom_apply, minpoly.aeval, map_zero]

variable (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra L M] [ValuativeExtension L M] [Module.Finite L M] [Algebra K M] [ValuativeExtension K M]
  [IsScalarTower K L M] [IsGalois (unramifiedExtension K L (inertiaDegree K L)) M] in
/-- **The associated inertias divide the residue degree of every Galois extension of `L^un`**
(LMFDB `lf.associated_inertia`): for a finite extension `L / K` of nonarchimedean local fields with
maximal unramified subextension `L^un`, the minimal polynomial `φ` over `L^un` of a uniformiser of
`L`, and a finite extension `M` of `L` that is Galois over `L^un`, such as the splitting field of
`φ` over `L^un`, every associated inertia of the ramification polygon of `φ` divides `f(M / L)`
and so the residue degree `f(M / K) = f(L / K) f(M / L)`. -/
lemma dvd_inertiaDegree_of_mem_associatedInertias (hα : Irreducible α)
    (ha : a ∈ associatedInertias (ramificationPolynomial
      (minpoly (unramifiedExtension K L (inertiaDegree K L)) (α : L)) (α : L)) (α : L)) :
    a ∣ inertiaDegree K M := by
  rcases List.mem_map.mp ha with ⟨kl, hkl, rfl⟩
  have hfin : Module.Finite (unramifiedExtension K L (inertiaDegree K L)) L :=
    finite_of_valuativeExtension _ L
  have hfin' : Module.Finite (unramifiedExtension K L (inertiaDegree K L)) M :=
    .trans L M
  have hval : ValuativeExtension (unramifiedExtension K L (inertiaDegree K L)) M :=
    ValuativeExtension.trans _ L M
  rw [inertiaDegree_tower K L M]
  exact (associatedInertia_dvd_inertiaDegree M
    (isTotallyRamified_unramifiedExtension_inertiaDegree K L) hα hkl).mul_left _

variable [Algebra.IsSeparable K L]

/-- **The associated inertias divide the residue degree of the splitting field** (LMFDB
`lf.associated_inertia`): for a finite separable extension `L / K` of nonarchimedean local fields,
such as an extension of `p`-adic fields, with maximal unramified subextension `L^un`, and the
minimal polynomial `φ` over `L^un` of a uniformiser `α` of `L`, every associated inertia of the
ramification polygon of `φ` divides the residue degree `f(N / L^un)` of the splitting field `N` of
`φ` over `L^un`, the normal closure of `L / L^un`. -/
lemma dvd_inertiaDegree_normalClosure_of_mem_associatedInertias (hα : Irreducible α)
    (ha : a ∈ associatedInertias (ramificationPolynomial
      (minpoly (unramifiedExtension K L (inertiaDegree K L)) (α : L)) (α : L)) (α : L)) :
    a ∣ inertiaDegree (unramifiedExtension K L (inertiaDegree K L))
      (NormalClosure (unramifiedExtension K L (inertiaDegree K L)) L) := by
  rcases List.mem_map.mp ha with ⟨kl, hkl, rfl⟩
  have hsep : Algebra.IsSeparable (unramifiedExtension K L (inertiaDegree K L)) L :=
    Algebra.isSeparable_tower_top_of_isSeparable K _ L
  have hKL : IsTotallyRamified (unramifiedExtension K L (inertiaDegree K L)) L :=
    isTotallyRamified_unramifiedExtension_inertiaDegree K L
  rw [inertiaDegree_tower (unramifiedExtension K L (inertiaDegree K L)) L
    (NormalClosure (unramifiedExtension K L (inertiaDegree K L)) L), hKL.inertiaDegree_eq_one,
    one_mul]
  exact associatedInertia_dvd_inertiaDegree _ hKL hα hkl

variable (N : Type*) [Field N] [ValuativeRel N] [TopologicalSpace N] [IsNonarchimedeanLocalField N]
  [Algebra (unramifiedExtension K L (inertiaDegree K L)) N]
  [ValuativeExtension (unramifiedExtension K L (inertiaDegree K L)) N]
  [IsSplittingField (unramifiedExtension K L (inertiaDegree K L)) N
    (minpoly (unramifiedExtension K L (inertiaDegree K L)) (α : L))] in
/-- **The associated inertias divide the residue degree of every splitting field of `φ`** (LMFDB
`lf.associated_inertia`): for a finite separable extension `L / K` of nonarchimedean local fields,
such as an extension of `p`-adic fields, with maximal unramified subextension `L^un`, the minimal
polynomial `φ` over `L^un` of a uniformiser `α` of `L`, and a splitting field `N` of `φ` over
`L^un`, with any structure of nonarchimedean local field extending that of `L^un`, every associated
inertia of the ramification polygon of `φ` divides the residue degree `f(N / L^un)`: `N` is
isomorphic over `L^un` to the normal closure of `L / L^un`, and so has the same residue degree. -/
lemma dvd_inertiaDegree_of_isSplittingField (hα : Irreducible α)
    (ha : a ∈ associatedInertias (ramificationPolynomial
      (minpoly (unramifiedExtension K L (inertiaDegree K L)) (α : L)) (α : L)) (α : L)) :
    a ∣ inertiaDegree (unramifiedExtension K L (inertiaDegree K L)) N := by
  have hN : IsSplittingField (unramifiedExtension K L (inertiaDegree K L))
      (NormalClosure (unramifiedExtension K L (inertiaDegree K L)) L)
        (minpoly (unramifiedExtension K L (inertiaDegree K L)) (α : L)) :=
    isSplittingField_normalClosure hα
  let σ : AlgEquiv (unramifiedExtension K L (inertiaDegree K L))
      (NormalClosure (unramifiedExtension K L (inertiaDegree K L)) L) N :=
    (IsSplittingField.algEquiv _ _).trans (IsSplittingField.algEquiv N
      (minpoly (unramifiedExtension K L (inertiaDegree K L)) (α : L))).symm
  let _ : Algebra (NormalClosure (unramifiedExtension K L (inertiaDegree K L)) L) N :=
    σ.toRingHom.toAlgebra
  have : IsScalarTower (unramifiedExtension K L (inertiaDegree K L))
      (NormalClosure (unramifiedExtension K L (inertiaDegree K L)) L) N :=
    .of_algebraMap_eq fun x ↦ (σ.commutes x).symm
  have : ValuativeExtension (NormalClosure (unramifiedExtension K L (inertiaDegree K L)) L) N :=
    σ.toAlgHom.valuativeExtension
  have h₁ : Module.finrank (NormalClosure (unramifiedExtension K L (inertiaDegree K L)) L) N = 1 :=
    Module.finrank_of_bijective_algebraMap σ.bijective
  rw [inertiaDegree_tower (unramifiedExtension K L (inertiaDegree K L))
    (NormalClosure (unramifiedExtension K L (inertiaDegree K L)) L) N,
    (mul_eq_one.mp ((ramificationIndex_mul_inertiaDegree _ N).trans h₁)).2, mul_one]
  exact dvd_inertiaDegree_normalClosure_of_mem_associatedInertias hα ha

variable [FiniteDimensional K L] in
/-- **The associated inertias divide the Galois unramified degree** (LMFDB `lf.associated_inertia`,
`lf.unramified_degree`): for a finite separable extension `L / K` of nonarchimedean local fields
with maximal unramified subextension `L^un`, and the minimal polynomial `φ` over `L^un` of a
uniformiser of `L`, every associated inertia of the ramification polygon of `φ` divides the residue
degree of the Galois closure of `L / K`, which is Galois over `L^un` and contains `L`. -/
lemma dvd_galoisUnramifiedDegree_of_mem_associatedInertias (hα : Irreducible α)
    (ha : a ∈ associatedInertias (ramificationPolynomial
      (minpoly (unramifiedExtension K L (inertiaDegree K L)) (α : L)) (α : L)) (α : L)) :
    a ∣ galoisUnramifiedDegree K L := by
  let _ : Algebra L (Algebra.galoisClosure K L) := (Algebra.toGaloisClosure K L).toAlgebra
  have : IsScalarTower K L (Algebra.galoisClosure K L) :=
    .of_algebraMap_eq fun x ↦ ((Algebra.toGaloisClosure K L).commutes x).symm
  have : ValuativeExtension L (Algebra.galoisClosure K L) :=
    (Algebra.toGaloisClosure K L).valuativeExtension
  have : Module.Finite L (Algebra.galoisClosure K L) :=
    .of_restrictScalars_finite K L _
  have : IsGalois (unramifiedExtension K L (inertiaDegree K L)) (Algebra.galoisClosure K L) :=
    IsGalois.tower_top_of_isGalois K _ _
  exact dvd_inertiaDegree_of_mem_associatedInertias _ hα ha

end IsNonarchimedeanLocalField
