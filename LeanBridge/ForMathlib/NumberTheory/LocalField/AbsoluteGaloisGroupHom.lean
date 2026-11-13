import TauCeti.NumberTheory.LocalField.Generation.AbsoluteGaloisGroup

/-!
# Continuous homomorphisms from a local absolute Galois group to a finite group

Let `K` be a finite extension of `ℚ_p`. The absolute Galois group `Gal(K̄/K)` is topologically
finitely generated (Tau Ceti, after NSW (7.4.1)), and a continuous homomorphism from it to a finite
Hausdorff (that is, discrete) group `G` is determined by its values on a finite topological
generating set, so there are only finitely many such homomorphisms. For `K = ℚ_p` this is the
finiteness of the set `Hom(Γ_{ℚ_p}, G)` on which the LMFDB knowl `nf.inertial_height_function`
takes its auxiliary local heights `H_p` at the primes `p ∣ #G`, the arguments `H` of
`NumberField.WeightFunction.inertialHeight`.

The same theorem gives the classical finiteness of the extensions of `K` of a given degree `n`
inside `K̄`: the fixing subgroup of such an extension is an open subgroup of index `n` of
`Gal(K̄/K)`, a topologically finitely generated group has finitely many of these (Tau Ceti), and an
intermediate field of the Galois extension `K̄/K` is the fixed field of its fixing subgroup.

## Main results

* `TauCeti.IsTopologicallyFinitelyGenerated.finite_continuousMonoidHom`: a topologically finitely
  generated group has finitely many continuous homomorphisms to a finite Hausdorff monoid.
* `IsNonarchimedeanLocalField.finite_continuousMonoidHom_absoluteGaloisGroup`: for a finite
  extension `K` of `ℚ_p` and a finite Hausdorff group `G`, there are finitely many continuous
  homomorphisms `Gal(K̄/K) → G`.
* `IsNonarchimedeanLocalField.finite_setOf_finrank_eq`: a finite extension `K` of `ℚ_p` has finitely
  many extensions of degree `n ≠ 0` inside `K̄`.
* `Padic.finite_continuousMonoidHom_absoluteGaloisGroup` (LMFDB `nf.inertial_height_function`):
  the set `Hom(Γ_{ℚ_p}, G)` of continuous homomorphisms `Gal(ℚ̄_p/ℚ_p) → G` is finite for every
  finite Hausdorff group `G`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.4.1).
-/

open TauCeti

namespace TauCeti.IsTopologicallyFinitelyGenerated

/-- **A topologically finitely generated group has finitely many continuous homomorphisms to a
finite Hausdorff monoid**: such a homomorphism is determined by its values on a finite topological
generating set. -/
lemma finite_continuousMonoidHom {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (hΓ : IsTopologicallyFinitelyGenerated Γ) (M : Type*) [Monoid M] [TopologicalSpace M]
    [T2Space M] [Finite M] : Finite (Γ →ₜ* M) := by
  rcases hΓ with ⟨s, hs⟩
  refine Finite.of_injective (fun φ (x : s) ↦ φ x) fun φ ψ h ↦ ?_
  exact ContinuousMonoidHom.toMonoidHom_injective <|
    MonoidHom.eq_of_eqOn_of_topologicalClosure_closure_eq_top hs φ.continuous ψ.continuous
      fun x hx ↦ congrFun h ⟨x, hx⟩

end TauCeti.IsTopologicallyFinitelyGenerated

namespace IsNonarchimedeanLocalField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **A local absolute Galois group has finitely many continuous homomorphisms to a finite group**:
for a finite extension `K` of `ℚ_p` and a finite Hausdorff group `G`, there are finitely many
continuous homomorphisms `Gal(K̄/K) → G`, as `Gal(K̄/K)` is topologically finitely generated (Tau
Ceti's `TauCeti.isTopologicallyFinitelyGenerated_absoluteGaloisGroup`). -/
lemma finite_continuousMonoidHom_absoluteGaloisGroup (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] K]
    [Module.Finite ℚ_[p] K] [ValuativeExtension ℚ_[p] K] (G : Type*) [Group G] [TopologicalSpace G]
    [T2Space G] [Finite G] : Finite (Field.absoluteGaloisGroup K →ₜ* G) :=
  (isTopologicallyFinitelyGenerated_absoluteGaloisGroup p K).finite_continuousMonoidHom G

/-- **A finite extension of `ℚ_p` has finitely many extensions of a given degree**: for a finite
extension `K` of `ℚ_p` and `n ≠ 0`, finitely many intermediate fields of `K̄/K` have degree `n` over
`K`. Their fixing subgroups are open subgroups of index `n` of the topologically finitely generated
group `Gal(K̄/K)`, of which there are finitely many, and they determine the fields. -/
lemma finite_setOf_finrank_eq (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] K] [Module.Finite ℚ_[p] K]
    [ValuativeExtension ℚ_[p] K] {n : ℕ} (hn : n ≠ 0) :
    {L : IntermediateField K (AlgebraicClosure K) | Module.finrank K L = n}.Finite := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  have : Finite {U : OpenSubgroup (Field.absoluteGaloisGroup K) // U.toSubgroup.index = n} :=
    isTopologicallyFinitelyGenerated_absoluteGaloisGroup p K
      |>.finite_openSubgroup_index_eq_of_ne_zero n hn
  let g : {L : IntermediateField K (AlgebraicClosure K) // Module.finrank K L = n} →
      {U : OpenSubgroup (Field.absoluteGaloisGroup K) // U.toSubgroup.index = n} := fun L ↦
    have : FiniteDimensional K L.1 := .of_finrank_pos <| (Nat.pos_of_ne_zero hn).trans_eq L.2.symm
    ⟨⟨L.1.fixingSubgroup, L.1.fixingSubgroup_isOpen⟩,
      L.1.finrank_eq_fixingSubgroup_index.symm.trans L.2⟩
  exact Set.finite_coe_iff.mp <| Finite.of_injective g fun L L' h ↦ Subtype.ext <|
    InfiniteGalois.GaloisCoinsertionIntermediateFieldSubgroup.l_injective <|
      congrArg (fun U ↦ U.1.toSubgroup) h

end IsNonarchimedeanLocalField

namespace Padic

/-- **The set `Hom(Γ_{ℚ_p}, G)` is finite** (LMFDB `nf.inertial_height_function`): for a finite
group `G` with a Hausdorff topology, such as the discrete one, there are finitely many continuous
homomorphisms `Gal(ℚ̄_p/ℚ_p) → G`. These form the domain of the auxiliary local heights `H_p` at the
primes `p ∣ #G` that enter the inertial height `NumberField.WeightFunction.inertialHeight`. -/
lemma finite_continuousMonoidHom_absoluteGaloisGroup (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [T2Space G] [Finite G] : Finite (Field.absoluteGaloisGroup ℚ_[p] →ₜ* G) :=
  IsNonarchimedeanLocalField.finite_continuousMonoidHom_absoluteGaloisGroup ℚ_[p] p G

end Padic
