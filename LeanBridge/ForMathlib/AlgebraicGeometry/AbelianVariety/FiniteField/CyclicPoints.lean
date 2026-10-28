import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.Isogenous
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.GroupTheory.Torsion

/-!
# Cyclic isogeny classes of abelian varieties

An isogeny class of abelian varieties over a finite field `𝔽_q` is cyclic if the group of points
`B(𝔽_q)` is cyclic for every abelian variety `B` in it, and non-cyclic at a prime `ℓ` if the
`ℓ`-primary part of `B(𝔽_q)` is not cyclic for some `B` in it. A finite commutative group is cyclic
if its primary components are, so a non-cyclic isogeny class is non-cyclic at some prime.

## Main definitions

* `TauCeti.AlgebraicGeometry.AbelianVariety.RationalPoint`: the group `A(K)` of points of `A`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.IsCyclicIsogenyClass` (LMFDB
  `av.fq.cyclic_group_points`).
* `TauCeti.AlgebraicGeometry.AbelianVariety.IsNonCyclicAt` (LMFDB `av.fq.noncyclic_primes`).

## Main results

* `CommGroup.isCyclic_of_forall_isCyclic_primaryComponent`: a finite commutative group whose
  primary components are cyclic is cyclic.
* `TauCeti.AlgebraicGeometry.AbelianVariety.exists_isNonCyclicAt`: an isogeny class with finite
  groups of points that is not cyclic is non-cyclic at some prime.
-/

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj

namespace CommGroup

variable {G : Type*} [CommGroup G] [Finite G]

/-- A finite commutative group whose primary components are cyclic is cyclic. -/
lemma isCyclic_of_forall_isCyclic_primaryComponent
    (h : ∀ p : ℕ, p.Prime → IsCyclic (primaryComponent G p)) : IsCyclic G :=
  have : IsZGroup G := ⟨fun p hp P ↦
    have : IsCyclic (primaryComponent G p) := h p hp
    Subgroup.isCyclic_of_le fun g hg ↦ (P.isPGroup ⟨g, hg⟩).elim fun k hk ↦
      mem_primaryComponent.mpr ⟨k, congrArg Subtype.val hk⟩⟩
  inferInstance

end CommGroup

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u

variable {K : Type u} [Field K] (A : AbelianVariety K)

/-- The **points** `A(K)` of an abelian variety `A` over `K`: the morphisms `Spec K ⟶ A` over
`Spec K`, the sections of `A`, a commutative group under the group law of `A`. -/
abbrev RationalPoint : Type u :=
  𝟙_ (Over (Spec (.of K))) ⟶ A.toOver

/-- The isogeny class of an abelian variety `A` over `K` is **cyclic** (LMFDB
`av.fq.cyclic_group_points`) if the group of points `B(K)` is cyclic for every abelian variety `B`
isogenous to `A`.

The LMFDB considers finite fields `K = 𝔽_q`, where the groups of points are finite; the definition
makes sense over every field. Being isogenous is symmetric (not formalised here), so the isogeny
class of `A` is the set of `B` with an isogeny `A ⟶ B`. -/
def IsCyclicIsogenyClass : Prop :=
  ∀ B : AbelianVariety K, IsIsogenous A B → IsCyclic B.RationalPoint

/-- The isogeny class of an abelian variety `A` over `K` is **non-cyclic at `ℓ`** (LMFDB
`av.fq.noncyclic_primes`) if the `ℓ`-primary component of the group of points `B(K)` is not cyclic
for some abelian variety `B` isogenous to `A`.

The LMFDB considers finite fields `K = 𝔽_q` and primes `ℓ`; the definition makes sense over every
field and for every natural number `ℓ`. Being isogenous is symmetric (not formalised here), so the
isogeny class of `A` is the set of `B` with an isogeny `A ⟶ B`. -/
def IsNonCyclicAt (ℓ : ℕ) : Prop :=
  ∃ B : AbelianVariety K, IsIsogenous A B ∧ ¬IsCyclic (CommGroup.primaryComponent B.RationalPoint ℓ)

variable {A}

/-- An isogeny class that is not cyclic is non-cyclic at some prime `ℓ`, provided the groups of
points in it are finite, as they are over a finite field (not formalised here). -/
lemma exists_isNonCyclicAt (hfin : ∀ B : AbelianVariety K, IsIsogenous A B → Finite B.RationalPoint)
    (hA : ¬A.IsCyclicIsogenyClass) : ∃ ℓ : ℕ, ℓ.Prime ∧ A.IsNonCyclicAt ℓ := by
  by_contra! h
  refine hA fun B hB ↦ ?_
  have : Finite B.RationalPoint := hfin B hB
  exact CommGroup.isCyclic_of_forall_isCyclic_primaryComponent fun ℓ hℓ ↦ by_contra fun hc ↦
    h ℓ hℓ ⟨B, hB, hc⟩

end TauCeti.AlgebraicGeometry.AbelianVariety
