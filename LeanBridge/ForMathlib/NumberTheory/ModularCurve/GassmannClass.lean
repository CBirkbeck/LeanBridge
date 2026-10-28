import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Level
import Mathlib.Algebra.Group.Conj

/-!
# Gassmann classes of open subgroups of `GL₂(ℤ̂)`

Two subgroups `H₁` and `H₂` of a finite group `G` are Gassmann equivalent if `|C ∩ H₁| = |C ∩ H₂|`
for every conjugacy class `C` of `G`. Two open subgroups of `GL₂(ℤ̂)` are Gassmann equivalent if
their reductions modulo `N` are Gassmann equivalent in `GL₂(ℤ/Nℤ)`, where `N` is the least common
multiple of their levels: both are then inverse images of their reductions modulo `N`, so this is
Gassmann equivalence in the finite quotient `GL₂(ℤ/Nℤ)` of `GL₂(ℤ̂)` through which they both
factor. As in `LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Level`, `GL₂(ℤ̂)` is the product
`∏_ℓ GL₂(ℤ_ℓ)` and `GL₂(ℤ/Nℤ)` the product `∏_ℓ GL₂(ℤ / ℓ ^ v_ℓ(N) ℤ)`.

That Gassmann equivalence does not depend on the choice of the multiple `N` of the levels, and
that Gassmann equivalent open subgroups have the same level, index and genus, and modular curves
with isogenous Jacobians (Prasad–Rajan), are not formalised.

## Main definitions

* `Subgroup.IsGassmannEquivalent` (LMFDB `group.gassmann_equivalence`): Gassmann equivalence of
  subgroups.
* `Matrix.GeneralLinearGroup.IsAdelicGassmannEquivalent`: Gassmann equivalence of open subgroups of
  `GL₂(ℤ̂)`.
* `Matrix.GeneralLinearGroup.gassmannClass` (LMFDB `modcurve.gassmann_class`): the Gassmann class.

## Main results

* `Subgroup.isGassmannEquivalent_equivalence`: Gassmann equivalence is an equivalence relation.
* `Matrix.GeneralLinearGroup.mem_gassmannClass_self`: an open subgroup is in its Gassmann class.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- Two subgroups `H₁` and `H₂` of a group `G` are **Gassmann equivalent** (LMFDB
`group.gassmann_equivalence`) if `|C ∩ H₁| = |C ∩ H₂|` for every conjugacy class `C` of `G`. The
LMFDB applies this to finite groups `G`; for infinite `G` the cardinalities are `Nat.card`, which is
`0` on infinite sets. -/
def IsGassmannEquivalent (H₁ H₂ : Subgroup G) : Prop :=
  ∀ C : ConjClasses G, Nat.card ↥(C.carrier ∩ H₁) = Nat.card ↥(C.carrier ∩ H₂)

/-- **Gassmann equivalence is an equivalence relation.** -/
lemma isGassmannEquivalent_equivalence : Equivalence (IsGassmannEquivalent (G := G)) :=
  ⟨fun _ _ ↦ rfl, fun h C ↦ (h C).symm, fun h h' C ↦ (h C).trans (h' C)⟩

end Subgroup

namespace Matrix.GeneralLinearGroup

variable (H H' : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]))

/-- Two open subgroups `H` and `H'` of `GL₂(ℤ̂)` are **Gassmann equivalent** if their reductions
modulo the least common multiple `N` of their levels are Gassmann equivalent subgroups of the
finite group `GL₂(ℤ/Nℤ)`. -/
def IsAdelicGassmannEquivalent : Prop :=
  (H.map (adelicReduction ((adelicLevel ⊤ H).lcm (adelicLevel ⊤ H')))).IsGassmannEquivalent
    (H'.map (adelicReduction ((adelicLevel ⊤ H).lcm (adelicLevel ⊤ H'))))

/-- The **Gassmann class** (LMFDB `modcurve.gassmann_class`) of an open subgroup `H` of `GL₂(ℤ̂)`:
the set of open subgroups of `GL₂(ℤ̂)` that are Gassmann equivalent to `H`. -/
def gassmannClass : Set (Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ])) :=
  {H' | IsOpen (H' : Set (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ])) ∧ IsAdelicGassmannEquivalent H H'}

/-- **An open subgroup of `GL₂(ℤ̂)` is in its Gassmann class.** -/
lemma mem_gassmannClass_self (hH : IsOpen (H : Set (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]))) :
    H ∈ gassmannClass H :=
  ⟨hH, fun _ ↦ rfl⟩

end Matrix.GeneralLinearGroup
