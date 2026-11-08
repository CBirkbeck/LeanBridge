import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Finite
import TauCeti.Algebra.Module.Lattice
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.BassOrder
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.EndomorphismRingNotation

/-!
# The index of an order in an étale `ℚ`-algebra

An étale `ℚ`-algebra `K` is a finite product of number fields, and its maximal order `𝒪_K`, the
integral closure of `ℤ` in `K`, is the product of their rings of integers. It is a finitely
generated abelian group: `K` is reduced and finite-dimensional, hence the product of its quotients
`K ⧸ 𝔪` by its maximal ideals, which are number fields, and `𝒪_K` embeds into the product of their
rings of integers, which are finitely generated.

An order `R` of `K` is a subring whose additive group is free of rank `dim_ℚ K`, that is, finitely
generated and spanning `K` over `ℚ`: a lattice (`Submodule.IsLattice`). It is integral over `ℤ`,
so it lies in `𝒪_K`, which is then a lattice too, and the index `[𝒪_K : R]` of `R` in `𝒪_K` is a
finite positive integer (LMFDB `av.fq.index_of_order`), by Tau Ceti's comparison of nested
lattices.

## Main results

* The instance `Module.Finite ℤ (integralClosure ℤ K)`: the maximal order of an étale `ℚ`-algebra
  is a finitely generated abelian group.
* `Subalgebra.isLattice_integralClosure`: the maximal order of an étale `ℚ`-algebra with an order
  is a lattice.
* `Subalgebra.maximalOrderIndex_pos` (LMFDB `av.fq.index_of_order`): the index `[𝒪_K : R]` of an
  order `R` of an étale `ℚ`-algebra `K` is a finite positive integer.
-/

open Module TauCeti Submodule

open Algebra (FormallyUnramified)

variable {K : Type*} [CommRing K] [Algebra ℚ K] [Algebra.Etale ℚ K]

open Ideal in
instance : Module.Finite ℤ (integralClosure ℤ K) := by
  have hfin : Module.Finite ℚ K := FormallyUnramified.finite_of_free ℚ K
  have hred : IsReduced K := FormallyUnramified.isReduced_of_field ℚ K
  have hart : IsArtinianRing K := isArtinian_of_tower ℚ inferInstance
  have hfac (m : MaximalSpectrum K) : Module.Finite ℤ (integralClosure ℤ (K ⧸ m.asIdeal)) := by
    have hm : m.asIdeal.IsMaximal := m.isMaximal
    let : Field (K ⧸ m.asIdeal) := Quotient.field m.asIdeal
    exact IsIntegralClosure.finite ℤ ℚ (K ⧸ m.asIdeal) (integralClosure ℤ (K ⧸ m.asIdeal))
  let Φ : integralClosure ℤ K →ₗ[ℤ] ∀ m : MaximalSpectrum K, integralClosure ℤ (K ⧸ m.asIdeal) :=
    LinearMap.pi fun m ↦ LinearMap.codRestrict
      (Subalgebra.toSubmodule (integralClosure ℤ (K ⧸ m.asIdeal)))
      ((Quotient.mkₐ ℤ m.asIdeal).toLinearMap ∘ₗ (integralClosure ℤ K).val.toLinearMap)
      fun x ↦ x.2.map (Quotient.mkₐ ℤ m.asIdeal)
  refine .of_injective Φ fun x y hxy ↦ ?_
  refine Subtype.ext <| (IsArtinianRing.equivPi K).injective <| funext fun m ↦ ?_
  exact congrArg Subtype.val (congrFun hxy m)

namespace Subalgebra

variable (R : Subalgebra ℤ K)

/-- **The maximal order of an étale `ℚ`-algebra with an order is a lattice**: the integral closure
`𝒪_K` of `ℤ` in `K` is finitely generated, and it spans `K` over `ℚ` as it contains an order. -/
lemma isLattice_integralClosure [(toSubmodule R).IsLattice ℚ] :
    (toSubmodule (integralClosure ℤ K)).IsLattice ℚ where
  fg := (Finite.iff_fg (N := toSubmodule (integralClosure ℤ K))).mp <|
    .equiv (integralClosure ℤ K).toSubmoduleEquiv.symm
  span_eq_top := eq_top_iff.mpr <| (IsLattice.span_eq_top (M := toSubmodule R)).ge.trans <|
    span_mono <| le_integralClosure_of_fg IsLattice.fg

/-- **The index `[𝒪_K : R]` of an order `R` of an étale `ℚ`-algebra `K` is a finite positive
integer** (LMFDB `av.fq.index_of_order`): an order, a subring whose additive group is finitely
generated and spans `K` over `ℚ`, has finite index in the maximal order `𝒪_K`. -/
lemma maximalOrderIndex_pos [(toSubmodule R).IsLattice ℚ] : 0 < R.maximalOrderIndex := by
  have hO : (toSubmodule (integralClosure ℤ K)).IsLattice ℚ := R.isLattice_integralClosure
  exact Nat.pos_of_ne_zero <| IsLattice.relIndex_ne_zero <| le_integralClosure_of_fg IsLattice.fg

end Subalgebra
