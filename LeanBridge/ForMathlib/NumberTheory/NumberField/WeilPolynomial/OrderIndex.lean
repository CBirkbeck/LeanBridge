import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Finite
import TauCeti.Algebra.Module.Lattice
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.BassOrder
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.EndomorphismRingNotation
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.MultiplierRing

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

For a subring `R` of a commutative `ℚ`-algebra `K` whose additive group is a lattice, `K` is the
total ring of fractions of `R` and `R` is Noetherian. The instances `Module.Finite ℤ R`,
`IsFractionRing R K` and `IsNoetherianRing R` record these facts. Instance search finds them when
the `ℤ`-algebra structure of `K` is `Ring.toIntAlgebra`, as for a variable `K`; for a concrete `K`
with another one, such as `Fin n → ℚ` or an `AdjoinRoot`, they apply by name.

## Main results

* The instances `Module.Finite ℤ R`, `IsFractionRing R K` and `IsNoetherianRing R`, for a subring
  `R` of a commutative `ℚ`-algebra `K` whose additive group is a lattice.
* The instance `Module.Finite ℤ (integralClosure ℤ K)`: the maximal order of an étale `ℚ`-algebra
  is a finitely generated abelian group.
* `Subalgebra.isLattice_integralClosure`: the maximal order of an étale `ℚ`-algebra with an order
  is a lattice.
* `Subalgebra.maximalOrderIndex_pos` (LMFDB `av.fq.index_of_order`): the index `[𝒪_K : R]` of an
  order `R` of an étale `ℚ`-algebra `K` is a finite positive integer.
-/

open Module TauCeti Submodule

open Algebra (FormallyUnramified)

open scoped nonZeroDivisors

variable {K : Type*} [CommRing K] [Algebra ℚ K]

namespace Submodule

lemma isArtinianRing_of_isLattice (M : Submodule ℤ K) [M.IsLattice ℚ] : IsArtinianRing K := by
  rcases IsLattice.fg (M := M) with ⟨T, hT⟩
  have : Module.Finite ℚ K :=
    ⟨⟨T, by rw [← span_span_of_tower ℤ, hT]; exact IsLattice.span_eq_top⟩⟩
  exact isArtinian_of_tower ℚ inferInstance

lemma isUnit_of_mem_nonZeroDivisors_of_isLattice (M : Submodule ℤ K) [M.IsLattice ℚ] {x : K}
    (hx : x ∈ K⁰) : IsUnit x :=
  have : IsArtinianRing K := isArtinianRing_of_isLattice M
  IsArtinianRing.isUnit_of_mem_nonZeroDivisors hx

end Submodule

namespace Subalgebra

variable (R : Subalgebra ℤ K)

lemma natCast_mem_nonZeroDivisors {n : ℕ} (hn : n ≠ 0) : (n : R) ∈ R⁰ :=
  mem_nonZeroDivisors_iff_right.mpr fun r hr ↦ Subtype.ext <|
    (isUnit_natCast_of_ne_zero hn).mul_left_eq_zero.mp (by simpa using congrArg Subtype.val hr)

variable [(toSubmodule R).IsLattice ℚ]

instance : Module.Finite ℤ R :=
  .equiv R.toSubmoduleEquiv

instance : IsFractionRing R K := by
  have hR : span ℚ (R : Set K) = ⊤ := IsLattice.span_eq_top (M := toSubmodule R)
  have : IsArtinianRing K := isArtinianRing_of_isLattice (toSubmodule R)
  refine (isLocalization_iff _ _).mpr
    ⟨fun y ↦ ?_, fun z ↦ ?_, fun {x y} h ↦ ⟨1, by rw [Subtype.ext h]⟩⟩
  · refine IsArtinianRing.isUnit_of_mem_nonZeroDivisors <|
      mem_nonZeroDivisors_iff_right.mpr fun k hk ↦ ?_
    rcases R.exists_natCast_mul_mem_of_span_eq_top hR k with ⟨n, hn, hnk⟩
    have h0 : (⟨n * k, hnk⟩ : R) * y = 0 :=
      Subtype.ext <| by simpa [mul_assoc] using congrArg ((n : K) * ·) hk
    exact (isUnit_natCast_of_ne_zero hn).mul_right_eq_zero.mp <|
      congrArg Subtype.val (mem_nonZeroDivisors_iff_right.mp y.2 _ h0)
  · rcases R.exists_natCast_mul_mem_of_span_eq_top hR z with ⟨n, hn, hnz⟩
    exact ⟨⟨⟨n * z, hnz⟩, ⟨n, R.natCast_mem_nonZeroDivisors hn⟩⟩, by simp [mul_comm]⟩

instance : IsNoetherianRing R :=
  isNoetherian_of_tower ℤ inferInstance

end Subalgebra

variable [Algebra.Etale ℚ K]

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
