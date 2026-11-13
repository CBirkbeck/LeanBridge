import LeanBridge.ForMathlib.RingTheory.Etale.QuadraticZModPowQuotient
import TauCeti.NumberTheory.LocalField.IntegerRing.Basic
import TauCeti.NumberTheory.LocalField.Padic
import TauCeti.NumberTheory.LocalField.Unramified.Existence

/-!
# The non-split algebra over `ℤ/p^eℤ` from the unramified quadratic extension of `ℚ_p`

Let `p` be a prime, `e ≥ 1` and `Ω` a separably closed extension of `ℚ_p`. The unramified quadratic
extension of `ℚ_p` in `Ω` is Tau Ceti's `TauCeti.unramifiedExtension ℚ_[p] Ω 2`, and its ring of
integers `𝒪` is the degree `2` unramified extension of `ℤ_p`. Then `𝒪/p^e𝒪` is the non-split
algebra `NonsplitCartanAlgebraPow p e` over `ℤ/p^eℤ` (LMFDB `gl2.cartan`). Indeed `𝒪` is a free
`ℤ_p`-module of rank `[L : ℚ_p] = 2` (Tau Ceti's `TauCeti.finrank_integerRing`), and the uniformizer
`p` of `ℚ_p` stays a uniformizer of the unramified extension, so `p 𝒪` is the maximal ideal of `𝒪`,
a prime ideal; this is the case of
`Matrix.GeneralLinearGroup.nonempty_ringEquiv_nonsplitCartanAlgebraPow_of_padicInt`.

As in Tau Ceti, the statements hold for any structure of nonarchimedean local field on the
unramified extension compatible with `ℚ_p`; Tau Ceti's `TauCeti.finiteIntermediateFieldValuativeRel`
provides one.

## Main results

* `Matrix.GeneralLinearGroup.isPrime_span_natCast_integerRing_unramifiedExtension`: `p` generates a
  prime ideal of the ring of integers of the unramified quadratic extension of `ℚ_p`.
* `Matrix.GeneralLinearGroup.nonempty_ringEquiv_nonsplitCartanAlgebraPow_of_unramifiedExtension`
  (LMFDB `gl2.cartan`): `𝒪/p^e𝒪` is the non-split algebra over `ℤ/p^eℤ`.
-/

open Module TauCeti ValuativeRel

namespace Matrix.GeneralLinearGroup

variable {p e : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra ℚ_[p] Ω] [IsSepClosed Ω]
  [ValuativeRel (unramifiedExtension ℚ_[p] Ω 2)] [TopologicalSpace (unramifiedExtension ℚ_[p] Ω 2)]
  [IsNonarchimedeanLocalField (unramifiedExtension ℚ_[p] Ω 2)]
  [ValuativeExtension ℚ_[p] (unramifiedExtension ℚ_[p] Ω 2)]

/-- **`p` is inert in the unramified quadratic extension of `ℤ_p`**: the ideal `p 𝒪` of the ring
of integers `𝒪` of `TauCeti.unramifiedExtension ℚ_[p] Ω 2` is its maximal ideal, as the uniformizer
`p` of `ℚ_p` stays a uniformizer in an unramified extension; so it is prime. -/
lemma isPrime_span_natCast_integerRing_unramifiedExtension :
    (Ideal.span {(p : 𝒪[unramifiedExtension ℚ_[p] Ω 2])}).IsPrime := by
  have : IsUnramified ℚ_[p] (unramifiedExtension ℚ_[p] Ω 2) :=
    isUnramified_unramifiedExtension two_ne_zero
  have h : Irreducible (algebraMap 𝒪[ℚ_[p]] 𝒪[unramifiedExtension ℚ_[p] Ω 2] p) :=
    IsUnramified.irreducible_algebraMap (Padic.irreducible_natCast_self p)
  rw [map_natCast, IsDiscreteValuationRing.irreducible_iff_uniformizer] at h
  rw [← h]
  exact inferInstance

variable [NeZero e]

/-- **`𝒪/p^e𝒪` for the unramified quadratic extension `𝒪` of `ℤ_p`** (LMFDB `gl2.cartan`): for the
ring of integers `𝒪` of the unramified quadratic extension `TauCeti.unramifiedExtension ℚ_[p] Ω 2`
of `ℚ_p`, `𝒪/p^e𝒪` is isomorphic to the non-split algebra `NonsplitCartanAlgebraPow p e`. A ring
has at most one `ℤ/p^eℤ`-algebra structure, so this is an isomorphism of `ℤ/p^eℤ`-algebras. -/
lemma nonempty_ringEquiv_nonsplitCartanAlgebraPow_of_unramifiedExtension :
    Nonempty (𝒪[unramifiedExtension ℚ_[p] Ω 2] ⧸
      Ideal.span {(p : 𝒪[unramifiedExtension ℚ_[p] Ω 2]) ^ e} ≃+*
      NonsplitCartanAlgebraPow p e) := by
  let _ : Algebra ℤ_[p] 𝒪[unramifiedExtension ℚ_[p] Ω 2] :=
    ((algebraMap 𝒪[ℚ_[p]] 𝒪[unramifiedExtension ℚ_[p] Ω 2]).comp
      (Padic.integerRingEquiv p).symm.toRingHom).toAlgebra
  let b : Basis (Fin 2) 𝒪[ℚ_[p]] 𝒪[unramifiedExtension ℚ_[p] Ω 2] :=
    finBasisOfFinrankEq _ _ ((finrank_integerRing ℚ_[p] _).trans
      (finrank_unramifiedExtension two_ne_zero))
  exact nonempty_ringEquiv_nonsplitCartanAlgebraPow_of_padicInt
    (b.mapCoeffs (Padic.integerRingEquiv p) fun c x ↦ by
      rw [Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply])
    isPrime_span_natCast_integerRing_unramifiedExtension

end Matrix.GeneralLinearGroup
