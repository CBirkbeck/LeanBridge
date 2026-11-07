import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import TauCeti.NumberTheory.NumberField.Global.Orders.Basic
import TauCeti.NumberTheory.NumberField.Index.Basic

/-!
# Monomial orders

An order of a number field `K` (LMFDB `nf.order`) is Tau Ceti's
`TauCeti.GlobalNumberFields.NumberFieldOrder K`. A monomial order (LMFDB `nf.monomial_order`) is
an order of the form `ℤ[α]` for an element `α ∈ K`. Such an `α` is necessarily an algebraic
integer, since an order consists of algebraic integers, and a primitive element of `K`, since an
order spans `K` over `ℚ`. Conversely, `ℤ[θ]` is an order for every integral primitive element `θ`
of `K` (Tau Ceti's `TauCeti.NumberField.IntegralPrimitiveElement`), so the monomial orders are
exactly these.

## Main definitions

* `TauCeti.GlobalNumberFields.NumberFieldOrder.IsMonomial` (LMFDB `nf.monomial_order`).
* `TauCeti.GlobalNumberFields.NumberFieldOrder.ofIntegralPrimitiveElement`: the order `ℤ[θ]` of
  an integral primitive element `θ`.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.isIntegral_of_toSubalgebra_eq_adjoin`
  (LMFDB `nf.monomial_order`): if an order is `ℤ[α]`, then `α` is an algebraic integer.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.primitive_element_of_toSubalgebra_eq_adjoin`
  (LMFDB `nf.monomial_order`): if an order is `ℤ[α]`, then `α` is a primitive element of `K`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.isMonomial_iff`: the monomial orders are the orders
  `ℤ[θ]` of the integral primitive elements `θ`.
-/

open scoped IntermediateField

namespace TauCeti.GlobalNumberFields.NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K} {α : K}
  (θ : NumberField.IntegralPrimitiveElement K)

variable (O) in
/-- An order `O` of a number field `K` is **monomial** (LMFDB `nf.monomial_order`) if it is
`ℤ[α]` for some `α ∈ K`. Such an `α` is an algebraic integer
(`isIntegral_of_toSubalgebra_eq_adjoin`) and a primitive element of `K`
(`primitive_element_of_toSubalgebra_eq_adjoin`). -/
def IsMonomial : Prop :=
  ∃ α : K, O.toSubalgebra = Algebra.adjoin ℤ {α}

/-- **The generator of a monomial order is an algebraic integer** (LMFDB `nf.monomial_order`). -/
lemma isIntegral_of_toSubalgebra_eq_adjoin (hα : O.toSubalgebra = Algebra.adjoin ℤ {α}) :
    IsIntegral ℤ α :=
  O.isIntegral ⟨α, hα ▸ Algebra.self_mem_adjoin_singleton ℤ α⟩

lemma adjoin_eq_top_of_toSubalgebra_eq_adjoin (hα : O.toSubalgebra = Algebra.adjoin ℤ {α}) :
    Algebra.adjoin ℚ {α} = ⊤ := by
  refine Subalgebra.toSubmodule_injective <| eq_top_iff.mpr ?_
  rw [← O.spans, Submodule.span_le, hα]
  exact Algebra.adjoin_le (S := (Algebra.adjoin ℚ {α}).restrictScalars ℤ) <|
    Set.singleton_subset_iff.mpr <| Algebra.self_mem_adjoin_singleton ℚ α

/-- **The generator of a monomial order is a primitive element** (LMFDB `nf.monomial_order`): if
an order of `K` is `ℤ[α]`, then `ℚ(α) = K`. -/
lemma primitive_element_of_toSubalgebra_eq_adjoin (hα : O.toSubalgebra = Algebra.adjoin ℤ {α}) :
    ℚ⟮α⟯ = ⊤ :=
  (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic <| .of_finite ℚ α).mpr <|
    adjoin_eq_top_of_toSubalgebra_eq_adjoin hα

/-- The order `ℤ[θ]` of an integral primitive element `θ` of `K`: it is finite over `ℤ` because `θ`
is integral, and it spans `K` over `ℚ` because `ℚ[θ] = K`. -/
noncomputable def ofIntegralPrimitiveElement : NumberFieldOrder K where
  toSubalgebra := Algebra.adjoin ℤ {(θ.1 : K)}
  finite := .of_fg θ.1.isIntegral_coe.fg_adjoin_singleton
  spans := by
    rw [← Subalgebra.coe_toSubmodule, Algebra.adjoin_eq_span, Submodule.span_span_of_tower,
      ← Algebra.adjoin_eq_span, θ.2, Algebra.top_toSubmodule]

@[simp]
lemma ofIntegralPrimitiveElement_toSubalgebra :
    (ofIntegralPrimitiveElement θ).toSubalgebra = Algebra.adjoin ℤ {(θ.1 : K)} :=
  rfl

lemma isMonomial_ofIntegralPrimitiveElement : (ofIntegralPrimitiveElement θ).IsMonomial :=
  ⟨θ.1, rfl⟩

/-- **The monomial orders are the orders `ℤ[θ]` of the integral primitive elements `θ`.** -/
lemma isMonomial_iff : O.IsMonomial ↔ ∃ θ, O = ofIntegralPrimitiveElement θ := by
  refine ⟨fun ⟨α, hα⟩ ↦ ⟨⟨⟨α, isIntegral_of_toSubalgebra_eq_adjoin hα⟩,
    adjoin_eq_top_of_toSubalgebra_eq_adjoin hα⟩, NumberFieldOrder.ext hα⟩, ?_⟩
  rintro ⟨θ, rfl⟩
  exact isMonomial_ofIntegralPrimitiveElement θ

end TauCeti.GlobalNumberFields.NumberFieldOrder
