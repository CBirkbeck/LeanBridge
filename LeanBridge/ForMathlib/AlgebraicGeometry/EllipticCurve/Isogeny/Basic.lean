import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Kernel
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange

/-!
# Isogenies of elliptic curves

LMFDB isogeny vocabulary (`ec.isogeny`) on top of Tau Ceti's isogenies `TauCeti.Isogeny`. A Tau
Ceti isogeny `W₁ → W₂` of Weierstrass curves over a field `K` is a nonconstant morphism defined
over `K` sending the point at infinity of `W₁` to that of `W₂`, given by its pullback of functions.
Its degree is `TauCeti.Isogeny.degree`, its dual `TauCeti.Isogeny.dual`, and isogenies compose by
`TauCeti.Isogeny.comp`.

## Main definitions

* `WeierstrassCurve.IsIsogenous` (LMFDB `ec.isogeny`): there is an isogeny between two curves.
* `WeierstrassCurve.isogenySetoid` (LMFDB `ec.isogeny`): isogeny as an equivalence relation on the
  elliptic curves over `K`, whose classes are the isogeny classes.
* `TauCeti.Isogeny.geometricKer` (LMFDB `ec.isogeny`): the kernel of an isogeny, as a group of
  points over an algebraic closure of `K`.
* `TauCeti.Isogeny.IsCyclic` (LMFDB `ec.isogeny`): an isogeny with cyclic kernel.

## Main results

* `WeierstrassCurve.IsIsogenous.symm`: isogeny is symmetric on elliptic curves, through the dual
  isogeny.
* `TauCeti.Isogeny.isCyclic_comp_iff_of_comp_eq_id` and
  `TauCeti.Isogeny.comp_isCyclic_iff_of_comp_eq_id`: composing with an isomorphism after or before
  an isogeny does not change whether it is cyclic.
* `TauCeti.Isogeny.card_geometricKer`: over a field of characteristic zero, where every isogeny is
  separable, the kernel of an isogeny has as many points as its degree.
* `TauCeti.Isogeny.isCyclic_of_prime_degree`: over a field of characteristic zero, an isogeny of
  prime degree is cyclic.
-/

open TauCeti
open scoped Classical

namespace WeierstrassCurve

variable {K : Type*} [Field K] {W W₁ W₂ W₃ : WeierstrassCurve K} (C : VariableChange K)

variable (W₁ W₂) in
/-- Two Weierstrass curves `W₁` and `W₂` over a field `K` are **isogenous** (LMFDB `ec.isogeny`)
if there is an isogeny `W₁ → W₂` over `K`: a nonconstant morphism defined over `K` sending the
point at infinity of `W₁` to that of `W₂` (`TauCeti.Isogeny`). -/
def IsIsogenous : Prop :=
  Nonempty (Isogeny W₁.toAffine W₂.toAffine)

variable (W) in
@[refl]
lemma IsIsogenous.refl : W.IsIsogenous W :=
  ⟨Isogeny.id W.toAffine⟩

@[trans]
lemma IsIsogenous.trans (h₁₂ : W₁.IsIsogenous W₂) (h₂₃ : W₂.IsIsogenous W₃) : W₁.IsIsogenous W₃ :=
  h₁₂.elim fun φ ↦ h₂₃.elim fun ψ ↦ ⟨ψ.comp φ⟩

variable (W) in
lemma isIsogenous_smul_self : W.IsIsogenous (C • W) :=
  ⟨Isogeny.variableChangeIsogeny C rfl⟩

variable (W) in
lemma smul_isIsogenous_self : (C • W).IsIsogenous W :=
  ⟨Isogeny.variableChangeIsogeny C⁻¹ (inv_smul_smul C W)⟩

lemma smul_isIsogenous_iff : (C • W₁).IsIsogenous W₂ ↔ W₁.IsIsogenous W₂ :=
  ⟨(isIsogenous_smul_self W₁ C).trans, (smul_isIsogenous_self W₁ C).trans⟩

lemma isIsogenous_smul_iff : W₁.IsIsogenous (C • W₂) ↔ W₁.IsIsogenous W₂ :=
  ⟨fun h ↦ h.trans (smul_isIsogenous_self W₂ C), fun h ↦ h.trans (isIsogenous_smul_self W₂ C)⟩

variable [W₁.IsElliptic] [W₂.IsElliptic]

/-- **Isogeny is symmetric** on elliptic curves: the dual of an isogeny `W₁ → W₂` is an isogeny
`W₂ → W₁`. -/
lemma IsIsogenous.symm (h : W₁.IsIsogenous W₂) : W₂.IsIsogenous W₁ :=
  h.map Isogeny.dual

lemma isIsogenous_comm : W₁.IsIsogenous W₂ ↔ W₂.IsIsogenous W₁ :=
  ⟨IsIsogenous.symm, IsIsogenous.symm⟩

variable (K) in
/-- **Isogeny** (LMFDB `ec.isogeny`) as an equivalence relation on the elliptic curves over `K`.
Its equivalence classes are the isogeny classes. -/
def isogenySetoid : Setoid {W : WeierstrassCurve K // W.IsElliptic} where
  r W₁ W₂ := W₁.1.IsIsogenous W₂.1
  iseqv := ⟨fun W ↦ .refl W.1, fun {W₁ W₂} h ↦ by
    have : W₁.1.IsElliptic := W₁.2
    have : W₂.1.IsElliptic := W₂.2
    exact h.symm, IsIsogenous.trans⟩

lemma isogenySetoid_r {V₁ V₂ : {W : WeierstrassCurve K // W.IsElliptic}} :
    isogenySetoid K V₁ V₂ ↔ V₁.1.IsIsogenous V₂.1 :=
  Iff.rfl

end WeierstrassCurve

namespace TauCeti.Isogeny

variable {K : Type*} [Field K] {W₀ W₁ W₂ W₃ : WeierstrassCurve.Affine K} [W₀.IsElliptic]
  [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic] (φ : Isogeny W₁ W₂) {ψ : Isogeny W₂ W₃}
  {ψ' : Isogeny W₃ W₂} (hψ : ψ'.comp ψ = id W₂)

/-- The **kernel** (LMFDB `ec.isogeny`) of an isogeny `φ : W₁ → W₂` over `K`: the subgroup of the
points of `W₁` over an algebraic closure `K̄` of `K` that `φ` sends to the point at infinity of
`W₂`. It is finite, and over a field of characteristic zero it has `deg φ` points
(`card_geometricKer`).

This is the kernel of the group homomorphism `W₁(K̄) → W₂(K̄)` induced by `φ`, as in the LMFDB.
Tau Ceti's `TauCeti.Isogeny.ker` is a different subgroup, of the points defined over `K` only. In
characteristic `p`, the group of points does not see the inseparable part of `φ`: it has as many
points as the separable degree of `φ`, not `deg φ`. -/
noncomputable def geometricKer : AddSubgroup (W₁.map (algebraMap K (AlgebraicClosure K))).Point :=
  (Hom.ofIsogeny (φ.map (algebraMap K (AlgebraicClosure K)))).pointMapHom.ker

/-- An isogeny `φ` over `K` is **cyclic** (LMFDB `ec.isogeny`) if its kernel, the group of points
over an algebraic closure of `K` that `φ` sends to the point at infinity (`geometricKer`), is
cyclic. -/
def IsCyclic : Prop :=
  IsAddCyclic φ.geometricKer

instance : Finite φ.geometricKer :=
  (Hom.finite_setOf_pointMap_eq (Hom.ofIsogeny_ne_zero _) 0).to_subtype

variable (W₁) in
@[simp]
lemma geometricKer_id : (id W₁).geometricKer = ⊥ := by
  ext P
  simp [geometricKer, ← Hom.id_def]

variable (W₁) in
lemma isCyclic_id : (id W₁).IsCyclic := by
  rw [IsCyclic, geometricKer_id]
  exact Bot.isAddCyclic

include hψ in
lemma leftInverse_pointMap_map : Function.LeftInverse
    (Hom.ofIsogeny (ψ'.map (algebraMap K (AlgebraicClosure K)))).pointMap
    (Hom.ofIsogeny (ψ.map (algebraMap K (AlgebraicClosure K)))).pointMap := fun P ↦ by
  rw [← Hom.comp_pointMap, Hom.ofIsogeny_comp_ofIsogeny, ← comp_map, hψ, id_map, ← Hom.id_def,
    Hom.id_pointMap]

include hψ in
lemma geometricKer_comp_of_comp_eq_id : (ψ.comp φ).geometricKer = φ.geometricKer := by
  ext P
  simp only [geometricKer, AddMonoidHom.mem_ker, Hom.pointMapHom_apply, comp_map,
    ← Hom.ofIsogeny_comp_ofIsogeny, Hom.comp_pointMap]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, Hom.pointMap_zero]⟩
  rw [← leftInverse_pointMap_map hψ ((Hom.ofIsogeny _).pointMap P), h, Hom.pointMap_zero]

include hψ in
/-- **Composing with an isomorphism after an isogeny keeps it cyclic**, the kernel being the
same. -/
lemma isCyclic_comp_iff_of_comp_eq_id : (ψ.comp φ).IsCyclic ↔ φ.IsCyclic := by
  rw [IsCyclic, IsCyclic, geometricKer_comp_of_comp_eq_id φ hψ]

/-- **Composing with an isomorphism before an isogeny keeps it cyclic**, the isomorphism carrying
one kernel onto the other. -/
lemma comp_isCyclic_iff_of_comp_eq_id {α : Isogeny W₀ W₁} {α' : Isogeny W₁ W₀}
    (hα : α'.comp α = id W₀) (hα' : α.comp α' = id W₁) : (φ.comp α).IsCyclic ↔ φ.IsCyclic := by
  let e : (W₀.map (algebraMap K (AlgebraicClosure K))).Point ≃+
      (W₁.map (algebraMap K (AlgebraicClosure K))).Point :=
    { toFun := (Hom.ofIsogeny (α.map (algebraMap K (AlgebraicClosure K)))).pointMap
      invFun := (Hom.ofIsogeny (α'.map (algebraMap K (AlgebraicClosure K)))).pointMap
      left_inv := leftInverse_pointMap_map hα
      right_inv := leftInverse_pointMap_map hα'
      map_add' := Hom.pointMap_add _ }
  have h : φ.geometricKer = (φ.comp α).geometricKer.map e.toAddMonoidHom := by
    ext Q
    rw [AddSubgroup.mem_map_equiv]
    simp [geometricKer, ← Hom.ofIsogeny_comp_ofIsogeny, e, leftInverse_pointMap_map hα' Q]
  rw [IsCyclic, IsCyclic, h]
  exact (e.addSubgroupMap _).isAddCyclic

variable [CharZero K]

/-- **The kernel of an isogeny over a field of characteristic zero has `deg φ` points**: every
isogeny is separable in characteristic zero, and a separable isogeny over an algebraically closed
field has `deg φ` points in its kernel (Silverman III.4.10). -/
lemma card_geometricKer : Nat.card φ.geometricKer = φ.degree := by
  have : IsIntegrallyClosed (W₂.map (algebraMap K (AlgebraicClosure K))).CoordinateRing :=
    (W₂.map (algebraMap K (AlgebraicClosure K))).isIntegrallyClosed_coordinateRing
  have h : φ.geometricKer = (φ.map (algebraMap K (AlgebraicClosure K))).toPointHom.ker := by
    ext P
    simp [geometricKer, Hom.pointMap_ofIsogeny_eq_toPointHom]
  rw [h, card_ker_toPointHom_eq_degree, degree_map]

/-- **An isogeny of prime degree is cyclic** over a field of characteristic zero: its kernel has
prime order. -/
lemma isCyclic_of_prime_degree (hφ : φ.degree.Prime) : φ.IsCyclic :=
  have : Fact φ.degree.Prime := ⟨hφ⟩
  isAddCyclic_of_prime_card φ.card_geometricKer

end TauCeti.Isogeny
