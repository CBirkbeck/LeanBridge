import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Trace.Defs
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.LeftMulMatrix

/-!
# Cartan subgroups of `GL₂`

Let `R` be a commutative ring and `A` a free `R`-algebra of rank `2` with a basis `b`.
Multiplication by a unit of `A` is an `R`-linear automorphism of `A`; reading it in the basis `b`
embeds `Aˣ` in `GL₂(R)` (`TauCeti.unitsLeftMulMatrix`), and when `A` is étale its image is a
**Cartan subgroup** of `GL₂(R)`. The canonical involution `x ↦ Tr(x) - x` of `A` is an `R`-algebra
automorphism; with the Cartan subgroup it generates the **extended Cartan subgroup**, which
normalises the Cartan subgroup and contains it with index `2` once the involution is not the
identity. Over a field, a Cartan subgroup is **split** if it is diagonalizable, that is, conjugate
to a group of diagonal matrices, and **non-split** otherwise.

## Main definitions

* `Matrix.GeneralLinearGroup.cartanSubgroup` (LMFDB `gl2.cartan`): the image of `Aˣ` in `GL₂(R)`.
* `Matrix.GeneralLinearGroup.canonicalInvolution`: the map `x ↦ Tr(x) - x`, with
  `Matrix.GeneralLinearGroup.canonicalInvolutionAlgEquiv`, the same map as an algebra automorphism,
  and `Matrix.GeneralLinearGroup.canonicalInvolutionGL`, its matrix in the basis.
* `Matrix.GeneralLinearGroup.extendedCartanSubgroup` (LMFDB `gl2.cartan`).
* `Matrix.GeneralLinearGroup.IsCartanSubgroup` and
  `Matrix.GeneralLinearGroup.IsExtendedCartanSubgroup` (LMFDB `gl2.cartan`): the subgroups of these
  forms for some free rank-2 étale algebra with a basis.
* `Matrix.GeneralLinearGroup.IsSplitCartanSubgroup` (LMFDB `gl2.split_cartan`) and
  `Matrix.GeneralLinearGroup.IsNonsplitCartanSubgroup` (LMFDB `gl2.nonsplit_cartan`).

## Main results

* `Matrix.GeneralLinearGroup.canonicalInvolution_mul`: the canonical involution is
  multiplicative.
* `Matrix.GeneralLinearGroup.extendedCartanSubgroup_le_normalizer`: the extended Cartan subgroup
  normalises the Cartan subgroup.
* `Matrix.GeneralLinearGroup.canonicalInvolutionGL_notMem_cartanSubgroup`: the canonical
  involution is not in the Cartan subgroup unless it is the identity.
* `Matrix.GeneralLinearGroup.relIndex_cartanSubgroup_extendedCartanSubgroup`: the Cartan subgroup
  has index `2` in the extended Cartan subgroup when the canonical involution is not in it.
-/

open Matrix Module TauCeti

namespace Matrix.GeneralLinearGroup

universe u v

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] (b : Basis (Fin 2) R A)
  {g : GL (Fin 2) R} (x : A)

/-- The **Cartan subgroup** of `GL₂(R)` attached to a free rank-2 `R`-algebra `A` with basis `b`
(LMFDB `gl2.cartan`): the image of the injective homomorphism `Aˣ → GL₂(R)` sending a unit to the
matrix of multiplication by it in the basis `b`. The LMFDB asks `A` to be étale, which this
construction does not need; `IsCartanSubgroup` imposes it. -/
noncomputable def cartanSubgroup : Subgroup (GL (Fin 2) R) :=
  (unitsLeftMulMatrix b).range

lemma mem_cartanSubgroup : g ∈ cartanSubgroup b ↔ ∃ u : Aˣ, unitsLeftMulMatrix b u = g :=
  MonoidHom.mem_range

variable (R A) in
/-- The **canonical involution** `x ↦ Tr(x) - x` of an `R`-algebra `A`, where `Tr` is the algebra
trace. On a free algebra of rank `2` it is an involutive algebra automorphism
(`canonicalInvolutionAlgEquiv`), the conjugation of `A`. -/
noncomputable def canonicalInvolution : A →ₗ[R] A :=
  (Algebra.trace R A).smulRight 1 - LinearMap.id

lemma canonicalInvolution_apply :
    canonicalInvolution R A x = algebraMap R A (Algebra.trace R A x) - x := by
  rw [canonicalInvolution, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.id_apply,
    Algebra.algebraMap_eq_smul_one]

include b in
lemma trace_one_eq_two : Algebra.trace R A 1 = 2 := by
  rw [Algebra.trace_eq_matrix_trace b, map_one, Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat]

include b in
lemma trace_algebraMap_eq_two_mul (t : R) : Algebra.trace R A (algebraMap R A t) = 2 * t := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, trace_one_eq_two b, smul_eq_mul, mul_comm]

include b in
lemma canonicalInvolution_canonicalInvolution :
    canonicalInvolution R A (canonicalInvolution R A x) = x := by
  rw [canonicalInvolution_apply, canonicalInvolution_apply x, map_sub,
    trace_algebraMap_eq_two_mul b, two_mul, add_sub_cancel_right, sub_sub_cancel]

include b in
lemma canonicalInvolution_one : canonicalInvolution R A 1 = 1 := by
  rw [canonicalInvolution_apply, trace_one_eq_two b, map_ofNat]
  norm_num

lemma algebraMap_trace_sub_eq_adjugate (X : Matrix (Fin 2) (Fin 2) R) :
    algebraMap R _ X.trace - X = X.adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjugate_fin_two, trace_fin_two, algebraMap_matrix_apply]

include b in
/-- **The canonical involution is multiplicative**: for a free rank-2 algebra this is the identity
`adj(X Y) = adj(Y) adj(X)` for the commuting `2 × 2` matrices of multiplication, the adjugate of
such a matrix `X` being `Tr(X) - X`. -/
lemma canonicalInvolution_mul (y : A) :
    canonicalInvolution R A (x * y) = canonicalInvolution R A x * canonicalInvolution R A y := by
  apply Algebra.leftMulMatrix_injective b
  simp only [canonicalInvolution_apply, map_sub, map_mul, AlgHom.commutes,
    Algebra.trace_eq_matrix_trace b, algebraMap_trace_sub_eq_adjugate]
  rw [← adjugate_mul_distrib, ((Commute.all x y).map (Algebra.leftMulMatrix b)).eq]

/-- The canonical involution of a free rank-2 `R`-algebra, as an `R`-algebra automorphism. -/
noncomputable def canonicalInvolutionAlgEquiv : A ≃ₐ[R] A :=
  AlgEquiv.ofLinearEquiv
    (LinearEquiv.ofInvolutive (canonicalInvolution R A) (canonicalInvolution_canonicalInvolution b))
    (canonicalInvolution_one b) (canonicalInvolution_mul b)

@[simp]
lemma canonicalInvolutionAlgEquiv_apply :
    canonicalInvolutionAlgEquiv b x = canonicalInvolution R A x :=
  rfl

include b in
lemma canonicalInvolution_mul_self : canonicalInvolution R A * canonicalInvolution R A = 1 :=
  LinearMap.ext (canonicalInvolution_canonicalInvolution b)

/-- The matrix in the basis `b` of the canonical involution of `A`, an element of `GL₂(R)` that is
its own inverse. -/
noncomputable def canonicalInvolutionGL : GL (Fin 2) R :=
  haveI h : LinearMap.toMatrix b b (canonicalInvolution R A) *
      LinearMap.toMatrix b b (canonicalInvolution R A) = 1 := by
    rw [← LinearMap.toMatrix_mul, canonicalInvolution_mul_self b, LinearMap.toMatrix_one]
  ⟨_, _, h, h⟩

lemma coe_canonicalInvolutionGL : (canonicalInvolutionGL b : Matrix (Fin 2) (Fin 2) R) =
    LinearMap.toMatrix b b (canonicalInvolution R A) :=
  rfl

lemma inv_canonicalInvolutionGL : (canonicalInvolutionGL b)⁻¹ = canonicalInvolutionGL b :=
  Units.ext rfl

lemma canonicalInvolutionGL_mul_self : canonicalInvolutionGL b * canonicalInvolutionGL b = 1 :=
  Units.ext (canonicalInvolutionGL b).val_inv

lemma canonicalInvolutionGL_mul_self_mul :
    canonicalInvolutionGL b * (canonicalInvolutionGL b * g) = g := by
  rw [← mul_assoc, canonicalInvolutionGL_mul_self, one_mul]

lemma canonicalInvolutionGL_mul_unitsLeftMulMatrix_mul (u : Aˣ) : canonicalInvolutionGL b *
    unitsLeftMulMatrix b u * canonicalInvolutionGL b =
    unitsLeftMulMatrix b (Units.map (canonicalInvolutionAlgEquiv b : A →* A) u) := by
  have h : canonicalInvolution R A * Algebra.lmul R A (u : A) * canonicalInvolution R A =
      Algebra.lmul R A (canonicalInvolution R A u) := by
    refine LinearMap.ext fun z ↦ ?_
    simp only [End.mul_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply',
      canonicalInvolution_mul b, canonicalInvolution_canonicalInvolution b]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_canonicalInvolutionGL, coe_unitsLeftMulMatrix,
    coe_unitsLeftMulMatrix, Algebra.leftMulMatrix_apply, Algebra.leftMulMatrix_apply,
    ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, h, Units.coe_map]
  rfl

lemma canonicalInvolutionGL_mul_mul_mem (hg : g ∈ cartanSubgroup b) :
    canonicalInvolutionGL b * g * canonicalInvolutionGL b ∈ cartanSubgroup b := by
  rcases hg with ⟨u, rfl⟩
  rw [canonicalInvolutionGL_mul_unitsLeftMulMatrix_mul]
  exact ⟨_, rfl⟩

lemma canonicalInvolutionGL_mem_normalizer :
    canonicalInvolutionGL b ∈ Subgroup.normalizer (cartanSubgroup b : Set (GL (Fin 2) R)) := by
  refine Subgroup.mem_normalizer_iff.mpr fun g ↦ ⟨fun hg ↦ ?_, fun hg ↦ ?_⟩
  · exact inv_canonicalInvolutionGL b ▸ canonicalInvolutionGL_mul_mul_mem b hg
  · simpa only [mul_assoc, inv_mul_cancel, mul_one, canonicalInvolutionGL_mul_self_mul] using
      canonicalInvolutionGL_mul_mul_mem b hg

variable {x} in
/-- **The canonical involution lies in the Cartan subgroup only when it is the identity.** -/
lemma canonicalInvolutionGL_notMem_cartanSubgroup (hx : canonicalInvolution R A x ≠ x) :
    canonicalInvolutionGL b ∉ cartanSubgroup b := by
  rintro ⟨u, hu⟩
  have h : canonicalInvolution R A = Algebra.lmul R A (u : A) := by
    refine (LinearMap.toMatrix b b).injective ?_
    rw [← Algebra.leftMulMatrix_apply, ← coe_unitsLeftMulMatrix, hu, coe_canonicalInvolutionGL]
  have h₁ : (u : A) = 1 := by
    simpa [canonicalInvolution_one b] using (LinearMap.congr_fun h 1).symm
  exact hx (by simp [h, h₁])

/-- The **extended Cartan subgroup** of `GL₂(R)` attached to `A` and its basis `b` (LMFDB
`gl2.cartan`): the subgroup generated by the Cartan subgroup `cartanSubgroup b` and the matrix of
the canonical involution of `A`. -/
noncomputable def extendedCartanSubgroup : Subgroup (GL (Fin 2) R) :=
  cartanSubgroup b ⊔ Subgroup.zpowers (canonicalInvolutionGL b)

lemma cartanSubgroup_le_extendedCartanSubgroup : cartanSubgroup b ≤ extendedCartanSubgroup b :=
  le_sup_left

lemma canonicalInvolutionGL_mem_extendedCartanSubgroup :
    canonicalInvolutionGL b ∈ extendedCartanSubgroup b :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

/-- **The extended Cartan subgroup normalises the Cartan subgroup.** -/
lemma extendedCartanSubgroup_le_normalizer :
    extendedCartanSubgroup b ≤ Subgroup.normalizer (cartanSubgroup b : Set (GL (Fin 2) R)) :=
  sup_le Subgroup.le_normalizer <| Subgroup.zpowers_le.mpr (canonicalInvolutionGL_mem_normalizer b)

/-- The union of the Cartan subgroup and its coset through the canonical involution, as a
subgroup. -/
private def cartanSubgroupUnionCoset : Subgroup (GL (Fin 2) R) where
  carrier := {g | g * canonicalInvolutionGL b ∈ cartanSubgroup b ∨ g ∈ cartanSubgroup b}
  one_mem' := Or.inr (one_mem _)
  mul_mem' := by
    rintro g h (hg | hg) (hh | hh)
    · refine Or.inr ?_
      simpa only [mul_assoc, canonicalInvolutionGL_mul_self, mul_one,
        canonicalInvolutionGL_mul_self_mul] using
        mul_mem hg (canonicalInvolutionGL_mul_mul_mem b hh)
    · refine Or.inl ?_
      simpa only [mul_assoc, canonicalInvolutionGL_mul_self_mul] using
        mul_mem hg (canonicalInvolutionGL_mul_mul_mem b hh)
    · exact Or.inl (mul_assoc g h _ ▸ mul_mem hg hh)
    · exact Or.inr (mul_mem hg hh)
  inv_mem' := by
    rintro g (hg | hg)
    · refine Or.inl ?_
      simpa only [DivisionMonoid.mul_inv_rev, inv_canonicalInvolutionGL,
        canonicalInvolutionGL_mul_self_mul] using canonicalInvolutionGL_mul_mul_mem b (inv_mem hg)
    · exact Or.inr (inv_mem hg)

/-- **The Cartan subgroup has index `2` in the extended Cartan subgroup** (LMFDB `gl2.cartan`), as
soon as the canonical involution is not in the Cartan subgroup. -/
lemma relIndex_cartanSubgroup_extendedCartanSubgroup
    (h : canonicalInvolutionGL b ∉ cartanSubgroup b) :
    (cartanSubgroup b).relIndex (extendedCartanSubgroup b) = 2 := by
  refine Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr
    ⟨_, canonicalInvolutionGL_mem_extendedCartanSubgroup b, h, fun g hg ↦ ?_⟩
  have hle : extendedCartanSubgroup b ≤ cartanSubgroupUnionCoset b :=
    sup_le (fun c hc ↦ Or.inr hc) <| Subgroup.zpowers_le.mpr <|
      Or.inl (canonicalInvolutionGL_mul_self b ▸ one_mem _)
  exact hle hg

section Predicates

variable (H : Subgroup (GL (Fin 2) R))

/-- A subgroup of `GL₂(R)` is a **Cartan subgroup** (LMFDB `gl2.cartan`) if it is the image
`cartanSubgroup b` of `Aˣ` for some free rank-2 étale `R`-algebra `A` with a basis `b`. -/
def IsCartanSubgroup : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A)
    (b : Basis (Fin 2) R A), H = cartanSubgroup b

/-- A subgroup of `GL₂(R)` is an **extended Cartan subgroup** (LMFDB `gl2.cartan`) if it is
`extendedCartanSubgroup b` for some free rank-2 étale `R`-algebra `A` with a basis `b`. -/
def IsExtendedCartanSubgroup : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A)
    (b : Basis (Fin 2) R A), H = extendedCartanSubgroup b

end Predicates

section Field

variable {F : Type u} [Field F] (H : Subgroup (GL (Fin 2) F))

/-- A **split Cartan subgroup** of `GL₂(F)` (LMFDB `gl2.split_cartan`): a Cartan subgroup that is
diagonalizable over `F`, that is, has a conjugate consisting of diagonal matrices. The LMFDB uses
it for `F = 𝔽_p`. -/
def IsSplitCartanSubgroup : Prop :=
  IsCartanSubgroup H ∧ ∃ g : GL (Fin 2) F, H.map (MulAut.conj g).toMonoidHom ≤ diagonalTorus F 2

/-- A **non-split Cartan subgroup** of `GL₂(F)` (LMFDB `gl2.nonsplit_cartan`): a Cartan subgroup
that is not diagonalizable over `F`, that is, no conjugate of which consists of diagonal matrices.
The LMFDB uses it for `F = 𝔽_p`. -/
def IsNonsplitCartanSubgroup : Prop :=
  IsCartanSubgroup H ∧ ∀ g : GL (Fin 2) F, ¬H.map (MulAut.conj g).toMonoidHom ≤ diagonalTorus F 2

end Field

end Matrix.GeneralLinearGroup
