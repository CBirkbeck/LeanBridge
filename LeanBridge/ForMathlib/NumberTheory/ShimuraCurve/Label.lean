import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.EnhancedGroup
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.QuaternionOrder

/-!
# Labels of Shimura curves

Let `(O, μ)` be a polarized order in an indefinite division quaternion algebra `B` over `ℚ` of
discriminant `D`, and let `H` be an open compact subgroup of level `N` of the enhanced group
`Aut_{±μ}(O) ⋉ Ô^×`. The LMFDB labels the Shimura curve `X_H` by `D.d.δ.N.i.g.c.n`, where `d` is
the reduced discriminant of `O`, omitted when `O` is maximal, `δ` is the polarization degree of
`μ`, `i` is the index of `H` in the enhanced group and `g` is the genus of `X_H`.

The base-`26` ordinal `c` of the Gassmann class of `H` among the groups of the same level, index
and genus, and the integer `n` distinguishing nonconjugate groups, follow LMFDB orderings that the
knowl does not specify: they are database numberings rather than mathematical functions of `H`, and
there is nothing to formalise in them (what they number, the Gassmann class and the conjugacy class
of `H`, is mathematical, but not their numbering). The genus `g`, the genus of a geometric component
of `X_H`, is mathematically defined, but it needs the Shimura curve `X_H` as an algebraic curve,
which is not available, so it is not formalised. The other entries `D`, `d`, `δ`, `N` and `i` are
formalised, from `QuaternionAlgebra.discriminant`, `Subalgebra.quaternionDiscrd`,
`PolarizedQuaternionOrder.degree`, `Subalgebra.enhancedGroupLevel` and `Subgroup.index`. As there,
`B` is any `ℚ`-algebra, the enhanced group is Mathlib's semidirect product `Ô^× ⋊ Aut_{±μ}(O)`,
and the topology of the enhanced group, which makes `H` open and compact, is not introduced.

Conjugate subgroups of the enhanced group, which define isomorphic Shimura curves, have the same
level, since the kernels of reduction are normal, and the same index; a conjugate `g H g⁻¹` is the
pointwise action `g • H` of `g ∈ ConjAct (Aut_{±μ}(O) ⋉ Ô^×)`.

## Main definitions

* `Subalgebra.enhancedGroupReduction`: reduction modulo `N` on the enhanced group.
* `PolarizedQuaternionOrder.ShimuraCurveLabel` (LMFDB `shimcurve.label`): the formalised part of
  the label of a Shimura curve.
* `PolarizedQuaternionOrder.shimuraCurveLabel` (LMFDB `shimcurve.label`): that of `X_H`.

## Main results

* `Subalgebra.normal_enhancedGroupKernel`: the kernel of reduction modulo `N` is normal in the
  enhanced group.
* `Subalgebra.enhancedGroupLevel_conj`: conjugate subgroups of the enhanced group have the same
  level.
-/

open scoped Pointwise

namespace Subalgebra

variable {B : Type*} [Ring B] [Algebra ℚ B] (O : Subalgebra ℤ B) (μ : B) (N : ℕ+)
  (H : Subgroup (O.EnhancedGroup μ)) (g : ConjAct (O.EnhancedGroup μ))

/-- **Reduction modulo `N`** on the enhanced group, `Aut_{±μ}(O) ⋉ Ô^× → Aut_{±μ}(O) ⋉ (O/NO)^×`:
reduction `Ô^× → (O/NO)^×` modulo `N`, which commutes with the actions of `Aut_{±μ}(O)`, and the
identity on `Aut_{±μ}(O)`. -/
noncomputable def enhancedGroupReduction : O.EnhancedGroup μ →* O.EnhancedGroupMod N μ :=
  SemidirectProduct.map (O.completedUnitsReduction N) (MonoidHom.id _) fun _ ↦
    MonoidHom.ext fun _ ↦ rfl

lemma ker_enhancedGroupReduction :
    (O.enhancedGroupReduction μ N).ker = O.enhancedGroupKernel μ N := by
  ext x
  rw [MonoidHom.mem_ker, enhancedGroupKernel, Subgroup.mem_map]
  refine ⟨fun h ↦ ⟨x.left, congrArg SemidirectProduct.left h,
    SemidirectProduct.ext rfl (congrArg SemidirectProduct.right h).symm⟩, ?_⟩
  rintro ⟨a, ha, rfl⟩
  exact SemidirectProduct.ext ha rfl

/-- **The kernel of `Ô^× → (O/NO)^×` is normal in the enhanced group**, as the kernel of reduction
modulo `N` on the enhanced group. -/
lemma normal_enhancedGroupKernel : (O.enhancedGroupKernel μ N).Normal :=
  O.ker_enhancedGroupReduction μ N ▸ MonoidHom.normal_ker _

lemma enhancedGroupKernel_le_conj_iff :
    O.enhancedGroupKernel μ N ≤ g • H ↔ O.enhancedGroupKernel μ N ≤ H := by
  conv_lhs => rw [← (O.normal_enhancedGroupKernel μ N).conjAct g]
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff

/-- **Conjugate subgroups of the enhanced group have the same level**: they contain the same
kernels of reduction, which are normal. -/
lemma enhancedGroupLevel_conj : O.enhancedGroupLevel μ (g • H) = O.enhancedGroupLevel μ H := by
  simp only [enhancedGroupLevel, enhancedGroupKernel_le_conj_iff]

end Subalgebra

namespace PolarizedQuaternionOrder

variable {B : Type*} [Ring B] [Algebra ℚ B] (O : PolarizedQuaternionOrder B)
  (H : Subgroup (O.order.EnhancedGroup (O.polarization : B)))

/-- The formalised part of the **label** `D.d.δ.N.i.g.c.n` (LMFDB `shimcurve.label`) of a Shimura
curve `X_H`: the part `D.d.δ.N.i`, where the entry `d` is omitted when the order is maximal. The
genus `g` needs `X_H` as an algebraic curve, and the entries `c` and `n` are database numberings. -/
structure ShimuraCurveLabel where
  /-- The discriminant `D` of the quaternion algebra `B`. -/
  discriminant : ℕ
  /-- The reduced discriminant `d` of the order `O`, and `none` when `O` is maximal. -/
  reducedDiscriminant : Option ℚ
  /-- The polarization degree `δ` of `μ`. -/
  polarizationDegree : ℕ
  /-- The level `N` of `H`. -/
  level : ℕ
  /-- The index `i` of `H` in the enhanced group. -/
  index : ℕ

open scoped Classical in
/-- The formalised part `D.d.δ.N.i` of the **label** `D.d.δ.N.i.g.c.n` (LMFDB `shimcurve.label`) of
the Shimura curve `X_H` of a subgroup `H` of the enhanced group `Aut_{±μ}(O) ⋉ Ô^×` of a polarized
order `(O, μ)`: the discriminant `D` of `B`, the reduced discriminant `d` of `O` unless `O` is
maximal, the polarization degree `δ` of `μ`, the level `N` of `H` and its index `i`. -/
noncomputable def shimuraCurveLabel : ShimuraCurveLabel where
  discriminant := QuaternionAlgebra.discriminant B
  reducedDiscriminant :=
    if O.order.IsMaximalQuaternionOrder then none else some O.order.quaternionDiscrd
  polarizationDegree := O.degree
  level := O.order.enhancedGroupLevel (O.polarization : B) H
  index := H.index

end PolarizedQuaternionOrder
