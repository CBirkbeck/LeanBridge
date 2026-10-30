import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.Label

/-!
# The standard Shimura curves `X(D;N)`, `X^*(D;N)` and `X(D,M;1)`

Let `(O, μ)` be a polarized order in an indefinite division quaternion algebra `B` over `ℚ` of
discriminant `D`, and let `N` be a positive integer. A subgroup `H̄` of the finite group
`Aut_{±μ}(O) ⋉ (O/NO)^×` defines the open subgroup `H` of level dividing `N` of the enhanced group
`Aut_{±μ}(O) ⋉ Ô^×`, its inverse image under reduction modulo `N`, and so the Shimura curve `X_H`.
The LMFDB's standard Shimura curves are:

* `X(D;N)` (LMFDB `shimcurve.xdn`), for `O` maximal and `H̄ = {1}` at level `N`, so that `H` is the
  kernel `Γ(Ô, N)` of `Ô^× → (O/NO)^×` and `X_H` is the full level `N` Shimura curve
  `X(O;N)^big` of LMFDB `shimcurve`;
* `X(D;1)` (LMFDB `shimcurve.xd1`), its case `N = 1`, where `H = Ô^×` and `X_H(ℂ) = O^× \ ℋ^±`;
* `X^*(D;N)` (LMFDB `shimcurve.xdn_star`), for `O` maximal and `H̄ = Aut_{±μ}(O)` at level `N`, so
  that `H = Aut_{±μ}(O) ⋉ Γ(Ô, N)` and `X_H` is the quotient of `X(D;N)` by `Aut_{±μ}(O)`;
* `X^*(D;1)` (LMFDB `shimcurve.xd1_star`), its case `N = 1`, where `H` is the whole enhanced group;
* `X(D,M;1)` (LMFDB `shimcurve.xdm1`), for `O` an Eichler order of level `M` and `H̄ = {1}` at level
  `1`, so that `H = Ô^×` and `X_H(ℂ) = O^× \ ℋ^±`: this is the curve `X(O;1)^big`, which LMFDB
  `shimcurve` writes `X_0(D;M)`.

The knowls write `H = {1}` and `H = Aut_{±μ}(O)` as subgroups of the enhanced group
`Aut_{±μ}(O) ⋉ Ô^×`, where they are not open: as in LMFDB `shimcurve.is_coarse`, they are read as
the subgroups `H̄` of `Aut_{±μ}(O) ⋉ (O/NO)^×` at the level `N` of the curve, here `1`. The knowls
describe the groups of `X(D;N)` and `X^*(D;N)` as the inverse images of `(O/NO)^×` and of
`Aut_{±μ}(O) ⋉ (O/NO)^×`; read literally, these are `Ô^×` and the whole enhanced group for every
`N`, the groups of `X(D;1)` and `X^*(D;1)` (`Subalgebra.comap_enhancedGroupReduction_range_inl`).
They are read here as the inverse images of `{1} ⊆ (O/NO)^×` and of `Aut_{±μ}(O) ⋉ {1}`, as LMFDB
`modcurve.xfull` defines `X(N)` by the inverse image of the trivial subgroup of `GL₂(ℤ/Nℤ)`; this
makes `X(D;N)` the full level `N` Shimura curve of LMFDB `shimcurve`, with `X(D;1)` and `X^*(D;1)`
the cases `N = 1`.

The Shimura curves themselves, their canonical models over `ℚ` and their complex points
`B^× \ (ℋ^± × B̂^×) / H`, are not available, so the curves are recorded by their data: the
discriminant `D` of `B`, the condition on the order `O` (maximal, or Eichler of level `M`) and the
subgroup `H` of the enhanced group. As in `LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.Label`,
the enhanced group is Mathlib's semidirect product `Ô^× ⋊ Aut_{±μ}(O)`, and `B` is any `ℚ`-algebra,
`O` any subring and `μ` any element in the definitions of the groups.

## Main definitions

* `PolarizedQuaternionOrder.StandardShimuraCurve` (LMFDB `shimcurve.standard`): the families
  `X(D;N)`, `X^*(D;N)` and `X(D,M;1)` of standard Shimura curves.
* `PolarizedQuaternionOrder.StandardShimuraCurve.IsOrder`: the condition on the order.
* `PolarizedQuaternionOrder.StandardShimuraCurve.reducedSubgroup` (LMFDB `shimcurve.xd1`,
  `shimcurve.xd1_star`, `shimcurve.xdm1`, `shimcurve.xdn`, `shimcurve.xdn_star`): the subgroup
  `H̄ = {1}` or `H̄ = Aut_{±μ}(O)` of `Aut_{±μ}(O) ⋉ (O/NO)^×`.
* `PolarizedQuaternionOrder.StandardShimuraCurve.subgroup` (LMFDB `shimcurve.xd1`,
  `shimcurve.xd1_star`, `shimcurve.xdm1`, `shimcurve.xdn`, `shimcurve.xdn_star`): its inverse image
  `H` in the enhanced group.
* `PolarizedQuaternionOrder.IsStandardShimuraCurve` (LMFDB `shimcurve.xd1`, `shimcurve.xd1_star`,
  `shimcurve.xdm1`, `shimcurve.xdn`, `shimcurve.xdn_star`): the Shimura curve `X_H` of a polarized
  order and a subgroup `H` of its enhanced group is a given standard Shimura curve.

## Main results

* `Subalgebra.comap_enhancedGroupReduction_range_inl`: the inverse image of `(O/NO)^×` in the
  enhanced group is `Ô^×`, the group of `X(D;1)`, whatever `N`.
* `PolarizedQuaternionOrder.StandardShimuraCurve.subgroup_full`: the group of `X(D;N)` is the kernel
  `Γ(Ô, N)` of reduction modulo `N`.
* `PolarizedQuaternionOrder.StandardShimuraCurve.subgroup_eichler`: the group of `X(D,M;1)` is
  `Ô^× = Γ(Ô, 1)`.
* `PolarizedQuaternionOrder.StandardShimuraCurve.mem_subgroup_star_iff`: the group of `X^*(D;N)` is
  `Aut_{±μ}(O) ⋉ Γ(Ô, N)`.
* `PolarizedQuaternionOrder.StandardShimuraCurve.subgroup_star_one`: the group of `X^*(D;1)` is the
  whole enhanced group.
* `PolarizedQuaternionOrder.StandardShimuraCurve.enhancedGroupKernel_le_subgroup`: the group of a
  standard Shimura curve contains the kernel of reduction modulo its level.
-/

open SemidirectProduct

variable {B : Type*} [Ring B]

namespace Subalgebra

variable (O : Subalgebra ℤ B)

lemma subsingleton_quotient_span_one : Subsingleton (O ⧸ Ideal.span {(((1 : ℕ+) : ℕ) : O)}) := by
  simp

variable [Algebra ℚ B] (μ : B) (N : ℕ+)

lemma enhancedGroupKernel_one : O.enhancedGroupKernel μ 1 = rightHom.ker := by
  have h : (O.completedUnitsReduction 1).ker = ⊤ :=
    eq_top_iff.mpr fun _ _ ↦ Units.ext <| O.subsingleton_quotient_span_one.allEq _ _
  rw [enhancedGroupKernel, h, ← MonoidHom.range_eq_map, range_inl_eq_ker_rightHom]

/-- **The inverse image of `(O/NO)^×` in the enhanced group is `Ô^×`**, the group of `X(D;1)`, for
every `N`: the inverse image of `(O/NO)^× ⋊ {1}` under reduction modulo `N` is `Ô^× ⋊ {1}`. So the
literal reading of LMFDB `shimcurve.xdn`, where `X(D;N)` is the Shimura curve of this inverse image,
would make `X(D;N)` the curve `X(D;1)`. -/
lemma comap_enhancedGroupReduction_range_inl :
    inl.range.comap (O.enhancedGroupReduction μ N) = O.enhancedGroupKernel μ 1 := by
  rw [range_inl_eq_ker_rightHom, MonoidHom.comap_ker, enhancedGroupReduction, rightHom_comp_map,
    MonoidHom.id_comp, enhancedGroupKernel_one]

end Subalgebra

namespace PolarizedQuaternionOrder

/-- The **standard Shimura curves** (LMFDB `shimcurve.standard`), defined from a polarized order
`(O, μ)` in an indefinite division quaternion algebra over `ℚ` of discriminant `D` and a subgroup
`H̄` of `Aut_{±μ}(O) ⋉ (O/NO)^×`: `X(D;N)` (LMFDB `shimcurve.xdn`, and `shimcurve.xd1` for
`N = 1`), `X^*(D;N)` (LMFDB `shimcurve.xdn_star`, and `shimcurve.xd1_star` for `N = 1`) and
`X(D,M;1)` (LMFDB `shimcurve.xdm1`). -/
inductive StandardShimuraCurve
  /-- `X(D;N)`: `O` maximal and `H̄ = {1}` at level `N`. -/
  | full (N : ℕ+)
  /-- `X^*(D;N)`: `O` maximal and `H̄ = Aut_{±μ}(O)` at level `N`. -/
  | star (N : ℕ+)
  /-- `X(D,M;1)`: `O` Eichler of level `M` and `H̄ = {1}` at level `1`. -/
  | eichler (M : ℕ+)

variable [Algebra ℚ B]

namespace StandardShimuraCurve

variable (O : Subalgebra ℤ B) (μ : B) (N : ℕ+) (c : StandardShimuraCurve)

/-- The **level** of a standard Shimura curve, modulo which its group is defined: `N` for `X(D;N)`
and `X^*(D;N)`, and `1` for `X(D,M;1)`. -/
def level : StandardShimuraCurve → ℕ+
  | full N | star N => N
  | eichler _ => 1

/-- The **condition on the order** `O` of a standard Shimura curve: `O` is maximal for `X(D;N)` and
`X^*(D;N)`, and Eichler of level `M` for `X(D,M;1)`. -/
def IsOrder : StandardShimuraCurve → Prop
  | full _ | star _ => O.IsMaximalQuaternionOrder
  | eichler M => O.IsEichlerOrderOfLevel M

/-- The subgroup **`H̄`** of `Aut_{±μ}(O) ⋉ (O/NO)^×`, at the level `N` of a standard Shimura curve
(LMFDB `shimcurve.xd1`, `shimcurve.xd1_star`, `shimcurve.xdm1`, `shimcurve.xdn`,
`shimcurve.xdn_star`): `H̄ = {1}` for `X(D;N)` and `X(D,M;1)`, and `H̄ = Aut_{±μ}(O)` for
`X^*(D;N)`. -/
noncomputable def reducedSubgroup : Subgroup (O.EnhancedGroupMod c.level μ) :=
  match c with
  | full _ | eichler _ => ⊥
  | star _ => inr.range

/-- The open subgroup **`H`** of the enhanced group `Aut_{±μ}(O) ⋉ Ô^×` of a standard Shimura curve
(LMFDB `shimcurve.xd1`, `shimcurve.xd1_star`, `shimcurve.xdm1`, `shimcurve.xdn`,
`shimcurve.xdn_star`): the inverse image under reduction modulo the level `N` of the subgroup
`H̄ = {1}` or `H̄ = Aut_{±μ}(O)` of `Aut_{±μ}(O) ⋉ (O/NO)^×`. It is `Γ(Ô, N)` for `X(D;N)`,
`Aut_{±μ}(O) ⋉ Γ(Ô, N)` for `X^*(D;N)` and `Ô^×` for `X(D,M;1)`. -/
noncomputable def subgroup : Subgroup (O.EnhancedGroup μ) :=
  (c.reducedSubgroup O μ).comap (O.enhancedGroupReduction μ c.level)

/-- **The group of `X(D;N)` is the kernel `Γ(Ô, N)` of reduction modulo `N`**, so that `X(D;N)` is
the full level `N` Shimura curve `X(O;N)^big`. -/
lemma subgroup_full : (full N).subgroup O μ = O.enhancedGroupKernel μ N :=
  O.ker_enhancedGroupReduction μ N

/-- **The group of `X(D,M;1)` is `Ô^× = Γ(Ô, 1)`**, so that `X(D,M;1)` is the level `1` Shimura
curve `X(O;1)^big` of an Eichler order `O` of level `M`. -/
lemma subgroup_eichler (M : ℕ+) : (eichler M).subgroup O μ = O.enhancedGroupKernel μ 1 :=
  O.ker_enhancedGroupReduction μ 1

/-- **The group of `X^*(D;N)` is `Aut_{±μ}(O) ⋉ Γ(Ô, N)`**: an element `x w` of the enhanced group,
with `x ∈ Ô^×` and `w ∈ Aut_{±μ}(O)`, lies in it if and only if `x` lies in the kernel `Γ(Ô, N)` of
reduction modulo `N`. -/
lemma mem_subgroup_star_iff {x : O.EnhancedGroup μ} :
    x ∈ (star N).subgroup O μ ↔ x.left ∈ (O.completedUnitsReduction N).ker :=
  ⟨fun ⟨_, h⟩ ↦ (congrArg left h).symm, fun h ↦ ⟨x.right, SemidirectProduct.ext h.symm rfl⟩⟩

/-- **The group of `X^*(D;1)` is the whole enhanced group**: `(O/O)^×` is trivial, so `Aut_{±μ}(O)`
is the whole group `Aut_{±μ}(O) ⋉ (O/O)^×`. -/
lemma subgroup_star_one : (star 1).subgroup O μ = ⊤ :=
  eq_top_iff.mpr fun x _ ↦
    ⟨x.right, SemidirectProduct.ext (Units.ext <| O.subsingleton_quotient_span_one.allEq _ _) rfl⟩

/-- **The group of a standard Shimura curve contains the kernel of reduction modulo its level**, so
it is an open subgroup of level dividing that level. -/
lemma enhancedGroupKernel_le_subgroup : O.enhancedGroupKernel μ c.level ≤ c.subgroup O μ :=
  O.ker_enhancedGroupReduction μ c.level ▸ MonoidHom.ker_le_comap _ _

end StandardShimuraCurve

variable (O : PolarizedQuaternionOrder B)

/-- The Shimura curve `X_H` of a polarized order `(O, μ)` in an indefinite division quaternion
algebra `B` over `ℚ` and of a subgroup `H` of its enhanced group `Aut_{±μ}(O) ⋉ Ô^×` **is the
standard Shimura curve** `c` of discriminant `D` (LMFDB `shimcurve.xd1`, `shimcurve.xd1_star`,
`shimcurve.xdm1`, `shimcurve.xdn`, `shimcurve.xdn_star`): `B` has discriminant `D`, the order `O`
is maximal for `X(D;N)` and `X^*(D;N)` and Eichler of level `M` for `X(D,M;1)`, and `H` is the
group of `c`. -/
structure IsStandardShimuraCurve (c : StandardShimuraCurve) (D : ℕ)
    (H : Subgroup (O.order.EnhancedGroup O.polarization)) : Prop where
  /-- The quaternion algebra `B` has discriminant `D`. -/
  discriminant_eq : QuaternionAlgebra.discriminant B = D
  /-- The order `O` is maximal, or Eichler of level `M` for `X(D,M;1)`. -/
  isOrder : c.IsOrder O.order
  /-- `H` is the group of the standard Shimura curve `c`. -/
  eq_subgroup : H = c.subgroup O.order O.polarization

end PolarizedQuaternionOrder
