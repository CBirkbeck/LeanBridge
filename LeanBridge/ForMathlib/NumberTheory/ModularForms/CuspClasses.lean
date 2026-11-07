import Mathlib.NumberTheory.ModularForms.Cusps

/-!
# The cusps of a subgroup of the modular group

The cusps of a subgroup `Γ` of the modular group `SL(2, ℤ)` (LMFDB `group.fuchsian.cusps`) are the
classes of the points of `ℚ ∪ {∞}` under the action of `Γ` by linear fractional transformations.
Here `ℚ ∪ {∞}` is Mathlib's projective line `OnePoint ℚ`, on which `GL(2, ℚ)` acts
(`OnePoint.instGLAction`), and `Γ` acts through `SL(2, ℤ) → GL(2, ℚ)`: `γ = (a, b; c, d)` sends
`x ∈ ℚ` to `(a x + b) / (c x + d)`, or to `∞` when `c x + d = 0`, and `∞` to `a / c`, or to `∞` when
`c = 0`, as the knowl says.

Mathlib's `CuspOrbits 𝒢` of a subgroup `𝒢` of `GL(2, ℝ)` are the orbits of `𝒢` on the fixed
points of its parabolic elements. For an arithmetic subgroup these are the points of `ℚ ∪ {∞}`
(`Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`), but not in general: the trivial subgroup has no
parabolic element, while it has one cusp for each point of `ℚ ∪ {∞}`. The knowl takes every
subgroup of `SL(2, ℤ)`, so its cusps are defined here as the orbits on all of `ℚ ∪ {∞}`.

## Main definitions

* `Subgroup.CuspClasses` (LMFDB `group.fuchsian.cusps`): the cusps of a subgroup of `SL(2, ℤ)`.

## Main results

* `Subgroup.mk_eq_mk_iff_cusp`: two points of `ℚ ∪ {∞}` give the same cusp of `Γ` exactly when an
  element of `Γ` maps one to the other.
* `Matrix.SpecialLinearGroup.mapGL_smul_coe` and `Matrix.SpecialLinearGroup.mapGL_smul_infty`
  (LMFDB `group.fuchsian.cusps`): the action of `SL(2, ℤ)` on `ℚ ∪ {∞}` by linear fractional
  transformations, with `γ ∞ = a / c` for `c ≠ 0` and `γ ∞ = ∞` for `c = 0`.
* The instance `Subsingleton (⊤ : Subgroup SL(2, ℤ)).CuspClasses`: the modular group has one cusp.
-/

open Matrix SpecialLinearGroup OnePoint

open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

variable (γ : SL(2, ℤ))

/-- **`SL(2, ℤ)` acts on `ℚ` by linear fractional transformations** (LMFDB `group.fuchsian.cusps`,
`group.fuchsian.action`): `γ = (a, b; c, d)` sends `x ∈ ℚ` to `(a x + b) / (c x + d)`, or to `∞`
when `c x + d = 0`. -/
lemma mapGL_smul_coe (x : ℚ) : mapGL ℚ γ • (x : OnePoint ℚ) = if γ 1 0 * x + γ 1 1 = 0 then ∞
    else (((γ 0 0 * x + γ 0 1) / (γ 1 0 * x + γ 1 1) : ℚ) : OnePoint ℚ) := by
  rw [smul_some_eq_ite]
  simp

/-- **`SL(2, ℤ)` acts on `∞` by `γ ∞ = a / c` for `c ≠ 0` and `γ ∞ = ∞` for `c = 0`** (LMFDB
`group.fuchsian.cusps`), where `γ = (a, b; c, d)`. -/
lemma mapGL_smul_infty :
    mapGL ℚ γ • (∞ : OnePoint ℚ) = if γ 1 0 = 0 then ∞ else ((γ 0 0 / γ 1 0 : ℚ) : OnePoint ℚ) := by
  rw [smul_infty_eq_ite]
  simp

end Matrix.SpecialLinearGroup

namespace Subgroup

variable (Γ : Subgroup SL(2, ℤ))

/-- The **cusps** (LMFDB `group.fuchsian.cusps`) of a subgroup `Γ` of the modular group
`SL(2, ℤ)`: the classes of the points of `ℚ ∪ {∞}`, Mathlib's `OnePoint ℚ`, under the action of `Γ`
by linear fractional transformations (`Matrix.SpecialLinearGroup.mapGL_smul_coe`,
`Matrix.SpecialLinearGroup.mapGL_smul_infty`), that is, the orbits of the image of `Γ` in
`GL(2, ℚ)` acting on the projective line. Two points give the same cusp exactly when an element of
`Γ` maps one to the other (`Subgroup.mk_eq_mk_iff_cusp`). This is meant for every subgroup, unlike
Mathlib's `CuspOrbits`, the orbits of the fixed points of parabolic elements, which differ for
subgroups of infinite index. -/
abbrev CuspClasses : Type :=
  MulAction.orbitRel.Quotient (Γ.map (mapGL ℚ)) (OnePoint ℚ)

variable {Γ}

/-- **Two points of `ℚ ∪ {∞}` give the same cusp of `Γ` exactly when an element of `Γ` maps one to
the other.** -/
lemma mk_eq_mk_iff_cusp {x y : OnePoint ℚ} :
    (Quotient.mk _ x : Γ.CuspClasses) = Quotient.mk _ y ↔ ∃ γ ∈ Γ, mapGL ℚ γ • y = x := by
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨_, γ, hγ, rfl⟩, h⟩
    exact ⟨γ, hγ, h⟩
  · rintro ⟨γ, hγ, h⟩
    exact ⟨⟨mapGL ℚ γ, γ, hγ, rfl⟩, h⟩

instance : Subsingleton (⊤ : Subgroup SL(2, ℤ)).CuspClasses := by
  refine ⟨fun c c' ↦ Quotient.inductionOn₂ c c' fun x y ↦ mk_eq_mk_iff_cusp.mpr ?_⟩
  rcases exists_mem_SL2 ℤ x with ⟨g, rfl⟩
  rcases exists_mem_SL2 ℤ y with ⟨h, rfl⟩
  exact ⟨g * h⁻¹, mem_top _, by rw [map_mul, mul_smul, map_inv, inv_smul_smul]⟩

end Subgroup
