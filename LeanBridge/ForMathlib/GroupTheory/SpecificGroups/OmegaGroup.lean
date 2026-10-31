import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.Chevalley

/-!
# Nondegeneracy of the standard orthogonal forms, `Ω⁻(2m + 2, q)` and the groups `PΩ`

The groups `Ω(n, q)` and `Ω^±(n, q)` (LMFDB `group.omega`) are subgroups of the special orthogonal
groups of the standard nondegenerate quadratic forms over `𝔽_q`: the parabolic form in odd
dimension, the hyperbolic (`+`) and elliptic (`-`) forms in even dimension. Mathlib's notion of a
nondegenerate quadratic form (`QuadraticMap.Nondegenerate`, trivial radical and a polar form whose
kernel has rank at most `1`) makes sense in every characteristic. We prove that the three standard
forms are nondegenerate in every characteristic, the hyperbolic and elliptic forms because their
polar forms are nondegenerate, the parabolic form because the kernel of its polar form is the line
of its first coordinate, on which it is `z²`. For odd `q`, where `Ω(Q)` is the kernel of the spinor
norm on `SO(Q)` (`QuadraticForm.omegaGroup`), this gives `Ω⁻(2m + 2, q)`, and `PΩ(Q)` is the
quotient of `Ω(Q)` by its scalar automorphisms.

For even `q` the LMFDB takes `Ω(2m + 1, q) = SO(2m + 1, q)`, the special orthogonal group of the
parabolic form, which `QuadraticForm.nondegenerate_parabolicForm'` shows to be nondegenerate in
characteristic `2` as well. The groups `Ω^±(2m, q)` for even `q`, kernels of the Dickson invariant
`g ↦ dim ker (g - 1) mod 2` (the knowl's quasideterminant), are not defined here: that the Dickson
invariant is a homomorphism on `O(Q)` is not proved.

## Main definitions

* `QuadraticForm.omegaMinusGroup` (LMFDB `group.omega`): `Ω⁻(2m + 2, q)` for odd `q`.
* `QuadraticForm.projectiveOmegaGroup` (LMFDB `group.omega`): `PΩ(Q)` for `2` invertible.

## Main results

* `QuadraticForm.nondegenerate_hyperbolicForm'`, `QuadraticForm.nondegenerate_parabolicForm'`,
  `QuadraticForm.nondegenerate_ellipticForm`: the standard forms are nondegenerate in every
  characteristic.
-/

open TauCeti QuadraticMap

namespace QuadraticForm

variable {F V V' : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V']
  {Q : QuadraticForm F V}

lemma nondegenerate_of_ker_polarBilin_eq_bot (h : (polarBilin Q).ker = ⊥) : Q.Nondegenerate :=
  ⟨eq_bot_iff.mpr <| h ▸ radical_le_ker_polarBilin, by rw [h, rank_bot]; exact zero_le_one⟩

lemma ker_polarBilin_prod {Q' : QuadraticForm F V'} (h : (polarBilin Q).ker = ⊥)
    (h' : (polarBilin Q').ker = ⊥) : (polarBilin (Q.prod Q')).ker = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun v hv ↦ Prod.ext ?_ ?_
  · refine (Submodule.eq_bot_iff _).mp h v.1 (LinearMap.mem_ker.mpr (LinearMap.ext fun w ↦ ?_))
    simpa using LinearMap.congr_fun (LinearMap.mem_ker.mp hv) (w, 0)
  · refine (Submodule.eq_bot_iff _).mp h' v.2 (LinearMap.mem_ker.mpr (LinearMap.ext fun w ↦ ?_))
    simpa using LinearMap.congr_fun (LinearMap.mem_ker.mp hv) (0, w)

variable [Invertible (2 : F)] [FiniteDimensional F V] (Q) in
/-- The **projective group `PΩ(Q)`** (LMFDB `group.omega`) of a nondegenerate quadratic form `Q`
over a field in which `2` is invertible: the quotient of `Ω(Q)` (`QuadraticForm.omegaGroup`, the
kernel of the spinor norm on `SO(Q)`) by its subgroup of scalar automorphisms. For the parabolic,
hyperbolic and elliptic forms over `𝔽_q`, `q` odd, these are `PΩ(2m + 1, q)`, `PΩ⁺(2m, q)` and
`PΩ⁻(2m + 2, q)`. -/
abbrev projectiveOmegaGroup (hQ : Q.Nondegenerate) : Type _ :=
  omegaGroup Q hQ ⧸ ((LinearEquiv.scalarSubgroup F V).subgroupOf
    (specialOrthogonalGroup Q)).subgroupOf (omegaGroup Q hQ)

variable (F) (m : ℕ)

lemma ker_polarBilin_hyperbolicForm : (polarBilin (hyperbolicForm F m)).ker = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun v hv ↦ funext fun i ↦ ?_
  have h₁ : polar (hyperbolicForm F m) v (Pi.single i (1, 0)) = 0 :=
    LinearMap.congr_fun (LinearMap.mem_ker.mp hv) _
  have h₂ : polar (hyperbolicForm F m) v (Pi.single i (0, 1)) = 0 :=
    LinearMap.congr_fun (LinearMap.mem_ker.mp hv) _
  simp [polar, hyperbolicForm_apply, Pi.single_apply, Finset.sum_add_distrib, add_mul, mul_add,
    apply_ite Prod.fst, apply_ite Prod.snd] at h₁ h₂
  exact Prod.ext h₂ h₁

/-- **The hyperbolic form is nondegenerate in every characteristic**, its polar form being
nondegenerate (`QuadraticForm.nondegenerate_hyperbolicForm` assumes `2` invertible). -/
lemma nondegenerate_hyperbolicForm' : (hyperbolicForm F m).Nondegenerate :=
  nondegenerate_of_ker_polarBilin_eq_bot <| ker_polarBilin_hyperbolicForm F m

/-- **The parabolic form is nondegenerate in every characteristic**
(`QuadraticForm.nondegenerate_parabolicForm` assumes `2` invertible): the kernel of its polar form
lies in the line of the first coordinate, on which the form `z²` vanishes only at `0`. -/
lemma nondegenerate_parabolicForm' : (parabolicForm F m).Nondegenerate := by
  have hker : (polarBilin (parabolicForm F m)).ker ≤
      LinearMap.range (LinearMap.inl F F (Fin m → F × F)) := by
    intro v hv
    refine ⟨v.1, Prod.ext rfl ((Submodule.eq_bot_iff _).mp (ker_polarBilin_hyperbolicForm F m) v.2
      (LinearMap.mem_ker.mpr (LinearMap.ext fun w ↦ ?_))).symm⟩
    simpa [parabolicForm] using LinearMap.congr_fun (LinearMap.mem_ker.mp hv) (0, w)
  refine ⟨(Submodule.eq_bot_iff _).mpr fun v hv ↦ ?_,
    (Submodule.rank_mono hker).trans <| (rank_range_le _).trans (Module.rank_self F).le⟩
  rcases hker (radical_le_ker_polarBilin hv) with ⟨z, rfl⟩
  simpa [parabolicForm] using (mem_radical_iff'.mp hv).1

variable [Finite F]

lemma ker_polarBilin_anisotropicPlane : (polarBilin (anisotropicPlane F)).ker = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun v hv ↦ ?_
  have h₁ : polar (anisotropicPlane F) v (1, 0) = 0 :=
    LinearMap.congr_fun (LinearMap.mem_ker.mp hv) _
  have h₂ : polar (anisotropicPlane F) v (0, 1) = 0 :=
    LinearMap.congr_fun (LinearMap.mem_ker.mp hv) _
  simp only [polar, anisotropicPlane_apply, Prod.fst_add, Prod.snd_add] at h₁ h₂
  have hζ : 1 - 4 * anisotropicCoeff F ≠ 0 := fun h ↦
    sq_add_add_anisotropicCoeff_ne_zero F (-2 * anisotropicCoeff F) <| by
      linear_combination (-anisotropicCoeff F) * h
  have ha : v.1 = 0 := by
    refine (mul_eq_zero.mp ?_).resolve_right hζ
    linear_combination h₂ - 2 * anisotropicCoeff F * h₁
  refine Prod.ext ha ?_
  rw [Prod.snd_zero]
  linear_combination h₁ - 2 * ha

/-- **The elliptic form is nondegenerate**, in every characteristic: the polar forms of the
hyperbolic part and of the anisotropic plane `x² + x y + ζ y²` are nondegenerate, the latter because
`t² + t + ζ` has no root, so that `4 ζ ≠ 1`. -/
lemma nondegenerate_ellipticForm : (ellipticForm F m).Nondegenerate :=
  nondegenerate_of_ker_polarBilin_eq_bot <|
    ker_polarBilin_prod (ker_polarBilin_hyperbolicForm F m) (ker_polarBilin_anisotropicPlane F)

variable [Invertible (2 : F)] in
/-- The group **`Ω⁻(2m + 2, q)`** (LMFDB `group.omega`), for `F = 𝔽_q` with `q` odd: the group `Ω`,
kernel of the spinor norm on `SO`, of the elliptic form `x₁ y₁ + ⋯ + x_m y_m + (z² + z w + ζ w²)`,
which is nondegenerate (`QuadraticForm.nondegenerate_ellipticForm`). -/
noncomputable abbrev omegaMinusGroup : Subgroup (specialOrthogonalGroup (ellipticForm F m)) :=
  omegaGroup (ellipticForm F m) (nondegenerate_ellipticForm F m)

end QuadraticForm
