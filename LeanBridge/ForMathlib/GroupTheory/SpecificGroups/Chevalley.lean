import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.Orthogonal
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic

/-!
# The classical Chevalley groups

The Chevalley groups of types `A`, `B`, `C`, `D` over the finite field `𝔽_q` are

* `A(n, q) = SL(n + 1, q)`, Mathlib's `Matrix.SpecialLinearGroup (Fin (n + 1)) F`;
* `B(n, q) = Ω(2n + 1, q)`, the group `Ω` of the parabolic form of dimension `2n + 1`;
* `C(n, q) = Sp(2n, q)`, Mathlib's `Matrix.symplecticGroup (Fin n) F`;
* `D(n, q) = Ω⁺(2n, q)`, the group `Ω` of the hyperbolic form of dimension `2n`.

For a nondegenerate quadratic form `Q` over a field in which `2` is invertible, `Ω(Q)` is the
kernel of the spinor norm `SO(Q) → F^× / (F^×)²`. This covers odd `q` only: in characteristic `2`,
`Ω` is the kernel of the Dickson invariant, which is not available, and is not defined here.

## Main definitions

* `QuadraticForm.omegaGroup` (LMFDB `group.chevalley`): the kernel `Ω(Q)` of the spinor norm.
* `QuadraticForm.chevalleyB` (LMFDB `group.chevalley`): `B(n, q) = Ω(2n + 1, q)`, `q` odd.
* `QuadraticForm.chevalleyD` (LMFDB `group.chevalley`): `D(n, q) = Ω⁺(2n, q)`, `q` odd.

## Main results

* `QuadraticForm.nondegenerate_hyperbolicForm`, `QuadraticForm.nondegenerate_parabolicForm`: the
  hyperbolic and parabolic forms are nondegenerate when `2` is invertible.
-/

open TauCeti QuadraticMap

namespace QuadraticForm

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

variable (F) in
lemma hyperbolicForm_apply (m : ℕ) (x : Fin m → F × F) :
    hyperbolicForm F m x = ∑ i, (x i).1 * (x i).2 := by
  simp [hyperbolicForm]

variable (F) in
lemma radical_hyperbolicForm (m : ℕ) : (hyperbolicForm F m).radical = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun x hx => funext fun i => ?_
  rcases mem_radical_iff'.mp hx with ⟨h₀, h⟩
  rw [hyperbolicForm_apply] at h₀
  have h₁ : hyperbolicForm F m (x + Pi.single i (1, 0)) = hyperbolicForm F m (Pi.single i (1, 0)) :=
    h _
  have h₂ : hyperbolicForm F m (x + Pi.single i (0, 1)) = hyperbolicForm F m (Pi.single i (0, 1)) :=
    h _
  simp [hyperbolicForm_apply, Pi.single_apply, Finset.sum_add_distrib, add_mul, mul_add,
    apply_ite Prod.fst, apply_ite Prod.snd, h₀] at h₁ h₂
  exact Prod.ext h₂ h₁

variable [Invertible (2 : F)]

variable (F) in
/-- **The hyperbolic form is nondegenerate** when `2` is invertible. -/
lemma nondegenerate_hyperbolicForm (m : ℕ) : (hyperbolicForm F m).Nondegenerate :=
  nondegenerate_iff_radical_eq_bot.mpr <| radical_hyperbolicForm F m

variable (F) in
/-- **The parabolic form is nondegenerate** when `2` is invertible. -/
lemma nondegenerate_parabolicForm (m : ℕ) : (parabolicForm F m).Nondegenerate :=
  (one_smul F (sq : QuadraticForm F F) ▸ nondegenerate_smul_sq one_ne_zero).prod
    (nondegenerate_hyperbolicForm F m)

variable [FiniteDimensional F V]

/-- The group **`Ω(Q)`** (LMFDB `group.chevalley`) of a nondegenerate quadratic form `Q` over a
field in which `2` is invertible: the kernel of the spinor norm on `SO(Q)`. -/
noncomputable def omegaGroup (Q : QuadraticForm F V) (hQ : Q.Nondegenerate) :
    Subgroup (specialOrthogonalGroup Q) :=
  (CliffordAlgebra.spinorNorm Q hQ).ker

variable (F) in
/-- The Chevalley group **`B(n, q) = Ω(2n + 1, q)`** (LMFDB `group.chevalley`), for `F = 𝔽_q` with
`q` odd: the group `Ω` of the parabolic form `z² + x₁ y₁ + ⋯ + xₙ yₙ`. -/
noncomputable abbrev chevalleyB (n : ℕ) : Subgroup (specialOrthogonalGroup (parabolicForm F n)) :=
  omegaGroup (parabolicForm F n) (nondegenerate_parabolicForm F n)

variable (F) in
/-- The Chevalley group **`D(n, q) = Ω⁺(2n, q)`** (LMFDB `group.chevalley`), for `F = 𝔽_q` with
`q` odd: the group `Ω` of the hyperbolic form `x₁ y₁ + ⋯ + xₙ yₙ`. -/
noncomputable abbrev chevalleyD (n : ℕ) :
    Subgroup (specialOrthogonalGroup (hyperbolicForm F n)) :=
  omegaGroup (hyperbolicForm F n) (nondegenerate_hyperbolicForm F n)

end QuadraticForm
