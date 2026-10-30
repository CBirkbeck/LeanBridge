import LeanBridge.ForMathlib.AlgebraicGeometry.GenusTwo.Curve
import LeanBridge.ForMathlib.AlgebraicGeometry.GenusTwo.MinimalEquation

/-!
# The label of a genus 2 curve over `ℚ`

The LMFDB labels a genus 2 curve over `ℚ` by `N.s.D.n` (LMFDB `g2c.label`), where `N` is the
conductor of the curve, the conductor of its Jacobian (LMFDB `g2c.conductor`), `s` is a string of
letters that distinguishes the isogeny class of the Jacobian among those of conductor `N`, `D` is
the absolute discriminant of the curve (LMFDB `g2c.abs_discriminant`) and `n` is a positive integer
that distinguishes the curve among those with the same absolute discriminant in the same isogeny
class; `N.s` is the label of the isogeny class of the Jacobian. As the knowl says, `s` and `n` are
assigned as curves are added to the database and carry no intrinsic meaning: these database
numberings are not formalised. Neither is the conductor `N`, the conductor of the Jacobian (LMFDB
`ag.conductor`), defined by the ramification of its `ℓ`-adic Galois representations: the conductor
of an abelian variety is not available.

What is formalised is the absolute discriminant `D`, the absolute value of the discriminant of a
minimal equation, which does not depend on the minimal equation
(`HyperellipticEquation.IsMinimal.abs_discriminant_eq`). That it is an integer, and that every
genus 2 curve over `ℚ` has a minimal equation, are not proved here.

## Main definitions

* `GenusTwoCurve.IsMinimalEquation` (LMFDB `g2c.minimal_equation`): a minimal equation of a genus 2
  curve over `ℚ`.
* `GenusTwoCurve.absDiscriminant` (LMFDB `g2c.label`, `g2c.abs_discriminant`): the absolute
  discriminant of a genus 2 curve over `ℚ`.

## Main results

* `GenusTwoCurve.absDiscriminant_eq`: the absolute discriminant is the absolute value of the
  discriminant of any minimal equation.
-/

namespace GenusTwoCurve

variable (C : GenusTwoCurve ℚ) {E : HyperellipticEquation 2 ℤ}

variable (E) in
/-- An integral Weierstrass equation `E` is a **minimal equation** (LMFDB `g2c.minimal_equation`)
of a genus 2 curve `C` over `ℚ` if it is minimal (`HyperellipticEquation.IsMinimal`) and defines
the same curve: its function field over `ℚ` is isomorphic to that of `C`. -/
def IsMinimalEquation : Prop :=
  E.IsMinimal ∧ Nonempty (E.toRat.FunctionField ≃ₐ[ℚ] C.FunctionField)

open scoped Classical in
/-- The **absolute discriminant** `D` (LMFDB `g2c.abs_discriminant`, and the `D` of the label
`N.s.D.n` of LMFDB `g2c.label`) of a genus 2 curve `C` over `ℚ`: the absolute value `|Δ|` of the
discriminant of a minimal equation of `C`, which does not depend on the minimal equation
(`absDiscriminant_eq`), and `0` if `C` has no minimal equation, which does not happen (not proved
here). It is a positive integer, which is not proved here either. -/
noncomputable def absDiscriminant : ℚ :=
  if h : ∃ E, C.IsMinimalEquation E then |h.choose.toRat.discriminant| else 0

/-- **The absolute discriminant of a genus 2 curve is that of any of its minimal equations.** -/
lemma absDiscriminant_eq (hE : C.IsMinimalEquation E) :
    C.absDiscriminant = |E.toRat.discriminant| := by
  have h : ∃ E, C.IsMinimalEquation E := ⟨E, hE⟩
  rw [absDiscriminant, dite_eq_left h]
  exact h.choose_spec.1.abs_discriminant_eq hE.1 (hE.2.some.trans h.choose_spec.2.some.symm)

end GenusTwoCurve
