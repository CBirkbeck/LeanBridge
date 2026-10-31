import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisStability
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.StarkUnit

/-!
# The Galois conjugates in the Stark unit of a newform of weight one

The Stark unit of a newform `f` of weight one (LMFDB `cmf.stark_unit`) is built from the
derivatives at `0` of the L-functions `L(s, f^α)` of its Galois conjugates `f^α = ∑ α(aₙ) qⁿ`, for
`α` in the Galois group of its coefficient field `E`. In `HeckeRing.GL2.Newform.galoisConjLFunction`
the L-function `L(s, f^α)` is the entire continuation of `∑ α(aₙ) n^{-s}`, with the junk value `0`
when there is none; the continuation exists when `f^α` is a newform, which is known for `α = 1`.

This file shows that the junk value does not occur, for every `α`, as soon as the rational Hecke
algebra of the newspace of weight one is a `ℚ`-form of the complex one
(`TauCeti.HasRationalHeckeForm N 1`): then `f^α` is a newform, and `L(s, f^α)` is its
L-function. The hypothesis holds (weight-one forms also have a rational structure), but it is not
proved here.

## Main results

* `HeckeRing.GL2.Newform.exists_galoisConjLFunction_eq_L_of_hasRationalHeckeForm`: if the rational
  Hecke algebra of weight one is a `ℚ`-form, then for every `α` the Galois conjugate `f^α` is a
  newform `g`, and `L(s, f^α)` is the L-function of `g`.
-/

open UpperHalfPlane TauCeti

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] (f : Newform N 1)

/-- **The Galois conjugates of a newform of weight one are newforms, with their L-functions, if
the rational Hecke algebra is a `ℚ`-form**: for every automorphism `α` of the coefficient field of
`f`, there is a newform `g` with coefficients `α(aₙ)`, and the L-function `L(s, f^α)` entering the
Stark unit (LMFDB `cmf.stark_unit`) is the L-function of `g`, not the junk value `0`. -/
lemma exists_galoisConjLFunction_eq_L_of_hasRationalHeckeForm (hH : HasRationalHeckeForm N 1)
    (α : CoefficientField f ≃ₐ[ℚ] CoefficientField f) : ∃ g : Newform N 1,
      (∀ n, (qExpansion 1 g.toCuspForm).coeff n = f.galoisConjCoeff α n) ∧
      f.galoisConjLFunction α = ModularForm.L one_pos g.toCuspForm := by
  rcases IntermediateField.exists_algEquiv_apply_eq_of_countable
    ((CoefficientField f).val.comp α.toAlgHom) with ⟨σ, hσ⟩
  rcases exists_isGaloisConjugateBy_of_hasRationalHeckeForm f σ hH with ⟨g, hg⟩
  exact ⟨g, fun n ↦ (hg.coeff n).trans <| hσ ⟨_, f.qExpansion_coeff_mem_coefficientField n⟩,
    galoisConjLFunction_eq_L_of_isGaloisConjugateBy hσ hg⟩

end HeckeRing.GL2.Newform
