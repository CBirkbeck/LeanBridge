import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.HeckeIdeal
import LeanBridge.ForMathlib.NumberTheory.NumberField.HeckeIdealCharacter

/-!
# Hilbert modular forms with complex multiplication

A modular form `f` for `GL(2)` over a number field `F` has **complex multiplication** (LMFDB
`mf.cm`) if it is equal to its twist by a nontrivial Hecke character `χ` of `F`, or equivalently if
`a_𝔭 = χ(𝔭) a_𝔭` for the good primes `𝔭 ∤ 𝔑`; then `a_𝔭 = 0` whenever `χ(𝔭) ≠ 1`, in particular
when `χ(𝔭) = -1`. For `F = ℚ` this is the self twist of a classical newform
(`HeckeRing.GL2.Newform.HasSelfTwist`), for `F` imaginary quadratic it is the notion of
`Bianchi/ComplexMultiplicationOfWeight.lean`, and this file treats the Hilbert modular forms, the
modular forms for `GL(2)` over a totally real field `F`: the Hecke eigenforms of
`HilbertModularForm.IsHeckeIdealEigenform`, eigenvectors of the Hecke operators `T_𝔞` of all the
nonzero ideals `𝔞` coprime to the level, principal or not, whose eigenvalues are therefore defined
at every good prime. Modular forms for `GL(2)` over the other number fields are not formalised.

The Hecke characters are those of LMFDB `character.hecke` (`IsIdealHeckeCharacter`): characters
`χ : I(𝔪) → ℂˣ` of the fractional ideals prime to a modulus `𝔪`, of any order, with an infinity
type; the condition is imposed at the good primes prime to `𝔪`, that is at all but finitely many
primes, which is what equality with the twist means by strong multiplicity one. The eigenvalues of
`HilbertModularForm.heckeIdealEigenvalue` differ from the LMFDB's by powers of `N(𝔭)`, which does
not change the condition. That `χ` is then quadratic is a theorem not proved here.

## Main definitions

* `HilbertModularForm.IsHeckeIdealEigenform.HasCMBy` (LMFDB `mf.cm`): a Hilbert Hecke eigenform has
  complex multiplication by the Hecke character `χ`.
* `HilbertModularForm.IsHeckeIdealEigenform.HasCM` (LMFDB `mf.cm`): a Hilbert Hecke eigenform has
  complex multiplication.

## Main results

* `HilbertModularForm.IsHeckeIdealEigenform.HasCMBy.heckeIdealEigenvalue_eq_zero`: the eigenvalues
  vanish at the good primes `𝔭` with `χ(𝔭) ≠ 1`, in particular where `χ(𝔭) = -1`.
-/

open NumberField TauCeti GlobalNumberFields NumberFieldArithmetic

open scoped nonZeroDivisors

namespace HilbertModularForm.IsHeckeIdealEigenform

variable {F : Type*} [Field F] [NumberField F] {k : {w : InfinitePlace F // w.IsReal} → ℤ}
  {𝔑 : Ideal (𝓞 F)} [NeZero 𝔑] {𝔟 : NarrowClassGroup F → (FractionalIdeal (𝓞 F)⁰ F)ˣ}
  {h𝔟 : ∀ c, NarrowClassGroup.mk (𝔟 c) = c} {ψ : HilbertModularForm 𝔑 k 𝔟 h𝔟}
  (hψ : ψ.IsHeckeIdealEigenform) {𝔪 : Modulus F} (χ : idealsPrimeTo 𝔪 →* ℂˣ)

/-- A Hilbert modular form `ψ` of level `𝔑` over `F`, a Hecke eigenform for the Hecke operators
`T_𝔞` with `𝔞` coprime to `𝔑`, has **complex multiplication by** the Hecke character
`χ : I(𝔪) → ℂˣ` of `F` (LMFDB `mf.cm`, `character.hecke`) if `χ` is a nontrivial Hecke character
modulo `𝔪` and `ψ` equals its twist by `χ`: `a_𝔭 = χ(𝔭) a_𝔭` for every prime `𝔭 ∤ 𝔑` prime to `𝔪`,
principal or not, where `a_𝔭` is the eigenvalue of `T_𝔭`. -/
def HasCMBy : Prop :=
  IsIdealHeckeCharacter 𝔪 χ ∧ χ ≠ 1 ∧ ∀ (𝔭 : (Ideal (𝓞 F))⁰), (𝔭 : Ideal (𝓞 F)).IsPrime →
    ∀ (h𝔭 : (𝔭 : Ideal (𝓞 F)) ⊔ 𝔑 = ⊤) (hχ : (𝔭 : Ideal (𝓞 F)) ∈ integralIdealsPrimeTo 𝔪),
      heckeIdealEigenvalue 𝔭 hψ h𝔭 =
        (χ (integralIdealsAwayHom F 𝔪.support ⟨𝔭, hχ⟩) : ℂ) * heckeIdealEigenvalue 𝔭 hψ h𝔭

/-- A Hilbert modular form which is a Hecke eigenform has **complex multiplication**, or **CM**
(LMFDB `mf.cm`), if it is equal to its own twist by a nontrivial Hecke character of `F`: it has
complex multiplication by a nontrivial Hecke character modulo some modulus `𝔪`. -/
def HasCM : Prop :=
  ∃ (𝔪 : Modulus F) (χ : idealsPrimeTo 𝔪 →* ℂˣ), hψ.HasCMBy χ

variable {hψ χ}

/-- **The eigenvalues of a CM eigenform vanish where its character is not `1`**: if `ψ` has complex
multiplication by `χ`, then `a_𝔭 = 0` for every prime `𝔭 ∤ 𝔑` prime to the modulus with
`χ(𝔭) ≠ 1`, in particular with `χ(𝔭) = -1`. -/
lemma HasCMBy.heckeIdealEigenvalue_eq_zero (h : hψ.HasCMBy χ) (𝔭 : (Ideal (𝓞 F))⁰)
    (h𝔭 : (𝔭 : Ideal (𝓞 F)).IsPrime) (h𝔑 : (𝔭 : Ideal (𝓞 F)) ⊔ 𝔑 = ⊤)
    (h𝔪 : (𝔭 : Ideal (𝓞 F)) ∈ integralIdealsPrimeTo 𝔪)
    (hχ : (χ (integralIdealsAwayHom F 𝔪.support ⟨𝔭, h𝔪⟩) : ℂ) ≠ 1) :
    heckeIdealEigenvalue 𝔭 hψ h𝔑 = 0 :=
  (mul_left_eq_self₀.mp (h.2.2 𝔭 h𝔭 h𝔑 h𝔪).symm).resolve_left hχ

end HilbertModularForm.IsHeckeIdealEigenform
