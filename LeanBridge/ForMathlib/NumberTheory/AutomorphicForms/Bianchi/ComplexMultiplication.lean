import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.Newform
import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Basic

/-!
# Bianchi newforms with complex multiplication

A Bianchi newform `F` of level `𝔑` over an imaginary quadratic field `K` has **complex
multiplication** (LMFDB `mf.bianchi.cm`) if it is equal to its own twist by a nontrivial Hecke
character `χ` of `K`, which is then of finite order, indeed quadratic. As the knowl says, this is
characterised by the Hecke eigenvalues: `a_𝔭 = χ(𝔭) a_𝔭` for the primes `𝔭 ∤ 𝔑`, so that
`a_𝔭 = 0` whenever `χ(𝔭) = -1`. The Hecke characters of finite order are the ray class characters
(Tau Ceti's `RayClassCharacter`), which are only defined at the ideals prime to their modulus; the
condition is imposed at the primes `𝔭 ∤ 𝔑` prime to the modulus, that is at all but finitely many
primes, which is what equality with the twist means by strong multiplicity one.

## Main definitions

* `HyperbolicThreeSpace.BianchiNewform.HasCMBy` (LMFDB `mf.bianchi.cm`): `F` has complex
  multiplication by the character `χ`.
* `HyperbolicThreeSpace.BianchiNewform.HasCM` (LMFDB `mf.bianchi.cm`): `F` has complex
  multiplication.

## Main results

* `HyperbolicThreeSpace.BianchiNewform.HasCMBy.eigenvalue_eq_zero`: the eigenvalues of a CM newform
  vanish at the primes where its character is `-1`.
-/

open NumberField TauCeti GlobalNumberFields

namespace HyperbolicThreeSpace.BianchiNewform

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K] [IsPrincipalIdealRing (𝓞 K)]
  {σ : K →+* ℂ} {𝔑 : Ideal (𝓞 K)} [NeZero 𝔑] (F : BianchiNewform σ 𝔑) {𝔪 : Modulus K}
  (χ : RayClassCharacter 𝔪)

/-- A Bianchi newform `F` of level `𝔑` has **complex multiplication by** a nontrivial ray class
character `χ` of `K` (LMFDB `mf.bianchi.cm`), a Hecke character of finite order: `F` equals its
twist by `χ`, that is `a_𝔭 = χ(𝔭) a_𝔭` for every prime `𝔭 ∤ 𝔑` prime to the modulus of `χ`. -/
def HasCMBy : Prop :=
  χ ≠ 1 ∧ ∀ (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (h𝔭 : 𝔭.1 ∈ integralIdealsPrimeTo 𝔪),
    ¬𝔑 ≤ 𝔭.1 → F.eigenvalue 𝔭 = (χ.onIdeals ⟨𝔭.1, h𝔭⟩ : ℂ) * F.eigenvalue 𝔭

/-- A Bianchi newform has **complex multiplication**, or **CM** (LMFDB `mf.bianchi.cm`), if it is
equal to its own twist by a nontrivial Hecke character of `K`, necessarily of finite order: it has
complex multiplication by a nontrivial ray class character of some modulus. -/
def HasCM : Prop :=
  ∃ (𝔪 : Modulus K) (χ : RayClassCharacter 𝔪), F.HasCMBy χ

variable {F χ}

/-- **The eigenvalues of a CM newform vanish at the inert primes of its character**: if `F` has
complex multiplication by `χ`, then `a_𝔭 = 0` for every prime `𝔭 ∤ 𝔑` with `χ(𝔭) = -1`. -/
lemma HasCMBy.eigenvalue_eq_zero (hF : F.HasCMBy χ) (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (h𝔭 : 𝔭.1 ∈ integralIdealsPrimeTo 𝔪) (h𝔑 : ¬𝔑 ≤ 𝔭.1) (hχ : (χ.onIdeals ⟨𝔭.1, h𝔭⟩ : ℂ) = -1) :
    F.eigenvalue 𝔭 = 0 :=
  CharZero.eq_neg_self_iff.mp <| (hF.2 𝔭 h𝔭 h𝔑).trans <| by rw [hχ, neg_one_mul]

end HyperbolicThreeSpace.BianchiNewform
