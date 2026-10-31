import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.ClassGroupHecke
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.ComplexMultiplication
import LeanBridge.ForMathlib.NumberTheory.NumberField.HeckeIdealCharacter

/-!
# Bianchi newforms of every weight with complex multiplication

A Bianchi newform `F` of level `𝔑` over an imaginary quadratic field `K` has **complex
multiplication** (LMFDB `mf.bianchi.cm`) if it is equal to its own twist by a nontrivial Hecke
character `χ` of `K`. As the knowl says, this is characterised by the Hecke eigenvalues:
`a_𝔭 = χ(𝔭) a_𝔭` for the primes `𝔭 ∤ 𝔑`, so that `a_𝔭 = 0` whenever `χ(𝔭) ≠ 1`, in particular when
`χ(𝔭) = -1`; the twist itself, the newform with the eigenvalues `χ(𝔭) a_𝔭`, is not constructed.

The Hecke characters are those of LMFDB `character.hecke` (`IsIdealHeckeCharacter`): characters
`χ : I(𝔪) → ℂˣ` of the fractional ideals prime to a modulus `𝔪`, of any order, with an infinity
type. They are only defined at the ideals prime to `𝔪`, so the condition is imposed at the primes
`𝔭 ∤ 𝔑` prime to `𝔪`, that is at all but finitely many primes, which is what equality with the twist
means by strong multiplicity one; for a CM newform the conductor of `χ` divides `𝔑`. That `χ` is
then quadratic, as the knowl states, is a theorem not proved here.

The newforms are those of every weight `k` of `BianchiNewformOfWeight` (class number `1`, as the
LMFDB assumes), with their eigenvalues `a_𝔭` in the arithmetic normalisation; the condition does not
depend on the normalisation. In weight `2` it extends ZH1's `BianchiNewform.HasCMBy`, whose
characters are the ray class characters `ψ`, the Hecke characters `ψ ∘ rayClassMk` of finite order.
For fields of any class number, the same notion is defined for the Hecke eigenforms of
`IsBianchiHeckeEigenform` on the tuples of Bianchi modular forms indexed by the class group, whose
eigenvalues `a_𝔭` are defined at every prime `𝔭 ∤ 𝔑`, principal or not. These include every Bianchi
newform, and the definition for them does not involve the Fourier–Bessel normalisation on which
`BianchiNewformOfWeight` rests in weight `k > 2` (facts not proved here).

## Main definitions

* `HyperbolicThreeSpace.BianchiNewformOfWeight.HasCMBy` (LMFDB `mf.bianchi.cm`): a Bianchi newform
  of weight `k` has complex multiplication by the Hecke character `χ`.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.HasCM` (LMFDB `mf.bianchi.cm`): a Bianchi newform of
  weight `k` has complex multiplication.
* `HyperbolicThreeSpace.IsBianchiHeckeEigenform.HasCMBy` and
  `HyperbolicThreeSpace.IsBianchiHeckeEigenform.HasCM` (LMFDB `mf.bianchi.cm`): the same for the
  Hecke eigenforms over fields of any class number.

## Main results

* `TauCeti.GlobalNumberFields.RayClassCharacter.isIdealHeckeCharacter_comp_rayClassMk`: a ray
  class character is a Hecke character.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.HasCMBy.eigenvalue_eq_zero` and
  `HyperbolicThreeSpace.IsBianchiHeckeEigenform.HasCMBy.eigenvalue_eq_zero`: the eigenvalues
  vanish at the primes `𝔭` with `χ(𝔭) ≠ 1`, in particular where `χ(𝔭) = -1`.
* `HyperbolicThreeSpace.BianchiNewform.hasCMBy_toBianchiNewformOfWeight_iff` and
  `HyperbolicThreeSpace.BianchiNewform.HasCM.toBianchiNewformOfWeight`: in weight `2`, complex
  multiplication by a ray class character is that of `BianchiNewform.HasCMBy`.
-/

open NumberField TauCeti GlobalNumberFields NumberFieldArithmetic

open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable (ψ : RayClassCharacter 𝔪)

/-- **A ray class character is a Hecke character** (LMFDB `character.hecke`): the character
`ψ ∘ rayClassMk : I(𝔪) → ℂˣ` of a ray class character `ψ` is trivial on the principal ideals of
the elements congruent to one modulo `𝔪`, so it is a Hecke character modulo `𝔪` with trivial
characters at the infinite places. -/
lemma isIdealHeckeCharacter_comp_rayClassMk : IsIdealHeckeCharacter 𝔪 (ψ.comp (rayClassMk 𝔪)) :=
  ⟨fun _ ↦ 1, fun x hx ↦ by
    rw [MonoidHom.comp_apply, rayClassMk_eq_one_iff.mpr (mem_ray_iff.mpr ⟨x, hx, rfl⟩), map_one]
    simp⟩

lemma comp_rayClassMk_eq_one_iff : ψ.comp (rayClassMk 𝔪) = 1 ↔ ψ = 1 := by
  rw [← MonoidHom.one_comp (rayClassMk 𝔪)]
  exact MonoidHom.cancel_right (rayClassMk_surjective 𝔪)

end TauCeti.GlobalNumberFields.RayClassCharacter

namespace HyperbolicThreeSpace

variable {σ : K →+* ℂ} {k : ℕ} {𝔑 : Ideal (𝓞 K)} [NeZero 𝔑] (χ : idealsPrimeTo 𝔪 →* ℂˣ)

namespace BianchiNewformOfWeight

variable [IsTotallyComplex K] [IsPrincipalIdealRing (𝓞 K)] (F : BianchiNewformOfWeight σ k 𝔑)

/-- A Bianchi newform `F` of weight `k` and level `𝔑` has **complex multiplication by** the Hecke
character `χ : I(𝔪) → ℂˣ` of `K` (LMFDB `mf.bianchi.cm`, `character.hecke`) if `χ` is a nontrivial
Hecke character modulo `𝔪` and `F` equals its twist by `χ`: `a_𝔭 = χ(𝔭) a_𝔭` for every prime
`𝔭 ∤ 𝔑` prime to `𝔪`, where `a_𝔭` is the eigenvalue of the arithmetic Hecke operator `T_𝔭`. -/
def HasCMBy : Prop :=
  IsIdealHeckeCharacter 𝔪 χ ∧ χ ≠ 1 ∧ ∀ (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (h𝔭 : 𝔭.1 ∈ integralIdealsPrimeTo 𝔪), ¬𝔑 ≤ 𝔭.1 →
      F.eigenvalue 𝔭 = (χ (integralIdealsAwayHom K 𝔪.support ⟨𝔭.1, h𝔭⟩) : ℂ) * F.eigenvalue 𝔭

/-- A Bianchi newform of weight `k` has **complex multiplication**, or **CM** (LMFDB
`mf.bianchi.cm`), if it is equal to its own twist by a nontrivial Hecke character of `K`: it has
complex multiplication by a nontrivial Hecke character modulo some modulus `𝔪`. -/
def HasCM : Prop :=
  ∃ (𝔪 : Modulus K) (χ : idealsPrimeTo 𝔪 →* ℂˣ), F.HasCMBy χ

variable {F χ}

/-- **The eigenvalues of a CM newform vanish where its character is not `1`**: if `F` has complex
multiplication by `χ`, then `a_𝔭 = 0` for every prime `𝔭 ∤ 𝔑` prime to the modulus with
`χ(𝔭) ≠ 1`, in particular with `χ(𝔭) = -1`. -/
lemma HasCMBy.eigenvalue_eq_zero (hF : F.HasCMBy χ) (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (h𝔭 : 𝔭.1 ∈ integralIdealsPrimeTo 𝔪) (h𝔑 : ¬𝔑 ≤ 𝔭.1)
    (hχ : (χ (integralIdealsAwayHom K 𝔪.support ⟨𝔭.1, h𝔭⟩) : ℂ) ≠ 1) : F.eigenvalue 𝔭 = 0 :=
  (mul_left_eq_self₀.mp (hF.2.2 𝔭 h𝔭 h𝔑).symm).resolve_left hχ

end BianchiNewformOfWeight

namespace BianchiNewform

variable [IsTotallyComplex K] [IsPrincipalIdealRing (𝓞 K)] {F : BianchiNewform σ 𝔑}
  {ψ : RayClassCharacter 𝔪}

variable (F ψ) in
/-- **In weight `2`, complex multiplication by a ray class character is that of
`BianchiNewform.HasCMBy`**: a Bianchi newform of weight `2` has complex multiplication by the Hecke
character `ψ ∘ rayClassMk` of a ray class character `ψ` exactly when it has complex multiplication
by `ψ` in the sense of ZH1, whose characters are the Hecke characters of finite order. -/
lemma hasCMBy_toBianchiNewformOfWeight_iff :
    F.toBianchiNewformOfWeight.HasCMBy (ψ.comp (rayClassMk 𝔪)) ↔ F.HasCMBy ψ :=
  ⟨fun h ↦ ⟨fun h' ↦ h.2.1 (ψ.comp_rayClassMk_eq_one_iff.mpr h'), h.2.2⟩,
    fun h ↦ ⟨ψ.isIdealHeckeCharacter_comp_rayClassMk,
      fun h' ↦ h.1 (ψ.comp_rayClassMk_eq_one_iff.mp h'), h.2⟩⟩

/-- **A Bianchi newform of weight `2` with complex multiplication in the sense of ZH1 has complex
multiplication** as a newform of weight `2`. -/
lemma HasCM.toBianchiNewformOfWeight (h : F.HasCM) : F.toBianchiNewformOfWeight.HasCM := by
  rcases h with ⟨𝔪, ψ, h⟩
  exact ⟨𝔪, ψ.comp (rayClassMk 𝔪), (hasCMBy_toBianchiNewformOfWeight_iff F ψ).mpr h⟩

end BianchiNewform

namespace IsBianchiHeckeEigenform

variable {𝔟 : NarrowClassGroup K → (FractionalIdeal (𝓞 K)⁰ K)ˣ} {Φ : bianchiClassGroupForms σ k 𝔑 𝔟}
  (hΦ : IsBianchiHeckeEigenform Φ)

/-- A Hecke eigenform `Φ` of weight `k` and level `𝔑` over an imaginary quadratic field `K` of any
class number has **complex multiplication by** the Hecke character `χ : I(𝔪) → ℂˣ` of `K` (LMFDB
`mf.bianchi.cm` for class number `1`, `character.hecke`) if `χ` is a nontrivial Hecke character
modulo `𝔪` and `a_𝔭 = χ(𝔭) a_𝔭` for every prime `𝔭 ∤ 𝔑` prime to `𝔪`, principal or not, where
`a_𝔭` is the eigenvalue of the arithmetic Hecke operator `T_𝔭`. -/
def HasCMBy : Prop :=
  IsIdealHeckeCharacter 𝔪 χ ∧ χ ≠ 1 ∧
    ∀ (𝔭 : {𝔭 : (Ideal (𝓞 K))⁰ // (𝔭 : Ideal (𝓞 K)).IsPrime ∧ ¬𝔑 ≤ 𝔭})
      (h𝔭 : (𝔭.1 : Ideal (𝓞 K)) ∈ integralIdealsPrimeTo 𝔪), hΦ.eigenvalue 𝔭 =
        (χ (integralIdealsAwayHom K 𝔪.support ⟨𝔭.1, h𝔭⟩) : ℂ) * hΦ.eigenvalue 𝔭

/-- A Hecke eigenform over an imaginary quadratic field of any class number has **complex
multiplication**, or **CM** (LMFDB `mf.bianchi.cm` for class number `1`), if it has complex
multiplication by a nontrivial Hecke character modulo some modulus `𝔪`. -/
def HasCM : Prop :=
  ∃ (𝔪 : Modulus K) (χ : idealsPrimeTo 𝔪 →* ℂˣ), hΦ.HasCMBy χ

variable {hΦ χ}

/-- **The eigenvalues of a CM eigenform vanish where its character is not `1`**: if `Φ` has complex
multiplication by `χ`, then `a_𝔭 = 0` for every prime `𝔭 ∤ 𝔑` prime to the modulus with
`χ(𝔭) ≠ 1`, in particular with `χ(𝔭) = -1`. -/
lemma HasCMBy.eigenvalue_eq_zero (h : hΦ.HasCMBy χ)
    (𝔭 : {𝔭 : (Ideal (𝓞 K))⁰ // (𝔭 : Ideal (𝓞 K)).IsPrime ∧ ¬𝔑 ≤ 𝔭})
    (h𝔭 : (𝔭.1 : Ideal (𝓞 K)) ∈ integralIdealsPrimeTo 𝔪)
    (hχ : (χ (integralIdealsAwayHom K 𝔪.support ⟨𝔭.1, h𝔭⟩) : ℂ) ≠ 1) : hΦ.eigenvalue 𝔭 = 0 :=
  (mul_left_eq_self₀.mp (h.2.2 𝔭 h𝔭).symm).resolve_left hχ

end IsBianchiHeckeEigenform

end HyperbolicThreeSpace
