import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.BaseChange

/-!
# Base changes are invariant under the automorphisms of the field

Let `K ⊇ F` be a finite extension of number fields and `g` a modular form on `GL(2)` over `K` which
is a base change of a modular form `f` on `GL(2)` over `F` (LMFDB `mf.base_change`): its good Euler
factors are `L_𝔮(g, T) = L_𝔭^{(r)}(f, T)` for all but finitely many primes `𝔮` of `K`, where `𝔮`
lies over `𝔭 ∤ 𝔑` and `r` is the residue degree of `𝔮` over `𝔭`. An automorphism `τ` of `𝒪_K` over
`𝒪_F` permutes the primes above each `𝔭` and preserves their residue degrees, so
`L_{τ(𝔮)}(g, T) = L_𝔮(g, T)` for almost all `𝔮`; comparing the coefficients of `T`,
`a_{τ(𝔮)}(g) = a_𝔮(g)`. This is the consequence that the knowl states for base changes from `ℚ`,
for all `τ ∈ Aut(K)`; as the relation only holds at almost all primes, so does its consequence.
As in `NumberField.IsBaseChangeOfEulerFactors`, it is stated on the families of good Euler factors.

## Main results

* `NumberField.IsBaseChangeOfEulerFactors.eventually_smul_eq` (LMFDB `mf.base_change`): the Euler
  factors of a base change are invariant under the automorphisms of `𝒪_K` over `𝒪_F`, at almost
  all primes.
-/

open Polynomial

open scoped Pointwise

namespace NumberField

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {𝔑 : Ideal (𝓞 F)}
  {Lf : Ideal (𝓞 F) → ℂ[X]} {Lg : Ideal (𝓞 K) → ℂ[X]} {G : Type*} [Group G]
  [MulSemiringAction G (𝓞 K)] [SMulCommClass G (𝓞 F) (𝓞 K)]

/-- **The Euler factors of a base change are invariant under the automorphisms of the field**
(LMFDB `mf.base_change`): if the family `Lg` of good Euler factors over `K` is a base change of the
family `Lf` over `F`, then `L_{τ(𝔮)}(g, T) = L_𝔮(g, T)`, hence `a_{τ(𝔮)}(g) = a_𝔮(g)`, for almost
all primes `𝔮` of `K` and every automorphism `τ` of `𝒪_K` over `𝒪_F`, given by the action of a
group `G` such as `Aut(K / F)`. -/
lemma IsBaseChangeOfEulerFactors.eventually_smul_eq (h : IsBaseChangeOfEulerFactors 𝔑 Lf Lg)
    (g : G) : ∀ᶠ 𝔮 in Filter.cofinite, 𝔮.IsPrime → 𝔮 ≠ ⊥ →
      ¬𝔑 ≤ 𝔮.comap (algebraMap (𝓞 F) (𝓞 K)) → Lg (g • 𝔮) = Lg 𝔮 := by
  filter_upwards [h, (MulAction.injective g).tendsto_cofinite.eventually h] with 𝔮 h₁ h₂ h𝔮 h𝔮₀ h𝔑
  have hu : (g • 𝔮).comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔮.comap (algebraMap (𝓞 F) (𝓞 K)) :=
    Ideal.under_smul (𝓞 F) 𝔮 g
  have hp : (g • 𝔮).IsPrime := by
    rw [Ideal.pointwise_smul_eq_comap]
    exact Ideal.comap_isPrime _ _
  have h₀ : g • 𝔮 ≠ ⊥ := fun h ↦ h𝔮₀ <| by
    rw [← inv_smul_smul g 𝔮, h, Ideal.smul_bot]
  rw [h₂ hp h₀ (hu ▸ h𝔑), h₁ h𝔮 h𝔮₀ h𝔑, hu, Ideal.inertiaDeg_smul]

end NumberField
