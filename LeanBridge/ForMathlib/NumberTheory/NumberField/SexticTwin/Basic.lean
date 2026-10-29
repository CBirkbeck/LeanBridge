import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.IsSepClosed
import LeanBridge.ForMathlib.NumberTheory.NumberField.SexticTwin.OuterAutomorphism

/-!
# Twin sextic algebras

A finite separable algebra `A` over a field `F` (an étale `F`-algebra) is determined up to
isomorphism by its Galois set, the finite set `Hom_F(A, F^sep)` of `F`-algebra maps to a separable
closure, on which `Gal(F^sep/F)` acts by composition (Tau Ceti's
`Algebra.Etale.algHomEquivMulActionHom`). Conversely, a finite set `X` with a continuous action
`ρ : Gal(F^sep/F) → Perm X` is the Galois set of the `F`-algebra of maps `f : X → F^sep` with
`f (ρ σ x) = σ (f x)` (`Algebra.bijective_evalGaloisSetAlgebra`).

For `A` of degree `6`, labelling `Hom_F(A, F^sep)` by `{0, …, 5}` makes the Galois action a
homomorphism `ρ_A : Gal(F^sep/F) → S₆`, well defined up to conjugation in `S₆`. Twisting it by the
outer automorphism `θ` of `S₆` (`Equiv.Perm.outerAutFinSix`) gives another Galois set with six
elements, that of the *twin* `B` of `A`. Another labelling of the Galois set of `A` conjugates
`ρ_A`, hence `θ ∘ ρ_A`, and so only relabels the Galois set of `B`; and as `θ` is unique up to inner
automorphisms, twins do not depend on the choice of `θ` (`Algebra.isSexticTwin_iff_of_isOuter`).
Every finite separable algebra of degree `6` has a twin, unique up to isomorphism
(`Algebra.exists_isSexticTwin`, `Algebra.IsSexticTwin.nonempty_algEquiv`).

The Galois sets and their algebras are defined over any extension `Ω` of `F`; the LMFDB's twins
use the separable closure `Ω = F^sep`.

## Main definitions

* `Algebra.galoisSetPerm`: the action of `Gal(Ω/F)` on the Galois set `Hom_F(A, Ω)` of an
  `F`-algebra `A`.
* `Algebra.IsSexticTwin` (LMFDB `nf.sextic_twin`): `B` is a twin of `A`, their Galois actions
  being related by `θ` once their Galois sets are labelled by `{0, …, 5}`.
* `Algebra.galoisSetAlgebra`: the `F`-algebra of a Galois set.
* `Algebra.sexticTwin` (LMFDB `nf.sextic_twin`): the twin of `A`, the `F`-algebra of the Galois
  set of `A` twisted by `θ`.

## Main results

* `Algebra.IsSexticTwin.symm`: `A` is a twin of its twins, since `θ` is an involution.
* `Algebra.isSexticTwin_iff_of_isOuter`: twins can be defined with any outer automorphism of `S₆`.
* `Algebra.galoisSetPerm_evalGaloisSetAlgebra`: the evaluations at the points of a Galois set `X`
  are elements of the Galois set of its algebra, permuted by `Gal(Ω/F)` as the points of `X` are.
-/

open Equiv Perm

lemma Equiv.permCongr_trans_eq_mul {α β : Type*} (e : α ≃ β) (g : Perm β) (p : Perm α) :
    (e.trans g).permCongr p = g * e.permCongr p * g⁻¹ :=
  rfl

namespace Algebra

variable (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] (A B : Type*) [CommRing A] [Algebra F A]
  [CommRing B] [Algebra F B] (σ : Gal(Ω/F))

/-- The **Galois set** of an `F`-algebra `A` (LMFDB `nf.sextic_twin`): the action of `Gal(Ω/F)`
on the `F`-algebra maps `A → Ω`, `σ` sending `f` to `σ ∘ f` (Tau Ceti's postcomposition action
`AlgEquiv.mulActionAlgHom`, as a homomorphism to permutations). The Galois set of the LMFDB is that
for the separable closure `Ω = F^sep`. -/
def galoisSetPerm : Gal(Ω/F) →* Perm (A →ₐ[F] Ω) where
  toFun τ := AlgEquiv.refl.arrowCongr τ
  map_one' := rfl
  map_mul' _ _ := rfl

lemma galoisSetPerm_apply_apply (f : A →ₐ[F] Ω) (a : A) : galoisSetPerm F Ω A σ f a = σ (f a) :=
  rfl

/-- An `F`-algebra `B` is a **twin** (LMFDB `nf.sextic_twin`) of an `F`-algebra `A` if their
Galois sets can be labelled by `{0, …, 5}` so that, for every `σ ∈ Gal(F^sep/F)`, the permutation
of the labels induced by `σ` on the Galois set of `B` is the image under the outer automorphism
`θ` of `S₆` of that induced on the Galois set of `A`. The LMFDB's twins are finite separable
algebras: for finite separable `A` and `B`, which then have degree `6`, this is its relation, and
`B` is unique up to isomorphism (`Algebra.IsSexticTwin.nonempty_algEquiv`). The definition itself
does not ask `A` or `B` to be separable. -/
def IsSexticTwin : Prop :=
  ∃ (eA : (A →ₐ[F] SeparableClosure F) ≃ Fin 6) (eB : (B →ₐ[F] SeparableClosure F) ≃ Fin 6), ∀ τ,
    eB.permCongr (galoisSetPerm F _ B τ) = outerAutFinSix (eA.permCongr (galoisSetPerm F _ A τ))

variable {F Ω A B}

/-- **`A` is a twin of its twins**, since the outer automorphism `θ` of `S₆` is an involution. -/
lemma IsSexticTwin.symm (h : IsSexticTwin F A B) : IsSexticTwin F B A := by
  rcases h with ⟨eA, eB, h⟩
  exact ⟨eB, eA, fun τ ↦ by rw [h τ, outerAutFinSix_outerAutFinSix]⟩

/-- **Twins do not depend on the choice of the outer automorphism of `S₆`**: for any outer
automorphism `φ` of `S₆`, `B` is a twin of `A` exactly when the Galois sets of `A` and `B` can be
labelled so that their Galois actions are related by `φ`, since `φ` is `θ` composed with an inner
automorphism (`Equiv.Perm.exists_eq_outerAutFinSix_mul_conj`). -/
lemma isSexticTwin_iff_of_isOuter {φ : MulAut (Perm (Fin 6))} (hφ : φ.IsOuter) :
    IsSexticTwin F A B ↔ ∃ (eA : (A →ₐ[F] SeparableClosure F) ≃ Fin 6)
      (eB : (B →ₐ[F] SeparableClosure F) ≃ Fin 6), ∀ τ,
        eB.permCongr (galoisSetPerm F _ B τ) = φ (eA.permCongr (galoisSetPerm F _ A τ)) := by
  rcases exists_eq_outerAutFinSix_mul_conj hφ with ⟨g, rfl⟩
  constructor
  · rintro ⟨eA, eB, h⟩
    refine ⟨eA.trans g⁻¹, eB, fun τ ↦ ?_⟩
    rw [h τ, MulAut.mul_apply, MulAut.conj_apply, permCongr_trans_eq_mul]
    group
  · rintro ⟨eA, eB, h⟩
    exact ⟨eA.trans g, eB, fun τ ↦ by
      rw [h τ, MulAut.mul_apply, MulAut.conj_apply, permCongr_trans_eq_mul]⟩

variable {X : Type*} (ρ : Gal(Ω/F) →* Perm X) (x : X)

/-- The **`F`-algebra of a Galois set** `X` with Galois action `ρ` of `Gal(Ω/F)`: the `F`-algebra
of maps `f : X → Ω` with `f (ρ τ y) = τ (f y)` for all `τ ∈ Gal(Ω/F)`. For a Galois extension
`Ω / F` and a finite `X` with a continuous action, it is the finite separable `F`-algebra whose
Galois set is `X`, the evaluations at the points of `X` (`evalGaloisSetAlgebra`) being its
`F`-algebra maps to `Ω`. -/
def galoisSetAlgebra : Subalgebra F (X → Ω) where
  carrier := {f | ∀ τ y, f (ρ τ y) = τ (f y)}
  mul_mem' hf hg τ y := by rw [Pi.mul_apply, Pi.mul_apply, hf, hg, map_mul]
  add_mem' hf hg τ y := by rw [Pi.add_apply, Pi.add_apply, hf, hg, map_add]
  algebraMap_mem' r τ _ := (τ.commutes r).symm

lemma mem_galoisSetAlgebra {f : X → Ω} : f ∈ galoisSetAlgebra ρ ↔ ∀ τ y, f (ρ τ y) = τ (f y) :=
  Iff.rfl

/-- The evaluation at a point `x` of a Galois set `X`, an `F`-algebra map from the `F`-algebra of
`X` to `Ω`. -/
def evalGaloisSetAlgebra : galoisSetAlgebra ρ →ₐ[F] Ω :=
  (Pi.evalAlgHom F (fun _ ↦ Ω) x).comp (galoisSetAlgebra ρ).val

lemma evalGaloisSetAlgebra_apply (f : galoisSetAlgebra ρ) : evalGaloisSetAlgebra ρ x f = f.1 x :=
  rfl

/-- **The Galois group permutes the evaluations at the points of a Galois set `X` as it permutes
the points of `X`**: `σ ∘ ev_x = ev_{ρ(σ)(x)}`. -/
lemma galoisSetPerm_evalGaloisSetAlgebra :
    galoisSetPerm F Ω _ σ (evalGaloisSetAlgebra ρ x) = evalGaloisSetAlgebra ρ (ρ σ x) :=
  AlgHom.ext fun f ↦ (f.2 σ x).symm

variable (e : (A →ₐ[F] SeparableClosure F) ≃ Fin 6)

/-- The Galois action `θ ∘ ρ_A` on `{0, …, 5}` (LMFDB `nf.sextic_twin`) for an `F`-algebra `A`
whose Galois set is labelled by `e`: the labelled Galois action `ρ_A τ = e ∘ (τ ∘ ·) ∘ e⁻¹` on `A`
twisted by the outer automorphism `θ` of `S₆`. -/
noncomputable def sexticTwinPerm : Gal(SeparableClosure F/F) →* Perm (Fin 6) :=
  outerAutFinSix.toMonoidHom.comp (e.permCongrHom.toMonoidHom.comp (galoisSetPerm F _ A))

lemma sexticTwinPerm_apply (τ : Gal(SeparableClosure F/F)) :
    sexticTwinPerm e τ = outerAutFinSix (e.permCongr (galoisSetPerm F _ A τ)) :=
  rfl

/-- The **twin** (LMFDB `nf.sextic_twin`) of an `F`-algebra `A` whose Galois set is labelled by
`e`: the `F`-algebra of the Galois set `{0, …, 5}` with the Galois action `θ ∘ ρ_A`
(`sexticTwinPerm`), where `ρ_A` is the labelled Galois action on `A` and `θ` is the outer
automorphism of `S₆`. For a finite `A` it is a finite separable algebra and a twin of `A`
(`Algebra.etale_sexticTwin`, `Algebra.isSexticTwin_sexticTwin`), so that another labelling gives
an isomorphic algebra (`Algebra.IsSexticTwin.nonempty_algEquiv`). -/
noncomputable def sexticTwin : Subalgebra F (Fin 6 → SeparableClosure F) :=
  galoisSetAlgebra (sexticTwinPerm e)

end Algebra
