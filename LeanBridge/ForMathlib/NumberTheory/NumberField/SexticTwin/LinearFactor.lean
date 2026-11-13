import Mathlib.FieldTheory.Galois.Infinite
import LeanBridge.ForMathlib.NumberTheory.NumberField.SexticTwin.Resolvent

/-!
# Twin sextic algebras with a factor `F`

Let `B` be a twin of a sextic algebra `A` over a field `F` (LMFDB `nf.sextic_twin`): once the
Galois sets of `A` and `B` are labelled by `{0, …, 5}`, an element `τ` of `Gal(F^sep/F)` permutes
the Galois set of `B` by `θ(ρ_A(τ))`, where `ρ_A(τ)` is the permutation of the Galois set of `A` by
`τ` and `θ` is the outer automorphism of `S₆`. By Galois descent the factors of a finite separable
`B` correspond to the orbits of `Gal(F^sep/F)` on its Galois set, each factor being the fixed field
of the stabilizer of a point of its orbit, of degree the size of the orbit
(`Algebra.galoisSetAlgebraEquivPi`), so the factorization of `B` reflects the Galois action on
`A`.

The simplest instance: `B` has `F` as a factor, that is an `F`-algebra map `B → F`, if and only if
the Galois action on `A`, for a suitable labelling of its Galois set, lies in the copy of
`PGL₂(𝔽₅)` in `S₆` given by its action on the projective line `ℙ¹(𝔽₅)`
(`Equiv.Perm.pglTwoFiveToPerm`), the image of the stabilizer `S₅` of a point under `θ`. Indeed an
`F`-algebra map `B → F` is a point of the Galois set of `B` fixed by `Gal(F^sep/F)`, as the field
fixed by `Gal(F^sep/F)` is `F`, and `θ(σ)` fixes the point `5` exactly when `σ` lies in the image of
`PGL₂(𝔽₅)`. Such a twin is not a field: a field `B` with an `F`-algebra map to `F` is `F` itself,
which has one `F`-algebra map to `F^sep`, not six.

## Main results

* `Algebra.IsSexticTwin.nonempty_algHom_iff` (LMFDB `nf.sextic_twin`): a twin `B` of `A` has an
  `F`-algebra map to `F` if and only if the Galois action on `A` lies in `PGL₂(𝔽₅)` for some
  labelling of its Galois set.
* `Algebra.IsSexticTwin.not_isField_of_algHom` (LMFDB `nf.sextic_twin`): a twin with an
  `F`-algebra map to `F` is not a field.
-/

open Equiv Perm

namespace Algebra

variable {F A B : Type*} [Field F] [CommRing A] [Algebra F A] [CommRing B] [Algebra F B]

lemma IsSexticTwin.exists_forall_galoisSetPerm_eq (h : IsSexticTwin F A B)
    (e : (A →ₐ[F] SeparableClosure F) ≃ Fin 6) {p : Fin 6} (hp : ∀ τ, sexticTwinPerm e τ p = p) :
    ∃ ψ : B →ₐ[F] SeparableClosure F, ∀ τ, galoisSetPerm F _ B τ ψ = ψ := by
  rcases h with ⟨eA, eB, h⟩
  let g : Perm (Fin 6) := eA.symm.trans e
  have he : eA.trans g = e := by
    rw [← trans_assoc, self_trans_symm, refl_trans]
  refine ⟨eB.symm ((outerAutFinSix g)⁻¹ p), fun τ ↦ eB.injective ?_⟩
  have hτ : sexticTwinPerm e τ p = p := hp τ
  rw [sexticTwinPerm_apply, ← he, permCongr_trans_eq_mul, map_mul, map_mul, map_inv, mul_apply,
    mul_apply] at hτ
  rw [apply_symm_apply, ← permCongr_apply, h τ]
  exact eq_inv_iff_eq.mpr hτ

lemma nonempty_algHom_of_forall_galoisSetPerm_eq {ψ : B →ₐ[F] SeparableClosure F}
    (hψ : ∀ τ, galoisSetPerm F _ B τ ψ = ψ) : Nonempty (B →ₐ[F] F) :=
  ⟨(IntermediateField.botEquiv F _).toAlgHom.comp <|
    ψ.codRestrict (⊥ : IntermediateField F _).toSubalgebra fun b ↦
      (InfiniteGalois.mem_bot_iff_fixed _).mpr fun τ ↦
        (galoisSetPerm_apply_apply F _ B τ ψ b).symm.trans (DFunLike.congr_fun (hψ τ) b)⟩

/-- **A twin `B` of `A` has a factor `F` if and only if the Galois action on `A` lies in
`PGL₂(𝔽₅)`** (LMFDB `nf.sextic_twin`): `B` has an `F`-algebra map to `F` exactly when, for some
labelling of the Galois set of `A` by `{0, …, 5}`, every `τ ∈ Gal(F^sep/F)` permutes it by an
element of the image of `PGL₂(𝔽₅)` acting on `ℙ¹(𝔽₅)` (`Equiv.Perm.pglTwoFiveToPerm`). The
`F`-algebra maps `B → F` are the points of the Galois set of `B` fixed by `Gal(F^sep/F)`, that is
by `θ ∘ ρ_A`, which a relabelling moves to the point `5`, and `θ(σ)` fixes `5` exactly when `σ`
lies in the image of `PGL₂(𝔽₅)`, since `θ` sends the stabilizer of `5` onto that image
(`Equiv.Perm.map_stabilizer_outerAutFinSix`) and is an involution. -/
lemma IsSexticTwin.nonempty_algHom_iff (h : IsSexticTwin F A B) : Nonempty (B →ₐ[F] F) ↔
    ∃ e : (A →ₐ[F] SeparableClosure F) ≃ Fin 6, ∀ τ, e.permCongr (galoisSetPerm F _ A τ) ∈
      pglTwoFiveToPerm.range := by
  refine ⟨fun ⟨f⟩ ↦ ?_, fun ⟨e, he⟩ ↦ ?_⟩
  · rcases h with ⟨eA, eB, h⟩
    let ψ : B →ₐ[F] SeparableClosure F := (ofId F _).comp f
    have hψ (τ : Gal(SeparableClosure F/F)) :
        outerAutFinSix (eA.permCongr (galoisSetPerm F _ A τ)) (eB ψ) = eB ψ := by
      rw [← h τ, permCongr_apply, symm_apply_apply]
      exact congrArg eB (AlgHom.ext fun b ↦ τ.commutes (f b))
    refine ⟨eA.trans (outerAutFinSix (swap (eB ψ) 5)), fun τ ↦
      (mem_range_pglTwoFiveToPerm_iff _).mpr ?_⟩
    rw [permCongr_trans_eq_mul, map_mul, map_mul, map_inv, outerAutFinSix_outerAutFinSix, swap_inv,
      mul_apply, mul_apply, swap_apply_right, hψ, swap_apply_left]
  · rcases h.exists_forall_galoisSetPerm_eq e fun τ ↦
      (mem_range_pglTwoFiveToPerm_iff _).mp (he τ) with ⟨ψ, hψ⟩
    exact nonempty_algHom_of_forall_galoisSetPerm_eq hψ

/-- **A twin with a factor `F` is not a field** (LMFDB `nf.sextic_twin`): an `F`-algebra map `f`
from a field `B` to `F` is injective, so `B` consists of the elements `algebraMap F B (f b)`, and
all `F`-algebra maps from `B` to `F^sep` agree, while a twin has six of them. -/
lemma IsSexticTwin.not_isField_of_algHom (h : IsSexticTwin F A B) (f : B →ₐ[F] F) : ¬IsField B := by
  intro hB
  have hf : Function.Injective f := (injective_iff_map_eq_zero f).mpr fun b hb ↦
    by_contra fun hb0 ↦ by
      rcases hB.mul_inv_cancel hb0 with ⟨b', hbb'⟩
      simpa [hb] using congrArg f hbb'
  have hall (φ : B →ₐ[F] SeparableClosure F) (b : B) : φ b = algebraMap F _ (f b) :=
    (congrArg φ (hf (f.commutes (f b)))).symm.trans (φ.commutes (f b))
  rcases h with ⟨-, eB, -⟩
  exact absurd (eB.symm.injective (AlgHom.ext fun b ↦ (hall _ b).trans (hall _ b).symm))
    (by decide : (0 : Fin 6) ≠ 1)

end Algebra
