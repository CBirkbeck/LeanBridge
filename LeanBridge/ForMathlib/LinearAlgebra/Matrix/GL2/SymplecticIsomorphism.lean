import Mathlib.LinearAlgebra.ExteriorPower.Basic
import TauCeti.RingTheory.RootsOfUnity.ZMod

/-!
# Symplectic isomorphisms

Let `N ≥ 1` and let `μ_N` be the group of `N`-th roots of unity of a field `K` (algebraically closed
of characteristic not dividing `N` in the LMFDB), a `ℤ/Nℤ`-module when written additively
(`TauCeti.instModuleZModAdditiveRootsOfUnity`). A free `ℤ/Nℤ`-module `M` of rank `2` carries a
symplectic structure when it comes with an isomorphism `α : ⋀²M ≃ μ_N`, equivalently with the
nondegenerate alternating pairing `(x, y) ↦ α (x ∧ y)`; for example `E[N]` with the Weil pairing.
An isomorphism `f : M ≃ M'` is symplectic if the isomorphism `⋀²f` it induces becomes the identity
of `μ_N` through `α` and `α'`, that is, if it preserves the pairings. The variants for Galois
modules and finite étale group schemes are not formalised.

## Main definitions

* `LinearEquiv.IsSymplectic` (LMFDB `alg.symplectic_isomorphism`).

## Main results

* `LinearEquiv.isSymplectic_iff`: an isomorphism is symplectic exactly when it preserves the
  pairings `(x, y) ↦ α (x ∧ y)`.
-/

open exteriorPower

variable {N : ℕ} {K : Type*} [CommRing K]

namespace LinearEquiv

variable {M M' : Type*} [AddCommGroup M] [Module (ZMod N) M] [AddCommGroup M'] [Module (ZMod N) M']
  (f : M ≃ₗ[ZMod N] M') (α : ⋀[ZMod N]^2 M ≃ₗ[ZMod N] Additive (rootsOfUnity N K))
  (α' : ⋀[ZMod N]^2 M' ≃ₗ[ZMod N] Additive (rootsOfUnity N K))

/-- An isomorphism `f : M ≃ M'` of `ℤ/Nℤ`-modules with symplectic structures `α : ⋀²M ≃ μ_N` and
`α' : ⋀²M' ≃ μ_N` is a **symplectic isomorphism** (LMFDB `alg.symplectic_isomorphism`) if the
isomorphism `⋀²f : ⋀²M ≃ ⋀²M'` it induces is identified through `α` and `α'` with the identity of
`μ_N`, that is, if `α' ∘ ⋀²f = α`. The LMFDB uses it for free modules of rank `2`. -/
def IsSymplectic : Prop :=
  α'.toLinearMap ∘ₗ exteriorPower.map 2 f.toLinearMap = α.toLinearMap

/-- **An isomorphism is symplectic exactly when it preserves the alternating pairings**
`(x, y) ↦ α (x ∧ y)` defined by the symplectic structures. -/
lemma isSymplectic_iff : f.IsSymplectic α α' ↔ ∀ x y : M, α' (ιMulti (ZMod N) 2 ![f x, f y]) =
    α (ιMulti (ZMod N) 2 ![x, y]) := by
  have hf (x y : M) : ⇑f.toLinearMap ∘ ![x, y] = ![f x, f y] :=
    funext fun i ↦ by fin_cases i <;> rfl
  refine ⟨fun h x y ↦ ?_, fun h ↦ exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ ?_)⟩
  · have h₁ : (α'.toLinearMap ∘ₗ exteriorPower.map 2 f.toLinearMap) (ιMulti (ZMod N) 2 ![x, y]) =
        α.toLinearMap (ιMulti (ZMod N) 2 ![x, y]) :=
      LinearMap.congr_fun h (ιMulti (ZMod N) 2 ![x, y])
    rwa [LinearMap.comp_apply, exteriorPower.map_apply_ιMulti, hf] at h₁
  · have hv : v = ![v 0, v 1] := funext fun i ↦ by fin_cases i <;> rfl
    rw [hv, LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply,
      LinearMap.comp_apply, exteriorPower.map_apply_ιMulti, hf]
    exact h (v 0) (v 1)

end LinearEquiv
