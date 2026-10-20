import Mathlib.FieldTheory.Galois.Basic
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.ComplexMultiplication
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Torsion

/-!
# Level structures on elliptic curves

Let `H` be an open subgroup of `GL₂(ℤ̂)` of level `N`, and `H_N` its reduction to `GL₂(ℤ/Nℤ)`; all
the notions below depend on `H` only through `H_N`, which is therefore the datum here. For an
elliptic curve `E = W` over a field `F` with separable closure `F^s`, an `H`-level structure on `E`
is the orbit `[ι]_H = {h ∘ ι : h ∈ H_N}` of an isomorphism `ι : E[N] ≃ (ℤ/Nℤ)²`, `E[N]` being the
`N`-torsion over `F^s`. It is rational if the isomorphism class of the pair `(E, [ι]_H)` is stable
under `Gal(F^s/F)`, which acts by `(E, [ι]_H) ↦ (E^σ, [ι ∘ σ⁻¹]_H)`; as `E` is defined over `F`,
`E^σ = E`, and an isomorphism of pairs is an automorphism `φ` of `E` over `F^s`, a unit of the
geometric endomorphism ring, with `[ι ∘ σ⁻¹ ∘ φ_N]_H = [ι]_H`.

The invariants of a rational level structure are field degrees over `F`: the least degree of an
extension `L ⊆ F^s` over which `E` has a rational cyclic `N`-isogeny (equivalently, its kernel, a
cyclic subgroup of order `N` of `E[N]` stable under `Gal(F^s/L)`), or a rational point of order
`N`, or all of `E[N]`. For a curve whose mod-`N` image is `H_N`, they are the indices in `H_N` of
the largest subgroup stabilising a cyclic subgroup of order `N` of `(ℤ/Nℤ)²`, of the largest
subgroup fixing a point of order `N`, and the order of `H_N`; these group-theoretic invariants are
defined too. The LMFDB states all of this over number fields; the definitions make sense over any
field.

## Main definitions

* `WeierstrassCurve.levelStructure` (LMFDB `modcurve.level_structure`): the orbit `[ι]_H`.
* `WeierstrassCurve.torsionGeometricAutRepresentation`: the action on `E[N]` of the automorphisms of
  `W` over `F^s`, the units of the geometric endomorphism ring.
* `WeierstrassCurve.IsRationalLevelStructure` (LMFDB `modcurve.level_structure`).
* `WeierstrassCurve.cyclicIsogenyFieldDegree`, `WeierstrassCurve.cyclicTorsionFieldDegree`,
  `WeierstrassCurve.torsionFieldDegree` (LMFDB `modcurve.level_structure`): the three field
  degrees.
* `Matrix.GeneralLinearGroup.cyclicIsogenyDegree`, `Matrix.GeneralLinearGroup.cyclicTorsionDegree`
  (LMFDB `modcurve.level_structure`): the corresponding invariants of `H_N`, the third being its
  order.

## Main results

* `WeierstrassCurve.levelStructure_eq_of_mem`: the level structures through `ι` partition the
  isomorphisms `E[N] ≃ (ℤ/Nℤ)²`.
-/

open Matrix TauCeti TauCeti.Isogeny
open scoped WeierstrassCurve

namespace Matrix.GeneralLinearGroup

variable {N : ℕ} (H : Subgroup (GL (Fin 2) (ZMod N)))

/-- The stabilizer in `GL₂(ℤ/Nℤ)` of a vector `v` of `(ℤ/Nℤ)²`. -/
def vecStabilizer (v : Fin 2 → ZMod N) : Subgroup (GL (Fin 2) (ZMod N)) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ v = v}
  one_mem' := Matrix.one_mulVec v
  mul_mem' {g h} hg hh := by
    rw [Set.mem_ofPred_eq, Units.val_mul, ← Matrix.mulVec_mulVec, Set.mem_ofPred_eq.mp hh,
      Set.mem_ofPred_eq.mp hg]
  inv_mem' {g} hg := by
    rw [Set.mem_ofPred_eq]
    nth_rw 1 [← Set.mem_ofPred_eq.mp hg]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

/-- The stabilizer in `GL₂(ℤ/Nℤ)` of an additive subgroup `C` of `(ℤ/Nℤ)²`: the elements `g` with
`g(C) = C`. -/
def addSubgroupStabilizer (C : AddSubgroup (Fin 2 → ZMod N)) : Subgroup (GL (Fin 2) (ZMod N)) where
  carrier := {g | ∀ v, v ∈ C ↔ (g : Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ v ∈ C}
  one_mem' v := by rw [Units.val_one, Matrix.one_mulVec]
  mul_mem' {g h} hg hh v := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hh, hg]
  inv_mem' {g} hg v := by
    rw [hg (((g⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) *ᵥ v),
      Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

/-- The **cyclic `N`-isogeny degree** of a subgroup `H` of `GL₂(ℤ/Nℤ)` (LMFDB
`modcurve.level_structure`): the least index in `H` of the stabilizer in `H` of a cyclic subgroup of
order `N` of `(ℤ/Nℤ)²`. For a curve whose mod-`N` image is `H` it is the cyclic `N`-isogeny field
degree. -/
noncomputable def cyclicIsogenyDegree : ℕ :=
  sInf {d | ∃ C : AddSubgroup (Fin 2 → ZMod N), IsAddCyclic C ∧ Nat.card C = N ∧
    (addSubgroupStabilizer C).relIndex H = d}

/-- The **cyclic `N`-torsion degree** of a subgroup `H` of `GL₂(ℤ/Nℤ)` (LMFDB
`modcurve.level_structure`): the least index in `H` of the stabilizer in `H` of a point of order
`N` of `(ℤ/Nℤ)²`. For a curve whose mod-`N` image is `H` it is the cyclic `N`-torsion field
degree. -/
noncomputable def cyclicTorsionDegree : ℕ :=
  sInf {d | ∃ v : Fin 2 → ZMod N, addOrderOf v = N ∧ (vecStabilizer v).relIndex H = d}

end Matrix.GeneralLinearGroup

namespace WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq (SeparableClosure F)] (W : WeierstrassCurve F) (N : ℕ)
  (H : Subgroup (GL (Fin 2) (ZMod N)))
  (ι : AddSubgroup.torsionBy (W⁄(SeparableClosure F)).toAffine.Point (N : ℤ) ≃ₗ[ZMod N]
    (Fin 2 → ZMod N))

/-- The **`H`-level structure** `[ι]_H` (LMFDB `modcurve.level_structure`) through an isomorphism
`ι : E[N] ≃ (ℤ/Nℤ)²`, `E[N]` being the `N`-torsion of `W` over a separable closure: the orbit
`{h ∘ ι : h ∈ H}` of `ι` under the reduction `H ≤ GL₂(ℤ/Nℤ)` of an open subgroup of `GL₂(ℤ̂)`. -/
def levelStructure : Set
    (AddSubgroup.torsionBy (W⁄(SeparableClosure F)).toAffine.Point (N : ℤ) ≃ₗ[ZMod N]
    (Fin 2 → ZMod N)) :=
  {ι' | ∃ h ∈ H, ι' = ι.trans (GeneralLinearGroup.toLin h).toLinearEquiv}

variable {W N H ι}
  {ι' : AddSubgroup.torsionBy (W⁄(SeparableClosure F)).toAffine.Point (N : ℤ) ≃ₗ[ZMod N]
    (Fin 2 → ZMod N)}

lemma mem_levelStructure_self : ι ∈ W.levelStructure N H ι :=
  ⟨1, one_mem H, LinearEquiv.ext fun P ↦ by simp⟩

lemma trans_toLin_trans_toLin (g h : GL (Fin 2) (ZMod N)) :
    (ι.trans (GeneralLinearGroup.toLin g).toLinearEquiv).trans
    (GeneralLinearGroup.toLin h).toLinearEquiv =
    ι.trans (GeneralLinearGroup.toLin (h * g)).toLinearEquiv :=
  LinearEquiv.ext fun P ↦ by simp

/-- The level structures through `ι` **partition** the isomorphisms `E[N] ≃ (ℤ/Nℤ)²`: the level
structure through any element of `[ι]_H` is `[ι]_H`. -/
lemma levelStructure_eq_of_mem (h : ι' ∈ W.levelStructure N H ι) :
    W.levelStructure N H ι' = W.levelStructure N H ι := by
  rcases h with ⟨g, hg, rfl⟩
  ext ι''
  refine ⟨?_, ?_⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k * g, mul_mem hk hg, trans_toLin_trans_toLin g k⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * g⁻¹, mul_mem hk (inv_mem hg), ?_⟩
    rw [trans_toLin_trans_toLin, inv_mul_cancel_right]

variable (W N H ι)

/-- The **cyclic `N`-isogeny field degree** of `W` (LMFDB `modcurve.level_structure`): the least
degree of a finite extension `L ⊆ F^s` of `F` over which `W` has a rational cyclic isogeny of degree
`N`, that is, over which a cyclic subgroup of order `N` of `E[N]`, its kernel, is Galois stable. -/
noncomputable def cyclicIsogenyFieldDegree : ℕ :=
  sInf {d | ∃ L : IntermediateField F (SeparableClosure F), FiniteDimensional F L ∧
    Module.finrank F L = d ∧
    ∃ C : AddSubgroup (AddSubgroup.torsionBy (W⁄(SeparableClosure F)).toAffine.Point (N : ℤ)),
    IsAddCyclic C ∧ Nat.card C = N ∧ ∀ σ ∈ L.fixingSubgroup, ∀ P ∈ C,
    (W.modGaloisRepresentation N σ).val P ∈ C}

/-- The **cyclic `N`-torsion field degree** of `W` (LMFDB `modcurve.level_structure`): the least
degree of a finite extension `L ⊆ F^s` of `F` over which `W` has a rational point of order `N`. -/
noncomputable def cyclicTorsionFieldDegree : ℕ :=
  sInf {d | ∃ L : IntermediateField F (SeparableClosure F), FiniteDimensional F L ∧
    Module.finrank F L = d ∧
    ∃ P : AddSubgroup.torsionBy (W⁄(SeparableClosure F)).toAffine.Point (N : ℤ), addOrderOf P = N ∧
    ∀ σ ∈ L.fixingSubgroup, (W.modGaloisRepresentation N σ).val P = P}

/-- The **`N`-torsion field degree** of `W` (LMFDB `modcurve.level_structure`): the least degree of
a finite extension `L ⊆ F^s` of `F` over which all of `E[N]` is rational, the degree of the
`N`-division field. -/
noncomputable def torsionFieldDegree : ℕ :=
  sInf {d | ∃ L : IntermediateField F (SeparableClosure F), FiniteDimensional F L ∧
    Module.finrank F L = d ∧ ∀ σ ∈ L.fixingSubgroup,
    ∀ P : AddSubgroup.torsionBy (W⁄(SeparableClosure F)).toAffine.Point (N : ℤ),
    (W.modGaloisRepresentation N σ).val P = P}

variable [W.IsElliptic]

/-- The action on `E[N]`, the `N`-torsion of `W` over a separable closure, of the automorphisms of
`W` over the separable closure, the units of the geometric endomorphism ring. -/
noncomputable def torsionGeometricAutRepresentation : W.GeometricEndˣ →*
    LinearMap.GeneralLinearGroup (ZMod N)
    (AddSubgroup.torsionBy (W⁄(SeparableClosure F)).toAffine.Point (N : ℤ)) :=
  Units.map (Hom.torsionRepresentation (W⁄(SeparableClosure F)).toAffine N).toMonoidHom

/-- An `H`-level structure `[ι]_H` on `W` is **rational** (LMFDB `modcurve.level_structure`) if the
isomorphism class of the pair `(E, [ι]_H)` is stable under the Galois group of a separable closure:
for every `σ` there is an automorphism `φ` of `W` over the separable closure, a unit of the
geometric endomorphism ring, with `ι ∘ σ⁻¹ ∘ φ_N ∈ [ι]_H`. -/
def IsRationalLevelStructure : Prop :=
  ∀ σ : SeparableClosure F ≃ₐ[F] SeparableClosure F, ∃ u : W.GeometricEndˣ,
    (W.modGaloisRepresentation N σ⁻¹ * W.torsionGeometricAutRepresentation N u).toLinearEquiv.trans
    ι ∈ W.levelStructure N H ι

end WeierstrassCurve
