import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Bilinear
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Galois
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.Basic
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.SymplecticPairing

/-!
# The Weil pairing as a symplectic structure on `E[N]`

Let `E` be an elliptic curve over a field `F`, let `K` be a separably closed extension of `F`, an
algebraic closure for instance, and let `N ≥ 1` be invertible in `K`. The `N`-torsion `E[N]` of
`E` over `K` is a free `ℤ/Nℤ`-module of rank `2`, and the Weil pairing `e_N` is a nondegenerate
alternating pairing `E[N] × E[N] → μ_N` (Tau Ceti's `TauCeti.Isogeny.weilPairingBilin`). By the
correspondence of `LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.SymplecticPairing` it is a
symplectic structure `⋀²E[N] ≃ μ_N`, `S ∧ T ↦ e_N(S, T)`: the example `E[N]` of LMFDB
`alg.symplectic_isomorphism`.

The automorphisms of `K` over `F` act on `E[N]` and on `μ_N`, and the Weil pairing is Galois
equivariant, `e_N(σ S, σ T) = σ (e_N(S, T))` (Tau Ceti's
`WeierstrassCurve.weilPairing_torsionGaloisAction`). So the symplectic structure is an
isomorphism of Galois modules, and `E[N]` is an example of the Galois-module variant too.

## Main definitions

* `WeierstrassCurve.torsionGaloisRepresentation`: the action of `Aut(K/F)` on `E[N]`, as a
  representation over `ℤ/Nℤ`.
* `WeierstrassCurve.weilPairingExteriorEquiv` (LMFDB `alg.symplectic_isomorphism`): the
  symplectic structure `⋀²E[N] ≃ μ_N` of the Weil pairing.

## Main results

* `WeierstrassCurve.isIntertwiningMap_weilPairingExteriorEquiv` (LMFDB
  `alg.symplectic_isomorphism`): it is Galois-equivariant.
-/

open exteriorPower TauCeti Isogeny

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] [Algebra F K] (W : WeierstrassCurve F)
  [W.IsElliptic] (N : ℕ)

variable (K) in
/-- The **Galois representation on `E[N]`**: an automorphism `σ` of `K` over `F` acts on the
`N`-torsion points of `W` over `K` by applying `σ` to their coordinates, a `ℤ/Nℤ`-linear map. It
is the mod-`N` representation `WeierstrassCurve.modGaloisRepresentation`, as a representation. -/
noncomputable def torsionGaloisRepresentation :
    Representation (ZMod N) (K ≃ₐ[F] K) (AddSubgroup.torsionBy (W⁄K).toAffine.Point (N : ℤ)) :=
  (Units.coeHom _).comp (W.modGaloisRepresentation N)

variable [IsSepClosed K] [NeZero N] (hN : (N : K) ≠ 0)

/-- The **Weil pairing as a symplectic structure** (LMFDB `alg.symplectic_isomorphism`): for an
elliptic curve `W` over `F`, a separably closed extension `K` of `F` and `N` invertible in `K`, the
isomorphism `⋀²E[N] ≃ μ_N` of `ℤ/Nℤ`-modules sending `S ∧ T` to the Weil pairing `e_N(S, T)`,
where `E[N]` is the `N`-torsion of `W` over `K` and `μ_N` the `N`-th roots of unity of `K`. -/
noncomputable def weilPairingExteriorEquiv :
    ⋀[ZMod N]^2 (AddSubgroup.torsionBy (W⁄K).toAffine.Point (N : ℤ)) ≃ₗ[ZMod N]
      Additive (rootsOfUnity N K) :=
  haveI : NeZero (N : K) := ⟨hN⟩
  (linearEquivEquivPairing ((W⁄K).nonempty_basis_torsionBy N hN)
      (rootsOfUnity.natCard_additive N K)).symm
    ⟨weilPairingBilin (W⁄K) N hN, isAlt_weilPairingBilin (W⁄K) N hN,
      (isAlt_weilPairingBilin (W⁄K) N hN).isRefl.nondegenerate_iff_separatingLeft.mpr <|
        separatingLeft_weilPairingBilin (W⁄K) N hN⟩

lemma weilPairingExteriorEquiv_ιMulti (S T : AddSubgroup.torsionBy (W⁄K).toAffine.Point (N : ℤ)) :
    W.weilPairingExteriorEquiv N hN (ιMulti (ZMod N) 2 ![S, T]) = weilPairing (W⁄K) N hN S T :=
  linearEquivEquivPairing_symm_apply_ιMulti _ _ _ S T

/-- **The symplectic structure of the Weil pairing is Galois-equivariant** (LMFDB
`alg.symplectic_isomorphism`): the automorphisms of `K` over `F` act on `E[N]` and on `μ_N`, and
`⋀²E[N] ≃ μ_N` is an isomorphism of Galois modules, since `e_N(σ S, σ T) = σ (e_N(S, T))`. -/
lemma isIntertwiningMap_weilPairingExteriorEquiv :
    ((W.torsionGaloisRepresentation K N).exteriorPower 2).IsIntertwiningMap
      (rootsOfUnity.algEquivRepresentation N K F) (W.weilPairingExteriorEquiv N hN).toLinearMap :=
  Representation.isIntertwiningMap_exteriorPower_two _ _ _ fun σ S T ↦ by
    rw [LinearEquiv.coe_coe, weilPairingExteriorEquiv_ιMulti, weilPairingExteriorEquiv_ιMulti]
    exact weilPairing_torsionGaloisAction W N hN σ S T

end WeierstrassCurve
