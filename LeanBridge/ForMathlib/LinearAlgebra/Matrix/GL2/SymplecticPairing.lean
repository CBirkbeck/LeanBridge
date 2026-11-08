import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.LinearAlgebra.BilinearForm.Multilinear
import TauCeti.LinearAlgebra.Determinant.Basic
import TauCeti.RepresentationTheory.ExteriorPower
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.SymplecticIsomorphism

/-!
# Symplectic structures as nondegenerate alternating pairings

Let `N ≥ 1` and let `μ_N` be the group of `N`-th roots of unity of an algebraically closed field `K`
of characteristic not dividing `N`, written additively as a `ℤ/Nℤ`-module. A symplectic structure
on a free `ℤ/Nℤ`-module `M` of rank `2` (LMFDB `alg.symplectic_isomorphism`) is an isomorphism
`α : ⋀²M ≃ μ_N`, or equivalently a nondegenerate alternating pairing `M × M → μ_N`. This file
proves that equivalence, gives the example `ℤ/Nℤ × μ_N` with the determinant pairing
`((a, γ), (b, δ)) ↦ δ^a / γ^b`, and sets up the Galois-module variant of symplectic isomorphisms.
The example `E[N]` with the Weil pairing is in
`LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.WeilPairingSymplectic`.

A linear map `φ : ⋀²M → P` gives the alternating pairing `(x, y) ↦ φ (x ∧ y)`
(`LinearMap.wedgeBilin`), and every alternating pairing arises so, from exactly one `φ`, by the
universal property of `⋀²M`. For a basis `(e₁, e₂)` of `M` over any commutative ring, the second
exterior power is free on `e₁ ∧ e₂` (`Module.Basis.exteriorSquareEquiv`), and
`φ (x ∧ y) = det(x, y) • φ (e₁ ∧ e₂)`. So `φ` is injective exactly when `φ (e₁ ∧ e₂)` has zero
annihilator, which is exactly when the pairing is left-separating (Tau Ceti's
`LinearMap.IsAlt.eq_zero_of_smul_apply_basis_eq_zero` gives one direction); an alternating
pairing is left-separating exactly when it is nondegenerate. Over `ℤ/Nℤ`, with `P` of order `N`,
injective is bijective. Tau Ceti's `LinearMap.IsAlt.exteriorSquareEquiv` recognises `⋀²M ≃ P`
when the values of the pairing on pairs of basis vectors are already known to form a basis of
`P`; here `P` is only assumed to have `N` elements, and the converse is proved as well.

In the Galois-module variant a group `G`, such as an absolute Galois group, acts on `M` and on
`μ_N`, hence on `⋀²M` (Tau Ceti's `Representation.exteriorPower`); a symplectic structure is then
`G`-equivariant, and a symplectic isomorphism of Galois modules is a `G`-equivariant isomorphism
that is symplectic (`LinearEquiv.IsGaloisSymplectic`), `-1` for instance. The variant in which `M`
is a finite étale group scheme that is `(ℤ/Nℤ)²` étale locally is not formalised. Tau Ceti has
commutative group schemes as group objects over a base, constant group schemes, finite étale
schemes over an affine base and the group scheme `μ_N` (`TauCeti.RootsOfUnityGroup.groupScheme`),
but neither tree has the second exterior power of a group scheme, or alternating pairings of group
schemes with values in `μ_N`, nor the notion of a group scheme that is `(ℤ/Nℤ)²` étale locally.

## Main definitions

* `LinearMap.wedgeBilin`: the alternating pairing `(x, y) ↦ φ (x ∧ y)` of `φ : ⋀²M → P`.
* `Module.Basis.exteriorSquareEquiv`: `⋀²M ≃ R`, `x ∧ y ↦ det(x, y)`, for a basis of `M` indexed
  by `Fin 2`.
* `exteriorPower.linearEquivEquivPairing`: isomorphisms `⋀²M ≃ P` are nondegenerate alternating
  pairings `M × M → P`, for `M` free of rank `2` over `ℤ/Nℤ` and `P` of order `N`.
* `LinearEquiv.IsGaloisSymplectic` (LMFDB `alg.symplectic_isomorphism`): a symplectic isomorphism
  of Galois modules.
* `rootsOfUnity.exteriorSquareEquivPairing` (LMFDB `alg.symplectic_isomorphism`): isomorphisms
  `⋀²M ≃ μ_N` are nondegenerate alternating pairings `M × M → μ_N`, for `μ_N` in a separably
  closed field, an algebraically closed one for instance, of characteristic not dividing `N`.
* `rootsOfUnity.detPairing`: the determinant pairing on `ℤ/Nℤ × μ_N`.
* `rootsOfUnity.algEquivRepresentation`: the Galois action on `μ_N`.
* `rootsOfUnity.prodBasis`: the basis `(1, 0), (0, ζ)` of `ℤ/Nℤ × μ_N` for a primitive `ζ`.
* `rootsOfUnity.detSymplecticEquiv` (LMFDB `alg.symplectic_isomorphism`): the symplectic
  structure `⋀²(ℤ/Nℤ × μ_N) ≃ μ_N` of the determinant pairing.

## Main results

* `LinearMap.injective_iff_separatingLeft`: `φ` is injective exactly when its pairing is
  left-separating, for `M` free of rank `2`.
* `exteriorPower.bijective_iff_nondegenerate`: over `ℤ/Nℤ`, with `P` of order `N`, `φ` is
  bijective exactly when its pairing is nondegenerate.
* `LinearEquiv.isGaloisSymplectic_neg`: `-1` is a symplectic automorphism of every symplectic
  Galois module.
* `rootsOfUnity.toMul_detPairing`: the determinant pairing is `((a, γ), (b, δ)) ↦ δ^a / γ^b`.
* `rootsOfUnity.nondegenerate_detPairing`: it is nondegenerate.
* `rootsOfUnity.isIntertwiningMap_detSymplecticEquiv`: its symplectic structure is equivariant for
  every action on `μ_N`, trivial on `ℤ/Nℤ`.
-/

open exteriorPower Module

namespace LinearMap

variable {R M P : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
  (φ : ⋀[R]^2 M →ₗ[R] P)

/-- The **alternating pairing** `(x, y) ↦ φ (x ∧ y)` of a linear map `φ : ⋀²M → P` out of the
second exterior power. -/
noncomputable def wedgeBilin : M →ₗ[R] M →ₗ[R] P :=
  mk₂ R (fun x y ↦ φ.compAlternatingMap (ιMulti R 2) ![x, y])
    (fun x x' y ↦ (φ.compAlternatingMap (ιMulti R 2)).toMultilinearMap.cons_add ![y] x x')
    (fun c x y ↦ (φ.compAlternatingMap (ιMulti R 2)).toMultilinearMap.cons_smul ![y] c x)
    (fun x y y' ↦ by
      simpa using (φ.compAlternatingMap (ιMulti R 2)).toMultilinearMap.snoc_add ![x] y y')
    (fun c x y ↦ by
      simpa using (φ.compAlternatingMap (ιMulti R 2)).toMultilinearMap.snoc_smul ![x] c y)

lemma wedgeBilin_apply (x y : M) : φ.wedgeBilin x y = φ (ιMulti R 2 ![x, y]) :=
  rfl

lemma isAlt_wedgeBilin : φ.wedgeBilin.IsAlt :=
  fun x ↦ (φ.compAlternatingMap (ιMulti R 2)).map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) rfl
    (by decide)

lemma apply_eq_smul (b : Basis (Fin 2) R M) (ξ : ⋀[R]^2 M) :
    φ ξ = alternatingMapLinearEquiv b.det ξ • φ (ιMulti R 2 b) := by
  refine LinearMap.congr_fun (linearMap_ext (AlternatingMap.ext fun v ↦ ?_) :
    φ = (alternatingMapLinearEquiv b.det).smulRight (φ (ιMulti R 2 b))) ξ
  rw [compAlternatingMap_apply, compAlternatingMap_apply, smulRight_apply,
    alternatingMapLinearEquiv_apply_ιMulti]
  exact DFunLike.congr_fun
    (AlternatingMap.eq_basis_det_smulRight b (φ.compAlternatingMap (ιMulti R 2))) v

lemma wedgeBilin_alternatingMapLinearEquiv {B : M →ₗ[R] M →ₗ[R] P} (hB : B.IsAlt) :
    (alternatingMapLinearEquiv hB.toAlternatingMap).wedgeBilin = B :=
  ext₂ fun x y ↦ by
    rw [wedgeBilin_apply, alternatingMapLinearEquiv_apply_ιMulti, IsAlt.toAlternatingMap_apply]
    rfl

lemma alternatingMapLinearEquiv_toAlternatingMap :
    alternatingMapLinearEquiv φ.isAlt_wedgeBilin.toAlternatingMap = φ :=
  linearMap_ext <| AlternatingMap.ext fun v ↦ by
    rw [compAlternatingMap_apply, compAlternatingMap_apply, alternatingMapLinearEquiv_apply_ιMulti,
      IsAlt.toAlternatingMap_apply, wedgeBilin_apply]
    congr

end LinearMap

namespace Module.Basis

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (b : Basis (Fin 2) R M)

/-- The **trivialisation of the second exterior power** of a free module `M` of rank `2` given by
a basis `b = (e₁, e₂)`: the isomorphism `⋀²M ≃ R` sending `x ∧ y` to the determinant of `(x, y)`
in the basis `b`, with inverse `r ↦ r • (e₁ ∧ e₂)`. -/
noncomputable def exteriorSquareEquiv : ⋀[R]^2 M ≃ₗ[R] R :=
  LinearEquiv.ofLinearMap (alternatingMapLinearEquiv b.det)
    (LinearMap.toSpanSingleton R _ (ιMulti R 2 b)) (LinearMap.ext_ring <| by simp [Basis.det_self])
    (LinearMap.ext fun ξ ↦ (LinearMap.id.apply_eq_smul b ξ).symm)

lemma exteriorSquareEquiv_ιMulti (v : Fin 2 → M) :
    b.exteriorSquareEquiv (ιMulti R 2 v) = b.det v :=
  alternatingMapLinearEquiv_apply_ιMulti _ v

end Module.Basis

namespace LinearMap

variable {R M P : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
  (φ : ⋀[R]^2 M →ₗ[R] P)

/-- **A linear map out of `⋀²M` is injective exactly when its pairing is left-separating**, for `M`
free of rank `2` over any commutative ring: both say that `φ (e₁ ∧ e₂)` has zero annihilator. -/
lemma injective_iff_separatingLeft (b : Basis (Fin 2) R M) :
    Function.Injective φ ↔ φ.wedgeBilin.SeparatingLeft := by
  have hc : φ (ιMulti R 2 b) = φ.wedgeBilin (b 0) (b 1) := by
    rw [wedgeBilin_apply]
    congr
  refine ⟨fun h x hx ↦ ?_, fun h ↦ (injective_iff_map_eq_zero φ).mpr fun ξ hξ ↦ ?_⟩
  · have h0 (y : M) : b.det ![x, y] = 0 := by
      have h1 : ιMulti R 2 ![x, y] = 0 := h ((hx y).trans φ.map_zero.symm)
      rw [← b.exteriorSquareEquiv_ιMulti, h1, map_zero]
    refine b.forall_coord_eq_zero_iff.mp fun i ↦ ?_
    fin_cases i
    · simpa [Basis.det_apply, Matrix.det_fin_two, Basis.toMatrix_apply] using h0 (b 1)
    · simpa [Basis.det_apply, Matrix.det_fin_two, Basis.toMatrix_apply] using h0 (b 0)
  · rw [φ.apply_eq_smul b, hc] at hξ
    exact b.exteriorSquareEquiv.map_eq_zero_iff.mp
      ((isAlt_wedgeBilin φ).eq_zero_of_smul_apply_basis_eq_zero b h hξ)

end LinearMap

namespace exteriorPower

variable {N : ℕ} [NeZero N] {M P : Type*} [AddCommGroup M] [Module (ZMod N) M] [AddCommGroup P]
  [Module (ZMod N) P]

/-- **Over `ℤ/Nℤ`, a linear map `⋀²M → P` is an isomorphism exactly when its pairing is
nondegenerate**, for `M` free of rank `2` and `P` of order `N`: both sides have `N` elements, so
injective is bijective. -/
lemma bijective_iff_nondegenerate (b : Basis (Fin 2) (ZMod N) M) (hP : Nat.card P = N)
    (φ : ⋀[ZMod N]^2 M →ₗ[ZMod N] P) : Function.Bijective φ ↔ φ.wedgeBilin.Nondegenerate := by
  have : Finite P := Nat.finite_of_card_ne_zero (hP.trans_ne (NeZero.ne N))
  rw [φ.isAlt_wedgeBilin.isRefl.nondegenerate_iff_separatingLeft,
    ← φ.injective_iff_separatingLeft b]
  refine ⟨fun h ↦ h.1, fun h ↦ h.bijective_of_nat_card_le ?_⟩
  rw [hP, Nat.card_congr b.exteriorSquareEquiv.toEquiv, Nat.card_zmod]

variable (hM : Nonempty (Basis (Fin 2) (ZMod N) M)) (hP : Nat.card P = N)

/-- **Symplectic structures are nondegenerate alternating pairings**: for `M` free of rank `2` over
`ℤ/Nℤ` and `P` of order `N`, the isomorphisms `α : ⋀²M ≃ P` correspond to the nondegenerate
alternating pairings `M × M → P`, through `α ↦ ((x, y) ↦ α (x ∧ y))`. -/
noncomputable def linearEquivEquivPairing : (⋀[ZMod N]^2 M ≃ₗ[ZMod N] P) ≃
    {B : M →ₗ[ZMod N] M →ₗ[ZMod N] P // B.IsAlt ∧ B.Nondegenerate} where
  toFun α := ⟨α.toLinearMap.wedgeBilin, α.toLinearMap.isAlt_wedgeBilin,
    (bijective_iff_nondegenerate hM.some hP α.toLinearMap).mp α.bijective⟩
  invFun B := LinearEquiv.ofBijective (alternatingMapLinearEquiv B.2.1.toAlternatingMap) <|
    (bijective_iff_nondegenerate hM.some hP _).mpr <|
      (LinearMap.wedgeBilin_alternatingMapLinearEquiv B.2.1).symm ▸ B.2.2
  left_inv α :=
    LinearEquiv.toLinearMap_injective α.toLinearMap.alternatingMapLinearEquiv_toAlternatingMap
  right_inv B := Subtype.ext <| LinearMap.wedgeBilin_alternatingMapLinearEquiv B.2.1

lemma linearEquivEquivPairing_apply_coe (α : ⋀[ZMod N]^2 M ≃ₗ[ZMod N] P) :
    (linearEquivEquivPairing hM hP α : M →ₗ[ZMod N] M →ₗ[ZMod N] P) = α.toLinearMap.wedgeBilin :=
  rfl

lemma linearEquivEquivPairing_symm_apply_ιMulti
    (B : {B : M →ₗ[ZMod N] M →ₗ[ZMod N] P // B.IsAlt ∧ B.Nondegenerate}) (x y : M) :
    (linearEquivEquivPairing hM hP).symm B (ιMulti (ZMod N) 2 ![x, y]) = B.1 x y :=
  LinearMap.congr_fun₂ (LinearMap.wedgeBilin_alternatingMapLinearEquiv B.2.1) x y

end exteriorPower

namespace Representation

variable {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

lemma isIntertwiningMap_exteriorPower_two {U : Type*} [AddCommGroup U] [Module k U]
    (χ : Representation k G U) (f : ⋀[k]^2 V →ₗ[k] U)
    (h : ∀ g x y, f (ιMulti k 2 ![ρ g x, ρ g y]) = χ g (f (ιMulti k 2 ![x, y]))) :
    (ρ.exteriorPower 2).IsIntertwiningMap χ f := by
  refine ⟨fun g ξ ↦ LinearMap.congr_fun (linearMap_ext <| AlternatingMap.ext fun v ↦ ?_ :
    f ∘ₗ ρ.exteriorPower 2 g = χ g ∘ₗ f) ξ⟩
  have hρv : ![ρ g (v 0), ρ g (v 1)] = ρ g ∘ v := FinVec.etaExpand_eq (ρ g ∘ v)
  rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, exteriorPower_apply_ιMulti, ← hρv]
  exact (h g (v 0) (v 1)).trans <|
    congrArg (fun w ↦ χ g (f (ιMulti k 2 w))) <| FinVec.etaExpand_eq v

end Representation

namespace LinearEquiv

variable {N : ℕ} {G K M M' : Type*} [Monoid G] [CommRing K] [AddCommGroup M] [Module (ZMod N) M]
  [AddCommGroup M'] [Module (ZMod N) M'] (f : M ≃ₗ[ZMod N] M') (ρ : Representation (ZMod N) G M)
  (α : ⋀[ZMod N]^2 M ≃ₗ[ZMod N] Additive (rootsOfUnity N K))

/-- A **symplectic isomorphism of Galois modules** (LMFDB `alg.symplectic_isomorphism`, its
Galois-module variant). A group `G`, such as an absolute Galois group, acts `ℤ/Nℤ`-linearly on
`M` by `ρ` and on `M'` by `ρ'`, and the symplectic structures `α : ⋀²M ≃ μ_N` and
`α' : ⋀²M' ≃ μ_N` are isomorphisms of Galois modules when `G` acts on `μ_N`
(`Representation.IsIntertwiningMap (ρ.exteriorPower 2) χ α`). An isomorphism `f : M ≃ M'` is then
a symplectic isomorphism of Galois modules if it is `G`-equivariant and symplectic. -/
def IsGaloisSymplectic (ρ' : Representation (ZMod N) G M')
    (α' : ⋀[ZMod N]^2 M' ≃ₗ[ZMod N] Additive (rootsOfUnity N K)) : Prop :=
  ρ.IsIntertwiningMap ρ' f.toLinearMap ∧ f.IsSymplectic α α'

/-- **`-1` is a symplectic automorphism of every symplectic Galois module**: it commutes with the
action, and `(-x) ∧ (-y) = x ∧ y`. -/
lemma isGaloisSymplectic_neg :
    (LinearEquiv.neg (ZMod N) : M ≃ₗ[ZMod N] M).IsGaloisSymplectic ρ α ρ α :=
  ⟨⟨fun g x ↦ (map_neg (ρ g) x).symm⟩, (isSymplectic_iff _ α α).mpr fun x y ↦
    ((α.toLinearMap.wedgeBilin.map_neg₂ x (-y)).trans <|
      congrArg Neg.neg <| (α.toLinearMap.wedgeBilin x).map_neg y).trans <| neg_neg _⟩

end LinearEquiv

namespace rootsOfUnity

variable (N : ℕ) (K : Type*) [Field K]

lemma natCard_additive [NeZero N] [HasEnoughRootsOfUnity K N] :
    Nat.card (Additive (rootsOfUnity N K)) = N :=
  (Nat.card_congr Additive.toMul).trans <| HasEnoughRootsOfUnity.natCard_rootsOfUnity K N

/-- **A symplectic structure is a nondegenerate alternating pairing** (LMFDB
`alg.symplectic_isomorphism`): with `μ_N` the group of `N`-th roots of unity of a separably closed
field `K`, an algebraically closed one for instance, of characteristic not dividing `N`, the
isomorphisms `α : ⋀²M ≃ μ_N` on a free `ℤ/Nℤ`-module `M` of rank `2` correspond to the
nondegenerate alternating pairings `M × M → μ_N`, through `α ↦ ((x, y) ↦ α (x ∧ y))`. -/
noncomputable def exteriorSquareEquivPairing [IsSepClosed K] [NeZero (N : K)] {M : Type*}
    [AddCommGroup M] [Module (ZMod N) M] (hM : Nonempty (Basis (Fin 2) (ZMod N) M)) :
    (⋀[ZMod N]^2 M ≃ₗ[ZMod N] Additive (rootsOfUnity N K)) ≃
      {B : M →ₗ[ZMod N] M →ₗ[ZMod N] Additive (rootsOfUnity N K) // B.IsAlt ∧ B.Nondegenerate} :=
  haveI : NeZero N := .of_neZero_natCast K
  linearEquivEquivPairing hM <| natCard_additive N K

/-- The **determinant pairing** on `ℤ/Nℤ × μ_N`, `((a, γ), (b, δ)) ↦ δ^a / γ^b`, written additively
as `a • δ - b • γ` (`rootsOfUnity.toMul_detPairing`). -/
noncomputable def detPairing : ZMod N × Additive (rootsOfUnity N K) →ₗ[ZMod N]
    ZMod N × Additive (rootsOfUnity N K) →ₗ[ZMod N] Additive (rootsOfUnity N K) :=
  letI A : ZMod N × Additive (rootsOfUnity N K) →ₗ[ZMod N]
      ZMod N × Additive (rootsOfUnity N K) →ₗ[ZMod N] Additive (rootsOfUnity N K) :=
    (LinearMap.lsmul (ZMod N) _).compl₁₂ (LinearMap.fst _ _ _) (LinearMap.snd _ _ _)
  A - A.flip

lemma detPairing_apply (x y : ZMod N × Additive (rootsOfUnity N K)) :
    detPairing N K x y = x.1 • y.2 - y.1 • x.2 :=
  rfl

lemma isAlt_detPairing : (detPairing N K).IsAlt :=
  fun x ↦ (detPairing_apply N K x x).trans <| sub_self _

variable (F : Type*) [Field F] [Algebra F K] in
/-- The **Galois action on `μ_N`**, as a representation over `ℤ/Nℤ`: an automorphism `σ` of `K`
over `F` acts on the `N`-th roots of unity by `ζ ↦ σ ζ`. Through it the absolute Galois group acts
by the cyclotomic character. -/
noncomputable def algEquivRepresentation :
    Representation (ZMod N) (K ≃ₐ[F] K) (Additive (rootsOfUnity N K)) where
  toFun σ := (MonoidHom.toAdditive (restrictRootsOfUnity σ N)).toZModLinearMap N
  map_one' := LinearMap.ext fun _ ↦ Additive.toMul.injective <| Subtype.ext <| Units.ext rfl
  map_mul' _ _ := LinearMap.ext fun _ ↦ Additive.toMul.injective <| Subtype.ext <| Units.ext rfl

variable [NeZero N]

/-- **The determinant pairing is `((a, γ), (b, δ)) ↦ δ^a / γ^b`** in multiplicative notation, as in
the LMFDB. -/
lemma toMul_detPairing (a b : ZMod N) (γ δ : Additive (rootsOfUnity N K)) :
    (detPairing N K (a, γ) (b, δ)).toMul = δ.toMul ^ a.val / γ.toMul ^ b.val := by
  have h (c : ZMod N) (z : Additive (rootsOfUnity N K)) : c • z = c.val • z := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_zmod_val]
  rw [detPairing_apply, h, h, toMul_sub, toMul_nsmul, toMul_nsmul]

/-- The **basis** `(1, 0), (0, ζ)` of `ℤ/Nℤ × μ_N` given by a primitive `N`-th root of unity `ζ`,
which makes `ℤ/Nℤ × μ_N` free of rank `2` over `ℤ/Nℤ`. -/
noncomputable def prodBasis {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ N) :
    Basis (Fin 2) (ZMod N) (ZMod N × Additive (rootsOfUnity N K)) :=
  (Basis.finTwoProd (ZMod N)).map <| (LinearEquiv.refl (ZMod N) (ZMod N)).prodCongr <|
    hζ.zmodEquivRootsOfUnity.toLinearEquiv <| ZMod.map_smul _

variable [HasEnoughRootsOfUnity K N]

/-- **The determinant pairing is nondegenerate**, over a field with a primitive `N`-th root of
unity `ζ`: `(a, γ)` pairs with `(1, 1)` to `γ⁻¹` and with `(0, ζ)` to `ζ^a`. -/
lemma nondegenerate_detPairing : (detPairing N K).Nondegenerate := by
  rcases HasEnoughRootsOfUnity.exists_isPrimitiveRoot K N with ⟨ζ, hζ⟩
  let e : ZMod N ≃+ Additive (rootsOfUnity N K) :=
    (hζ.isUnit_unit (NeZero.ne N)).zmodEquivRootsOfUnity
  refine (isAlt_detPairing N K).isRefl.nondegenerate_iff_separatingLeft.mpr fun x hx ↦ ?_
  have h₁ : x.1 • e 1 = 0 := by simpa [detPairing_apply] using hx (0, e 1)
  have h₂ : x.2 = 0 := by simpa [detPairing_apply] using hx (1, 0)
  refine Prod.ext (e.injective ?_) h₂
  rw [← mul_one x.1, ← smul_eq_mul, ZMod.map_smul, h₁, Prod.fst_zero, map_zero]

/-- The **symplectic structure of the determinant pairing** (LMFDB `alg.symplectic_isomorphism`):
the isomorphism `⋀²(ℤ/Nℤ × μ_N) ≃ μ_N` sending `(a, γ) ∧ (b, δ)` to `δ^a / γ^b`, over a field with
a primitive `N`-th root of unity, an algebraically closed field of characteristic not dividing
`N` for instance. -/
noncomputable def detSymplecticEquiv :
    ⋀[ZMod N]^2 (ZMod N × Additive (rootsOfUnity N K)) ≃ₗ[ZMod N] Additive (rootsOfUnity N K) :=
  (linearEquivEquivPairing ((HasEnoughRootsOfUnity.exists_isPrimitiveRoot K N).elim
      fun _ hζ ↦ ⟨prodBasis N K (hζ.isUnit_unit (NeZero.ne N))⟩) (natCard_additive N K)).symm
    ⟨detPairing N K, isAlt_detPairing N K, nondegenerate_detPairing N K⟩

lemma detSymplecticEquiv_ιMulti (x y : ZMod N × Additive (rootsOfUnity N K)) :
    detSymplecticEquiv N K (ιMulti (ZMod N) 2 ![x, y]) = detPairing N K x y :=
  linearEquivEquivPairing_symm_apply_ιMulti _ _ _ x y

variable {G : Type*} [Monoid G] in
/-- **The symplectic structure of the determinant pairing is Galois-equivariant**: if a group `G`
acts on `μ_N` by `χ`, for instance through the cyclotomic character, and trivially on `ℤ/Nℤ`, then
`detSymplecticEquiv` is an isomorphism of `G`-modules `⋀²(ℤ/Nℤ × μ_N) ≃ μ_N`. -/
lemma isIntertwiningMap_detSymplecticEquiv
    (χ : Representation (ZMod N) G (Additive (rootsOfUnity N K))) :
    (((Representation.trivial (ZMod N) G (ZMod N)).prod χ).exteriorPower 2).IsIntertwiningMap χ
      (detSymplecticEquiv N K).toLinearMap :=
  Representation.isIntertwiningMap_exteriorPower_two _ _ _ fun g x y ↦ by
    simp [detSymplecticEquiv_ιMulti, detPairing_apply]

end rootsOfUnity
