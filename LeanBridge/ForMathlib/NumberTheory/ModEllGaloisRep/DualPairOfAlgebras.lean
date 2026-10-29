import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Dual pairs of algebras

Let `R` be a commutative ring. A dual pair of algebras over `R` is a triple `(A, B, φ)` of finite
locally free commutative `R`-algebras `A` and `B` and a perfect `R`-bilinear pairing
`φ : A × B → R` such that

1. `φ(1, 1) = 1`;
2. `φ(a a', 1) = φ(a, 1) φ(a', 1)`;
3. `φ(1, b b') = φ(1, b) φ(1, b')`;
4. `Φ⁽²⁾(μ₁(a) μ₁(a'), b ⊗ b') = φ(a a', b b') = Φ⁽²⁾(a ⊗ a', μ₂(b) μ₂(b'))`,

where `Φ⁽²⁾ : (A ⊗ A) × (B ⊗ B) → R` is the pairing `(a ⊗ a', b ⊗ b') ↦ φ(a, b) φ(a', b')`, and
`μ₁ : A → A ⊗ A` and `μ₂ : B → B ⊗ B` are the duals of the multiplications of `B` and `A`,
transported by the isomorphisms `A ≅ Hom(B, R)` and `B ≅ Hom(A, R)` given by `φ`. Identities 1 to 3
say that the counits `φ(·, 1)` of `A` and `φ(1, ·)` of `B`, dual to the units of `B` and `A`, are
ring homomorphisms, and identity 4 that `μ₁` and `μ₂` are multiplicative, making `A` and `B` dual
commutative and cocommutative bialgebras. The outer terms of identity 4 always agree, so its two
equations are equivalent (not formalised here). The LMFDB knowl `modlgal.dual_pair_of_algebras`
writes `μ₂(b) μ₁(b')` in identity 4, a typo for `μ₂(b) μ₂(b')`. Finite locally free modules are
expressed as finite projective modules, as in Tau Ceti's Cartier duality
(`TauCeti.FiniteLocallyFreeBicommutativeHopfAlgCat`).

The relation with finite commutative group schemes, through Cartier duality, is not formalised
here. The identities do not provide an antipode: the functions on the multiplicative monoid
`{0, 1}` and its monoid algebra form a dual pair, whose spectra are monoid schemes but not group
schemes.

## Main definitions

* `LinearMap.tensorPairing` (LMFDB `modlgal.dual_pair_of_algebras`): the pairing `Φ⁽²⁾`.
* `LinearMap.leftComul` (LMFDB `modlgal.dual_pair_of_algebras`): the map `μ₁ : A → A ⊗ A`.
* `LinearMap.rightComul` (LMFDB `modlgal.dual_pair_of_algebras`): the map `μ₂ : B → B ⊗ B`.
* `LinearMap.IsDualPairOfAlgebras` (LMFDB `modlgal.dual_pair_of_algebras`): dual pairs of algebras.

## Main results

* `LinearMap.tensorPairing_leftComul`: `Φ⁽²⁾(μ₁(a), y) = φ(a, m_B(y))` for `y ∈ B ⊗ B`, where `m_B`
  is the multiplication of `B`.
* `LinearMap.tensorPairing_rightComul`: `Φ⁽²⁾(x, μ₂(b)) = φ(m_A(x), b)` for `x ∈ A ⊗ A`.
-/

open TensorProduct Module

namespace LinearMap

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (φ : A →ₗ[R] B →ₗ[R] R)

/-- The **pairing `Φ⁽²⁾`** `: (A ⊗ A) × (B ⊗ B) → R` (LMFDB `modlgal.dual_pair_of_algebras`) of an
`R`-bilinear pairing `φ : A × B → R`: the `R`-bilinear map sending `(a ⊗ a', b ⊗ b')` to
`φ(a, b) φ(a', b')` (`LinearMap.tensorPairing_tmul_tmul`). -/
noncomputable def tensorPairing : A ⊗[R] A →ₗ[R] B ⊗[R] B →ₗ[R] R :=
  dualDistrib R B B ∘ₗ map φ φ

lemma tensorPairing_tmul_tmul (a a' : A) (b b' : B) :
    φ.tensorPairing (a ⊗ₜ a') (b ⊗ₜ b') = φ a b * φ a' b' := by
  simp [tensorPairing]

variable [φ.IsPerfPair]

variable [Module.Finite R B] [Module.Projective R B] in
/-- The **map `μ₁`** `: A → A ⊗ A` (LMFDB `modlgal.dual_pair_of_algebras`) of a perfect `R`-bilinear
pairing `φ : A × B → R` of algebras, `B` finite projective: the `R`-linear dual
`Hom(B, R) → Hom(B ⊗ B, R)` of the multiplication of `B`, transported by the isomorphisms
`A ≅ Hom(B, R)` and `A ⊗ A ≅ Hom(B, R) ⊗ Hom(B, R) ≅ Hom(B ⊗ B, R)` given by `φ`. It is
characterised by `Φ⁽²⁾(μ₁(a), b ⊗ b') = φ(a, b b')` (`LinearMap.tensorPairing_leftComul`). -/
noncomputable def leftComul : A →ₗ[R] A ⊗[R] A :=
  (congr φ.toPerfPair.symm φ.toPerfPair.symm).toLinearMap ∘ₗ
    (dualDistribEquiv R B B).symm.toLinearMap ∘ₗ (mul' R B).dualMap ∘ₗ φ

variable [Module.Finite R A] [Module.Projective R A] in
/-- The **map `μ₂`** `: B → B ⊗ B` (LMFDB `modlgal.dual_pair_of_algebras`) of a perfect `R`-bilinear
pairing `φ : A × B → R` of algebras, `A` finite projective: the `R`-linear dual
`Hom(A, R) → Hom(A ⊗ A, R)` of the multiplication of `A`, transported by the isomorphisms
`B ≅ Hom(A, R)` and `B ⊗ B ≅ Hom(A ⊗ A, R)` given by `φ`. It is characterised by
`Φ⁽²⁾(a ⊗ a', μ₂(b)) = φ(a a', b)` (`LinearMap.tensorPairing_rightComul`). -/
noncomputable def rightComul : B →ₗ[R] B ⊗[R] B :=
  (congr φ.flip.toPerfPair.symm φ.flip.toPerfPair.symm).toLinearMap ∘ₗ
    (dualDistribEquiv R A A).symm.toLinearMap ∘ₗ (mul' R A).dualMap ∘ₗ φ.flip

variable [Module.Finite R B] [Module.Projective R B] in
/-- **`μ₁` is dual to the multiplication of `B`**: `Φ⁽²⁾(μ₁(a), y) = φ(a, m_B(y))` for
`y ∈ B ⊗ B`, in particular `Φ⁽²⁾(μ₁(a), b ⊗ b') = φ(a, b b')`. -/
lemma tensorPairing_leftComul (a : A) (y : B ⊗[R] B) :
    φ.tensorPairing (φ.leftComul a) y = φ a (mul' R B y) := by
  have h (x : Dual R B ⊗[R] Dual R B) :
      map φ φ (congr φ.toPerfPair.symm φ.toPerfPair.symm x) = x := by
    induction x with
    | tmul f g => simp
    | add x x' hx hx' => rw [map_add, map_add, hx, hx']
  rw [tensorPairing, leftComul, comp_apply, comp_apply, comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, comp_apply, h, ← toLinearMap_dualDistribEquiv, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, dualMap_apply]

variable [Module.Finite R A] [Module.Projective R A] in
/-- **`μ₂` is dual to the multiplication of `A`**: `Φ⁽²⁾(x, μ₂(b)) = φ(m_A(x), b)` for
`x ∈ A ⊗ A`, in particular `Φ⁽²⁾(a ⊗ a', μ₂(b)) = φ(a a', b)`. -/
lemma tensorPairing_rightComul (x : A ⊗[R] A) (b : B) :
    φ.tensorPairing x (φ.rightComul b) = φ (mul' R A x) b := by
  have h (w : Dual R A ⊗[R] Dual R A) :
      φ.tensorPairing x (congr φ.flip.toPerfPair.symm φ.flip.toPerfPair.symm w) =
        dualDistribEquiv R A A w x := by
    induction x with
    | tmul a a' =>
      induction w with
      | tmul f g => simp [tensorPairing_tmul_tmul, mul_comm]
      | add w w' hw hw' => rw [map_add, map_add, map_add, LinearMap.add_apply, hw, hw']
    | add x x' hx hx' => rw [map_add, LinearMap.add_apply, map_add, hx, hx']
  rw [rightComul, comp_apply, comp_apply, comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, h,
    LinearEquiv.apply_symm_apply, dualMap_apply, flip_apply]

variable [Module.Finite R A] [Module.Projective R A] [Module.Finite R B] [Module.Projective R B] in
/-- A perfect `R`-bilinear pairing `φ : A × B → R` of finite locally free (finite projective)
commutative `R`-algebras makes `(A, B, φ)` a **dual pair of algebras** (LMFDB
`modlgal.dual_pair_of_algebras`) if `φ(1, 1) = 1`, `φ(a a', 1) = φ(a, 1) φ(a', 1)`,
`φ(1, b b') = φ(1, b) φ(1, b')` and
`Φ⁽²⁾(μ₁(a) μ₁(a'), b ⊗ b') = φ(a a', b b') = Φ⁽²⁾(a ⊗ a', μ₂(b) μ₂(b'))` for all `a, a' ∈ A` and
`b, b' ∈ B`, where `Φ⁽²⁾` is `LinearMap.tensorPairing` and `μ₁`, `μ₂` are `LinearMap.leftComul` and
`LinearMap.rightComul`. The finiteness, projectivity and perfectness are the instance arguments.
The knowl writes `μ₂(b) μ₁(b')` in the last identity, a typo for `μ₂(b) μ₂(b')`. -/
structure IsDualPairOfAlgebras : Prop where
  /-- `φ(1, 1) = 1`. -/
  apply_one_one : φ 1 1 = 1
  /-- `φ(·, 1)` is multiplicative. -/
  apply_mul_one (a a' : A) : φ (a * a') 1 = φ a 1 * φ a' 1
  /-- `φ(1, ·)` is multiplicative. -/
  apply_one_mul (b b' : B) : φ 1 (b * b') = φ 1 b * φ 1 b'
  /-- `Φ⁽²⁾(μ₁(a) μ₁(a'), b ⊗ b') = φ(a a', b b')`. -/
  tensorPairing_leftComul_mul (a a' : A) (b b' : B) :
    φ.tensorPairing (φ.leftComul a * φ.leftComul a') (b ⊗ₜ b') = φ (a * a') (b * b')
  /-- `φ(a a', b b') = Φ⁽²⁾(a ⊗ a', μ₂(b) μ₂(b'))`. -/
  apply_mul_mul_eq_tensorPairing (a a' : A) (b b' : B) :
    φ (a * a') (b * b') = φ.tensorPairing (a ⊗ₜ a') (φ.rightComul b * φ.rightComul b')

end LinearMap
