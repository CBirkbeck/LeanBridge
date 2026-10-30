import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.GaloisRepresentation
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.LPolynomial
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import TauCeti.AlgebraicGeometry.AbelianVariety.Trivial

/-!
# The Weil polynomial and the L-polynomial of an abelian variety over a finite field

Let `A` be an abelian variety of dimension `g` over a finite field `K = 𝔽_q`, and `ℓ` a prime
different from the characteristic of `K`. The `q`-power Frobenius endomorphism `F` of `A` induces an
endomorphism of the `ℓ`-adic Tate module `T_ℓ A`, whose characteristic polynomial
`P_A(t) = det(t - F | T_ℓ A)` is the Weil polynomial, or characteristic polynomial, of `A` (LMFDB
`av.fq.weil_polynomial`); its reverse `L_A(t) = det(1 - t F | T_ℓ A)` is the L-polynomial of `A`
(LMFDB `av.fq.l-polynomial`). By Weil, `P_A` has integer coefficients independent of `ℓ`, and it is
a Weil `q`-polynomial of degree `2g` (LMFDB `nf.weil_polynomial`).

The Frobenius endomorphism raises the coordinates of points to the `q`-th power, so it acts on the
points `A(𝔽̄_q)` as the arithmetic Frobenius `x ↦ x ^ q` of `Gal(𝔽̄_q / 𝔽_q)`. This is how it is
realised here (`TauCeti.AlgebraicGeometry.AbelianVariety.frobeniusTate`), through the `ℓ`-adic
Galois representation of `A` (`TauCeti.AlgebraicGeometry.AbelianVariety.tateModuleRep`), Tau Ceti
having no Frobenius endomorphism of an abelian variety. The knowl's second description, with the
geometric Frobenius `F_q`, the inverse of `x ↦ x ^ q`, acting on
`H¹(A_{𝔽̄_q}, ℚ_ℓ) = Hom(T_ℓ A, ℚ_ℓ)`, gives the same polynomials, as `F_q` acts there as the
transpose of `F`; étale cohomology is not available.

That `T_ℓ A` is free of rank `2g` over `ℤ_ℓ`, and Weil's theorems, are not formalised. So the Weil
polynomial is formalised as a property of a polynomial `h ∈ ℤ[x]`: for every prime `ℓ` invertible
in `K`, `T_ℓ A` has a finite basis over `ℤ_ℓ` in which `F` has characteristic polynomial `h`. An
abelian variety has at most one Weil polynomial, and by these theorems it has exactly one; the
trivial abelian variety has the Weil polynomial `1`. The same goes for the L-polynomial, and the two
are each other's reverse.

## Main definitions

* `TauCeti.AlgebraicGeometry.AbelianVariety.frobeniusTate` (LMFDB `av.fq.weil_polynomial`): the
  `q`-power Frobenius `F` acting on `T_ℓ A`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.HasWeilPolynomial` (LMFDB `av.fq.weil_polynomial`): `h`
  is the Weil polynomial `det(t - F | T_ℓ A)` of `A`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.HasLPolynomial` (LMFDB `av.fq.l-polynomial`): `L` is the
  L-polynomial `det(1 - t F | T_ℓ A)` of `A`.

## Main results

* `TauCeti.AlgebraicGeometry.AbelianVariety.HasWeilPolynomial.eq`: an abelian variety over a finite
  field has at most one Weil polynomial.
* `TauCeti.AlgebraicGeometry.AbelianVariety.HasLPolynomial.eq`: it has at most one L-polynomial.
* `TauCeti.AlgebraicGeometry.AbelianVariety.hasWeilPolynomial_trivial`: the trivial abelian variety,
  of dimension `0`, has the Weil polynomial `1`, so that the definition is not vacuous.
* `TauCeti.AlgebraicGeometry.AbelianVariety.HasWeilPolynomial.hasLPolynomial_reverse`: the reverse
  of the Weil polynomial is the L-polynomial.
* `TauCeti.AlgebraicGeometry.AbelianVariety.HasLPolynomial.hasWeilPolynomial_reverse`: the reverse
  of the L-polynomial is the Weil polynomial.
-/

open Polynomial

universe u

namespace TauCeti.AlgebraicGeometry.AbelianVariety

private lemma of_forall_prime_natCast_ne_zero (F : Type*) [Field F] {P : Prop}
    (h : ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : F) ≠ 0 → P) : P := by
  by_cases h2 : ((2 : ℕ) : F) = 0
  · exact h 3 fun h3 ↦ one_ne_zero (α := F) <| by linear_combination h3 - h2
  · exact h 2 h2

variable {K : Type u} [Field K] [Fintype K] (A : AbelianVariety K) (ℓ : ℕ) [Fact ℓ.Prime]
  {h h' L L' : ℤ[X]}

/-- The **`q`-power Frobenius** (LMFDB `av.fq.weil_polynomial`) of an abelian variety `A` over a
finite field `K = 𝔽_q`, acting on the `ℓ`-adic Tate module `T_ℓ A`: the image of the arithmetic
Frobenius `x ↦ x ^ q` of `Gal(Kˢ / K)` under the `ℓ`-adic Galois representation of `A`. The
Frobenius endomorphism of `A` acts in this way on the points `A(Kˢ)`, as it raises their
coordinates to the `q`-th power. -/
noncomputable def frobeniusTate : Module.End ℤ_[ℓ] (TateModule ℓ (A.PointCoeff K)) :=
  A.tateModuleRep ℓ (FiniteField.frobeniusAlgEquivOfAlgebraic K (SeparableClosure K))

variable (h) in
/-- A polynomial `h ∈ ℤ[x]` is the **Weil polynomial**, or **characteristic polynomial** (LMFDB
`av.fq.weil_polynomial`), of an abelian variety `A` over a finite field `K = 𝔽_q` if, for every
prime `ℓ` invertible in `K`, it is the characteristic polynomial `P_A(t) = det(t - F | T_ℓ A)` of
the `q`-power Frobenius `F` acting on the `ℓ`-adic Tate module `T_ℓ A` (`frobeniusTate`), in some
basis of `T_ℓ A` over `ℤ_ℓ`. An abelian variety has at most one Weil polynomial
(`HasWeilPolynomial.eq`). That `T_ℓ A` is free of rank `2 dim A` and that the characteristic
polynomial of `F` has integer coefficients independent of `ℓ` (Weil), so that every abelian variety
over `K` has a Weil polynomial, are not formalised. -/
def HasWeilPolynomial : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 → ∃ (n : ℕ)
    (b : Module.Basis (Fin n) ℤ_[ℓ] (TateModule ℓ (A.PointCoeff K))),
    (LinearMap.toMatrix b b (A.frobeniusTate ℓ)).charpoly = h.map (Int.castRingHom ℤ_[ℓ])

variable (L) in
/-- A polynomial `L ∈ ℤ[x]` is the **L-polynomial** (LMFDB `av.fq.l-polynomial`) of an abelian
variety `A` over a finite field `K = 𝔽_q` if, for every prime `ℓ` invertible in `K`, it is the
polynomial `L_A(t) = det(1 - t F | T_ℓ A)` of the `q`-power Frobenius `F` acting on the `ℓ`-adic
Tate module `T_ℓ A` (`frobeniusTate`), in some basis of `T_ℓ A` over `ℤ_ℓ` (Mathlib's
`Matrix.charpolyRev`). The L-polynomial and the Weil polynomial are each other's reverse
(`HasWeilPolynomial.hasLPolynomial_reverse`, `HasLPolynomial.hasWeilPolynomial_reverse`). -/
def HasLPolynomial : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 → ∃ (n : ℕ)
    (b : Module.Basis (Fin n) ℤ_[ℓ] (TateModule ℓ (A.PointCoeff K))),
    (LinearMap.toMatrix b b (A.frobeniusTate ℓ)).charpolyRev = L.map (Int.castRingHom ℤ_[ℓ])

variable {A ℓ}

lemma HasWeilPolynomial.eq_of_natCast_ne_zero (hh : A.HasWeilPolynomial h)
    (hh' : A.HasWeilPolynomial h') (hℓ : (ℓ : K) ≠ 0) : h = h' := by
  rcases hh ℓ hℓ with ⟨n, b, hb⟩
  rcases hh' ℓ hℓ with ⟨n', b', hb'⟩
  have hfree : Module.Free ℤ_[ℓ] (TateModule ℓ (A.PointCoeff K)) := .of_basis b
  have hfin : Module.Finite ℤ_[ℓ] (TateModule ℓ (A.PointCoeff K)) := .of_basis b
  refine map_injective _ (Int.castRingHom ℤ_[ℓ]).injective_int ?_
  rw [← hb, ← hb', LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]

/-- **An abelian variety over a finite field has at most one Weil polynomial**: the characteristic
polynomial of an endomorphism of a free module of finite rank does not depend on the basis. -/
lemma HasWeilPolynomial.eq (hh : A.HasWeilPolynomial h) (hh' : A.HasWeilPolynomial h') : h = h' :=
  of_forall_prime_natCast_ne_zero K fun _ _ hℓ ↦ hh.eq_of_natCast_ne_zero hh' hℓ

lemma HasLPolynomial.eq_of_natCast_ne_zero (hL : A.HasLPolynomial L) (hL' : A.HasLPolynomial L')
    (hℓ : (ℓ : K) ≠ 0) : L = L' := by
  rcases hL ℓ hℓ with ⟨n, b, hb⟩
  rcases hL' ℓ hℓ with ⟨n', b', hb'⟩
  have hfree : Module.Free ℤ_[ℓ] (TateModule ℓ (A.PointCoeff K)) := .of_basis b
  have hfin : Module.Finite ℤ_[ℓ] (TateModule ℓ (A.PointCoeff K)) := .of_basis b
  refine map_injective _ (Int.castRingHom ℤ_[ℓ]).injective_int ?_
  rw [← hb, ← hb', ← Matrix.reverse_charpoly, ← Matrix.reverse_charpoly,
    LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]

/-- **An abelian variety over a finite field has at most one L-polynomial**: the characteristic
polynomial of an endomorphism of a free module of finite rank, and so its reverse, does not depend
on the basis. -/
lemma HasLPolynomial.eq (hL : A.HasLPolynomial L) (hL' : A.HasLPolynomial L') : L = L' :=
  of_forall_prime_natCast_ne_zero K fun _ _ hℓ ↦ hL.eq_of_natCast_ne_zero hL' hℓ

/-- **The trivial abelian variety has the Weil polynomial `1`**, of degree `2 · 0`: its points form
the trivial group, so that its Tate modules are zero, with the empty basis. In particular, the
definition of the Weil polynomial is not vacuous. -/
lemma hasWeilPolynomial_trivial : (trivial K).HasWeilPolynomial 1 := by
  rintro ℓ _ -
  have : Subsingleton ((trivial K).PointCoeff K) := ⟨fun a b ↦ congrArg Additive.ofMul <|
    (isTerminalTrivialToOver K).hom_ext (Additive.toMul a) (Additive.toMul b)⟩
  have : Subsingleton (TateModule ℓ ((trivial K).PointCoeff K)) :=
    ⟨fun x y ↦ TateModule.ext fun n ↦ Subsingleton.elim _ _⟩
  exact ⟨0, .empty _, by simp⟩

/-- **The L-polynomial is the reverse of the Weil polynomial** (LMFDB `av.fq.l-polynomial`):
`det(1 - t F) = t^n det(t - F)(1 / t)` for an endomorphism `F` of a free module of rank `n`. -/
lemma HasWeilPolynomial.hasLPolynomial_reverse (hh : A.HasWeilPolynomial h) :
    A.HasLPolynomial h.reverse := by
  intro ℓ _ hℓ
  rcases hh ℓ hℓ with ⟨n, b, hb⟩
  refine ⟨n, b, ?_⟩
  rw [← Matrix.reverse_charpoly, hb, reverse_map_of_injective (Int.castRingHom ℤ_[ℓ]).injective_int]

/-- **The Weil polynomial is the reverse of the L-polynomial** (LMFDB `av.fq.weil_polynomial`): the
Frobenius `F` acts invertibly on `T_ℓ A`, as an element of the Galois group, so that its
characteristic polynomial has a nonzero constant term `± det F`, and is the reverse of its reverse
`det(1 - t F)`. -/
lemma HasLPolynomial.hasWeilPolynomial_reverse (hL : A.HasLPolynomial L) :
    A.HasWeilPolynomial L.reverse := by
  intro ℓ _ hℓ
  rcases hL ℓ hℓ with ⟨n, b, hb⟩
  refine ⟨n, b, ?_⟩
  have hu : IsUnit (LinearMap.toMatrix b b (A.frobeniusTate ℓ)) :=
    ((A.tateModuleRep ℓ).asGroupHom
      (FiniteField.frobeniusAlgEquivOfAlgebraic K (SeparableClosure K))).isUnit.map
      (LinearMap.toMatrixAlgEquiv b)
  have h0 : (LinearMap.toMatrix b b (A.frobeniusTate ℓ)).charpoly.coeff 0 ≠ 0 := by
    intro h0
    refine ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero ?_
    rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero]
  rw [← reverse_map_of_injective (Int.castRingHom ℤ_[ℓ]).injective_int, ← hb,
    ← Matrix.reverse_charpoly, reverse_reverse h0]

end TauCeti.AlgebraicGeometry.AbelianVariety
