import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.NewformSubspace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Hecke characteristic polynomials of newforms

The Hecke characteristic polynomial of a newform `f` at a prime `p` (LMFDB `cmf.heckecharpolys`) is
the characteristic polynomial of the Hecke operator `T_p` acting on the newform subspace `V_f`. The
Galois conjugates `g` of `f` form an eigenbasis of `V_f`, with eigenvalues `a_p(g)`, so it is
`∏_{g ∈ [f]} (X - a_p(g))`. The LMFDB records it with integer coefficients, computed on the rational
structure of `V_f`; here `V_f` is the complex span of the Galois orbit, whose characteristic
polynomial is the same polynomial seen in `ℂ[X]`. That its coefficients are integers is not proved
here.

A set of Hecke operators `T_p` distinguishes the newforms of a space of newforms (LMFDB
`cmf.distinguishing_primes`) if their characteristic polynomials on the newform subspaces separate
the Galois orbits. The sequence of distinguishing primes that the LMFDB lists, chosen greedily, is
formalised in `LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.DistinguishingPrimes`.

## Main definitions

* `HeckeRing.GL2.Newform.heckeCharpoly`: the Hecke characteristic polynomial of a newform at a prime
  (LMFDB `cmf.heckecharpolys`).
* `HeckeRing.GL2.Newform.DistinguishesNewforms`: a set of primes distinguishes the newforms of a
  space `S_k^{new}(N, χ)` (LMFDB `cmf.distinguishing_primes`).

## Main results

* `HeckeRing.GL2.Newform.heckeCharpoly_eq_prod`: the Hecke characteristic polynomial of `f` at `p`
  is `∏_{g ∈ [f]} (X - a_p(g))`.
* `HeckeRing.GL2.Newform.IsGaloisConjugate.heckeCharpoly_eq`: it only depends on the Galois orbit of
  `f`.
* `HeckeRing.GL2.Newform.distinguishesNewforms_empty_iff`: no prime is needed to distinguish the
  newforms of a space exactly when they form a single Galois orbit.
-/

open UpperHalfPlane TauCeti CongruenceSubgroup Matrix.SpecialLinearGroup Polynomial Module

open scoped MatrixGroups

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} {f g : Newform N k} {p : ℕ} (hp : p.Prime) {χ : (ZMod N)ˣ →* ℂˣ}
  {T T' : Set Nat.Primes}

variable (f) in
/-- The **Hecke characteristic polynomial** of a newform `f` at a prime `p`
(LMFDB `cmf.heckecharpolys`): the characteristic polynomial of the Hecke operator `T_p` acting on
the newform subspace `V_f`. The LMFDB computes it on the rational structure of `V_f`, which gives
the same polynomial, with integer coefficients. -/
noncomputable def heckeCharpoly : ℂ[X] :=
  haveI : NeZero p := ⟨hp.ne_zero⟩
  ((heckeTCuspNat k p).restrict fun _ ↦ heckeTCuspNat_mem_newformSubspace hp :
    Module.End ℂ f.newformSubspace).charpoly

variable (f) in
/-- **The Hecke characteristic polynomial of `f` at `p` is `∏_{g ∈ [f]} (X - a_p(g))`**: the
Galois orbit of `f` is a basis of `V_f` of eigenvectors of `T_p`, with eigenvalues `a_p(g)`. -/
lemma heckeCharpoly_eq_prod : f.heckeCharpoly hp = ∏ g ∈ f.finite_galoisOrbit.toFinset,
    (X - C ((qExpansion 1 g.toCuspForm).coeff p)) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  let _ : Fintype f.galoisOrbit := f.finite_galoisOrbit.fintype
  rw [heckeCharpoly, ← LinearMap.charpoly_toMatrix _ f.galoisOrbitBasis]
  have h : LinearMap.toMatrix f.galoisOrbitBasis f.galoisOrbitBasis ((heckeTCuspNat k p).restrict
      fun _ ↦ heckeTCuspNat_mem_newformSubspace hp) =
      Matrix.diagonal fun g : f.galoisOrbit ↦ (qExpansion 1 g.1.toCuspForm).coeff p := by
    ext i j
    have hj : (heckeTCuspNat k p).restrict (fun _ ↦ heckeTCuspNat_mem_newformSubspace hp)
        (f.galoisOrbitBasis j) = (qExpansion 1 j.1.toCuspForm).coeff p • f.galoisOrbitBasis j :=
      Subtype.ext <| by simp [j.1.heckeTCuspNat_eq_qExpansion_coeff_smul hp]
    rw [LinearMap.toMatrix_apply, hj, map_smul, Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, Matrix.diagonal_apply]
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [hij, hij.symm]
  rw [h, Matrix.charpoly_diagonal]
  exact Finset.prod_set_coe (f := fun g : Newform N k ↦ X - C ((qExpansion 1 g.toCuspForm).coeff p))
    f.galoisOrbit

/-- **The Hecke characteristic polynomials of Galois conjugate newforms are equal**: they only
depend on the Galois orbit. -/
lemma IsGaloisConjugate.heckeCharpoly_eq (hfg : f.IsGaloisConjugate g) :
    f.heckeCharpoly hp = g.heckeCharpoly hp := by
  simp only [heckeCharpoly_eq_prod, galoisOrbit_eq_iff.mpr hfg]

variable (N k χ T) in
/-- A set `T` of primes **distinguishes** the newforms of the space `S_k^{new}(N, χ)` (LMFDB
`cmf.distinguishing_primes`) if the Hecke characteristic polynomials at the primes `p ∈ T`, i.e. the
characteristic polynomials of the `T_p` on the newform subspaces, separate the Galois orbits of the
newforms of nebentypus `χ`: newforms of nebentypus `χ` with the same characteristic polynomials at
every `p ∈ T` are Galois conjugate. -/
def DistinguishesNewforms : Prop :=
  ∀ f g : Newform N k, f.χ = χ → g.χ = χ → (∀ p ∈ T, f.heckeCharpoly p.2 = g.heckeCharpoly p.2) →
    f.IsGaloisConjugate g

lemma DistinguishesNewforms.mono (hT : DistinguishesNewforms N k χ T) (hTT' : T ⊆ T') :
    DistinguishesNewforms N k χ T' :=
  fun f g hf hg h ↦ hT f g hf hg fun p hp ↦ h p (hTT' hp)

/-- **The empty set distinguishes the newforms of `S_k^{new}(N, χ)` exactly when they form a single
Galois orbit**, in which case the LMFDB lists no distinguishing primes. -/
lemma distinguishesNewforms_empty_iff : DistinguishesNewforms N k χ ∅ ↔ ∀ f g : Newform N k,
    f.χ = χ → g.χ = χ → f.IsGaloisConjugate g :=
  ⟨fun h f g hf hg ↦ h f g hf hg fun _ hp ↦ hp.elim, fun h f g hf hg _ ↦ h f g hf hg⟩

end HeckeRing.GL2.Newform
