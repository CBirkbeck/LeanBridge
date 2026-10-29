import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ModularForm
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Fourier expansions of Siegel modular forms

For a subgroup `Γ` of `Sp(2g, ℚ)`, the translation lattice `L_Γ` is the set of rational symmetric
`s` with `(1, s; 0, 1) ∈ Γ`, and its dual lattice `L_Γ^∨` is the set of rational symmetric `n` with
`tr(sn) ∈ ℤ` for every `s ∈ L_Γ`. A Siegel modular form `f` on `Γ` has a Fourier expansion
`f(τ) = ∑_{n ∈ L_Γ^∨} a(n) e^{2πi tr(nτ)}`.

## Main definitions

* `SiegelUpperHalfSpace.translationLattice`: the translation lattice `L_Γ`.
* `SiegelUpperHalfSpace.dualLattice`: its dual lattice `L_Γ^∨`.
* `SiegelUpperHalfSpace.HasSiegelFourierExpansion` (LMFDB `mf.siegel.q-expansion`): `a` is a
  family of Fourier coefficients of `f`.
* `SiegelUpperHalfSpace.KoecherPrinciple` (LMFDB `mf.siegel.koecher.principle`): the statement of
  the Koecher principle.
* `SiegelUpperHalfSpace.coefficientField` (LMFDB `mf.siegel.coefficient_field`): the coefficient
  field of a scalar-valued form.
* `SiegelUpperHalfSpace.coefficientRing` (LMFDB `mf.siegel.coefficient_ring`): its coefficient
  ring.
* `SiegelUpperHalfSpace.IsDefiningPolynomial` (LMFDB `mf.siegel.defining_polynomial`): a defining
  polynomial of the coefficient field.

## Main results

* `SiegelUpperHalfSpace.HasSiegelFourierExpansion.add` and
  `SiegelUpperHalfSpace.HasSiegelFourierExpansion.const_smul`: Fourier expansions are linear.
-/

open Complex Matrix Module Real

namespace SiegelUpperHalfSpace

variable {l : Type*} [Fintype l] [DecidableEq l] (Γ : Subgroup (symplecticGroup l ℚ))

/-- The **translation lattice** `L_Γ` of a subgroup `Γ` of `Sp(2g, ℚ)`: the rational symmetric
`g × g` matrices `s` with `(1, s; 0, 1) ∈ Γ`. -/
def translationLattice : AddSubgroup (Matrix l l ℚ) where
  carrier := {s | sᵀ = s ∧ ∃ γ ∈ Γ, (γ : Matrix (l ⊕ l) (l ⊕ l) ℚ) = fromBlocks 1 s 0 1}
  add_mem' {s t} hs ht := by
    rcases hs with ⟨hs, γ, hγ, hγs⟩
    rcases ht with ⟨ht, δ, hδ, hδt⟩
    refine ⟨by rw [transpose_add, hs, ht], γ * δ, Γ.mul_mem hγ hδ, ?_⟩
    rw [Submonoid.coe_mul, hγs, hδt, fromBlocks_multiply]
    simp [add_comm]
  zero_mem' := ⟨transpose_zero, 1, Γ.one_mem, by simp⟩
  neg_mem' {s} hs := by
    rcases hs with ⟨hs, γ, hγ, hγs⟩
    refine ⟨by rw [transpose_neg, hs], γ⁻¹, Γ.inv_mem hγ, ?_⟩
    have h : (γ : Matrix (l ⊕ l) (l ⊕ l) ℚ) * (γ⁻¹ : symplecticGroup l ℚ) = 1 := by
      rw [← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one]
    have h' : fromBlocks 1 (-s) 0 1 * (γ : Matrix (l ⊕ l) (l ⊕ l) ℚ) = 1 := by
      rw [hγs, fromBlocks_multiply]
      simp
    rw [← one_mul ((γ⁻¹ : symplecticGroup l ℚ) : Matrix (l ⊕ l) (l ⊕ l) ℚ), ← h', mul_assoc, h,
      mul_one]

/-- The **dual lattice** `L_Γ^∨` of the translation lattice of `Γ`: the rational symmetric `n` with
`tr(sn) ∈ ℤ` for every `s ∈ L_Γ`. -/
def dualLattice : AddSubgroup (Matrix l l ℚ) where
  carrier := {n | nᵀ = n ∧ ∀ s ∈ translationLattice Γ, ∃ z : ℤ, (s * n).trace = z}
  add_mem' {n m} hn hm := ⟨by rw [transpose_add, hn.1, hm.1], fun s hs ↦ by
    rcases hn.2 s hs with ⟨z, hz⟩
    rcases hm.2 s hs with ⟨w, hw⟩
    exact ⟨z + w, by rw [mul_add, trace_add, hz, hw, Int.cast_add]⟩⟩
  zero_mem' := ⟨transpose_zero, fun _ _ ↦ ⟨0, by simp⟩⟩
  neg_mem' {n} hn := ⟨by rw [transpose_neg, hn.1], fun s hs ↦ by
    rcases hn.2 s hs with ⟨z, hz⟩
    exact ⟨-z, by rw [mul_neg, trace_neg, hz, Int.cast_neg]⟩⟩

variable {Γ} in
/-- The exponential `e^{2πi tr(nτ)}` of the Fourier expansion of a Siegel modular form, for `n` in
the dual lattice `L_Γ^∨` and `τ ∈ ℋ_g`. -/
noncomputable def fourierExp (n : dualLattice Γ) (τ : SiegelUpperHalfSpace l) : ℂ :=
  cexp (2 * π * I * ((n : Matrix l l ℚ).map ((↑) : ℚ → ℂ) * τ.val).trace)

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {f g : SiegelUpperHalfSpace l → V}
    {a b : dualLattice Γ → V}

variable (f a) in
/-- The family `a : L_Γ^∨ → V` is **a family of Fourier coefficients** of `f : ℋ_g → V` (LMFDB
`mf.siegel.q-expansion`): `f(τ) = ∑_{n ∈ L_Γ^∨} a(n) e^{2πi tr(nτ)}` for every `τ ∈ ℋ_g`, the sum
converging unconditionally. As in `SiegelUpperHalfSpace.HasSiegelPhi`, the sum is taken
coordinatewise, through every linear form on `V`, which is the usual one when `V` is
finite-dimensional. The coefficients are unique when `L_Γ` contains `N · Sym_g(ℤ)` for some
`N ≠ 0` (`SiegelUpperHalfSpace.HasSiegelFourierExpansion.unique`); the existence of such an
expansion for a Siegel modular form on an arithmetic `Γ` is a theorem which is not proved here. -/
def HasSiegelFourierExpansion : Prop :=
  ∀ (τ : SiegelUpperHalfSpace l) (φ : Dual ℂ V),
    HasSum (fun n ↦ fourierExp n τ * φ (a n)) (φ (f τ))

/-- **Fourier expansions are additive**. -/
lemma HasSiegelFourierExpansion.add (hf : HasSiegelFourierExpansion Γ f a)
    (hg : HasSiegelFourierExpansion Γ g b) : HasSiegelFourierExpansion Γ (f + g) (a + b) :=
  fun τ φ ↦ by simpa [mul_add] using (hf τ φ).add (hg τ φ)

/-- **Fourier expansions are `ℂ`-linear**. -/
lemma HasSiegelFourierExpansion.const_smul (hf : HasSiegelFourierExpansion Γ f a) (c : ℂ) :
    HasSiegelFourierExpansion Γ (c • f) (c • a) :=
  fun τ φ ↦ by simpa [mul_left_comm] using (hf τ φ).mul_left c

variable (ρ : Representation ℂ (GL l ℂ) V)

/-- The **Koecher principle** (LMFDB `mf.siegel.koecher.principle`), as a statement: for degree
`g ≥ 2`, every Fourier coefficient `a(n) ≠ 0` of a Siegel modular form `f ∈ M_ρ(Γ)` is indexed by a
positive semidefinite `n`. It is a theorem for arithmetic `Γ`, which is not proved here. -/
def KoecherPrinciple : Prop :=
  2 ≤ Fintype.card l → ∀ f ∈ modularForms ρ Γ 1, ∀ a : dualLattice Γ → V,
    HasSiegelFourierExpansion Γ f a → ∀ n, a n ≠ 0 → (n : Matrix l l ℚ).PosSemidef

variable (F : SiegelUpperHalfSpace l → ℂ)

/-- The set of **Fourier coefficients** `a(n)` of the Fourier expansions of `F : ℋ_g → ℂ` on `Γ`.
When `L_Γ` contains `N · Sym_g(ℤ)` for some `N ≠ 0` (for instance when `Γ` is commensurable with
`Sp(2g, ℤ)`), the expansion is unique and this is the set of its coefficients
(`SiegelUpperHalfSpace.fourierCoeffs_eq_range`). -/
def fourierCoeffs : Set ℂ :=
  {c | ∃ a : dualLattice Γ → ℂ, HasSiegelFourierExpansion Γ F a ∧ ∃ n, a n = c}

/-- The **coefficient field** (LMFDB `mf.siegel.coefficient_field`) of a scalar-valued Siegel
modular form `F` on `Γ`: the subfield of `ℂ` generated by the Fourier coefficients `a(n)` of `F`,
indexed by `n ∈ L_Γ^∨` (the knowl's `∑ a_n q^n` stands for the Fourier expansion over `L_Γ^∨`).
When `L_Γ` contains `N · Sym_g(ℤ)` for some `N ≠ 0`, these are the coefficients of the unique
Fourier expansion of `F` (`SiegelUpperHalfSpace.fourierCoeffs_eq_range`). For a Hecke eigenform it
is also called the Hecke field. If `F` has no Fourier expansion on `Γ`, it is the junk value `ℚ`,
the subfield generated by the empty set. -/
noncomputable def coefficientField : Subfield ℂ :=
  Subfield.closure (fourierCoeffs Γ F)

/-- The **coefficient ring** (LMFDB `mf.siegel.coefficient_ring`) `ℤ[a(n)]` of a scalar-valued
Siegel modular form `F` on `Γ`: the subring of `ℂ` generated by its Fourier coefficients, those of
its unique Fourier expansion when `L_Γ` contains `N · Sym_g(ℤ)` for some `N ≠ 0`
(`SiegelUpperHalfSpace.fourierCoeffs_eq_range`). If `F` has no Fourier expansion on `Γ`, it is the
junk value `ℤ`. -/
def coefficientRing : Subring ℂ :=
  Subring.closure (fourierCoeffs Γ F)

/-- The polynomial `p ∈ ℚ[X]` is a **defining polynomial** (LMFDB `mf.siegel.defining_polynomial`)
of the coefficient field `K` of `F`: `K` is generated over `ℚ` by a root of `p`, with
`K ≅ ℚ[X]/(p)`. Which defining polynomial the LMFDB records is a database choice. -/
def IsDefiningPolynomial (p : Polynomial ℚ) : Prop :=
  Nonempty (IsAdjoinRoot (coefficientField Γ F) p)

lemma coefficientRing_le : coefficientRing Γ F ≤ (coefficientField Γ F).toSubring :=
  Subring.closure_le.mpr Subfield.subset_closure

end SiegelUpperHalfSpace
