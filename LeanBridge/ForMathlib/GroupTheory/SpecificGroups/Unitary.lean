import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# Finite unitary groups

For a field `K` with a ring endomorphism `σ` (the "conjugation"), a matrix `M ∈ GL_n(K)` is
`σ`-unitary if its inverse is its `σ`-conjugate transpose `(M.map σ)ᵀ`. Over `𝔽_{q²}` with
`σ x = x ^ q`, these form the general unitary group `GU(n, q)`; its subgroup of matrices of
determinant `1` is `SU(n, q)`, and `PGU(n, q)`, `PSU(n, q)` are their quotients by the scalar
matrices they contain. Mathlib's `Matrix.unitaryGroup` needs a star ring, which `𝔽_{q²}` is not
given, hence the definitions here.

Here `q = p ^ r` and `𝔽_{q²}` is `GaloisField p (2 * r)`. The scalar matrices are the centre of
`GL_n` (Mathlib's `Matrix.GeneralLinearGroup.center_eq_range_scalar`), so the scalar matrices of
`GU(n, q)` are `(Subgroup.center (GL n K)).subgroupOf GU(n, q)`. The knowl's remark that they form
the centre of `GU(n, q)` (and of `SU(n, q)`) is not proved here.

## Main definitions

* `Matrix.sesquiUnitaryGroup`: the `σ`-unitary matrices in `GL_n(K)`.
* `Matrix.generalUnitaryGroup` (LMFDB `group.unitary`): `GU(n, q)`.
* `Matrix.specialUnitaryGroupFq` (LMFDB `group.unitary`): `SU(n, q)`.
* `Matrix.projectiveGeneralUnitaryGroup` (LMFDB `group.unitary`): `PGU(n, q)`.
* `Matrix.projectiveSpecialUnitaryGroup` (LMFDB `group.unitary`): `PSU(n, q)`.

## Main results

* `Matrix.mem_sesquiUnitaryGroup_iff`: a matrix is `σ`-unitary exactly when its inverse is its
  `σ`-conjugate transpose.
-/

namespace Matrix

variable {K : Type*} [Field K] (σ : K →+* K) (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The **`σ`-unitary group**: the invertible matrices `M` over `K` whose inverse is the
`σ`-conjugate transpose `(M.map σ)ᵀ`, i.e. with `M * (M.map σ)ᵀ = 1`. -/
def sesquiUnitaryGroup : Subgroup (GL ι K) where
  carrier := {g | (g : Matrix ι ι K) * ((g : Matrix ι ι K).map σ)ᵀ = 1}
  one_mem' := by
    simp
  mul_mem' {a b} ha hb := by
    rw [Set.mem_ofPred_eq, Units.val_mul, Matrix.map_mul, transpose_mul, mul_assoc,
      ← mul_assoc (b : Matrix ι ι K), hb, one_mul, ha]
  inv_mem' {a} ha := by
    have h₁ : ((a : Matrix ι ι K).map σ)ᵀ = (a⁻¹ : GL ι K) := by
      rw [← one_mul ((a : Matrix ι ι K).map σ)ᵀ, ← Units.inv_mul a, mul_assoc, ha, mul_one]
    have h₂ :
        (((a⁻¹ : GL ι K) : Matrix ι ι K).map σ)ᵀ * ((a : Matrix ι ι K).map σ)ᵀ = 1 := by
      rw [← transpose_mul, ← Matrix.map_mul, Units.mul_inv]
      simp
    rw [h₁] at h₂
    exact mul_eq_one_comm.mp h₂

variable {σ ι} in
/-- A matrix is `σ`-unitary exactly when its inverse is its `σ`-conjugate transpose. -/
lemma mem_sesquiUnitaryGroup_iff {g : GL ι K} :
    g ∈ sesquiUnitaryGroup σ ι ↔ ((g : Matrix ι ι K).map σ)ᵀ = (g⁻¹ : GL ι K) := by
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · rw [← one_mul ((g : Matrix ι ι K).map σ)ᵀ, ← Units.inv_mul g, mul_assoc]
    exact (congrArg _ hg).trans <| mul_one _
  · exact (congrArg _ hg).trans <| Units.mul_inv g

variable (n p r : ℕ) [Fact p.Prime]

/-- The **general unitary group** `GU(n, q)`, `q = p ^ r` (LMFDB `group.unitary`): the `n × n`
matrices over `𝔽_{q²} = GaloisField p (2 r)` whose inverse is their conjugate transpose, the
conjugate of an entry `x` being `x ^ q`. -/
noncomputable abbrev generalUnitaryGroup : Subgroup (GL (Fin n) (GaloisField p (2 * r))) :=
  sesquiUnitaryGroup (iterateFrobenius (GaloisField p (2 * r)) p r) (Fin n)

/-- The **special unitary group** `SU(n, q)` (LMFDB `group.unitary`): the matrices of
determinant `1` in `GU(n, q)`. -/
noncomputable abbrev specialUnitaryGroupFq : Subgroup (GL (Fin n) (GaloisField p (2 * r))) :=
  generalUnitaryGroup n p r ⊓ GeneralLinearGroup.det.ker

/-- The **projective (general) unitary group** `PGU(n, q)` (LMFDB `group.unitary`): the
quotient of `GU(n, q)` by its scalar matrices, the elements of the centre of `GL_n`. -/
noncomputable abbrev projectiveGeneralUnitaryGroup : Type :=
  generalUnitaryGroup n p r ⧸
    (Subgroup.center (GL (Fin n) (GaloisField p (2 * r)))).subgroupOf (generalUnitaryGroup n p r)

/-- The **projective special unitary group** `PSU(n, q)` (LMFDB `group.unitary`): the quotient
of `SU(n, q)` by its scalar matrices. -/
noncomputable abbrev projectiveSpecialUnitaryGroup : Type :=
  specialUnitaryGroupFq n p r ⧸
    (Subgroup.center (GL (Fin n) (GaloisField p (2 * r)))).subgroupOf (specialUnitaryGroupFq n p r)

end Matrix
