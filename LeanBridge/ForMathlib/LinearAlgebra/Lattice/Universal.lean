import Mathlib.NumberTheory.SumFourSquares
import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.LinearAlgebra.IntegralLattice.Even
import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Finite
import TauCeti.LinearAlgebra.IntegralLattice.Unit
import TauCeti.LinearAlgebra.QuadraticForm.Representation

/-!
# Universal integral lattices

The quadratic form (LMFDB `lattice.quadratic_form`) of an integral lattice `L` with Gram matrix `G`
is `Q(v) = ⟨v, v⟩ = vᵀ G v` on `L ⊗ ℚ`, and `Q(v)` is the norm of `v`. These are Tau Ceti's
`TauCeti.IntegralLattice.norm`, a quadratic form on the rational span of `L`, and its restriction
`TauCeti.IntegralLattice.integralNorm` to `L`, so that `Q(L) ⊆ ℤ`. The LMFDB calls `L` (or `Q`)
universal if `Q(L) = ℤ`, and even universal if `Q(L) ⊇ 2ℤ`.

Taken literally, neither condition ever holds for a positive definite lattice, for which
`Q(L) ⊆ ℤ_{≥0}`; universality of a positive definite lattice is the classical condition
`Q(L) = ℤ_{≥0}`, that `Q` represents every positive integer. Both conditions are therefore read
here with the sign of `Q`: `L` is universal if `Q` represents every positive integer, and every
negative integer as well as soon as `L` has a vector of negative norm, and similarly for even
integers. For a positive semidefinite lattice this says `Q(L) = ℤ_{≥0}` (respectively
`Q(L) ⊇ 2ℤ_{≥0}`), and for a lattice with a vector of negative norm, an indefinite lattice for
instance, it is literally `Q(L) = ℤ` (respectively `Q(L) ⊇ 2ℤ`). The literal reading is thus only
changed where it can never hold; in particular a negative definite lattice, of a signature `(0, n)`
which the LMFDB does not store (its lattices have `n₊ ≥ n₋`), is never universal, as literally.

## Main definitions

* `TauCeti.IntegralLattice.IsUniversal` (LMFDB `lattice.quadratic_form`).
* `TauCeti.IntegralLattice.IsEvenUniversal` (LMFDB `lattice.quadratic_form`).

## Main results

* `TauCeti.IntegralLattice.isUniversal_iff_range_eq_Ici`: a positive semidefinite lattice is
  universal exactly when `Q(L) = ℤ_{≥0}`.
* `TauCeti.IntegralLattice.isUniversal_iff_range_eq_univ` and
  `TauCeti.IntegralLattice.IsIndefinite.isUniversal_iff`: a lattice with a vector of negative norm,
  for instance an indefinite lattice, is universal exactly when `Q(L) = ℤ`.
* `TauCeti.IntegralLattice.isEvenUniversal_iff_subset_range`,
  `TauCeti.IntegralLattice.isEvenUniversal_iff_subset_range_of_exists` and
  `TauCeti.IntegralLattice.IsIndefinite.isEvenUniversal_iff`: the same for even universality, with
  `2ℤ_{≥0} ⊆ Q(L)` and `2ℤ ⊆ Q(L)`.
* `TauCeti.IntegralLattice.IsEven.not_isUniversal`: an even lattice is never universal.
* `TauCeti.IntegralLattice.isUniversal_unitLattice_fin_four`: the lattice `ℤ⁴` with the sum of
  four squares is universal (Lagrange).
-/

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V) {v : V}

variable (v) in
lemma exists_zsmul_mem_carrier : ∃ n : ℤ, n ≠ 0 ∧ n • v ∈ L.carrier := by
  rcases IsLocalizedModule.surj (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ L 1)
    ((Submodule.rationalizationEquiv L.carrier).symm v) with ⟨⟨x, n⟩, hx⟩
  have h : (n : ℤ) • v = x := by
    simpa [Submonoid.smul_def] using congrArg (Submodule.rationalizationEquiv L.carrier) hx
  exact ⟨n, nonZeroDivisors.coe_ne_zero n, h ▸ x.2⟩

lemma integralNorm_mk_zsmul {n : ℤ} (h : n • v ∈ L.carrier) :
    (L.integralNorm ⟨n • v, h⟩ : ℚ) = (n : ℚ) ^ 2 * L.form v v := by
  rw [integralNorm_cast, Submodule.coe_mk, ← Int.cast_smul_eq_zsmul ℚ, norm_smul, norm_apply]

variable {L} in
lemma IsIndefinite.exists_integralNorm_neg (hL : L.IsIndefinite) :
    ∃ x : L, L.integralNorm x < 0 := by
  rcases (L.isIndefinite_iff_exists_pos_and_exists_neg.mp hL).2 with ⟨v, hv⟩
  rcases L.exists_zsmul_mem_carrier v with ⟨n, hn, hmem⟩
  have h : (L.integralNorm ⟨n • v, hmem⟩ : ℚ) < 0 :=
    L.integralNorm_mk_zsmul hmem ▸ mul_neg_of_pos_of_neg (by positivity) hv
  exact ⟨⟨n • v, hmem⟩, by exact_mod_cast h⟩

/-- An integral lattice `L` is **universal** (LMFDB `lattice.quadratic_form`) if its quadratic form
`Q` satisfies `Q(L) = ℤ`, read with the sign of `Q`: `Q` represents every positive integer, and
every negative integer as well if `L` has a vector of negative norm. For a positive semidefinite
lattice, for which the literal condition `Q(L) = ℤ` cannot hold, this is the classical universality
`Q(L) = ℤ_{≥0}` (`isUniversal_iff_range_eq_Ici`), and otherwise it is the literal `Q(L) = ℤ`
(`isUniversal_iff_range_eq_univ`), which a negative definite lattice never satisfies. -/
def IsUniversal : Prop :=
  ∀ n : ℤ, (0 < n ∨ ∃ x : L, L.integralNorm x < 0) → L.integralNorm.Represents n

/-- An integral lattice `L` is **even universal** (LMFDB `lattice.quadratic_form`) if its quadratic
form `Q` satisfies `Q(L) ⊇ 2ℤ`, read with the sign of `Q` as for `IsUniversal`: `Q` represents
every positive even integer, and every negative even integer as well if `L` has a vector of
negative norm. For a positive semidefinite lattice this is `Q(L) ⊇ 2ℤ_{≥0}`, and otherwise it is
`Q(L) ⊇ 2ℤ` (`isEvenUniversal_iff_subset_range`, `isEvenUniversal_iff_subset_range_of_exists`). -/
def IsEvenUniversal : Prop :=
  ∀ n : ℤ, Even n → (0 < n ∨ ∃ x : L, L.integralNorm x < 0) → L.integralNorm.Represents n

variable {L}

/-- **A positive semidefinite lattice is universal exactly when `Q(L) = ℤ_{≥0}`.** -/
lemma isUniversal_iff_range_eq_Ici (hL : L.IsPosSemidef) :
    L.IsUniversal ↔ Set.range L.integralNorm = Set.Ici 0 := by
  refine ⟨fun h ↦ Set.eq_of_subset_of_subset ?_ fun n hn ↦ ?_, fun h n hn ↦ ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hL.integralNorm_nonneg x
  · rcases (Set.mem_Ici.mp hn).eq_or_lt with rfl | hn
    · exact ⟨0, L.integralNorm_zero⟩
    · exact h n (Or.inl hn)
  · rcases hn with hn | ⟨x, hx⟩
    · exact (h ▸ Set.mem_Ici.mpr hn.le : n ∈ Set.range L.integralNorm)
    · exact absurd (hL.integralNorm_nonneg x) hx.not_ge

/-- **A lattice with a vector of negative norm is universal exactly when `Q(L) = ℤ`.** -/
lemma isUniversal_iff_range_eq_univ (h : ∃ x : L, L.integralNorm x < 0) :
    L.IsUniversal ↔ Set.range L.integralNorm = Set.univ :=
  ⟨fun hU ↦ Set.eq_univ_of_forall fun n ↦ hU n (Or.inr h),
    fun hU n _ ↦ (hU ▸ Set.mem_univ n : n ∈ Set.range L.integralNorm)⟩

/-- **An indefinite lattice is universal exactly when `Q(L) = ℤ`.** -/
lemma IsIndefinite.isUniversal_iff (hL : L.IsIndefinite) :
    L.IsUniversal ↔ Set.range L.integralNorm = Set.univ :=
  isUniversal_iff_range_eq_univ hL.exists_integralNorm_neg

/-- **A positive semidefinite lattice is even universal exactly when `Q(L) ⊇ 2ℤ_{≥0}`.** -/
lemma isEvenUniversal_iff_subset_range (hL : L.IsPosSemidef) :
    L.IsEvenUniversal ↔ {n : ℤ | 0 ≤ n ∧ Even n} ⊆ Set.range L.integralNorm := by
  refine ⟨fun h n hn ↦ ?_, fun h n hn hpos ↦ ?_⟩
  · rcases hn.1.eq_or_lt with rfl | hpos
    · exact ⟨0, L.integralNorm_zero⟩
    · exact h n hn.2 (Or.inl hpos)
  · rcases hpos with hpos | ⟨x, hx⟩
    · exact h ⟨hpos.le, hn⟩
    · exact absurd (hL.integralNorm_nonneg x) hx.not_ge

/-- **A lattice with a vector of negative norm is even universal exactly when `Q(L) ⊇ 2ℤ`.** -/
lemma isEvenUniversal_iff_subset_range_of_exists (h : ∃ x : L, L.integralNorm x < 0) :
    L.IsEvenUniversal ↔ {n : ℤ | Even n} ⊆ Set.range L.integralNorm :=
  ⟨fun hU n hn ↦ hU n hn (Or.inr h), fun hU _ hn _ ↦ hU hn⟩

/-- **An indefinite lattice is even universal exactly when `Q(L) ⊇ 2ℤ`.** -/
lemma IsIndefinite.isEvenUniversal_iff (hL : L.IsIndefinite) :
    L.IsEvenUniversal ↔ {n : ℤ | Even n} ⊆ Set.range L.integralNorm :=
  isEvenUniversal_iff_subset_range_of_exists hL.exists_integralNorm_neg

lemma IsUniversal.isEvenUniversal (hL : L.IsUniversal) : L.IsEvenUniversal :=
  fun n _ ↦ hL n

/-- **An even lattice is never universal**, as `Q(L) ⊆ 2ℤ` does not contain `1`. -/
lemma IsEven.not_isUniversal (hL : L.IsEven) : ¬L.IsUniversal :=
  fun hU ↦ (hU 1 (Or.inl one_pos)).elim fun x hx ↦ Int.not_even_one (hx ▸ hL x)

/-- **The lattice `ℤ⁴` with the form `x₁² + x₂² + x₃² + x₄²`, Tau Ceti's `unitLattice (Fin 4)`, is
universal**, by Lagrange's four-square theorem. -/
lemma isUniversal_unitLattice_fin_four : (unitLattice (Fin 4)).IsUniversal := by
  rintro n (hn | ⟨x, hx⟩)
  · rcases Nat.sum_four_squares n.toNat with ⟨a, b, c, d, h⟩
    have hmem : (![(a : ℚ), b, c, d] : Fin 4 → ℚ) ∈ (unitLattice (Fin 4)).carrier :=
      (mem_unitLattice_carrier_iff (Fin 4) _).mpr fun i ↦ by
        fin_cases i <;> exact ⟨_, Int.cast_natCast _⟩
    have h' : (a : ℚ) ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n := by
      rw [← Int.toNat_of_nonneg hn.le, ← h]
      push_cast
      ring1
    refine ⟨⟨_, hmem⟩, Int.cast_injective (α := ℚ) ?_⟩
    rw [integralNorm_cast, unitLattice_norm_apply, Fin.sum_univ_four]
    simpa using h'
  · exact absurd hx ((isPosDef_unitLattice (Fin 4)).isPosSemidef.integralNorm_nonneg x).not_gt

end TauCeti.IntegralLattice
