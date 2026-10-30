import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.Basic

/-!
# Moment matrices of Sato–Tate groups

The moment matrix of a Sato–Tate group `G` (LMFDB `st_group.moment_matrix`) is the matrix of the
moments `E[χᵢ χⱼ]` over `G`, for its Haar probability measure, of the irreducible characters `χᵢ`
of its ambient group, and its diagonal is the vector of the `E[χᵢ²]`.

In odd weight the ambient group is `USp(2g)`. Its irreducible characters are indexed by the
dominant weights `λ = c₁ ω₁ + ⋯ + c_g ω_g`, `ω_k` the `k`-th fundamental weight, which the LMFDB
writes as the monomials `e₁^{c₁} ⋯ e_g^{c_g}` in the elementary symmetric functions; as a partition
`λᵢ = cᵢ + ⋯ + c_g`, and its conjugate partition `λ'` has the part `k` with multiplicity `c_k`.
The character of highest weight `λ` at a matrix with eigenvalues `x₁^{±1}, …, x_g^{±1}` is the
symplectic Schur function `sp_λ = det(e_{λ'ᵢ - i + j} - e_{λ'ᵢ - i - j})_{1 ≤ i, j ≤ λ₁}` of
Koike and Terada, `e_k` the elementary symmetric functions of the eigenvalues, which agrees with
Weyl's character formula (this agreement and the irreducibility are not proved here). Each is an
integer polynomial in the coefficients `aᵢ = (-1)ⁱ eᵢ` of the characteristic polynomial, as the
knowl says. The LMFDB orders the characters by the degree `c₁ + ⋯ + c_g` of the monomial and then
by an order on exponent vectors; the moment matrix is indexed here by the exponent vectors
themselves, the order being a display convention.

In even weight the ambient group is `O(d)`, whose irreducible characters are not formalised; the
moment matrix is defined here for the symplectic ambient group, that of the Sato–Tate groups of odd
weight.

## Main definitions

* `SatoTateGroup.highestWeight` and `SatoTateGroup.conjugateHighestWeight`: the partition `λ` of
  the dominant weight with exponent vector `c`, and its conjugate `λ'`.
* `SatoTateGroup.symplecticSchur`: the symplectic Schur function `sp_λ` of a multiset of
  eigenvalues.
* `SatoTateGroup.symplecticCharacter` (LMFDB `st_group.moment_matrix`): the irreducible character
  of `USp(2g)` of highest weight `λ`, as a random variable on a Sato–Tate group.
* `SatoTateGroup.symplecticMomentMatrix` (LMFDB `st_group.moment_matrix`): the moment matrix, whose
  diagonal (`Matrix.diag`) is the vector of the `E[χ²]`.

## Main results

* `SatoTateGroup.symplecticMomentMatrix_isSymm`: the moment matrix is symmetric.
* `SatoTateGroup.symplecticMomentMatrix_zero_zero`: the moment of the trivial character is `1`.
* `SatoTateGroup.diag_symplecticMomentMatrix`: the diagonal is the vector of the `E[χ²]`.
* `SatoTateGroup.symplecticCharacter_single`: the character of highest weight `e₁` is the trace.
* `SatoTateGroup.symplecticMomentMatrix_single_single`: its moment is the second trace moment.
-/

open Matrix Finset

namespace SatoTateGroup

section SymplecticSchur

variable {g : ℕ} (c : Fin g → ℕ) (s : Multiset ℂ)

/-- The **partition** `λ` of the dominant weight `λ = c₁ ω₁ + ⋯ + c_g ω_g` of `USp(2g)` with
exponent vector `c` (written `e₁^{c₁} ⋯ e_g^{c_g}` by the LMFDB): `λᵢ = cᵢ + ⋯ + c_g`, with
`0`-based indices `i`. -/
def highestWeight (i : Fin g) : ℕ :=
  ∑ k ∈ Ici i, c k

/-- The **conjugate partition** `λ'_j = #{i | j ≤ λᵢ}` of the dominant weight with exponent vector
`c`: its parts are the `k` with multiplicity `c_k`. -/
def conjugateHighestWeight (j : ℕ) : ℕ :=
  #{i | j ≤ highestWeight c i}

/-- The elementary symmetric function `e_m` of a multiset, for an integer `m`, and `0` for `m < 0`.
-/
noncomputable def esymmOfInt (m : ℤ) : ℂ :=
  if 0 ≤ m then s.esymm m.toNat else 0

/-- The **symplectic Schur function** `sp_λ` (Koike–Terada) of the dominant weight
`λ = c₁ ω₁ + ⋯ + c_g ω_g` of `USp(2g)`, evaluated at a multiset `s` of eigenvalues:
`det(e_{λ'ᵢ - i + j} - e_{λ'ᵢ - i - j})_{1 ≤ i, j ≤ λ₁}`, `λ'` the conjugate partition, `e_k` the
elementary symmetric functions of `s` and `λ₁ = c₁ + ⋯ + c_g`. At the eigenvalues of a matrix of
`USp(2g)` it is the irreducible character of highest weight `λ` (Weyl's character formula; not
proved here). -/
noncomputable def symplecticSchur : ℂ :=
  (of fun i j : Fin (∑ k, c k) ↦
    esymmOfInt s (conjugateHighestWeight c (i + 1) - i + j) -
      esymmOfInt s (conjugateHighestWeight c (i + 1) - i - j - 2)).det

lemma symplecticSchur_zero : symplecticSchur (0 : Fin g → ℕ) s = 1 := by
  simp [symplecticSchur]

lemma symplecticSchur_single (hg : 0 < g) :
    symplecticSchur (Pi.single ⟨0, hg⟩ 1 : Fin g → ℕ) s = s.sum := by
  have hn : ∑ k, (Pi.single ⟨0, hg⟩ 1 : Fin g → ℕ) k = 1 := by
    simp
  have hconj : conjugateHighestWeight (Pi.single ⟨0, hg⟩ 1 : Fin g → ℕ) 1 = 1 := by
    refine card_eq_one.mpr ⟨⟨0, hg⟩, ext fun i ↦ ?_⟩
    simp [highestWeight, apply_ite, Fin.le_def, Fin.ext_iff]
  rw [symplecticSchur, det_eq_elem_of_card_eq_one (by rw [Fintype.card_fin, hn])
    ⟨0, one_pos.trans_eq hn.symm⟩]
  simp [hconj, esymmOfInt, Multiset.esymm, Multiset.powersetCard_one]

end SymplecticSchur

variable (G : SatoTateGroup) (c : Fin (G.degree / 2) → ℕ) (hd : 0 < G.degree / 2)

/-- The **irreducible character** (LMFDB `st_group.moment_matrix`) of highest weight
`e₁^{c₁} ⋯ e_g^{c_g}` of the ambient group `USp(2g)` of a Sato–Tate group `G` of odd weight and
degree `2g`, as a random variable on `G`: the symplectic Schur function of the eigenvalues. -/
noncomputable def symplecticCharacter (x : G.toSubgroup) : ℂ :=
  symplecticSchur c (G.matrix x).charpoly.roots

/-- The **moment matrix** (LMFDB `st_group.moment_matrix`) of a Sato–Tate group `G` of odd weight
and degree `2g`: the matrix of the moments `E[χ_c χ_{c'}]`, for the Haar probability measure of `G`,
of the irreducible characters `χ_c` of its ambient group `USp(2g)`, indexed by their highest weights
`e₁^{c₁} ⋯ e_g^{c_g}`. Its **diagonal** is `Matrix.diag`, the vector of the `E[χ_c²]`
(`diag_symplecticMomentMatrix`). The LMFDB lists the characters by the degree `c₁ + ⋯ + c_g` and
then by an order on exponent vectors, a display convention not recorded here. -/
noncomputable def symplecticMomentMatrix :
    Matrix (Fin (G.degree / 2) → ℕ) (Fin (G.degree / 2) → ℕ) ℂ :=
  of fun c c' ↦ G.expectation (G.symplecticCharacter c * G.symplecticCharacter c')

/-- **The moment matrix is symmetric.** -/
lemma symplecticMomentMatrix_isSymm : G.symplecticMomentMatrix.IsSymm :=
  IsSymm.ext fun _ _ ↦ congrArg G.expectation <| mul_comm _ _

/-- **The moment of the trivial character is `1`**: the character of highest weight `0` is the
constant `1`. -/
lemma symplecticMomentMatrix_zero_zero : G.symplecticMomentMatrix 0 0 = 1 := by
  simp [symplecticMomentMatrix, symplecticCharacter, symplecticSchur_zero, expectation]

/-- **The diagonal of the moment matrix is the vector of the `E[χ²]`.** -/
lemma diag_symplecticMomentMatrix :
    G.symplecticMomentMatrix.diag c = G.expectation (G.symplecticCharacter c ^ 2) :=
  congrArg G.expectation (sq _).symm

/-- **The character of highest weight `e₁` is the trace**, the character of the standard
representation of `USp(2g)`. -/
lemma symplecticCharacter_single : G.symplecticCharacter (Pi.single ⟨0, hd⟩ 1) = G.trace :=
  funext fun x ↦ (symplecticSchur_single _ hd).trans (G.matrix x).trace_eq_sum_roots_charpoly.symm

/-- **The moment of the character `e₁` is the second trace moment** `E[t²]` (LMFDB
`st_group.second_trace_moment`). -/
lemma symplecticMomentMatrix_single_single :
    G.symplecticMomentMatrix (Pi.single ⟨0, hd⟩ 1) (Pi.single ⟨0, hd⟩ 1) = G.secondTraceMoment := by
  rw [symplecticMomentMatrix, of_apply, G.symplecticCharacter_single hd, ← sq]
  rfl

end SatoTateGroup
