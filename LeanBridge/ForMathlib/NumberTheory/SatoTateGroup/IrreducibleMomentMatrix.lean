import TauCeti.RepresentationTheory.Compact.Character.Basis
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.Basic

/-!
# The moment matrix over the irreducible characters of the ambient group

The moment matrix of a Sato–Tate group `G` (LMFDB `st_group.moment_matrix`) is the matrix of the
moments `E[χᵢ χⱼ]` over `G`, with `χᵢ`, `χⱼ` ranging over the irreducible characters of the ambient
group of `G`, which is `USp(d)` in odd weight and `O(d)` in even weight. The ambient group is a
compact group, so Tau Ceti's Peter–Weyl theory gives its irreducible characters: the unitary dual
`TauCeti.IrrepClass ℂ (SatoTateGroup.ambientGroup w d)` and the characters of the chosen models.
This covers both weights, and no description of the irreducible characters is needed for the
definition.

The LMFDB orders the characters by their highest weights, written as monomials in the elementary
symmetric functions, by the degree of the monomial and then by "reverse lexicographic order of
exponent vectors". The LMFDB's data shows that this is the decreasing lexicographic order of the
vectors `(c₁, c₂, …)` of exponents of `e₁, e₂, …`, which is `SatoTateGroup.IsBeforeInDisplayOrder`.
In the table `gps_st`, the first row of the `character_matrix` of `1.6.K.1.1a`, the group
`SU(2) × U(1)₂`, is `[1, 0, 4, 0, 4, 0, 7, 10, 0, 4, 0, 15, 0, 0, 24]`, the moments `E[χᵢ]`, where
`7` and `10` are the moments of the characters of the monomials `e₁ e₃` and `e₂²`. An exact
computation of the moments of `SatoTateGroup.symplecticSchur` reproduces all of this matrix and of
`character_diagonal`, also for the connected groups of degree `4`, in this order, and in no other
order the words allow: colexicographic, increasing, or comparing from `c_g` instead of `c₁`.

## Main definitions

* `SatoTateGroup.ambientCharacter`: the irreducible characters of the ambient group.
* `SatoTateGroup.irreducibleCharacter` (LMFDB `st_group.moment_matrix`): an irreducible character
  of the ambient group of a Sato–Tate group, as a random variable on the group.
* `SatoTateGroup.momentMatrix` (LMFDB `st_group.moment_matrix`): the moment matrix.
* `SatoTateGroup.momentDiagonal` (LMFDB `st_group.moment_matrix`): its diagonal.
* `SatoTateGroup.IsBeforeInDisplayOrder`: the LMFDB's order on exponent vectors, a linear order (the
  instance `IsLinearOrder (Fin n → ℕ) IsBeforeInDisplayOrder`).

## Main results

* `SatoTateGroup.injective_ambientCharacter`: distinct classes have distinct characters.
* `SatoTateGroup.integral_ambientCharacter_mul_conj_self`,
  `SatoTateGroup.integral_ambientCharacter_mul_conj_of_ne`: orthonormality of the irreducible
  characters of the ambient group.
* `SatoTateGroup.momentMatrix_isSymm`: the moment matrix is symmetric.
* `SatoTateGroup.diag_momentMatrix`: its diagonal is the vector of the `E[χ²]`.
* `SatoTateGroup.isBeforeInDisplayOrder_two_zero_zero_two`,
  `SatoTateGroup.isBeforeInDisplayOrder_one_zero_one_zero_two_zero`: two tests of the order against
  the LMFDB's data, which separate it from the other readings of the knowl.
-/

open Matrix MeasureTheory TauCeti

open scoped ComplexConjugate InnerProductSpace

namespace SatoTateGroup

section Ambient

variable (w d : ℕ)

lemma isClosed_ambientGroup : IsClosed (ambientGroup w d : Set (unitaryGroup (Fin d) ℂ)) := by
  have hc : Continuous fun A : unitaryGroup (Fin d) ℂ ↦
      (A : Matrix (Fin d) (Fin d) ℂ)ᵀ * ambientForm w d * (A : Matrix (Fin d) (Fin d) ℂ) := by
    have h₁ : Continuous fun A : unitaryGroup (Fin d) ℂ ↦ (A : Matrix (Fin d) (Fin d) ℂ) :=
      continuous_subtype_val
    exact (h₁.matrix_transpose.mul continuous_const).mul h₁
  exact isClosed_eq hc continuous_const

instance : CompactSpace (ambientGroup w d) :=
  isCompact_iff_compactSpace.mp (isClosed_ambientGroup w d).isCompact

noncomputable instance : MeasurableSpace (ambientGroup w d) :=
  borel _

instance : BorelSpace (ambientGroup w d) :=
  ⟨rfl⟩

/-- The **irreducible character** of the ambient group `USp(d)` or `O(d)` (LMFDB
`st_group.moment_matrix`) of a class of its unitary dual, by Peter–Weyl theory the classes of the
finite-dimensional irreducible unitary continuous representations: the trace of the model of the
class. -/
noncomputable def ambientCharacter (χ : IrrepClass ℂ (ambientGroup w d)) : C(ambientGroup w d, ℂ) :=
  ContRepresentation.character χ.model.rep χ.model.continuous_rep

lemma inner_stdCharacterBasis (χ χ' : IrrepClass ℂ (ambientGroup w d)) :
    ⟪stdCharacterBasis ℂ (ambientGroup w d) χ', stdCharacterBasis ℂ (ambientGroup w d) χ⟫_ℂ =
      ∫ a, ambientCharacter w d χ a * conj (ambientCharacter w d χ' a)
        ∂haarProb (ambientGroup w d) := by
  rw [coe_stdCharacterBasis, Submodule.coe_inner, coe_characterFamily, coe_characterFamily,
    ContRepresentation.characterLp_def, ContRepresentation.characterLp_def,
    ContinuousMap.inner_toLp]
  rfl

/-- **The irreducible characters of the ambient group have norm one.** -/
lemma integral_ambientCharacter_mul_conj_self (χ : IrrepClass ℂ (ambientGroup w d)) : ∫ a,
    ambientCharacter w d χ a * conj (ambientCharacter w d χ a)
      ∂haarProb (ambientGroup w d) = 1 := by
  classical
  rw [← inner_stdCharacterBasis, orthonormal_iff_ite.mp
    (stdCharacterBasis ℂ (ambientGroup w d)).orthonormal χ χ, ite_eq_left rfl]

/-- **Distinct irreducible characters of the ambient group are orthogonal.** -/
lemma integral_ambientCharacter_mul_conj_of_ne {χ χ' : IrrepClass ℂ (ambientGroup w d)}
    (h : χ' ≠ χ) : ∫ a, ambientCharacter w d χ a * conj (ambientCharacter w d χ' a)
      ∂haarProb (ambientGroup w d) = 0 := by
  classical
  rw [← inner_stdCharacterBasis, orthonormal_iff_ite.mp
    (stdCharacterBasis ℂ (ambientGroup w d)).orthonormal χ' χ, ite_eq_right h]

/-- **Distinct classes of the unitary dual of the ambient group have distinct characters.** -/
lemma injective_ambientCharacter : Function.Injective (ambientCharacter w d) := fun χ χ' h ↦ by
  by_contra hne
  have h₁ : ∫ a, ambientCharacter w d χ a * conj (ambientCharacter w d χ' a)
      ∂haarProb (ambientGroup w d) = 0 :=
    integral_ambientCharacter_mul_conj_of_ne w d (Ne.symm hne)
  rw [← h, integral_ambientCharacter_mul_conj_self] at h₁
  exact one_ne_zero h₁

end Ambient

variable (G : SatoTateGroup)

lemma degree_eq_of_odd (hw : Odd G.weight) : G.degree = G.degree / 2 + G.degree / 2 := by
  have h : Even G.degree := G.even_degree_of_odd_weight hw
  rcases h with ⟨r, hr⟩
  omega

/-- The inclusion of a Sato–Tate group in its ambient group. -/
def toAmbient : G.toSubgroup →* ambientGroup G.weight G.degree :=
  Subgroup.inclusion G.le_ambientGroup

/-- An **irreducible character** (LMFDB `st_group.moment_matrix`) of the ambient group of a
Sato–Tate group, as a random variable on the group. -/
noncomputable def irreducibleCharacter (χ : IrrepClass ℂ (ambientGroup G.weight G.degree))
    (x : G.toSubgroup) : ℂ :=
  ambientCharacter G.weight G.degree χ (G.toAmbient x)

/-- The **moment matrix** (LMFDB `st_group.moment_matrix`) of a Sato–Tate group: the matrix of the
moments `E[χ χ']`, for its Haar probability measure, with `χ`, `χ'` ranging over the irreducible
characters of its ambient group. -/
noncomputable def momentMatrix : Matrix (IrrepClass ℂ (ambientGroup G.weight G.degree))
    (IrrepClass ℂ (ambientGroup G.weight G.degree)) ℂ :=
  of fun χ χ' ↦ G.expectation (G.irreducibleCharacter χ * G.irreducibleCharacter χ')

/-- The **diagonal** (LMFDB `st_group.moment_matrix`) of the moment matrix: the vector of the
`E[χ²]`. -/
noncomputable def momentDiagonal (χ : IrrepClass ℂ (ambientGroup G.weight G.degree)) : ℂ :=
  G.expectation (G.irreducibleCharacter χ ^ 2)

/-- **The moment matrix is symmetric.** -/
lemma momentMatrix_isSymm : G.momentMatrix.IsSymm :=
  IsSymm.ext fun _ _ ↦ congrArg G.expectation <| mul_comm _ _

/-- **The diagonal of the moment matrix is the vector of the `E[χ²]`.** -/
lemma diag_momentMatrix : G.momentMatrix.diag = G.momentDiagonal :=
  funext fun _ ↦ congrArg G.expectation (sq _).symm

/-- The LMFDB's order on the exponent vectors `c` of the monomials `∏ₖ e_{k + 1} ^ c k` in the
elementary symmetric functions, which are the highest weights of the irreducible characters: by the
degree `∑ₖ c k`, and then by decreasing lexicographic order. The relation is reflexive: `c` comes
before `c'` or is `c'`. -/
def IsBeforeInDisplayOrder {n : ℕ} (c c' : Fin n → ℕ) : Prop :=
  ∑ k, c k < ∑ k, c' k ∨ ∑ k, c k = ∑ k, c' k ∧ toLex c' ≤ toLex c

instance {n : ℕ} : IsLinearOrder (Fin n → ℕ) IsBeforeInDisplayOrder where
  refl _ := .inr ⟨rfl, le_rfl⟩
  trans _ _ _ h h' := by
    rcases h with h | ⟨h, h₁⟩ <;> rcases h' with h' | ⟨h', h₁'⟩
    · exact .inl (h.trans h')
    · exact .inl (h.trans_eq h')
    · exact .inl (h.trans_lt h')
    · exact .inr ⟨h.trans h', h₁'.trans h₁⟩
  antisymm _ _ h h' := by
    rcases h with h | ⟨h, h₁⟩ <;> rcases h' with h' | ⟨h', h₁'⟩
    · exact absurd (h.trans h') (lt_irrefl _)
    · exact absurd h'.symm h.ne
    · exact absurd h.symm h'.ne
    · exact toLex.injective (le_antisymm h₁' h₁)
  total c c' := by
    rcases lt_trichotomy (∑ k, c k) (∑ k, c' k) with h | h | h
    · exact .inl (.inl h)
    · exact (le_total (toLex c') (toLex c)).imp (fun h₁ ↦ .inr ⟨h, h₁⟩) fun h₁ ↦ .inr ⟨h.symm, h₁⟩
    · exact .inr (.inl h)

/-- `e₁²` comes before `e₂²` in the LMFDB's order: the moments `E[χ]` of their characters are `0`
and `1` on `1.4.B.1.1a`, the group `SU(2) × SU(2)`, in this order in the first row of the
`character_matrix`, so the comparison does not start from the last exponent. -/
lemma isBeforeInDisplayOrder_two_zero_zero_two : IsBeforeInDisplayOrder ![2, 0] ![0, 2] := by
  refine .inr ⟨by simp, le_of_lt ⟨0, fun j hj ↦ absurd hj (Fin.not_lt_zero j), ?_⟩⟩
  simp

/-- `e₁ e₃` comes before `e₂²` in the LMFDB's order: the moments `E[χ]` of their characters are `7`
and `10` on `1.6.K.1.1a`, in this order in the first row of the `character_matrix`, so the order is
not the graded reverse lexicographic order. -/
lemma isBeforeInDisplayOrder_one_zero_one_zero_two_zero :
    IsBeforeInDisplayOrder ![1, 0, 1] ![0, 2, 0] := by
  refine .inr ⟨by simp [Fin.sum_univ_three], le_of_lt
    ⟨0, fun j hj ↦ absurd hj (Fin.not_lt_zero j), ?_⟩⟩
  simp

end SatoTateGroup
