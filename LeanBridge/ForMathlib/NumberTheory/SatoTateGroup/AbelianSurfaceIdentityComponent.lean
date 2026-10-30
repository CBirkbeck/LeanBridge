import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.IdentityComponent
import Mathlib.Data.Matrix.Block
import Mathlib.Topology.Instances.Matrix

/-!
# The identity components of the Sato–Tate groups of abelian surfaces

For an abelian surface `A` over `ℚ`, such as the Jacobian of a genus `2` curve, the identity
component `ST⁰(A)` of its Sato–Tate group (LMFDB `g2c.st_group_identity_component`) is, up to
conjugacy in `USp(4)`, one of six connected compact groups (Fité, Kedlaya, Rotger and Sutherland),
according to the real geometric endomorphism algebra `End(A_ℚ̄) ⊗ ℝ`:

* `U(1)`, for `M₂(ℂ)`, of real dimension `1`: `A_ℚ̄` is isogenous to the square of a CM elliptic
  curve;
* `SU(2)`, for `M₂(ℝ)`, of real dimension `3`: the square of a non-CM elliptic curve;
* `U(1) × U(1)`, for `ℂ × ℂ`, of real dimension `2`: a product of non-isogenous CM elliptic curves,
  or a simple abelian surface with CM;
* `U(1) × SU(2)`, for `ℝ × ℂ`, of real dimension `4`: a CM times a non-CM elliptic curve;
* `SU(2) × SU(2)`, for `ℝ × ℝ`, of real dimension `6`: a product of non-isogenous non-CM elliptic
  curves, or a simple abelian surface with RM;
* `USp(4)`, for `ℝ`, of real dimension `10`: the generic case.

This file defines these six groups, as Sato–Tate groups of weight `1` and degree `4`, inside the
group `USp(4)` of the form `Matrix.satoTateForm 4`, which pairs `e₀` with `e₂` and `e₁` with `e₃`.
Five of them lie in `SU(2) × SU(2)`, embedded in `USp(4)` (`SatoTateGroup.pairBlockHom`) so that
`(P, Q)` acts as `P` on the span of `e₀, e₂` and as `Q` on the span of `e₁, e₃`: this is
`USp(2) × USp(2) ⊆ USp(4)` for this orthogonal decomposition, with `USp(2) = SU(2)`. With the
diagonal torus `T = {diag(u, ū)}` of `SU(2)`, they are:

* `U(1)`: the pairs `(t, t)` with `t ∈ T`, that is the matrices `diag(u, u, ū, ū)` with `|u| = 1`;
* `SU(2)`: the pairs `(P, P)`;
* `U(1) × U(1)`: the pairs in `T × T`, that is the matrices `diag(u, v, ū, v̄)`;
* `U(1) × SU(2)`: the pairs in `T × SU(2)`;
* `SU(2) × SU(2)`: all pairs;
* `USp(4)`: the ambient group `SatoTateGroup.ambientGroup 1 4`.

Another symplectic basis would only conjugate them. That the identity component of the Sato–Tate
group of an abelian surface is conjugate to one of them, the correspondence with `End(A_ℚ̄) ⊗ ℝ`,
their connectedness and their real dimensions are not formalised, the Sato–Tate group of an abelian
variety being unavailable.

## Main definitions

* `SatoTateGroup.pairBlock` and `SatoTateGroup.pairBlockHom`: the embedding
  `SU(2) × SU(2) → USp(4)`.
* `SatoTateGroup.diagonalTorus`: the diagonal torus `T` of `SU(2)`.
* `SatoTateGroup.diagonalPairs`: the diagonal `{(P, P)}` of `SU(2) × SU(2)`.
* `SatoTateGroup.ofPairBlock`: the Sato–Tate group of a closed subgroup of `SU(2) × SU(2)`.
* `SatoTateGroup.AbelianSurfaceIdentityComponent` (LMFDB `g2c.st_group_identity_component`): the
  six types of identity components, and
  `SatoTateGroup.AbelianSurfaceIdentityComponent.toSatoTateGroup` their groups.

## Main results

* `SatoTateGroup.range_pairBlockHom_le`: the embedding takes values in `USp(4)`.
* `SatoTateGroup.pairBlock_diagonal`: `(diag(a, b), diag(c, d))` acts as `diag(a, c, b, d)`.
* `SatoTateGroup.mem_diagonalTorus_iff`: `T` is the group of the matrices `diag(u, ū)`, `|u| = 1`.
* `SatoTateGroup.AbelianSurfaceIdentityComponent.mem_toSatoTateGroup_u1_iff`: `U(1)` is the group of
  the matrices `diag(u, u, ū, ū)`, `|u| = 1`.
* `SatoTateGroup.AbelianSurfaceIdentityComponent.mem_toSatoTateGroup_u1u1_iff`: `U(1) × U(1)` is the
  group of the matrices `diag(u, v, ū, v̄)`, `|u| = |v| = 1`.
-/

open Matrix ComplexConjugate

local notation "SU₂" => specialUnitaryGroup (Fin 2) ℂ

namespace SatoTateGroup

variable {P Q P' Q' : Matrix (Fin 2) (Fin 2) ℂ}

variable (P Q) in
/-- The block matrix acting as `P` on the span of `e₀, e₂` and as `Q` on the span of `e₁, e₃`, for
`2 × 2` matrices `P` and `Q`: the block diagonal matrix of `P` and `Q`, reindexed by
`Fin 2 × Fin 2 ≃ Fin 4`, `(a, b) ↦ b + 2a`. -/
def pairBlock : Matrix (Fin 4) (Fin 4) ℂ :=
  reindex finProdFinEquiv finProdFinEquiv (blockDiagonal ![P, Q])

lemma pairBlock_mul : pairBlock P Q * pairBlock P' Q' = pairBlock (P * P') (Q * Q') := by
  rw [pairBlock, pairBlock, pairBlock, reindex_apply, reindex_apply, reindex_apply,
    submatrix_mul_equiv, ← blockDiagonal_mul]
  congr 2
  funext k
  fin_cases k <;> rfl

lemma pairBlock_one : pairBlock 1 1 = 1 := by
  have h : ![(1 : Matrix (Fin 2) (Fin 2) ℂ), 1] = 1 := by
    funext k
    fin_cases k <;> rfl
  rw [pairBlock, h, blockDiagonal_one, reindex_apply, submatrix_one_equiv]

lemma conjTranspose_pairBlock : (pairBlock P Q)ᴴ = pairBlock Pᴴ Qᴴ := by
  rw [pairBlock, pairBlock, conjTranspose_reindex, blockDiagonal_conjTranspose]
  congr 2
  funext k
  fin_cases k <;> rfl

lemma transpose_pairBlock : (pairBlock P Q)ᵀ = pairBlock Pᵀ Qᵀ := by
  rw [pairBlock, pairBlock, transpose_reindex, blockDiagonal_transpose]
  congr 2
  funext k
  fin_cases k <;> rfl

/-- **The block matrix of two diagonal matrices is diagonal**: `(diag(a, b), diag(c, d))` acts as
`diag(a, c, b, d)`. -/
lemma pairBlock_diagonal (a b c d : ℂ) :
    pairBlock (diagonal ![a, b]) (diagonal ![c, d]) = diagonal ![a, c, b, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma satoTateForm_four : satoTateForm 4 = pairBlock (satoTateForm 2) (satoTateForm 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

variable (P) in
lemma transpose_mul_satoTateForm_two_mul : Pᵀ * satoTateForm 2 * P = P.det • satoTateForm 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [satoTateForm, mul_apply, det_fin_two] <;> ring1

lemma pairBlock_mem_unitaryGroup (hP : P ∈ unitaryGroup (Fin 2) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin 2) ℂ) : pairBlock P Q ∈ unitaryGroup (Fin 4) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_pairBlock, pairBlock_mul,
    ← star_eq_conjTranspose, ← star_eq_conjTranspose, mem_unitaryGroup_iff.mp hP,
    mem_unitaryGroup_iff.mp hQ, pairBlock_one]

lemma transpose_pairBlock_mul_satoTateForm_mul (hP : P.det = 1) (hQ : Q.det = 1) :
    (pairBlock P Q)ᵀ * satoTateForm 4 * pairBlock P Q = satoTateForm 4 := by
  rw [satoTateForm_four, transpose_pairBlock, pairBlock_mul, pairBlock_mul,
    transpose_mul_satoTateForm_two_mul, transpose_mul_satoTateForm_two_mul, hP, hQ, one_smul]

/-- The embedding `SU(2) × SU(2) → USp(4)`, `(P, Q) ↦ pairBlock P Q`, acting as `P` on the span of
`e₀, e₂` and as `Q` on the span of `e₁, e₃`, as a homomorphism to the unitary group `U(4)`; it
takes values in `USp(4)` (`range_pairBlockHom_le`). -/
noncomputable def pairBlockHom : SU₂ × SU₂ →* unitaryGroup (Fin 4) ℂ where
  toFun x := ⟨pairBlock x.1 x.2, pairBlock_mem_unitaryGroup (mem_specialUnitaryGroup_iff.mp x.1.2).1
    (mem_specialUnitaryGroup_iff.mp x.2.2).1⟩
  map_one' := Subtype.ext pairBlock_one
  map_mul' _ _ := Subtype.ext pairBlock_mul.symm

lemma coe_pairBlockHom (x : SU₂ × SU₂) :
    (pairBlockHom x : Matrix (Fin 4) (Fin 4) ℂ) = pairBlock x.1 x.2 :=
  rfl

lemma continuous_pairBlockHom : Continuous pairBlockHom := by
  refine continuous_induced_rng.mpr <| (Continuous.matrix_blockDiagonal ?_).matrix_reindex _ _
  refine continuous_pi fun k ↦ ?_
  fin_cases k
  · exact continuous_subtype_val.comp continuous_fst
  · exact continuous_subtype_val.comp continuous_snd

/-- **The embedding `SU(2) × SU(2) → U(4)` takes values in `USp(4)`**: a `2 × 2` matrix `P`
satisfies `Pᵀ J P = det(P) J` for the standard alternating form `J`. -/
lemma range_pairBlockHom_le : pairBlockHom.range ≤ ambientGroup 1 4 := by
  rintro _ ⟨x, rfl⟩
  rw [mem_ambientGroup, ambientForm, ite_eq_left odd_one]
  exact transpose_pairBlock_mul_satoTateForm_mul (mem_specialUnitaryGroup_iff.mp x.1.2).2
    (mem_specialUnitaryGroup_iff.mp x.2.2).2

/-- The **diagonal torus** of `SU(2)`: its diagonal matrices, which are the matrices `diag(u, ū)`
with `|u| = 1` (`mem_diagonalTorus_iff`). It is the identity component `U(1)` of the Sato–Tate group
of a CM elliptic curve. -/
def diagonalTorus : Subgroup SU₂ where
  carrier := {X | (X : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 ∧ (X : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0}
  mul_mem' {X Y} hX hY := by
    simp [mul_apply, hX.1, hX.2, hY.1, hY.2]
  one_mem' := by
    simp
  inv_mem' {X} hX := by
    rw [← star_eq_inv]
    simp [hX.1, hX.2]

lemma isClosed_diagonalTorus : IsClosed (diagonalTorus : Set SU₂) :=
  (isClosed_eq (continuous_subtype_val.matrix_elem 0 1) continuous_const).inter
    (isClosed_eq (continuous_subtype_val.matrix_elem 1 0) continuous_const)

lemma diagonal_mem_specialUnitaryGroup {u : ℂ} (hu : ‖u‖ = 1) : diagonal ![u, conj u] ∈ SU₂ := by
  have h : u * conj u = 1 := by
    rw [Complex.mul_conj', hu, Complex.ofReal_one, one_pow]
  refine mem_specialUnitaryGroup_iff.mpr ⟨mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · rw [star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    fin_cases k
    · exact h
    · simpa [mul_comm] using h
  · rw [det_diagonal, Fin.prod_univ_two]
    exact h

/-- **The diagonal torus of `SU(2)` is the group of the matrices `diag(u, ū)` with `|u| = 1`**: a
diagonal unitary matrix `diag(a, b)` has `|a| = 1`, and `ab = 1` when its determinant is `1`. -/
lemma mem_diagonalTorus_iff {X : SU₂} : X ∈ diagonalTorus ↔ ∃ u : ℂ, ‖u‖ = 1 ∧
    (X : Matrix (Fin 2) (Fin 2) ℂ) = diagonal ![u, conj u] := by
  refine ⟨fun hX ↦ ?_, ?_⟩
  · have hu : X.1 0 0 * conj (X.1 0 0) = 1 := by
      simpa [mul_apply, hX.1] using
        congrFun (congrFun (mem_unitaryGroup_iff.mp (mem_specialUnitaryGroup_iff.mp X.2).1) 0) 0
    have hd : X.1 0 0 * X.1 1 1 = 1 := by
      simpa [det_fin_two, hX.2] using (mem_specialUnitaryGroup_iff.mp X.2).2
    refine ⟨X.1 0 0, ?_, ?_⟩
    · have h : ((‖X.1 0 0‖ ^ 2 : ℝ) : ℂ) = 1 := by
        rw [Complex.ofReal_pow, ← Complex.mul_conj', hu]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp (Complex.ofReal_eq_one.mp h)
    · ext i j
      fin_cases i <;> fin_cases j
      · rfl
      · exact hX.1
      · exact hX.2
      · exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one hu) (hd.trans hu.symm)
  · rintro ⟨u, -, hu⟩
    refine ⟨?_, ?_⟩ <;> simp [hu]

/-- The **diagonal** of `SU(2) × SU(2)`: the pairs `(P, P)`. -/
def diagonalPairs : Subgroup (SU₂ × SU₂) :=
  (MonoidHom.fst _ _).eqLocus (MonoidHom.snd _ _)

lemma isClosed_diagonalPairs : IsClosed (diagonalPairs : Set (SU₂ × SU₂)) :=
  isClosed_eq continuous_fst continuous_snd

lemma isClosed_ambientGroup (w d : ℕ) :
    IsClosed (ambientGroup w d : Set (unitaryGroup (Fin d) ℂ)) :=
  isClosed_eq ((continuous_subtype_val.matrix_transpose.matrix_mul continuous_const).matrix_mul
    continuous_subtype_val) continuous_const

/-- The Sato–Tate group of weight `1` and degree `4` of a closed subgroup `H` of `SU(2) × SU(2)`:
its image in `USp(4)` under the embedding `pairBlockHom`, closed as `H` is compact. -/
noncomputable def ofPairBlock (H : Subgroup (SU₂ × SU₂)) (hH : IsClosed (H : Set (SU₂ × SU₂))) :
    SatoTateGroup where
  weight := 1
  degree := 4
  even_degree_of_odd_weight _ := ⟨2, rfl⟩
  toSubgroup := H.map pairBlockHom
  isClosed := by
    rw [Subgroup.coe_map]
    exact (hH.isCompact.image continuous_pairBlockHom).isClosed
  le_ambientGroup := (Subgroup.map_le_range pairBlockHom H).trans range_pairBlockHom_le

/-- The six possible **identity components** of the Sato–Tate group of an abelian surface over `ℚ`
(LMFDB `g2c.st_group_identity_component`), up to conjugacy, named after their isomorphism types;
their groups are `AbelianSurfaceIdentityComponent.toSatoTateGroup`. -/
inductive AbelianSurfaceIdentityComponent
  /-- `U(1)`, for `End(A_ℚ̄) ⊗ ℝ ≅ M₂(ℂ)`. -/
  | u1
  /-- `SU(2)`, for `End(A_ℚ̄) ⊗ ℝ ≅ M₂(ℝ)`. -/
  | su2
  /-- `U(1) × U(1)`, for `End(A_ℚ̄) ⊗ ℝ ≅ ℂ × ℂ`. -/
  | u1u1
  /-- `U(1) × SU(2)`, for `End(A_ℚ̄) ⊗ ℝ ≅ ℝ × ℂ`. -/
  | u1su2
  /-- `SU(2) × SU(2)`, for `End(A_ℚ̄) ⊗ ℝ ≅ ℝ × ℝ`. -/
  | su2su2
  /-- `USp(4)`, for `End(A_ℚ̄) ⊗ ℝ ≅ ℝ`, the generic case. -/
  | usp4

namespace AbelianSurfaceIdentityComponent

variable (M : unitaryGroup (Fin 4) ℂ)

/-- The **identity component** `ST⁰(A)` of the Sato–Tate group of an abelian surface `A` over `ℚ`
(LMFDB `g2c.st_group_identity_component`) of each of the six types, as a Sato–Tate group of weight
`1` and degree `4`: `U(1) = {diag(u, u, ū, ū)}`, `SU(2) = {(P, P)}`,
`U(1) × U(1) = {diag(u, v, ū, v̄)}`, `U(1) × SU(2) = T × SU(2)`, `SU(2) × SU(2)` (in `SU(2) × SU(2)`
embedded by `pairBlockHom`, with the diagonal torus `T`), and `USp(4)`. These are the groups of
Fité, Kedlaya, Rotger and Sutherland for the form `Matrix.satoTateForm 4`. -/
noncomputable def toSatoTateGroup : AbelianSurfaceIdentityComponent → SatoTateGroup
  | u1 => ofPairBlock (diagonalPairs ⊓ diagonalTorus.prod diagonalTorus) <|
      isClosed_diagonalPairs.inter (isClosed_diagonalTorus.prod isClosed_diagonalTorus)
  | su2 => ofPairBlock diagonalPairs isClosed_diagonalPairs
  | u1u1 => ofPairBlock (diagonalTorus.prod diagonalTorus) <|
      isClosed_diagonalTorus.prod isClosed_diagonalTorus
  | u1su2 => ofPairBlock (diagonalTorus.prod ⊤) <| isClosed_diagonalTorus.prod isClosed_univ
  | su2su2 => ofPairBlock ⊤ isClosed_univ
  | usp4 => ⟨1, 4, fun _ ↦ ⟨2, rfl⟩, ambientGroup 1 4, isClosed_ambientGroup 1 4, le_rfl⟩

/-- **The identity component `U(1)` is the group of the matrices `diag(u, u, ū, ū)`** with
`|u| = 1`. -/
lemma mem_toSatoTateGroup_u1_iff : M ∈ u1.toSatoTateGroup.toSubgroup ↔ ∃ u : ℂ, ‖u‖ = 1 ∧
    (M : Matrix (Fin 4) (Fin 4) ℂ) = diagonal ![u, u, conj u, conj u] := by
  refine ⟨?_, ?_⟩
  · rintro ⟨x, ⟨hx, hX, -⟩, rfl⟩
    rcases mem_diagonalTorus_iff.mp hX with ⟨u, hu, hXu⟩
    have hx' : x.1 = x.2 := hx
    refine ⟨u, hu, ?_⟩
    rw [coe_pairBlockHom, ← hx', hXu, pairBlock_diagonal]
  · rintro ⟨u, hu, hM⟩
    let X : SU₂ := ⟨_, diagonal_mem_specialUnitaryGroup hu⟩
    have hX : X ∈ diagonalTorus := mem_diagonalTorus_iff.mpr ⟨u, hu, rfl⟩
    refine ⟨(X, X), ⟨rfl, hX, hX⟩, Subtype.ext ?_⟩
    rw [coe_pairBlockHom, pairBlock_diagonal, hM]

/-- **The identity component `U(1) × U(1)` is the group of the matrices `diag(u, v, ū, v̄)`** with
`|u| = |v| = 1`. -/
lemma mem_toSatoTateGroup_u1u1_iff : M ∈ u1u1.toSatoTateGroup.toSubgroup ↔ ∃ u v : ℂ, ‖u‖ = 1 ∧
    ‖v‖ = 1 ∧ (M : Matrix (Fin 4) (Fin 4) ℂ) = diagonal ![u, v, conj u, conj v] := by
  refine ⟨?_, ?_⟩
  · rintro ⟨x, ⟨hX, hY⟩, rfl⟩
    rcases mem_diagonalTorus_iff.mp hX with ⟨u, hu, hXu⟩
    rcases mem_diagonalTorus_iff.mp hY with ⟨v, hv, hYv⟩
    refine ⟨u, v, hu, hv, ?_⟩
    rw [coe_pairBlockHom, hXu, hYv, pairBlock_diagonal]
  · rintro ⟨u, v, hu, hv, hM⟩
    let X : SU₂ := ⟨_, diagonal_mem_specialUnitaryGroup hu⟩
    let Y : SU₂ := ⟨_, diagonal_mem_specialUnitaryGroup hv⟩
    have hX : X ∈ diagonalTorus := mem_diagonalTorus_iff.mpr ⟨u, hu, rfl⟩
    have hY : Y ∈ diagonalTorus := mem_diagonalTorus_iff.mpr ⟨v, hv, rfl⟩
    refine ⟨(X, Y), ⟨hX, hY⟩, Subtype.ext ?_⟩
    rw [coe_pairBlockHom, pairBlock_diagonal, hM]

end AbelianSurfaceIdentityComponent

end SatoTateGroup
