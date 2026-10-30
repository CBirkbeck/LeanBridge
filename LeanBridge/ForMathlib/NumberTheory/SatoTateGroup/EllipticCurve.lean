import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.ComplexMultiplication.Basic
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.AbelianSurfaceIdentityComponent

/-!
# The Sato–Tate group of an elliptic curve

The Sato–Tate group of a motive over a number field (LMFDB `ag.sato_tate_group`) is a compact Lie
group, a maximal compact subgroup of the Zariski closure of the image of its `ℓ`-adic Galois
representation, which conjecturally governs the distribution of its normalised Euler factors. That
definition is out of reach. For an elliptic curve `E` over a number field `K` the knowl describes
the group explicitly, and this is what is formalised here: the Sato–Tate group of `E` is

* `SU(2)` if `E` has no complex multiplication, even over an algebraic closure of `K`;
* `U(1)`, the knowl's `SO(2)`, if `E` has complex multiplication defined over `K`;
* the normaliser `N(U(1))` of `U(1)` in `SU(2)` if `E` has potential complex multiplication that
  is not defined over `K`.

The groups are Sato–Tate groups of weight `1` and degree `2` in the sense of LeanBridge's
`SatoTateGroup`, closed subgroups of the unitary group `U(2)` inside the ambient group
`USp(2) = SU(2)`, with the embeddings of the LMFDB: `U(1)` is the circle of diagonal matrices
`diag(u, ū)`, conjugate in `SU(2)` to the rotation group `SO(2)`, and `N(U(1))` is
`U(1) ∪ J U(1)`, the circle and the antidiagonal matrices `(0, u; -ū, 0)`, where
`J = (0, 1; -1, 0)`, which is the normaliser of `U(1)` in `SU(2)`.

## Main definitions

* `WeierstrassCurve.satoTateSU2`, `WeierstrassCurve.satoTateU1`, `WeierstrassCurve.satoTateNU1`
  (LMFDB `ag.sato_tate_group`): the Sato–Tate groups `SU(2)`, `U(1)` and `N(U(1))`.
* `WeierstrassCurve.satoTateGroup` (LMFDB `ag.sato_tate_group`): the Sato–Tate group of an elliptic
  curve over a number field.

## Main results

* `WeierstrassCurve.mem_satoTateSU2_iff`: the ambient group `USp(2)` is `SU(2)`.
* `WeierstrassCurve.satoTateTorusNormalizer_eq_normalizer_inf_ambientGroup`: `U(1) ∪ J U(1)` is the
  normaliser of `U(1)` in `SU(2)`.
* `WeierstrassCurve.satoTateGroup_of_not_hasGeometricCM`,
  `WeierstrassCurve.satoTateGroup_of_hasCM` and
  `WeierstrassCurve.satoTateGroup_of_not_hasCM_of_hasGeometricCM`: the Sato–Tate group is `SU(2)`
  without potential complex multiplication, `U(1)` with complex multiplication over `K`, and
  `N(U(1))` with potential complex multiplication not defined over `K`.
-/

open Complex Matrix SatoTateGroup

namespace WeierstrassCurve

variable {A B : Matrix (Fin 2) (Fin 2) ℂ} {U : unitaryGroup (Fin 2) ℂ}

variable (A) in
/-- A `2 × 2` matrix `A` is in the **circle** `U(1) ⊆ SU(2)` pattern of the Sato–Tate group of an
elliptic curve with complex multiplication if it is `diag(u, ū)`. -/
def IsSatoTateTorusMatrix : Prop :=
  A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 1 1 = star (A 0 0)

variable (A) in
/-- A `2 × 2` matrix `A` is in the **antidiagonal** pattern of the normaliser of the circle
`U(1) ⊆ SU(2)` if it is `(0, u; -ū, 0)`. -/
def IsSatoTateAntidiagonalMatrix : Prop :=
  A 0 0 = 0 ∧ A 1 1 = 0 ∧ A 1 0 = -star (A 0 1)

lemma isSatoTateTorusMatrix_one : IsSatoTateTorusMatrix 1 :=
  ⟨by simp, by simp, by simp⟩

lemma IsSatoTateTorusMatrix.mul (hA : IsSatoTateTorusMatrix A) (hB : IsSatoTateTorusMatrix B) :
    IsSatoTateTorusMatrix (A * B) := by
  rcases hA with ⟨hA₁, hA₂, hA₃⟩
  rcases hB with ⟨hB₁, hB₂, hB₃⟩
  refine ⟨?_, ?_, ?_⟩ <;> simp [mul_apply, hA₁, hA₂, hA₃, hB₁, hB₂, hB₃]

lemma IsSatoTateTorusMatrix.mul_antidiagonal (hA : IsSatoTateTorusMatrix A)
    (hB : IsSatoTateAntidiagonalMatrix B) : IsSatoTateAntidiagonalMatrix (A * B) := by
  rcases hA with ⟨hA₁, hA₂, hA₃⟩
  rcases hB with ⟨hB₁, hB₂, hB₃⟩
  refine ⟨?_, ?_, ?_⟩ <;> simp [mul_apply, hA₁, hA₂, hA₃, hB₁, hB₂, hB₃]

lemma IsSatoTateAntidiagonalMatrix.mul_torus (hA : IsSatoTateAntidiagonalMatrix A)
    (hB : IsSatoTateTorusMatrix B) : IsSatoTateAntidiagonalMatrix (A * B) := by
  rcases hA with ⟨hA₁, hA₂, hA₃⟩
  rcases hB with ⟨hB₁, hB₂, hB₃⟩
  refine ⟨?_, ?_, ?_⟩ <;> simp [mul_apply, hA₁, hA₂, hA₃, hB₁, hB₂, hB₃]

lemma IsSatoTateAntidiagonalMatrix.mul (hA : IsSatoTateAntidiagonalMatrix A)
    (hB : IsSatoTateAntidiagonalMatrix B) : IsSatoTateTorusMatrix (A * B) := by
  rcases hA with ⟨hA₁, hA₂, hA₃⟩
  rcases hB with ⟨hB₁, hB₂, hB₃⟩
  refine ⟨?_, ?_, ?_⟩ <;> simp [mul_apply, hA₁, hA₂, hA₃, hB₁, hB₂, hB₃]

lemma IsSatoTateTorusMatrix.star (hA : IsSatoTateTorusMatrix A) :
    IsSatoTateTorusMatrix (star A) := by
  rcases hA with ⟨hA₁, hA₂, hA₃⟩
  refine ⟨?_, ?_, ?_⟩ <;> simp [hA₁, hA₂, hA₃]

lemma IsSatoTateAntidiagonalMatrix.star (hA : IsSatoTateAntidiagonalMatrix A) :
    IsSatoTateAntidiagonalMatrix (star A) := by
  rcases hA with ⟨hA₁, hA₂, hA₃⟩
  refine ⟨?_, ?_, ?_⟩ <;> simp [hA₁, hA₂, hA₃]

/-- The **circle** `U(1) ⊆ SU(2)` of the diagonal unitary matrices `diag(u, ū)`, the identity
component of the Sato–Tate group of an elliptic curve with potential complex multiplication. -/
def satoTateTorus : Subgroup (unitaryGroup (Fin 2) ℂ) where
  carrier := {U | IsSatoTateTorusMatrix U}
  one_mem' := isSatoTateTorusMatrix_one
  mul_mem' hU hV := hU.mul hV
  inv_mem' {U} hU := by
    rw [Set.mem_ofPred_eq, ← Unitary.star_eq_inv, Unitary.coe_star]
    exact hU.star

/-- The **normaliser** `N(U(1)) = U(1) ∪ J U(1)` of the circle `U(1)` in `SU(2)`, where
`J = (0, 1; -1, 0)`: the unitary matrices `diag(u, ū)` and `(0, u; -ū, 0)`. That it is the
normaliser is `satoTateTorusNormalizer_eq_normalizer_inf_ambientGroup`. -/
def satoTateTorusNormalizer : Subgroup (unitaryGroup (Fin 2) ℂ) where
  carrier := {U | IsSatoTateTorusMatrix U ∨ IsSatoTateAntidiagonalMatrix U}
  one_mem' := .inl isSatoTateTorusMatrix_one
  mul_mem' {U V} hU hV := by
    rcases hU with hU | hU <;> rcases hV with hV | hV
    · exact .inl (hU.mul hV)
    · exact .inr (hU.mul_antidiagonal hV)
    · exact .inr (hU.mul_torus hV)
    · exact .inl (hU.mul hV)
  inv_mem' {U} hU := by
    rw [Set.mem_ofPred_eq, ← Unitary.star_eq_inv, Unitary.coe_star]
    exact hU.imp IsSatoTateTorusMatrix.star IsSatoTateAntidiagonalMatrix.star

lemma det_eq_one_of_isSatoTateTorusMatrix (hU : IsSatoTateTorusMatrix U) :
    (U : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
  have h : (star (U : Matrix (Fin 2) (Fin 2) ℂ) * U) 0 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
    rw [Unitary.star_mul_self_of_mem U.2]
  rcases hU with ⟨hU₁, hU₂, hU₃⟩
  rw [det_fin_two, hU₁, hU₃, zero_mul, sub_zero]
  simpa [mul_apply, hU₂, mul_comm] using h

lemma det_eq_one_of_isSatoTateAntidiagonalMatrix (hU : IsSatoTateAntidiagonalMatrix U) :
    (U : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
  have h : (star (U : Matrix (Fin 2) (Fin 2) ℂ) * U) 1 1 = (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 1 := by
    rw [Unitary.star_mul_self_of_mem U.2]
  rcases hU with ⟨hU₁, hU₂, hU₃⟩
  rw [det_fin_two, hU₁, hU₃, zero_mul, zero_sub, mul_neg, neg_neg]
  simpa [mul_apply, hU₂, mul_comm] using h

variable (U) in
private lemma mem_ambientGroup_one_two_iff :
    U ∈ ambientGroup 1 2 ↔ (U : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
  rw [mem_ambientGroup, ambientForm, ite_eq_left odd_one, transpose_mul_satoTateForm_two_mul]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, one_smul]⟩
  simpa [satoTateForm] using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M 1 0) h

lemma isClosed_setOf_isSatoTateTorusMatrix :
    IsClosed {A : unitaryGroup (Fin 2) ℂ | IsSatoTateTorusMatrix A} :=
  (isClosed_eq (continuous_subtype_val.matrix_elem 0 1) continuous_const).inter
    ((isClosed_eq (continuous_subtype_val.matrix_elem 1 0) continuous_const).inter
      (isClosed_eq (continuous_subtype_val.matrix_elem 1 1)
        (continuous_subtype_val.matrix_elem 0 0).star))

lemma isClosed_setOf_isSatoTateAntidiagonalMatrix :
    IsClosed {A : unitaryGroup (Fin 2) ℂ | IsSatoTateAntidiagonalMatrix A} :=
  (isClosed_eq (continuous_subtype_val.matrix_elem 0 0) continuous_const).inter
    ((isClosed_eq (continuous_subtype_val.matrix_elem 1 1) continuous_const).inter
      (isClosed_eq (continuous_subtype_val.matrix_elem 1 0)
        (continuous_subtype_val.matrix_elem 0 1).star.neg))

/-- The Sato–Tate group **`SU(2)`** (LMFDB `ag.sato_tate_group`) of weight `1` and degree `2`: the
whole ambient group `USp(2)`, which is `SU(2)` (`mem_satoTateSU2_iff`), the Sato–Tate group of an
elliptic curve without potential complex multiplication. -/
def satoTateSU2 : SatoTateGroup where
  weight := 1
  degree := 2
  even_degree_of_odd_weight _ := even_two
  toSubgroup := ambientGroup 1 2
  isClosed := isClosed_ambientGroup 1 2
  le_ambientGroup := le_rfl

/-- The Sato–Tate group **`U(1)`** (LMFDB `ag.sato_tate_group`, the knowl's `SO(2)`) of weight `1`
and degree `2`: the circle of the matrices `diag(u, ū)`, the Sato–Tate group of an elliptic curve
with complex multiplication defined over its field of definition. -/
def satoTateU1 : SatoTateGroup where
  weight := 1
  degree := 2
  even_degree_of_odd_weight _ := even_two
  toSubgroup := satoTateTorus
  isClosed := isClosed_setOf_isSatoTateTorusMatrix
  le_ambientGroup U hU :=
    (mem_ambientGroup_one_two_iff U).mpr (det_eq_one_of_isSatoTateTorusMatrix hU)

/-- The Sato–Tate group **`N(U(1))`** (LMFDB `ag.sato_tate_group`) of weight `1` and degree `2`:
the normaliser `U(1) ∪ J U(1)` of the circle `U(1)` in `SU(2)`, the Sato–Tate group of an elliptic
curve with potential complex multiplication not defined over its field of definition. -/
def satoTateNU1 : SatoTateGroup where
  weight := 1
  degree := 2
  even_degree_of_odd_weight _ := even_two
  toSubgroup := satoTateTorusNormalizer
  isClosed :=
    isClosed_setOf_isSatoTateTorusMatrix.union isClosed_setOf_isSatoTateAntidiagonalMatrix
  le_ambientGroup U hU := (mem_ambientGroup_one_two_iff U).mpr <|
    hU.elim det_eq_one_of_isSatoTateTorusMatrix det_eq_one_of_isSatoTateAntidiagonalMatrix

variable (U) in
/-- **The ambient group `USp(2)` is `SU(2)`**: a unitary `2 × 2` matrix preserves the alternating
form exactly when its determinant is `1`. -/
lemma mem_satoTateSU2_iff : U ∈ satoTateSU2.toSubgroup ↔ (U : Matrix (Fin 2) (Fin 2) ℂ).det = 1 :=
  mem_ambientGroup_one_two_iff U

lemma isSatoTateTorusMatrix_or_isSatoTateAntidiagonalMatrix (hA : A * star A = 1)
    (hdet : A.det = 1) (h : (A * diagonal ![I, starRingEnd ℂ I] * star A) 0 1 = 0) :
    IsSatoTateTorusMatrix A ∨ IsSatoTateAntidiagonalMatrix A := by
  have h' : star A = adjugate A :=
    (left_inv_eq_right_inv (by rw [adjugate_mul, hdet, one_smul]) hA).symm
  have h₁₁ : A 1 1 = star (A 0 0) := by
    simpa [adjugate_fin_two] using (congrFun (congrFun h' 0) 0).symm
  have h₁₀ : A 1 0 = -star (A 0 1) := by
    simpa [adjugate_fin_two, neg_eq_iff_eq_neg] using (congrFun (congrFun h' 1) 0).symm
  have h₀₁ : (A * diagonal ![I, starRingEnd ℂ I] * star A) 0 1 =
      -(A 0 0 * I * A 0 1) + -(A 0 1 * I * A 0 0) := by
    simp [mul_apply, h₁₁, h₁₀]
  have h₂ : A 0 0 * A 0 1 = 0 := by
    linear_combination (I / 2) * (h₀₁.symm.trans h) + A 0 0 * A 0 1 * I_sq
  rcases mul_eq_zero.mp h₂ with h | h
  · exact .inr ⟨h, by rw [h₁₁, h, star_zero], h₁₀⟩
  · exact .inl ⟨h, by rw [h₁₀, h, star_zero, neg_zero], h₁₁⟩

lemma mem_normalizer_of_isSatoTateAntidiagonalMatrix (hU : IsSatoTateAntidiagonalMatrix U) :
    U ∈ Subgroup.normalizer satoTateTorus := by
  refine Subgroup.mem_normalizer_iff.mpr fun V ↦ ⟨fun hV ↦ (hU.mul_torus hV).mul hU.star,
    fun hV ↦ ?_⟩
  rw [show V = U⁻¹ * (U * V * U⁻¹) * U by group]
  exact (hU.star.mul_torus hV).mul hU

/-- **`N(U(1)) = U(1) ∪ J U(1)` is the normaliser of `U(1)` in `SU(2)`**, the ambient group
`USp(2)` (`mem_satoTateSU2_iff`): an element of `SU(2)` that normalises the circle conjugates
`diag(i, -i)` to a diagonal matrix, so it is diagonal or antidiagonal. -/
lemma satoTateTorusNormalizer_eq_normalizer_inf_ambientGroup :
    satoTateTorusNormalizer = Subgroup.normalizer satoTateTorus ⊓ ambientGroup 1 2 := by
  ext U
  refine ⟨fun hU ↦ ⟨hU.elim (fun h ↦ Subgroup.le_normalizer h)
    mem_normalizer_of_isSatoTateAntidiagonalMatrix, satoTateNU1.le_ambientGroup hU⟩, fun hU ↦ ?_⟩
  have hV : IsSatoTateTorusMatrix (diagonal ![I, starRingEnd ℂ I]) :=
    ⟨rfl, rfl, rfl⟩
  exact isSatoTateTorusMatrix_or_isSatoTateAntidiagonalMatrix (Unitary.mul_star_self_of_mem U.2)
    ((mem_satoTateSU2_iff U).mp hU.2) ((Subgroup.mem_normalizer_iff.mp hU.1
      ⟨_, (mem_specialUnitaryGroup_iff.mp (diagonal_mem_specialUnitaryGroup norm_I)).1⟩).mp hV).1

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

open scoped Classical in
/-- The **Sato–Tate group** (LMFDB `ag.sato_tate_group`) of an elliptic curve `W` over a number
field `K`, as the knowl describes it: `U(1)` if `W` has complex multiplication defined over `K`, the
normaliser `N(U(1))` of `U(1)` in `SU(2)` if `W` has potential complex multiplication not defined
over `K`, and `SU(2)` otherwise. The definition of the Sato–Tate group of a motive, through the
Zariski closure of the image of its `ℓ`-adic Galois representation, is not formalised. The
definition is stated for every field `K`, but the knowl, and the theory behind it, concern number
fields. -/
noncomputable def satoTateGroup : SatoTateGroup :=
  if W.HasCM then satoTateU1 else if W.HasGeometricCM then satoTateNU1 else satoTateSU2

variable {W}

/-- **With complex multiplication over `K`, the Sato–Tate group is `U(1)`.** -/
lemma satoTateGroup_of_hasCM (h : W.HasCM) : W.satoTateGroup = satoTateU1 := by
  rw [satoTateGroup, ite_eq_left h]

/-- **With potential complex multiplication not defined over `K`, the Sato–Tate group is
`N(U(1))`.** -/
lemma satoTateGroup_of_not_hasCM_of_hasGeometricCM (h : ¬W.HasCM) (h' : W.HasGeometricCM) :
    W.satoTateGroup = satoTateNU1 := by
  rw [satoTateGroup, ite_eq_right h, ite_eq_left h']

/-- **Without potential complex multiplication, the Sato–Tate group is `SU(2)`.** -/
lemma satoTateGroup_of_not_hasGeometricCM (h : ¬W.HasGeometricCM) :
    W.satoTateGroup = satoTateSU2 := by
  rw [satoTateGroup, ite_eq_right fun h' ↦ h h'.hasGeometricCM, ite_eq_right h]

end WeierstrassCurve
