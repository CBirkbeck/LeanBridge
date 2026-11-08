import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.EllipticCurve
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.MaximalSubgroup

/-!
# The Sato–Tate group `N(U(1))` and its maximal subgroup `U(1)`

The Sato–Tate group `N(U(1)) = U(1) ∪ J U(1)` (LMFDB `ag.sato_tate_group`,
`WeierstrassCurve.satoTateNU1`), of an elliptic curve with potential complex multiplication not
defined over its field of definition, is the union of the closed sets of its diagonal matrices
`diag(u, ū)` and of its antidiagonal matrices `(0, u; -ū, 0)`, which are disjoint and nonempty. So
it is not connected: a Sato–Tate group need not be connected (LMFDB `st_group.components`). Its
subgroup `U(1)` has index `2`, so it is a maximal subgroup (LMFDB `st_group.subgroups`), as the
LMFDB lists it.

## Main definitions

* `WeierstrassCurve.satoTateJ`: the matrix `J = (0, 1; -1, 0)` of `N(U(1))`.

## Main results

* `WeierstrassCurve.not_connectedSpace_satoTateNU1` (LMFDB `st_group.components`): the Sato–Tate
  group `N(U(1))` is not connected.
* `WeierstrassCurve.isMaximalSubgroup_satoTateTorus` (LMFDB `st_group.subgroups`): the circle
  `U(1)` is a maximal subgroup of `N(U(1))`.
-/

open Matrix

namespace WeierstrassCurve

variable {U : unitaryGroup (Fin 2) ℂ}

/-- The matrix `J = (0, 1; -1, 0)` of the unitary group `U(2)`, an antidiagonal matrix of the
normaliser `N(U(1))` of the circle `U(1)` that does not lie in `U(1)`. -/
def satoTateJ : unitaryGroup (Fin 2) ℂ :=
  ⟨!![0, 1; -1, 0], by
    rw [mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply]⟩

lemma isSatoTateAntidiagonalMatrix_satoTateJ : IsSatoTateAntidiagonalMatrix satoTateJ :=
  ⟨rfl, rfl, by simp [satoTateJ]⟩

lemma not_isSatoTateTorusMatrix_satoTateJ : ¬IsSatoTateTorusMatrix satoTateJ :=
  fun h ↦ one_ne_zero h.1

lemma not_isSatoTateTorusMatrix_of_isSatoTateAntidiagonalMatrix
    (hU : IsSatoTateAntidiagonalMatrix U) : ¬IsSatoTateTorusMatrix U := by
  intro h
  have h₁ : (U : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := det_eq_one_of_isSatoTateTorusMatrix h
  rw [det_fin_two, hU.1, h.1] at h₁
  simp at h₁

lemma satoTateJ_mem_satoTateTorusNormalizer : satoTateJ ∈ satoTateTorusNormalizer :=
  Or.inr isSatoTateAntidiagonalMatrix_satoTateJ

lemma not_connectedSpace_satoTateTorusNormalizer : ¬ConnectedSpace satoTateTorusNormalizer := by
  intro _
  let T : Set satoTateTorusNormalizer := {g | IsSatoTateTorusMatrix (g : unitaryGroup (Fin 2) ℂ)}
  have hT :
      T = (Subtype.val ⁻¹' {A : unitaryGroup (Fin 2) ℂ | IsSatoTateAntidiagonalMatrix A})ᶜ := by
    ext g
    exact ⟨fun hg hg' ↦ not_isSatoTateTorusMatrix_of_isSatoTateAntidiagonalMatrix hg' hg,
      fun hg ↦ Or.resolve_right g.2 hg⟩
  have hT' : IsClopen T := ⟨isClosed_setOf_isSatoTateTorusMatrix.preimage continuous_subtype_val,
    hT ▸ (isClosed_setOf_isSatoTateAntidiagonalMatrix.preimage continuous_subtype_val).isOpen_compl⟩
  rcases isClopen_iff.mp hT' with h | h
  · exact Set.eq_empty_iff_forall_notMem.mp h 1 isSatoTateTorusMatrix_one
  · have hJ : (⟨satoTateJ, satoTateJ_mem_satoTateTorusNormalizer⟩ : satoTateTorusNormalizer) ∈ T :=
      h ▸ Set.mem_univ _
    exact not_isSatoTateTorusMatrix_satoTateJ hJ

/-- **The Sato–Tate group `N(U(1))` is not connected** (LMFDB `st_group.components`): its diagonal
matrices form a closed and open subset containing `1` but not `J`. -/
lemma not_connectedSpace_satoTateNU1 : ¬ConnectedSpace satoTateNU1.toSubgroup :=
  not_connectedSpace_satoTateTorusNormalizer

lemma satoTateTorus_lt_satoTateTorusNormalizer : satoTateTorus < satoTateTorusNormalizer :=
  IsConcreteLE.lt_iff_le_and_exists.mpr ⟨fun _ ↦ Or.inl, satoTateJ,
    satoTateJ_mem_satoTateTorusNormalizer, not_isSatoTateTorusMatrix_satoTateJ⟩

lemma relIndex_satoTateTorus : satoTateTorus.relIndex satoTateTorusNormalizer = 2 := by
  refine Subgroup.index_eq_two_iff.mpr
    ⟨⟨satoTateJ, satoTateJ_mem_satoTateTorusNormalizer⟩, fun b ↦ ?_⟩
  rcases b.2 with hb | hb
  · exact Or.inr ⟨hb, not_isSatoTateTorusMatrix_of_isSatoTateAntidiagonalMatrix
      (hb.mul_antidiagonal isSatoTateAntidiagonalMatrix_satoTateJ)⟩
  · exact Or.inl ⟨hb.mul isSatoTateAntidiagonalMatrix_satoTateJ,
      not_isSatoTateTorusMatrix_of_isSatoTateAntidiagonalMatrix hb⟩

lemma not_lt_satoTateTorusNormalizer {K : Subgroup (unitaryGroup (Fin 2) ℂ)}
    (hTK : satoTateTorus < K) : ¬K < satoTateTorusNormalizer := by
  intro hKN
  rcases IsConcreteLE.exists_of_lt hTK with ⟨x, hxK, hxT⟩
  rcases IsConcreteLE.exists_of_lt hKN with ⟨y, hyN, hyK⟩
  have hx : IsSatoTateAntidiagonalMatrix x := Or.resolve_left (hKN.le hxK) hxT
  have hy : IsSatoTateAntidiagonalMatrix y := Or.resolve_left hyN fun h ↦ hyK (hTK.le h)
  have h : x⁻¹ * y ∈ K := hTK.le (hx.star.mul hy)
  exact hyK (by simpa using K.mul_mem hxK h)

/-- **The circle `U(1)` is a maximal subgroup of the Sato–Tate group `N(U(1))`** (LMFDB
`st_group.subgroups`): it has index `2`, its other coset being the antidiagonal matrices. -/
lemma isMaximalSubgroup_satoTateTorus : satoTateNU1.IsMaximalSubgroup satoTateTorus :=
  ⟨satoTateTorus_lt_satoTateTorusNormalizer, relIndex_satoTateTorus.trans_ne two_ne_zero,
    fun _ ↦ not_lt_satoTateTorusNormalizer⟩

end WeierstrassCurve
