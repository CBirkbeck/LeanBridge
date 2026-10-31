import TauCeti.Algebra.CentralSimple.Subfield
import TauCeti.Algebra.CentralSimple.Wedderburn
import TauCeti.Algebra.Quaternion.CentralSimple
import TauCeti.Algebra.Quaternion.Split
import TauCeti.LinearAlgebra.Matrix.TensorProduct

/-!
# Quaternion algebras are symbol algebras

A quaternion algebra over a field `F` (LMFDB `shimcurve.quaternion_algebra`) is a central simple
`F`-algebra of dimension `4`. When the characteristic of `F` is not `2`, every quaternion algebra
`B` has elements `i`, `j` such that `{1, i, j, ij}` is an `F`-basis of `B`, with `i ^ 2 = a`,
`j ^ 2 = b` for some `a b : Fˣ` and `j * i = -(i * j)` (LMFDB `shimcurve.b`); then
`B = B⟨i, j⟩ = (a, b / F)`, which is Mathlib's `ℍ[F,a,b]`.

By Wedderburn's theorem `B` is either the matrix algebra `M₂(F) ≅ ℍ[F,1,1]` or a division algebra.
In a central division algebra of dimension `4`, every element `y` generates a subfield `F[y]` of
degree at most `2`, so `y ^ 2 = s + t y` for some `s t : F`; completing the square in some `y ∉ F`
gives `i ∉ F` with `i ^ 2 = a ∈ F`, and for `x` not commuting with `i`, the element
`j = x i - i x` anticommutes with `i`, which forces the linear term of the quadratic satisfied by
`j` to vanish, so that `j ^ 2 = b ∈ F`. The pair `(i, j)` gives a homomorphism `ℍ[F,a,b] → B`,
injective because `ℍ[F,a,b]` is simple and surjective because both sides have dimension `4`.

## Main results

* `QuaternionAlgebra.exists_nonempty_algEquiv_of_finrank_eq_four` (LMFDB `shimcurve.b`): a
  quaternion algebra over a field of characteristic not `2` is isomorphic to some `ℍ[F,a,b]`.
* `QuaternionAlgebra.exists_bijective_liftHom_of_finrank_eq_four` (LMFDB `shimcurve.b`): the same
  in the form of the knowl, with elements `i`, `j` of `B` such that `{1, i, j, ij}` is a basis.
-/

open scoped Quaternion

open Algebra Module TauCeti

namespace QuaternionAlgebra

variable {F D B : Type*} [Field F] [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D] [Ring B]
  [Algebra F B] [Algebra.IsCentral F B] [IsSimpleRing B]

lemma exists_mul_self_eq_of_finrank_eq_four (h4 : finrank F D = 4) (y : D) :
    ∃ s t : F, y * y = algebraMap F D s + t • y := by
  have hfin : FiniteDimensional F D := .of_finrank_pos (by omega)
  have hy : y ∈ Algebra.adjoin F {y} := Algebra.self_mem_adjoin_singleton F y
  let _ : Field (Algebra.adjoin F {y}) := (IsField.of_isDomain_of_finite F _).toField
  have hle : finrank F (Algebra.adjoin F {y}) ≤ 2 :=
    (Algebra.finrank_le_deg (Algebra.adjoin F {y}).val).trans
      (Algebra.deg_eq_of_finrank_eq_sq (n := 2) h4).le
  have hdep :
      ¬LinearIndependent F ![(1 : Algebra.adjoin F {y}), ⟨y, hy⟩, ⟨y, hy⟩ * ⟨y, hy⟩] := fun h ↦ by
    have h3 : Fintype.card (Fin 3) ≤ finrank F (Algebra.adjoin F {y}) := h.fintype_card_le_finrank
    rw [Fintype.card_fin] at h3
    omega
  rcases Fintype.not_linearIndependent_iff.mp hdep with ⟨g, hg, i, hi⟩
  have hgD : g 0 • 1 + g 1 • y + g 2 • (y * y) = 0 := by
    simpa [Fin.sum_univ_three] using congrArg Subtype.val hg
  by_cases h2 : g 2 = 0
  · by_cases h1 : g 1 = 0
    · rw [h2, h1, zero_smul, zero_smul, add_zero, add_zero, smul_eq_zero] at hgD
      have h0 : g 0 = 0 := hgD.resolve_right one_ne_zero
      exact absurd hi (by fin_cases i <;> simpa)
    · refine ⟨(g 0 / g 1) ^ 2, 0, ?_⟩
      rw [h2, zero_smul, add_zero] at hgD
      have hy1 : y = algebraMap F D (-(g 0 / g 1)) := by
        rw [(eq_inv_smul_iff₀ h1).mpr (eq_neg_of_add_eq_zero_right hgD),
          Algebra.algebraMap_eq_smul_one]
        module
      rw [zero_smul, add_zero, hy1, ← map_mul, neg_mul_neg, sq]
  · refine ⟨-(g 0 / g 2), -(g 1 / g 2), ?_⟩
    rw [(eq_inv_smul_iff₀ h2).mpr (eq_neg_of_add_eq_zero_right hgD),
      Algebra.algebraMap_eq_smul_one]
    module

lemma exists_notMem_bot_mul_self_eq_of_finrank_eq_four (h2 : (2 : F) ≠ 0) (h4 : finrank F D = 4) :
    ∃ (i : D) (a : F), i ∉ (⊥ : Subalgebra F D) ∧ i * i = algebraMap F D a := by
  rcases IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr fun h : (⊥ : Subalgebra F D) = ⊤ ↦ by
    rw [Subalgebra.bot_eq_top_iff_finrank_eq_one] at h
    omega) with ⟨y, -, hy⟩
  rcases exists_mul_self_eq_of_finrank_eq_four h4 y with ⟨s, t, hst⟩
  refine ⟨(2 : F) • y - algebraMap F D t, 4 * s + t ^ 2, fun hmem ↦ hy ?_, ?_⟩
  · have hy2 : y = (2 : F)⁻¹ • ((2 : F) • y - algebraMap F D t + algebraMap F D t) := by
      rw [sub_add_cancel, inv_smul_smul₀ h2]
    rw [hy2]
    exact Subalgebra.smul_mem _ (add_mem hmem (Subalgebra.algebraMap_mem _ t)) _
  · have hyt : y * algebraMap F D t = t • y := by
      rw [← Algebra.commutes, ← Algebra.smul_def]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hst, hyt, ← Algebra.smul_def]
    simp only [Algebra.algebraMap_eq_smul_one]
    module

lemma exists_ne_zero_mul_eq_neg_of_notMem_bot {i : D} {a : F} (hi : i ∉ (⊥ : Subalgebra F D))
    (ha : i * i = algebraMap F D a) : ∃ j : D, j ≠ 0 ∧ j * i = -(i * j) := by
  rcases not_forall.mp (fun h : ∀ x : D, x * i = i * x ↦ hi <| by
    rw [← IsCentral.center_eq_bot F D]
    exact Subalgebra.mem_center_iff.mpr fun x ↦ h x) with ⟨x, hx⟩
  refine ⟨x * i - i * x, sub_ne_zero.mpr hx, ?_⟩
  rw [sub_mul, mul_sub, mul_assoc, ha, ← mul_assoc i i x, ha, ← Algebra.commutes, neg_sub,
    mul_assoc]

lemma exists_mul_self_eq_of_mul_eq_neg (h2 : (2 : F) ≠ 0) (h4 : finrank F D = 4) {i j : D}
    (hi : i ≠ 0) (hj : j ≠ 0) (hji : j * i = -(i * j)) : ∃ b : F, j * j = algebraMap F D b := by
  rcases exists_mul_self_eq_of_finrank_eq_four h4 j with ⟨s, t, hst⟩
  have hij : i * j = -(j * i) := by
    rw [hji, neg_neg]
  have hcomm : i * (j * j) = j * j * i := by
    rw [← mul_assoc, hij, neg_mul, mul_assoc, hij, mul_neg, neg_neg, ← mul_assoc]
  rw [hst, mul_add, add_mul, Algebra.commutes, mul_smul_comm, smul_mul_assoc, hji, smul_neg,
    add_right_inj, eq_neg_iff_add_eq_zero, ← two_smul F, smul_smul, smul_eq_zero] at hcomm
  refine ⟨s, ?_⟩
  rw [hst, (mul_eq_zero.mp (hcomm.resolve_right (mul_ne_zero hi hj))).resolve_left h2, zero_smul,
    add_zero]

lemma exists_nonempty_algEquiv_of_divisionRing (h2 : (2 : F) ≠ 0) (h4 : finrank F D = 4) :
    ∃ a b : Fˣ, Nonempty (ℍ[F,(a : F),(b : F)] ≃ₐ[F] D) := by
  rcases exists_notMem_bot_mul_self_eq_of_finrank_eq_four h2 h4 with ⟨i, a, hi, ha⟩
  have hi0 : i ≠ 0 := fun h ↦ hi (h ▸ zero_mem _)
  rcases exists_ne_zero_mul_eq_neg_of_notMem_bot hi ha with ⟨j, hj, hji⟩
  rcases exists_mul_self_eq_of_mul_eq_neg h2 h4 hi0 hj hji with ⟨b, hb⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_self_eq_zero] at ha
    exact hi0 ha
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_self_eq_zero] at hb
    exact hj hb
  let _ : Invertible (2 : F) := invertibleOfNonzero h2
  let q : Basis D ((Units.mk0 a ha0 : Fˣ) : F) 0 ((Units.mk0 b hb0 : Fˣ) : F) :=
    { i := i
      j := j
      k := i * j
      i_mul_i := by rw [ha, Units.val_mk0, Algebra.algebraMap_eq_smul_one, zero_smul, add_zero]
      j_mul_j := by rw [hb, Units.val_mk0, Algebra.algebraMap_eq_smul_one]
      i_mul_j := rfl
      j_mul_i := by rw [hji, zero_smul, zero_sub] }
  have hfin : FiniteDimensional F D := .of_finrank_pos (by omega)
  have hinj : Function.Injective q.liftHom := q.liftHom.toRingHom.injective
  refine ⟨Units.mk0 a ha0, Units.mk0 b hb0, ⟨AlgEquiv.ofBijective q.liftHom ⟨hinj, ?_⟩⟩⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := q.liftHom.toLinearMap)
    (by rw [finrank_eq_four, h4])).mp hinj

/-- **Every quaternion algebra over a field of characteristic not `2` is a symbol algebra**
(LMFDB `shimcurve.b`): a central simple `F`-algebra `B` of dimension `4` is isomorphic to
`ℍ[F,a,b] = (a, b / F)` for some `a b : Fˣ`. -/
lemma exists_nonempty_algEquiv_of_finrank_eq_four (hF : ringChar F ≠ 2) (h4 : finrank F B = 4) :
    ∃ a b : Fˣ, Nonempty (ℍ[F,(a : F),(b : F)] ≃ₐ[F] B) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hfin : FiniteDimensional F B := .of_finrank_pos (by omega)
  rcases IsSimpleRing.exists_algEquiv_matrix_centralDivisionRing F B with
    ⟨n, hn, E, _, _, _, _, hrank, ⟨e⟩⟩
  have hE : 0 < finrank F E := finrank_pos
  have hn2 : n ≤ 2 := by nlinarith
  interval_cases n
  · exact absurd rfl hn.out
  · rcases exists_nonempty_algEquiv_of_divisionRing h2 (by omega : finrank F E = 4) with
      ⟨a, b, ⟨f⟩⟩
    exact ⟨a, b, ⟨f.trans ((Matrix.finOneAlgEquiv F E).trans e.symm)⟩⟩
  · let _ : Invertible (2 : F) := invertibleOfNonzero h2
    have hbij : Function.Bijective (Algebra.ofId F E) :=
      ⟨(algebraMap F E).injective, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (f := (Algebra.ofId F E).toLinearMap) ((finrank_self F).trans (by omega))).mp
          (algebraMap F E).injective⟩
    exact ⟨1, 1, ⟨(QuaternionAlgebra.oneEquivMatrix 1).trans
      ((AlgEquiv.ofBijective (Algebra.ofId F E) hbij).mapMatrix.trans e.symm)⟩⟩

/-- **A quaternion algebra over a field of characteristic not `2` is `B⟨i, j⟩`** (LMFDB
`shimcurve.b`): a central simple `F`-algebra `B` of dimension `4` has elements `i = q.i` and
`j = q.j` with `i ^ 2 = a`, `j ^ 2 = b` for some `a b : Fˣ` and `j * i = -(i * j)` (a quaternion
basis `q` of `B`), such that `{1, i, j, ij}` is an `F`-basis of `B`, that is, the homomorphism
`ℍ[F,a,b] → B` sending the standard generators to `i` and `j` is bijective. -/
lemma exists_bijective_liftHom_of_finrank_eq_four (hF : ringChar F ≠ 2) (h4 : finrank F B = 4) :
    ∃ (a b : Fˣ) (q : Basis B (a : F) 0 (b : F)), Function.Bijective q.liftHom := by
  rcases exists_nonempty_algEquiv_of_finrank_eq_four hF h4 with ⟨a, b, ⟨f⟩⟩
  refine ⟨a, b, lift.symm f.toAlgHom, ?_⟩
  rw [← lift_apply, lift.apply_symm_apply]
  exact f.bijective

end QuaternionAlgebra
