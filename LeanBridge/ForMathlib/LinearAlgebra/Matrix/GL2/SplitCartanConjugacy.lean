import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.CartanConjugate
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.SplitCartan
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Split Cartan subgroups are the conjugates of the diagonal torus

A split Cartan subgroup of `GL₂(F)` (LMFDB `gl2.split_cartan`) is a Cartan subgroup, the image of
the units of a free rank-2 étale `F`-algebra `A` in a basis, with a conjugate inside the group of
invertible diagonal matrices. That conjugate is then the whole diagonal torus, over every field `F`.
Over `𝔽₂` the torus is trivial. Otherwise `F` has an element `c ≠ 0, 1`; an element `a` of `A`
outside `F` has a translate `a + t`, `t ∈ {0, 1, c}`, that is a unit, since the determinant of
multiplication by `a + t` is a monic quadratic polynomial in `t`, and the three values cannot all
vanish. The matrix of multiplication by `u = a + t` is then diagonal with distinct entries, so
every diagonal matrix is the matrix of multiplication by some `α + β u`, `α, β ∈ F`, and every
invertible one by a unit of `A`. So the split Cartan subgroups are exactly the conjugates of the
diagonal torus, which is isomorphic to `Fˣ × Fˣ`.

## Main definitions

* `Matrix.GeneralLinearGroup.diagonalTorusMulEquivProd` (LMFDB `gl2.split_cartan`): the
  isomorphism of the diagonal torus of `GL₂(F)` with `Fˣ × Fˣ`.

## Main results

* `Matrix.GeneralLinearGroup.isUnit_iff_det_leftMulMatrix_ne_zero`: an element of a free algebra of
  finite rank over a field is a unit exactly when the determinant of multiplication by it is
  nonzero.
* `Matrix.GeneralLinearGroup.exists_det_leftMulMatrix_add_algebraMap_ne_zero`: over a field with
  an element other than `0` and `1`, every element of a free rank-2 algebra has a translate by a
  scalar that is a unit.
* `Matrix.GeneralLinearGroup.cartanSubgroup_eq_diagonalTorus_of_le`: a Cartan subgroup consisting
  of diagonal matrices is the whole diagonal torus.
* `Matrix.GeneralLinearGroup.IsSplitCartanSubgroup.exists_map_conj_eq` (LMFDB
  `gl2.split_cartan`): every split Cartan subgroup is conjugate to the diagonal torus.
* `Matrix.GeneralLinearGroup.isSplitCartanSubgroup_iff` (LMFDB `gl2.split_cartan`): the split
  Cartan subgroups are exactly the conjugates of the diagonal torus.
-/

open Matrix Module TauCeti

namespace Matrix.GeneralLinearGroup

universe u v

variable {F : Type u} [Field F] {A : Type v} [CommRing A] [Algebra F A] (b : Basis (Fin 2) F A)

variable (F) in
/-- The **isomorphism of the diagonal torus of `GL₂(F)` with `Fˣ × Fˣ`** (LMFDB `gl2.split_cartan`),
by the two diagonal entries. -/
noncomputable def diagonalTorusMulEquivProd : diagonalTorus F 2 ≃* Fˣ × Fˣ :=
  (diagonalTorusEquiv F 2).symm.trans { piFinTwoEquiv fun _ ↦ Fˣ with map_mul' _ _ := rfl }

/-- **An element of a free algebra of rank `2` over a field is a unit exactly when the determinant
of multiplication by it is nonzero.** -/
lemma isUnit_iff_det_leftMulMatrix_ne_zero (x : A) :
    IsUnit x ↔ (Algebra.leftMulMatrix b x).det ≠ 0 := by
  have : Module.Finite F A := .of_basis b
  have : Module.Free F A := .of_basis b
  rw [← Algebra.lmul_isUnit_iff (R := F), LinearMap.isUnit_iff_isUnit_det,
    ← LinearMap.det_toMatrix b, ← Algebra.leftMulMatrix_apply, isUnit_iff_ne_zero]

/-- **Every element of a free rank-2 algebra over a field with an element `c ≠ 0, 1` has a
translate by a scalar that is a unit**: the determinant of multiplication by `a + t` is a monic
quadratic polynomial in `t`, which cannot vanish at `0`, `1` and `c`. -/
lemma exists_det_leftMulMatrix_add_algebraMap_ne_zero (a : A) {c : F} (hc : c ≠ 0) (hc₁ : c ≠ 1) :
    ∃ t : F, (Algebra.leftMulMatrix b (a + algebraMap F A t)).det ≠ 0 := by
  by_contra h
  have hdet (t : F) : (Algebra.leftMulMatrix b a 0 0 + t) * (Algebra.leftMulMatrix b a 1 1 + t) -
      Algebra.leftMulMatrix b a 0 1 * Algebra.leftMulMatrix b a 1 0 = 0 := by
    have ht : ¬(Algebra.leftMulMatrix b (a + algebraMap F A t)).det ≠ 0 := not_exists.mp h t
    rw [not_not, map_add, AlgHom.commutes, det_fin_two] at ht
    simpa [algebraMap_eq_diagonal] using ht
  refine mul_ne_zero hc (sub_ne_zero.mpr hc₁) ?_
  linear_combination hdet c - hdet 0 - c * (hdet 1 - hdet 0)

lemma leftMulMatrix_eq_of_isDiag {u : A} (hu : (Algebra.leftMulMatrix b u).IsDiag)
    (hne : Algebra.leftMulMatrix b u 0 0 ≠ Algebra.leftMulMatrix b u 1 1)
    {d : Matrix (Fin 2) (Fin 2) F} (hd : d.IsDiag) :
    letI c : F := (d 0 0 - d 1 1) / (Algebra.leftMulMatrix b u 0 0 - Algebra.leftMulMatrix b u 1 1)
    Algebra.leftMulMatrix b (algebraMap F A (d 0 0 - c * Algebra.leftMulMatrix b u 0 0) + c • u) =
      d := by
  have hsub : Algebra.leftMulMatrix b u 0 0 - Algebra.leftMulMatrix b u 1 1 ≠ 0 :=
    sub_ne_zero.mpr hne
  ext i j
  fin_cases i <;> fin_cases j
  · simp [algebraMap_eq_diagonal]
  · simp [algebraMap_eq_diagonal, hu (show (0 : Fin 2) ≠ 1 by decide),
      hd (show (0 : Fin 2) ≠ 1 by decide)]
  · simp [algebraMap_eq_diagonal, hu (show (1 : Fin 2) ≠ 0 by decide),
      hd (show (1 : Fin 2) ≠ 0 by decide)]
  · simp [algebraMap_eq_diagonal]
    field_simp
    ring1

lemma exists_isDiag_ne_of_le (h : cartanSubgroup b ≤ diagonalTorus F 2) {c : F} (hc : c ≠ 0)
    (hc₁ : c ≠ 1) : ∃ u : A, (Algebra.leftMulMatrix b u).IsDiag ∧ Algebra.leftMulMatrix b u 0 0 ≠
    Algebra.leftMulMatrix b u 1 1 := by
  have : Nontrivial A := nontrivial_of_ne _ _ (b.ne_zero 0)
  have : Module.Free F A := .of_basis b
  have hbot : (⊥ : Subalgebra F A) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h₁ ↦ ?_
    have h₂ : Module.finrank F A = 1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp h₁
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin] at h₂
    exact absurd h₂ (by decide)
  rcases IsConcreteLE.exists_of_lt hbot with ⟨a, -, ha⟩
  rcases exists_det_leftMulMatrix_add_algebraMap_ne_zero b a hc hc₁ with ⟨t, ht⟩
  have hu : (Algebra.leftMulMatrix b (a + algebraMap F A t)).IsDiag := by
    have hmem : unitsLeftMulMatrix b ((isUnit_iff_det_leftMulMatrix_ne_zero b _).mpr ht).unit ∈
        diagonalTorus F 2 := h ⟨_, rfl⟩
    rwa [mem_diagonalTorus_iff, coe_unitsLeftMulMatrix, IsUnit.unit_spec] at hmem
  refine ⟨_, hu, fun h₀ ↦ ha (Algebra.mem_bot.mpr ⟨Algebra.leftMulMatrix b
    (a + algebraMap F A t) 0 0 - t, ?_⟩)⟩
  have hL : Algebra.leftMulMatrix b (a + algebraMap F A t) = Algebra.leftMulMatrix b
      (algebraMap F A (Algebra.leftMulMatrix b (a + algebraMap F A t) 0 0)) := by
    rw [AlgHom.commutes]
    ext i j
    fin_cases i <;> fin_cases j
    · simp [algebraMap_eq_diagonal]
    · simp [algebraMap_eq_diagonal, hu (show (0 : Fin 2) ≠ 1 by decide)]
    · simp [algebraMap_eq_diagonal, hu (show (1 : Fin 2) ≠ 0 by decide)]
    · simp [algebraMap_eq_diagonal, h₀]
  rw [map_sub, ← Algebra.leftMulMatrix_injective b hL, add_sub_cancel_right]

/-- **A Cartan subgroup of `GL₂(F)` consisting of diagonal matrices is the whole diagonal torus**:
over `𝔽₂` the torus is trivial, and otherwise the Cartan subgroup contains the matrix of a unit `u`
with distinct diagonal entries, so every invertible diagonal matrix is the matrix of multiplication
by a unit `α + β u`. -/
lemma cartanSubgroup_eq_diagonalTorus_of_le (h : cartanSubgroup b ≤ diagonalTorus F 2) :
    cartanSubgroup b = diagonalTorus F 2 := by
  refine le_antisymm h fun d hd ↦ ?_
  by_cases hF : ∃ c : F, c ≠ 0 ∧ c ≠ 1
  · rcases hF with ⟨c, hc, hc₁⟩
    rcases exists_isDiag_ne_of_le b h hc hc₁ with ⟨u, hu, hne⟩
    let k : F := (d 0 0 - d 1 1) / (Algebra.leftMulMatrix b u 0 0 - Algebra.leftMulMatrix b u 1 1)
    let w : A := algebraMap F A (d 0 0 - k * Algebra.leftMulMatrix b u 0 0) + k • u
    have hw : Algebra.leftMulMatrix b w = d :=
      leftMulMatrix_eq_of_isDiag b hu hne (mem_diagonalTorus_iff.mp hd)
    exact ⟨((isUnit_iff_det_leftMulMatrix_ne_zero b w).mpr (hw ▸ (det d).ne_zero)).unit,
      Units.ext <| (coe_unitsLeftMulMatrix b _).trans hw⟩
  · have hF₁ (c : F) (hc : c ≠ 0) : c = 1 := not_not.mp fun hc₁ ↦ hF ⟨c, hc, hc₁⟩
    have : Subsingleton Fˣ :=
      ⟨fun x y ↦ Units.ext <| (hF₁ _ x.ne_zero).trans (hF₁ _ y.ne_zero).symm⟩
    rw [diagonalTorus_eq_bot, Subgroup.mem_bot] at hd
    exact hd ▸ one_mem _

variable {H : Subgroup (GL (Fin 2) F)}

/-- **Every split Cartan subgroup of `GL₂(F)` is conjugate to the subgroup of diagonal matrices**
(LMFDB `gl2.split_cartan`), which is isomorphic to `Fˣ × Fˣ` (`diagonalTorusMulEquivProd`): its
conjugate consisting of diagonal matrices is a Cartan subgroup, hence the whole diagonal torus. -/
lemma IsSplitCartanSubgroup.exists_map_conj_eq (hH : IsSplitCartanSubgroup H) :
    ∃ g : GL (Fin 2) F, H.map (MulAut.conj g).toMonoidHom = diagonalTorus F 2 := by
  rcases hH with ⟨⟨A, _, _, _, b, rfl⟩, g, hg⟩
  rw [cartanSubgroup_map_conj] at hg
  exact ⟨g, (cartanSubgroup_map_conj b g).trans (cartanSubgroup_eq_diagonalTorus_of_le _ hg)⟩

/-- **The split Cartan subgroups of `GL₂(F)` are exactly the conjugates of the subgroup of diagonal
matrices** (LMFDB `gl2.split_cartan`). -/
lemma isSplitCartanSubgroup_iff : IsSplitCartanSubgroup H ↔ ∃ g : GL (Fin 2) F,
    H.map (MulAut.conj g).toMonoidHom = diagonalTorus F 2 := by
  refine ⟨fun hH ↦ hH.exists_map_conj_eq, fun ⟨g, hg⟩ ↦ ⟨?_, g, hg.le⟩⟩
  have hH : (diagonalTorus F 2).map (MulAut.conj g⁻¹).toMonoidHom = H := by
    have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext fun x ↦ by simp [mul_assoc]
    rw [← hg, Subgroup.map_map, hid, Subgroup.map_id]
  exact hH ▸ (isSplitCartanSubgroup_diagonalTorus F).1.map_conj g⁻¹

end Matrix.GeneralLinearGroup
