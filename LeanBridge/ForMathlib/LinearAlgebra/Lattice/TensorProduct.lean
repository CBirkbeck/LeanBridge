import Mathlib.Algebra.Module.Submodule.Bilinear
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.LinearAlgebra.TensorProduct.Basis
import TauCeti.LinearAlgebra.IntegralLattice.Gram

/-!
# Tensor products of integral lattices

The tensor product (LMFDB `lattice.tensor_decomposition`) of integral lattices `L₁` and `L₂` is the
lattice `L₁ ⊗_ℤ L₂` with the bilinear form determined by
`B(v₁ ⊗ w₁, v₂ ⊗ w₂) = B_{L₁}(v₁, v₂) B_{L₂}(w₁, w₂)`. Here `L₁` and `L₂` span rational spaces
`V₁` and `V₂`, and `L₁ ⊗ L₂` is the `ℤ`-span of the tensors `v ⊗ w` with `v ∈ L₁` and `w ∈ L₂` in
`V₁ ⊗_ℚ V₂`, with Mathlib's tensor product `LinearMap.BilinForm.tmul` of the two rational forms; it
is a copy of `L₁ ⊗_ℤ L₂`, a `ℤ`-basis being given by the tensors `bᵢ ⊗ cⱼ` of bases `(bᵢ)` of `L₁`
and `(cⱼ)` of `L₂`. Its rank is the product of the ranks, and
`det(L₁ ⊗ L₂) = det(L₁)^{rank L₂} det(L₂)^{rank L₁}`.

A lattice `L` is tensor decomposable if it is isometric to a tensor product `L₁ ⊗ L₂`, and tensor
indecomposable otherwise. Both factors are required to have rank at least `2`, as is usual: since
`L ≅ L ⊗ ⟨1⟩`, the literal condition of the knowl would make every lattice decomposable. A tensor
decomposition of `L` is an isometry `L₁ ⊗ L₂ ⊗ ⋯ ⊗ L_r ≅ L`, the tensor product of `r` lattices
being defined in the same way in `⨂ᵢ Vᵢ`; as in the knowl, its factors are not restricted.

## Main definitions

* `TauCeti.IntegralLattice.tensorProduct` (LMFDB `lattice.tensor_decomposition`).
* `TauCeti.IntegralLattice.IsTensorDecomposable` (LMFDB `lattice.tensor_decomposition`).
* `TauCeti.IntegralLattice.IsTensorIndecomposable` (LMFDB `lattice.tensor_decomposition`).
* `TauCeti.IntegralLattice.piTensorProduct`: the tensor product of finitely many lattices.
* `TauCeti.IntegralLattice.TensorDecomposition` (LMFDB `lattice.tensor_decomposition`).
* `TauCeti.IntegralLattice.Isometry.tensorProduct`: the tensor product of two isometries.

## Main results

* `TauCeti.IntegralLattice.tensorProduct_form_tmul`: the form of `L₁ ⊗ L₂` is
  `B(v₁ ⊗ w₁, v₂ ⊗ w₂) = B_{L₁}(v₁, v₂) B_{L₂}(w₁, w₂)`.
* `TauCeti.IntegralLattice.tensorProduct_carrier`: `L₁ ⊗ L₂` is spanned by the tensors `v ⊗ w`
  with `v ∈ L₁` and `w ∈ L₂`.
* `TauCeti.IntegralLattice.finrank_tensorProduct`: its rank is the product of the ranks.
* `TauCeti.IntegralLattice.determinant_tensorProduct`:
  `det(L₁ ⊗ L₂) = det(L₁)^{rank L₂} det(L₂)^{rank L₁}`.
* `TauCeti.IntegralLattice.isTensorDecomposable_of_isometry`: a lattice isometric to a tensor
  product of lattices of rank at least `2`, in any rational spaces, is tensor decomposable.
* `TauCeti.IntegralLattice.piTensorProduct_form_tprod`,
  `TauCeti.IntegralLattice.piTensorProduct_carrier` and
  `TauCeti.IntegralLattice.finrank_piTensorProduct`: the same for `L₁ ⊗ ⋯ ⊗ L_r`.
-/

open Module TensorProduct
open LinearMap (BilinForm)

namespace TauCeti.IntegralLattice

variable {V W V' W' : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  [AddCommGroup V'] [Module ℚ V'] [AddCommGroup W'] [Module ℚ W'] (L : IntegralLattice V)
  (M : IntegralLattice W) {L' : IntegralLattice V'} {M' : IntegralLattice W'} {ι : Type*}
  [Fintype ι] {U : ι → Type*} [∀ i, AddCommGroup (U i)] [∀ i, Module ℚ (U i)]
  (Λ : (i : ι) → IntegralLattice (U i)) (v w : (i : ι) → U i)

lemma form_tmul_form_mem_one (p q : Free.ChooseBasisIndex ℤ L × Free.ChooseBasisIndex ℤ M) :
    L.form.tmul M.form (L.rationalBasis.tensorProduct M.rationalBasis p)
      (L.rationalBasis.tensorProduct M.rationalBasis q) ∈ (1 : Submodule ℤ ℚ) := by
  rw [Basis.tensorProduct_apply', Basis.tensorProduct_apply', BilinForm.tensorDistrib_tmul,
    rationalBasis_apply, rationalBasis_apply, rationalBasis_apply, rationalBasis_apply,
    smul_eq_mul]
  exact one_mul (1 : Submodule ℤ ℚ) ▸
    Submodule.mul_mem_mul (M.form_mem_one _ _) (L.form_mem_one _ _)

/-- The **tensor product** `L ⊗ M` (LMFDB `lattice.tensor_decomposition`) of integral lattices
`L` and `M` in rational spaces `V` and `W`: the lattice of `V ⊗ W` spanned by the tensors `v ⊗ w`
with `v ∈ L` and `w ∈ M` (`tensorProduct_carrier`), a copy of `L ⊗_ℤ M`, with the tensor product
of the bilinear forms, `B(v ⊗ w, v' ⊗ w') = B_L(v, v') B_M(w, w')` (`tensorProduct_form_tmul`). It
is built from the tensor products of chosen bases of `L` and `M`, but does not depend on them. -/
noncomputable def tensorProduct : IntegralLattice (V ⊗[ℚ] W) :=
  ofBasis (L.rationalBasis.tensorProduct M.rationalBasis) (L.form.tmul M.form)
    (BilinForm.isSymm_iff.mpr <| (BilinForm.isSymm_iff.mp L.isSymm).tmul <|
      BilinForm.isSymm_iff.mp M.isSymm) (L.form_tmul_form_mem_one M)

/-- The basis `(bᵢ ⊗ cⱼ)` of `L ⊗ M` made of the tensor products of the chosen bases `(bᵢ)` of
`L` and `(cⱼ)` of `M`. -/
noncomputable def tensorProductBasis :
    Basis (Free.ChooseBasisIndex ℤ L × Free.ChooseBasisIndex ℤ M) ℤ (L.tensorProduct M) :=
  ofBasis.basis _ _ _ _

lemma coe_tensorProductBasis (i : Free.ChooseBasisIndex ℤ L) (j : Free.ChooseBasisIndex ℤ M) :
    (L.tensorProductBasis M (i, j) : V ⊗[ℚ] W) =
      (Free.chooseBasis ℤ L i : V) ⊗ₜ (Free.chooseBasis ℤ M j : W) :=
  (ofBasis.coe_basis _ _ _ _ (i, j)).trans <| by
    rw [Basis.tensorProduct_apply, rationalBasis_apply, rationalBasis_apply]

/-- **The form of `L ⊗ M` is `B(v ⊗ w, v' ⊗ w') = B_L(v, v') B_M(w, w')`.** -/
lemma tensorProduct_form_tmul (x x' : V) (y y' : W) :
    (L.tensorProduct M).form (x ⊗ₜ y) (x' ⊗ₜ y') = L.form x x' * M.form y y' :=
  mul_comm (M.form y y') (L.form x x')

/-- **`L ⊗ M` is spanned by the tensors `v ⊗ w` with `v ∈ L` and `w ∈ M`.** -/
lemma tensorProduct_carrier : (L.tensorProduct M).carrier = Submodule.span ℤ
    (Set.image2 (· ⊗ₜ[ℚ] ·) (L.carrier : Set V) (M.carrier : Set W)) := by
  let f : V →ₗ[ℤ] W →ₗ[ℤ] V ⊗[ℚ] W := (TensorProduct.mk ℚ V W).restrictScalars₁₂ ℤ ℤ
  rw [tensorProduct, ofBasis_carrier,
    funext (Basis.tensorProduct_apply' L.rationalBasis M.rationalBasis), ← Set.image2_range]
  refine (Submodule.map₂_span_span ℤ f _ _).symm.trans ?_
  rw [rationalBasis, rationalBasis, Basis.span_range_extendOfIsLattice,
    Basis.span_range_extendOfIsLattice, Submodule.map₂_eq_span_image2]
  rfl

/-- **The rank of `L ⊗ M` is the product of the ranks of `L` and `M`.** -/
lemma finrank_tensorProduct : finrank ℤ (L.tensorProduct M) = finrank ℤ L * finrank ℤ M := by
  rw [finrank_eq_card_basis (L.tensorProductBasis M), Fintype.card_prod,
    ← finrank_eq_card_chooseBasisIndex, ← finrank_eq_card_chooseBasisIndex]

lemma gramMatrix_tensorProductBasis : (L.tensorProduct M).gramMatrix (L.tensorProductBasis M) =
    Matrix.kroneckerMap (· * ·) (L.gramMatrix (Free.chooseBasis ℤ L))
      (M.gramMatrix (Free.chooseBasis ℤ M)) := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  apply Int.cast_injective (α := ℚ)
  rw [gramMatrix_apply, integralForm_cast, coe_tensorProductBasis, coe_tensorProductBasis,
    tensorProduct_form_tmul, Matrix.kroneckerMap_apply, gramMatrix_apply, gramMatrix_apply,
    Int.cast_mul, integralForm_cast, integralForm_cast]

/-- **`det(L ⊗ M) = det(L)^{rank M} det(M)^{rank L}`.** -/
lemma determinant_tensorProduct : (L.tensorProduct M).determinant =
    L.determinant ^ finrank ℤ M * M.determinant ^ finrank ℤ L := by
  rw [determinant_eq_gramDet _ (L.tensorProductBasis M), gramDet_def,
    gramMatrix_tensorProductBasis, Matrix.det_kronecker, ← gramDet_def, ← gramDet_def,
    ← determinant_eq_gramDet, ← determinant_eq_gramDet, finrank_eq_card_chooseBasisIndex,
    finrank_eq_card_chooseBasisIndex]

/-- An integral lattice `L` is **tensor decomposable** (LMFDB `lattice.tensor_decomposition`) if
it is isometric to a tensor product `L₁ ⊗ L₂` of integral lattices of rank at least `2`. The ranks
are bounded below as usual, since `L ≅ L ⊗ ⟨1⟩` for every `L`. The factors are taken in the
rational spaces `ℚᵐ` and `ℚⁿ`, which is no restriction (`isTensorDecomposable_of_isometry`). -/
def IsTensorDecomposable : Prop :=
  ∃ (m n : ℕ) (L₁ : IntegralLattice (Fin m → ℚ)) (L₂ : IntegralLattice (Fin n → ℚ)),
    2 ≤ m ∧ 2 ≤ n ∧ Nonempty (Isometry (L₁.tensorProduct L₂) L)

/-- An integral lattice is **tensor indecomposable** (LMFDB `lattice.tensor_decomposition`) if it
is not tensor decomposable. -/
def IsTensorIndecomposable : Prop :=
  ¬L.IsTensorDecomposable

/-- The rational bilinear form `(⨂ᵢ vᵢ, ⨂ᵢ wᵢ) ↦ ∏ᵢ B_{Λᵢ}(vᵢ, wᵢ)` on `⨂ᵢ Uᵢ`. -/
noncomputable def piTensorProductForm : BilinForm ℚ (⨂[ℚ] i, U i) :=
  PiTensorProduct.dualDistrib ∘ₗ PiTensorProduct.map fun i ↦ (Λ i).form

lemma piTensorProductForm_tprod :
    piTensorProductForm Λ (⨂ₜ[ℚ] i, v i) (⨂ₜ[ℚ] i, w i) = ∏ i, (Λ i).form (v i) (w i) := by
  rw [piTensorProductForm, LinearMap.comp_apply, PiTensorProduct.map_tprod,
    PiTensorProduct.dualDistrib_apply]

lemma isSymm_piTensorProductForm : (piTensorProductForm Λ).IsSymm := by
  refine BilinForm.isSymm_iff.mpr <| LinearMap.isSymm_iff_eq_flip.mpr <|
    PiTensorProduct.ext <| MultilinearMap.ext fun v ↦ PiTensorProduct.ext <|
      MultilinearMap.ext fun w ↦ ?_
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply, LinearMap.flip_apply,
    piTensorProductForm_tprod, piTensorProductForm_tprod]
  exact Finset.prod_congr rfl fun i _ ↦ (Λ i).isSymm.eq (v i) (w i)

lemma piTensorProductForm_mem_one (p q : (i : ι) → Free.ChooseBasisIndex ℤ (Λ i)) :
    piTensorProductForm Λ (Basis.piTensorProduct (fun i ↦ (Λ i).rationalBasis) p)
      (Basis.piTensorProduct (fun i ↦ (Λ i).rationalBasis) q) ∈ (1 : Submodule ℤ ℚ) := by
  rw [Basis.piTensorProduct_apply, Basis.piTensorProduct_apply, piTensorProductForm_tprod]
  refine Submodule.mem_one.mpr ⟨∏ i, (Λ i).integralForm (Free.chooseBasis ℤ (Λ i) (p i))
    (Free.chooseBasis ℤ (Λ i) (q i)), ?_⟩
  simp

/-- The **tensor product** `Λ₁ ⊗ ⋯ ⊗ Λ_r` of finitely many integral lattices `Λᵢ` in rational
spaces `Uᵢ`: the lattice of `⨂ᵢ Uᵢ` spanned by the tensors `⨂ᵢ vᵢ` with `vᵢ ∈ Λᵢ`
(`piTensorProduct_carrier`), with the bilinear form `(⨂ᵢ vᵢ, ⨂ᵢ wᵢ) ↦ ∏ᵢ B_{Λᵢ}(vᵢ, wᵢ)`
(`piTensorProduct_form_tprod`). It is built from the tensors `⨂ᵢ bᵢ(pᵢ)` of chosen bases `bᵢ` of
the `Λᵢ`, but does not depend on them. -/
noncomputable def piTensorProduct : IntegralLattice (⨂[ℚ] i, U i) :=
  ofBasis (Basis.piTensorProduct fun i ↦ (Λ i).rationalBasis) (piTensorProductForm Λ)
    (isSymm_piTensorProductForm Λ) (piTensorProductForm_mem_one Λ)

/-- The basis `(⨂ᵢ bᵢ(pᵢ))` of `Λ₁ ⊗ ⋯ ⊗ Λ_r` made of the tensor products of the chosen bases
`bᵢ` of the `Λᵢ`. -/
noncomputable def piTensorProductBasis :
    Basis ((i : ι) → Free.ChooseBasisIndex ℤ (Λ i)) ℤ (piTensorProduct Λ) :=
  ofBasis.basis _ _ _ _

/-- **The form of `Λ₁ ⊗ ⋯ ⊗ Λ_r` is `(⨂ᵢ vᵢ, ⨂ᵢ wᵢ) ↦ ∏ᵢ B_{Λᵢ}(vᵢ, wᵢ)`.** -/
lemma piTensorProduct_form_tprod :
    (piTensorProduct Λ).form (⨂ₜ[ℚ] i, v i) (⨂ₜ[ℚ] i, w i) = ∏ i, (Λ i).form (v i) (w i) :=
  piTensorProductForm_tprod Λ v w

/-- **`Λ₁ ⊗ ⋯ ⊗ Λ_r` is spanned by the tensors `⨂ᵢ vᵢ` with `vᵢ ∈ Λᵢ`.** -/
lemma piTensorProduct_carrier : (piTensorProduct Λ).carrier = Submodule.span ℤ
    (Set.range fun v : (i : ι) → Λ i ↦ ⨂ₜ[ℚ] i, (v i : U i)) := by
  classical
  rw [piTensorProduct, ofBasis_carrier, funext (Basis.piTensorProduct_apply _)]
  refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨p, rfl⟩
    exact ⟨fun i ↦ Free.chooseBasis ℤ (Λ i) (p i), by simp⟩
  · rintro _ ⟨v, rfl⟩
    have hv (i : ι) : (v i : U i) ∈ Submodule.span ℤ (Set.range (Λ i).rationalBasis) := by
      rw [rationalBasis, Basis.span_range_extendOfIsLattice]
      exact (v i).2
    simp_rw [Finsupp.mem_span_range_iff_exists_finsupp] at hv
    choose c hc using hv
    simp_rw [← hc, Finsupp.sum,
      ← MultilinearMap.coe_restrictScalars ℤ (PiTensorProduct.tprod ℚ),
      MultilinearMap.map_sum_finset, MultilinearMap.map_smul_univ]
    exact sum_mem fun p _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

/-- **The rank of `Λ₁ ⊗ ⋯ ⊗ Λ_r` is the product of the ranks of the `Λᵢ`.** -/
lemma finrank_piTensorProduct : finrank ℤ (piTensorProduct Λ) = ∏ i, finrank ℤ (Λ i) := by
  classical
  rw [finrank_eq_card_basis (piTensorProductBasis Λ), Fintype.card_pi]
  exact Finset.prod_congr rfl fun i _ ↦ (finrank_eq_card_chooseBasisIndex ℤ (Λ i)).symm

/-- A **tensor decomposition** `L = L₁ ⊗ L₂ ⊗ ⋯ ⊗ L_r` (LMFDB `lattice.tensor_decomposition`) of
an integral lattice `L`: integral lattices `L₁, …, L_r`, in the rational spaces
`ℚ^{n₁}, …, ℚ^{n_r}`, with an isometry from their tensor product onto `L`. -/
structure TensorDecomposition where
  /-- The number `r` of factors. -/
  length : ℕ
  /-- The ranks `n₁, …, n_r` of the factors. -/
  rank : Fin length → ℕ
  /-- The factors `L₁, …, L_r`. -/
  factor (i : Fin length) : IntegralLattice (Fin (rank i) → ℚ)
  /-- The isometry `L₁ ⊗ ⋯ ⊗ L_r ≅ L`. -/
  isometry : Isometry (piTensorProduct factor) L

variable {L M} (e : Isometry L L') (f : Isometry M M')

lemma tensorProduct_form_congr (x y : V ⊗[ℚ] W) : (L'.tensorProduct M').form
    (congr e.toLinearEquiv f.toLinearEquiv x) (congr e.toLinearEquiv f.toLinearEquiv y) =
      (L.tensorProduct M).form x y := by
  induction x using TensorProduct.inductionOn with
  | tmul x₁ x₂ =>
    induction y using TensorProduct.inductionOn with
    | tmul y₁ y₂ =>
      rw [congr_tmul, congr_tmul, tensorProduct_form_tmul, tensorProduct_form_tmul,
        Isometry.coe_toLinearEquiv, Isometry.coe_toLinearEquiv, e.map_app, f.map_app]
    | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']

/-- The **tensor product of isometries** `L ≅ L'` and `M ≅ M'`: an isometry
`L ⊗ M ≅ L' ⊗ M'`. -/
noncomputable def Isometry.tensorProduct : Isometry (L.tensorProduct M) (L'.tensorProduct M') where
  toLinearEquiv := congr e.toLinearEquiv f.toLinearEquiv
  map_app' := tensorProduct_form_congr e f
  map_carrier := by
    rw [tensorProduct_carrier, tensorProduct_carrier, Submodule.map_span, ← e.map_carrier,
      ← f.map_carrier, Submodule.map_coe, Submodule.map_coe, Set.image2_image_left,
      Set.image2_image_right, Set.image_image2]
    rfl

/-- **A lattice isometric to a tensor product of lattices of rank at least `2` is tensor
decomposable**, whatever the rational spaces of the factors. -/
lemma isTensorDecomposable_of_isometry (hL' : 2 ≤ finrank ℤ L') (hM' : 2 ≤ finrank ℤ M')
    (g : Isometry (L'.tensorProduct M') L) : L.IsTensorDecomposable := by
  have : FiniteDimensional ℚ V' := L'.finiteDimensional
  have : FiniteDimensional ℚ W' := M'.finiteDimensional
  exact ⟨_, _, _, _, L'.finrank_carrier ▸ hL', M'.finrank_carrier ▸ hM',
    ⟨((L'.transportIsometry (finBasis ℚ V').equivFun).tensorProduct
      (M'.transportIsometry (finBasis ℚ W').equivFun)).symm.trans g⟩⟩

end TauCeti.IntegralLattice
