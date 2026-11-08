import LeanBridge.ForMathlib.Algebra.AlgebraicGroup.TorusSplittingField
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Unramified.Field
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice.Torsion
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.EssentialImage
import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.CharacterLattice
import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
import TauCeti.Algebra.HopfAlgebra.GroupLike.FiniteExtension

/-!
# Existence of the splitting field of a torus

The splitting field of an algebraic torus `T` over a field `k` (LMFDB `ag.splitting_field`) is the
minimal Galois extension of `k` over which `T` becomes isomorphic to a power of `𝔾ₘ`. LeanBridge's
`TauCeti.torusSplittingField` defines it, inside an algebraic closure `k̄` of `k`, as the infimum of
the Galois extensions of `k` that split `T`, and `TauCeti.IsTorusSplittingField` says that a field
is the least of them. This file proves that the least one exists, for every torus over every field,
perfect or not: `TauCeti.isTorusSplittingField_torusSplittingField`.

The characters of `T` over `k̄` are the group-like elements of `k̄ ⊗[k] H`, where `H` is the
coordinate Hopf algebra of `T`. A subextension `E` of `k̄ / k` splits `T` exactly when every
character is defined over `E` (`TauCeti.isTorusSplitOver_iff_surjective_groupLikeScalarTowerHom`):
over a splitting field the characters do not change (Tau Ceti's `groupLikeScalarTowerEquiv`), and
conversely characters defined over `E` span `E ⊗[k] H`, which is then the group algebra of its
characters, a free abelian group of finite rank since those of `T` over `k̄` are torsion free. So
the subextensions splitting `T` are those containing the field of definition `F` of the characters
(`TauCeti.isTorusSplitOver_iff_torusCharacterField_le`), generated over `k` by their coordinates in
any `k`-basis of `H` (`TauCeti.torusCharacterField_le_iff`); it is finite over `k`
(`TauCeti.finiteDimensional_torusCharacterField`).

The field `F` is separable over `k` (`TauCeti.isSeparable_torusCharacterField`), the infinitesimal
form of the theorem that tori split over separable extensions (`Hom(T, 𝔾ₐ) = 0`). For a
`k`-derivation `D` of `F`, the automorphism `a + bε ↦ a + (D a + b)ε` of the dual numbers `F[ε]`
over `k` moves each character `χ`, defined over `F`, to a character of `T` over `F[ε]`; since `T`
is split over `F` and `F[ε]` has a connected spectrum, the characters over `F[ε]` are those over
`F`, so this one is `χ` itself, and its `ε`-part shows that `D` kills the coordinates of `χ`
(`TauCeti.rTensor_val_eq_zero_of_derivation`). Hence every `k`-derivation of `F` vanishes, the
Kähler differentials `Ω[F⁄k]` vanish, and the finite extension `F / k`, being formally unramified,
is separable. The least Galois extension of `k` containing `F` is then its normal closure in `k̄`
(`TauCeti.isTorusSplittingField_normalClosure`), which is the splitting field
(`TauCeti.torusSplittingField_eq_normalClosure`), a finite extension of `k`
(`TauCeti.finiteDimensional_torusSplittingField`).

## Main definitions

* `TauCeti.dualNumberDerivationAut`: the automorphism `a + bε ↦ a + (D a + b)ε` of `F[ε]` defined
  by a derivation `D` of `F`.
* `TauCeti.torusCharacterField`: the field of definition of the characters of a torus.

## Main results

* `TauCeti.rTensor_val_eq_zero_of_derivation`: the characters of a group split over `F` are killed
  by the derivations of `F`.
* `TauCeti.isTorusSplitOver_iff_surjective_groupLikeScalarTowerHom`: a torus splits over `E` exactly
  when all its characters are defined over `E`.
* `TauCeti.torusCharacterField_le_iff`: the field of definition of the characters does not depend
  on the basis of `H` in which their coordinates are taken.
* `TauCeti.isTorusSplitOver_iff_torusCharacterField_le`: a torus splits over `E` exactly when `E`
  contains the field of definition of its characters.
* `TauCeti.finiteDimensional_torusCharacterField`: that field is finite over `k`.
* `TauCeti.isSeparable_torusCharacterField`: that field is separable over `k`.
* `TauCeti.isTorusSplittingField_normalClosure`: its normal closure is the least Galois splitting
  field.
* `TauCeti.isTorusSplittingField_torusSplittingField` (LMFDB `ag.splitting_field`): **the splitting
  field of a torus exists**: `TauCeti.torusSplittingField` is a Galois extension of `k` splitting
  the torus, contained in every other.
* `TauCeti.torusSplittingField_eq_normalClosure`: the splitting field is the normal closure of the
  field of definition of the characters.
* `TauCeti.finiteDimensional_torusSplittingField`: the splitting field is finite over `k`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12, groups of multiplicative type split over a separable
  extension of the base field.
-/

open CategoryTheory Algebra Module TauCeti Bialgebra TensorProduct

open scoped DualNumber

namespace TauCeti

universe u

variable {k : Type u} [Field k] {F A : Type u} [Field F] [Algebra k F] [CommRing A]
  [HopfAlgebra k A] {ι : Type*} (b : Basis ι k A)
  (E : IntermediateField k (AlgebraicClosure k)) (D : Derivation k F F)
  {H : FiniteTypeCommHopfAlgCat.{u, u} k}

lemma basis_repr_map_toAlgHom (x : E ⊗[k] A) : (TensorProduct.basis (AlgebraicClosure k) b).repr
    (map (IsScalarTower.toAlgHom k E (AlgebraicClosure k)) (AlgHom.id k A) x) =
      ((TensorProduct.basis E b).repr x).mapRange (algebraMap E (AlgebraicClosure k))
        (map_zero _) := by
  induction x using TensorProduct.inductionOn with
  | tmul a c =>
    ext i
    simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Finsupp.mapRange_add (map_add _)]

lemma mem_range_map_iff_forall_basis_repr_mem (v : AlgebraicClosure k ⊗[k] A) : v ∈ Set.range
    (map (IsScalarTower.toAlgHom k E (AlgebraicClosure k)) (AlgHom.id k A)) ↔
      ∀ i, (TensorProduct.basis (AlgebraicClosure k) b).repr v i ∈ E := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨x, rfl⟩ i
    rw [basis_repr_map_toAlgHom, Finsupp.mapRange_apply]
    exact ((TensorProduct.basis E b).repr x i).2
  · let c : ι →₀ E := Finsupp.ofSupportFinite (fun i ↦ ⟨_, h i⟩) <|
      ((TensorProduct.basis (AlgebraicClosure k) b).repr v).support.finite_toSet.subset
        fun i hi ↦ Finsupp.mem_support_iff.mpr fun h₀ ↦ hi (Subtype.ext h₀)
    refine ⟨(TensorProduct.basis E b).repr.symm c,
      (TensorProduct.basis (AlgebraicClosure k) b).repr.injective ?_⟩
    rw [basis_repr_map_toAlgHom, LinearEquiv.apply_symm_apply]
    ext i
    simp [c]

/-- The automorphism `a + bε ↦ a + (D a + b)ε` of the dual numbers `F[ε]` over `k` defined by a
`k`-derivation `D` of `F`. -/
def dualNumberDerivationAut : F[ε] ≃ₐ[k] F[ε] where
  toFun x := TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr (D x.fst + x.snd)
  invFun x := TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr (x.snd - D x.fst)
  left_inv x := by
    ext <;> simp
  right_inv x := by
    ext <;> simp
  map_mul' x y := by
    ext <;> simp [mul_add, mul_comm, add_add_add_comm, add_comm]
  map_add' x y := by
    ext <;> simp [add_add_add_comm]
  commutes' c := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

lemma fst_dualNumberDerivationAut (x : F[ε]) : (dualNumberDerivationAut D x).fst = x.fst := by
  simp [dualNumberDerivationAut]

lemma snd_dualNumberDerivationAut (x : F[ε]) :
    (dualNumberDerivationAut D x).snd = D x.fst + x.snd := by
  simp [dualNumberDerivationAut]

/-- **The characters of a group split over a field `F` are killed by the derivations of `F`**: if
`F ⊗[k] A` is spanned by its group-like elements, then for every `k`-derivation `D` of `F` and every
group-like element `χ` of `F ⊗[k] A`, `(D ⊗ id) χ = 0`. The automorphism
`a + bε ↦ a + (D a + b)ε` of `F[ε]` sends the character `χ` to a character of `A` over `F[ε]`,
which comes from `F` and reduces to `χ` modulo `ε`, so it is `χ`; its `ε`-part is `(D ⊗ id) χ`. -/
lemma rTensor_val_eq_zero_of_derivation
    (hspan : Submodule.span F (Set.range (GroupLike.val (R := F) (A := F ⊗[k] A))) = ⊤)
    (χ : GroupLike F (F ⊗[k] A)) : D.toLinearMap.rTensor A χ.val = 0 := by
  have : IrreducibleSpace (PrimeSpectrum F[ε]) := by
    have hε : (Ideal.span {ε} : Ideal F[ε]).IsPrime :=
      DualNumber.isMaximal_span_singleton_eps.isPrime
    have h : nilradical F[ε] = Ideal.span {ε} :=
      le_antisymm (nilradical_le_prime _) <| Ideal.span_le.mpr <| Set.singleton_subset_iff.mpr <|
        mem_nilradical.mpr ⟨2, by rw [pow_two, DualNumber.eps_mul_eps]⟩
    rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical, h]
    exact hε
  let _ : Group (GroupLike F[ε] (F[ε] ⊗[k] A)) :=
    GroupLike.instGroup (R := F[ε]) (A := F[ε] ⊗[k] A)
  let e : GroupLike F (F ⊗[k] A) ≃* GroupLike F[ε] (F[ε] ⊗[k] A) :=
    groupLikeScalarTowerEquiv hspan
  let θ : F[ε] ≃ₐ[k] F[ε] := dualNumberDerivationAut D
  let Θ : F[ε] ⊗[k] A ≃ₐ[k] F[ε] ⊗[k] A := congr θ AlgEquiv.refl
  let fstMap : F[ε] ⊗[k] A →ₐ[k] F ⊗[k] A := map (TrivSqZeroExt.fstHom k F F) (AlgHom.id k A)
  let sndMap : F[ε] ⊗[k] A →ₗ[k] F ⊗[k] A :=
    ((TrivSqZeroExt.sndHom F F).restrictScalars k).rTensor A
  let ι₀ : F ⊗[k] A →ₐ[k] F[ε] ⊗[k] A := map (IsScalarTower.toAlgHom k F F[ε]) (AlgHom.id k A)
  have ha (x : F ⊗[k] A) : fstMap (ι₀ x) = x := by
    induction x using TensorProduct.inductionOn with
    | tmul a c => simp [ι₀, TrivSqZeroExt.algebraMap_eq_inl, fstMap]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hb (y : F[ε] ⊗[k] A) : fstMap (Θ y) = fstMap y := by
    induction y using TensorProduct.inductionOn with
    | tmul a c => simp [Θ, θ, fstMap, fst_dualNumberDerivationAut]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  have hc (x : F ⊗[k] A) : sndMap (Θ (ι₀ x)) = D.toLinearMap.rTensor A x := by
    induction x using TensorProduct.inductionOn with
    | tmul a c =>
      simp [ι₀, TrivSqZeroExt.algebraMap_eq_inl, Θ, θ, sndMap, snd_dualNumberDerivationAut]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  have hd (x : F ⊗[k] A) : sndMap (ι₀ x) = 0 := by
    induction x using TensorProduct.inductionOn with
    | tmul a c => simp [ι₀, TrivSqZeroExt.algebraMap_eq_inl, sndMap]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  have he (x : GroupLike F (F ⊗[k] A)) : (e x).val = ι₀ x.val :=
    val_groupLikeScalarTowerEquiv hspan x
  have h₁ : e.symm (θ • e χ) = χ := by
    apply GroupLike.val_injective
    rw [← ha (e.symm (θ • e χ)).val, ← he, e.apply_symm_apply, ScalarAut.val_smul,
      ScalarAut.smul_def, he]
    exact (hb _).trans (ha _)
  have h₂ : sndMap (θ • e χ).val = sndMap (e χ).val :=
    congrArg (fun z ↦ sndMap z.val) <| (e.apply_symm_apply _).symm.trans (congrArg e h₁)
  rw [ScalarAut.val_smul, ScalarAut.smul_def, he, hd] at h₂
  exact (hc _).symm.trans h₂

lemma basis_repr_rTensor_derivation (x : F ⊗[k] A) (i : ι) : (TensorProduct.basis F b).repr
    (D.toLinearMap.rTensor A x) i = D ((TensorProduct.basis F b).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul a c => simp [mul_comm]
  | add x y hx hy =>
    rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply, map_add]

lemma surjective_groupLikeScalarTowerHom_iff : Function.Surjective
    (groupLikeScalarTowerHom (k := k) (L := E) (K := AlgebraicClosure k) (A := A)) ↔
      ∀ χ : GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A), χ.val ∈ Set.range
        (map (IsScalarTower.toAlgHom k E (AlgebraicClosure k)) (AlgHom.id k A)) := by
  refine ⟨fun h χ ↦ ?_, fun h χ ↦ ?_⟩
  · rcases h χ with ⟨x, rfl⟩
    exact ⟨x.val, (val_groupLikeScalarTowerHom x).symm⟩
  · rcases h χ with ⟨x, hx⟩
    have he :
        TensorProduct.baseChangeTowerBialgEquiv k E A (AlgebraicClosure k) (1 ⊗ₜ[E] x) = χ.val :=
      (TensorProduct.baseChangeTowerBialgEquiv_one_tmul k E A (AlgebraicClosure k) x).trans hx
    have hxg : IsGroupLikeElem E x := by
      rw [← isGroupLikeElem_one_tmul_iff (K := AlgebraicClosure k),
        ← isGroupLikeElem_map_equiv
          (TensorProduct.baseChangeTowerBialgEquiv k E A (AlgebraicClosure k)), he]
      exact χ.isGroupLikeElem_val
    exact ⟨⟨x, hxg⟩, GroupLike.val_injective ((val_groupLikeScalarTowerHom _).trans hx)⟩

lemma span_range_groupLikeVal_algebraicClosure (hH : torusCommHopfAlgProperty k H) : Submodule.span
    (AlgebraicClosure k) (Set.range (GroupLike.val (R := AlgebraicClosure k)
      (A := AlgebraicClosure k ⊗[k] H.obj))) = ⊤ :=
  (Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top (R := AlgebraicClosure k)
    (C := CommHopfAlgCat.baseChange (K := AlgebraicClosure k) H.obj)).mp
      ((multiplicativeTypeCommHopfAlgProperty_iff k H).mp
        (torusCommHopfAlgProperty.multiplicativeType k H hH))

lemma span_range_groupLikeVal_of_surjective (hH : torusCommHopfAlgProperty k H)
    (hsurj : Function.Surjective
      (groupLikeScalarTowerHom (k := k) (L := E) (K := AlgebraicClosure k) (A := H.obj))) :
    Submodule.span E (Set.range (GroupLike.val (R := E) (A := E ⊗[k] H.obj))) = ⊤ := by
  let p : Submodule E (E ⊗[k] H.obj) :=
    Submodule.span E (Set.range (GroupLike.val (R := E) (A := E ⊗[k] H.obj)))
  let e : AlgebraicClosure k ⊗[E] (E ⊗[k] H.obj) ≃ₗ[AlgebraicClosure k]
      AlgebraicClosure k ⊗[k] H.obj :=
    (TensorProduct.baseChangeTowerBialgEquiv k E H.obj
      (AlgebraicClosure k)).toAlgEquiv.toLinearEquiv
  have hmap : (p.baseChange (AlgebraicClosure k)).map e.toLinearMap = ⊤ := by
    apply top_unique
    rw [← span_range_groupLikeVal_algebraicClosure hH]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    rcases hsurj g with ⟨x, rfl⟩
    refine ⟨1 ⊗ₜ[E] x.val,
      Submodule.tmul_mem_baseChange_of_mem 1 (Submodule.subset_span ⟨x, rfl⟩), ?_⟩
    rw [val_groupLikeScalarTowerHom]
    exact TensorProduct.baseChangeTowerBialgEquiv_one_tmul k E H.obj (AlgebraicClosure k) x.val
  have hp : p.baseChange (AlgebraicClosure k) = ⊤ :=
    Submodule.map_eq_top_iff.mp hmap
  apply Submodule.baseChange_injective (A := AlgebraicClosure k)
  simpa only [Submodule.baseChange_top] using hp

open torusCommHopfAlgProperty in
/-- **A torus splits over a subextension `E` of `k̄ / k` exactly when all its characters over `k̄`
are defined over `E`**: the group-like elements of `k̄ ⊗[k] H` come from `E ⊗[k] H`. -/
lemma isTorusSplitOver_iff_surjective_groupLikeScalarTowerHom (hH : torusCommHopfAlgProperty k H) :
    IsTorusSplitOver H E ↔ Function.Surjective
      (groupLikeScalarTowerHom (k := k) (L := E) (K := AlgebraicClosure k) (A := H.obj)) := by
  refine ⟨fun ⟨n, ⟨i⟩⟩ ↦ ?_, fun hsurj ↦ ?_⟩
  · have hsp : Subcoalgebra.groupLikeSetSpan (R := E) (C := E ⊗[k] H.obj) Set.univ = ⊤ :=
      (DiagonalizableGroup.groupLikeSpannedProperty E).prop_of_iso i
        (MonoidAlgebra.groupLikeSetSpan_eq_top E _)
    have hspan : Submodule.span E (Set.range (GroupLike.val (R := E) (A := E ⊗[k] H.obj))) = ⊤ :=
      Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top.mp hsp
    intro χ
    refine ⟨(groupLikeScalarTowerEquiv hspan).symm χ, GroupLike.val_injective ?_⟩
    rw [val_groupLikeScalarTowerHom, ← val_groupLikeScalarTowerEquiv hspan,
      MulEquiv.apply_symm_apply]
  · have hspan : Submodule.span E (Set.range (GroupLike.val (R := E) (A := E ⊗[k] H.obj))) = ⊤ :=
      span_range_groupLikeVal_of_surjective E hH hsurj
    have hsp : Subcoalgebra.groupLikeSetSpan (R := E) (C := E ⊗[k] H.obj) Set.univ = ⊤ :=
      Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top.mpr hspan
    rcases (iff_multiplicativeType_and_geometricallyConnected_and_geometricallyReduced k H).mp hH
      with ⟨-, hconn, hred⟩
    have : IsMulTorsionFree (GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] H.obj)) :=
      CommHopfAlgCat.isMulTorsionFree_geometricCharacterGroup H.obj hred hconn
    let _ : CommGroup (GroupLike E (E ⊗[k] H.obj)) :=
      GroupLike.instCommGroup (R := E) (A := E ⊗[k] H.obj)
    let f : GroupLike E (E ⊗[k] H.obj) →*
        GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] H.obj) :=
      MonoidHom.mk' (groupLikeScalarTowerEquiv hspan) (groupLikeScalarTowerEquiv hspan).map_mul
    have : IsMulTorsionFree (GroupLike E (E ⊗[k] H.obj)) :=
      (groupLikeScalarTowerEquiv hspan).injective.isMulTorsionFree f
    have : Group.FG (GroupLike E (E ⊗[k] H.obj)) :=
      GroupLike.fg_of_finiteType_of_groupLikeSetSpan_eq_top E (E ⊗[k] H.obj) inferInstance hsp
    exact (splitTorusCommHopfAlgProperty E).prop_of_iso
      (ObjectProperty.isoMk _
        (CommHopfAlgCat.isoMk (GroupLike.evaluationBialgEquiv E (E ⊗[k] H.obj) hspan)))
      (splitTorusCommHopfAlgProperty_coordinateRing E
        (FGCommGrpCat.of (GroupLike E (E ⊗[k] H.obj))))

variable (H) in
/-- The **field of definition of the characters** of an affine group `T` over `k` with coordinate
Hopf algebra `H`: the subfield of `k̄` generated over `k` by the coordinates, in a `k`-basis of `H`,
of the characters of `T` over `k̄`, the group-like elements of `k̄ ⊗[k] H`. Every `k`-basis of `H`
gives the same field (`TauCeti.torusCharacterField_le_iff`). For a torus, a subfield `E` of `k̄`
contains it exactly when every character of `T` over `k̄` is defined over `E`, that is when `T`
splits over `E` (`TauCeti.isTorusSplitOver_iff_torusCharacterField_le`). -/
noncomputable def torusCharacterField : IntermediateField k (AlgebraicClosure k) :=
  IntermediateField.adjoin k (⋃ χ : GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] H.obj),
    Set.range ((TensorProduct.basis (AlgebraicClosure k)
      (Free.chooseBasis k H.obj)).repr χ.val))

/-- **The field of definition of the characters does not depend on the basis**: for every `k`-basis
`c` of `H`, it lies in a subextension `E` of `k̄ / k` exactly when `E` contains the coordinates in
`c` of all the characters over `k̄`, so it is the subfield generated by these coordinates. -/
lemma torusCharacterField_le_iff (c : Basis ι k H.obj) : torusCharacterField H ≤ E ↔
    ∀ (χ : GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] H.obj)) (i : ι),
      (TensorProduct.basis (AlgebraicClosure k) c).repr χ.val i ∈ E := by
  rw [torusCharacterField, IntermediateField.adjoin_le_iff, Set.iUnion_subset_iff]
  simp only [Set.range_subset_iff, SetLike.mem_coe,
    ← mem_range_map_iff_forall_basis_repr_mem (Free.chooseBasis k H.obj),
    mem_range_map_iff_forall_basis_repr_mem c]

/-- **A torus splits over a subextension `E` of `k̄ / k` exactly when `E` contains the field of
definition of its characters.** -/
lemma isTorusSplitOver_iff_torusCharacterField_le (hH : torusCommHopfAlgProperty k H) :
    IsTorusSplitOver H E ↔ torusCharacterField H ≤ E := by
  rw [isTorusSplitOver_iff_surjective_groupLikeScalarTowerHom E hH,
    surjective_groupLikeScalarTowerHom_iff, torusCharacterField, IntermediateField.adjoin_le_iff,
    Set.iUnion_subset_iff]
  simp only [mem_range_map_iff_forall_basis_repr_mem (Free.chooseBasis k H.obj),
    Set.range_subset_iff, SetLike.mem_coe]

/-- **The field of definition of the characters of a torus is finite over `k`.** -/
lemma finiteDimensional_torusCharacterField (hH : torusCommHopfAlgProperty k H) :
    FiniteDimensional k (torusCharacterField H) := by
  have : Group.FG (GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] H.obj)) :=
    CommHopfAlgCat.geometricCharacterGroup_fg_of_multiplicativeType H
      (torusCommHopfAlgProperty.multiplicativeType k H hH)
  rcases exists_finiteDimensional_surjective_groupLikeScalarTowerHom (k := k)
    (K := AlgebraicClosure k) (A := H.obj) with ⟨L, hL, hsurj⟩
  have hle : torusCharacterField H ≤ L := (isTorusSplitOver_iff_torusCharacterField_le L hH).mp
    ((isTorusSplitOver_iff_surjective_groupLikeScalarTowerHom L hH).mpr hsurj)
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion hle).toRingHom.injective

/-- **The field of definition of the characters of a torus is separable over `k`**: every
`k`-derivation of it kills the coordinates of the characters, which generate it, so its Kähler
differentials over `k` vanish and it is formally unramified, hence separable, over `k`. -/
lemma isSeparable_torusCharacterField (hH : torusCommHopfAlgProperty k H) :
    Algebra.IsSeparable k (torusCharacterField H) := by
  have : FiniteDimensional k (torusCharacterField H) := finiteDimensional_torusCharacterField hH
  have hsurj : Function.Surjective (groupLikeScalarTowerHom (k := k) (L := torusCharacterField H)
      (K := AlgebraicClosure k) (A := H.obj)) :=
    (isTorusSplitOver_iff_surjective_groupLikeScalarTowerHom _ hH).mp
      ((isTorusSplitOver_iff_torusCharacterField_le _ hH).mpr le_rfl)
  have hspan : Submodule.span (torusCharacterField H) (Set.range (GroupLike.val
      (R := torusCharacterField H) (A := torusCharacterField H ⊗[k] H.obj))) = ⊤ :=
    span_range_groupLikeVal_of_surjective _ hH hsurj
  have hδ (δ : Derivation k (torusCharacterField H) (torusCharacterField H))
      (x : torusCharacterField H) : δ x = 0 := by
    rcases x with ⟨x, hx⟩
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      rcases Set.mem_iUnion.mp hx with ⟨χ, i, rfl⟩
      rcases hsurj χ with ⟨ψ, rfl⟩
      let bH : Basis (Free.ChooseBasisIndex k H.obj) k H.obj := Free.chooseBasis k H.obj
      have h : δ ((TensorProduct.basis (torusCharacterField H) bH).repr ψ.val i) = 0 := by
        rw [← basis_repr_rTensor_derivation, rTensor_val_eq_zero_of_derivation δ hspan, map_zero,
          Finsupp.zero_apply]
      have hx' : (TensorProduct.basis (AlgebraicClosure k) bH).repr
          (groupLikeScalarTowerHom ψ).val i =
            (TensorProduct.basis (torusCharacterField H) bH).repr ψ.val i := by
        rw [val_groupLikeScalarTowerHom, basis_repr_map_toAlgHom, Finsupp.mapRange_apply]
        rfl
      exact (congrArg δ (Subtype.ext hx')).trans h
    | algebraMap c => exact δ.map_algebraMap c
    | add x y hx hy hx' hy' => exact (δ.map_add ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [hx', hy', add_zero])
    | inv x hx hx' => exact (δ.leibniz_inv ⟨x, hx⟩).trans (by rw [hx', smul_zero])
    | mul x y hx hy hx' hy' =>
      exact (δ.leibniz ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [hx', hy', smul_zero, smul_zero, add_zero])
  have : Subsingleton Ω[torusCharacterField H⁄k] := by
    have hd (x : torusCharacterField H) : KaehlerDifferential.D k (torusCharacterField H) x = 0 :=
      (Module.forall_dual_apply_eq_zero_iff (torusCharacterField H) _).mp fun φ ↦
        hδ (φ.compDer (KaehlerDifferential.D k (torusCharacterField H))) x
    refine subsingleton_of_forall_eq 0 fun ω ↦ ?_
    have hω : ω ∈ Submodule.span (torusCharacterField H)
        (Set.range (KaehlerDifferential.D k (torusCharacterField H))) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hω using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨y, rfl⟩
      exact hd y
    | zero => rfl
    | add x y _ _ hx hy => rw [hx, hy, add_zero]
    | smul a x _ hx => rw [hx, smul_zero]
  have : Algebra.FormallyUnramified k (torusCharacterField H) := ⟨this⟩
  exact FormallyUnramified.isSeparable k _

/-- **The normal closure of the field of definition of the characters of a torus is the least
Galois extension of `k` splitting the torus**: it is Galois since that field is separable, it splits
the torus since it contains that field, and a Galois extension splitting the torus contains that
field, hence its normal closure. -/
lemma isTorusSplittingField_normalClosure (hH : torusCommHopfAlgProperty k H) :
    IsTorusSplittingField H
      (IntermediateField.normalClosure k (torusCharacterField H) (AlgebraicClosure k)) := by
  have : Algebra.IsSeparable k (torusCharacterField H) := isSeparable_torusCharacterField hH
  refine ⟨⟨inferInstance, (isTorusSplitOver_iff_torusCharacterField_le _ hH).mpr
    (IntermediateField.le_normalClosure _)⟩, fun E' ⟨hE', hsplit⟩ ↦ ?_⟩
  have : Normal k E' := hE'.to_normal
  exact IntermediateField.normalClosure_le_iff_of_normal.mpr
    ((isTorusSplitOver_iff_torusCharacterField_le E' hH).mp hsplit)

/-- **The splitting field of a torus is the normal closure of the field of definition of its
characters.** -/
lemma torusSplittingField_eq_normalClosure (hH : torusCommHopfAlgProperty k H) :
    torusSplittingField H =
      IntermediateField.normalClosure k (torusCharacterField H) (AlgebraicClosure k) :=
  (isTorusSplittingField_normalClosure hH).torusSplittingField_eq

/-- **The splitting field of a torus exists** (LMFDB `ag.splitting_field`): for a torus `T` over a
field `k`, perfect or not, `TauCeti.torusSplittingField` is a Galois extension of `k` inside `k̄`
over which `T` becomes isomorphic to a power of `𝔾ₘ`, contained in every other such extension. -/
lemma isTorusSplittingField_torusSplittingField (hH : torusCommHopfAlgProperty k H) :
    IsTorusSplittingField H (torusSplittingField H) :=
  torusSplittingField_eq_normalClosure hH ▸ isTorusSplittingField_normalClosure hH

/-- **The splitting field of a torus is finite over `k`.** -/
lemma finiteDimensional_torusSplittingField (hH : torusCommHopfAlgProperty k H) :
    FiniteDimensional k (torusSplittingField H) := by
  have : FiniteDimensional k (torusCharacterField H) := finiteDimensional_torusCharacterField hH
  rw [torusSplittingField_eq_normalClosure hH]
  infer_instance

end TauCeti
