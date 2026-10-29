import LeanBridge.ForMathlib.GroupTheory.Perm.CentralizerTransitive
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Closure
import TauCeti.FieldTheory.Galois.FixedField

/-!
# Automorphisms of the stem field of a transitive Galois group

Let `L/K` be a finite Galois extension whose Galois group acts transitively on a set `X`, with image
a transitive permutation group `G ≤ Sym(X)`; for the LMFDB, `X = {1, …, n}` and `G ≤ S_n` is a
transitive group realised as `Gal(L/K)`, and every group of permutations of a finite set is so
realised, by its action on the field `ℚ(x_1, …, x_n)` of rational functions over its fixed field.
Let `F = L^{G₁}` be the fixed field of the stabilizer `G₁` of a point `x`. Then `F/K` has degree
`n = |X|` and, when the action is faithful, Galois closure `L/K`. By the Galois correspondence, the
automorphism group `Aut(F/K)` is `N(G₁)/G₁`, and by the group theory of transitive actions this has
the order of the centralizer of `G` in `Sym(X)`; so `#Aut(F/K)` depends only on the permutation
group `G`. If `F = K[x]/(f)`, then `#Aut(F/K)` is the number of roots of `f` in `F`.

## Main definitions

* `IsGalois.restrictNormalizer`: the restriction of the normalizer of a subgroup `H` of `Gal(L/K)`
  to the fixed field `L^H`.
* `IsGalois.normalizerQuotientEquivAut` (LMFDB `gg.field_automorphisms`): the isomorphism
  `N(H)/H ≃ Aut(L^H/K)` of the Galois correspondence.

## Main results

* `IsGalois.finrank_fixedField_stabilizer`: `[F : K] = |X|`.
* `IsGalois.normalClosure_fixedField_stabilizer`: for a faithful action, the normal closure of
  `F/K` in `L` is `L`.
* `IsGalois.card_aut_fixedField_stabilizer`: `#Aut(F/K)` is the order of the centralizer of `G` in
  `Sym(X)`.
* `Subgroup.exists_isGalois_range_eq`: every group of permutations of a finite set is the image of
  an injective homomorphism `Gal(L/K) → Sym(X)` for a finite Galois extension `L/K`.
* `AdjoinRoot.card_aut_eq_card_rootSet`: `#Aut(K[x]/(f) / K)` is the number of roots of `f` in
  `K[x]/(f)`, for an irreducible `f`.
-/

universe u

open IntermediateField MulAction Subgroup

open scoped Polynomial

namespace IsGalois

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (H : Subgroup Gal(L/K)) {σ : Gal(L/K)}

lemma map_fixedField_eq (hσ : σ ∈ normalizer H) :
    (fixedField H).map (σ : L →ₐ[K] L) = fixedField H :=
  (H.fixedField_map_conj σ).symm.trans <| congrArg fixedField <|
    mem_normalizer_iff_map_conj_eq.mp hσ

/-- The restriction to the fixed field `L^H` of the elements of the normalizer of a subgroup `H` of
`Gal(L/K)`, which map `L^H` onto itself. -/
noncomputable def restrictNormalizer : normalizer (H : Set Gal(L/K)) →* Gal(fixedField H/K) where
  toFun σ := ((fixedField H).equivMap (σ : L →ₐ[K] L)).trans (equivOfEq (map_fixedField_eq H σ.2))
  map_one' := by
    ext
    rfl
  map_mul' σ τ := by
    ext
    rfl

lemma coe_restrictNormalizer_apply (n : normalizer (H : Set Gal(L/K))) (a : fixedField H) :
    (restrictNormalizer H n a : L) = (n : Gal(L/K)) a :=
  rfl

variable [FiniteDimensional K L]

lemma mem_iff_forall_mem_fixedField {g : Gal(L/K)} : g ∈ H ↔ ∀ x ∈ fixedField H, g x = x :=
  (SetLike.ext_iff.mp (fixingSubgroup_fixedField H) g).symm.trans
    (IntermediateField.mem_fixingSubgroup_iff _ g)

lemma ker_restrictNormalizer : (restrictNormalizer H).ker = H.subgroupOf (normalizer H) := by
  ext σ
  rw [MonoidHom.mem_ker, mem_subgroupOf, mem_iff_forall_mem_fixedField, AlgEquiv.ext_iff]
  exact ⟨fun h a ha ↦ congrArg Subtype.val (h ⟨a, ha⟩), fun h a ↦ Subtype.ext (h a a.2)⟩

variable [IsGalois K L]

lemma restrictNormalizer_surjective : Function.Surjective (restrictNormalizer H) := by
  intro τ
  have hτ (a : fixedField H) : τ.liftNormal L a = τ a := τ.liftNormal_commutes L a
  refine ⟨⟨τ.liftNormal L, mem_normalizer_fintype fun h hh ↦ ?_⟩,
    AlgEquiv.ext fun a ↦ Subtype.ext (hτ a)⟩
  refine (mem_iff_forall_mem_fixedField H).mpr fun a ha ↦ ?_
  have h₁ : (τ.liftNormal L).symm a = τ.symm ⟨a, ha⟩ := by
    rw [AlgEquiv.symm_apply_eq, hτ, AlgEquiv.apply_symm_apply]
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, h₁,
    (mem_fixedField_iff H _).mp (τ.symm ⟨a, ha⟩).2 h hh, hτ, AlgEquiv.apply_symm_apply]

/-- **The automorphisms of a fixed field** (LMFDB `gg.field_automorphisms`): for a subgroup `H` of
the Galois group of a finite Galois extension `L/K`, restriction identifies `N(H)/H` with the group
`Aut(L^H/K)` of automorphisms of the fixed field `L^H` over `K`: this is how the Galois
correspondence computes `Aut(L^H/K)` when `L^H/K` is not Galois. -/
noncomputable def normalizerQuotientEquivAut :
    normalizer (H : Set Gal(L/K)) ⧸ H.subgroupOf (normalizer H) ≃* Gal(fixedField H/K) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_restrictNormalizer H).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (restrictNormalizer_surjective H))

variable {X : Type*} [MulAction Gal(L/K) X] [IsPretransitive Gal(L/K) X] (x : X)

/-- **The stem field of a transitive Galois group of degree `n` has degree `n`** (LMFDB
`gg.field_automorphisms`): the fixed field of the stabilizer of a point of `X` has degree `|X|`. -/
lemma finrank_fixedField_stabilizer :
    Module.finrank K (fixedField (stabilizer Gal(L/K) x)) = Nat.card X := by
  rw [finrank_eq_fixingSubgroup_index, fixingSubgroup_fixedField, index_stabilizer_of_transitive]

/-- **The automorphisms of the stem field of a transitive Galois group** (LMFDB
`gg.field_automorphisms`): if `Gal(L/K)` acts transitively on `X`, with image `G` in `Sym(X)`, the
fixed field `F` of the stabilizer of a point has as many automorphisms over `K` as the centralizer
of `G` in `Sym(X)` has elements. So `#Aut(F/K)` is an invariant of the permutation group `G`. -/
lemma card_aut_fixedField_stabilizer : Nat.card Gal(fixedField (stabilizer Gal(L/K) x)/K) =
    Nat.card (centralizer ((toPermHom Gal(L/K) X).range : Set (Equiv.Perm X))) := by
  rw [card_centralizer_eq_relIndex x, ← Nat.card_congr (normalizerQuotientEquivAut _).toEquiv]
  rfl

/-- **The Galois closure of the stem field of a faithful transitive Galois group is `L`** (LMFDB
`gg.field_automorphisms`): the normal closure in `L` of the fixed field of the stabilizer of a point
is `L`, since the elements of `Gal(L/K)` fixing it fix every point of `X`. -/
lemma normalClosure_fixedField_stabilizer [FaithfulSMul Gal(L/K) X] :
    IntermediateField.normalClosure K (fixedField (stabilizer Gal(L/K) x)) L = ⊤ := by
  rw [← fixedField_fixingSubgroup (IntermediateField.normalClosure K _ L), ← fixedField_bot]
  congr 1
  refine eq_bot_iff.mpr fun g hg ↦ mem_bot.mpr <| eq_of_smul_eq_smul fun (y : X) ↦ ?_
  rcases exists_smul_eq Gal(L/K) x y with ⟨k, rfl⟩
  have hk : k⁻¹ * g * k ∈ stabilizer Gal(L/K) x :=
    fixingSubgroup_fixedField (stabilizer Gal(L/K) x) ▸
      fixingSubgroup_le (le_normalClosure _) (Normal.conj_mem' inferInstance g hg k)
  rw [mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff] at hk
  rw [hk, one_smul]

end IsGalois

/-- **Every group of permutations of a finite set is a Galois group** (LMFDB
`gg.field_automorphisms`): for a subgroup `G` of `Sym(X)`, `X` finite, there are a finite Galois
extension `L/K` and an injective homomorphism `Gal(L/K) → Sym(X)` with image `G`. Here `L` is the
field `ℚ(x_i : i ∈ X)` of rational functions, on which `G` acts by permuting the variables, and
`K = L^G` (Artin's theorem). So every transitive `G` is realised as in
`IsGalois.card_aut_fixedField_stabilizer`. -/
lemma Subgroup.exists_isGalois_range_eq {X : Type u} [Finite X] (G : Subgroup (Equiv.Perm X)) :
    ∃ (K L : Type u) (_ : Field K) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : IsGalois K L) (ρ : Gal(L/K) →* Equiv.Perm X), Function.Injective ρ ∧ ρ.range = G := by
  let ρ₀ : Equiv.Perm X →* MvPolynomial X ℚ ≃ₐ[ℚ] MvPolynomial X ℚ :=
    { toFun := MvPolynomial.renameEquiv ℚ
      map_one' := MvPolynomial.renameEquiv_refl ℚ
      map_mul' := fun σ τ ↦ (MvPolynomial.renameEquiv_trans ℚ τ σ).symm }
  let _ : MulSemiringAction G (MvPolynomial X ℚ) := MulSemiringAction.compHom _ (ρ₀.comp G.subtype)
  have hsmul (g : G) (p : MvPolynomial X ℚ) : g • p = MvPolynomial.rename (g : Equiv.Perm X) p :=
    rfl
  have _ : FaithfulSMul G (MvPolynomial X ℚ) := ⟨fun h ↦ Subtype.ext <| Equiv.ext fun i ↦ by
    simpa [hsmul] using h (MvPolynomial.X i)⟩
  let _ : MulSemiringAction G (FractionRing (MvPolynomial X ℚ)) :=
    IsFractionRing.mulSemiringAction G (MvPolynomial X ℚ) (FractionRing (MvPolynomial X ℚ))
  have _ : FaithfulSMul G (FractionRing (MvPolynomial X ℚ)) :=
    IsFractionRing.faithfulSMul G (MvPolynomial X ℚ) (FractionRing (MvPolynomial X ℚ))
  refine ⟨FixedPoints.subfield G (FractionRing (MvPolynomial X ℚ)), FractionRing (MvPolynomial X ℚ),
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    G.subtype.comp (FixedPoints.toAlgAutMulEquiv G _).symm.toMonoidHom, ?_, ?_⟩
  · exact G.subtype_injective.comp (FixedPoints.toAlgAutMulEquiv G _).symm.injective
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _
      (FixedPoints.toAlgAutMulEquiv G _).symm.surjective, map_top, range_subtype]

/-- **The automorphisms of `K[x]/(f)` are counted by the roots of `f`** (LMFDB
`gg.field_automorphisms`): for an irreducible `f`, the number of automorphisms of `F = K[x]/(f)`
over `K` is the number of roots of `f` in `F`. -/
lemma AdjoinRoot.card_aut_eq_card_rootSet {K : Type*} [Field K] (f : K[X]) [Fact (Irreducible f)] :
    Nat.card (AdjoinRoot f ≃ₐ[K] AdjoinRoot f) = Nat.card (f.rootSet (AdjoinRoot f)) := by
  have hf : f ≠ 0 := (Fact.out : Irreducible f).ne_zero
  have : FiniteDimensional K (AdjoinRoot f) := (powerBasis hf).finite
  classical
  rw [Nat.card_congr (algEquivEquivAlgHom K (AdjoinRoot f)).toEquiv,
    Nat.card_congr (AdjoinRoot.equiv (AdjoinRoot f) K f hf), Polynomial.rootSet_def]
  exact Nat.card_congr <| Equiv.subtypeEquivRight fun _ ↦ by simp
