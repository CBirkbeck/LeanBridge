import Mathlib

open NumberField InfinitePlace Units Polynomial

macro "polynomial_simp" : tactic =>
  `(tactic| simp only [map_C, map_X, Polynomial.map_zero, Polynomial.map_one, Polynomial.map_neg,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    eval_C, eval_X, eval_zero, eval_one, eval_neg, eval_add, eval_sub, eval_mul, eval_pow,
    eval₂_C, eval₂_X, eval₂_zero, eval₂_one, eval₂_neg, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

lemma Set.univ_eq_two {X : Type*} {a b : X} (_ : a ≠ b) (f : X ≃ Fin 2) :
    (Set.univ : Set X) = {a, b} := by
  classical
  have : Fintype X := Fintype.ofEquiv _ f.symm
  refine (Set.eq_of_subset_of_card_le (Set.subset_univ _) ?_).symm
  rw [Fintype.card_setUniv, Fintype.card_congr f]
  aesop

def Set.equiv_fin_two {X : Type*} [DecidableEq X] {a b : X} (_ : a ≠ b) :
    ({a, b} : Set X) ≃ Fin 2 where
  toFun x := if x = a then 0 else 1
  invFun x := if x = 0 then ⟨a, by aesop⟩ else ⟨b, by aesop⟩
  left_inv _ := by aesop
  right_inv x := by fin_cases x <;> aesop

noncomputable section

namespace K_2_2_5_1

def minPolyℤ : Polynomial ℤ :=
  (1) * X ^ 2 + (-1) * X + (-1)

def minPoly : Polynomial ℚ :=
  minPolyℤ.map <| algebraMap ℤ ℚ

abbrev K := AdjoinRoot minPoly

lemma monic_minPolyℤ : minPolyℤ.Monic := by
  rw [minPolyℤ]
  ring_nf
  monicity!
  exact Polynomial.coeff_one

lemma monic_minPoly : minPoly.Monic :=
  monic_minPolyℤ.map _

lemma minPolyℤ_ne_zero : minPolyℤ ≠ 0 :=
  monic_minPolyℤ.ne_zero

lemma minPoly_ne_zero : minPoly ≠ 0 :=
  monic_minPoly.ne_zero

lemma irreducible_minPoly : Irreducible minPoly := by
  sorry -- tactic_dev

lemma irreducible_minPolyℤ : Irreducible minPolyℤ :=
  monic_minPolyℤ.irreducible_of_irreducible_map _ _ irreducible_minPoly

instance: Fact (Irreducible minPoly) :=
  ⟨irreducible_minPoly⟩

axiom discr : NumberField.discr K = 5

axiom isGalois : IsGalois ℚ K

axiom classNumber : NumberField.classNumber K = 1

def root1 : ℝ :=
  (1 + Real.sqrt 5) / 2

def root2 : ℝ :=
  (1 - Real.sqrt 5) / 2

-- tactic?
lemma minPolyℝ_eq : minPoly.map (algebraMap ℚ ℝ) = (X - C root1) * (X - C root2) := by
  rw [minPoly, minPolyℤ]
  have coeff0 : C root1 * C root2 = -1 := by
    rw [← C_mul, ← C_1, ← C_neg]
    congr 1
    sorry
  have coeff1 : C root1 + C root2 = 1 := by
    rw [← C_add, ← C_1]
    congr 1
    sorry
  linear_combination (norm := (polynomial_simp; ring1)) X * coeff1 - coeff0

-- tactic?
lemma root1_ne_root2' : root1 ≠ root2 := by
  sorry

variable (A : Type*) [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra ℝ A] [IsScalarTower ℚ ℝ A]

omit [IsDomain A] in
lemma minPoly_eq : minPoly.map (algebraMap ℚ A) =
    (X - C (algebraMap ℝ A root1)) * (X - C (algebraMap ℝ A root2)) := by
  rw [IsScalarTower.algebraMap_eq ℚ ℝ A, ← Polynomial.map_map, minPolyℝ_eq]
  polynomial_simp

lemma mem_roots (x : A) :
    x ∈ minPoly.aroots A ↔ x = algebraMap ℝ A root1 ∨ x = algebraMap ℝ A root2 := by
  have := X_sub_C_ne_zero <| algebraMap ℝ A root1
  have := X_sub_C_ne_zero <| algebraMap ℝ A root2
  simp_rw [aroots, minPoly_eq, mem_roots', root_mul, root_X_sub_C]
  aesop

lemma roots1_mem_roots : algebraMap ℝ A root1 ∈ minPoly.aroots A :=
  (mem_roots ..).mpr <| Or.inl rfl

lemma roots2_mem_roots : algebraMap ℝ A root2 ∈ minPoly.aroots A :=
  (mem_roots ..).mpr <| Or.inr rfl

omit [Algebra ℚ A] in
lemma root1_ne_root2 : algebraMap ℝ A root1 ≠ algebraMap ℝ A root2 := by
  simpa only [ne_eq, algebraMap.coe_inj] using root1_ne_root2'

lemma roots_eq : {x : A | x ∈ minPoly.aroots A} = {algebraMap ℝ A root1, algebraMap ℝ A root2} :=
  Set.ext <| mem_roots A

def roots_equiv [DecidableEq A] : {x : A // x ∈ minPoly.aroots A} ≃ Fin 2 :=
  (Equiv.setCongr <| roots_eq A).trans <| Set.equiv_fin_two <| root1_ne_root2 A

def embedding1 : K →ₐ[ℚ] A :=
  (Algebra.algHom ..).comp <|
    AdjoinRoot.liftHom _ _ (mem_aroots.mp <| roots1_mem_roots ℝ).right

def embedding2 : K →ₐ[ℚ] A :=
  (Algebra.algHom ..).comp <|
    AdjoinRoot.liftHom _ _ (mem_aroots.mp <| roots2_mem_roots ℝ).right

omit [IsDomain A] in
@[simp]
lemma embedding1_root : embedding1 A (AdjoinRoot.root minPoly) = algebraMap ℝ A root1 := by
  rw [embedding1, AlgHom.coe_comp, Function.comp_apply, AdjoinRoot.liftHom_root]
  rfl

omit [IsDomain A] in
@[simp]
lemma embedding2_root : embedding2 A (AdjoinRoot.root minPoly) = algebraMap ℝ A root2 := by
  rw [embedding2, AlgHom.coe_comp, Function.comp_apply, AdjoinRoot.liftHom_root]
  rfl

lemma embedding1_isReal : ComplexEmbedding.IsReal (embedding1 ℂ).toRingHom := by
  rw [embedding1, Algebra.algHom, ComplexEmbedding.isReal_iff]
  ext
  simp

lemma embedding2_isReal : ComplexEmbedding.IsReal (embedding2 ℂ).toRingHom := by
  rw [embedding2, Algebra.algHom, ComplexEmbedding.isReal_iff]
  ext
  simp

lemma embedding1_ne_embedding2 : embedding1 A ≠ embedding2 A := by
  rw [ne_eq, AlgHom.ext_iff, not_forall]
  use AdjoinRoot.root minPoly
  rw [embedding1_root, embedding2_root]
  exact root1_ne_root2 A

lemma embeddings_eq [DecidableEq A] :
    (Set.univ : Set <| K →ₐ[ℚ] A) = {embedding1 A, embedding2 A} :=
  Set.univ_eq_two (embedding1_ne_embedding2 A) <| (AdjoinRoot.equiv _ _ _ minPoly_ne_zero).trans <|
    roots_equiv A

def embeddings_equiv [DecidableEq A] [DecidableEq <| K →ₐ[ℚ] A] : (K →ₐ[ℚ] A) ≃ Fin 2 :=
  (Equiv.Set.univ _).symm.trans <| (Equiv.setCongr <| embeddings_eq A).trans <| Set.equiv_fin_two <|
    embedding1_ne_embedding2 A

def realEmbedding1 : {φ : K →+* ℂ // ComplexEmbedding.IsReal φ} :=
  ⟨embedding1 ℂ, embedding1_isReal⟩

def realEmbedding2 : {φ : K →+* ℂ // ComplexEmbedding.IsReal φ} :=
  ⟨embedding2 ℂ, embedding2_isReal⟩

omit [IsDomain A] in
@[simp]
lemma realEmbedding1_root : realEmbedding1.val (AdjoinRoot.root minPoly) = root1 := by
  rw [realEmbedding1, RingHom.coe_coe, embedding1_root, Complex.coe_algebraMap]

omit [IsDomain A] in
@[simp]
lemma realEmbedding2_root : realEmbedding2.val (AdjoinRoot.root minPoly) = root2 := by
  rw [realEmbedding2, RingHom.coe_coe, embedding2_root, Complex.coe_algebraMap]

lemma realEmbedding1_ne_realEmbedding2 : realEmbedding1 ≠ realEmbedding2 := by
  rw [realEmbedding1, realEmbedding2, ne_eq, Subtype.mk.injEq]
  exact fun h ↦ embedding1_ne_embedding2 ℂ <| AlgHom.coe_ringHom_injective h

lemma realEmbeddings_eq [DecidableEq <| K →ₐ[ℚ] ℝ] :
    (Set.univ : Set {φ : K →+* ℂ // ComplexEmbedding.IsReal φ}) =
      {realEmbedding1, realEmbedding2} :=
  Set.univ_eq_two realEmbedding1_ne_realEmbedding2 <|
    (sorry : {φ : K →+* ℂ // ComplexEmbedding.IsReal φ} ≃ (K →ₐ[ℚ] ℝ)).trans <| embeddings_equiv ℝ

def realEmbeddings_equiv [DecidableEq <| K →ₐ[ℚ] ℝ]
    [DecidableEq {φ : K →+* ℂ // ComplexEmbedding.IsReal φ}] :
    {φ : K →+* ℂ // ComplexEmbedding.IsReal φ} ≃ Fin 2 :=
  (Equiv.Set.univ _).symm.trans <| (Equiv.setCongr realEmbeddings_eq).trans <|
    Set.equiv_fin_two realEmbedding1_ne_realEmbedding2

def realPlace1 : {v : InfinitePlace K // v.IsReal} :=
  mkReal realEmbedding1

def realPlace2 : {v : InfinitePlace K // v.IsReal} :=
  mkReal realEmbedding2

lemma realPlace1_ne_realPlace2 : realPlace1 ≠ realPlace2 := by
  rw [realPlace1, realPlace2, ne_eq, EmbeddingLike.apply_eq_iff_eq]
  exact realEmbedding1_ne_realEmbedding2

lemma realPlaces_eq [DecidableEq <| K →ₐ[ℚ] ℝ]
    [DecidableEq {φ : K →+* ℂ // ComplexEmbedding.IsReal φ}] :
    (Set.univ : Set {v : InfinitePlace K // v.IsReal}) = {realPlace1, realPlace2} :=
  Set.univ_eq_two realPlace1_ne_realPlace2 <| mkReal.symm.trans realEmbeddings_equiv

def realPlaces_equiv [DecidableEq <| K →ₐ[ℚ] ℝ]
    [DecidableEq {φ : K →+* ℂ // ComplexEmbedding.IsReal φ}]
    [DecidableEq {v : InfinitePlace K // v.IsReal}] : {v : InfinitePlace K // v.IsReal} ≃ Fin 2 :=
  (Equiv.Set.univ _).symm.trans <| (Equiv.setCongr realPlaces_eq).trans <|
    Set.equiv_fin_two realPlace1_ne_realPlace2

def realPlaces_equiv' : {w : InfinitePlace K // w ≠ realPlace1} ≃ Fin (rank K) :=
  sorry

abbrev x : 𝓞 K :=
  ⟨AdjoinRoot.root minPoly, minPolyℤ, monic_minPolyℤ,
    by simpa [minPoly, minPolyℤ] using AdjoinRoot.eval₂_root minPoly⟩

lemma x_poly : x ^ 2 - x - 1 = 0 :=
  RingOfIntegers.coe_injective <| by simpa [minPoly, minPolyℤ] using AdjoinRoot.eval₂_root minPoly

abbrev fundUnit1 : (𝓞 K)ˣ :=
  ⟨x, x - 1, by linear_combination x_poly, by linear_combination x_poly⟩

def fundSystem : Fin (rank K) → (𝓞 K)ˣ :=
  fun _ ↦ fundUnit1

lemma fundSystem_eq : Units.fundSystem K = fundSystem := by
  sorry

lemma regulator_mem : NumberField.Units.regulator K ∈ Set.Ioo 0.48 0.49 := by
  sorry

end K_2_2_5_1

end
