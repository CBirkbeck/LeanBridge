import Mathlib

open NumberField InfinitePlace Units Polynomial

universe u

macro "polynomial_simp" : tactic =>
  `(tactic| simp only [map_C, map_X, Polynomial.map_zero, Polynomial.map_one, Polynomial.map_neg,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    eval_C, eval_X, eval_zero, eval_one, eval_neg, eval_add, eval_sub, eval_mul, eval_pow,
    eval₂_C, eval₂_X, eval₂_zero, eval₂_one, eval₂_neg, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

private lemma eq_or_eq_of_surjective {X Y : Type u} {f : X → Y} (hf : f.Surjective) {a b : X}
    (hX : ∀ x : X, x = a ∨ x = b) {c d : Y} (hY : c ≠ d) (y : Y) : y = c ∨ y = d := by
  rcases hf y, hf c, hf d with ⟨⟨y', rfl⟩, ⟨c', rfl⟩, ⟨d', rfl⟩⟩
  rcases hX y', hX c', hX d' with ⟨rfl | rfl, rfl | rfl, rfl | rfl⟩ <;> aesop

private lemma Fintype.card_eq_two {X : Type u} [Fintype X] {a b : X} (h : a ≠ b)
    (hX : ∀ x : X, x = a ∨ x = b) : Fintype.card X = 2 := by
  let : Unique {x : X // x ≠ b} := {
    default := ⟨a, h⟩
    uniq x := Subtype.eq <| (hX x.val).resolve_right x.prop
  }
  nth_rw 1 [← Nat.pred_eq_succ_iff, ← card_subtype_eq b, ← card_subtype_compl, card_unique]

private lemma Units.rank_eq {K : Type u} [Field K] [NumberField K] (w₀ : InfinitePlace K) :
    rank K = @Fintype.card {w : InfinitePlace K // w ≠ w₀} (Fintype.ofFinite _) := by
  rw [rank, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

noncomputable section

namespace K_2_2_5_1

/-! ## Minimal polynomials -/

def minPolyℤ : Polynomial ℤ :=
  (1) * X ^ 2 + (-1) * X + (-1)

def minPoly : Polynomial ℚ :=
  minPolyℤ.map <| algebraMap ℤ ℚ

abbrev K := AdjoinRoot minPoly

lemma monic_minPolyℤ : minPolyℤ.Monic := by
  rw [minPolyℤ]
  ring_nf
  monicity!
  exact coeff_one

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

/-! ## Minimal polynomial roots -/

def root₁ : ℝ :=
  (1 + Real.sqrt 5) / 2

def root₂ : ℝ :=
  (1 - Real.sqrt 5) / 2

-- tactic?
lemma minPoly_eq : minPoly.map (algebraMap ℚ ℝ) = (X - C root₁) * (X - C root₂) := by
  rw [minPoly, minPolyℤ]
  have coeff0 : C root₁ * C root₂ = -1 := by
    rw [← C_mul, ← C_1, ← C_neg]
    congr 1
    sorry
  have coeff1 : C root₁ + C root₂ = 1 := by
    rw [← C_add, ← C_1]
    congr 1
    sorry
  linear_combination (norm := (polynomial_simp; ring1)) X * coeff1 - coeff0

-- tactic?
lemma root₁_ne_root₂ : root₁ ≠ root₂ := by
  sorry

variable (A : Type u) [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra ℝ A] [IsScalarTower ℚ ℝ A]

lemma mem_minPoly_aroots (x : A) :
    x ∈ minPoly.aroots A ↔ x = algebraMap ℝ A root₁ ∨ x = algebraMap ℝ A root₂ := by
  rw [aroots, IsScalarTower.algebraMap_eq ℚ ℝ, ← map_map, minPoly_eq]
  polynomial_simp
  simp_rw [mem_roots <| mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _), root_mul, root_X_sub_C]
  tauto

abbrev MinPolyRoot : Type u :=
  {x : A // x ∈ minPoly.aroots A}

def minPolyRoot₁ : MinPolyRoot A :=
  ⟨algebraMap ℝ A root₁, (mem_minPoly_aroots ..).mpr <| Or.inl rfl⟩

def minPolyRoot₂ : MinPolyRoot A :=
  ⟨algebraMap ℝ A root₂, (mem_minPoly_aroots ..).mpr <| Or.inr rfl⟩

lemma minPolyRoot₁_ne_minPolyRoot₂ : minPolyRoot₁ A ≠ minPolyRoot₂ A :=
  fun h ↦ root₁_ne_root₂ <| (algebraMap ℝ A).injective <| Subtype.mk.inj h

lemma minPolyRoot_eq (x : MinPolyRoot A) : x = minPolyRoot₁ A ∨ x = minPolyRoot₂ A := by
  rcases x with ⟨_, h⟩
  rcases (mem_minPoly_aroots ..).mp h with rfl | rfl <;> simp [minPolyRoot₁, minPolyRoot₂]

/-! ## Complex embeddings -/

def embedding₁ : K →ₐ[ℚ] A :=
  (Algebra.algHom ..).comp <| AdjoinRoot.liftHom _ _ (mem_aroots.mp (minPolyRoot₁ ℝ).prop).right

def embedding₂ : K →ₐ[ℚ] A :=
  (Algebra.algHom ..).comp <| AdjoinRoot.liftHom _ _ (mem_aroots.mp (minPolyRoot₂ ℝ).prop).right

omit [IsDomain A] in
@[simp]
lemma embedding₁_root : embedding₁ A (AdjoinRoot.root minPoly) = algebraMap ℝ A root₁ := by
  rw [embedding₁, AlgHom.coe_comp, Function.comp_apply, AdjoinRoot.liftHom_root]
  rfl

omit [IsDomain A] in
@[simp]
lemma embedding₂_root : embedding₂ A (AdjoinRoot.root minPoly) = algebraMap ℝ A root₂ := by
  rw [embedding₂, AlgHom.coe_comp, Function.comp_apply, AdjoinRoot.liftHom_root]
  rfl

lemma embedding₁_ne_embedding₂ : embedding₁ A ≠ embedding₂ A := by
  rw [ne_eq, AlgHom.ext_iff, not_forall]
  use AdjoinRoot.root minPoly
  rw [embedding₁_root, embedding₂_root]
  exact fun h ↦ root₁_ne_root₂ <| (algebraMap ℝ A).injective h

lemma embedding_eq (φ : K →ₐ[ℚ] A) : φ = embedding₁ A ∨ φ = embedding₂ A :=
  eq_or_eq_of_surjective (AdjoinRoot.equiv _ _ _ minPoly_ne_zero).symm.surjective (minPolyRoot_eq A)
    (embedding₁_ne_embedding₂ A) _

lemma embedding_isReal (φ : K →ₐ[ℚ] ℂ) : ComplexEmbedding.IsReal φ.toRingHom := by
  rcases embedding_eq ℂ φ with rfl | rfl <;> exact RingHom.ext fun _ ↦ Complex.conj_ofReal _

/-! ## Real embeddings -/

abbrev RealEmbedding : Type :=
  {φ : K →+* ℂ // ComplexEmbedding.IsReal φ}

def realEmbedding₁ : RealEmbedding :=
  ⟨embedding₁ ℂ, embedding_isReal _⟩

def realEmbedding₂ : RealEmbedding :=
  ⟨embedding₂ ℂ, embedding_isReal _⟩

omit [IsDomain A] in
@[simp]
lemma realEmbedding₁_root : realEmbedding₁.val (AdjoinRoot.root minPoly) = root₁ := by
  rw [realEmbedding₁, RingHom.coe_coe, embedding₁_root, Complex.coe_algebraMap]

omit [IsDomain A] in
@[simp]
lemma realEmbedding₂_root : realEmbedding₂.val (AdjoinRoot.root minPoly) = root₂ := by
  rw [realEmbedding₂, RingHom.coe_coe, embedding₂_root, Complex.coe_algebraMap]

def mkRealEmbedding (φ : K →ₐ[ℚ] ℝ) : RealEmbedding :=
  ⟨(algebraMap ℝ ℂ).comp φ, ComplexEmbedding.isReal_iff.mp <| RingHom.ext fun _ ↦ by simp⟩

lemma mkRealEmbedding_surjective : mkRealEmbedding.Surjective := fun φ ↦
  ⟨AlgHom.mk' (embedding_of_isReal (mkReal φ).prop) fun _ _ ↦ map_rat_smul .., by
    ext; simp [mkRealEmbedding, embedding_mk_eq_of_isReal φ.prop]⟩

lemma realEmbedding₁_ne_realEmbedding₂ : realEmbedding₁ ≠ realEmbedding₂ :=
  fun h ↦ embedding₁_ne_embedding₂ ℂ <| AlgHom.coe_ringHom_injective <| Subtype.mk_eq_mk.mp h

lemma realEmbedding_eq (φ : RealEmbedding) : φ = realEmbedding₁ ∨ φ = realEmbedding₂ :=
  eq_or_eq_of_surjective mkRealEmbedding_surjective (embedding_eq ℝ)
    realEmbedding₁_ne_realEmbedding₂ φ

/-! ## Real places -/

abbrev RealPlace : Type :=
  {v : InfinitePlace K // v.IsReal}

def realPlace₁ : RealPlace :=
  mkReal realEmbedding₁

def realPlace₂ : RealPlace :=
  mkReal realEmbedding₂

@[simp]
lemma realPlace₁_embedding : realPlace₁.val.embedding = realEmbedding₁ := by
  rw [realPlace₁, mkReal_coe, embedding_mk_eq_of_isReal <| isReal_of_mk_isReal realPlace₁.prop]

@[simp]
lemma realPlace₂_embedding : realPlace₂.val.embedding = realEmbedding₂ := by
  rw [realPlace₂, mkReal_coe, embedding_mk_eq_of_isReal <| isReal_of_mk_isReal realPlace₂.prop]

lemma realPlace₁_ne_realPlace₂ : realPlace₁ ≠ realPlace₂ :=
  realEmbedding₁_ne_realEmbedding₂ ∘ (EmbeddingLike.apply_eq_iff_eq _).mp

lemma realPlace_eq (v : RealPlace) : v = realPlace₁ ∨ v = realPlace₂ :=
  eq_or_eq_of_surjective mkReal.surjective realEmbedding_eq realPlace₁_ne_realPlace₂ v

/-! ## Infinite places -/

def place₁ : InfinitePlace K :=
  realPlace₁.val

def place₂ : InfinitePlace K :=
  realPlace₂.val

@[simp]
lemma place₁_mult : place₁.mult = 1 := by
  rw [mult, if_pos <| by exact realPlace₁.prop]

@[simp]
lemma place₂_mult : place₂.mult = 1 := by
  rw [mult, if_pos <| by exact realPlace₂.prop]

lemma place_isReal (v : InfinitePlace K) : v.IsReal :=
  isReal_iff.mpr <| embedding_isReal <| AlgHom.mk' v.embedding fun _ _ ↦ map_rat_smul ..

lemma place₁_ne_place₂ : place₁ ≠ place₂ :=
  realPlace₁_ne_realPlace₂ ∘ Subtype.eq

lemma place_eq (v : InfinitePlace K) : v = place₁ ∨ v = place₂ :=
  eq_or_eq_of_surjective (fun v ↦ ⟨⟨v, place_isReal v⟩, Subtype.coe_mk ..⟩)
    realPlace_eq place₁_ne_place₂ v

abbrev Place₀ : Type :=
  {v : InfinitePlace K // v ≠ place₂}

instance place₀_unique : Unique Place₀ where
  default := ⟨place₁, place₁_ne_place₂⟩
  uniq v := Subtype.eq <| (place_eq v).resolve_right v.prop

@[simp]
lemma place₀_default (v : Place₀) : v = place₁ := by
  rw [Unique.eq_default v]
  rfl

@[simp]
lemma place₀_mult (v : Place₀) : v.val.mult = 1 := by
  rw [place₀_default, place₁_mult]

def place₀_equiv : Place₀ ≃ Fin 1 where
  toFun _ := default
  invFun _ := default
  left_inv := Unique.default_eq
  right_inv := Unique.default_eq

@[simp]
lemma place₀_equiv_apply (v : Place₀) : place₀_equiv v = 0 :=
  rfl

/-! ## Miscellaneous -/

abbrev x : 𝓞 K :=
  ⟨AdjoinRoot.root minPoly, minPolyℤ, monic_minPolyℤ,
    by simpa [minPoly, minPolyℤ] using AdjoinRoot.eval₂_root minPoly⟩

lemma x_poly : x ^ 2 - x - 1 = 0 :=
  RingOfIntegers.coe_injective <| by simpa [minPoly, minPolyℤ] using AdjoinRoot.eval₂_root minPoly

def fundUnit1 : (𝓞 K)ˣ :=
  ⟨x, x - 1, by linear_combination x_poly, by linear_combination x_poly⟩

lemma fundSystem_eq : Units.fundSystem K = (fun _ ↦ fundUnit1) := by
  sorry

lemma rank : rank K = 1 := by
  rw [Units.rank_eq place₂]
  convert @Fintype.card_unique _ place₀_unique _

lemma regulator_mem : regulator K ∈ Set.Ioo 0.48 0.49 := by
  simp_rw [regulator_eq_det K place₂ <| place₀_equiv.trans <| finCongr rank.symm, place₀_mult,
    place₀_default, fundSystem_eq]
  simp
  sorry

axiom discr : discr K = 5

axiom isGalois : IsGalois ℚ K

axiom classNumber : classNumber K = 1

end K_2_2_5_1

end
