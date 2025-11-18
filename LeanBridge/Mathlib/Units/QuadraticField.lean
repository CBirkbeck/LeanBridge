import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

open NumberField InfinitePlace Units Polynomial

universe u

local macro "polynomial_simp" : tactic =>
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

namespace QuadraticField

/-! ## Minimal polynomials -/

variable (D : ℕ)

def minPolyℤ : Polynomial ℤ :=
  X ^ 2 - X - C (D : ℤ)

def minPoly : Polynomial ℚ :=
  (minPolyℤ D).map <| algebraMap ℤ ℚ

abbrev K :=
  AdjoinRoot <| minPoly D

abbrev root :=
  AdjoinRoot.root <| minPoly D

lemma monic_minPolyℤ : (minPolyℤ D).Monic := by
  rw [minPolyℤ]
  monicity!

lemma monic_minPoly : (minPoly D).Monic :=
  (monic_minPolyℤ D).map _

lemma minPolyℤ_ne_zero : minPolyℤ D ≠ 0 :=
  (monic_minPolyℤ D).ne_zero

lemma minPoly_ne_zero : minPoly D ≠ 0 :=
  (monic_minPoly D).ne_zero

/-! ## Minimal polynomial roots -/

def root₁ : ℝ :=
  (1 + Real.sqrt (1 + 4 * D)) / 2

def root₂ : ℝ :=
  (1 - Real.sqrt (1 + 4 * D)) / 2

@[simp]
lemma root₁_mul_root₂ : root₁ D * root₂ D = -D := by
  rw [root₁, root₂, div_mul_div_comm, ← sq_sub_sq, Real.sq_sqrt <| by exact_mod_cast zero_le _]
  norm_num [neg_div]

@[simp]
lemma root₁_add_root₂ : root₁ D + root₂ D = 1 := by
  rw [root₁, root₂, div_add_div_same, add_add_sub_cancel, add_self_div_two]

@[simp]
lemma minPoly_eq : (minPoly D).map (algebraMap ℚ ℝ) = (X - C (root₁ D)) * (X - C (root₂ D)) := by
  rw [minPoly, minPolyℤ]
  polynomial_simp
  simp_rw [map_natCast]
  have h0 : C (root₁ D) * C (root₂ D) = -D := by rw [← C_mul, root₁_mul_root₂, map_neg, map_natCast]
  have h1 : C (root₁ D) + C (root₂ D) = 1 := by rw [← C_add, root₁_add_root₂, C_1]
  linear_combination X * h1 - h0

lemma root₁_ne_root₂ : root₁ D ≠ root₂ D := by
  rw [root₁, root₂, ne_eq, div_left_inj' two_ne_zero, ← sub_neg_eq_add, sub_eq_sub_iff_sub_eq_sub,
    sub_self, ← neg_add', zero_eq_neg, add_self_eq_zero,
    Real.sqrt_eq_zero <| by exact_mod_cast zero_le _]
  exact_mod_cast NeZero.ne _

variable (A : Type u) [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra ℝ A] [IsScalarTower ℚ ℝ A]

lemma mem_minPoly_aroots (x : A) :
    x ∈ (minPoly D).aroots A ↔ x = algebraMap ℝ A (root₁ D) ∨ x = algebraMap ℝ A (root₂ D) := by
  rw [aroots, IsScalarTower.algebraMap_eq ℚ ℝ, ← map_map, minPoly_eq]
  polynomial_simp
  simp_rw [mem_roots <| mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _), root_mul, root_X_sub_C]
  tauto

abbrev MinPolyRoot : Type u :=
  {x : A // x ∈ (minPoly D).aroots A}

def minPolyRoot₁ : MinPolyRoot D A :=
  ⟨algebraMap ℝ A <| root₁ D, (mem_minPoly_aroots ..).mpr <| Or.inl rfl⟩

def minPolyRoot₂ : MinPolyRoot D A :=
  ⟨algebraMap ℝ A <| root₂ D, (mem_minPoly_aroots ..).mpr <| Or.inr rfl⟩

lemma minPolyRoot₁_ne_minPolyRoot₂ : minPolyRoot₁ D A ≠ minPolyRoot₂ D A :=
  fun h ↦ root₁_ne_root₂ D <| (algebraMap ℝ A).injective <| Subtype.mk.inj h

lemma minPolyRoot_eq (x : MinPolyRoot D A) : x = minPolyRoot₁ D A ∨ x = minPolyRoot₂ D A := by
  rcases x with ⟨_, h⟩
  rcases (mem_minPoly_aroots ..).mp h with rfl | rfl <;> simp [minPolyRoot₁, minPolyRoot₂]

/-! ## Complex embeddings -/

def embedding₁ : K D →ₐ[ℚ] A :=
  (Algebra.algHom ..).comp <| AdjoinRoot.liftHom _ _ (mem_aroots.mp (minPolyRoot₁ D ℝ).prop).right

def embedding₂ : K D →ₐ[ℚ] A :=
  (Algebra.algHom ..).comp <| AdjoinRoot.liftHom _ _ (mem_aroots.mp (minPolyRoot₂ D ℝ).prop).right

omit [IsDomain A] in
@[simp]
lemma embedding₁_root : embedding₁ D A (root D) = algebraMap ℝ A (root₁ D) := by
  rw [embedding₁, AlgHom.coe_comp, Function.comp_apply, AdjoinRoot.liftHom_root]
  rfl

omit [IsDomain A] in
@[simp]
lemma embedding₂_root : embedding₂ D A (root D) = algebraMap ℝ A (root₂ D) := by
  rw [embedding₂, AlgHom.coe_comp, Function.comp_apply, AdjoinRoot.liftHom_root]
  rfl

lemma embedding₁_ne_embedding₂ : embedding₁ D A ≠ embedding₂ D A := by
  rw [ne_eq, AlgHom.ext_iff, not_forall]
  use root D
  rw [embedding₁_root, embedding₂_root]
  exact fun h ↦ root₁_ne_root₂ D <| (algebraMap ℝ A).injective h

lemma embedding_eq (φ : K D →ₐ[ℚ] A) : φ = embedding₁ D A ∨ φ = embedding₂ D A :=
  eq_or_eq_of_surjective (AdjoinRoot.equiv _ _ _ <| minPoly_ne_zero D).symm.surjective
    (minPolyRoot_eq  D A) (embedding₁_ne_embedding₂ D A) _

variable [Fact <| Irreducible <| minPoly D]

lemma embedding_isReal (φ : K D →ₐ[ℚ] ℂ) : ComplexEmbedding.IsReal φ.toRingHom := by
  rcases embedding_eq D ℂ φ with rfl | rfl <;> exact RingHom.ext fun _ ↦ Complex.conj_ofReal _

/-! ## Real embeddings -/

abbrev RealEmbedding : Type :=
  {φ : K D →+* ℂ // ComplexEmbedding.IsReal φ}

def realEmbedding₁ : RealEmbedding D :=
  ⟨embedding₁ D ℂ, embedding_isReal D _⟩

def realEmbedding₂ : RealEmbedding D :=
  ⟨embedding₂ D ℂ, embedding_isReal D _⟩

omit [IsDomain A] in
@[simp]
lemma realEmbedding₁_root : (realEmbedding₁ D).val (root D) = root₁ D := by
  rw [realEmbedding₁, RingHom.coe_coe, embedding₁_root, Complex.coe_algebraMap]

omit [IsDomain A] in
@[simp]
lemma realEmbedding₂_root : (realEmbedding₂ D).val (root D) = root₂ D := by
  rw [realEmbedding₂, RingHom.coe_coe, embedding₂_root, Complex.coe_algebraMap]

def mkRealEmbedding (φ : K D →ₐ[ℚ] ℝ) : RealEmbedding D :=
  ⟨(algebraMap ℝ ℂ).comp φ, ComplexEmbedding.isReal_iff.mp <| RingHom.ext fun _ ↦ by simp⟩

lemma mkRealEmbedding_surjective : (mkRealEmbedding D).Surjective := fun φ ↦
  ⟨AlgHom.mk' (embedding_of_isReal (mkReal φ).prop) fun _ _ ↦ map_rat_smul .., by
    ext; simp [mkRealEmbedding, embedding_mk_eq_of_isReal φ.prop]⟩

lemma realEmbedding₁_ne_realEmbedding₂ : realEmbedding₁ D ≠ realEmbedding₂ D :=
  fun h ↦ embedding₁_ne_embedding₂ D ℂ <| AlgHom.coe_ringHom_injective <| Subtype.mk_eq_mk.mp h

lemma realEmbedding_eq (φ : RealEmbedding D) : φ = realEmbedding₁ D ∨ φ = realEmbedding₂ D :=
  eq_or_eq_of_surjective (mkRealEmbedding_surjective D) (embedding_eq D ℝ)
    (realEmbedding₁_ne_realEmbedding₂ D) φ

/-! ## Real places -/

abbrev RealPlace : Type :=
  {v : InfinitePlace <| K D // v.IsReal}

def realPlace₁ : RealPlace D :=
  mkReal <| realEmbedding₁ D

def realPlace₂ : RealPlace D :=
  mkReal <| realEmbedding₂ D

@[simp]
lemma realPlace₁_embedding : (realPlace₁ D).val.embedding = realEmbedding₁ D := by
  rw [realPlace₁, mkReal_coe, embedding_mk_eq_of_isReal <| isReal_of_mk_isReal (realPlace₁ D).prop]

@[simp]
lemma realPlace₂_embedding : (realPlace₂ D).val.embedding = realEmbedding₂ D := by
  rw [realPlace₂, mkReal_coe, embedding_mk_eq_of_isReal <| isReal_of_mk_isReal (realPlace₂ D).prop]

lemma realPlace₁_ne_realPlace₂ : realPlace₁ D ≠ realPlace₂ D :=
  realEmbedding₁_ne_realEmbedding₂ D ∘ (EmbeddingLike.apply_eq_iff_eq _).mp

lemma realPlace_eq (v : RealPlace D) : v = realPlace₁ D ∨ v = realPlace₂ D :=
  eq_or_eq_of_surjective mkReal.surjective (realEmbedding_eq D) (realPlace₁_ne_realPlace₂ D) v

/-! ## Infinite places -/

def place₁ : InfinitePlace <| K D :=
  (realPlace₁ D).val

def place₂ : InfinitePlace <| K D :=
  (realPlace₂ D).val

@[simp]
lemma place₁_mult : (place₁ D).mult = 1 := by
  rw [mult, if_pos <| by exact (realPlace₁ D).prop]

@[simp]
lemma place₂_mult : (place₂ D).mult = 1 := by
  rw [mult, if_pos <| by exact (realPlace₂ D).prop]

lemma place_isReal (v : InfinitePlace <| K D) : v.IsReal :=
  isReal_iff.mpr <| embedding_isReal D <| AlgHom.mk' v.embedding fun _ _ ↦ map_rat_smul ..

lemma place₁_ne_place₂ : place₁ D ≠ place₂ D :=
  realPlace₁_ne_realPlace₂ D ∘ Subtype.eq

lemma place_eq (v : InfinitePlace <| K D) : v = place₁ D ∨ v = place₂ D :=
  eq_or_eq_of_surjective (fun v ↦ ⟨⟨v, place_isReal D v⟩, Subtype.coe_mk ..⟩)
    (realPlace_eq D) (place₁_ne_place₂ D) v

abbrev Place₀ : Type :=
  {v : InfinitePlace <| K D // v ≠ place₂ D}

instance place₀_unique : Unique (Place₀ D) where
  default := ⟨place₁ D, place₁_ne_place₂ D⟩
  uniq v := Subtype.eq <| (place_eq D v).resolve_right v.prop

@[simp]
lemma place₀_default (v : Place₀ D) : v = place₁ D := by
  rw [Unique.eq_default v]
  rfl

@[simp]
lemma place₀_mult (v : Place₀ D) : v.val.mult = 1 := by
  rw [place₀_default, place₁_mult]

def place₀_equiv : Place₀ D ≃ Fin 1 where
  toFun _ := default
  invFun _ := default
  left_inv := Unique.default_eq
  right_inv := Unique.default_eq

@[simp]
lemma place₀_equiv_apply (v : Place₀ D) : place₀_equiv D v = 0 :=
  rfl

theorem rank : rank (K D) = 1 := by
  rw [Units.rank_eq <| place₂ D]
  convert @Fintype.card_unique _ (place₀_unique D) _

end QuadraticField

end
