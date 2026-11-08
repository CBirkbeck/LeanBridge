import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# The Pfaffian

For a matrix `A` indexed by `l ⊕ l`, with `l` finite of cardinality `g`, let
`pfaffianSum A = ∑ σ, sign σ ∏ i, A (σ (inl i)) (σ (inr i))`, the sum over the permutations `σ` of
`l ⊕ l`. Over a `ℚ`-algebra the Pfaffian is `Pf(A) = (2ᵍ g!)⁻¹ · pfaffianSum A`; for an alternating
matrix it is the classical Pfaffian for the ordering `inl i₁, inr i₁, inl i₂, inr i₂, …` of the
indices.

The Pfaffian transforms by the determinant: `Pf(Bᵀ A B) = det B · Pf(A)` for all matrices `A` and
`B`. The alternatization of the multilinear form `v ↦ ∏ i, v (inl i) ⬝ᵥ A *ᵥ v (inr i)` on
`(R^(l ⊕ l))^(l ⊕ l)` is an alternating form of top degree, so a multiple of the determinant, the
multiple being `pfaffianSum A`, and `Bᵀ A B` gives its composite with `B`. The Pfaffian of
Mathlib's `J = [[0, -1], [1, 0]]` is `(-1)ᵍ`: the multilinearity in the `g` pairs and a
transposition in each pair give `pfaffianSum (A - Aᵀ) = 2ᵍ · pfaffianSum A`, and
`pfaffianSum [[0, 1], [0, 0]] = g!`, the only permutations contributing being the `π ⊕ π`.

These are the properties of the Pfaffian with which the LMFDB (`group.sp2gr`) shows that a
symplectic matrix `γ`, one with `γᵀ J γ = J`, has determinant `1`: `Pf(γᵀ J γ) = Pf(J)` and
`Pf(γᵀ J γ) = det γ · Pf(J)`, with `Pf(J) = ±1`. The conclusion itself is Mathlib's
`SymplecticGroup.det_eq_one`, over any commutative ring. The integral symplectic group
`Sp(2g, ℤ)`, which the LMFDB defines as `Sp(2g, ℝ) ∩ M(2g, ℤ)`, is `symplecticGroup l ℤ`, since an
injective ring homomorphism such as `ℤ → ℝ` reflects symplectic matrices.

## Main definitions

* `LinearMap.pairProd`: the multilinear form `v ↦ ∏ i, β (v (inl i)) (v (inr i))` of a bilinear
  form `β`.
* `Matrix.pfaffianSum`, `Matrix.pfaffian` (LMFDB `group.sp2gr`): the Pfaffian.
* `Matrix.pfaffianSumMultilinear`: the Pfaffian sum as a multilinear form in one matrix per pair.

## Main results

* `Matrix.pfaffianSum_transpose_mul_mul`, `Matrix.pfaffian_transpose_mul_mul` (LMFDB
  `group.sp2gr`): `Pf(Bᵀ A B) = det B · Pf(A)`.
* `Matrix.pfaffian_J`, `Matrix.pfaffian_neg_J` (LMFDB `group.sp2gr`): `Pf(J) = (-1)ᵍ`, and
  `Pf(-J) = 1` for the LMFDB's `J`, which is Mathlib's `-J`.
* `Matrix.pfaffian_transpose_mul_J_mul` (LMFDB `group.sp2gr`): `Pf(γᵀ J γ) = Pf(J)` for a
  symplectic matrix `γ`.
* `Matrix.map_mem_symplecticGroup_iff` (LMFDB `group.sp2gr`): an injective ring homomorphism
  reflects symplectic matrices, so `Sp(2g, ℤ) = Sp(2g, ℝ) ∩ M(2g, ℤ)`.
-/

open Equiv Function

variable {l R : Type*} [Fintype l] [DecidableEq l] [CommRing R]

namespace LinearMap

variable {M : Type*} [AddCommGroup M] [Module R M] (β : M →ₗ[R] M →ₗ[R] R) (v : l ⊕ l → M) (k : l)
  (z : M)

variable [DecidableEq (l ⊕ l)] in
lemma prod_update_inl_eq_mkPiAlgebra :
    ∏ i, β (update v (.inl k) z (.inl i)) (update v (.inl k) z (.inr i)) =
      (MultilinearMap.mkPiAlgebra R l R).compLinearMap (fun i ↦ β.flip (v (.inr i)))
        (update (v ∘ .inl) k z) := by
  rw [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [flip_apply, update_of_ne Sum.inr_ne_inl, ← update_comp_eq_of_injective v Sum.inl_injective]
  rfl

variable [DecidableEq (l ⊕ l)] in
lemma prod_update_inr_eq_mkPiAlgebra :
    ∏ i, β (update v (.inr k) z (.inl i)) (update v (.inr k) z (.inr i)) =
      (MultilinearMap.mkPiAlgebra R l R).compLinearMap (fun i ↦ β (v (.inl i)))
        (update (v ∘ .inr) k z) := by
  rw [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [update_of_ne Sum.inl_ne_inr, ← update_comp_eq_of_injective v Sum.inr_injective]
  rfl

variable (l) in
/-- The multilinear form `v ↦ ∏ i, β (v (inl i)) (v (inr i))` on `M ^ (l ⊕ l)` attached to a
bilinear form `β`, pairing the arguments `inl i` and `inr i`. -/
def pairProd : MultilinearMap R (fun _ : l ⊕ l ↦ M) R where
  toFun v := ∏ i, β (v (.inl i)) (v (.inr i))
  map_update_add' v j x y := by
    rcases j with k | k
    · simp only [prod_update_inl_eq_mkPiAlgebra, MultilinearMap.map_update_add]
    · simp only [prod_update_inr_eq_mkPiAlgebra, MultilinearMap.map_update_add]
  map_update_smul' v j c x := by
    rcases j with k | k
    · simp only [prod_update_inl_eq_mkPiAlgebra, MultilinearMap.map_update_smul]
    · simp only [prod_update_inr_eq_mkPiAlgebra, MultilinearMap.map_update_smul]

lemma pairProd_apply : pairProd l β v = ∏ i, β (v (.inl i)) (v (.inr i)) :=
  rfl

lemma pairProd_compLinearMap {M' : Type*} [AddCommGroup M'] [Module R M'] (g : M' →ₗ[R] M) :
    (pairProd l β).compLinearMap (fun _ ↦ g) = pairProd l (β.compl₁₂ g g) :=
  rfl

end LinearMap

namespace Matrix

variable (A B : Matrix (l ⊕ l) (l ⊕ l) R) (C : l → Matrix (l ⊕ l) (l ⊕ l) R)
  {γ : Matrix (l ⊕ l) (l ⊕ l) R}

/-- The sum `∑ σ, sign σ • ∏ i, A (σ (inl i)) (σ (inr i))` over the permutations `σ` of `l ⊕ l`:
`2ᵍ g!` times the Pfaffian of `A`, for `g` the cardinality of `l`. -/
def pfaffianSum : R :=
  ∑ σ : Perm (l ⊕ l), Perm.sign σ • ∏ i, A (σ (.inl i)) (σ (.inr i))

lemma alternatization_pairProd_toLinearMap₂' :
    (LinearMap.pairProd l (toLinearMap₂' R A)).alternatization (Pi.basisFun R (l ⊕ l)) =
      pfaffianSum A := by
  rw [MultilinearMap.alternatization_apply, pfaffianSum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [MultilinearMap.domDomCongr_apply, LinearMap.pairProd_apply]
  simp [toLinearMap₂'_apply']

/-- **The Pfaffian transforms by the determinant**: `Pf(Bᵀ A B) = det B · Pf(A)`, here for the
unnormalised sum `pfaffianSum`, over any commutative ring. -/
lemma pfaffianSum_transpose_mul_mul : pfaffianSum (Bᵀ * A * B) = B.det * pfaffianSum A := by
  rw [← alternatization_pairProd_toLinearMap₂', ← toLinearMap₂'_comp,
    ← LinearMap.pairProd_compLinearMap, MultilinearMap.alternatization_compLinearMap,
    AlternatingMap.compLinearMap_apply,
    (MultilinearMap.alternatization _).eq_smul_basis_det (Pi.basisFun R (l ⊕ l)),
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, alternatization_pairProd_toLinearMap₂',
    Pi.basisFun_det_apply, mul_comm, ← det_transpose B]
  congr 2
  ext i j
  simp

/-- The multilinear form `C ↦ ∑ σ, sign σ • ∏ i, C i (σ (inl i)) (σ (inr i))` in a family of
matrices indexed by the pairs `(inl i, inr i)`, which is `pfaffianSum A` on the constant family
`A`. -/
def pfaffianSumMultilinear : MultilinearMap R (fun _ : l ↦ Matrix (l ⊕ l) (l ⊕ l) R) R :=
  ∑ σ : Perm (l ⊕ l), Perm.sign σ • (MultilinearMap.mkPiAlgebra R l R).compLinearMap
    fun i ↦ entryLinearMap R R (σ (.inl i)) (σ (.inr i))

lemma pfaffianSumMultilinear_apply :
    pfaffianSumMultilinear C =
      ∑ σ : Perm (l ⊕ l), Perm.sign σ • ∏ i, C i (σ (.inl i)) (σ (.inr i)) := by
  simp [pfaffianSumMultilinear]

lemma pfaffianSumMultilinear_const : pfaffianSumMultilinear (fun _ ↦ A) = pfaffianSum A :=
  pfaffianSumMultilinear_apply _

lemma pfaffianSumMultilinear_update_transpose (k : l) :
    pfaffianSumMultilinear (update C k Aᵀ) = -pfaffianSumMultilinear (update C k A) := by
  rw [pfaffianSumMultilinear_apply, pfaffianSumMultilinear_apply,
    ← Equiv.sum_comp (Equiv.mulRight (Equiv.swap (Sum.inl k) (Sum.inr k))),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [coe_mulRight, Perm.sign_mul, Perm.sign_swap Sum.inl_ne_inr, mul_neg_one, Units.neg_smul]
  congr 2
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rcases eq_or_ne i k with rfl | hik
  · simp
  · simp [hik, swap_apply_of_ne_of_ne]

lemma pfaffianSum_sub_transpose : pfaffianSum (A - Aᵀ) = 2 ^ Fintype.card l * pfaffianSum A := by
  have key (S : Finset l) : pfaffianSumMultilinear (fun i ↦ if i ∈ S then A - Aᵀ else A) =
      2 ^ S.card * pfaffianSum A := by
    induction S using Finset.induction_on with
    | empty => simp [pfaffianSumMultilinear_const]
    | insert k S hk ih =>
      have h : (fun i ↦ if i ∈ insert k S then A - Aᵀ else A) =
          update (fun i ↦ if i ∈ S then A - Aᵀ else A) k (A - Aᵀ) := by
        ext1 i
        rcases eq_or_ne i k with rfl | hik
        · simp
        · simp [hik]
      rw [h, MultilinearMap.map_update_sub, pfaffianSumMultilinear_update_transpose, sub_neg_eq_add,
        update_eq_self_iff.mpr (by simp [hk]), ih, Finset.card_insert_of_notMem hk, pow_succ]
      ring1
  simpa [pfaffianSumMultilinear_const] using key Finset.univ

lemma pfaffianSum_fromBlocks_zero_one_zero_zero :
    pfaffianSum (fromBlocks 0 1 0 0 : Matrix (l ⊕ l) (l ⊕ l) R) = (Fintype.card l).factorial := by
  have hD : Injective fun π : Perm l ↦ sumCongr π π := fun π π' h ↦ by
    ext i
    simpa using congrArg (· (Sum.inl i)) h
  rw [pfaffianSum, ← Finset.sum_subset (Finset.subset_univ (Finset.univ.image fun π ↦ sumCongr π π))
    ?_, Finset.sum_image fun π _ π' _ h ↦ hD h]
  · simp [Fintype.card_perm]
  · intro σ _ hσ
    by_contra hne
    have h (i : l) : ∃ j, σ (.inl i) = .inl j ∧ σ (.inr i) = .inr j := by
      have hi : (fromBlocks 0 1 0 0 : Matrix (l ⊕ l) (l ⊕ l) R) (σ (.inl i)) (σ (.inr i)) ≠ 0 :=
        fun h0 ↦ hne (by rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, smul_zero])
      rcases ha : σ (.inl i) with a | a <;> rcases hb : σ (.inr i) with b | b <;>
        rw [ha, hb] at hi <;> simp [one_apply] at hi
      exact ⟨a, rfl, by rw [hi.1]⟩
    choose f hf using h
    have hinj : Injective f := fun i i' hii' ↦ Sum.inl_injective <| σ.injective <|
      (hf i).1.trans ((congrArg Sum.inl hii').trans (hf i').1.symm)
    refine hσ (Finset.mem_image.mpr ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj),
      Finset.mem_univ _, Equiv.ext fun x ↦ ?_⟩)
    rcases x with i | i
    · simp [(hf i).1]
    · simp [(hf i).2]

lemma pfaffianSum_neg : pfaffianSum (-A) = (-1) ^ Fintype.card l * pfaffianSum A := by
  simp [pfaffianSum, Finset.prod_neg, Finset.mul_sum, mul_smul_comm]

lemma pfaffianSum_J : pfaffianSum (J l R) =
    (-1) ^ Fintype.card l * (2 ^ Fintype.card l * (Fintype.card l).factorial) := by
  have h : J l R = -((fromBlocks 0 1 0 0 : Matrix (l ⊕ l) (l ⊕ l) R) - (fromBlocks 0 1 0 0)ᵀ) := by
    simp [J, fromBlocks_transpose, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  rw [h, pfaffianSum_neg, pfaffianSum_sub_transpose, pfaffianSum_fromBlocks_zero_one_zero_zero]

variable {S : Type*} [CommRing S] {A} in
/-- **An injective ring homomorphism reflects symplectic matrices** (LMFDB `group.sp2gr`): `A` is
symplectic exactly when its image under an injective `f : R →+* S` is. For `f : ℤ → ℝ`, this says
that the integral symplectic group `Sp(2g, ℤ) = symplecticGroup l ℤ` is `Sp(2g, ℝ) ∩ M(2g, ℤ)`. -/
lemma map_mem_symplecticGroup_iff {f : R →+* S} (hf : Injective f) :
    A.map f ∈ symplecticGroup l S ↔ A ∈ symplecticGroup l R := by
  rw [SymplecticGroup.mem_iff, SymplecticGroup.mem_iff, ← transpose_map, ← map_J l f,
    ← Matrix.map_mul, ← Matrix.map_mul, (map_injective hf).eq_iff]

variable [Algebra ℚ R]

/-- The **Pfaffian** of a square matrix `A` indexed by `l ⊕ l`, over a `ℚ`-algebra, for the
pairing of `inl i` with `inr i`: `Pf(A) = (2ᵍ g!)⁻¹ ∑ σ, sign σ ∏ i, A (σ (inl i)) (σ (inr i))`,
where `g` is the cardinality of `l` and `σ` runs over the permutations of `l ⊕ l`. For an
alternating matrix it is the classical `(2ᵍ g!)⁻¹ ∑_{σ ∈ S_{2g}} sign σ ∏ i, A_{σ(2i-1), σ(2i)}`
for the ordering `inl i₁, inr i₁, inl i₂, inr i₂, …` of `l ⊕ l`; another ordering changes its sign
only. -/
noncomputable def pfaffian : R :=
  (2 ^ Fintype.card l * (Fintype.card l).factorial : ℚ)⁻¹ • pfaffianSum A

/-- **The Pfaffian transforms by the determinant** (LMFDB `group.sp2gr`):
`Pf(Bᵀ A B) = det B · Pf(A)`. -/
lemma pfaffian_transpose_mul_mul : pfaffian (Bᵀ * A * B) = B.det * pfaffian A := by
  rw [pfaffian, pfaffian, pfaffianSum_transpose_mul_mul, mul_smul_comm]

lemma pfaffian_neg : pfaffian (-A) = (-1) ^ Fintype.card l * pfaffian A := by
  rw [pfaffian, pfaffian, pfaffianSum_neg, mul_smul_comm]

/-- **The Pfaffian of `J`** (LMFDB `group.sp2gr`): `Pf(J) = (-1)ᵍ` for Mathlib's
`J = [[0, -1], [1, 0]]`. -/
lemma pfaffian_J : pfaffian (J l R) = (-1) ^ Fintype.card l := by
  have h : (2 ^ Fintype.card l * (Fintype.card l).factorial : ℚ) ≠ 0 := by positivity
  have h' : (2 ^ Fintype.card l * (Fintype.card l).factorial : R) =
      algebraMap ℚ R (2 ^ Fintype.card l * (Fintype.card l).factorial) := by
    rw [map_mul, map_pow, map_natCast, map_ofNat]
  rw [pfaffian, pfaffianSum_J, ← mul_smul_comm, Algebra.smul_def, h', ← map_mul,
    inv_mul_cancel₀ h, map_one, mul_one]

/-- The Pfaffian of the LMFDB's `J = [[0, 1], [-1, 0]]`, the negative of Mathlib's `J`, is `1`. -/
lemma pfaffian_neg_J : pfaffian (-J l R) = 1 := by
  rw [pfaffian_neg, pfaffian_J, ← mul_pow, neg_one_mul, neg_neg, one_pow]

/-- The first Pfaffian property of the LMFDB (`group.sp2gr`): `Pf(γᵀ J γ) = Pf(J)` for a symplectic
matrix `γ`. -/
lemma pfaffian_transpose_mul_J_mul (hγ : γ ∈ symplecticGroup l R) :
    pfaffian (γᵀ * J l R * γ) = pfaffian (J l R) := by
  rw [SymplecticGroup.mem_iff'.mp hγ]

end Matrix
