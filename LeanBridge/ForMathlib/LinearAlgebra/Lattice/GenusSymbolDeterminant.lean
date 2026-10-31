import LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolSign
import TauCeti.LinearAlgebra.Matrix.Block

/-!
# The Jordan ranks determine the valuation of the determinant

For a Jordan splitting `L ⊗ ℤ_p = ⊕_j N j` of a nondegenerate integral lattice, with `N j` the
`p ^ j`-modular constituent, the Gram matrix in a basis adapted to the splitting is block diagonal
with blocks `p ^ j` times matrices of unit determinant. Hence the determinant of `L` is
`p ^ (∑_j j n_j)` times a `p`-adic unit, `n_j` the rank of `N j`: the `p`-adic valuation of the
determinant is `∑_j j n_j` (`TauCeti.IntegralLattice.factorization_natAbs_determinant`). This is the
identity behind the Conway genus symbol (LMFDB `lattice.conway_genus_symbol`) recording the
powers `q = p ^ j` of the Jordan constituents, and behind the label of a genus
(LMFDB `lattice.genus_label`), whose rank codes at `p` omit the ranks `n₀` and `n₁`, determined by
the rank, the valuation of the determinant and the other ranks.

## Main definitions

* `LinearMap.BilinForm.IsJordanSplitting.adaptedBasis`: a basis adapted to a Jordan splitting.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.associated_det`: the Gram determinant of a form over `ℤ_p`
  with a Jordan splitting is associated to `p ^ ∑_j j n_j`.
* `TauCeti.IntegralLattice.factorization_natAbs_determinant`: the `p`-adic valuation of the
  determinant of a nondegenerate lattice is `∑_k k n_k`, the sum of the scale exponents of its
  Jordan constituents at `p` weighted by their ranks.
* `TauCeti.IntegralLattice.jordanRank_eq_zero_of_lt`: the nonzero Jordan constituents have scale
  exponents at most the valuation of the determinant.
-/

open Module

open LinearMap (BilinForm)

namespace LinearMap.BilinForm

variable {p : ℕ} [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
  {B : BilinForm ℤ_[p] M} {N : ℕ → Submodule ℤ_[p] M} {J : ℕ} {ι : Type*} [Fintype ι]
  [DecidableEq ι]

lemma IsJordanSplitting.isInternal_fin (h : B.IsJordanSplitting (p : ℤ_[p]) N)
    (hJ : ∀ j, J ≤ j → N j = ⊥) : DirectSum.IsInternal fun j : Fin J ↦ N j := by
  refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨h.isInternal.submodule_iSupIndep.comp Fin.val_injective, eq_top_iff.mpr ?_⟩
  rw [← h.isInternal.submodule_iSup_eq_top]
  refine iSup_le fun j ↦ ?_
  rcases lt_or_ge j J with hj | hj
  · exact le_iSup (fun i : Fin J ↦ N i) ⟨j, hj⟩
  · rw [hJ j hj]
    exact bot_le

variable [Module.Finite ℤ_[p] M] in
lemma IsJordanSplitting.exists_forall_eq_bot (h : B.IsJordanSplitting (p : ℤ_[p]) N) :
    ∃ J, ∀ j, J ≤ j → N j = ⊥ := by
  rcases h.hasFiniteSupport.bddAbove with ⟨b, hb⟩
  exact ⟨b + 1, fun j hj ↦ by_contra fun hne ↦ absurd (hb hne) (by omega)⟩

variable [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M]

/-- A **basis adapted to a Jordan splitting** `N` whose constituents `N j` vanish for `j ≥ J`: the
union of the bases `finBasis` of the constituents `N j`, `j < J`. -/
noncomputable def IsJordanSplitting.adaptedBasis (h : B.IsJordanSplitting (p : ℤ_[p]) N)
    (hJ : ∀ j, J ≤ j → N j = ⊥) : Basis (Σ j : Fin J, Fin (finrank ℤ_[p] (N j))) ℤ_[p] M :=
  (h.isInternal_fin hJ).collectedBasis fun j ↦ finBasis ℤ_[p] (N j)

lemma IsJordanSplitting.toMatrix₂_adaptedBasis (h : B.IsJordanSplitting (p : ℤ_[p]) N)
    (hJ : ∀ j, J ≤ j → N j = ⊥) : toMatrix₂ (h.adaptedBasis hJ) (h.adaptedBasis hJ) B =
    Matrix.blockDiagonal' fun j : Fin J ↦ (p : ℤ_[p]) ^ (j : ℕ) •
      toMatrix₂ (finBasis ℤ_[p] (N j)) (finBasis ℤ_[p] (N j)) (h.unitForm j) := by
  refine Matrix.ext fun x y ↦ ?_
  rcases x with ⟨j, a⟩
  rcases y with ⟨k, c⟩
  rw [LinearMap.toMatrix₂_apply, IsJordanSplitting.adaptedBasis,
    (h.isInternal_fin hJ).collectedBasis_coe]
  rcases eq_or_ne j k with rfl | hjk
  · rw [Matrix.blockDiagonal'_apply_eq, Matrix.smul_apply, smul_eq_mul, h.apply_basis]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hjk, h.apply_eq_zero j k (Fin.val_ne_of_ne hjk) _
      ((finBasis ℤ_[p] (N j)) a).2 _ ((finBasis ℤ_[p] (N k)) c).2]

lemma IsJordanSplitting.associated_det_of_forall_eq_bot (h : B.IsJordanSplitting (p : ℤ_[p]) N)
    (hJ : ∀ j, J ≤ j → N j = ⊥) (b : Basis ι ℤ_[p] M) : Associated (toMatrix₂ b b B).det
    ((p : ℤ_[p]) ^ ∑ j : Fin J, (j : ℕ) * finrank ℤ_[p] (N j)) := by
  have hG : Associated (toMatrix₂ (h.adaptedBasis hJ) (h.adaptedBasis hJ) B).det
      ((p : ℤ_[p]) ^ ∑ j : Fin J, (j : ℕ) * finrank ℤ_[p] (N j)) := by
    rw [h.toMatrix₂_adaptedBasis hJ, Matrix.det_blockDiagonal']
    simp only [Matrix.det_smul, Fintype.card_fin, ← pow_mul, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    exact associated_mul_unit_left _ _ (IsUnit.prod_univ_iff.mpr fun j ↦
      isUnit_det_toMatrix₂_of_isPerfPair _ (h.isPerfPair_unitForm j))
  have hcard : Fintype.card (Σ j : Fin J, Fin (finrank ℤ_[p] (N j))) = Fintype.card ι := by
    rw [← finrank_eq_card_basis b, ← finrank_eq_card_basis (h.adaptedBasis hJ)]
  rw [← det_toMatrix₂_reindex _ (Fintype.equivOfCardEq hcard)] at hG
  refine Associated.trans ?_ hG
  rw [← LinearMap.toMatrix₂_mul_basis_toMatrix
    ((h.adaptedBasis hJ).reindex (Fintype.equivOfCardEq hcard))
    ((h.adaptedBasis hJ).reindex (Fintype.equivOfCardEq hcard)) b b, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose, mul_comm, ← mul_assoc]
  exact associated_unit_mul_left _ _ <| (Matrix.isUnit_det_of_right_inverse
    (Basis.toMatrix_mul_toMatrix_flip _ _)).mul (Matrix.isUnit_det_of_right_inverse
    (Basis.toMatrix_mul_toMatrix_flip _ _))

/-- **The Gram determinant of a form with a Jordan splitting is `p ^ ∑_j j n_j` times a unit.**
If `N` is a Jordan splitting of a bilinear form `B` over `ℤ_p`, with constituents `N j` of rank
`n_j`, then the determinant of `B` in any basis is associated to `p ^ ∑_j j n_j`. -/
lemma IsJordanSplitting.associated_det (h : B.IsJordanSplitting (p : ℤ_[p]) N)
    (b : Basis ι ℤ_[p] M) :
    Associated (toMatrix₂ b b B).det ((p : ℤ_[p]) ^ ∑ᶠ j, j * finrank ℤ_[p] (N j)) := by
  rcases h.exists_forall_eq_bot with ⟨J, hJ⟩
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range J) fun j hj ↦ ?_, Finset.sum_range]
  · exact h.associated_det_of_forall_eq_bot hJ b
  · by_contra hjJ
    rw [Finset.coe_range, Set.mem_Iio, not_lt] at hjJ
    exact Function.mem_support.mp hj (by rw [hJ j hjJ, finrank_bot, mul_zero])

end LinearMap.BilinForm

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V) [L.IsNondegenerate]
  (p : ℕ) [Fact p.Prime]

/-- **The Jordan ranks determine the valuation of the determinant**: the `p`-adic valuation of the
determinant of a nondegenerate integral lattice is `∑_k k n_k`, `n_k` the rank of the constituent of
scale `p ^ k` of its `p`-adic Jordan decompositions. -/
lemma factorization_natAbs_determinant :
    L.determinant.natAbs.factorization p = ∑ᶠ k, k * L.jordanRank p k := by
  classical
  have hassoc :
      Associated (L.determinant : ℤ_[p]) ((p : ℤ_[p]) ^ ∑ᶠ k, k * L.jordanRank p k) := by
    rw [← L.det_toMatrix_localIntegralForm p (Free.chooseBasis ℤ L)]
    exact (L.exists_isJordanSplitting_localIntegralForm p
      L.form_nondegenerate).choose_spec.associated_det _
  have hd : L.determinant.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (L.determinant_ne_zero_iff.mpr L.form_nondegenerate)
  have hdvd (m : ℕ) : p ^ m ∣ L.determinant.natAbs ↔ m ≤ ∑ᶠ k, k * L.jordanRank p k := by
    rcases hassoc.symm with ⟨u, hu⟩
    rw [← Int.natCast_dvd, Nat.cast_pow, ← PadicInt.norm_int_le_pow_iff_dvd, ← hu, norm_mul,
      PadicInt.isUnit_iff.mp u.isUnit, mul_one, PadicInt.norm_p_pow,
      zpow_le_zpow_iff_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt), neg_le_neg_iff,
      Nat.cast_le]
  exact le_antisymm ((hdvd _).mp (((Fact.out : p.Prime).pow_dvd_iff_le_factorization hd).mpr
    le_rfl)) (((Fact.out : p.Prime).pow_dvd_iff_le_factorization hd).mp ((hdvd _).mpr le_rfl))

/-- **The Jordan constituents of a lattice have scales dividing its determinant**: the rank of the
constituent of scale `p ^ k` vanishes when `k` exceeds the `p`-adic valuation of the determinant. -/
lemma jordanRank_eq_zero_of_lt {k : ℕ} (hk : L.determinant.natAbs.factorization p < k) :
    L.jordanRank p k = 0 := by
  by_contra hne
  have hzero (S : Submodule ℤ_[p] (L.LocalCarrier p)) (hS : S = ⊥) : finrank ℤ_[p] S = 0 :=
    hS ▸ finrank_bot ℤ_[p] _
  have hfin : (Function.support fun k ↦ k * L.jordanRank p k).Finite :=
    (L.exists_isJordanSplitting_localIntegralForm p
      L.form_nondegenerate).choose_spec.hasFiniteSupport.subset
      fun k hk hbot ↦ hk (by simp only [jordanRank, hzero _ hbot, mul_zero])
  have hle : k * L.jordanRank p k ≤ L.determinant.natAbs.factorization p :=
    L.factorization_natAbs_determinant p ▸ single_le_finsum k hfin fun _ ↦ Nat.zero_le _
  have hkn : k ≤ k * L.jordanRank p k := Nat.le_mul_of_pos_right k (Nat.pos_of_ne_zero hne)
  omega

end TauCeti.IntegralLattice
