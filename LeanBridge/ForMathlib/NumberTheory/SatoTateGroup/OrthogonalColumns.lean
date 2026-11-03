import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.OrthogonalCommutant
import TauCeti.GroupTheory.Perm.FiberSubgroup
import TauCeti.RepresentationTheory.Symmetric.SignCharacter
import TauCeti.RepresentationTheory.SubgroupCharSum

/-!
# Column antisymmetrisers on tensor powers

The two factors of a Young symmetrizer, as operators of a representation of the permutations of the
slots: the column antisymmetriser and the row symmetriser, Tau Ceti's character sums
(`TauCeti.subgroupCharSum`) over the permutations preserving a family of fibres. On a tensor power
of a matrix `A`, the trace of the column antisymmetriser is a product over the columns of sums of
principal minors of `A`, so of elementary symmetric functions of its eigenvalues. This is what
relates the tensor powers to the monomials in the elementary symmetric functions.

## Main definitions

* `SatoTateGroup.columnOp`: the column antisymmetriser.
* `SatoTateGroup.rowOp`: the row symmetriser.

## Main results

* `SatoTateGroup.columnOp_mul_mul_rowOp_eq_zero`, `SatoTateGroup.rowOp_mul_mul_columnOp_eq_zero`:
  their products vanish, through a permutation, when two slots lie in a common row and a common
  column.
* `SatoTateGroup.sum_sum_sign_mul_tensorRep`: the trace of a column antisymmetriser on a tensor
  power of a matrix.
-/

open Equiv Matrix TauCeti

namespace SatoTateGroup

variable {P K L M I S : Type*} [Fintype P] [DecidableEq P] [DecidableEq K] [DecidableEq L]
  [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (Perm P) M) (col : P → K) (row : P → L)

instance : DecidablePred (· ∈ fiberSubgroup col) :=
  fun q ↦ inferInstanceAs (Decidable (∀ a, col (q a) = col a))

/-- The **column antisymmetriser** of the columns `col` on a representation of the permutations of
the slots: the signed sum of the permutations preserving the columns. -/
noncomputable def columnOp : Module.End ℂ M :=
  ρ.asAlgebraHom
    (subgroupCharSum ((Units.coeHom ℂ).comp (signLinearCharacter ℂ P)) (fiberSubgroup col))

/-- The **row symmetriser** of the rows `row`: the sum of the permutations preserving the rows. -/
noncomputable def rowOp : Module.End ℂ M :=
  ρ.asAlgebraHom (subgroupCharSum 1 (fiberSubgroup row))

lemma columnOp_eq_sum :
    columnOp ρ col = ∑ q : fiberSubgroup col, ((Perm.sign (q : Perm P) : ℤ) : ℂ) • ρ q :=
  LinearMap.ext fun x ↦ (asAlgebraHom_subgroupCharSum_apply _ _ ρ x).trans (by simp)

lemma rowOp_eq_sum : rowOp ρ row = ∑ p : fiberSubgroup row, ρ p :=
  LinearMap.ext fun x ↦ (asAlgebraHom_subgroupCharSum_apply _ _ ρ x).trans (by simp)

lemma sign_mul_self_cast (q : Perm P) : ((Perm.sign q : ℤ) : ℂ) * ((Perm.sign q : ℤ) : ℂ) = 1 := by
  rw [← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]

lemma coeHom_comp_signLinearCharacter_inv (τ : Perm P) :
    (Units.coeHom ℂ).comp (signLinearCharacter ℂ P) τ⁻¹ = ((Perm.sign τ : ℤ) : ℂ) := by
  simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply,
    coe_signLinearCharacter_apply, Perm.sign_inv]

variable {col row} in
lemma columnOp_mul_of_mem {τ : Perm P} (hτ : τ ∈ fiberSubgroup col) :
    columnOp ρ col * ρ τ = ((Perm.sign τ : ℤ) : ℂ) • columnOp ρ col := by
  rw [columnOp, ← ρ.asAlgebraHom_single_one τ, ← map_mul, subgroupCharSum_mul_single _ _ ⟨τ, hτ⟩,
    map_smul, coeHom_comp_signLinearCharacter_inv]

lemma columnOp_mul_self :
    columnOp ρ col * columnOp ρ col = (Fintype.card (fiberSubgroup col) : ℂ) • columnOp ρ col := by
  rw [columnOp, ← map_mul, subgroupCharSum_mul_self, map_nsmul, Nat.card_eq_fintype_card,
    Nat.cast_smul_eq_nsmul]

lemma commute_columnOp {x : Module.End ℂ M} (h : ∀ σ, Commute x (ρ σ)) :
    Commute x (columnOp ρ col) :=
  ρ.commute_asAlgebraHom_of_forall_commute h _

variable {col row} in
lemma mul_rowOp_of_mem {τ : Perm P} (hτ : τ ∈ fiberSubgroup row) :
    ρ τ * rowOp ρ row = rowOp ρ row := by
  rw [rowOp, ← ρ.asAlgebraHom_single_one τ, ← map_mul, single_mul_subgroupCharSum _ _ ⟨τ, hτ⟩]
  simp

lemma eq_zero_of_eq_neg {V : Type*} [AddCommGroup V] [Module ℂ V] {x : V} (h : x = -x) : x = 0 := by
  have h₁ : (2 : ℂ) • x = 0 := by
    rw [two_smul]
    nth_rw 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h₁).resolve_left two_ne_zero

variable {col row} in
/-- **The sandwich vanishes when a row meets a column twice.** -/
lemma columnOp_mul_mul_rowOp_eq_zero (σ : Perm P) {x y : P} (hxy : x ≠ y) (hr : row x = row y)
    (hc : col (σ x) = col (σ y)) : columnOp ρ col * ρ σ * rowOp ρ row = 0 := by
  have h₁ : Equiv.swap x y ∈ fiberSubgroup row := swap_mem_fiberSubgroup hr
  have h₂ : Equiv.swap (σ x) (σ y) ∈ fiberSubgroup col := swap_mem_fiberSubgroup hc
  have h₃ : Perm.sign (Equiv.swap (σ x) (σ y)) = -1 :=
    Perm.sign_swap fun h ↦ hxy (σ.injective h)
  have h₄ : ρ σ * ρ (Equiv.swap x y) = ρ (Equiv.swap (σ x) (σ y)) * ρ σ := by
    rw [← map_mul, ← map_mul, mul_swap_eq_swap_mul]
  refine eq_zero_of_eq_neg ?_
  nth_rw 1 [← mul_rowOp_of_mem ρ h₁]
  rw [← mul_assoc, mul_assoc (columnOp ρ col), h₄, ← mul_assoc (columnOp ρ col),
    columnOp_mul_of_mem ρ h₂, h₃]
  simp

variable {col row} in
lemma mul_columnOp_of_mem {τ : Perm P} (hτ : τ ∈ fiberSubgroup col) :
    ρ τ * columnOp ρ col = ((Perm.sign τ : ℤ) : ℂ) • columnOp ρ col := by
  rw [columnOp, ← ρ.asAlgebraHom_single_one τ, ← map_mul, single_mul_subgroupCharSum _ _ ⟨τ, hτ⟩,
    map_smul, coeHom_comp_signLinearCharacter_inv]

variable {col row} in
lemma rowOp_mul_of_mem {τ : Perm P} (hτ : τ ∈ fiberSubgroup row) :
    rowOp ρ row * ρ τ = rowOp ρ row := by
  rw [rowOp, ← ρ.asAlgebraHom_single_one τ, ← map_mul, subgroupCharSum_mul_single _ _ ⟨τ, hτ⟩]
  simp

variable {col row} in
/-- **The sandwich vanishes when a column meets a row twice.** -/
lemma rowOp_mul_mul_columnOp_eq_zero (σ : Perm P) {x y : P} (hxy : x ≠ y) (hc : col x = col y)
    (hr : row (σ x) = row (σ y)) : rowOp ρ row * ρ σ * columnOp ρ col = 0 := by
  have h₁ : Equiv.swap x y ∈ fiberSubgroup col := swap_mem_fiberSubgroup hc
  have h₂ : Equiv.swap (σ x) (σ y) ∈ fiberSubgroup row := swap_mem_fiberSubgroup hr
  have h₃ : Perm.sign (Equiv.swap x y) = -1 := Perm.sign_swap hxy
  have h₄ : ρ σ * ρ (Equiv.swap x y) = ρ (Equiv.swap (σ x) (σ y)) * ρ σ := by
    rw [← map_mul, ← map_mul, mul_swap_eq_swap_mul]
  refine eq_zero_of_eq_neg ?_
  nth_rw 1 [← rowOp_mul_of_mem ρ h₂]
  rw [mul_assoc (rowOp ρ row) (ρ (Equiv.swap (σ x) (σ y))), ← h₄, ← mul_assoc,
    mul_assoc _ (ρ (Equiv.swap x y)), mul_columnOp_of_mem ρ h₁, h₃]
  simp

variable [Fintype I] [DecidableEq I] in
lemma trace_columnOp_mul_mulVecLin (T : Matrix (P → I) (P → I) ℂ) :
    LinearMap.trace ℂ _ (columnOp (slotRep P I) col * T.mulVecLin) = ∑ a : P → I,
      ∑ q : fiberSubgroup col, ((Perm.sign (q : Perm P) : ℤ) : ℂ) * T (a ∘ q) a := by
  have h₁ (q : Perm P) : slotRep P I q * T.mulVecLin = (T.submatrix (· ∘ q) id).mulVecLin := rfl
  have h₂ (q : Perm P) :
      LinearMap.trace ℂ _ (slotRep P I q * T.mulVecLin) = ∑ a : P → I, T (a ∘ q) a := by
    rw [h₁, ← toLin'_apply', trace_toLin'_eq]
    rfl
  rw [columnOp_eq_sum, Finset.sum_mul, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [smul_mul_assoc, map_smul, h₂, smul_eq_mul, Finset.mul_sum]

variable [Fintype K]

lemma sign_coe_fiberSubgroup (q : fiberSubgroup col) :
    Perm.sign (q : Perm P) = ∏ k, Perm.sign (fiberSubgroupMulEquivPiPerm col q k) := by
  let φ₁ : (∀ k, Perm {p // col p = k}) →* ℤˣ :=
    Perm.sign.comp ((fiberSubgroup col).subtype.comp
      (fiberSubgroupMulEquivPiPerm col).symm.toMonoidHom)
  let φ₂ : (∀ k, Perm {p // col p = k}) →* ℤˣ := ∏ k, Perm.sign.comp (Pi.evalMonoidHom _ k)
  have hφ₂ (Q : ∀ k, Perm {p // col p = k}) : φ₂ Q = ∏ k, Perm.sign (Q k) :=
    MonoidHom.finsetProd_apply ..
  have h₁ : φ₁ = φ₂ := by
    refine MonoidHom.pi_ext fun k r ↦ ?_
    have h₂ : ((fiberSubgroupMulEquivPiPerm col).symm (Pi.mulSingle k r) : Perm P) =
        Perm.ofSubtype r := by
      ext p
      rw [fiberSubgroupMulEquivPiPerm_symm_apply]
      by_cases hp : col p = k
      · subst hp
        rw [Pi.mulSingle_eq_same, Perm.ofSubtype_apply_of_mem r rfl]
      · rw [Pi.mulSingle_eq_of_ne hp, Perm.ofSubtype_apply_of_not_mem r hp]
        rfl
    rw [hφ₂, Finset.prod_eq_single k (fun l _ hl ↦ by rw [Pi.mulSingle_eq_of_ne hl, map_one])
      (by simp), Pi.mulSingle_eq_same]
    exact (congrArg Perm.sign h₂).trans (Perm.sign_ofSubtype r)
  rw [← hφ₂, ← h₁]
  simp [φ₁]

lemma sum_sign_mul_prod_eq_prod_det (A : Matrix I I ℂ) (a : P → I) : ∑ q : fiberSubgroup col,
    ((Perm.sign (q : Perm P) : ℤ) : ℂ) * ∏ p, A (a ((q : Perm P) p)) (a p) =
      ∏ k, (A.submatrix (fun x : {p // col p = k} ↦ a x.1) fun x ↦ a x.1).det := by
  simp only [det_apply']
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Fintype.sum_equiv (fiberSubgroupMulEquivPiPerm col).toEquiv _ _ fun q ↦ ?_
  rw [Finset.prod_mul_distrib, sign_coe_fiberSubgroup]
  congr 1
  · push_cast
    rfl
  · rw [← Fintype.prod_fiberwise col]
    refine Finset.prod_congr rfl fun k _ ↦ Finset.prod_congr rfl fun x _ ↦ ?_
    have h₁ : ((fiberSubgroupMulEquivPiPerm col q k) x : P) = (q : Perm P) x :=
      fiberSubgroupMulEquivPiPerm_apply_coe col q k x
    rw [← h₁]
    rfl

variable [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]

lemma sum_det_submatrix_eq_sum_powersetCard (A : Matrix I I ℂ) : ∑ b : S → I,
    (A.submatrix b b).det = (Fintype.card S).factorial *
      ∑ s ∈ Finset.powersetCard (Fintype.card S) Finset.univ,
        (A.submatrix (Subtype.val : s → I) (Subtype.val : s → I)).det := by
  have h₁ : ∑ b : S → I, (A.submatrix b b).det =
      ∑ b ∈ Finset.univ.filter fun b : S → I ↦ Function.Injective b, (A.submatrix b b).det := by
    refine (Finset.sum_filter_of_ne fun b _ hb ↦ ?_).symm
    by_contra hinj
    rcases Function.not_injective_iff.mp hinj with ⟨x, y, hxy, hne⟩
    exact hb (det_zero_of_row_eq hne (funext fun j ↦ by simp only [submatrix_apply, hxy]))
  have hmaps : ∀ b ∈ (Finset.univ.filter fun b : S → I ↦ Function.Injective b),
      Finset.univ.image b ∈ Finset.powersetCard (Fintype.card S) (Finset.univ : Finset I) := by
    intro b hb
    refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injective _ (Finset.mem_filter.mp hb).2, Finset.card_univ]
  rw [h₁, ← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  have hcard : Fintype.card S = Fintype.card s := by
    rw [Fintype.card_coe, (Finset.mem_powersetCard.mp hs).2]
  let ι : (S ≃ s) → S → I := fun e x ↦ (e x).1
  have hι : Function.Injective ι := fun e e' h ↦ Equiv.ext fun x ↦ Subtype.ext (congrFun h x)
  have himage : ((Finset.univ.filter fun b : S → I ↦ Function.Injective b).filter
      fun b ↦ Finset.univ.image b = s) = Finset.univ.image ι := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hb, hb'⟩
      have hmem (x : S) : b x ∈ s := hb' ▸ Finset.mem_image_of_mem b (Finset.mem_univ x)
      refine ⟨ofBijective (fun x ↦ (⟨b x, hmem x⟩ : s)) ?_, rfl⟩
      refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun x y h ↦ hb ?_, hcard⟩
      exact congrArg Subtype.val h
    · rintro ⟨e, -, rfl⟩
      refine ⟨fun x y h ↦ e.injective (Subtype.ext h), ?_⟩
      ext i
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨x, rfl⟩
        exact (e x).2
      · intro hi
        exact ⟨e.symm ⟨i, hi⟩, by simp [ι]⟩
  rw [himage, Finset.sum_image fun e _ e' _ h ↦ hι h]
  have h₂ (e : S ≃ s) : (A.submatrix (ι e) (ι e)).det =
      (A.submatrix (Subtype.val : s → I) (Subtype.val : s → I)).det :=
    det_submatrix_equiv_self e (A.submatrix (Subtype.val : s → I) (Subtype.val : s → I))
  simp only [h₂]
  have h₃ : Nonempty (S ≃ s) := ⟨Fintype.equivOfCardEq hcard⟩
  rcases h₃ with ⟨e₀⟩
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_equiv e₀, nsmul_eq_mul]

lemma esymm_roots_charpoly_eq_zero (A : Matrix I I ℂ) {n : ℕ} (hn : Fintype.card I < n) :
    A.charpoly.roots.esymm n = 0 :=
  Multiset.esymm_of_card_lt ((Polynomial.card_roots' _).trans_lt (by
    rwa [charpoly_natDegree_eq_dim]))

lemma esymm_roots_charpoly_eq_sum (A : Matrix I I ℂ) (n : ℕ) : A.charpoly.roots.esymm n =
    ∑ s ∈ Finset.powersetCard n Finset.univ,
      (A.submatrix (Subtype.val : s → I) (Subtype.val : s → I)).det := by
  rcases le_or_gt n (Fintype.card I) with hn | hn
  · have h₁ : A.charpoly.coeff (Fintype.card I - n) = (-1) ^ n * A.charpoly.roots.esymm n := by
      rw [Polynomial.coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits A.charpoly) (by simp),
        A.charpoly_monic.leadingCoeff, charpoly_natDegree_eq_dim, Nat.sub_sub_self hn, one_mul]
    exact mul_left_cancel₀ (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero))
      (h₁.symm.trans (A.charpoly_coeff_eq_sum_minors n hn))
  · have h₁ : Finset.powersetCard n (Finset.univ : Finset I) = ∅ :=
      Finset.powersetCard_eq_empty.mpr (by rwa [Finset.card_univ])
    rw [h₁, Finset.sum_empty, esymm_roots_charpoly_eq_zero A hn]

lemma sum_det_submatrix (A : Matrix I I ℂ) : ∑ b : S → I, (A.submatrix b b).det =
    (Fintype.card S).factorial * A.charpoly.roots.esymm (Fintype.card S) := by
  rw [sum_det_submatrix_eq_sum_powersetCard, esymm_roots_charpoly_eq_sum]

/-- **The trace of a column antisymmetriser on a tensor power of a matrix** is the product over the
columns of the elementary symmetric functions of the eigenvalues, up to factorials. -/
lemma sum_sum_sign_mul_tensorRep (A : Matrix I I ℂ) : ∑ a : P → I, ∑ q : fiberSubgroup col,
    ((Perm.sign (q : Perm P) : ℤ) : ℂ) * tensorRep A (a ∘ q) a =
      ∏ k, ((Fintype.card {p // col p = k}).factorial *
        A.charpoly.roots.esymm (Fintype.card {p // col p = k})) := by
  let E : (P → I) ≃ ∀ k, {p // col p = k} → I :=
    (arrowCongr (sigmaFiberEquiv col).symm (Equiv.refl I)).trans (piCurry fun _ _ ↦ I)
  simp only [← sum_det_submatrix, Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [← E.sum_comp]
  exact Finset.sum_congr rfl fun a _ ↦ sum_sign_mul_prod_eq_prod_det col A a

end SatoTateGroup
