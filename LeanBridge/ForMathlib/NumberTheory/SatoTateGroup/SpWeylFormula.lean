import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.KoikeTerada
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.SpTensor
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Weyl's character formula for the symplectic Lie algebra, evaluated on the torus

Evaluating the group algebra of the weights at an element `X` of the Cartan subalgebra, by
`e^μ ↦ exp μ(X)`, turns Tau Ceti's Weyl character formula for `𝔰𝔭(2g, ℂ)` into the classical
quotient of determinants `det(x_j^{λᵢ + g - i} - x_j^{-(λᵢ + g - i)})`, which is the formula of
`SatoTateGroup.symplecticSchur_mul_det` for the Koike–Terada function.

## Main definitions

* `SatoTateGroup.spEval`: the evaluation of the group algebra of the weights at an element of the
  Cartan subalgebra.

## Main results

* `SatoTateGroup.spEval_weylNumerator`: the evaluation of the Weyl numerator is a determinant.
* `SatoTateGroup.spEval_formalCharacter_mul_det`: the classical form of Weyl's character formula.
-/

open Equiv LieAlgebra LieModule Matrix Module TauCeti

namespace SatoTateGroup

variable {g : ℕ}

/-- The character `μ ↦ exp μ(X)` of the group of weights. -/
noncomputable def spExpChar (X : spCartan (g := g)) :
    Multiplicative (Dual ℂ (spCartan (g := g))) →* ℂ where
  toFun μ := Complex.exp (Multiplicative.toAdd μ X)
  map_one' := by
    simp
  map_mul' μ ν := by
    simp [Complex.exp_add]

/-- The **evaluation** `e^μ ↦ exp μ(X)` of the group algebra of the weights at an element `X` of the
Cartan subalgebra. -/
noncomputable def spEval (X : spCartan (g := g)) :
    AddMonoidAlgebra ℤ (Dual ℂ (spCartan (g := g))) →ₐ[ℤ] ℂ :=
  AddMonoidAlgebra.lift ℤ ℂ _ (spExpChar X)

lemma spEval_single (X : spCartan (g := g)) (μ : Dual ℂ (spCartan (g := g))) (n : ℤ) :
    spEval X (AddMonoidAlgebra.single μ n) = n * Complex.exp (μ X) := by
  rw [spEval, AddMonoidAlgebra.lift_single, zsmul_eq_mul]
  rfl

section

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Finite ι] [CharZero R] [IsDomain R] [Invertible (2 : R)] (P : RootPairing ι R M N)
  [P.IsCrystallographic] [P.IsReduced] [Fintype P.weylGroup] (b : P.Base)

lemma lift_weylNumerator (F : Multiplicative M →* ℂ) (lam : M) :
    AddMonoidAlgebra.lift ℤ ℂ M F (weylNumerator P b lam) =
      (∑ w : P.weylGroup, ((weylSign P b w : ℤ) : ℂ) *
        F (Multiplicative.ofAdd (w • (lam + weylVector P b)))) *
          F (Multiplicative.ofAdd (-weylVector P b)) := by
  rw [weylNumerator_def, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [AddMonoidAlgebra.lift_single, zsmul_eq_mul, dotAction_def, sub_eq_add_neg, ofAdd_add, map_mul,
    mul_assoc]

end

lemma spAct_spDiag (π : Equiv.Perm (Fin g)) (s : Fin g → ℤˣ) (y : Dual ℂ (spCartan (g := g)))
    (θ : Fin g → ℂ) : spAct π s y ⟨spDiag θ, spDiag_mem_spCartan θ⟩ =
      ∑ i, ((s i : ℤ) : ℂ) * y (spDelta i) * θ (π i) := by
  rw [spAct, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [LinearMap.smul_apply, spEpsilon_spDiag, smul_eq_mul]

lemma sum_units_mul_exp (v : ℕ) (t : ℂ) : ∑ u : ℤˣ,
    ((u : ℤ) : ℂ) * Complex.exp (((u : ℤ) : ℂ) * v * t) =
      Complex.exp t ^ v - (Complex.exp t)⁻¹ ^ v := by
  have h₁ : (Finset.univ : Finset ℤˣ) = {1, -1} := rfl
  rw [h₁, Finset.sum_pair (by decide), ← Complex.exp_nat_mul, ← Complex.exp_neg,
    ← Complex.exp_nat_mul]
  simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_mul, mul_neg,
    sub_eq_add_neg]

lemma sum_spSign_mul_exp (π : Equiv.Perm (Fin g)) (v : Fin g → ℕ) (θ : Fin g → ℂ) :
    ∑ s : Fin g → ℤˣ, ((spSign π s : ℤ) : ℂ) *
        Complex.exp (∑ i, ((s i : ℤ) : ℂ) * (v i : ℂ) * θ (π i)) =
      ((Perm.sign π : ℤ) : ℂ) *
        ∏ i, weylEntry (fun k ↦ Complex.exp (θ k)) (π i) (v i) := by
  have h₁ (s : Fin g → ℤˣ) : ((spSign π s : ℤ) : ℂ) *
      Complex.exp (∑ i, ((s i : ℤ) : ℂ) * (v i : ℂ) * θ (π i)) =
        ((Perm.sign π : ℤ) : ℂ) *
          ∏ i, (((s i : ℤ) : ℂ) * Complex.exp (((s i : ℤ) : ℂ) * (v i : ℂ) * θ (π i))) := by
    rw [spSign, Complex.exp_sum, Finset.prod_mul_distrib, ← mul_assoc]
    push_cast
    rfl
  simp only [h₁, ← Finset.mul_sum]
  congr 1
  have h₂ : ∏ i, weylEntry (fun k ↦ Complex.exp (θ k)) (π i) (v i) =
      ∏ i, ∑ u : ℤˣ, ((u : ℤ) : ℂ) * Complex.exp (((u : ℤ) : ℂ) * (v i : ℂ) * θ (π i)) :=
    Finset.prod_congr rfl fun i _ ↦ (sum_units_mul_exp (v i) (θ (π i))).symm
  rw [h₂, Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma det_weylEntry_eq_sum (v : Fin g → ℕ) (θ : Fin g → ℂ) :
    (of fun i j : Fin g ↦ weylEntry (fun k ↦ Complex.exp (θ k)) j (v i)).det =
      ∑ π : Equiv.Perm (Fin g), ((Perm.sign π : ℤ) : ℂ) *
        ∏ i, weylEntry (fun k ↦ Complex.exp (θ k)) (π i) (v i) := by
  rw [← det_transpose, det_apply']
  rfl

/-- **The evaluation of the Weyl numerator is a determinant.** -/
lemma spEval_weylNumerator [Fintype (spRootSystem g).weylGroup] (lam : Dual ℂ (spCartan (g := g)))
    (v : Fin g → ℕ) (hv : ∀ i, (lam + weylVector (spRootSystem g) spBase) (spDelta i) = v i)
    (θ : Fin g → ℂ) :
    spEval ⟨spDiag θ, spDiag_mem_spCartan θ⟩ (weylNumerator (spRootSystem g) spBase lam) =
      (of fun i j : Fin g ↦ weylEntry (fun k ↦ Complex.exp (θ k)) j (v i)).det *
        Complex.exp (-weylVector (spRootSystem g) spBase ⟨spDiag θ, spDiag_mem_spCartan θ⟩) := by
  refine (lift_weylNumerator (spRootSystem g) spBase _ lam).trans (congrArg₂ _ ?_ rfl)
  refine (sum_weylGroup_eq (fun μ ↦ Complex.exp (μ ⟨spDiag θ, spDiag_mem_spCartan θ⟩)) _).trans ?_
  rw [det_weylEntry_eq_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun π _ ↦ ?_
  rw [← sum_spSign_mul_exp π v θ]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [spAct_spDiag, hv]

section

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule (Symplectic.sp (Fin g) ℂ) M]
  [LieModule ℂ (Symplectic.sp (Fin g) ℂ) M] [FiniteDimensional ℂ M]

lemma trace_eq_spEval_formalCharacter (X : spCartan (g := g)) {φ : M →ₗ[ℂ] M}
    (hφ : ∀ (μ : Weight ℂ (spCartan (g := g)) M) (v : M),
      v ∈ genWeightSpace M (μ : spCartan (g := g) → ℂ) →
        φ v = Complex.exp ((μ : Dual ℂ (spCartan (g := g))) X) • v) :
    LinearMap.trace ℂ M φ = spEval X (formalCharacter ℂ (spCartan (g := g)) M) := by
  classical
  have hmaps (μ : Weight ℂ (spCartan (g := g)) M) : Set.MapsTo φ
      (genWeightSpace M (μ : spCartan (g := g) → ℂ)).toSubmodule
      (genWeightSpace M (μ : spCartan (g := g) → ℂ)).toSubmodule := fun v hv ↦ by
    rw [SetLike.mem_coe, hφ μ v hv]
    exact Submodule.smul_mem _ _ hv
  rw [LinearMap.trace_eq_sum_trace_restrict (isInternal_genWeightSpace ℂ (spCartan (g := g)) M)
    hmaps, formalCharacter_eq_sum_single, map_sum]
  refine Finset.sum_congr rfl fun μ _ ↦ ?_
  have h₁ :
      φ.restrict (hmaps μ) = Complex.exp ((μ : Dual ℂ (spCartan (g := g))) X) • LinearMap.id :=
    LinearMap.ext fun v ↦ Subtype.ext (hφ μ v v.2)
  rw [h₁, map_smul, LinearMap.trace_id, spEval_single, smul_eq_mul, mul_comm]
  rfl

end

instance : IsEmpty (YoungBox (0 : Fin g → ℕ)) :=
  ⟨fun p ↦ p.1.2.elim0⟩

lemma lieSpan_youngVector_zero : LieSubmodule.lieSpan ℂ (Symplectic.sp (Fin g) ℂ)
    {youngVector (g := g) (0 : Fin g → ℕ)} = ⊤ := by
  refine eq_top_iff.mpr fun f _ ↦ ?_
  have h₁ : youngVector (g := g) (0 : Fin g → ℕ) (fun p ↦ Sum.inl p.2.1) = 1 := by
    simp [youngVector, columnTensor]
  have h₂ : f = f (fun p ↦ Sum.inl p.2.1) • youngVector (g := g) (0 : Fin g → ℕ) := by
    funext a
    have h₃ : a = fun p ↦ Sum.inl p.2.1 := Subsingleton.elim _ _
    subst h₃
    exact (mul_one _).symm.trans (congrArg _ h₁.symm)
  rw [h₂]
  exact Submodule.smul_mem _ _ (LieSubmodule.subset_lieSpan rfl)

lemma tensorAction_of_isEmpty {P I : Type*} [Fintype P] [DecidableEq P] [DecidableEq I] [IsEmpty P]
    (X : Matrix I I ℂ) : tensorAction (P := P) X = 0 :=
  Finset.sum_of_isEmpty _

lemma spEval_formalCharacter_zero (X : spCartan (g := g)) : spEval X
    (formalCharacter ℂ (spCartan (g := g)) (SpTensor (YoungBox (0 : Fin g → ℕ)) g)) = 1 := by
  have h₁ : LinearMap.trace ℂ (SpTensor (YoungBox (0 : Fin g → ℕ)) g) LinearMap.id = 1 := by
    rw [LinearMap.trace_id]
    have h₂ : Module.finrank ℂ (SpTensor (YoungBox (0 : Fin g → ℕ)) g) = 1 :=
      (Module.finrank_fintype_fun_eq_card ℂ).trans (Fintype.card_unique)
    rw [h₂, Nat.cast_one]
  rw [← h₁]
  refine (trace_eq_spEval_formalCharacter X fun μ v hv ↦ ?_).symm
  have h₂ :
      v ∈ weightSpace (SpTensor (YoungBox (0 : Fin g → ℕ)) g) (μ : spCartan (g := g) → ℂ) := by
    rwa [← genWeightSpace_eq_weightSpace]
  by_cases hv₀ : v = 0
  · rw [hv₀, map_zero, smul_zero]
  · have h₃ : ⁅(X : Symplectic.sp (Fin g) ℂ), v⁆ = (0 : SpTensor _ g) := by
      rw [lie_spTensor_def, tensorAction_of_isEmpty]
      exact zero_mulVec _
    have h₄ : (μ : Dual ℂ (spCartan (g := g))) X • v = 0 :=
      ((mem_weightSpace _ _).mp h₂ X).symm.trans h₃
    rw [(smul_eq_zero.mp h₄).resolve_right hv₀, Complex.exp_zero, one_smul]
    rfl

lemma spEval_weylDenominator (θ : Fin g → ℂ) :
    spEval ⟨spDiag θ, spDiag_mem_spCartan θ⟩ (weylDenominator (spRootSystem g) spBase) =
      (of fun i j : Fin g ↦ weylEntry (fun k ↦ Complex.exp (θ k)) j (g - i)).det *
        Complex.exp (-weylVector (spRootSystem g) spBase ⟨spDiag θ, spDiag_mem_spCartan θ⟩) := by
  have : Finite (spRootSystem g).weylGroup := RootPairing.finite_weylGroup _
  let : Fintype (spRootSystem g).weylGroup := Fintype.ofFinite _
  have h₁ : spEval ⟨spDiag θ, spDiag_mem_spCartan θ⟩ (formalCharacter ℂ (spCartan (g := g))
      (SpTensor (YoungBox (0 : Fin g → ℕ)) g) * weylDenominator (spRootSystem g) spBase) =
        spEval ⟨spDiag θ, spDiag_mem_spCartan θ⟩ (weylNumerator (spRootSystem g) spBase
          (spPartitionWeight (0 : Fin g → ℕ))) :=
    congrArg _ (formalCharacter_mul_weylDenominator_eq_weylNumerator
      (isHighestWeightVector_youngVector (g := g) (0 : Fin g → ℕ)) lieSpan_youngVector_zero)
  have h₂ : ∀ i : Fin g, (spPartitionWeight (0 : Fin g → ℕ) +
      weylVector (spRootSystem g) spBase) (spDelta i) =
        ((fun i : Fin g ↦ g - (i : ℕ)) i : ℂ) := fun i ↦ by
    rw [LinearMap.add_apply, spPartitionWeight_spDelta, weylVector_spDelta]
    simp [highestWeight]
  rwa [map_mul, spEval_formalCharacter_zero, one_mul, spEval_weylNumerator _ _ h₂] at h₁

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule (Symplectic.sp (Fin g) ℂ) M]
  [LieModule ℂ (Symplectic.sp (Fin g) ℂ) M] [FiniteDimensional ℂ M]

/-- **Weyl's character formula as a quotient of determinants.** The evaluation of the formal
character of the module generated by a highest weight vector. -/
lemma spEval_formalCharacter_mul_det (c : Fin g → ℕ) {v : M}
    (hv : IsHighestWeightVector spBase (spPartitionWeight c) v)
    (hgen : LieSubmodule.lieSpan ℂ (Symplectic.sp (Fin g) ℂ) {v} = ⊤) (θ : Fin g → ℂ) :
    spEval ⟨spDiag θ, spDiag_mem_spCartan θ⟩ (formalCharacter ℂ (spCartan (g := g)) M) *
        (of fun i j : Fin g ↦ weylEntry (fun k ↦ Complex.exp (θ k)) j (g - i)).det =
      (of fun i j : Fin g ↦
        weylEntry (fun k ↦ Complex.exp (θ k)) j (highestWeight c i + g - i)).det := by
  have : Finite (spRootSystem g).weylGroup := RootPairing.finite_weylGroup _
  let : Fintype (spRootSystem g).weylGroup := Fintype.ofFinite _
  have h₁ : spEval ⟨spDiag θ, spDiag_mem_spCartan θ⟩ (formalCharacter ℂ (spCartan (g := g)) M *
      weylDenominator (spRootSystem g) spBase) = spEval ⟨spDiag θ, spDiag_mem_spCartan θ⟩
        (weylNumerator (spRootSystem g) spBase (spPartitionWeight c)) :=
    congrArg _ (formalCharacter_mul_weylDenominator_eq_weylNumerator hv hgen)
  have h₃ : ∀ i : Fin g, (spPartitionWeight c + weylVector (spRootSystem g) spBase) (spDelta i) =
      ((fun i : Fin g ↦ highestWeight c i + g - (i : ℕ)) i : ℂ) := fun i ↦ by
    rw [LinearMap.add_apply, spPartitionWeight_spDelta, weylVector_spDelta]
    simp only [Nat.add_sub_assoc i.2.le, Nat.cast_add]
  rw [map_mul, spEval_weylDenominator, spEval_weylNumerator _ _ h₃, ← mul_assoc] at h₁
  exact mul_right_cancel₀ (Complex.exp_ne_zero _) h₁

end SatoTateGroup
