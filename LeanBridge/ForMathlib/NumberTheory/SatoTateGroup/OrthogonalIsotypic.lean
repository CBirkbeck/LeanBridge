import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.OrthogonalColumns

/-!
# Isotypic projectors on the tensor powers of the ambient group

The isotypic projector of an irreducible character `χ` of the ambient group on a tensor power of the
standard representation, as a matrix. A column antisymmetriser kills it exactly when `χ` does not
occur in the product of the elementary symmetric functions of the lengths of the columns, by the
trace formula for column antisymmetrisers. In even weight, the projector is compatible with the
cups, the tensors `δ_{a p, a q} y`, and a column antisymmetriser kills such a tensor if `p` and `q`
lie in one column, and otherwise if the antisymmetriser of the other slots kills `y`.

## Main definitions

* `SatoTateGroup.cupEquiv`: the tuples of indices, by their values at two slots and on the others.
* `SatoTateGroup.cupMap`: the cup at two slots of a tensor of the other slots.

## Main results

* `SatoTateGroup.isotypicMatrix_mul_eq_zero`: the projectors of distinct characters are orthogonal.
* `SatoTateGroup.trace_columnOp_mul_isotypicMatrix`: the trace of a column antisymmetriser on an
  isotypic projector.
* `SatoTateGroup.columnOp_mul_isotypicMatrix_eq_zero_iff`: when a column antisymmetriser kills an
  isotypic projector.
* `SatoTateGroup.columnOp_cupMap_eq_zero`: when a column antisymmetriser kills a cup.
-/

open Equiv Filter Matrix MeasureTheory Module Representation TauCeti

open LinearMap (IsIdempotentElem.eq_zero_of_trace_eq_zero)

open scoped ComplexConjugate MonoidAlgebra

universe u

namespace SatoTateGroup

section Isotypic

variable {w d : ℕ} {P : Type u} [Fintype P] (χ χ' : IrrepClass ℂ (ambientGroup w d))

variable [DecidableEq P]

lemma isotypicMatrix_mul_self : (isotypicMatrix χ : Matrix (P → Fin d) (P → Fin d) ℂ) *
    isotypicMatrix χ = isotypicMatrix χ := by
  refine mulVec_injective (funext fun f ↦ ?_)
  have h₁ : (ambientProjector (P := P) χ).comp (ambientProjector χ) = ambientProjector χ :=
    ContRepresentation.isotypicProjector_idempotent _ _ isUnitary_ambientTensorRep _ _
      χ.model.isIrreducible
  have h₂ : ambientProjector χ (ambientProjector χ (WithLp.toLp 2 f)) =
      ambientProjector χ (WithLp.toLp 2 f) :=
    congrArg (fun R : ContIntertwiningMap (ambientTensorRep (w := w) (d := d) (P := P))
      (ambientTensorRep (w := w) (d := d) (P := P)) ↦ R (WithLp.toLp 2 f)) h₁
  have h₃ : (ambientProjector χ (ambientProjector χ (WithLp.toLp 2 f))).ofLp =
      (ambientProjector χ (WithLp.toLp 2 f)).ofLp :=
    congrArg WithLp.ofLp h₂
  rw [ambientProjector_apply_ofLp, ambientProjector_apply_ofLp] at h₃
  rw [← mulVec_mulVec]
  exact h₃

lemma tensorRep_mul_isotypicMatrix (g : ambientGroup w d) :
    tensorRep (P := P) (g : Matrix (Fin d) (Fin d) ℂ) * isotypicMatrix χ =
      isotypicMatrix χ * tensorRep (g : Matrix (Fin d) (Fin d) ℂ) := by
  refine mulVec_injective (funext fun f ↦ ?_)
  have h₁ : ambientProjector χ (ambientTensorRep g (WithLp.toLp 2 f)) =
      ambientTensorRep g (ambientProjector χ (WithLp.toLp 2 f)) :=
    congrArg (fun R ↦ R (WithLp.toLp 2 f)) ((ambientProjector (P := P) χ).isIntertwining' g)
  have h₂ : (ambientProjector χ (ambientTensorRep g (WithLp.toLp 2 f))).ofLp =
      (ambientTensorRep g (ambientProjector χ (WithLp.toLp 2 f))).ofLp :=
    congrArg WithLp.ofLp h₁
  rw [ambientProjector_apply_ofLp] at h₂
  have h₃ (x : EuclideanSpace ℂ (P → Fin d)) :
      (ambientTensorRep g x).ofLp = tensorRep (P := P) (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ x.ofLp :=
    rfl
  rw [h₃, h₃, ambientProjector_apply_ofLp] at h₂
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  exact h₂.symm

lemma slotRep_isotypicMatrix_mulVec (σ : Perm P) (f : (P → Fin d) → ℂ) :
    slotRep P (Fin d) σ (isotypicMatrix χ *ᵥ f) = isotypicMatrix χ *ᵥ slotRep P (Fin d) σ f := by
  funext a
  rw [slotRep_apply, isotypicMatrix_mulVec_apply, isotypicMatrix_mulVec_apply]
  refine congrArg _ (integral_congr_ae (Eventually.of_forall fun g ↦ ?_))
  have h₁ : (tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ f) (a ∘ σ) =
      (tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ slotRep P (Fin d) σ f) a :=
    congrFun (commute_slotRep_tensorRep σ (g : Matrix (Fin d) (Fin d) ℂ) f) a
  beta_reduce
  rw [h₁]

lemma commute_mulVecLin_slotRep (σ : Perm P) :
    Commute (isotypicMatrix χ : Matrix (P → Fin d) (P → Fin d) ℂ).mulVecLin (slotRep P (Fin d) σ) :=
  LinearMap.ext fun f ↦ (slotRep_isotypicMatrix_mulVec χ σ f).symm

variable {χ χ'}

/-- **The isotypic projectors of distinct irreducible characters are orthogonal.** -/
lemma isotypicMatrix_mul_eq_zero (h : χ ≠ χ') :
    (isotypicMatrix χ : Matrix (P → Fin d) (P → Fin d) ℂ) * isotypicMatrix χ' = 0 := by
  let ρ : ContRepresentation ℂ (ambientGroup w d) (EuclideanSpace ℂ (P → Fin d)) := ambientTensorRep
  have hρ : Continuous ρ := continuous_ambientTensorRep
  have hu : ContRepresentation.IsUnitary ρ := isUnitary_ambientTensorRep
  let C : Submodule ℂ[ambientGroup w d] ρ.toRepresentation.asModule :=
    isotypicComponent ℂ[ambientGroup w d] ρ.toRepresentation.asModule
      χ'.model.rep.toRepresentation.asModule
  have hC : ∀ x ∈ C, ambientProjector χ (x : EuclideanSpace ℂ (P → Fin d)) = 0 := by
    let p : End ℂ[ambientGroup w d] ρ.toRepresentation.asModule :=
      IntertwiningMap.equivLinearMapAsModule _ _ (ambientProjector (P := P) χ).toIntertwiningMap
    have hp (x : ρ.toRepresentation.asModule) :
        p x = ambientProjector χ (x : EuclideanSpace ℂ (P → Fin d)) :=
      (IntertwiningMap.equivLinearMapAsModule_apply
          (ambientProjector (P := P) χ).toIntertwiningMap x).trans
        (ContIntertwiningMap.toIntertwiningMap_apply (ambientProjector (P := P) χ) _)
    have hle : C ≤ LinearMap.ker p := by
      refine sSup_le fun m he x hx ↦ ?_
      let τ : Subrepresentation ρ.toRepresentation := Subrepresentation.ofSubmodule' m
      have hτ : IsAtom τ := Subrepresentation.isSimpleModule_asSubmodule_iff.mp
        (IsSimpleModule.congr (Classical.choice he))
      have hne : IsEmpty (m ≃ₗ[ℂ[ambientGroup w d]] χ.model.rep.toRepresentation.asModule) := by
        refine ⟨fun e ↦ h ?_⟩
        refine injective_ambientCharacter w d (ContinuousMap.ext fun g ↦ ?_)
        have h₁ : χ.model.rep.toRepresentation.Equiv χ'.model.rep.toRepresentation :=
          Representation.equivOfAsModuleLinearEquiv (e.symm.trans (Classical.choice he))
        exact congrFun (char_iso h₁) g
      exact (hp x).trans (ContRepresentation.isotypicProjector_apply_subtype_of_not_equiv ρ hρ
        χ.model.rep χ.model.continuous_rep χ.model.isIrreducible hτ hne (⟨x, hx⟩ : τ.toSubmodule))
    exact fun x hx ↦ (hp x).symm.trans (hle hx)
  refine mulVec_injective (funext fun f ↦ ?_)
  have h₁ : ρ.toRepresentation.asModuleEquiv.symm (ambientProjector χ' (WithLp.toLp 2 f)) ∈ C := by
    have h₂ : ambientProjector χ' (WithLp.toLp 2 f) ∈ (ContRepresentation.isotypicProjector ρ hρ
        χ'.model.rep χ'.model.continuous_rep).toIntertwiningMap.range :=
      (IntertwiningMap.mem_range _ _ _ _).mpr ⟨_, rfl⟩
    have h₃ : ρ.toRepresentation.asModuleEquiv.symm (ambientProjector χ' (WithLp.toLp 2 f)) ∈
        (ContRepresentation.isotypicProjector ρ hρ χ'.model.rep
          χ'.model.continuous_rep).toIntertwiningMap.range.asSubmodule :=
      (Subrepresentation.mem_asSubmodule_iff (σ := (ContRepresentation.isotypicProjector ρ hρ
        χ'.model.rep χ'.model.continuous_rep).toIntertwiningMap.range)).mpr h₂
    rwa [ContRepresentation.range_isotypicProjector ρ hρ hu χ'.model.rep χ'.model.continuous_rep
      χ'.model.isIrreducible] at h₃
  have h₂ : ambientProjector χ (ambientProjector χ' (WithLp.toLp 2 f)) = 0 := hC _ h₁
  have h₃ : (ambientProjector χ (ambientProjector χ' (WithLp.toLp 2 f))).ofLp = 0 :=
    congrArg WithLp.ofLp h₂
  rw [ambientProjector_apply_ofLp, ambientProjector_apply_ofLp] at h₃
  rw [← mulVec_mulVec, zero_mulVec]
  exact h₃

variable (χ) {K : Type*} [Fintype K] [DecidableEq K] (col : P → K)

/-- **The trace of a column antisymmetriser on an isotypic projector**: up to nonzero factors, the
integral of the product of the elementary symmetric functions against the character. -/
lemma trace_columnOp_mul_isotypicMatrix : LinearMap.trace ℂ _ (columnOp (slotRep P (Fin d)) col *
    (isotypicMatrix χ : Matrix (P → Fin d) (P → Fin d) ℂ).mulVecLin) =
      (χ.model.dim : ℂ) * ((∏ k, ((Fintype.card {p // col p = k}).factorial : ℂ)) *
        ∫ g : ambientGroup w d, (∏ k, (g : Matrix (Fin d) (Fin d) ℂ).charpoly.roots.esymm
          (Fintype.card {p // col p = k})) * conj (ambientCharacter w d χ g)
            ∂haarProb (ambientGroup w d)) := by
  rw [trace_columnOp_mul_mulVecLin, ← integral_const_mul]
  have h₁ (g : ambientGroup w d) : (∏ k, ((Fintype.card {p // col p = k}).factorial : ℂ)) *
      ((∏ k, (g : Matrix (Fin d) (Fin d) ℂ).charpoly.roots.esymm
        (Fintype.card {p // col p = k})) * conj (ambientCharacter w d χ g)) =
      ∑ a : P → Fin d, ∑ q : fiberSubgroup col, ((Perm.sign (q : Perm P) : ℤ) : ℂ) *
        (tensorRep (g : Matrix (Fin d) (Fin d) ℂ) (a ∘ q) a * conj (ambientCharacter w d χ g)) := by
    simp only [← mul_assoc, ← Finset.sum_mul]
    rw [sum_sum_sign_mul_tensorRep, Finset.prod_mul_distrib]
  have hint (a : P → Fin d) (q : fiberSubgroup col) : Integrable (fun g : ambientGroup w d ↦
      ((Perm.sign (q : Perm P) : ℤ) : ℂ) * (tensorRep (g : Matrix (Fin d) (Fin d) ℂ) (a ∘ q) a *
        conj (ambientCharacter w d χ g))) (haarProb (ambientGroup w d)) :=
    (continuous_const.mul (continuous_tensorRep_mul_conj χ _ a)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [h₁]
  rw [integral_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun q _ ↦ hint a q, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [integral_finsetSum _ fun q _ ↦ hint a q, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [integral_const_mul]
  exact mul_left_comm _ _ _

/-- **A column antisymmetriser kills an isotypic projector exactly when the integral of the product
of the elementary symmetric functions against the character vanishes.** -/
lemma columnOp_mul_isotypicMatrix_eq_zero_iff : columnOp (slotRep P (Fin d)) col *
    (isotypicMatrix χ : Matrix (P → Fin d) (P → Fin d) ℂ).mulVecLin = 0 ↔
      ∫ g : ambientGroup w d, (∏ k, (g : Matrix (Fin d) (Fin d) ℂ).charpoly.roots.esymm
        (Fintype.card {p // col p = k})) * conj (ambientCharacter w d χ g)
          ∂haarProb (ambientGroup w d) = 0 := by
  have hd : (χ.model.dim : ℂ) ≠ 0 := by
    have h₁ : (finrank ℂ (EuclideanSpace ℂ (Fin χ.model.dim)) : ℂ) ≠ 0 :=
      χ.model.isIrreducible.natCast_finrank_ne_zero
    simpa using h₁
  have hf : (∏ k, ((Fintype.card {p // col p = k}).factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  let A : End ℂ ((P → Fin d) → ℂ) := columnOp (slotRep P (Fin d)) col
  let M : End ℂ ((P → Fin d) → ℂ) :=
    (isotypicMatrix χ : Matrix (P → Fin d) (P → Fin d) ℂ).mulVecLin
  have hM : M * M = M := LinearMap.ext fun f ↦
    (mulVec_mulVec f _ _).trans (congrArg (· *ᵥ f) (isotypicMatrix_mul_self χ))
  have hAM : Commute M A := commute_columnOp _ col (commute_mulVecLin_slotRep χ)
  have hcard : (Fintype.card (fiberSubgroup col) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hE : IsIdempotentElem ((Fintype.card (fiberSubgroup col) : ℂ)⁻¹ • (A * M)) := by
    have h₁ : (A * M) * (A * M) = (Fintype.card (fiberSubgroup col) : ℂ) • (A * M) := by
      rw [mul_assoc, ← mul_assoc M, hAM.eq, mul_assoc, hM, ← mul_assoc, columnOp_mul_self,
        smul_mul_assoc]
    rw [IsIdempotentElem, smul_mul_smul_comm, h₁, smul_smul, mul_assoc,
      inv_mul_cancel₀ hcard, mul_one]
  constructor
  · intro h₁
    refine (mul_eq_zero.mp ((mul_eq_zero.mp
      ((trace_columnOp_mul_isotypicMatrix χ col).symm.trans ?_)).resolve_left hd)).resolve_left hf
    rw [h₁, map_zero]
  · intro h₁
    have h₂ : LinearMap.trace ℂ _ (A * M) = 0 := by
      refine (trace_columnOp_mul_isotypicMatrix χ col).trans ?_
      rw [h₁, mul_zero, mul_zero]
    have h₃ : (Fintype.card (fiberSubgroup col) : ℂ)⁻¹ • (A * M) = 0 :=
      hE.eq_zero_of_trace_eq_zero (by rw [map_smul, h₂, smul_zero])
    exact (smul_eq_zero.mp h₃).resolve_left (inv_ne_zero hcard)

end Isotypic

section Tuples

variable {P : Type u} {I : Type*} [DecidableEq P] {p q : P}

variable [Fintype P] in
lemma prod_eq_mul_mul_prod_subtype (hpq : p ≠ q) (f : P → ℂ) :
    ∏ r, f r = f p * (f q * ∏ r : {r : P // r ≠ p ∧ r ≠ q}, f r) := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ p),
    ← Finset.mul_prod_erase (Finset.univ.erase p) f
      (Finset.mem_erase.mpr ⟨hpq.symm, Finset.mem_univ q⟩),
    Finset.prod_subtype ((Finset.univ.erase p).erase q) (p := fun r ↦ r ≠ p ∧ r ≠ q)
      (fun r ↦ by simp [and_comm])]

/-- The tuples of indices, by their values at two distinct slots and on the others. -/
def cupEquiv (hpq : p ≠ q) : (I × I) × ({r : P // r ≠ p ∧ r ≠ q} → I) ≃ (P → I) where
  toFun x r := if hr : r ≠ p ∧ r ≠ q then x.2 ⟨r, hr⟩ else if r = p then x.1.1 else x.1.2
  invFun b := ((b p, b q), fun r ↦ b r.1)
  left_inv x := by
    refine Prod.ext (Prod.ext ?_ ?_) (funext fun r ↦ ?_)
    · simp
    · simp [hpq.symm]
    · simp [r.2]
  right_inv b := by
    funext r
    by_cases hr : r ≠ p ∧ r ≠ q
    · simp [hr]
    · by_cases hp : r = p
      · simp [hp]
      · have hq : r = q := by
          by_contra hq
          exact hr ⟨hp, hq⟩
        simp [hq, hpq.symm]

lemma cupEquiv_left (hpq : p ≠ q) (x : (I × I) × ({r : P // r ≠ p ∧ r ≠ q} → I)) :
    cupEquiv hpq x p = x.1.1 := by
  simp [cupEquiv]

lemma cupEquiv_right (hpq : p ≠ q) (x : (I × I) × ({r : P // r ≠ p ∧ r ≠ q} → I)) :
    cupEquiv hpq x q = x.1.2 := by
  simp [cupEquiv, hpq.symm]

lemma cupEquiv_coe (hpq : p ≠ q) (x : (I × I) × ({r : P // r ≠ p ∧ r ≠ q} → I))
    (r : {r : P // r ≠ p ∧ r ≠ q}) : cupEquiv hpq x r.1 = x.2 r := by
  simp [cupEquiv, r.2]

lemma cupEquiv_eq_update (hpq : p ≠ q) (a : P → I) (c : I) :
    cupEquiv hpq ((c, c), fun r ↦ a r.1) = Function.update (Function.update a p c) q c := by
  funext r
  by_cases hr : r ≠ p ∧ r ≠ q
  · rw [cupEquiv_coe hpq _ ⟨r, hr⟩, Function.update_of_ne hr.2, Function.update_of_ne hr.1]
  · by_cases hp : r = p
    · subst hp
      rw [cupEquiv_left, Function.update_of_ne hpq, Function.update_self]
    · have hq : r = q := by
        by_contra hq
        exact hr ⟨hp, hq⟩
      subst hq
      rw [cupEquiv_right, Function.update_self]

end Tuples

section Cup

variable {P : Type u} {I : Type*} [DecidableEq I] (p q : P)

/-- The **cup at the slots `p`, `q`**: the tensor `δ_{a p, a q} y (a |_{other slots})`. -/
def cupMap : (({r : P // r ≠ p ∧ r ≠ q} → I) → ℂ) →ₗ[ℂ] ((P → I) → ℂ) where
  toFun y a := if a p = a q then y fun r ↦ a r.1 else 0
  map_add' y y' := by
    funext a
    by_cases h : a p = a q <;> simp [h]
  map_smul' c y := by
    funext a
    simp

lemma cupMap_apply (y : ({r : P // r ≠ p ∧ r ≠ q} → I) → ℂ) (a : P → I) :
    cupMap p q y a = if a p = a q then y fun r ↦ a r.1 else 0 :=
  rfl

variable {p q} in
lemma isCupAt_cupMap (y : ({r : P // r ≠ p ∧ r ≠ q} → I) → ℂ) : IsCupAt p q (cupMap p q y) := by
  refine ⟨fun a ha ↦ ite_eq_right ha, fun a a' ha ha' he ↦ ?_⟩
  rw [cupMap_apply, cupMap_apply, ite_eq_left ha, ite_eq_left ha']
  exact congrArg y (funext fun r ↦ he r.1 r.2.1 r.2.2)

variable {p q} [DecidableEq P]

lemma IsCupAt.exists_eq_cupMap {f : (P → I) → ℂ} (hf : IsCupAt p q f) : ∃ y, f = cupMap p q y := by
  rcases isEmpty_or_nonempty I with hI | ⟨⟨c₀⟩⟩
  · exact ⟨0, funext fun a ↦ hI.elim (a p)⟩
  · let e (a' : {r : P // r ≠ p ∧ r ≠ q} → I) (r : P) : I :=
      if hr : r ≠ p ∧ r ≠ q then a' ⟨r, hr⟩ else c₀
    have he₁ (a' : {r : P // r ≠ p ∧ r ≠ q} → I) : e a' p = c₀ := dite_eq_right fun h ↦ h.1 rfl
    have he₂ (a' : {r : P // r ≠ p ∧ r ≠ q} → I) : e a' q = c₀ := dite_eq_right fun h ↦ h.2 rfl
    refine ⟨fun a' ↦ f (e a'), funext fun a ↦ ?_⟩
    rw [cupMap_apply]
    by_cases h : a p = a q
    · rw [ite_eq_left h]
      refine hf.2 _ _ h ((he₁ fun r ↦ a r.1).trans (he₂ fun r ↦ a r.1).symm) fun r hr hr' ↦ ?_
      simp [e, hr, hr']
    · rw [ite_eq_right h]
      exact hf.1 a h

lemma slotRep_swap_cupMap (y : ({r : P // r ≠ p ∧ r ≠ q} → I) → ℂ) :
    slotRep P I (Equiv.swap p q) (cupMap p q y) = cupMap p q y := by
  funext a
  rw [slotRep_apply, cupMap_apply, cupMap_apply]
  simp only [Function.comp_apply, swap_apply_left, swap_apply_right, eq_comm (a := a q)]
  refine if_congr Iff.rfl (congrArg y (funext fun r ↦ ?_)) rfl
  rw [swap_apply_of_ne_of_ne r.2.1 r.2.2]

lemma slotRep_ofSubtype_cupMap (τ : Perm {r : P // r ≠ p ∧ r ≠ q})
    (y : ({r : P // r ≠ p ∧ r ≠ q} → I) → ℂ) :
    slotRep P I (Perm.ofSubtype τ) (cupMap p q y) = cupMap p q (slotRep _ I τ y) := by
  funext a
  have h₁ : Perm.ofSubtype τ p = p :=
    Perm.ofSubtype_apply_of_not_mem τ fun h ↦ h.1 rfl
  have h₂ : Perm.ofSubtype τ q = q :=
    Perm.ofSubtype_apply_of_not_mem τ fun h ↦ h.2 rfl
  rw [slotRep_apply, cupMap_apply, cupMap_apply]
  simp only [Function.comp_apply, h₁, h₂]
  refine if_congr Iff.rfl (congrArg y (funext fun r ↦ ?_)) rfl
  rw [Perm.ofSubtype_apply_of_mem τ r.2]
  rfl

variable [Fintype P]

/-- **A column antisymmetriser kills a cup on two slots of one column, and, on two slots of distinct
columns, whenever the antisymmetriser of the remaining boxes kills its argument.** -/
lemma columnOp_cupMap_eq_zero {K : Type*} [DecidableEq K] (col : P → K) (hpq : p ≠ q)
    {y : ({r : P // r ≠ p ∧ r ≠ q} → I) → ℂ}
    (hy : col p ≠ col q →
      columnOp (slotRep _ I) (fun r : {r : P // r ≠ p ∧ r ≠ q} ↦ col r.1) y = 0) :
    columnOp (slotRep P I) col (cupMap p q y) = 0 := by
  by_cases hc : col p = col q
  · have h₁ : Equiv.swap p q ∈ fiberSubgroup col := swap_mem_fiberSubgroup hc
    have h₂ : columnOp (slotRep P I) col (slotRep P I (Equiv.swap p q) (cupMap p q y)) =
        ((Perm.sign (Equiv.swap p q) : ℤ) : ℂ) • columnOp (slotRep P I) col (cupMap p q y) :=
      LinearMap.congr_fun (columnOp_mul_of_mem _ h₁) (cupMap p q y)
    rw [slotRep_swap_cupMap, Perm.sign_swap hpq] at h₂
    exact eq_zero_of_eq_neg (h₂.trans (by simp))
  · let col' : {r : P // r ≠ p ∧ r ≠ q} → K := fun r ↦ col r.1
    have hext (τ : fiberSubgroup col') :
        Perm.ofSubtype (τ : Perm {r : P // r ≠ p ∧ r ≠ q}) ∈ fiberSubgroup col := by
      intro r
      by_cases hr : r ≠ p ∧ r ≠ q
      · rw [Perm.ofSubtype_apply_of_mem (τ : Perm {r : P // r ≠ p ∧ r ≠ q}) hr]
        exact τ.2 ⟨r, hr⟩
      · rw [Perm.ofSubtype_apply_of_not_mem (τ : Perm {r : P // r ≠ p ∧ r ≠ q}) hr]
    have h₁ (τ : fiberSubgroup col') :
        columnOp (slotRep P I) col (cupMap p q (slotRep _ I (τ : Perm _) y)) =
          ((Perm.sign (τ : Perm {r : P // r ≠ p ∧ r ≠ q}) : ℤ) : ℂ) •
            columnOp (slotRep P I) col (cupMap p q y) := by
      rw [← slotRep_ofSubtype_cupMap]
      have h₂ : columnOp (slotRep P I) col
          (slotRep P I (Perm.ofSubtype (τ : Perm {r : P // r ≠ p ∧ r ≠ q})) (cupMap p q y)) =
            ((Perm.sign (Perm.ofSubtype (τ : Perm {r : P // r ≠ p ∧ r ≠ q})) : ℤ) : ℂ) •
              columnOp (slotRep P I) col (cupMap p q y) :=
        LinearMap.congr_fun (columnOp_mul_of_mem (slotRep P I) (hext τ)) (cupMap p q y)
      rwa [Perm.sign_ofSubtype] at h₂
    have h₂ : (Fintype.card (fiberSubgroup col') : ℂ) •
        columnOp (slotRep P I) col (cupMap p q y) = 0 := by
      have h₃ : columnOp (slotRep P I) col (cupMap p q (columnOp (slotRep _ I) col' y)) = 0 := by
        rw [hy hc, map_zero, map_zero]
      have h₄ : columnOp (slotRep _ I) col' y = ∑ τ : fiberSubgroup col',
          ((Perm.sign (τ : Perm {r : P // r ≠ p ∧ r ≠ q}) : ℤ) : ℂ) • slotRep _ I (τ : Perm _) y :=
        (LinearMap.congr_fun (columnOp_eq_sum _ col') y).trans (LinearMap.sum_apply _ _ _)
      rw [h₄, map_sum, map_sum] at h₃
      simp only [map_smul, h₁, smul_smul, sign_mul_self_cast, one_smul] at h₃
      rwa [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ] at h₃
    exact (smul_eq_zero.mp h₂).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

variable [Fintype I]

lemma sum_cupMap_mul (hpq : p ≠ q) (y : ({r : P // r ≠ p ∧ r ≠ q} → I) → ℂ) (f : (P → I) → ℂ) :
    ∑ b, cupMap p q y b * f b = ∑ a', y a' * ∑ c, f (cupEquiv hpq ((c, c), a')) := by
  have h₁ (x : (I × I) × ({r : P // r ≠ p ∧ r ≠ q} → I)) :
      cupMap p q y (cupEquiv hpq x) = if x.1.1 = x.1.2 then y x.2 else 0 := by
    have h₂ : (fun r : {r : P // r ≠ p ∧ r ≠ q} ↦ cupEquiv hpq x r.1) = x.2 :=
      funext (cupEquiv_coe hpq x)
    rw [cupMap_apply, cupEquiv_left, cupEquiv_right, h₂]
  rw [← (cupEquiv hpq).sum_comp, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun a' _ ↦ ?_
  rw [Fintype.sum_prod_type]
  simp only [h₁, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]

lemma tensorRep_mulVec_cupMap (hpq : p ≠ q) {A : Matrix I I ℂ} (hA : A * Aᵀ = 1)
    (y : ({r : P // r ≠ p ∧ r ≠ q} → I) → ℂ) :
    tensorRep A *ᵥ cupMap p q y = cupMap p q (tensorRep A *ᵥ y) := by
  funext a
  have h₁ (x y' : I) : ∑ c, A x c * A y' c = if x = y' then 1 else 0 := by
    have h₂ : (A * Aᵀ) x y' = ∑ c, A x c * A y' c := Matrix.mul_apply
    rw [← h₂, hA, one_apply]
  have h₂ : (tensorRep A *ᵥ cupMap p q y) a = ∑ b, cupMap p q y b * ∏ r, A (a r) (b r) :=
    Finset.sum_congr rfl fun b _ ↦ mul_comm _ _
  have h₃ (a' : {r : P // r ≠ p ∧ r ≠ q} → I) : ∑ c, ∏ r, A (a r) (cupEquiv hpq ((c, c), a') r) =
      (if a p = a q then 1 else 0) * ∏ r : {r : P // r ≠ p ∧ r ≠ q}, A (a r.1) (a' r) := by
    simp only [prod_eq_mul_mul_prod_subtype hpq, cupEquiv_left, cupEquiv_right, cupEquiv_coe]
    rw [← h₁, Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ ↦ by ring1
  rw [h₂, sum_cupMap_mul hpq, cupMap_apply]
  simp only [h₃]
  split_ifs with h
  · refine Finset.sum_congr rfl fun a' _ ↦ ?_
    rw [one_mul]
    exact mul_comm _ _
  · simp

variable {w d : ℕ} (χ : IrrepClass ℂ (ambientGroup w d))

lemma isotypicMatrix_mulVec_cupMap (hw : Even w) (hpq : p ≠ q)
    (y : ({r : P // r ≠ p ∧ r ≠ q} → Fin d) → ℂ) :
    isotypicMatrix χ *ᵥ cupMap p q y = cupMap p q (isotypicMatrix χ *ᵥ y) := by
  funext a
  rw [isotypicMatrix_mulVec_apply, cupMap_apply]
  have h₁ (g : ambientGroup w d) : (tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ cupMap p q y) a =
      cupMap p q (tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ y) a :=
    congrFun (tensorRep_mulVec_cupMap hpq (mul_transpose_self_ambient hw g) y) a
  simp only [h₁, cupMap_apply]
  split_ifs with h
  · rw [isotypicMatrix_mulVec_apply]
  · simp

end Cup

end SatoTateGroup
