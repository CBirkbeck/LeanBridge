import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.OrthogonalIntertwiner
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.OrthogonalYoung

/-!
# Traceless tensors

Weyl's construction of the irreducible representations of `O(d)` applies the Young symmetrizer of a
partition to the **traceless tensors**, those whose contractions at all pairs of distinct slots
vanish (Weyl, *The Classical Groups*, Chapter V; Fulton and Harris, *Representation Theory*, §19.5).

A tensor is the sum of a traceless tensor and of a combination of cups, and this decomposition is
stable under `O(d)` and the permutations of the slots. By the first fundamental theorem, an operator
commuting with `O(d)` acts on the traceless tensors as a combination of permutations of the slots,
and it sends the traceless tensors to combinations of cups if its source and its target have
different degrees. Since the Young symmetrizers of two distinct partitions annihilate each other
through any permutation, an irreducible character of `O(d)` occurs in Weyl's construction for at
most one partition, and at most one irreducible character occurs in Weyl's construction for a given
partition.

Tau Ceti's `TauCeti.harmonicTensors` are the same tensors in `PiTensorProduct` form. On Tau Ceti's
main, `TauCeti.isCompl_harmonicTensors_iSup_range_orthogonalCupCapAt` has the same content as the
two short statements on the decomposition here, which can be replaced after the next bump if the
tensors are moved to that form.

## Main definitions

* `SatoTateGroup.cupSpan`: the span of the cups.
* `SatoTateGroup.traceless`: the traceless tensors.
* `SatoTateGroup.youngOp`: the Young symmetrizer of a partition on a tensor power.
* `SatoTateGroup.youngTraceless`: the traceless tensors on which it is a given scalar.

## Main results

* `SatoTateGroup.eq_zero_of_mem_traceless_of_mem_cupSpan`: a traceless tensor in the span of the
  cups is zero.
* `SatoTateGroup.exists_eq_add_traceless_cupSpan`: a tensor is the sum of a traceless tensor and of
  a combination of cups.
* `SatoTateGroup.tensorRep_mulVec_mem_traceless`: the traceless tensors are stable under `O(d)`.
* `SatoTateGroup.mulVec_mem_cupSpan_of_card_ne`: an operator between tensor powers of different
  degrees commuting with `O(d)` sends the traceless tensors to combinations of cups.
* `SatoTateGroup.exists_mulVec_eq_asAlgebraHom_of_traceless`: an operator on a tensor power
  commuting with `O(d)` acts on the traceless tensors as a combination of permutations of the slots.
* `SatoTateGroup.exists_matrix_of_isotypic`: two isotypic tensors of the same type are related by an
  operator commuting with `O(d)`.
* `SatoTateGroup.ofPartition_eq_of_traceless`: an irreducible character of `O(d)` occurs in Weyl's
  construction for at most one partition.
* `SatoTateGroup.eq_of_traceless`: Weyl's construction for a partition contains at most one
  irreducible character of `O(d)`.
-/

open Equiv Function Matrix MeasureTheory Module TauCeti YoungDiagram

open scoped ComplexConjugate ComplexOrder

universe u

namespace SatoTateGroup

section Traceless

variable (P : Type u) (I : Type*)

/-- The span of the cups. -/
def cupSpan : Submodule ℂ ((P → I) → ℂ) :=
  Submodule.span ℂ {h | ∃ p q, p ≠ q ∧ IsCupAt p q h}

variable {P I} in
lemma star_mem_cupSpan {h : (P → I) → ℂ} (hh : h ∈ cupSpan P I) : star h ∈ cupSpan P I := by
  induction hh using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨p, q, hpq, hx₁, hx₂⟩
    refine Submodule.subset_span ⟨p, q, hpq, fun a ha ↦ ?_, fun a a' ha ha' he ↦ ?_⟩
    · rw [Pi.star_apply, hx₁ a ha, star_zero]
    · rw [Pi.star_apply, Pi.star_apply, hx₂ a a' ha ha' he]
  | zero =>
    rw [star_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [star_add]
    exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [star_smul]
    exact Submodule.smul_mem _ _ hx

variable [DecidableEq P] [Fintype I]

/-- The **traceless tensors**: those whose contractions at all pairs of distinct slots vanish. -/
def traceless : Submodule ℂ ((P → I) → ℂ) where
  carrier := {f | ∀ p q, p ≠ q → ∀ a, ∑ c, f (update (update a p c) q c) = 0}
  add_mem' hf hg p q hpq a := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, hf p q hpq a, hg p q hpq a, add_zero]
  zero_mem' p q hpq a := by
    simp
  smul_mem' r f hf p q hpq a := by
    simp only [Pi.smul_apply, ← Finset.smul_sum, hf p q hpq a, smul_zero]

variable {P I} {f h : (P → I) → ℂ} {p q : P}

lemma slotRep_mem_traceless (σ : Perm P) (hf : f ∈ traceless P I) :
    slotRep P I σ f ∈ traceless P I := by
  refine fun p q hpq a ↦ ?_
  have h₁ (c : I) :
      (update (update a p c) q c) ∘ σ = update (update (a ∘ σ) (σ.symm p) c) (σ.symm q) c := by
    rw [update_comp_equiv, update_comp_equiv]
  simp only [slotRep_apply, h₁]
  exact hf _ _ (σ.symm.injective.ne hpq) _

variable [Fintype P]

lemma asAlgebraHom_mem_traceless (z : MonoidAlgebra ℂ (Perm P)) (hf : f ∈ traceless P I) :
    (slotRep P I).asAlgebraHom z f ∈ traceless P I := by
  rw [Representation.asAlgebraHom_eq_sum, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun σ _ ↦ Submodule.smul_mem _ _ (slotRep_mem_traceless σ hf)

variable [DecidableEq I]

lemma sum_mul_eq_zero_of_isCupAt (hf : f ∈ traceless P I) (hpq : p ≠ q) (hh : IsCupAt p q h) :
    ∑ a, h a * f a = 0 := by
  rcases hh.exists_eq_cupMap with ⟨y, rfl⟩
  rw [sum_cupMap_mul hpq]
  refine Finset.sum_eq_zero fun a' _ ↦ ?_
  have h₁ : ∑ c, f (cupEquiv hpq ((c, c), a')) = 0 := by
    rcases isEmpty_or_nonempty I with hI | ⟨⟨c₀⟩⟩
    · simp
    · let a : P → I := cupEquiv hpq ((c₀, c₀), a')
      have h₂ : (fun r : {r : P // r ≠ p ∧ r ≠ q} ↦ a r.1) = a' :=
        funext (cupEquiv_coe hpq ((c₀, c₀), a'))
      have h₃ (c : I) : cupEquiv hpq ((c, c), a') = update (update a p c) q c := by
        rw [← cupEquiv_eq_update hpq a c, h₂]
      simp only [h₃]
      exact hf p q hpq a
  rw [h₁, mul_zero]

lemma brauerMatrix_mulVec_eq_zero {P' : Type u} [Fintype P'] {π : PerfectMatching (P' ⊕ P)}
    (hq : π.val (.inr p) = .inr q) (hh : h ∈ traceless P I) : brauerMatrix π *ᵥ h = 0 :=
  funext fun a ↦ sum_mul_eq_zero_of_isCupAt hh (fun h₁ ↦ π.apply_ne (.inr p) (by rw [hq, h₁]))
    (brauerMatrix_row_isCupAt hq a)

lemma sum_mul_eq_zero_of_mem_cupSpan (hf : f ∈ traceless P I) (hh : h ∈ cupSpan P I) :
    ∑ a, h a * f a = 0 := by
  induction hh using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨p, q, hpq, hx⟩
    exact sum_mul_eq_zero_of_isCupAt hf hpq hx
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hx, hy, add_zero]
  | smul r x _ hx =>
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hx, mul_zero]

/-- **A traceless tensor in the span of the cups is zero.** -/
lemma eq_zero_of_mem_traceless_of_mem_cupSpan (hf : f ∈ traceless P I) (hc : f ∈ cupSpan P I) :
    f = 0 :=
  dotProduct_star_self_eq_zero.mp (sum_mul_eq_zero_of_mem_cupSpan hf (star_mem_cupSpan hc))

variable (f) in
/-- **A tensor is the sum of a traceless tensor and of a combination of cups.** -/
lemma exists_eq_add_traceless_cupSpan : ∃ h ∈ traceless P I, ∃ c ∈ cupSpan P I, f = h + c := by
  rcases exists_eq_add_star_dotProduct_eq_zero (cupSpan P I) f with ⟨y, hy, z, hz, rfl⟩
  refine ⟨z, fun p q hpq a ↦ ?_, y, hy, add_comm _ _⟩
  classical
  let y₀ : ({r : P // r ≠ p ∧ r ≠ q} → I) → ℂ := fun a' ↦ if a' = fun r ↦ a r.1 then 1 else 0
  have h₁ : star (cupMap p q y₀) ⬝ᵥ z = 0 :=
    hz _ (Submodule.subset_span ⟨p, q, hpq, isCupAt_cupMap y₀⟩)
  have h₂ : star (cupMap p q y₀) = cupMap p q y₀ := by
    funext b
    rw [Pi.star_apply, cupMap_apply]
    split_ifs
    · simp only [y₀]
      split_ifs <;> simp
    · simp
  have h₃ : ∑ b, cupMap p q y₀ b * z b = 0 := by
    rwa [h₂] at h₁
  rw [sum_cupMap_mul hpq, Finset.sum_eq_single (fun r ↦ a r.1)] at h₃
  · simp only [y₀, ite_true, one_mul, cupEquiv_eq_update] at h₃
    exact h₃
  · intro a' _ ha'
    simp [y₀, ha']
  · simp

/-- **The traceless tensors are stable under `O(d)`.** -/
lemma tensorRep_mulVec_mem_traceless {A : Matrix I I ℂ} (hA : Aᵀ * A = 1) (hf : f ∈ traceless P I) :
    tensorRep A *ᵥ f ∈ traceless P I := by
  refine fun p q hpq a ↦ ?_
  have h₁ (x y : I) : ∑ c, A c x * A c y = if x = y then 1 else 0 := by
    have h₂ : (Aᵀ * A) x y = ∑ c, A c x * A c y := Matrix.mul_apply
    rw [← h₂, hA, one_apply]
  let y : ({r : P // r ≠ p ∧ r ≠ q} → I) → ℂ :=
    fun b' ↦ ∏ r : {r : P // r ≠ p ∧ r ≠ q}, A (a r.1) (b' r)
  have h₂ (b : P → I) : ∑ c, ∏ r, A (update (update a p c) q c r) (b r) = cupMap p q y b := by
    have h₃ (c : I) : ∏ r, A (update (update a p c) q c r) (b r) =
        A c (b p) * A c (b q) * ∏ r : {r : P // r ≠ p ∧ r ≠ q}, A (a r.1) (b r.1) := by
      rw [prod_eq_mul_mul_prod_subtype hpq, update_of_ne hpq, update_self, update_self, mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun r _ ↦ ?_
      rw [update_of_ne r.2.2, update_of_ne r.2.1]
    simp only [h₃]
    rw [← Finset.sum_mul, h₁, cupMap_apply]
    split_ifs <;> simp [y]
  have h₃ : ∑ c, (tensorRep A *ᵥ f) (update (update a p c) q c) = ∑ b, cupMap p q y b * f b := by
    simp only [mulVec, dotProduct, tensorRep, kroneckerFamily_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [← Finset.sum_mul, h₂]
  rw [h₃]
  exact sum_mul_eq_zero_of_isCupAt hf hpq (isCupAt_cupMap y)

end Traceless

section Operators

variable {w d : ℕ} {P P' : Type u} [Fintype P] [DecidableEq P] [Fintype P'] [DecidableEq P']
  {f h : (P → Fin d) → ℂ} (χ : IrrepClass ℂ (ambientGroup w d))

lemma isotypicMatrix_mulVec_mem_traceless (hw : Even w) (hf : f ∈ traceless P (Fin d)) :
    isotypicMatrix χ *ᵥ f ∈ traceless P (Fin d) := by
  refine fun p q hpq a ↦ ?_
  have hint (c : Fin d) : Integrable (fun g : ambientGroup w d ↦
      (tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ f) (update (update a p c) q c) *
        conj (ambientCharacter w d χ g)) (haarProb (ambientGroup w d)) :=
    ((continuous_tensorRep_mulVec f _).mul (Complex.continuous_conj.comp
      (ambientCharacter w d χ).continuous)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  simp only [isotypicMatrix_mulVec_apply, ← Finset.mul_sum]
  rw [← integral_finsetSum _ fun c _ ↦ hint c]
  have h₁ (g : ambientGroup w d) : ∑ c, (tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ f)
      (update (update a p c) q c) * conj (ambientCharacter w d χ g) = 0 := by
    rw [← Finset.sum_mul,
      tensorRep_mulVec_mem_traceless (transpose_mul_self_ambient hw g) hf p q hpq a, zero_mul]
  simp only [h₁, integral_zero, mul_zero]

/-- **An operator between tensor powers of different degrees commuting with `O(d)` sends the
traceless tensors to combinations of cups.** -/
lemma mulVec_mem_cupSpan_of_card_ne (hw : Even w) (hcard : Fintype.card P ≠ Fintype.card P')
    {F : Matrix (P' → Fin d) (P → Fin d) ℂ}
    (hF : ∀ g : ambientGroup w d, tensorRep (g : Matrix (Fin d) (Fin d) ℂ) * F =
      F * tensorRep (g : Matrix (Fin d) (Fin d) ℂ)) (hh : h ∈ traceless P (Fin d)) :
    F *ᵥ h ∈ cupSpan P' (Fin d) := by
  rcases eq_sum_smul_brauerMatrix hw hF with ⟨c, rfl⟩
  rw [sum_mulVec]
  refine Submodule.sum_mem _ fun π _ ↦ ?_
  rw [smul_mulVec]
  refine Submodule.smul_mem _ _ ?_
  by_cases h₁ : ∃ p q, π.val (.inl p) = .inl q
  · rcases h₁ with ⟨p, q, hq⟩
    have hpq : p ≠ q := fun h₂ ↦ π.apply_ne (.inl p) (by rw [hq, h₂])
    exact Submodule.subset_span ⟨p, q, hpq, brauerMatrix_mulVec_isCupAt hq h⟩
  · by_cases h₂ : ∃ p q, π.val (.inr p) = .inr q
    · rcases h₂ with ⟨p, q, hq⟩
      rw [brauerMatrix_mulVec_eq_zero hq hh]
      exact Submodule.zero_mem _
    · push Not at h₁ h₂
      have h₃ (p : P') : ∃ q, π.val (.inl p) = .inr q := by
        rcases hπ : π.val (.inl p) with q | q
        · exact absurd hπ (h₁ p q)
        · exact ⟨q, rfl⟩
      have h₄ (p : P) : ∃ q, π.val (.inr p) = .inl q := by
        rcases hπ : π.val (.inr p) with q | q
        · exact ⟨q, rfl⟩
        · exact absurd hπ (h₂ p q)
      choose φ hφ using h₃
      choose ψ hψ using h₄
      have hφ' : Injective φ := fun x y hxy ↦ by
        have h₅ : π.val (.inl x) = π.val (.inl y) := by
          rw [hφ, hφ, hxy]
        exact Sum.inl_injective (π.val.injective h₅)
      have hψ' : Injective ψ := fun x y hxy ↦ by
        have h₅ : π.val (.inr x) = π.val (.inr y) := by
          rw [hψ, hψ, hxy]
        exact Sum.inr_injective (π.val.injective h₅)
      exact absurd (le_antisymm (Fintype.card_le_of_injective ψ hψ')
        (Fintype.card_le_of_injective φ hφ')) hcard

/-- **An operator on a tensor power commuting with `O(d)` acts on the traceless tensors as a
combination of permutations of the slots.** -/
lemma exists_mulVec_eq_asAlgebraHom_of_traceless (hw : Even w)
    {F : Matrix (P → Fin d) (P → Fin d) ℂ}
    (hF : ∀ g : ambientGroup w d, tensorRep (g : Matrix (Fin d) (Fin d) ℂ) * F =
      F * tensorRep (g : Matrix (Fin d) (Fin d) ℂ)) : ∃ z : MonoidAlgebra ℂ (Perm P),
        ∀ h ∈ traceless P (Fin d), F *ᵥ h = (slotRep P (Fin d)).asAlgebraHom z h := by
  rcases eq_sum_smul_brauerMatrix hw hF with ⟨c, rfl⟩
  have h₁ (π : PerfectMatching (P ⊕ P)) : ∃ z : MonoidAlgebra ℂ (Perm P),
      ∀ h ∈ traceless P (Fin d), brauerMatrix π *ᵥ h = (slotRep P (Fin d)).asAlgebraHom z h := by
    by_cases h₂ : ∀ p, ∃ q, π.val (.inr p) = .inl q
    · rcases exists_brauerMatrix_mulVec_eq (I := Fin d) h₂ with ⟨σ, hσ⟩
      refine ⟨MonoidAlgebra.of ℂ (Perm P) σ, fun h _ ↦ ?_⟩
      rw [hσ, Representation.asAlgebraHom_of]
    · push Not at h₂
      rcases h₂ with ⟨p, hp⟩
      have h₃ : ∃ q, π.val (.inr p) = .inr q := by
        rcases hπ : π.val (.inr p) with q | q
        · exact absurd hπ (hp q)
        · exact ⟨q, rfl⟩
      rcases h₃ with ⟨q, hq⟩
      refine ⟨0, fun h hh ↦ ?_⟩
      rw [map_zero, LinearMap.zero_apply]
      exact brauerMatrix_mulVec_eq_zero hq hh
  choose z hz using h₁
  refine ⟨∑ π, c π • z π, fun h hh ↦ ?_⟩
  rw [sum_mulVec, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun π _ ↦ ?_
  rw [smul_mulVec, hz π h hh, map_smul, LinearMap.smul_apply]

lemma ofLp_mem_of_mem_span_orbit {W : Submodule ℂ ((P → Fin d) → ℂ)}
    (hW : ∀ g : ambientGroup w d, ∀ f ∈ W, tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ f ∈ W)
    {z : (P → Fin d) → ℂ} (hz : z ∈ W) {e : EuclideanSpace ℂ (P → Fin d)}
    (he : e ∈ Submodule.span ℂ (Set.range fun g ↦ ambientTensorRep (w := w) g (WithLp.toLp 2 z))) :
    e.ofLp ∈ W :=
  Submodule.span_le (p := W.comap (WithLp.linearEquiv 2 ℂ ((P → Fin d) → ℂ)).toLinearMap).mpr
    (Set.range_subset_iff.mpr fun g ↦ hW g z hz) he

/-- **Two isotypic tensors of the same type are related by an operator commuting with `O(d)`**,
between any two subspaces stable under `O(d)` containing them. -/
lemma exists_matrix_of_isotypic {x : (P → Fin d) → ℂ} {y : (P' → Fin d) → ℂ}
    (hx : isotypicMatrix χ *ᵥ x = x) (hx₀ : x ≠ 0) (hy : isotypicMatrix χ *ᵥ y = y) (hy₀ : y ≠ 0)
    {U : Submodule ℂ ((P → Fin d) → ℂ)} {U' : Submodule ℂ ((P' → Fin d) → ℂ)}
    (hU : ∀ g : ambientGroup w d, ∀ f ∈ U, tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ f ∈ U)
    (hxU : x ∈ U)
    (hU' : ∀ g : ambientGroup w d, ∀ f ∈ U', tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ f ∈ U')
    (hyU : y ∈ U') : ∃ F : Matrix (P' → Fin d) (P → Fin d) ℂ,
      (∀ g : ambientGroup w d, tensorRep (g : Matrix (Fin d) (Fin d) ℂ) * F =
        F * tensorRep (g : Matrix (Fin d) (Fin d) ℂ)) ∧ ∃ v ∈ U, F *ᵥ v ≠ 0 ∧ F *ᵥ v ∈ U' := by
  have hx₁ : ambientProjector χ (WithLp.toLp 2 x) = WithLp.toLp 2 x :=
    WithLp.ofLp_injective 2 ((ambientProjector_apply_ofLp χ _).trans hx)
  have hy₁ : ambientProjector χ (WithLp.toLp 2 y) = WithLp.toLp 2 y :=
    WithLp.ofLp_injective 2 ((ambientProjector_apply_ofLp χ _).trans hy)
  have hx₂ : WithLp.toLp 2 x ≠ 0 := fun h₀ ↦ hx₀ (congrArg WithLp.ofLp h₀)
  have hy₂ : WithLp.toLp 2 y ≠ 0 := fun h₀ ↦ hy₀ (congrArg WithLp.ofLp h₀)
  rcases exists_intertwiner_of_isotypic χ continuous_ambientTensorRep isUnitary_ambientTensorRep
    continuous_ambientTensorRep isUnitary_ambientTensorRep hx₁ hx₂ hy₁ hy₂ with
    ⟨F₀, hF₀, v, hv, hv₁, hv₂⟩
  let L : ((P → Fin d) → ℂ) →ₗ[ℂ] ((P' → Fin d) → ℂ) :=
    (WithLp.linearEquiv 2 ℂ ((P' → Fin d) → ℂ)).toLinearMap ∘ₗ F₀.toLinearMap ∘ₗ
      (WithLp.linearEquiv 2 ℂ ((P → Fin d) → ℂ)).symm.toLinearMap
  have hL (f : (P → Fin d) → ℂ) : LinearMap.toMatrix' L *ᵥ f = (F₀ (WithLp.toLp 2 f)).ofLp :=
    LinearMap.toMatrix'_mulVec L f
  refine ⟨LinearMap.toMatrix' L, fun g ↦ mulVec_injective (funext fun f ↦ ?_), v.ofLp,
    ofLp_mem_of_mem_span_orbit hU hxU hv, ?_, ?_⟩
  · rw [← mulVec_mulVec, ← mulVec_mulVec, hL, hL]
    exact (congrArg WithLp.ofLp (hF₀ g (WithLp.toLp 2 f))).symm
  · rw [hL]
    exact fun h₀ ↦ hv₁ (WithLp.ofLp_injective 2 h₀)
  · rw [hL]
    exact ofLp_mem_of_mem_span_orbit hU' hyU hv₂

lemma exists_isotypicMatrix_mulVec_ne_zero {x : (P → Fin d) → ℂ} (hx : x ≠ 0) :
    ∃ χ : IrrepClass ℂ (ambientGroup w d), isotypicMatrix χ *ᵥ x ≠ 0 := by
  have hx₂ : WithLp.toLp 2 x ≠ 0 := fun h₀ ↦ hx (congrArg WithLp.ofLp h₀)
  rcases exists_isotypicProjector_ne_zero ambientTensorRep continuous_ambientTensorRep
    isUnitary_ambientTensorRep hx₂ with ⟨χ, hχ⟩
  exact ⟨χ, fun h₀ ↦ hχ (WithLp.ofLp_injective 2 ((ambientProjector_apply_ofLp χ _).trans h₀))⟩

variable {m m' : ℕ} {μ : m.Partition} {ν : m'.Partition}

variable (d μ) in
/-- The **Young symmetrizer** of a partition on a tensor power. -/
noncomputable abbrev youngOp : End ℂ ((Fin m → Fin d) → ℂ) :=
  (slotRep (Fin m) (Fin d)).asAlgebraHom (μ.youngSymmetrizer ℂ)

lemma youngOp_apply (x : (Fin m → Fin d) → ℂ) : youngOp d μ x =
    rowOp (slotRep (Fin m) (Fin d)) (partitionRow μ)
      (columnOp (slotRep (Fin m) (Fin d)) (partitionCol μ) x) :=
  LinearMap.congr_fun (asAlgebraHom_youngSymmetrizer μ _) x

variable (μ) in
lemma youngOp_isotypicMatrix_mulVec (x : (Fin m → Fin d) → ℂ) :
    youngOp d μ (isotypicMatrix χ *ᵥ x) = isotypicMatrix χ *ᵥ youngOp d μ x :=
  (LinearMap.congr_fun (Representation.commute_asAlgebraHom_of_forall_commute _
    (commute_mulVecLin_slotRep χ) (μ.youngSymmetrizer ℂ)) x).symm

lemma youngOp_youngOp {t : ℂ}
    (ht : μ.youngSymmetrizer ℂ * μ.youngSymmetrizer ℂ = t • μ.youngSymmetrizer ℂ)
    (z : (Fin m → Fin d) → ℂ) : youngOp d μ (youngOp d μ z) = t • youngOp d μ z := by
  have h₁ : (slotRep (Fin m) (Fin d)).asAlgebraHom (μ.youngSymmetrizer ℂ * μ.youngSymmetrizer ℂ) z =
      (slotRep (Fin m) (Fin d)).asAlgebraHom (t • μ.youngSymmetrizer ℂ) z := by
    rw [ht]
  simpa only [map_mul, End.mul_apply, map_smul, LinearMap.smul_apply] using h₁

lemma isotypicMatrix_mulVec_mulVec (z : (P → Fin d) → ℂ) :
    isotypicMatrix χ *ᵥ (isotypicMatrix χ *ᵥ z) = isotypicMatrix χ *ᵥ z := by
  rw [mulVec_mulVec, isotypicMatrix_mul_self]

variable (d μ) in
/-- The traceless tensors on which the Young symmetrizer of a partition is a given scalar. -/
noncomputable def youngTraceless (κ : ℂ) : Submodule ℂ ((Fin m → Fin d) → ℂ) :=
  traceless (Fin m) (Fin d) ⊓ LinearMap.ker (youngOp d μ - κ • 1)

variable {κ : ℂ} {x : (Fin m → Fin d) → ℂ}

lemma mem_youngTraceless :
    x ∈ youngTraceless d μ κ ↔ x ∈ traceless (Fin m) (Fin d) ∧ youngOp d μ x = κ • x := by
  rw [youngTraceless, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

lemma tensorRep_mulVec_mem_youngTraceless (hw : Even w) (g : ambientGroup w d)
    (hx : x ∈ youngTraceless d μ κ) :
    tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ x ∈ youngTraceless d μ κ := by
  rw [mem_youngTraceless] at hx ⊢
  refine ⟨tensorRep_mulVec_mem_traceless (transpose_mul_self_ambient hw g) hx.1, ?_⟩
  have h₁ :
      Commute (tensorRep (P := Fin m) (g : Matrix (Fin d) (Fin d) ℂ)).mulVecLin (youngOp d μ) :=
    Representation.commute_asAlgebraHom_of_forall_commute _ (fun σ ↦ LinearMap.ext fun f ↦
      (commute_slotRep_tensorRep σ (g : Matrix (Fin d) (Fin d) ℂ) f).symm) _
  have h₂ : youngOp d μ (tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ x) =
      tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ youngOp d μ x :=
    (LinearMap.congr_fun h₁ x).symm
  rw [h₂, hx.2, mulVec_smul]

lemma isotypicMatrix_mulVec_youngOp_mem_youngTraceless (hw : Even w) {t : ℂ}
    (ht : μ.youngSymmetrizer ℂ * μ.youngSymmetrizer ℂ = t • μ.youngSymmetrizer ℂ)
    {z : (Fin m → Fin d) → ℂ} (hz : z ∈ traceless (Fin m) (Fin d)) :
    isotypicMatrix χ *ᵥ youngOp d μ z ∈ youngTraceless d μ t := by
  refine mem_youngTraceless.mpr ⟨isotypicMatrix_mulVec_mem_traceless χ hw
    (asAlgebraHom_mem_traceless _ hz), ?_⟩
  rw [youngOp_isotypicMatrix_mulVec, youngOp_youngOp ht, mulVec_smul]

variable {χ} {t : (Fin m → Fin d) → ℂ}

/-- **An irreducible character of `O(d)` occurs in Weyl's construction for at most one
partition.** -/
lemma ofPartition_eq_of_traceless (hw : Even w) {t' : (Fin m' → Fin d) → ℂ}
    (ht : t ∈ traceless (Fin m) (Fin d)) (ht' : t' ∈ traceless (Fin m') (Fin d))
    (hx : isotypicMatrix χ *ᵥ youngOp d μ t ≠ 0) (hy : isotypicMatrix χ *ᵥ youngOp d ν t' ≠ 0) :
    ofPartition μ = ofPartition ν := by
  rcases exists_youngSymmetrizer_mul_self μ with ⟨κ, hκ₀, hκ⟩
  rcases exists_youngSymmetrizer_mul_self ν with ⟨κ', hκ₀', hκ'⟩
  rcases exists_matrix_of_isotypic χ (isotypicMatrix_mulVec_mulVec χ _) hx
    (isotypicMatrix_mulVec_mulVec χ _) hy (fun g _ hf ↦ tensorRep_mulVec_mem_youngTraceless hw g hf)
    (isotypicMatrix_mulVec_youngOp_mem_youngTraceless χ hw hκ ht)
    (fun g _ hf ↦ tensorRep_mulVec_mem_youngTraceless hw g hf)
    (isotypicMatrix_mulVec_youngOp_mem_youngTraceless χ hw hκ' ht') with ⟨F, hF, v, hv, hv₁, hv₂⟩
  rw [mem_youngTraceless] at hv hv₂
  by_cases hm : m = m'
  · subst hm
    rcases exists_mulVec_eq_asAlgebraHom_of_traceless hw hF with ⟨z, hz⟩
    by_contra hne
    have hνμ : ν ≠ μ := fun h₀ ↦ hne (by rw [h₀])
    refine hv₁ ?_
    have h₁ : (slotRep (Fin m) (Fin d)).asAlgebraHom z (youngOp d μ v) = κ • F *ᵥ v := by
      rw [hv.2, map_smul, hz v hv.1]
    have h₂ : youngOp d ν ((slotRep (Fin m) (Fin d)).asAlgebraHom z (youngOp d μ v)) = 0 :=
      LinearMap.congr_fun (asAlgebraHom_youngSymmetrizer_mul_mul_eq_zero ν
        (slotRep (Fin m) (Fin d)) hνμ z) v
    rw [h₁, map_smul, hv₂.2] at h₂
    exact (smul_eq_zero.mp ((smul_eq_zero.mp h₂).resolve_left hκ₀)).resolve_left hκ₀'
  · have hcard : Fintype.card (Fin m) ≠ Fintype.card (Fin m') := by
      simpa using hm
    exact absurd (eq_zero_of_mem_traceless_of_mem_cupSpan hv₂.1
      (mulVec_mem_cupSpan_of_card_ne hw hcard hF hv.1)) hv₁

/-- **Weyl's construction for a partition contains at most one irreducible character of `O(d)`.** -/
lemma eq_of_traceless {χ' : IrrepClass ℂ (ambientGroup w d)} (hw : Even w)
    {t' : (Fin m → Fin d) → ℂ} (ht : t ∈ traceless (Fin m) (Fin d))
    (ht' : t' ∈ traceless (Fin m) (Fin d)) (hne : isotypicMatrix χ *ᵥ youngOp d μ t ≠ 0)
    (hne' : isotypicMatrix χ' *ᵥ youngOp d μ t' ≠ 0) : χ = χ' := by
  by_contra hχ
  rcases exists_mulVec_eq_asAlgebraHom_of_traceless (P := Fin m) hw
    (tensorRep_mul_isotypicMatrix χ') with ⟨z, hz⟩
  rcases exists_youngSymmetrizer_mul_mul μ z with ⟨l, hl⟩
  rcases exists_youngSymmetrizer_mul_self μ with ⟨κ, hκ₀, hκ⟩
  have hsand {x : (Fin m → Fin d) → ℂ} (hx : x ∈ traceless (Fin m) (Fin d)) :
      youngOp d μ (isotypicMatrix χ' *ᵥ youngOp d μ x) = l • youngOp d μ x := by
    rw [hz _ (asAlgebraHom_mem_traceless _ hx)]
    have h₁ : (slotRep (Fin m) (Fin d)).asAlgebraHom (μ.youngSymmetrizer ℂ * z *
        μ.youngSymmetrizer ℂ) x =
          (slotRep (Fin m) (Fin d)).asAlgebraHom (l • μ.youngSymmetrizer ℂ) x := by
      rw [hl]
    simpa only [map_mul, End.mul_apply, map_smul, LinearMap.smul_apply] using h₁
  have hl₀ : l = 0 := by
    by_contra hl₁
    refine hne ?_
    have h₁ : isotypicMatrix χ *ᵥ youngOp d μ (isotypicMatrix χ' *ᵥ youngOp d μ t) = 0 := by
      rw [← youngOp_isotypicMatrix_mulVec, mulVec_mulVec, isotypicMatrix_mul_eq_zero hχ,
        zero_mulVec, map_zero]
    rw [hsand ht, mulVec_smul] at h₁
    exact (smul_eq_zero.mp h₁).resolve_left hl₁
  refine hne' ?_
  have h₁ : youngOp d μ (isotypicMatrix χ' *ᵥ youngOp d μ t') = l • youngOp d μ t' := hsand ht'
  rw [hl₀, zero_smul, youngOp_isotypicMatrix_mulVec, youngOp_youngOp hκ, mulVec_smul] at h₁
  exact (smul_eq_zero.mp h₁).resolve_left hκ₀

end Operators

end SatoTateGroup
