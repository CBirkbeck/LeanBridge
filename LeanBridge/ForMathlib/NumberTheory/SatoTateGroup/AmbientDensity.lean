import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.IrreducibleMomentMatrix
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.TensorModel
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import TauCeti.RepresentationTheory.Compact.Character.IsotypicProjection

/-!
# Every irreducible character of the ambient group occurs in a tensor power

By the Stone–Weierstrass theorem, the polynomials in the matrix entries are dense in the continuous
functions on the ambient group `USp(2g)` or `O(d)`: they are stable under complex conjugation, the
complex conjugate of a matrix `A` of the group being `Ωᵀ A Ωᵀ⁻¹`, for `Ω` the form defining the
group. So an irreducible character is not orthogonal to all the monomials in the matrix entries,
which are the matrix coefficients of the tensor powers of the standard representation. The isotypic
projector of a tensor power is then nonzero, so that its trace does not vanish.

## Main definitions

* `SatoTateGroup.isotypicMatrix`: the isotypic projector of an irreducible character on a tensor
  power, as a matrix.
* `SatoTateGroup.ambientProjector`: the same projector in Tau Ceti's character theory.

## Main results

* `SatoTateGroup.integral_trace_pow_mul_conj_ne_zero`: an irreducible character occurring in a
  matrix coefficient of a tensor power occurs in its character.
* `SatoTateGroup.exists_integral_trace_pow_mul_conj_ne_zero`: every irreducible character of the
  ambient group occurs in a power of the trace of the standard representation.
-/

open Filter LinearMap Matrix MeasureTheory TauCeti

open scoped ComplexConjugate InnerProductSpace

namespace SatoTateGroup

variable {w d : ℕ}

/-- A matrix entry, as a continuous function on the ambient group. -/
def ambientEntry (a b : Fin d) : C(ambientGroup w d, ℂ) :=
  ⟨fun h ↦ (h : Matrix (Fin d) (Fin d) ℂ) a b,
    (continuous_subtype_val.comp continuous_subtype_val).matrix_elem a b⟩

lemma ambientEntry_apply (a b : Fin d) (h : ambientGroup w d) :
    ambientEntry a b h = (h : Matrix (Fin d) (Fin d) ℂ) a b :=
  rfl

lemma conjTranspose_transpose_ambient (h : ambientGroup w d) :
    (ambientForm w d)ᵀ * (h : Matrix (Fin d) (Fin d) ℂ) =
      ((h : Matrix (Fin d) (Fin d) ℂ)ᴴ)ᵀ * (ambientForm w d)ᵀ := by
  have h₁ : (h : Matrix (Fin d) (Fin d) ℂ)ᵀ * ambientForm w d * h = ambientForm w d := h.2
  have h₂ : (h : Matrix (Fin d) (Fin d) ℂ) * (h : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem h.1.2
  have h₃ : (h : Matrix (Fin d) (Fin d) ℂ)ᵀ * ambientForm w d =
      ambientForm w d * (h : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
    rw [← Matrix.mul_one ((h : Matrix (Fin d) (Fin d) ℂ)ᵀ * ambientForm w d), ← h₂,
      ← Matrix.mul_assoc, h₁]
  have h₄ : ((h : Matrix (Fin d) (Fin d) ℂ)ᵀ * ambientForm w d)ᵀ =
      (ambientForm w d * (h : Matrix (Fin d) (Fin d) ℂ)ᴴ)ᵀ :=
    congrArg transpose h₃
  rwa [transpose_mul, transpose_mul, transpose_transpose] at h₄

lemma star_ambientEntry_mem (hF : IsUnit (ambientForm w d)) (a b : Fin d) :
    star (ambientEntry a b : C(ambientGroup w d, ℂ)) ∈ Algebra.adjoin ℂ
      (Set.range fun p : Fin d × Fin d ↦ (ambientEntry p.1 p.2 : C(ambientGroup w d, ℂ))) := by
  have hF' : IsUnit (ambientForm w d)ᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, det_transpose, ← Matrix.isUnit_iff_isUnit_det]
    exact hF
  have h₁ : star (ambientEntry a b : C(ambientGroup w d, ℂ)) =
      ∑ i, ∑ j, ((ambientForm w d)ᵀ a i * ((ambientForm w d)ᵀ)⁻¹ j b) • ambientEntry i j := by
    ext h
    have h₂ : ((h : Matrix (Fin d) (Fin d) ℂ)ᴴ)ᵀ =
        (ambientForm w d)ᵀ * (h : Matrix (Fin d) (Fin d) ℂ) * ((ambientForm w d)ᵀ)⁻¹ := by
      rw [conjTranspose_transpose_ambient, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hF'), Matrix.mul_one]
    have h₃ : ((h : Matrix (Fin d) (Fin d) ℂ)ᴴ)ᵀ a b = ((ambientForm w d)ᵀ *
        (h : Matrix (Fin d) (Fin d) ℂ) * ((ambientForm w d)ᵀ)⁻¹) a b :=
      congrFun (congrFun h₂ a) b
    simp only [ambientEntry_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply]
    refine h₃.trans ?_
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring1
  have h₂ (i j : Fin d) : (ambientEntry i j : C(ambientGroup w d, ℂ)) ∈ Algebra.adjoin ℂ
      (Set.range fun p : Fin d × Fin d ↦ (ambientEntry p.1 p.2 : C(ambientGroup w d, ℂ))) :=
    Algebra.subset_adjoin ⟨(i, j), rfl⟩
  rw [h₁]
  exact Subalgebra.sum_mem _ fun i _ ↦ Subalgebra.sum_mem _ fun j _ ↦
    Subalgebra.smul_mem _ (h₂ i j) _

/-- The star subalgebra of the polynomials in the matrix entries. -/
noncomputable def ambientPolynomials (hF : IsUnit (ambientForm w d)) :
    StarSubalgebra ℂ C(ambientGroup w d, ℂ) :=
  { Algebra.adjoin ℂ
      (Set.range fun p : Fin d × Fin d ↦ (ambientEntry p.1 p.2 : C(ambientGroup w d, ℂ))) with
    star_mem' := fun {x} hx ↦ by
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        rcases hx with ⟨p, rfl⟩
        exact star_ambientEntry_mem hF p.1 p.2
      | algebraMap c =>
        rw [← algebraMap_star_comm]
        exact Subalgebra.algebraMap_mem _ _
      | add x y _ _ hx hy =>
        rw [star_add]
        exact Subalgebra.add_mem _ hx hy
      | mul x y _ _ hx hy =>
        rw [star_mul]
        exact Subalgebra.mul_mem _ hy hx }

lemma ambientPolynomials_separatesPoints (hF : IsUnit (ambientForm w d)) :
    (ambientPolynomials hF).SeparatesPoints := by
  intro h k hne
  have h₁ : (h : Matrix (Fin d) (Fin d) ℂ) ≠ k := fun h₂ ↦ hne (Subtype.ext (Subtype.ext h₂))
  rcases Function.ne_iff.mp h₁ with ⟨a, ha⟩
  rcases Function.ne_iff.mp ha with ⟨b, hb⟩
  exact ⟨_, ⟨ambientEntry a b, Algebra.subset_adjoin ⟨(a, b), rfl⟩, rfl⟩, hb⟩

/-- A monomial in the matrix entries, as a continuous function on the ambient group. -/
def IsEntryMonomial (f : C(ambientGroup w d, ℂ)) : Prop :=
  ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P) (a b : P → Fin d),
    ∀ h, f h = ∏ p, (h : Matrix (Fin d) (Fin d) ℂ) (a p) (b p)

lemma isEntryMonomial_of_mem_closure {f : C(ambientGroup w d, ℂ)}
    (hf : f ∈ Submonoid.closure (Set.range fun p : Fin d × Fin d ↦
      (ambientEntry p.1 p.2 : C(ambientGroup w d, ℂ)))) : IsEntryMonomial f := by
  induction hf using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with ⟨p, rfl⟩
    exact ⟨Unit, inferInstance, inferInstance, fun _ ↦ p.1, fun _ ↦ p.2, fun h ↦ by
      simp [ambientEntry_apply]⟩
  | one => exact ⟨Empty, inferInstance, inferInstance, Empty.elim, Empty.elim, fun h ↦ by simp⟩
  | mul x y _ _ hx hy =>
    rcases hx with ⟨P, _, _, a, b, hx⟩
    rcases hy with ⟨Q, _, _, a', b', hy⟩
    refine ⟨P ⊕ Q, inferInstance, inferInstance, Sum.elim a a', Sum.elim b b', fun h ↦ ?_⟩
    rw [ContinuousMap.mul_apply, hx, hy, Fintype.prod_sum_type]
    rfl

lemma exists_monomial_integral_ne_zero (hF : IsUnit (ambientForm w d))
    (χ : IrrepClass ℂ (ambientGroup w d)) : ∃ f : C(ambientGroup w d, ℂ), IsEntryMonomial f ∧
      ∫ h, f h * conj (ambientCharacter w d χ h) ∂haarProb (ambientGroup w d) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  let Λ : C(ambientGroup w d, ℂ) →ₗ[ℂ] ℂ :=
    (innerSL ℂ (ContinuousMap.toLp 2 (haarProb (ambientGroup w d)) ℂ
      (ambientCharacter w d χ))).toLinearMap ∘ₗ
        (ContinuousMap.toLp 2 (haarProb (ambientGroup w d)) ℂ).toLinearMap
  have hΛ (f : C(ambientGroup w d, ℂ)) :
      Λ f = ∫ h, f h * conj (ambientCharacter w d χ h) ∂haarProb (ambientGroup w d) :=
    ContinuousMap.inner_toLp _ _ _
  have hcont : Continuous Λ :=
    (innerSL ℂ (ContinuousMap.toLp 2 (haarProb (ambientGroup w d)) ℂ
      (ambientCharacter w d χ))).continuous.comp
        (ContinuousMap.toLp 2 (haarProb (ambientGroup w d)) ℂ).continuous
  have h₁ : ∀ f ∈ (ambientPolynomials hF : Set C(ambientGroup w d, ℂ)), Λ f = 0 := by
    intro f hf
    have h₂ : Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun p : Fin d × Fin d ↦
        (ambientEntry p.1 p.2 : C(ambientGroup w d, ℂ)))) ≤ LinearMap.ker Λ := by
      rw [Algebra.adjoin_eq_span, Submodule.span_le]
      intro x hx
      rw [SetLike.mem_coe, LinearMap.mem_ker, hΛ]
      exact hcon x (isEntryMonomial_of_mem_closure hx)
    exact h₂ hf
  have h₂ : (ambientCharacter w d χ) ∈ (ambientPolynomials hF).topologicalClosure := by
    rw [ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
      (ambientPolynomials_separatesPoints hF)]
    exact StarSubalgebra.mem_top
  have h₃ : Λ (ambientCharacter w d χ) = 0 :=
    closure_minimal (s := (ambientPolynomials hF : Set C(ambientGroup w d, ℂ)))
      (t := {f | Λ f = 0}) h₁ (isClosed_eq hcont continuous_const) h₂
  rw [hΛ, integral_ambientCharacter_mul_conj_self] at h₃
  exact one_ne_zero h₃

section Tensor

variable {P : Type*} [Fintype P]

lemma conjTranspose_tensorRep {I : Type*} (A : Matrix I I ℂ) :
    (tensorRep (P := P) A)ᴴ = tensorRep Aᴴ := by
  ext a b
  simp only [conjTranspose_apply, tensorRep, kroneckerFamily_apply, star_prod]

lemma continuous_ambient_tensorRep_apply (a b : P → Fin d) :
    Continuous fun h : ambientGroup w d ↦ tensorRep (P := P) (h : Matrix (Fin d) (Fin d) ℂ) a b :=
  continuous_finsetProd _ fun _ _ ↦ (ambientEntry _ _).continuous

/-- The **isotypic projector** of an irreducible character `χ` of the ambient group on a tensor
power of the standard representation, as a matrix: `dim χ ∫ conj (χ g) g^{⊗P} dg`. -/
noncomputable def isotypicMatrix (χ : IrrepClass ℂ (ambientGroup w d)) :
    Matrix (P → Fin d) (P → Fin d) ℂ :=
  of fun a b ↦ (χ.model.dim : ℂ) * ∫ g : ambientGroup w d,
    tensorRep (P := P) (g : Matrix (Fin d) (Fin d) ℂ) a b * conj (ambientCharacter w d χ g)
      ∂haarProb (ambientGroup w d)

lemma continuous_tensorRep_mul_conj (χ : IrrepClass ℂ (ambientGroup w d)) (a b : P → Fin d) :
    Continuous fun g : ambientGroup w d ↦ tensorRep (P := P) (g : Matrix (Fin d) (Fin d) ℂ) a b *
      conj (ambientCharacter w d χ g) :=
  (continuous_ambient_tensorRep_apply a b).mul
    (Complex.continuous_conj.comp (ambientCharacter w d χ).continuous)

variable [DecidableEq P]

lemma trace_tensorRep {I : Type*} [Fintype I] (A : Matrix I I ℂ) :
    (tensorRep (P := P) A).trace = A.trace ^ Fintype.card P := by
  have h₁ : A.trace ^ Fintype.card P = ∏ _ : P, ∑ i, A i i := by
    rw [Finset.prod_const, Finset.card_univ, Matrix.trace]
    rfl
  rw [h₁, Finset.prod_univ_sum, Fintype.piFinset_univ]
  rfl

/-- The tensor power of the standard representation of the ambient group. -/
noncomputable def ambientTensorRep :
    ContRepresentation ℂ (ambientGroup w d) (EuclideanSpace ℂ (P → Fin d)) :=
  .ofMonoidHom
    { toFun := fun h ↦ toEuclideanCLM (n := P → Fin d) (𝕜 := ℂ)
        (tensorRep (P := P) (h : Matrix (Fin d) (Fin d) ℂ))
      map_one' := by
        simp [tensorRep_one]
      map_mul' := fun h k ↦ by
        simp [tensorRep_mul] }

lemma ambientTensorRep_apply (h : ambientGroup w d) (x : EuclideanSpace ℂ (P → Fin d))
    (a : P → Fin d) :
    ambientTensorRep h x a = (tensorRep (P := P) (h : Matrix (Fin d) (Fin d) ℂ) *ᵥ x.ofLp) a :=
  rfl

lemma continuous_ambientTensorRep : Continuous (ambientTensorRep (w := w) (d := d) (P := P)) := by
  refine continuous_clm_apply.mpr fun y ↦ ?_
  refine (EuclideanSpace.equiv (P → Fin d) ℂ).symm.continuous.comp (continuous_pi fun a ↦ ?_)
  exact continuous_finsetSum _ fun b _ ↦
    (continuous_ambient_tensorRep_apply a b).mul continuous_const

lemma isUnitary_ambientTensorRep :
    ContRepresentation.IsUnitary (ambientTensorRep (w := w) (d := d) (P := P)) := by
  refine (ContRepresentation.isUnitary_iff_norm_map _).mpr fun h x ↦ ?_
  have h₁ : (h : Matrix (Fin d) (Fin d) ℂ)ᴴ * (h : Matrix (Fin d) (Fin d) ℂ) = 1 :=
    Unitary.star_mul_self_of_mem h.1.2
  have h₂ : (h : Matrix (Fin d) (Fin d) ℂ) * (h : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem h.1.2
  refine ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.map_mem
    (toEuclideanCLM (n := P → Fin d) (𝕜 := ℂ)) (Unitary.mem_iff.mpr ⟨?_, ?_⟩)) x
  · rw [star_eq_conjTranspose, conjTranspose_tensorRep, ← tensorRep_mul, h₁, tensorRep_one]
  · rw [star_eq_conjTranspose, conjTranspose_tensorRep, ← tensorRep_mul, h₂, tensorRep_one]

lemma continuous_tensorRep_mulVec (f : (P → Fin d) → ℂ) (a : P → Fin d) :
    Continuous fun g : ambientGroup w d ↦ (tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ f) a :=
  continuous_finsetSum _ fun b _ ↦ (continuous_ambient_tensorRep_apply a b).mul continuous_const

lemma isotypicMatrix_mulVec_apply (χ : IrrepClass ℂ (ambientGroup w d)) (f : (P → Fin d) → ℂ)
    (a : P → Fin d) : (isotypicMatrix χ *ᵥ f) a = (χ.model.dim : ℂ) * ∫ g : ambientGroup w d,
      (tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ f) a * conj (ambientCharacter w d χ g)
        ∂haarProb (ambientGroup w d) := by
  have h₁ (g : ambientGroup w d) : (tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ f) a *
      conj (ambientCharacter w d χ g) = ∑ b, (tensorRep (P := P) (g : Matrix (Fin d) (Fin d) ℂ) a b
        * conj (ambientCharacter w d χ g)) * f b := by
    simp only [mulVec, dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ ↦ by ring1
  have hint (b : P → Fin d) : Integrable (fun g : ambientGroup w d ↦
      (tensorRep (P := P) (g : Matrix (Fin d) (Fin d) ℂ) a b *
        conj (ambientCharacter w d χ g)) * f b) (haarProb (ambientGroup w d)) :=
    ((continuous_tensorRep_mul_conj χ a b).mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [h₁]
  rw [integral_finsetSum _ fun b _ ↦ hint b, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [integral_mul_const, ← mul_assoc]
  rfl

/-- The projector of Tau Ceti's character theory. -/
noncomputable abbrev ambientProjector (χ : IrrepClass ℂ (ambientGroup w d)) : ContIntertwiningMap
    (ambientTensorRep (w := w) (d := d) (P := P)) (ambientTensorRep (w := w) (d := d) (P := P)) :=
  ContRepresentation.isotypicProjector (ambientTensorRep (w := w) (d := d) (P := P))
    continuous_ambientTensorRep χ.model.rep χ.model.continuous_rep

lemma ambientProjector_apply_ofLp (χ : IrrepClass ℂ (ambientGroup w d))
    (v : EuclideanSpace ℂ (P → Fin d)) :
    (ambientProjector χ v).ofLp = isotypicMatrix χ *ᵥ v.ofLp := by
  funext a
  rw [isotypicMatrix_mulVec_apply]
  have h₁ : ambientProjector χ v = ∫ g, ContRepresentation.isotypicKernel
      χ.model.rep χ.model.continuous_rep g • ambientTensorRep g v ∂haarProb (ambientGroup w d) :=
    ContRepresentation.isotypicProjector_apply _ _ _ _ v
  have hint : Integrable (fun g ↦ ContRepresentation.isotypicKernel
      χ.model.rep χ.model.continuous_rep g • ambientTensorRep g v)
        (haarProb (ambientGroup w d)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
    exact (ContRepresentation.isotypicKernel χ.model.rep χ.model.continuous_rep).continuous.smul
      (continuous_ambientTensorRep.clm_apply continuous_const)
  have h₂ : ∫ g, (EuclideanSpace.proj (𝕜 := ℂ) a) (ContRepresentation.isotypicKernel
      χ.model.rep χ.model.continuous_rep g • ambientTensorRep g v)
        ∂haarProb (ambientGroup w d) = (EuclideanSpace.proj (𝕜 := ℂ) a)
          (∫ g, ContRepresentation.isotypicKernel χ.model.rep χ.model.continuous_rep g •
            ambientTensorRep g v ∂haarProb (ambientGroup w d)) :=
    (EuclideanSpace.proj (𝕜 := ℂ) a).integral_comp_comm hint
  rw [← h₁] at h₂
  have h₃ :
      (ambientProjector χ v).ofLp a = (EuclideanSpace.proj (𝕜 := ℂ) a) (ambientProjector χ v) :=
    rfl
  rw [h₃, ← h₂, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g ↦ ?_)
  have h₄ : (EuclideanSpace.proj (𝕜 := ℂ) a) (ContRepresentation.isotypicKernel
      χ.model.rep χ.model.continuous_rep g • ambientTensorRep g v) =
        ContRepresentation.isotypicKernel χ.model.rep χ.model.continuous_rep g *
          (tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ v.ofLp) a :=
    rfl
  have h₅ : star (ContRepresentation.character χ.model.rep χ.model.continuous_rep g) =
      conj (ambientCharacter w d χ g) :=
    rfl
  have h₆ : Module.finrank ℂ (EuclideanSpace ℂ (Fin χ.model.dim)) = χ.model.dim := by
    simp
  beta_reduce
  rw [h₄, ContRepresentation.isotypicKernel_apply, h₅, h₆]
  ring1

/-- **An irreducible character of the ambient group occurs in the tensor power.** -/
lemma integral_trace_pow_mul_conj_ne_zero (χ : IrrepClass ℂ (ambientGroup w d)) {a b : P → Fin d}
    (h : ∫ h, tensorRep (P := P) (h : Matrix (Fin d) (Fin d) ℂ) a b *
      conj (ambientCharacter w d χ h) ∂haarProb (ambientGroup w d) ≠ 0) : ∫ h,
    (h : Matrix (Fin d) (Fin d) ℂ).trace ^ Fintype.card P *
      conj (ambientCharacter w d χ h) ∂haarProb (ambientGroup w d) ≠ 0 := by
  have hd₀ : (χ.model.dim : ℂ) ≠ 0 := by
    simpa using χ.model.isIrreducible.natCast_finrank_ne_zero
  have hentry (b' a' : P → Fin d) :
      ambientProjector χ (EuclideanSpace.single b' 1) a' = isotypicMatrix χ a' b' := by
    refine (congrFun (ambientProjector_apply_ofLp χ _) a').trans ?_
    rw [PiLp.ofLp_single, mulVec_single_one]
    rfl
  let f : EuclideanSpace ℂ (P → Fin d) →ₗ[ℂ] EuclideanSpace ℂ (P → Fin d) :=
    ((ambientProjector χ).toContinuousLinearMap : _ →L[ℂ] _).toLinearMap
  have hf : IsIdempotentElem f := by
    refine LinearMap.ext fun v ↦ ?_
    exact congrArg (fun R : ContIntertwiningMap ambientTensorRep ambientTensorRep ↦ R v)
      (ContRepresentation.isotypicProjector_idempotent _ continuous_ambientTensorRep
        isUnitary_ambientTensorRep _ _ χ.model.isIrreducible)
  have hne : f ≠ 0 := by
    intro h₀
    have h₂ : ambientProjector χ (EuclideanSpace.single b 1) = 0 := LinearMap.congr_fun h₀ _
    exact mul_ne_zero hd₀ h ((hentry b a).symm.trans (congrArg (fun x ↦ x.ofLp a) h₂))
  refine fun h₀ ↦ hne (IsIdempotentElem.eq_zero_of_trace_eq_zero hf ?_)
  rw [LinearMap.trace_eq_sum_inner f (EuclideanSpace.basisFun (P → Fin d) ℂ)]
  have h₁ (a' : P → Fin d) : ⟪EuclideanSpace.basisFun (P → Fin d) ℂ a',
      f (EuclideanSpace.basisFun (P → Fin d) ℂ a')⟫_ℂ = (χ.model.dim : ℂ) * ∫ g, tensorRep (P := P)
        (g : Matrix (Fin d) (Fin d) ℂ) a' a' * conj (ambientCharacter w d χ g)
          ∂haarProb (ambientGroup w d) := by
    rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, map_one, one_mul]
    exact hentry a' a'
  have h₂ (g : ambientGroup w d) : ∑ a', tensorRep (P := P)
      (g : Matrix (Fin d) (Fin d) ℂ) a' a' * conj (ambientCharacter w d χ g) =
        (g : Matrix (Fin d) (Fin d) ℂ).trace ^ Fintype.card P *
          conj (ambientCharacter w d χ g) := by
    rw [← Finset.sum_mul, ← trace_tensorRep]
    rfl
  simp only [h₁]
  rw [← Finset.mul_sum, ← integral_finsetSum _ fun a' _ ↦
    (continuous_tensorRep_mul_conj χ a' a').integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)]
  simp only [h₂, h₀, mul_zero]

/-- **Every irreducible character of the ambient group occurs in a power of the trace of the
standard representation**, when the form defining the group is nondegenerate. -/
lemma exists_integral_trace_pow_mul_conj_ne_zero (hF : IsUnit (ambientForm w d))
    (χ : IrrepClass ℂ (ambientGroup w d)) : ∃ n : ℕ, ∫ h, (h : Matrix (Fin d) (Fin d) ℂ).trace ^ n *
      conj (ambientCharacter w d χ h) ∂haarProb (ambientGroup w d) ≠ 0 := by
  rcases exists_monomial_integral_ne_zero hF χ with ⟨f, ⟨Q, _, _, a, b, hf⟩, hne⟩
  refine ⟨Fintype.card Q, integral_trace_pow_mul_conj_ne_zero (P := Q) χ (a := a) (b := b) ?_⟩
  simp only [hf] at hne
  exact hne

end Tensor

end SatoTateGroup
