import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import TauCeti.Algebra.Lie.HighestWeight.Weyl.Character
import TauCeti.Algebra.Lie.Symplectic.Killing

/-!
# The diagonal Cartan subalgebra of the symplectic Lie algebra

The diagonal matrices `diag(d, -d)` form a Cartan subalgebra `H` of the symplectic Lie algebra
`𝔰𝔭(2g, ℂ) = Symplectic.sp (Fin g) ℂ`, and this file computes the root system of `H`: the
roots are the `ε_a - ε_b`, where `ε_{inl i} = εᵢ` and `ε_{inr i} = -εᵢ`, and the simple roots
`εᵢ - εᵢ₊₁`, `2 ε_g` give a base.

## Main definitions

* `SatoTateGroup.spDiag`: the matrix `diag(d, -d)`.
* `SatoTateGroup.spCartan`: the diagonal Cartan subalgebra `H`.
* `SatoTateGroup.spEpsilon`: the coordinate functionals `εᵢ` of `H`.
* `SatoTateGroup.spRootVector`: the root vector of the root `ε_a - ε_b`.
* `SatoTateGroup.spBase`: the base of the root system of `H`.

## Main results

* `SatoTateGroup.spCartan_normalizer_eq_self`: `H` is self-normalizing.
* `SatoTateGroup.exists_eq_spRootForm`: the roots of `H` are the `ε_a - ε_b`.
-/

open LieAlgebra LieModule Matrix Module RootPairing

attribute [local instance 100] LieRing.ofAssociativeRing

namespace SatoTateGroup

variable {g : ℕ}

/-- The values `d₁, …, d_g, -d₁, …, -d_g` on the indices `Fin g ⊕ Fin g`. -/
def spValue (d : Fin g → ℂ) : Fin g ⊕ Fin g → ℂ :=
  Sum.elim d fun i ↦ -d i

lemma spValue_inl (d : Fin g → ℂ) (i : Fin g) : spValue d (.inl i) = d i :=
  rfl

lemma spValue_inr (d : Fin g → ℂ) (i : Fin g) : spValue d (.inr i) = -d i :=
  rfl

lemma diagonal_spValue_mem (d : Fin g → ℂ) : diagonal (spValue d) ∈ Symplectic.sp (Fin g) ℂ := by
  rw [mem_symplecticLieAlgebra_iff]
  refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩
  · simp
  · simp
  · by_cases h : i = j
    · subst h
      simp [spValue_inl, spValue_inr]
    · have h' : j ≠ i := Ne.symm h
      simp [h, h']

/-- The matrix `diag(d, -d)`, as a linear map from `ℂ^g` to `𝔰𝔭(2g, ℂ)`. -/
noncomputable def spDiag : (Fin g → ℂ) →ₗ[ℂ] Symplectic.sp (Fin g) ℂ where
  toFun d := ⟨diagonal (spValue d), diagonal_spValue_mem d⟩
  map_add' d d' := Subtype.ext <| by
    ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [spValue, h]
    ring1
  map_smul' c d := Subtype.ext <| by
    ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [spValue, h]

lemma coe_spDiag (d : Fin g → ℂ) : (spDiag d : Matrix _ _ ℂ) = diagonal (spValue d) :=
  rfl

lemma spDiag_lie_apply (d : Fin g → ℂ) (X : Symplectic.sp (Fin g) ℂ) (a b : Fin g ⊕ Fin g) :
    (⁅spDiag d, X⁆ : Symplectic.sp (Fin g) ℂ).1 a b = (spValue d a - spValue d b) * X.1 a b := by
  rw [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket, coe_spDiag, Matrix.sub_apply,
    diagonal_mul, mul_diagonal]
  ring1

lemma spDiag_lie_spDiag (d d' : Fin g → ℂ) : ⁅spDiag d, spDiag d'⁆ = 0 := Subtype.ext <| by
  rw [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket, coe_spDiag, coe_spDiag,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  simp [mul_comm]

/-- The **diagonal Cartan subalgebra** of `𝔰𝔭(2g, ℂ)`, the matrices `diag(d, -d)`. -/
noncomputable def spCartan : LieSubalgebra ℂ (Symplectic.sp (Fin g) ℂ) where
  toSubmodule := LinearMap.range spDiag
  lie_mem' := by
    rintro _ _ ⟨d, rfl⟩ ⟨d', rfl⟩
    exact ⟨0, by rw [map_zero, spDiag_lie_spDiag]⟩

lemma spDiag_mem_spCartan (d : Fin g → ℂ) : spDiag d ∈ spCartan (g := g) :=
  ⟨d, rfl⟩

instance : IsLieAbelian (spCartan (g := g)) where
  trivial := by
    rintro ⟨_, d, rfl⟩ ⟨_, d', rfl⟩
    exact Subtype.ext (spDiag_lie_spDiag d d')

lemma exists_spValue_sub_ne_zero {a b : Fin g ⊕ Fin g} (hab : a ≠ b) :
    ∃ d : Fin g → ℂ, spValue d a - spValue d b ≠ 0 := by
  classical
  rcases a with i | i <;> rcases b with j | j
  · exact ⟨Pi.single i 1, by
      have hij : i ≠ j := fun h ↦ hab (congrArg Sum.inl h)
      simp [spValue, hij]⟩
  · by_cases hij : i = j
    · subst hij
      exact ⟨Pi.single i 1, by norm_num [spValue]⟩
    · exact ⟨Pi.single i 1, by simp [spValue, hij]⟩
  · by_cases hij : i = j
    · subst hij
      exact ⟨Pi.single i 1, by norm_num [spValue]⟩
    · exact ⟨Pi.single i 1, by simp [spValue, hij]⟩
  · exact ⟨Pi.single i 1, by
      have hij : i ≠ j := fun h ↦ hab (congrArg Sum.inr h)
      simp [spValue, hij]⟩

/-- **`H` is self-normalizing.** -/
lemma spCartan_normalizer_eq_self : (spCartan (g := g)).normalizer = spCartan := by
  refine le_antisymm (fun X hX ↦ ?_) (LieSubalgebra.le_normalizer _)
  have hoff {a b : Fin g ⊕ Fin g} (hab : a ≠ b) : X.1 a b = 0 := by
    rcases exists_spValue_sub_ne_zero hab with ⟨d, hd⟩
    have h₁ : ⁅spDiag d, X⁆ ∈ spCartan (g := g) :=
      (LieSubalgebra.mem_normalizer_iff' _ X).mp hX (spDiag d) (spDiag_mem_spCartan d)
    rcases h₁ with ⟨d', hd'⟩
    have h₂ : (⁅spDiag d, X⁆ : Symplectic.sp (Fin g) ℂ).1 a b = 0 := by
      rw [← hd', coe_spDiag, diagonal_apply_ne _ hab]
    rw [spDiag_lie_apply] at h₂
    exact (mul_eq_zero.mp h₂).resolve_left hd
  have hdiag (i : Fin g) : X.1 (.inr i) (.inr i) = -X.1 (.inl i) (.inl i) :=
    ((mem_symplecticLieAlgebra_iff _).mp X.2).2.2 i i
  refine ⟨fun i ↦ X.1 (.inl i) (.inl i), Subtype.ext ?_⟩
  ext a b
  by_cases hab : a = b
  · subst hab
    rcases a with i | i
    · simp [coe_spDiag, spValue_inl]
    · simp [coe_spDiag, spValue_inr, hdiag]
  · rw [coe_spDiag, diagonal_apply_ne _ hab, hoff hab]

instance : (spCartan (g := g)).IsCartanSubalgebra where
  nilpotent := inferInstance
  self_normalizing := spCartan_normalizer_eq_self

/-- The coordinate functional `εᵢ` of the diagonal Cartan subalgebra. -/
noncomputable def spEpsilon (i : Fin g) : Dual ℂ (spCartan (g := g)) where
  toFun h := h.1.1 (.inl i) (.inl i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma spEpsilon_spDiag (i : Fin g) (d : Fin g → ℂ) :
    spEpsilon i ⟨spDiag d, spDiag_mem_spCartan d⟩ = d i :=
  diagonal_apply_eq (spValue d) (.inl i)

/-- The weight `ε_a` of the standard module, for `a : Fin g ⊕ Fin g`: `εᵢ` for `a = inl i` and `-εᵢ`
for `a = inr i`. -/
noncomputable def spEps : Fin g ⊕ Fin g → Dual ℂ (spCartan (g := g)) :=
  Sum.elim spEpsilon fun i ↦ -spEpsilon i

lemma spEps_spDiag (a : Fin g ⊕ Fin g) (d : Fin g → ℂ) :
    spEps a ⟨spDiag d, spDiag_mem_spCartan d⟩ = spValue d a := by
  rcases a with i | i
  · exact spEpsilon_spDiag i d
  · exact congrArg Neg.neg (spEpsilon_spDiag i d)

lemma exists_eq_spDiag (h : spCartan (g := g)) :
    h = ⟨spDiag fun i ↦ spEpsilon i h, spDiag_mem_spCartan _⟩ := by
  rcases h with ⟨_, d, rfl⟩
  exact Subtype.ext (congrArg spDiag (funext fun i ↦ (spEpsilon_spDiag i d).symm))

instance : IsKilling ℂ (Symplectic.sp (Fin g) ℂ) :=
  HasTrivialRadical.instIsKilling ℂ _

/-- The sign `1` on `inl i` and `-1` on `inr i`. -/
def spSgn : Fin g ⊕ Fin g → ℂ :=
  Sum.elim (fun _ ↦ 1) fun _ ↦ -1

/-- The root vector `E_{a b} - σ_a σ_b E_{-b, -a}` of `𝔰𝔭(2g, ℂ)`, of weight `ε_a - ε_b`, for the
sign `σ` of `spSgn` and `-(inl i) = inr i`, `-(inr i) = inl i`. -/
noncomputable def spRootVector (a b : Fin g ⊕ Fin g) : Symplectic.sp (Fin g) ℂ :=
  ⟨single a b 1 - (spSgn a * spSgn b) • single b.swap a.swap 1, by
    rw [mem_symplecticLieAlgebra_iff]
    rcases a with i | i <;> rcases b with j | j <;>
      refine ⟨fun p q ↦ ?_, fun p q ↦ ?_, fun p q ↦ ?_⟩ <;>
      simp [spSgn] <;> grind⟩

lemma spValue_swap (d : Fin g → ℂ) (a : Fin g ⊕ Fin g) : spValue d a.swap = -spValue d a := by
  rcases a with i | i <;> simp [spValue]

lemma spRootVector_apply (a b p q : Fin g ⊕ Fin g) : (spRootVector a b).1 p q =
    (if a = p ∧ b = q then 1 else 0) -
      spSgn a * spSgn b * if b.swap = p ∧ a.swap = q then 1 else 0 := by
  simp [spRootVector, single_apply]

lemma spDiag_lie_spRootVector (d : Fin g → ℂ) (a b : Fin g ⊕ Fin g) :
    ⁅spDiag d, spRootVector a b⁆ = (spValue d a - spValue d b) • spRootVector a b := by
  refine Subtype.ext ?_
  ext p q
  have h₀ : ((spValue d a - spValue d b) • spRootVector a b).1 p q =
      (spValue d a - spValue d b) * (spRootVector a b).1 p q := rfl
  rw [spDiag_lie_apply, h₀]
  by_cases h₁ : a = p ∧ b = q
  · rw [h₁.1, h₁.2]
  by_cases h₂ : b.swap = p ∧ a.swap = q
  · rw [← h₂.1, ← h₂.2, spValue_swap, spValue_swap]
    ring1
  · rw [spRootVector_apply, ite_eq_right h₁, ite_eq_right h₂]
    ring1

/-- The linear form `ε_a - ε_b` on the diagonal Cartan subalgebra. -/
noncomputable def spRootForm (a b : Fin g ⊕ Fin g) : Dual ℂ (spCartan (g := g)) :=
  spEps a - spEps b

lemma spRootForm_spDiag (a b : Fin g ⊕ Fin g) (d : Fin g → ℂ) :
    spRootForm a b ⟨spDiag d, spDiag_mem_spCartan d⟩ = spValue d a - spValue d b := by
  rw [spRootForm, LinearMap.sub_apply, spEps_spDiag, spEps_spDiag]

lemma spRootVector_ne_zero {a b : Fin g ⊕ Fin g} (hab : a ≠ b) : spRootVector a b ≠ 0 := fun h ↦ by
  have h₁ : (spRootVector a b).1 a b = 0 := by
    rw [h]
    rfl
  rw [spRootVector_apply, ite_eq_left ⟨rfl, rfl⟩] at h₁
  by_cases h₂ : b.swap = a ∧ a.swap = b
  · rw [ite_eq_left h₂] at h₁
    have h₃ : spSgn a * spSgn b = -1 := by
      rcases a with i | i <;> rcases b with j | j <;> simp [spSgn] at h₂ ⊢
    rw [h₃] at h₁
    norm_num at h₁
  · rw [ite_eq_right h₂] at h₁
    norm_num at h₁

lemma spRootVector_mem_rootSpace (a b : Fin g ⊕ Fin g) :
    spRootVector a b ∈ rootSpace (spCartan (g := g)) (spRootForm a b) := by
  refine LieModule.weightSpace_le_genWeightSpace _ _ ?_
  rw [LieModule.mem_weightSpace]
  rintro ⟨_, d, rfl⟩
  have h₁ : ⁅spDiag d, spRootVector a b⁆ = (spValue d a - spValue d b) • spRootVector a b :=
    spDiag_lie_spRootVector d a b
  rw [← spRootForm_spDiag] at h₁
  exact h₁

/-- The weight `ε_a - ε_b`, for `a ≠ b`, a root of the diagonal Cartan subalgebra. -/
noncomputable def spWeight (a b : Fin g ⊕ Fin g) (hab : a ≠ b) :
    Weight ℂ (spCartan (g := g)) (Symplectic.sp (Fin g) ℂ) where
  toFun := spRootForm a b
  genWeightSpace_ne_bot' := fun h ↦ spRootVector_ne_zero hab <| by
    have h₁ : spRootVector a b ∈ rootSpace (spCartan (g := g)) (spRootForm a b) :=
      spRootVector_mem_rootSpace a b
    rw [rootSpace, h] at h₁
    simpa using h₁

lemma spRootForm_ne_zero {a b : Fin g ⊕ Fin g} (hab : a ≠ b) : spRootForm a b ≠ 0 := fun h ↦ by
  rcases exists_spValue_sub_ne_zero hab with ⟨d, hd⟩
  refine hd ?_
  rw [← spRootForm_spDiag, h]
  rfl

lemma isNonZero_spWeight (a b : Fin g ⊕ Fin g) (hab : a ≠ b) : (spWeight a b hab).IsNonZero :=
  fun h ↦ spRootForm_ne_zero hab (DFunLike.coe_injective h)

lemma coe_spWeight (a b : Fin g ⊕ Fin g) (hab : a ≠ b) :
    (spWeight a b hab : spCartan (g := g) → ℂ) = spRootForm a b :=
  rfl

/-- **The roots of the diagonal Cartan subalgebra are the `ε_a - ε_b`.** -/
lemma exists_eq_spRootForm (α : Weight ℂ (spCartan (g := g)) (Symplectic.sp (Fin g) ℂ))
    (hα : α.IsNonZero) : ∃ a b, a ≠ b ∧ (α : spCartan (g := g) → ℂ) = spRootForm a b := by
  rcases α.exists_ne_zero with ⟨x, hx, hx₀⟩
  have hentry : ∃ p q, x.1 p q ≠ 0 := by
    by_contra h
    push Not at h
    exact hx₀ (Subtype.ext (Matrix.ext h))
  rcases hentry with ⟨p, q, hpq⟩
  have hα₁ (d : Fin g → ℂ) : α ⟨spDiag d, spDiag_mem_spCartan d⟩ = spValue d p - spValue d q := by
    have h₁ : ⁅(⟨spDiag d, spDiag_mem_spCartan d⟩ : spCartan (g := g)), x⁆ =
        α ⟨spDiag d, spDiag_mem_spCartan d⟩ • x :=
      IsKilling.lie_eq_smul_of_mem_rootSpace hx _
    have h₂ : (⁅spDiag d, x⁆ : Symplectic.sp (Fin g) ℂ).1 p q =
        α ⟨spDiag d, spDiag_mem_spCartan d⟩ * x.1 p q :=
      congrFun (congrFun (congrArg Subtype.val h₁) p) q
    rw [spDiag_lie_apply] at h₂
    exact (mul_right_cancel₀ hpq h₂).symm
  have heq : (α : spCartan (g := g) → ℂ) = spRootForm p q := by
    funext h
    rcases h with ⟨_, d, rfl⟩
    rw [hα₁ d]
    exact (spRootForm_spDiag p q d).symm
  refine ⟨p, q, ?_, heq⟩
  rintro rfl
  refine hα ?_
  rw [Weight.IsZero, heq]
  funext h
  rw [spRootForm, sub_self]
  rfl

lemma neg_spRootForm (a b : Fin g ⊕ Fin g) : -spRootForm a b = spRootForm b a := by
  rw [spRootForm, spRootForm, neg_sub]

lemma spDiag_ne_zero {d : Fin g → ℂ} (hd : d ≠ 0) : spDiag d ≠ 0 := fun h ↦ hd <| by
  funext i
  have h₁ : (spDiag d).1 (.inl i) (.inl i) = 0 := by
    rw [h]
    rfl
  rwa [coe_spDiag, diagonal_apply_eq, spValue_inl] at h₁

lemma spRootVector_inl_inl (i j : Fin g) : (spRootVector (.inl i) (.inl j)).1 =
    single (.inl i) (.inl j) 1 - single (.inr j) (.inr i) 1 := by
  simp [spRootVector, spSgn]

lemma spRootVector_lie_short {i j : Fin g} (hij : i ≠ j) :
    ⁅spRootVector (.inl i) (.inl j), spRootVector (.inl j) (.inl i)⁆ =
      spDiag (Pi.single i 1 - Pi.single j 1) := by
  refine Subtype.ext ?_
  rw [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket, spRootVector_inl_inl,
    spRootVector_inl_inl, coe_spDiag]
  simp only [Matrix.sub_mul, Matrix.mul_sub]
  ext (p | p) (q | q) <;> by_cases hpq : p = q <;>
    simp [spValue, hpq] <;> grind

lemma isSl2Triple_short {i j : Fin g} (hij : i ≠ j) :
    IsSl2Triple (spDiag (Pi.single i 1 - Pi.single j 1)) (spRootVector (.inl i) (.inl j))
      (spRootVector (.inl j) (.inl i)) where
  h_ne_zero := spDiag_ne_zero fun h ↦ by
    have h₁ : (Pi.single i 1 - Pi.single j 1 : Fin g → ℂ) i = 0 := by
      rw [h]
      rfl
    simp [hij] at h₁
  lie_e_f := spRootVector_lie_short hij
  lie_h_e_nsmul := by
    rw [spDiag_lie_spRootVector]
    have h₁ : spValue (Pi.single i 1 - Pi.single j 1 : Fin g → ℂ) (.inl i) -
        spValue (Pi.single i 1 - Pi.single j 1 : Fin g → ℂ) (.inl j) = 2 := by
      simp [spValue, hij.symm]
      norm_num
    rw [h₁, two_smul, two_smul]
  lie_h_f_nsmul := by
    rw [spDiag_lie_spRootVector]
    have h₁ : spValue (Pi.single i 1 - Pi.single j 1 : Fin g → ℂ) (.inl j) -
        spValue (Pi.single i 1 - Pi.single j 1 : Fin g → ℂ) (.inl i) = -2 := by
      simp [spValue, hij.symm]
      norm_num
    rw [h₁, neg_smul, two_smul, two_smul]

/-- The element `E_{i, -i}` of `𝔰𝔭(2g, ℂ)`, half of `spRootVector (inl i) (inr i)`. -/
noncomputable def spRaise (i : Fin g) : Symplectic.sp (Fin g) ℂ :=
  ⟨single (.inl i) (.inr i) 1, by
    rw [mem_symplecticLieAlgebra_iff]
    refine ⟨fun p q ↦ ?_, fun p q ↦ ?_, fun p q ↦ ?_⟩ <;> simp [single_apply]
    grind⟩

/-- The element `E_{-i, i}` of `𝔰𝔭(2g, ℂ)`, half of `spRootVector (inr i) (inl i)`. -/
noncomputable def spLower (i : Fin g) : Symplectic.sp (Fin g) ℂ :=
  ⟨single (.inr i) (.inl i) 1, by
    rw [mem_symplecticLieAlgebra_iff]
    refine ⟨fun p q ↦ ?_, fun p q ↦ ?_, fun p q ↦ ?_⟩ <;> simp [single_apply]
    grind⟩

lemma spDiag_lie_spRaise (d : Fin g → ℂ) (i : Fin g) :
    ⁅spDiag d, spRaise i⁆ = (2 * d i) • spRaise i := by
  refine Subtype.ext ?_
  ext p q
  have h₀ : ((2 * d i) • spRaise i).1 p q = (2 * d i) * (spRaise i).1 p q := rfl
  rw [spDiag_lie_apply, h₀]
  by_cases h₁ : Sum.inl i = p ∧ Sum.inr i = q
  · rw [← h₁.1, ← h₁.2, spValue_inl, spValue_inr]
    ring1
  · have h₂ : (spRaise i).1 p q = 0 := by
      simp [spRaise, h₁]
    rw [h₂, mul_zero, mul_zero]

lemma spDiag_lie_spLower (d : Fin g → ℂ) (i : Fin g) :
    ⁅spDiag d, spLower i⁆ = (-(2 * d i)) • spLower i := by
  refine Subtype.ext ?_
  ext p q
  have h₀ : ((-(2 * d i)) • spLower i).1 p q = (-(2 * d i)) * (spLower i).1 p q := rfl
  rw [spDiag_lie_apply, h₀]
  by_cases h₁ : Sum.inr i = p ∧ Sum.inl i = q
  · rw [← h₁.1, ← h₁.2, spValue_inl, spValue_inr]
    ring1
  · have h₂ : (spLower i).1 p q = 0 := by
      simp [spLower, h₁]
    rw [h₂, mul_zero, mul_zero]

lemma spRaise_lie_spLower (i : Fin g) : ⁅spRaise i, spLower i⁆ = spDiag (Pi.single i 1) := by
  refine Subtype.ext ?_
  rw [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket, coe_spDiag]
  simp only [spRaise, spLower]
  ext (p | p) (q | q) <;> by_cases hpq : p = q <;>
    simp [spValue, hpq] <;> grind

lemma isSl2Triple_long (i : Fin g) :
    IsSl2Triple (spDiag (Pi.single i 1)) (spRaise i) (spLower i) where
  h_ne_zero := spDiag_ne_zero fun h ↦ by
    have h₁ : (Pi.single i 1 : Fin g → ℂ) i = 0 := by
      rw [h]
      rfl
    simp at h₁
  lie_e_f := spRaise_lie_spLower i
  lie_h_e_nsmul := by
    rw [spDiag_lie_spRaise, Pi.single_eq_same, mul_one, two_smul, two_smul]
  lie_h_f_nsmul := by
    rw [spDiag_lie_spLower, Pi.single_eq_same, mul_one, neg_smul, two_smul, two_smul]

lemma spRaise_mem_rootSpace (i : Fin g) :
    spRaise i ∈ rootSpace (spCartan (g := g)) (spRootForm (.inl i) (.inr i)) := by
  refine LieModule.weightSpace_le_genWeightSpace _ _ ?_
  rw [LieModule.mem_weightSpace]
  rintro ⟨_, d, rfl⟩
  have h₁ : ⁅spDiag d, spRaise i⁆ = (2 * d i) • spRaise i := spDiag_lie_spRaise d i
  have h₂ : 2 * d i = spRootForm (.inl i) (.inr i) ⟨spDiag d, spDiag_mem_spCartan d⟩ := by
    rw [spRootForm_spDiag, spValue_inl, spValue_inr]
    ring1
  rw [h₂] at h₁
  exact h₁

lemma spLower_mem_rootSpace (i : Fin g) :
    spLower i ∈ rootSpace (spCartan (g := g)) (spRootForm (.inr i) (.inl i)) := by
  refine LieModule.weightSpace_le_genWeightSpace _ _ ?_
  rw [LieModule.mem_weightSpace]
  rintro ⟨_, d, rfl⟩
  have h₁ : ⁅spDiag d, spLower i⁆ = (-(2 * d i)) • spLower i := spDiag_lie_spLower d i
  have h₂ : -(2 * d i) = spRootForm (.inr i) (.inl i) ⟨spDiag d, spDiag_mem_spCartan d⟩ := by
    rw [spRootForm_spDiag, spValue_inl, spValue_inr]
    ring1
  rw [h₂] at h₁
  exact h₁

lemma coroot_short {i j : Fin g} (hij : i ≠ j) (hne : (Sum.inl i : Fin g ⊕ Fin g) ≠ Sum.inl j) :
    ((IsKilling.coroot (spWeight (.inl i) (.inl j) hne) : spCartan (g := g)) :
      Symplectic.sp (Fin g) ℂ) = spDiag (Pi.single i 1 - Pi.single j 1) := by
  refine ((isSl2Triple_short hij).h_eq_coroot (isNonZero_spWeight _ _ hne)
    (spRootVector_mem_rootSpace _ _) ?_).symm
  have h₁ : spRootVector (.inl j) (.inl i) ∈
      rootSpace (spCartan (g := g)) (spRootForm (.inl j) (.inl i)) :=
    spRootVector_mem_rootSpace _ _
  rw [← neg_spRootForm] at h₁
  exact h₁

lemma coroot_long (i : Fin g) (hne : (Sum.inl i : Fin g ⊕ Fin g) ≠ Sum.inr i) :
    ((IsKilling.coroot (spWeight (.inl i) (.inr i) hne) : spCartan (g := g)) :
      Symplectic.sp (Fin g) ℂ) = spDiag (Pi.single i 1) := by
  refine ((isSl2Triple_long i).h_eq_coroot (isNonZero_spWeight _ _ hne)
    (spRaise_mem_rootSpace i) ?_).symm
  have h₁ : spLower i ∈ rootSpace (spCartan (g := g)) (spRootForm (.inr i) (.inl i)) :=
    spLower_mem_rootSpace i
  rw [← neg_spRootForm] at h₁
  exact h₁

/-- The element `diag(δᵢ, -δᵢ)` of the diagonal Cartan subalgebra. -/
noncomputable def spDelta (i : Fin g) : spCartan (g := g) :=
  ⟨spDiag (Pi.single i 1), spDiag_mem_spCartan _⟩

lemma spEpsilon_spDelta (i j : Fin g) : spEpsilon i (spDelta j) = (Pi.single j 1 : Fin g → ℂ) i :=
  spEpsilon_spDiag i _

lemma mk_spDiag_eq_sum (d : Fin g → ℂ) :
    (⟨spDiag d, spDiag_mem_spCartan d⟩ : spCartan (g := g)) = ∑ i, d i • spDelta i := by
  have h₁ : d = ∑ i, d i • (Pi.single i 1 : Fin g → ℂ) := by
    funext j
    simp [Pi.single_apply]
  have h₂ : ((∑ i, d i • spDelta i : spCartan (g := g)) : Symplectic.sp (Fin g) ℂ) =
      ∑ i, ((d i • spDelta i : spCartan (g := g)) : Symplectic.sp (Fin g) ℂ) :=
    map_sum (spCartan (g := g)).toSubmodule.subtype _ _
  have h₃ : spDiag d = ∑ i, ((d i • spDelta i : spCartan (g := g)) : Symplectic.sp (Fin g) ℂ) := by
    conv_lhs => rw [h₁, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ map_smul spDiag (d i) _
  exact Subtype.ext (h₃.trans h₂.symm)

lemma dual_ext {φ ψ : Dual ℂ (spCartan (g := g))} (h : ∀ i, φ (spDelta i) = ψ (spDelta i)) :
    φ = ψ := by
  refine LinearMap.ext ?_
  rintro ⟨_, d, rfl⟩
  rw [mk_spDiag_eq_sum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, map_smul, h]

lemma spEps_inl (i : Fin g) : spEps (.inl i) = spEpsilon i :=
  rfl

lemma spEps_inr (i : Fin g) : spEps (.inr i) = -spEpsilon i :=
  rfl

/-- The root `ε_a - ε_b`, for `a ≠ b`, as an index of the root system. -/
noncomputable def spRootIdx (a b : Fin g ⊕ Fin g) (hab : a ≠ b) : (spCartan (g := g)).root :=
  ⟨spWeight a b hab, by simpa using isNonZero_spWeight a b hab⟩

lemma root_spRootIdx (a b : Fin g ⊕ Fin g) (hab : a ≠ b) :
    (IsKilling.rootSystem (spCartan (g := g))).root (spRootIdx a b hab) = spRootForm a b :=
  LinearMap.ext fun _ ↦ rfl

/-- The second index of the `k`-th simple root: `inl (k + 1)` for `k + 1 < g`, and `inr k` for
`k + 1 = g`. -/
def spSimpleSnd (k : Fin g) : Fin g ⊕ Fin g :=
  if h : (k : ℕ) + 1 < g then .inl ⟨k + 1, h⟩ else .inr k

lemma inl_ne_spSimpleSnd (k : Fin g) : Sum.inl k ≠ spSimpleSnd k := by
  by_cases h : (k : ℕ) + 1 < g
  · rw [spSimpleSnd, dite_eq_left_of_eq_true (eq_true h)]
    simp [Fin.ext_iff]
  · rw [spSimpleSnd, dite_eq_right_of_eq_false (eq_false h)]
    simp

/-- The `k`-th simple root: `ε_k - ε_{k + 1}` for `k + 1 < g`, and `2 ε_k` for `k + 1 = g`. -/
noncomputable def spSimpleIdx (k : Fin g) : (spCartan (g := g)).root :=
  spRootIdx (.inl k) (spSimpleSnd k) (inl_ne_spSimpleSnd k)

lemma root_spSimpleIdx_of_lt (k : Fin g) (h : (k : ℕ) + 1 < g) :
    (IsKilling.rootSystem (spCartan (g := g))).root (spSimpleIdx k) =
      spEpsilon k - spEpsilon ⟨k + 1, h⟩ := by
  rw [spSimpleIdx, root_spRootIdx, spRootForm, spEps_inl, spSimpleSnd,
    dite_eq_left_of_eq_true (eq_true h), spEps_inl]

lemma root_spSimpleIdx_of_not_lt (k : Fin g) (h : ¬(k : ℕ) + 1 < g) :
    (IsKilling.rootSystem (spCartan (g := g))).root (spSimpleIdx k) =
      spEpsilon k + spEpsilon k := by
  rw [spSimpleIdx, root_spRootIdx, spRootForm, spEps_inl, spSimpleSnd,
    dite_eq_right_of_eq_false (eq_false h), spEps_inr, sub_neg_eq_add]

/-- A coweight dual to the simple roots: `δ₀ + ⋯ + δ_m`, and half of the sum of all the `δᵢ` when
`m` is the last index. -/
noncomputable def spDualWeight (m : Fin g) : Fin g → ℂ :=
  if (m : ℕ) + 1 < g then fun i ↦ if i ≤ m then 1 else 0 else fun _ ↦ 2⁻¹

lemma root_spSimpleIdx_spDualWeight (k m : Fin g) :
    (IsKilling.rootSystem (spCartan (g := g))).root (spSimpleIdx k)
      ⟨spDiag (spDualWeight m), spDiag_mem_spCartan _⟩ = if k = m then 1 else 0 := by
  by_cases hk : (k : ℕ) + 1 < g
  · rw [root_spSimpleIdx_of_lt k hk, LinearMap.sub_apply, spEpsilon_spDiag, spEpsilon_spDiag]
    by_cases hm : (m : ℕ) + 1 < g
    · simp only [spDualWeight, hm, ite_true, Fin.le_def]
      by_cases h : k = m
      · subst h
        simp
      · have h' : (k : ℕ) ≠ m := fun h₁ ↦ h (Fin.ext h₁)
        by_cases h₂ : (k : ℕ) ≤ m
        · rw [ite_eq_left h₂, ite_eq_left (by omega), ite_eq_right h, sub_self]
        · rw [ite_eq_right h₂, ite_eq_right (by omega), ite_eq_right h, sub_self]
    · have h : k ≠ m := fun h₁ ↦ hm (h₁ ▸ hk)
      simp only [spDualWeight, hm, ite_false, sub_self, ite_eq_right h]
  · rw [root_spSimpleIdx_of_not_lt k hk, LinearMap.add_apply, spEpsilon_spDiag]
    have hk' : (k : ℕ) + 1 = g := by
      have h₁ : (k : ℕ) < g := k.2
      omega
    by_cases hm : (m : ℕ) + 1 < g
    · have h : k ≠ m := fun h₁ ↦ hk (h₁ ▸ hm)
      have h₂ : ¬k ≤ m := by
        rw [Fin.le_def]
        omega
      simp only [spDualWeight, hm, ite_true, ite_eq_right h₂, add_zero, ite_eq_right h]
    · have h : k = m := Fin.ext (by have h₁ : (m : ℕ) < g := m.2; omega)
      simp only [spDualWeight, hm, ite_eq_left h]
      norm_num

lemma linearIndependent_root_spSimpleIdx : LinearIndependent ℂ
    fun k : Fin g ↦ (IsKilling.rootSystem (spCartan (g := g))).root (spSimpleIdx k) := by
  classical
  refine Fintype.linearIndependent_iff.mpr fun c hc m ↦ ?_
  have h₁ : (∑ i, c i • (IsKilling.rootSystem (spCartan (g := g))).root (spSimpleIdx i))
      ⟨spDiag (spDualWeight m), spDiag_mem_spCartan _⟩ =
        (0 : Dual ℂ (spCartan (g := g))) ⟨spDiag (spDualWeight m), spDiag_mem_spCartan _⟩ :=
    congrArg (fun φ : Dual ℂ (spCartan (g := g)) ↦
      φ ⟨spDiag (spDualWeight m), spDiag_mem_spCartan _⟩) hc
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, root_spSimpleIdx_spDualWeight, smul_eq_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq'] at h₁
  simpa using h₁

lemma injective_spSimpleIdx : Function.Injective (spSimpleIdx (g := g)) := fun _ _ h ↦
  linearIndependent_root_spSimpleIdx.injective (congrArg _ h)

lemma linearIndepOn_root_spSimpleIdx : LinearIndepOn ℂ
    (IsKilling.rootSystem (spCartan (g := g))).root (Set.range (spSimpleIdx (g := g))) :=
  (linearIndepOn_range_iff injective_spSimpleIdx _).mpr linearIndependent_root_spSimpleIdx

variable (g) in
/-- The additive monoid generated by the simple roots. -/
noncomputable abbrev spCone : AddSubmonoid (Dual ℂ (spCartan (g := g))) :=
  AddSubmonoid.closure ((IsKilling.rootSystem (spCartan (g := g))).root ''
    Set.range (spSimpleIdx (g := g)))

lemma root_spSimpleIdx_mem (k : Fin g) :
    (IsKilling.rootSystem (spCartan (g := g))).root (spSimpleIdx k) ∈ spCone g :=
  AddSubmonoid.subset_closure ⟨_, ⟨k, rfl⟩, rfl⟩

lemma spEpsilon_sub_mem_of_le (i : Fin g) (n : ℕ) (hn : (i : ℕ) + n < g) :
    spEpsilon i - spEpsilon ⟨i + n, hn⟩ ∈ spCone g := by
  induction n with
  | zero =>
    have h : (⟨i + 0, hn⟩ : Fin g) = i := Fin.ext rfl
    rw [h, sub_self]
    exact zero_mem _
  | succ n ih =>
    have h₁ : (i : ℕ) + n < g := by
      omega
    have h₂ : (i : ℕ) + n + 1 < g := hn
    have h₃ : spEpsilon i - spEpsilon ⟨i + n, h₁⟩ +
        (IsKilling.rootSystem (spCartan (g := g))).root (spSimpleIdx ⟨i + n, h₁⟩) ∈ spCone g :=
      add_mem (ih h₁) (root_spSimpleIdx_mem ⟨i + n, h₁⟩)
    rw [root_spSimpleIdx_of_lt ⟨i + n, h₁⟩ h₂] at h₃
    have h₄ : spEpsilon i - spEpsilon ⟨i + n, h₁⟩ +
        (spEpsilon ⟨i + n, h₁⟩ - spEpsilon ⟨i + n + 1, h₂⟩) =
          spEpsilon i - spEpsilon ⟨i + (n + 1), hn⟩ := by
      abel
    rwa [h₄] at h₃

lemma spEpsilon_sub_mem {i j : Fin g} (hij : i ≤ j) : spEpsilon i - spEpsilon j ∈ spCone g := by
  have h₁ : (j : ℕ) = i + (j - i) := by
    have h₂ : (i : ℕ) ≤ j := hij
    omega
  have h₃ : (i : ℕ) + (j - i) < g := h₁ ▸ j.2
  have h₄ : spEpsilon i - spEpsilon ⟨i + (j - i), h₃⟩ ∈ spCone g :=
    spEpsilon_sub_mem_of_le i ((j : ℕ) - i) h₃
  have h₅ : (⟨i + (j - i), h₃⟩ : Fin g) = j := Fin.ext h₁.symm
  rwa [h₅] at h₄

lemma spEpsilon_add_mem (i j : Fin g) : spEpsilon i + spEpsilon j ∈ spCone g := by
  have hg : 0 < g := Fin.pos i
  let l : Fin g := ⟨g - 1, by omega⟩
  have hl : ¬(l : ℕ) + 1 < g := by
    simp only [l]
    omega
  have hle (m : Fin g) : m ≤ l := by
    rw [Fin.le_def]
    have h₁ : (m : ℕ) < g := m.2
    simp only [l]
    omega
  have h₁ : spEpsilon i - spEpsilon l + (spEpsilon j - spEpsilon l) +
      (IsKilling.rootSystem (spCartan (g := g))).root (spSimpleIdx l) ∈ spCone g :=
    add_mem (add_mem (spEpsilon_sub_mem (hle i)) (spEpsilon_sub_mem (hle j)))
      (root_spSimpleIdx_mem l)
  rw [root_spSimpleIdx_of_not_lt l hl] at h₁
  have h₂ : spEpsilon i - spEpsilon l + (spEpsilon j - spEpsilon l) + (spEpsilon l + spEpsilon l) =
      spEpsilon i + spEpsilon j := by
    abel
  rwa [h₂] at h₁

lemma spRootForm_mem_or_neg_mem (a b : Fin g ⊕ Fin g) :
    spRootForm a b ∈ spCone g ∨ -spRootForm a b ∈ spCone g := by
  rcases a with i | i <;> rcases b with j | j
  · rcases le_total i j with h | h
    · exact Or.inl (spEpsilon_sub_mem h)
    · refine Or.inr ?_
      rw [neg_spRootForm]
      exact spEpsilon_sub_mem h
  · refine Or.inl ?_
    rw [spRootForm, spEps_inl, spEps_inr, sub_neg_eq_add]
    exact spEpsilon_add_mem i j
  · refine Or.inr ?_
    rw [neg_spRootForm, spRootForm, spEps_inl, spEps_inr, sub_neg_eq_add]
    exact spEpsilon_add_mem j i
  · rcases le_total i j with h | h
    · refine Or.inr ?_
      rw [neg_spRootForm, spRootForm, spEps_inr, spEps_inr, sub_neg_eq_add, add_comm,
        ← sub_eq_add_neg]
      exact spEpsilon_sub_mem h
    · refine Or.inl ?_
      rw [spRootForm, spEps_inr, spEps_inr, sub_neg_eq_add, add_comm, ← sub_eq_add_neg]
      exact spEpsilon_sub_mem h

/-- The **base** of the root system of `𝔰𝔭(2g, ℂ)`: the roots `εᵢ - εᵢ₊₁` and `2 ε_g`. -/
noncomputable def spBase : (IsKilling.rootSystem (spCartan (g := g))).Base :=
  Base.mk' _ (Set.range (spSimpleIdx (g := g))) linearIndepOn_root_spSimpleIdx <| by
    rintro ⟨α, hα⟩
    rcases exists_eq_spRootForm α (by simpa using hα) with ⟨a, b, -, h⟩
    have h₁ : (IsKilling.rootSystem (spCartan (g := g))).root ⟨α, hα⟩ = spRootForm a b :=
      LinearMap.ext fun x ↦ congrFun h x
    rw [h₁]
    exact spRootForm_mem_or_neg_mem a b

lemma mem_spBase_support {i : (spCartan (g := g)).root} :
    i ∈ (spBase (g := g)).support ↔ ∃ k, spSimpleIdx k = i := by
  simp [spBase, Base.mk']

end SatoTateGroup
