import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.HeckeSpace

/-!
# The Hecke operators `T_𝔫` on Hilbert modular forms

Let `F` be a number field, `𝔑` a nonzero ideal of `𝒪_F` and `(𝔟_c)` representatives of the narrow
class group. A Hilbert modular form (LMFDB `mf.hilbert`) is a tuple `(f_c)` with `f_c` invariant
under `Γ₀(𝔑)_{𝔟_c}` in weight `k`. For a nonzero ideal `𝔫` of `𝒪_F` and narrow classes `c` and
`c' = c [𝔫]⁻¹`, the matrices `α` with totally positive determinant, `α(𝒪_F ⊕ 𝔟_c) ⊆ 𝒪_F ⊕ 𝔟_{c'}`,
`α(𝒪_F ⊕ 𝔑𝔟_c) ⊆ 𝒪_F ⊕ 𝔑𝔟_{c'}` and `(det α) 𝔟_c = 𝔫 𝔟_{c'}` form a set `Δ` stable under
`Γ₀(𝔑)_{𝔟_{c'}}` on the left and `Γ₀(𝔑)_{𝔟_c}` on the right, and the Hecke operator is
`(T_𝔫 f)_c = ∑ f_{c'} ∣ₖ α` over `α ∈ Γ₀(𝔑)_{𝔟_{c'}} \ Δ` (Shimura). It permutes the components.

The coset space `Γ₀(𝔑)_{𝔟_{c'}} \ Δ` is finite: `α ↦ (α⁻¹ L, α⁻¹ L')`, `L = 𝒪_F ⊕ 𝔟_{c'}`,
`L' = 𝒪_F ⊕ 𝔑𝔟_{c'}`, is injective on it, and by Cramer's rule `e n α⁻¹ L ⊆ 𝒪_F ⊕ 𝔟_c` for fixed
`0 ≠ e ∈ 𝔫` and `0 ≠ n ∈ 𝔑`, so that these lattices lie in a finite set of lattices. The two groups
differ, so the finite quotient is used directly rather than a Hecke pair. Since `Δ` contains
`diag(1, δ)` for a totally positive generator `δ` of `𝔫 𝔟_{c'} 𝔟_c⁻¹`, the sums are not empty.

For a prime `𝔭 ∤ 𝔑` this is the Hecke operator `T_𝔭`, and for `𝔫` coprime to `𝔑` Shimura's
`T(𝔫)`, as a sum over all matrices of determinant `𝔫`. When `𝔭 = (π)` with `π` totally positive,
the double coset `Γ₀(𝔑)_𝔟 diag(1, π) Γ₀(𝔑)_𝔟` of `HilbertModularGroup.heckeT` lies in `Δ`; that
it is all of `Δ` (an elementary divisor theorem for `𝒪_F ⊕ 𝔟`) is not proved, so the agreement with
`heckeTSpace` is not formalised. The operator is not normalised: the LMFDB's `T_𝔫` differs by a
power of `N(𝔫)` and by a rescaling of the components, which changes eigenforms by that rescaling
and eigenvalues by that power.

## Main definitions

* `HilbertModularGroup.heckeSet`: the matrices `Δ` of `T_𝔫` between two components.
* `HilbertModularGroup.gammaZeroRightCosets`: the right cosets of `Γ₀(𝔑)_𝔟`.
* `HilbertModularGroup.heckeCosets`: the right cosets `Γ₀(𝔑)_{𝔟_{c'}} \ Δ`.
* `HilbertModularForm.heckeIdealOperator`: `T_𝔫` from one component to another.
* `HilbertModularForm.heckeIdealSpace`: `T_𝔫` on the space of Hilbert modular forms.
* `HilbertModularForm.heckeIdealForm`: the Hilbert modular form `T_𝔫 f`.
* `HilbertModularForm.HasHeckeIdealEigenvalue`, `HilbertModularForm.IsHeckeIdealEigenform`:
  eigenvectors of `T_𝔫` and Hecke eigenforms for the `T_𝔫` with `𝔫` coprime to the level.
* `HilbertModularForm.heckeIdealEigenvalue` (LMFDB `mf.hilbert.eigenvalue`): the eigenvalue `a_𝔫`.
* `HilbertModularForm.heckeIdealOrbit` (LMFDB `mf.hilbert.hecke_orbit`): the Hecke orbit.

## Main results

* `HilbertModularGroup.finite_heckeCosets`: `Γ₀(𝔑)_{𝔟_{c'}} \ Δ` is finite.
* `HilbertModularGroup.doubleCoset_subset_heckeSet`: `Δ` is a union of double cosets.
* `HilbertModularGroup.doubleCoset_heckeDiagonal_subset_heckeSet`: the narrow-principal `T_𝔭`
  double coset lies in `Δ`.
* `HilbertModularForm.heckeCosets_nonempty`: the sums defining `T_𝔫` are not empty.
* `HilbertModularForm.IsCuspForm.heckeIdealForm`: `T_𝔫` maps cusp forms to cusp forms.
* `HilbertModularForm.HasHeckeIdealEigenvalue.eq`: the eigenvalue of a nonzero form is unique.
* `HilbertModularForm.heckeIdealOrbit_eq_span`: the Hecke orbit of an eigenform is `ℂ f`.
-/

open Matrix hiding mul_inv_rev

open NumberField InfinitePlace UpperHalfPlane HilbertModularGroup DoubleCoset

open scoped nonZeroDivisors Pointwise

namespace HilbertModularGroup

variable {F : Type*} [Field F] {𝔑 𝔫 : Ideal (𝓞 F)} {𝔟 𝔠 : FractionalIdeal (𝓞 F)⁰ F}
  {A : Matrix (Fin 2) (Fin 2) F} {y : F}

lemma algebraMap_mul_mem {r : 𝓞 F} {t : F} (ht : t ∈ 𝔠) : algebraMap (𝓞 F) F r * t ∈ 𝔠 := by
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem (𝔠 : Submodule (𝓞 F) F) r ht

lemma mul_mem_one {x x' : F} (hx : x ∈ (1 : Submodule (𝓞 F) F))
    (hx' : x' ∈ (1 : Submodule (𝓞 F) F)) : x * x' ∈ (1 : Submodule (𝓞 F) F) := by
  rcases Submodule.mem_one.mp hx with ⟨r, rfl⟩
  rcases Submodule.mem_one.mp hx' with ⟨r', rfl⟩
  exact Submodule.mem_one.mpr ⟨r * r', map_mul _ r r'⟩

lemma apply_zero_zero_mem (hA : ∀ v ∈ lattice 𝔟, A *ᵥ v ∈ lattice 𝔠) :
    A 0 0 ∈ (1 : Submodule (𝓞 F) F) := by
  simpa [mulVec, dotProduct] using ((mem_lattice 𝔠).mp (hA ![1, 0] ((mem_lattice 𝔟).mpr
    ⟨Submodule.mem_one.mpr ⟨1, map_one _⟩, (𝔟 : Submodule (𝓞 F) F).zero_mem⟩))).1

lemma apply_one_zero_mem (hA : ∀ v ∈ lattice 𝔟, A *ᵥ v ∈ lattice 𝔠) : A 1 0 ∈ 𝔠 := by
  simpa [mulVec, dotProduct] using ((mem_lattice 𝔠).mp (hA ![1, 0] ((mem_lattice 𝔟).mpr
    ⟨Submodule.mem_one.mpr ⟨1, map_one _⟩, (𝔟 : Submodule (𝓞 F) F).zero_mem⟩))).2

lemma apply_zero_one_mul_mem (hA : ∀ v ∈ lattice 𝔟, A *ᵥ v ∈ lattice 𝔠) (hy : y ∈ 𝔟) :
    A 0 1 * y ∈ (1 : Submodule (𝓞 F) F) := by
  simpa [mulVec, dotProduct] using
    ((mem_lattice 𝔠).mp (hA ![0, y] ((mem_lattice 𝔟).mpr ⟨by simp, hy⟩))).1

lemma apply_one_one_mul_mem (hA : ∀ v ∈ lattice 𝔟, A *ᵥ v ∈ lattice 𝔠) (hy : y ∈ 𝔟) :
    A 1 1 * y ∈ 𝔠 := by
  simpa [mulVec, dotProduct] using
    ((mem_lattice 𝔠).mp (hA ![0, y] ((mem_lattice 𝔟).mpr ⟨by simp, hy⟩))).2

attribute [local instance] mulVecDistribMulAction

local instance : SMulCommClass (GL (Fin 2) F) (𝓞 F) (Fin 2 → F) where
  smul_comm g r v := smul_comm g.val r v

lemma le_inv_smul {α : GL (Fin 2) F} {M N : Submodule (𝓞 F) (Fin 2 → F)}
    (h : ∀ v ∈ M, α.val *ᵥ v ∈ N) : M ≤ α⁻¹ • N :=
  fun v hv ↦ (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨α • v, h v hv, inv_smul_smul α v⟩

lemma gammaZeroLattice_le_lattice : gammaZeroLattice 𝔟 𝔑 ≤ lattice 𝔟 :=
  fun _ hv ↦ (mem_lattice 𝔟).mpr ⟨((mem_gammaZeroLattice 𝔟 𝔑).mp hv).1,
    Submodule.smul_le_right ((mem_gammaZeroLattice 𝔟 𝔑).mp hv).2⟩

lemma smul_lattice_le_gammaZeroLattice {n : 𝓞 F} (hn : n ∈ 𝔑) :
    n • lattice 𝔟 ≤ gammaZeroLattice 𝔟 𝔑 := by
  rintro - ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, mem_lattice] at hv
  exact (mem_gammaZeroLattice 𝔟 𝔑).mpr ⟨Submodule.smul_mem _ n hv.1,
    Submodule.smul_mem_smul hn hv.2⟩

lemma inv_smul_lattice_mul {γ α : GL (Fin 2) F} (hγ : γ ∈ gammaZero 𝔠 (glPlus 𝔠) 𝔑) :
    (γ * α)⁻¹ • lattice 𝔠 = α⁻¹ • lattice 𝔠 := by
  rw [mul_inv_rev, mul_smul α⁻¹ γ⁻¹ (lattice 𝔠),
    MulAction.mem_stabilizer_iff.mp ((gl_eq_stabilizer 𝔠).le (inv_mem hγ).1.1)]

lemma inv_smul_gammaZeroLattice_mul {γ α : GL (Fin 2) F} (hγ : γ ∈ gammaZero 𝔠 (glPlus 𝔠) 𝔑) :
    (γ * α)⁻¹ • gammaZeroLattice 𝔠 𝔑 = α⁻¹ • gammaZeroLattice 𝔠 𝔑 := by
  rw [gammaZero_eq] at hγ
  rw [mul_inv_rev, mul_smul α⁻¹ γ⁻¹ (gammaZeroLattice 𝔠 𝔑),
    MulAction.mem_stabilizer_iff.mp (inv_mem hγ).2]

lemma mul_inv_mem_gammaZero {α β : GL (Fin 2) F} (hα : IsTotallyPositive α.det.val)
    (hβ : IsTotallyPositive β.det.val) (h : α⁻¹ • lattice 𝔠 = β⁻¹ • lattice 𝔠)
    (h' : α⁻¹ • gammaZeroLattice 𝔠 𝔑 = β⁻¹ • gammaZeroLattice 𝔠 𝔑) :
    β * α⁻¹ ∈ gammaZero 𝔠 (glPlus 𝔠) 𝔑 := by
  rw [gammaZero_eq]
  refine ⟨⟨(gl_eq_stabilizer 𝔠).ge ?_, ?_⟩, ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul β α⁻¹ (lattice 𝔠), h,
      ← mul_smul β β⁻¹ (lattice 𝔠), mul_inv_cancel, one_smul (GL (Fin 2) F) (lattice 𝔠)]
  · refine Subgroup.mem_comap.mpr ?_
    rw [map_mul, map_inv]
    exact mul_mem (mem_totallyPositiveUnits.mpr hβ) (inv_mem (mem_totallyPositiveUnits.mpr hα))
  · refine MulAction.mem_stabilizer_iff.mpr ?_
    rw [mul_smul β α⁻¹ (gammaZeroLattice 𝔠 𝔑), h',
      ← mul_smul β β⁻¹ (gammaZeroLattice 𝔠 𝔑), mul_inv_cancel,
      one_smul (GL (Fin 2) F) (gammaZeroLattice 𝔠 𝔑)]

variable (𝔑 𝔠) in
/-- The right cosets `Γ₀(𝔑)_𝔠 g`, `g ∈ GL₂(F)`. -/
abbrev gammaZeroRightCosets : Type _ :=
  Quotient (QuotientGroup.rightRel (gammaZero 𝔠 (glPlus 𝔠) 𝔑))

lemma out_mul_inv_mem (α : GL (Fin 2) F) :
    (⟦α⟧ : gammaZeroRightCosets 𝔑 𝔠).out * α⁻¹ ∈ gammaZero 𝔠 (glPlus 𝔠) 𝔑 := by
  rw [← inv_inv ((⟦α⟧ : gammaZeroRightCosets 𝔑 𝔠).out * α⁻¹), mul_inv_rev, inv_inv]
  exact inv_mem <| QuotientGroup.rightRel_apply.mp <| Quotient.exact <| Quotient.out_eq _

lemma mk_out_mul (α γ : GL (Fin 2) F) :
    (⟦(⟦α⟧ : gammaZeroRightCosets 𝔑 𝔠).out * γ⟧ : gammaZeroRightCosets 𝔑 𝔠) = ⟦α * γ⟧ := by
  refine Quotient.sound <| QuotientGroup.rightRel_apply.mpr ?_
  convert inv_mem (out_mul_inv_mem (𝔑 := 𝔑) (𝔠 := 𝔠) α) using 1
  group

lemma mk_out_mul_mul_inv (q : gammaZeroRightCosets 𝔑 𝔠) (γ : GL (Fin 2) F) :
    (⟦(⟦q.out * γ⟧ : gammaZeroRightCosets 𝔑 𝔠).out * γ⁻¹⟧ : gammaZeroRightCosets 𝔑 𝔠) = q := by
  rw [mk_out_mul, mul_inv_cancel_right, Quotient.out_eq]

variable [NumberField F]

variable (𝔑 𝔫 𝔟 𝔠) in
/-- The set of matrices of the **Hecke operator `T_𝔫`** from the component of `𝔠` to the component
of `𝔟`: the `α ∈ GL₂(F)` with totally positive determinant mapping `𝒪_F ⊕ 𝔟` into `𝒪_F ⊕ 𝔠` and
`𝒪_F ⊕ 𝔑𝔟` into `𝒪_F ⊕ 𝔑𝔠`, with `(det α) 𝔟 = 𝔫 𝔠`. Equivalently, `α = (a, b; c, d)` with
`a ∈ 𝒪_F`, `b ∈ 𝔟⁻¹`, `c ∈ 𝔑𝔠`, `d ∈ 𝔠𝔟⁻¹` and `(det α) = 𝔫𝔠𝔟⁻¹`. It is nonempty exactly when
`[𝔟] = [𝔫][𝔠]` in the narrow class group. -/
def heckeSet : Set (GL (Fin 2) F) :=
  {α | IsTotallyPositive α.det.val ∧ (∀ v ∈ lattice 𝔟, α.val *ᵥ v ∈ lattice 𝔠) ∧
    (∀ v ∈ gammaZeroLattice 𝔟 𝔑, α.val *ᵥ v ∈ gammaZeroLattice 𝔠 𝔑) ∧
    FractionalIdeal.spanSingleton (𝓞 F)⁰ α.det.val * 𝔟 = 𝔫 * 𝔠}

lemma mem_of_mul_mem {D x : F} (hD : D ≠ 0)
    (hdet : FractionalIdeal.spanSingleton (𝓞 F)⁰ D * 𝔟 = 𝔫 * 𝔠)
    (hx : D * x ∈ (𝔫 * 𝔠 : FractionalIdeal (𝓞 F)⁰ F)) : x ∈ 𝔟 := by
  rw [← hdet, FractionalIdeal.mem_singleton_mul] at hx
  rcases hx with ⟨y, hy, hxy⟩
  rwa [mul_left_cancel₀ hD hxy]

lemma mem_one_of_forall_mul_mem (h𝔟 : 𝔟 ≠ 0) {x : F} (hx : ∀ y ∈ 𝔟, x * y ∈ 𝔟) :
    x ∈ (1 : Submodule (𝓞 F) F) := by
  have h : FractionalIdeal.spanSingleton (𝓞 F)⁰ x * 𝔟 ≤ 1 * 𝔟 := by
    rw [one_mul, ← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul,
      FractionalIdeal.coe_spanSingleton, Submodule.span_singleton_mul]
    rintro - ⟨y, hy, rfl⟩
    exact hx y hy
  have h' : FractionalIdeal.spanSingleton (𝓞 F)⁰ x * 𝔟 * 𝔟⁻¹ ≤ 1 * 𝔟 * 𝔟⁻¹ :=
    mul_le_mul' h le_rfl
  rw [mul_assoc, mul_assoc, mul_inv_cancel₀ h𝔟, mul_one, mul_one] at h'
  exact Submodule.mem_one.mpr <|
    (FractionalIdeal.mem_one_iff _).mp (h' (FractionalIdeal.mem_spanSingleton_self _ x))

lemma det_mem_one (h𝔟 : 𝔟 ≠ 0) (hA : ∀ v ∈ lattice 𝔟, A *ᵥ v ∈ lattice 𝔟) :
    A.det ∈ (1 : Submodule (𝓞 F) F) := by
  rw [det_fin_two]
  exact Submodule.sub_mem _ (mul_mem_one (apply_zero_zero_mem hA) <|
    mem_one_of_forall_mul_mem h𝔟 fun _ ↦ apply_one_one_mul_mem hA)
    (apply_zero_one_mul_mem hA (apply_one_zero_mem hA))

lemma spanSingleton_det_eq_one (h𝔟 : 𝔟 ≠ 0) {γ : GL (Fin 2) F} (hγ : γ ∈ gl 𝔟) :
    FractionalIdeal.spanSingleton (𝓞 F)⁰ γ.det.val = 1 := by
  have h (g : GL (Fin 2) F) (hg : g ∈ gl 𝔟) :
      FractionalIdeal.spanSingleton (𝓞 F)⁰ g.det.val ≤ 1 := by
    rw [FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_one_iff,
      ← Submodule.mem_one, GeneralLinearGroup.val_det_apply]
    exact det_mem_one h𝔟 fun v ↦ (hg v).mp
  refine le_antisymm (h γ hγ) ?_
  have hmul : FractionalIdeal.spanSingleton (𝓞 F)⁰ γ.det.val *
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ⁻¹).det.val = 1 := by
    rw [← map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, map_one]
  rw [← hmul]
  exact mul_le_of_le_one_right' (h γ⁻¹ (inv_mem hγ))

lemma smul_mulVec_inv_mem_lattice (h𝔟 : 𝔟 ≠ 0) {α : GL (Fin 2) F} (hα : α ∈ heckeSet 𝔑 𝔫 𝔟 𝔠)
    {e : 𝓞 F} (he : e ∈ 𝔫) {w : Fin 2 → F} (hw : w ∈ lattice 𝔠) :
    e • ((α⁻¹).val *ᵥ w) ∈ lattice 𝔟 := by
  rcases hα with ⟨-, hL, -, hdet⟩
  have hv : α.val *ᵥ ((α⁻¹).val *ᵥ w) = w := by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  generalize (α⁻¹).val *ᵥ w = v at hv ⊢
  have h₀ : α.val 0 0 * v 0 + α.val 0 1 * v 1 = w 0 := by
    simpa [mulVec] using congrFun hv 0
  have h₁ : α.val 1 0 * v 0 + α.val 1 1 * v 1 = w 1 := by
    simpa [mulVec] using congrFun hv 1
  have hD : α.det.val = α.val 0 0 * α.val 1 1 - α.val 0 1 * α.val 1 0 := by
    rw [GeneralLinearGroup.val_det_apply, det_fin_two]
  have he' : algebraMap (𝓞 F) F e ∈ (𝔫 : FractionalIdeal (𝓞 F)⁰ F) :=
    (FractionalIdeal.mem_coeIdeal _).mpr ⟨e, he, rfl⟩
  rw [mem_lattice] at hw ⊢
  rcases Submodule.mem_one.mp hw.1 with ⟨w₀, hw₀⟩
  rcases Submodule.mem_one.mp (apply_zero_zero_mem hL) with ⟨a, ha⟩
  simp only [Pi.smul_apply, Algebra.smul_def]
  refine ⟨mem_one_of_forall_mul_mem h𝔟 fun y hy ↦ mem_of_mul_mem α.det.ne_zero hdet ?_,
    mem_of_mul_mem α.det.ne_zero hdet ?_⟩
  · rcases Submodule.mem_one.mp (apply_zero_one_mul_mem hL hy) with ⟨b, hb⟩
    have h : α.det.val * (algebraMap (𝓞 F) F e * v 0 * y) =
        algebraMap (𝓞 F) F e * (w 0 * (α.val 1 1 * y) - α.val 0 1 * y * w 1) := by
      rw [hD]
      linear_combination (algebraMap (𝓞 F) F e * y) * (α.val 1 1 * h₀ - α.val 0 1 * h₁)
    rw [h, ← hw₀, ← hb]
    exact FractionalIdeal.mul_mem_mul he' <| Submodule.sub_mem _
      (algebraMap_mul_mem (apply_one_one_mul_mem hL hy)) (algebraMap_mul_mem hw.2)
  · have h : α.det.val * (algebraMap (𝓞 F) F e * v 1) =
        algebraMap (𝓞 F) F e * (α.val 0 0 * w 1 - w 0 * α.val 1 0) := by
      rw [hD]
      linear_combination algebraMap (𝓞 F) F e * (α.val 0 0 * h₁ - α.val 1 0 * h₀)
    rw [h, ← hw₀, ← ha]
    exact FractionalIdeal.mul_mem_mul he' <| Submodule.sub_mem _ (algebraMap_mul_mem hw.2)
      (algebraMap_mul_mem (apply_one_zero_mem hL))

lemma mul_mem_heckeSet (h𝔟 : 𝔟 ≠ 0) {α γ : GL (Fin 2) F} (hα : α ∈ heckeSet 𝔑 𝔫 𝔟 𝔠)
    (hγ : γ ∈ gammaZero 𝔟 (glPlus 𝔟) 𝔑) : α * γ ∈ heckeSet 𝔑 𝔫 𝔟 𝔠 := by
  rcases hα with ⟨hpos, hL, hL', hdet⟩
  refine ⟨?_, fun v hv ↦ ?_, fun v hv ↦ ?_, ?_⟩
  · rw [map_mul]
    exact mem_totallyPositiveUnits.mp (mul_mem (mem_totallyPositiveUnits.mpr hpos) hγ.1.2)
  · rw [Units.val_mul, ← mulVec_mulVec]
    exact hL _ ((hγ.1.1 v).mp hv)
  · rw [Units.val_mul, ← mulVec_mulVec]
    exact hL' _ ((hγ.2 v).mp hv)
  · rw [map_mul, Units.val_mul, map_mul, mul_assoc, spanSingleton_det_eq_one h𝔟 hγ.1.1, one_mul,
      hdet]

lemma mul_mem_heckeSet_left (h𝔠 : 𝔠 ≠ 0) {α γ : GL (Fin 2) F} (hα : α ∈ heckeSet 𝔑 𝔫 𝔟 𝔠)
    (hγ : γ ∈ gammaZero 𝔠 (glPlus 𝔠) 𝔑) : γ * α ∈ heckeSet 𝔑 𝔫 𝔟 𝔠 := by
  rcases hα with ⟨hpos, hL, hL', hdet⟩
  refine ⟨?_, fun v hv ↦ ?_, fun v hv ↦ ?_, ?_⟩
  · rw [map_mul]
    exact mem_totallyPositiveUnits.mp (mul_mem hγ.1.2 (mem_totallyPositiveUnits.mpr hpos))
  · rw [Units.val_mul, ← mulVec_mulVec]
    exact (hγ.1.1 _).mp (hL v hv)
  · rw [Units.val_mul, ← mulVec_mulVec]
    exact (hγ.2 _).mp (hL' v hv)
  · rw [map_mul, Units.val_mul, map_mul, spanSingleton_det_eq_one h𝔠 hγ.1.1, one_mul, hdet]

/-- **`heckeSet 𝔑 𝔫 𝔟 𝔠` is a union of double cosets** `Γ₀(𝔑)_𝔠 α Γ₀(𝔑)_𝔟`. -/
lemma doubleCoset_subset_heckeSet (h𝔟 : 𝔟 ≠ 0) (h𝔠 : 𝔠 ≠ 0) {α : GL (Fin 2) F}
    (hα : α ∈ heckeSet 𝔑 𝔫 𝔟 𝔠) :
    doubleCoset α (gammaZero 𝔠 (glPlus 𝔠) 𝔑) (gammaZero 𝔟 (glPlus 𝔟) 𝔑) ⊆ heckeSet 𝔑 𝔫 𝔟 𝔠 := by
  rintro - ⟨-, ⟨γ, hγ, y, hy, rfl⟩, γ', hγ', rfl⟩
  rw [Set.mem_singleton_iff.mp hy]
  exact mul_mem_heckeSet h𝔟 (mul_mem_heckeSet_left h𝔠 hα hγ) hγ'

lemma smul_inv_smul_lattice_le (h𝔟 : 𝔟 ≠ 0) {α : GL (Fin 2) F} (hα : α ∈ heckeSet 𝔑 𝔫 𝔟 𝔠)
    {e : 𝓞 F} (he : e ∈ 𝔫) : e • α⁻¹ • lattice 𝔠 ≤ lattice 𝔟 := by
  intro x hx
  rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx with ⟨u, hu, rfl⟩
  rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hu with ⟨w, hw, rfl⟩
  exact smul_mulVec_inv_mem_lattice h𝔟 hα he hw

variable (𝔑 𝔫 𝔟 𝔠) in
/-- The right cosets `Γ₀(𝔑)_𝔠 α` of the matrices `α` of `heckeSet 𝔑 𝔫 𝔟 𝔠`. -/
noncomputable def heckeCosets : Set (gammaZeroRightCosets 𝔑 𝔠) :=
  Quotient.mk _ '' heckeSet 𝔑 𝔫 𝔟 𝔠

/-- **The coset space `Γ₀(𝔑)_𝔠 \ heckeSet 𝔑 𝔫 𝔟 𝔠` is finite**: `Γ₀(𝔑)_𝔠 α` is determined by the
lattices `α⁻¹(𝒪_F ⊕ 𝔠)` and `α⁻¹(𝒪_F ⊕ 𝔑𝔠)`, which lie between `e n (𝒪_F ⊕ 𝔟)` and
`(e n)⁻¹ (𝒪_F ⊕ 𝔟)` for fixed nonzero `e ∈ 𝔫` and `n ∈ 𝔑`. -/
lemma finite_heckeCosets (h𝔟 : 𝔟 ≠ 0) (h𝔑 : 𝔑 ≠ ⊥) (h𝔫 : 𝔫 ≠ ⊥) :
    (heckeCosets 𝔑 𝔫 𝔟 𝔠).Finite := by
  rcases Submodule.exists_mem_ne_zero_of_ne_bot h𝔑 with ⟨n, hn, hn0⟩
  rcases Submodule.exists_mem_ne_zero_of_ne_bot h𝔫 with ⟨e, he, he0⟩
  have hB : {N | (n * e) • lattice 𝔟 ≤ N ∧ (n * e) • N ≤ lattice 𝔟}.Finite :=
    finite_setOf_isBand (isCommensurableLattice_lattice h𝔟) (mul_ne_zero hn0 he0)
  have hout (α : GL (Fin 2) F) : (⟦α⟧ : gammaZeroRightCosets 𝔑 𝔠).out =
      (⟦α⟧ : gammaZeroRightCosets 𝔑 𝔠).out * α⁻¹ * α :=
    (inv_mul_cancel_right _ _).symm
  refine Set.Finite.of_finite_image (f := fun q : gammaZeroRightCosets 𝔑 𝔠 ↦
    (q.out⁻¹ • lattice 𝔠, q.out⁻¹ • gammaZeroLattice 𝔠 𝔑)) ((hB.prod hB).subset ?_) ?_
  · rintro - ⟨-, ⟨α, hα, rfl⟩, rfl⟩
    beta_reduce
    rw [hout, inv_smul_lattice_mul (out_mul_inv_mem α),
      inv_smul_gammaZeroLattice_mul (out_mul_inv_mem α)]
    refine ⟨⟨(Submodule.smul_le_self_of_tower _ _).trans (le_inv_smul hα.2.1), ?_⟩, ?_, ?_⟩
    · rw [mul_smul]
      exact (smul_le_smul_left n (smul_inv_smul_lattice_le h𝔟 hα he)).trans
        (Submodule.smul_le_self_of_tower _ _)
    · rw [mul_comm, mul_smul]
      exact (smul_le_smul_left e (smul_lattice_le_gammaZeroLattice hn)).trans
        ((Submodule.smul_le_self_of_tower _ _).trans (le_inv_smul hα.2.2.1))
    · rw [mul_smul]
      exact (smul_le_smul_left n ((smul_le_smul_left e
        (Submodule.map_mono gammaZeroLattice_le_lattice)).trans
          (smul_inv_smul_lattice_le h𝔟 hα he))).trans (Submodule.smul_le_self_of_tower _ _)
  · rintro - ⟨α, hα, rfl⟩ - ⟨β, hβ, rfl⟩ h
    beta_reduce at h
    rw [Prod.mk.injEq, hout α, hout β, inv_smul_lattice_mul (out_mul_inv_mem α),
      inv_smul_gammaZeroLattice_mul (out_mul_inv_mem α), inv_smul_lattice_mul (out_mul_inv_mem β),
      inv_smul_gammaZeroLattice_mul (out_mul_inv_mem β)] at h
    exact Quotient.sound <| QuotientGroup.rightRel_apply.mpr <|
      mul_inv_mem_gammaZero hα.1 hβ.1 h.1 h.2

lemma isTotallyPositive_det_out {q : gammaZeroRightCosets 𝔑 𝔠} (hq : q ∈ heckeCosets 𝔑 𝔫 𝔟 𝔠) :
    IsTotallyPositive q.out.det.val := by
  rcases hq with ⟨α, hα, rfl⟩
  have h : (⟦α⟧ : gammaZeroRightCosets 𝔑 𝔠).out * α⁻¹ * α ∈
      totallyPositiveUnits.comap GeneralLinearGroup.det :=
    mul_mem (out_mul_inv_mem (𝔑 := 𝔑) (𝔠 := 𝔠) α).1.2
      (Subgroup.mem_comap.mpr (mem_totallyPositiveUnits.mpr hα.1))
  rw [inv_mul_cancel_right] at h
  exact mem_totallyPositiveUnits.mp (Subgroup.mem_comap.mp h)

lemma heckeDiagonal_mem_heckeSet {δ : Fˣ} (hδ : IsTotallyPositive (δ : F))
    (hdet : FractionalIdeal.spanSingleton (𝓞 F)⁰ (δ : F) * 𝔟 = 𝔫 * 𝔠) :
    (heckeDiagonal δ hδ : GL (Fin 2) F) ∈ heckeSet 𝔑 𝔫 𝔟 𝔠 := by
  have hδ' (y : F) (hy : y ∈ 𝔟) : δ * y ∈ 𝔠 := by
    have h : δ * y ∈ FractionalIdeal.spanSingleton (𝓞 F)⁰ (δ : F) * 𝔟 :=
      FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self (𝓞 F)⁰ (δ : F)) hy
    rw [hdet] at h
    exact mul_le_of_le_one_left' FractionalIdeal.coeIdeal_le_one h
  have hval (v : Fin 2 → F) : (heckeDiagonal δ hδ : GL (Fin 2) F).val *ᵥ v = ![v 0, δ * v 1] := by
    ext i
    fin_cases i <;> simp [heckeDiagonal, mulVec_diagonal]
  refine ⟨?_, fun v hv ↦ ?_, fun v hv ↦ ?_, ?_⟩
  · rwa [HilbertModularForm.det_heckeDiagonal]
  · rw [mem_lattice] at hv
    rw [hval, mem_lattice]
    exact ⟨hv.1, hδ' _ hv.2⟩
  · rw [mem_gammaZeroLattice] at hv
    rw [hval, mem_gammaZeroLattice]
    have h : (𝔑 • (𝔟 : Submodule (𝓞 F) F)).map (LinearMap.mulLeft (𝓞 F) (δ : F)) ≤
        𝔑 • (𝔠 : Submodule (𝓞 F) F) := by
      rw [Submodule.map_smul'']
      exact smul_mono_right _ (Submodule.map_le_iff_le_comap.mpr hδ')
    exact ⟨hv.1, h ⟨v 1, hv.2, rfl⟩⟩
  · rwa [HilbertModularForm.det_heckeDiagonal]

/-- **The double coset `T_𝔭 = Γ₀(𝔑)_𝔟 diag(1, π) Γ₀(𝔑)_𝔟` of a narrow-principal `𝔭 = (π)` lies in
`heckeSet 𝔑 𝔭 𝔟 𝔟`.** -/
lemma doubleCoset_heckeDiagonal_subset_heckeSet (h𝔟 : 𝔟 ≠ 0) {π : Fˣ}
    (hπ : IsTotallyPositive (π : F)) {p : 𝓞 F} (hp : algebraMap (𝓞 F) F p = π) :
    doubleCoset (heckeDiagonal π hπ : GL (Fin 2) F) (gammaZero 𝔟 (glPlus 𝔟) 𝔑)
      (gammaZero 𝔟 (glPlus 𝔟) 𝔑) ⊆ heckeSet 𝔑 (Ideal.span {p}) 𝔟 𝔟 :=
  doubleCoset_subset_heckeSet h𝔟 h𝔟 <| heckeDiagonal_mem_heckeSet hπ <| by
    rw [FractionalIdeal.coeIdeal_span_singleton, hp]

end HilbertModularGroup

namespace HilbertModularForm

variable {F : Type*} [Field F] [NumberField F] {k : {w : InfinitePlace F // w.IsReal} → ℤ}
  {𝔑 𝔫 : Ideal (𝓞 F)} {𝔟 𝔠 : FractionalIdeal (𝓞 F)⁰ F}

lemma slash_out_mk {φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ}
    (hφ : φ ∈ slashInvariants k (gammaZero 𝔠 (glPlus 𝔠) 𝔑)) {x : GL (Fin 2) F}
    (hx : IsTotallyPositive x.det.val) :
    slash k (⟦x⟧ : gammaZeroRightCosets 𝔑 𝔠).out φ = slash k x φ := by
  rw [← inv_mul_cancel_right (⟦x⟧ : gammaZeroRightCosets 𝔑 𝔠).out x, slash_mul k _ _ φ
    (isTotallyPositive_det_of_mem_gammaZero (out_mul_inv_mem x)) hx, hφ _ (out_mul_inv_mem x)]

variable [NeZero 𝔟] [NeZero 𝔑] [NeZero 𝔫]

variable (k 𝔑 𝔫 𝔟 𝔠) in
/-- The **Hecke operator `T_𝔫`** from the component of `𝔠` to the component of `𝔟`, on the
functions satisfying the transformation law of weight `k`: `φ ↦ ∑_α φ ∣ₖ α`, where `α` runs over
representatives of the finitely many right cosets `Γ₀(𝔑)_𝔠 α ⊆ heckeSet 𝔑 𝔫 𝔟 𝔠`
(`finite_heckeCosets`). The sum does not depend on the representatives, since `φ` is invariant
under `Γ₀(𝔑)_𝔠`, and it satisfies the transformation law for `Γ₀(𝔑)_𝔟`, since right
multiplication by `Γ₀(𝔑)_𝔟` permutes these cosets. -/
noncomputable def heckeIdealOperator : slashInvariants k (gammaZero 𝔠 (glPlus 𝔠) 𝔑) →ₗ[ℂ]
    slashInvariants k (gammaZero 𝔟 (glPlus 𝔟) 𝔑) where
  toFun φ := ⟨∑ q ∈ (finite_heckeCosets (NeZero.ne 𝔟) (NeZero.ne 𝔑) (NeZero.ne 𝔫)).toFinset,
    slashLinearMap k q.out φ, fun γ hγ ↦ by
    have hγ' : IsTotallyPositive γ.det.val :=
      isTotallyPositive_det_of_mem_gammaZero hγ
    rw [← slashLinearMap_apply, map_sum]
    refine (Finset.sum_congr rfl fun q hq ↦ ?_).trans <| Finset.sum_nbij'
      (f := fun q : gammaZeroRightCosets 𝔑 𝔠 ↦ slash k (q.out * γ) φ)
      (fun q ↦ ⟦q.out * γ⟧) (fun q ↦ ⟦q.out * γ⁻¹⟧) ?_ ?_ (fun q _ ↦ mk_out_mul_mul_inv q γ)
      (fun q _ ↦ by simpa using mk_out_mul_mul_inv q γ⁻¹) fun q hq ↦ ?_
    · exact (slash_mul k _ _ φ (isTotallyPositive_det_out (Set.Finite.mem_toFinset _ |>.mp hq))
        hγ').symm
    · rintro q hq
      rw [Set.Finite.mem_toFinset] at hq ⊢
      rcases hq with ⟨α, hα, rfl⟩
      rw [mk_out_mul]
      exact ⟨_, mul_mem_heckeSet (NeZero.ne 𝔟) hα hγ, rfl⟩
    · rintro q hq
      rw [Set.Finite.mem_toFinset] at hq ⊢
      rcases hq with ⟨α, hα, rfl⟩
      rw [mk_out_mul]
      exact ⟨_, mul_mem_heckeSet (NeZero.ne 𝔟) hα (inv_mem hγ), rfl⟩
    · rw [slashLinearMap_apply, slash_out_mk φ.2]
      rw [map_mul]
      exact mem_totallyPositiveUnits.mp (mul_mem (mem_totallyPositiveUnits.mpr
        (isTotallyPositive_det_out (Set.Finite.mem_toFinset _ |>.mp hq))) hγ.1.2)⟩
  map_add' φ₁ φ₂ := Subtype.ext <| by
    simp [Finset.sum_add_distrib]
  map_smul' c φ := Subtype.ext <| by
    simp [Finset.smul_sum]

lemma coe_heckeIdealOperator (φ : slashInvariants k (gammaZero 𝔠 (glPlus 𝔠) 𝔑)) :
    (heckeIdealOperator k 𝔑 𝔫 𝔟 𝔠 φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) =
      ∑ q ∈ (finite_heckeCosets (𝔠 := 𝔠) (NeZero.ne 𝔟) (NeZero.ne 𝔑) (NeZero.ne 𝔫)).toFinset,
        slash k q.out φ :=
  rfl

variable {φ : slashInvariants k (gammaZero 𝔠 (glPlus 𝔠) 𝔑)}

lemma IsHolomorphic.heckeIdeal
    (h : IsHolomorphic (φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ)) : IsHolomorphic
      (heckeIdealOperator k 𝔑 𝔫 𝔟 𝔠 φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) := by
  rw [coe_heckeIdealOperator]
  exact Finset.sum_induction _ IsHolomorphic (fun _ _ ↦ IsHolomorphic.add)
    (differentiableOn_const 0) fun _ hq ↦
      h.slash (isTotallyPositive_det_out ((Set.Finite.mem_toFinset _).mp hq))

lemma IsBoundedAtCusps.heckeIdeal
    (h : IsBoundedAtCusps k (φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ)) :
    IsBoundedAtCusps k
      (heckeIdealOperator k 𝔑 𝔫 𝔟 𝔠 φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) := by
  rw [coe_heckeIdealOperator]
  exact Finset.sum_induction _ (fun f ↦ IsBoundedAtCusps k f) (fun _ _ ↦ IsBoundedAtCusps.add)
    isBoundedAtCusps_zero fun _ hq ↦
      h.slash (isTotallyPositive_det_out ((Set.Finite.mem_toFinset _).mp hq))

lemma VanishesAtCusps.heckeIdeal
    (h : VanishesAtCusps k (φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ)) :
    VanishesAtCusps k
      (heckeIdealOperator k 𝔑 𝔫 𝔟 𝔠 φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) := by
  rw [coe_heckeIdealOperator]
  exact Finset.sum_induction _ (fun f ↦ VanishesAtCusps k f) (fun _ _ ↦ VanishesAtCusps.add)
    vanishesAtCusps_zero fun _ hq ↦
      h.slash (isTotallyPositive_det_out ((Set.Finite.mem_toFinset _).mp hq))

end HilbertModularForm

namespace HilbertModularForm

variable {F : Type*} [Field F] [NumberField F] {k : {w : InfinitePlace F // w.IsReal} → ℤ}
  {𝔑 : Ideal (𝓞 F)} {𝔟 : NarrowClassGroup F → (FractionalIdeal (𝓞 F)⁰ F)ˣ} (𝔞 : (Ideal (𝓞 F))⁰)

instance : NeZero (𝔞 : Ideal (𝓞 F)) :=
  ⟨nonZeroDivisors.coe_ne_zero 𝔞⟩

lemma exists_spanSingleton_mul_eq (h𝔟 : ∀ c, NarrowClassGroup.mk (𝔟 c) = c)
    (c : NarrowClassGroup F) : ∃ δ : Fˣ, IsTotallyPositive (δ : F) ∧
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (δ : F) * 𝔟 c =
        𝔞 * 𝔟 (c * (NarrowClassGroup.mk0 𝔞)⁻¹) := by
  have h : NarrowClassGroup.mk (𝔟 (c * (NarrowClassGroup.mk0 𝔞)⁻¹)) =
      NarrowClassGroup.mk (𝔟 c * (FractionalIdeal.mk0 F 𝔞)⁻¹) := by
    rw [h𝔟, map_mul, map_inv, NarrowClassGroup.mk_mk0, h𝔟]
  rcases NarrowClassGroup.mk_eq_mk_iff.mp h with ⟨z, hz, hzeq⟩
  rcases mem_narrowPrincipalSubgroup.mp hz with ⟨x, hx, rfl⟩
  refine ⟨x⁻¹, mem_totallyPositiveUnits.mp (inv_mem (mem_totallyPositiveUnits.mpr hx)), ?_⟩
  have h' : 𝔟 c = 𝔟 (c * (NarrowClassGroup.mk0 𝔞)⁻¹) * toPrincipalIdeal (𝓞 F) F x *
      FractionalIdeal.mk0 F 𝔞 := by
    rw [hzeq, inv_mul_cancel_right]
  have hx' : FractionalIdeal.spanSingleton (𝓞 F)⁰ ((x⁻¹ : Fˣ) : F) *
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F) = 1 := by
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  rw [h', Units.val_mul, Units.val_mul, coe_toPrincipalIdeal, FractionalIdeal.coe_mk0,
    ← one_mul ((𝔞 : FractionalIdeal (𝓞 F)⁰ F) * _), ← hx']
  ac_rfl

/-- **The Hecke operator `T_𝔞` from the component `c 𝔞⁻¹` to the component `c` is a nonempty sum**:
some `diag(1, δ)`, `δ` totally positive, lies in `heckeSet 𝔑 𝔞 𝔟_c 𝔟_{c 𝔞⁻¹}`. -/
lemma heckeCosets_nonempty (h𝔟 : ∀ c, NarrowClassGroup.mk (𝔟 c) = c) (c : NarrowClassGroup F) :
    (heckeCosets 𝔑 𝔞 (𝔟 c) (𝔟 (c * (NarrowClassGroup.mk0 𝔞)⁻¹))).Nonempty := by
  rcases exists_spanSingleton_mul_eq 𝔞 h𝔟 c with ⟨δ, hδ, hdet⟩
  exact ⟨_, _, heckeDiagonal_mem_heckeSet hδ hdet, rfl⟩

variable [NeZero 𝔑]

/-- The **Hecke operator `T_𝔞`** of a nonzero ideal `𝔞` of `𝒪_F` on the space of Hilbert modular
forms of weight `k` and level `𝔑`: `(T_𝔞 f)_c = ∑_α f_{c'} ∣ₖ α`, where `c' = c [𝔞]⁻¹` in the
narrow class group and `α` runs over representatives of `Γ₀(𝔑)_{𝔟_{c'}} \ heckeSet 𝔑 𝔞 𝔟_c 𝔟_{c'}`.
It permutes the components by `c' ↦ c' [𝔞]`. -/
noncomputable def heckeIdealSpace : Module.End ℂ (space k 𝔑 𝔟) where
  toFun f := ⟨fun c ↦ (heckeIdealOperator k 𝔑 𝔞 (𝔟 c) (𝔟 (c * (NarrowClassGroup.mk0 𝔞)⁻¹))
      ⟨f.1 (c * (NarrowClassGroup.mk0 𝔞)⁻¹), (f.2 _).2.2⟩ :
        ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ),
    fun _ ↦ ⟨(f.2 _).1.heckeIdeal, (f.2 _).2.1.heckeIdeal, Subtype.prop _⟩⟩
  map_add' f f' := Subtype.ext <| funext fun c ↦ congrArg Subtype.val <|
    map_add (heckeIdealOperator k 𝔑 𝔞 (𝔟 c) (𝔟 (c * (NarrowClassGroup.mk0 𝔞)⁻¹)))
      ⟨f.1 _, (f.2 _).2.2⟩ ⟨f'.1 _, (f'.2 _).2.2⟩
  map_smul' a f := Subtype.ext <| funext fun c ↦ congrArg Subtype.val <|
    map_smul (heckeIdealOperator k 𝔑 𝔞 (𝔟 c) (𝔟 (c * (NarrowClassGroup.mk0 𝔞)⁻¹))) a
      ⟨f.1 _, (f.2 _).2.2⟩

variable {h𝔟 : ∀ c, NarrowClassGroup.mk (𝔟 c) = c} (ψ : HilbertModularForm 𝔑 k 𝔟 h𝔟)

/-- The **Hecke operator `T_𝔞`** applied to a Hilbert modular form `ψ`: the Hilbert modular form
`(T_𝔞 ψ)_c = ∑_α ψ_{c [𝔞]⁻¹} ∣ₖ α` (`heckeIdealSpace`). -/
noncomputable def heckeIdealForm : HilbertModularForm 𝔑 k 𝔟 h𝔟 where
  toFun c := heckeIdealOperator k 𝔑 𝔞 (𝔟 c) (𝔟 (c * (NarrowClassGroup.mk0 𝔞)⁻¹))
    ⟨ψ.toFun _, ψ.toFun_mem_slashInvariants _⟩
  isHolomorphic _ := (ψ.isHolomorphic _).heckeIdeal
  isBoundedAtCusps _ := (ψ.isBoundedAtCusps _).heckeIdeal
  smul_eq c γ hγ z := (mem_slashInvariants_iff fun _ ↦ isTotallyPositive_det_of_mem_gammaZero).mp
    (heckeIdealOperator k 𝔑 𝔞 (𝔟 c) (𝔟 (c * (NarrowClassGroup.mk0 𝔞)⁻¹))
      ⟨ψ.toFun _, ψ.toFun_mem_slashInvariants _⟩).2 γ hγ z

lemma coe_heckeIdealSpace_toFun :
    (heckeIdealSpace 𝔞 ⟨ψ.toFun, ψ.toFun_mem_space⟩ : NarrowClassGroup F →
      ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) = (ψ.heckeIdealForm 𝔞).toFun :=
  rfl

variable {ψ} in
/-- **`T_𝔞` maps cusp forms to cusp forms.** -/
lemma IsCuspForm.heckeIdealForm (h : ψ.IsCuspForm) : (ψ.heckeIdealForm 𝔞).IsCuspForm :=
  fun _ ↦ VanishesAtCusps.heckeIdeal (h _)

/-- `ψ` **has Hecke eigenvalue** `a` for `T_𝔞`: `T_𝔞 ψ = a ψ`. -/
def HasHeckeIdealEigenvalue (a : ℂ) : Prop :=
  (ψ.heckeIdealForm 𝔞).toFun = a • ψ.toFun

variable {ψ 𝔞} in
/-- **The Hecke eigenvalue of a nonzero form is unique.** -/
lemma HasHeckeIdealEigenvalue.eq (hψ : ψ.toFun ≠ 0) {a b : ℂ} (ha : ψ.HasHeckeIdealEigenvalue 𝔞 a)
    (hb : ψ.HasHeckeIdealEigenvalue 𝔞 b) : a = b :=
  smul_left_injective ℂ hψ <| ha.symm.trans hb

/-- `ψ` is a **Hecke eigenform** for the Hecke operators `T_𝔞` coprime to the level: `ψ ≠ 0` and
`ψ` is an eigenvector of `T_𝔞` for every nonzero ideal `𝔞` with `𝔞 + 𝔑 = 𝒪_F`. -/
def IsHeckeIdealEigenform : Prop :=
  ψ.toFun ≠ 0 ∧ ∀ 𝔭 : (Ideal (𝓞 F))⁰, (𝔭 : Ideal (𝓞 F)) ⊔ 𝔑 = ⊤ →
    ∃ a : ℂ, ψ.HasHeckeIdealEigenvalue 𝔭 a

variable {ψ} in
/-- The **Hecke eigenvalue** `a_𝔞` (LMFDB `mf.hilbert.eigenvalue`) of a Hecke eigenform `ψ` at a
nonzero ideal `𝔞` coprime to the level: the unique `a_𝔞 ∈ ℂ` with `T_𝔞 ψ = a_𝔞 ψ`
(`HasHeckeIdealEigenvalue.eq`). The LMFDB normalises `ψ` by `a_(1) = 1`, a condition on Fourier
coefficients that is not formalised, and its `T_𝔞` differs from `heckeIdealSpace` by a power of
`N(𝔞)` and a rescaling of the components. -/
noncomputable def heckeIdealEigenvalue (hψ : ψ.IsHeckeIdealEigenform)
    (h𝔞 : (𝔞 : Ideal (𝓞 F)) ⊔ 𝔑 = ⊤) : ℂ :=
  (hψ.2 𝔞 h𝔞).choose

variable {ψ} in
lemma hasHeckeIdealEigenvalue_heckeIdealEigenvalue (hψ : ψ.IsHeckeIdealEigenform)
    (h𝔞 : (𝔞 : Ideal (𝓞 F)) ⊔ 𝔑 = ⊤) : ψ.HasHeckeIdealEigenvalue 𝔞 (heckeIdealEigenvalue 𝔞 hψ h𝔞) :=
  (hψ.2 𝔞 h𝔞).choose_spec

/-- The **Hecke orbit** (LMFDB `mf.hilbert.hecke_orbit`) of a Hilbert modular form `ψ`: the
subspace of the space of Hilbert modular forms of weight `k` and level `𝔑` spanned by the images of
`ψ` under the finite products of the Hecke operators `T_𝔞`, `𝔞` coprime to the level. -/
noncomputable def heckeIdealOrbit : Submodule ℂ (space k 𝔑 𝔟) :=
  Submodule.span ℂ <| Set.range fun l : List {𝔭 : (Ideal (𝓞 F))⁰ // (𝔭 : Ideal (𝓞 F)) ⊔ 𝔑 = ⊤} ↦
    (l.map fun 𝔭 ↦ heckeIdealSpace 𝔭.1).prod ⟨ψ.toFun, ψ.toFun_mem_space⟩

lemma mem_heckeIdealOrbit : ⟨ψ.toFun, ψ.toFun_mem_space⟩ ∈ ψ.heckeIdealOrbit :=
  Submodule.subset_span ⟨[], rfl⟩

variable {ψ} in
lemma prod_heckeIdealSpace_apply (hψ : ψ.IsHeckeIdealEigenform)
    (l : List {𝔭 : (Ideal (𝓞 F))⁰ // (𝔭 : Ideal (𝓞 F)) ⊔ 𝔑 = ⊤}) :
    (l.map fun 𝔭 ↦ heckeIdealSpace 𝔭.1).prod ⟨ψ.toFun, ψ.toFun_mem_space⟩ =
      (l.map fun 𝔭 ↦ heckeIdealEigenvalue 𝔭.1 hψ 𝔭.2).prod •
        (⟨ψ.toFun, ψ.toFun_mem_space⟩ : space k 𝔑 𝔟) := by
  induction l with
  | nil => simp
  | cons 𝔭 l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, map_smul, List.map_cons,
      List.prod_cons, mul_comm, mul_smul]
    exact congrArg _ <| Subtype.ext <| hasHeckeIdealEigenvalue_heckeIdealEigenvalue 𝔭.1 hψ 𝔭.2

variable {ψ} in
/-- **The Hecke orbit of a Hecke eigenform `ψ` is the line `ℂ ψ`.** -/
lemma heckeIdealOrbit_eq_span (hψ : ψ.IsHeckeIdealEigenform) :
    ψ.heckeIdealOrbit = ℂ ∙ ⟨ψ.toFun, ψ.toFun_mem_space⟩ := by
  refine le_antisymm (Submodule.span_le.mpr ?_) <|
    (Submodule.span_singleton_le_iff_mem _ _).mpr ψ.mem_heckeIdealOrbit
  rintro _ ⟨l, rfl⟩
  exact Submodule.mem_span_singleton.mpr ⟨_, (prod_heckeIdealSpace_apply hψ l).symm⟩

end HilbertModularForm
