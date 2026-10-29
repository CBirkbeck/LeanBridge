import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.HeckeCosetDecomposition

/-!
# The Hecke operators `U_𝔭` on Hilbert modular forms

Let `F` be a number field, `𝔑` a nonzero ideal of `𝒪_F` and `(𝔟_c)` representatives of the narrow
class group. Shimura (Duke Math. J. 45 (1978), §2) defines the Hecke operators of level `𝔑` with the
matrices `α = (a, b; c, d)` of `HilbertModularGroup.heckeSet` (`a ∈ 𝒪_F`, `b ∈ 𝔟⁻¹`, `c ∈ 𝔑𝔠`,
totally positive determinant, `(det α) 𝔟 = 𝔫𝔠`) that satisfy, in addition, `a𝒪_F + 𝔑 = 𝒪_F`, i.e.
`a` is a unit modulo `𝔑`. This set is stable under `Γ₀(𝔑)_𝔟` on the right, so it defines an
operator `T(𝔫)` on the space of Hilbert modular forms, as in `Hilbert/HeckeIdeal.lean`.

For a prime `𝔭 = (π) ⊇ 𝔑` with `π` totally positive, `T(𝔭)` is the operator `U_𝔭`. Its right cosets
are those of the `(1, b; 0, π)`, `b ∈ 𝔟⁻¹ / π 𝔟⁻¹`, each exactly once: the argument for `a ∉ 𝔭` of
`Hilbert/HeckeCosetDecomposition.lean` applies to every matrix of the set (`a` is a unit modulo
`𝔑 ⊆ 𝔭`), and the representative `(π, 0; 0, 1)` of `T_𝔭` for `𝔭 ∤ 𝔑` is excluded, since `π ∈ 𝔭`
is not a unit modulo `𝔑`. On Fourier expansions in parallel weight `m`, `U_𝔭` therefore has
coefficients `N(𝔭)^{1 - m/2} a(πμ)`, so the normalised `N(𝔭)^{m/2 - 1} U_𝔭` has eigenvalue `a_𝔭`
on a normalised eigenform. Only narrow-principal `𝔭` are treated, as in `Hilbert/HeckeFourier.lean`.

## Main definitions

* `HilbertModularGroup.shimuraHeckeSet`: Shimura's matrices of `T(𝔫)` at level `𝔑`.
* `HilbertModularGroup.shimuraHeckeCosets`: their right cosets.
* `HilbertModularForm.shimuraHeckeOperator`: `T(𝔫)` from one component to another.
* `HilbertModularForm.shimuraHeckeSpace`: `T(𝔫)` on the space of Hilbert modular forms, which is
  `U_𝔭` for a prime `𝔭 ⊇ 𝔑`.
* `HilbertModularForm.shimuraHeckeForm`: the Hilbert modular form `T(𝔫) f`.
* `HilbertModularForm.HasShimuraHeckeEigenvalue`: eigenvectors of `T(𝔫)`.
* `HilbertModularForm.IsUEigenform`: eigenforms of the `U_𝔭`, `𝔭 ⊇ 𝔑` prime.
* `HilbertModularForm.uEigenvalue`, `HilbertModularForm.uEigenvalueNormalised` (LMFDB
  `mf.hilbert.eigenvalue` at `𝔭 ∣ 𝔑`): the eigenvalue of `U_𝔭`, unnormalised and normalised.

## Main results

* `HilbertModularGroup.mul_mem_shimuraHeckeSet`: the set is stable under `Γ₀(𝔑)_𝔟` on the right.
* `HilbertModularGroup.finite_shimuraHeckeCosets`: it has finitely many right cosets.
* `HilbertModularForm.bijOn_mk_heckeUpper`: the coset decomposition of `U_𝔭`.
* `HilbertModularForm.hasHilbertFourierExpansion_shimuraHeckeOperator`: `U_𝔭` has Fourier
  coefficients `N(𝔭)^{1 - m/2} a(πμ)`.
* `HilbertModularForm.uEigenvalueNormalised_eq_idealCoeff`: the normalised eigenvalue of `U_𝔭` on a
  normalised eigenform is its Fourier coefficient `a_𝔭`.
-/

open Matrix Complex NumberField InfinitePlace HilbertModularGroup Set

open scoped nonZeroDivisors UpperHalfPlane

namespace HilbertModularGroup

variable {F : Type*} [Field F] {𝔑 𝔫 : Ideal (𝓞 F)} {𝔟 𝔠 : FractionalIdeal (𝓞 F)⁰ F}

lemma mul_mem_map_of_mem_smul {x z : F} (hx : ∀ y ∈ 𝔟, x * y ∈ (1 : Submodule (𝓞 F) F))
    (hz : z ∈ 𝔑 • (𝔟 : Submodule (𝓞 F) F)) :
    x * z ∈ Submodule.map (Algebra.linearMap (𝓞 F) F) 𝔑 := by
  refine Submodule.smul_induction_on hz (fun n hn y hy ↦ ?_) fun z z' hz hz' ↦ ?_
  · rcases Submodule.mem_one.mp (hx y hy) with ⟨s, hs⟩
    refine ⟨n * s, 𝔑.mul_mem_right s hn, ?_⟩
    rw [Algebra.linearMap_apply, map_mul, hs, Algebra.smul_def]
    ring1
  · rw [mul_add]
    exact add_mem hz hz'

variable [NumberField F]

variable (𝔑 𝔫 𝔟 𝔠) in
/-- **Shimura's matrices of the Hecke operator `T(𝔫)` at level `𝔑`**, from the component of `𝔠` to
the component of `𝔟`: the `α = (a, b; c, d)` of `heckeSet 𝔑 𝔫 𝔟 𝔠` whose entry `a ∈ 𝒪_F` is a unit
modulo `𝔑`, i.e. `a𝒪_F + 𝔑 = 𝒪_F`. For a prime `𝔭 ⊇ 𝔑` this gives the operator `U_𝔭`. -/
def shimuraHeckeSet : Set (GL (Fin 2) F) :=
  {α | α ∈ heckeSet 𝔑 𝔫 𝔟 𝔠 ∧
    ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = α.val 0 0 ∧ IsUnit (Ideal.Quotient.mk 𝔑 r)}

/-- **Shimura's set is stable under `Γ₀(𝔑)_𝔟` on the right**: for `γ ∈ Γ₀(𝔑)_𝔟`, the entry `γ₀₀`
is a unit modulo `𝔑` and `(αγ)₀₀ ≡ a γ₀₀` modulo `𝔑`. -/
lemma mul_mem_shimuraHeckeSet (h𝔟 : 𝔟 ≠ 0) {α γ : GL (Fin 2) F}
    (hα : α ∈ shimuraHeckeSet 𝔑 𝔫 𝔟 𝔠) (hγ : γ ∈ gammaZero 𝔟 (glPlus 𝔟) 𝔑) :
    α * γ ∈ shimuraHeckeSet 𝔑 𝔫 𝔟 𝔠 := by
  rcases hα with ⟨hα, r, hr, hu⟩
  have hL : ∀ v ∈ lattice 𝔟, γ.val *ᵥ v ∈ lattice 𝔟 := fun v ↦ (hγ.1.1 v).mp
  have hc : γ.val 1 0 ∈ 𝔑 • (𝔟 : Submodule (𝓞 F) F) := by
    simpa [mulVec, dotProduct] using ((mem_gammaZeroLattice _ _).mp ((hγ.2 ![1, 0]).mp
      ((mem_gammaZeroLattice _ _).mpr ⟨Submodule.mem_one.mpr ⟨1, map_one _⟩, zero_mem _⟩))).2
  rcases Submodule.mem_one.mp (apply_zero_zero_mem hL) with ⟨s, hs⟩
  rcases Submodule.mem_one.mp (mem_one_of_forall_mul_mem h𝔟 fun _ ↦ apply_one_one_mul_mem hL) with
    ⟨t, ht⟩
  rcases mul_mem_map_of_mem_smul (fun _ ↦ apply_zero_one_mul_mem hL) hc with ⟨n₂, hn₂, hn₂'⟩
  rcases mul_mem_map_of_mem_smul (fun _ ↦ apply_zero_one_mul_mem hα.2.1) hc with ⟨n₁, hn₁, hn₁'⟩
  rw [Algebra.linearMap_apply] at hn₁' hn₂'
  have hdet : FractionalIdeal.spanSingleton (𝓞 F)⁰ γ.det.val =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ 1 :=
    (spanSingleton_det_eq_one h𝔟 hγ.1.1).trans (map_one _).symm
  rcases FractionalIdeal.spanSingleton_eq_spanSingleton.mp hdet with ⟨z, hz⟩
  rw [Units.smul_def, Algebra.smul_def, GeneralLinearGroup.val_det_apply, det_fin_two] at hz
  have h1 : z * (s * t - n₂) = 1 := IsFractionRing.injective (𝓞 F) F <| by
    rw [map_mul, map_sub, map_mul, map_one, hs, ht, hn₂']
    linear_combination hz
  have hst : Ideal.Quotient.mk 𝔑 s * (Ideal.Quotient.mk 𝔑 t * Ideal.Quotient.mk 𝔑 z) = 1 := by
    rw [← map_mul, ← map_mul, ← map_one (Ideal.Quotient.mk 𝔑), Ideal.Quotient.eq]
    have h : s * (t * z) - 1 = z * n₂ := by
      linear_combination h1
    rw [h]
    exact 𝔑.mul_mem_left z hn₂
  refine ⟨mul_mem_heckeSet h𝔟 hα hγ, r * s + n₁, ?_, ?_⟩
  · rw [map_add, map_mul, hr, hs, hn₁', Units.val_mul, mul_apply, Fin.sum_univ_two]
  · rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hn₁, add_zero, map_mul]
    exact hu.mul (.of_mul_eq_one _ hst)

variable (𝔑 𝔫 𝔟 𝔠) in
/-- The right cosets `Γ₀(𝔑)_𝔠 α` of the matrices `α` of `shimuraHeckeSet 𝔑 𝔫 𝔟 𝔠`. -/
noncomputable def shimuraHeckeCosets : Set (gammaZeroRightCosets 𝔑 𝔠) :=
  Quotient.mk _ '' shimuraHeckeSet 𝔑 𝔫 𝔟 𝔠

lemma shimuraHeckeCosets_subset : shimuraHeckeCosets 𝔑 𝔫 𝔟 𝔠 ⊆ heckeCosets 𝔑 𝔫 𝔟 𝔠 :=
  image_mono fun _ h ↦ h.1

/-- **The coset space `Γ₀(𝔑)_𝔠 \ shimuraHeckeSet 𝔑 𝔫 𝔟 𝔠` is finite.** -/
lemma finite_shimuraHeckeCosets (h𝔟 : 𝔟 ≠ 0) (h𝔑 : 𝔑 ≠ ⊥) (h𝔫 : 𝔫 ≠ ⊥) :
    (shimuraHeckeCosets 𝔑 𝔫 𝔟 𝔠).Finite :=
  (finite_heckeCosets h𝔟 h𝔑 h𝔫).subset shimuraHeckeCosets_subset

end HilbertModularGroup

namespace HilbertModularForm

variable {F : Type*} [Field F] [NumberField F] {k : {w : InfinitePlace F // w.IsReal} → ℤ}
  {𝔑 𝔫 : Ideal (𝓞 F)} {𝔟 𝔠 : FractionalIdeal (𝓞 F)⁰ F} [NeZero 𝔟] [NeZero 𝔑] [NeZero 𝔫]

lemma isTotallyPositive_det_out_of_mem {q : gammaZeroRightCosets 𝔑 𝔠}
    (hq : q ∈ (finite_shimuraHeckeCosets (𝔠 := 𝔠) (NeZero.ne 𝔟) (NeZero.ne 𝔑)
      (NeZero.ne 𝔫)).toFinset) : IsTotallyPositive q.out.det.val :=
  isTotallyPositive_det_out (shimuraHeckeCosets_subset ((Finite.mem_toFinset _).mp hq))

variable (k 𝔑 𝔫 𝔟 𝔠) in
/-- **Shimura's Hecke operator `T(𝔫)`** at level `𝔑` from the component of `𝔠` to the component of
`𝔟`, on the functions satisfying the transformation law of weight `k`: `φ ↦ ∑_α φ ∣ₖ α`, where `α`
runs over representatives of the finitely many right cosets `Γ₀(𝔑)_𝔠 α ⊆ shimuraHeckeSet 𝔑 𝔫 𝔟 𝔠`.
For a prime `𝔫 = 𝔭 ⊇ 𝔑` it is the operator `U_𝔭`. -/
noncomputable def shimuraHeckeOperator : slashInvariants k (gammaZero 𝔠 (glPlus 𝔠) 𝔑) →ₗ[ℂ]
    slashInvariants k (gammaZero 𝔟 (glPlus 𝔟) 𝔑) where
  toFun φ := ⟨∑ q ∈ (finite_shimuraHeckeCosets (NeZero.ne 𝔟) (NeZero.ne 𝔑) (NeZero.ne 𝔫)).toFinset,
    slashLinearMap k q.out φ, fun γ hγ ↦ by
    have hγ' : IsTotallyPositive γ.det.val :=
      isTotallyPositive_det_of_mem_gammaZero hγ
    rw [← slashLinearMap_apply, map_sum]
    refine (Finset.sum_congr rfl fun q hq ↦ ?_).trans <| Finset.sum_nbij'
      (f := fun q : gammaZeroRightCosets 𝔑 𝔠 ↦ slash k (q.out * γ) φ)
      (fun q ↦ ⟦q.out * γ⟧) (fun q ↦ ⟦q.out * γ⁻¹⟧) ?_ ?_ (fun q _ ↦ mk_out_mul_mul_inv q γ)
      (fun q _ ↦ by simpa using mk_out_mul_mul_inv q γ⁻¹) fun q hq ↦ ?_
    · exact (slash_mul k _ _ φ (isTotallyPositive_det_out_of_mem hq) hγ').symm
    · rintro q hq
      rw [Finite.mem_toFinset] at hq ⊢
      rcases hq with ⟨α, hα, rfl⟩
      rw [mk_out_mul]
      exact ⟨_, mul_mem_shimuraHeckeSet (NeZero.ne 𝔟) hα hγ, rfl⟩
    · rintro q hq
      rw [Finite.mem_toFinset] at hq ⊢
      rcases hq with ⟨α, hα, rfl⟩
      rw [mk_out_mul]
      exact ⟨_, mul_mem_shimuraHeckeSet (NeZero.ne 𝔟) hα (inv_mem hγ), rfl⟩
    · rw [slashLinearMap_apply, slash_out_mk φ.2]
      rw [map_mul]
      exact mem_totallyPositiveUnits.mp (mul_mem (mem_totallyPositiveUnits.mpr
        (isTotallyPositive_det_out_of_mem hq)) hγ.1.2)⟩
  map_add' φ₁ φ₂ := Subtype.ext <| by
    simp [Finset.sum_add_distrib]
  map_smul' c φ := Subtype.ext <| by
    simp [Finset.smul_sum]

lemma coe_shimuraHeckeOperator (φ : slashInvariants k (gammaZero 𝔠 (glPlus 𝔠) 𝔑)) :
    (shimuraHeckeOperator k 𝔑 𝔫 𝔟 𝔠 φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) =
      ∑ q ∈ (finite_shimuraHeckeCosets (𝔠 := 𝔠) (NeZero.ne 𝔟) (NeZero.ne 𝔑)
        (NeZero.ne 𝔫)).toFinset, slash k q.out φ :=
  rfl

variable {φ : slashInvariants k (gammaZero 𝔠 (glPlus 𝔠) 𝔑)}

lemma IsHolomorphic.shimuraHecke
    (h : IsHolomorphic (φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ)) : IsHolomorphic
      (shimuraHeckeOperator k 𝔑 𝔫 𝔟 𝔠 φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) := by
  rw [coe_shimuraHeckeOperator]
  exact Finset.sum_induction _ IsHolomorphic (fun _ _ ↦ IsHolomorphic.add)
    (differentiableOn_const 0) fun _ hq ↦ h.slash (isTotallyPositive_det_out_of_mem hq)

lemma IsBoundedAtCusps.shimuraHecke
    (h : IsBoundedAtCusps k (φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ)) :
    IsBoundedAtCusps k
      (shimuraHeckeOperator k 𝔑 𝔫 𝔟 𝔠 φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) := by
  rw [coe_shimuraHeckeOperator]
  exact Finset.sum_induction _ (fun f ↦ IsBoundedAtCusps k f) (fun _ _ ↦ IsBoundedAtCusps.add)
    isBoundedAtCusps_zero fun _ hq ↦ h.slash (isTotallyPositive_det_out_of_mem hq)

lemma VanishesAtCusps.shimuraHecke
    (h : VanishesAtCusps k (φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ)) :
    VanishesAtCusps k
      (shimuraHeckeOperator k 𝔑 𝔫 𝔟 𝔠 φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) := by
  rw [coe_shimuraHeckeOperator]
  exact Finset.sum_induction _ (fun f ↦ VanishesAtCusps k f) (fun _ _ ↦ VanishesAtCusps.add)
    vanishesAtCusps_zero fun _ hq ↦ h.slash (isTotallyPositive_det_out_of_mem hq)

end HilbertModularForm

namespace HilbertModularForm

variable {F : Type*} [Field F] [NumberField F] {k : {w : InfinitePlace F // w.IsReal} → ℤ}
  {𝔑 : Ideal (𝓞 F)} {𝔟 : NarrowClassGroup F → (FractionalIdeal (𝓞 F)⁰ F)ˣ} (𝔞 : (Ideal (𝓞 F))⁰)
  [NeZero 𝔑]

/-- **Shimura's Hecke operator `T(𝔞)`** of a nonzero ideal `𝔞` of `𝒪_F` on the space of Hilbert
modular forms of weight `k` and level `𝔑`: `(T(𝔞) f)_c = ∑_α f_{c'} ∣ₖ α`, where `c' = c [𝔞]⁻¹` and
`α` runs over representatives of `Γ₀(𝔑)_{𝔟_{c'}} \ shimuraHeckeSet 𝔑 𝔞 𝔟_c 𝔟_{c'}`. For a prime
`𝔞 = 𝔭 ⊇ 𝔑` this is the operator **`U_𝔭`**, unnormalised. -/
noncomputable def shimuraHeckeSpace : Module.End ℂ (space k 𝔑 𝔟) where
  toFun f := ⟨fun c ↦ (shimuraHeckeOperator k 𝔑 𝔞 (𝔟 c) (𝔟 (c * (NarrowClassGroup.mk0 𝔞)⁻¹))
      ⟨f.1 (c * (NarrowClassGroup.mk0 𝔞)⁻¹), (f.2 _).2.2⟩ :
        ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ),
    fun _ ↦ ⟨(f.2 _).1.shimuraHecke, (f.2 _).2.1.shimuraHecke, Subtype.prop _⟩⟩
  map_add' f f' := Subtype.ext <| funext fun c ↦ congrArg Subtype.val <|
    map_add (shimuraHeckeOperator k 𝔑 𝔞 (𝔟 c) (𝔟 (c * (NarrowClassGroup.mk0 𝔞)⁻¹)))
      ⟨f.1 _, (f.2 _).2.2⟩ ⟨f'.1 _, (f'.2 _).2.2⟩
  map_smul' a f := Subtype.ext <| funext fun c ↦ congrArg Subtype.val <|
    map_smul (shimuraHeckeOperator k 𝔑 𝔞 (𝔟 c) (𝔟 (c * (NarrowClassGroup.mk0 𝔞)⁻¹))) a
      ⟨f.1 _, (f.2 _).2.2⟩

variable {h𝔟 : ∀ c, NarrowClassGroup.mk (𝔟 c) = c} (ψ : HilbertModularForm 𝔑 k 𝔟 h𝔟)

/-- **Shimura's Hecke operator `T(𝔞)`** applied to a Hilbert modular form `ψ`: the Hilbert modular
form `(T(𝔞) ψ)_c = ∑_α ψ_{c [𝔞]⁻¹} ∣ₖ α` (`shimuraHeckeSpace`); `U_𝔭 ψ` for a prime `𝔭 ⊇ 𝔑`. -/
noncomputable def shimuraHeckeForm : HilbertModularForm 𝔑 k 𝔟 h𝔟 where
  toFun c := shimuraHeckeOperator k 𝔑 𝔞 (𝔟 c) (𝔟 (c * (NarrowClassGroup.mk0 𝔞)⁻¹))
    ⟨ψ.toFun _, ψ.toFun_mem_slashInvariants _⟩
  isHolomorphic _ := (ψ.isHolomorphic _).shimuraHecke
  isBoundedAtCusps _ := (ψ.isBoundedAtCusps _).shimuraHecke
  smul_eq c γ hγ z := (mem_slashInvariants_iff fun _ ↦ isTotallyPositive_det_of_mem_gammaZero).mp
    (shimuraHeckeOperator k 𝔑 𝔞 (𝔟 c) (𝔟 (c * (NarrowClassGroup.mk0 𝔞)⁻¹))
      ⟨ψ.toFun _, ψ.toFun_mem_slashInvariants _⟩).2 γ hγ z

lemma coe_shimuraHeckeSpace_toFun :
    (shimuraHeckeSpace 𝔞 ⟨ψ.toFun, ψ.toFun_mem_space⟩ : NarrowClassGroup F →
      ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) = (ψ.shimuraHeckeForm 𝔞).toFun :=
  rfl

variable {ψ} in
lemma IsCuspForm.shimuraHeckeForm (h : ψ.IsCuspForm) : (ψ.shimuraHeckeForm 𝔞).IsCuspForm :=
  fun _ ↦ VanishesAtCusps.shimuraHecke (h _)

/-- `ψ` **has eigenvalue** `a` for Shimura's `T(𝔞)`: `T(𝔞) ψ = a ψ`. -/
def HasShimuraHeckeEigenvalue (a : ℂ) : Prop :=
  (ψ.shimuraHeckeForm 𝔞).toFun = a • ψ.toFun

variable {ψ 𝔞} in
lemma HasShimuraHeckeEigenvalue.eq (hψ : ψ.toFun ≠ 0) {a b : ℂ}
    (ha : ψ.HasShimuraHeckeEigenvalue 𝔞 a) (hb : ψ.HasShimuraHeckeEigenvalue 𝔞 b) : a = b :=
  smul_left_injective ℂ hψ <| ha.symm.trans hb

/-- `ψ` is an **eigenform of the operators `U_𝔭`**: `ψ ≠ 0` and `ψ` is an eigenvector of
`U_𝔭 = shimuraHeckeSpace 𝔭` for every prime `𝔭 ⊇ 𝔑`. Together with
`HilbertModularForm.IsHeckeIdealEigenform` (the `T_𝔞` with `𝔞 + 𝔑 = 𝒪_F`), this covers the Hecke
operators at all primes. -/
def IsUEigenform : Prop :=
  ψ.toFun ≠ 0 ∧ ∀ 𝔭 : (Ideal (𝓞 F))⁰, (𝔭 : Ideal (𝓞 F)).IsPrime → 𝔑 ≤ 𝔭 →
    ∃ a : ℂ, ψ.HasShimuraHeckeEigenvalue 𝔭 a

variable {ψ} in
/-- The **eigenvalue of `U_𝔭`** on an eigenform `ψ` of the `U_𝔭`, for a prime `𝔭 ⊇ 𝔑`: the unique
`λ ∈ ℂ` with `U_𝔭 ψ = λ ψ` (`HasShimuraHeckeEigenvalue.eq`), unnormalised. -/
noncomputable def uEigenvalue (hψ : ψ.IsUEigenform) (h𝔞 : (𝔞 : Ideal (𝓞 F)).IsPrime)
    (h𝔑𝔞 : 𝔑 ≤ 𝔞) : ℂ :=
  (hψ.2 𝔞 h𝔞 h𝔑𝔞).choose

variable {ψ} in
lemma hasShimuraHeckeEigenvalue_uEigenvalue (hψ : ψ.IsUEigenform)
    (h𝔞 : (𝔞 : Ideal (𝓞 F)).IsPrime) (h𝔑𝔞 : 𝔑 ≤ 𝔞) :
    ψ.HasShimuraHeckeEigenvalue 𝔞 (uEigenvalue 𝔞 hψ h𝔞 h𝔑𝔞) :=
  (hψ.2 𝔞 h𝔞 h𝔑𝔞).choose_spec

variable (m : ℤ) {ψ} in
/-- The **Hecke eigenvalue** `a_𝔭` (LMFDB `mf.hilbert.eigenvalue`) at a prime `𝔭 ∣ 𝔑` of an
eigenform `ψ` of the `U_𝔭` of parallel weight `m`, in the LMFDB's normalisation: `N(𝔭)^{m/2 - 1} λ`,
where `λ` is the eigenvalue of `U_𝔭 = shimuraHeckeSpace 𝔭` (`uEigenvalue`), as for
`HilbertModularForm.heckeIdealEigenvalueNormalised`. For a normalised eigenform and `𝔭 = (π)` with
`π` totally positive, it is the Fourier coefficient `a_𝔭`
(`HilbertModularForm.uEigenvalueNormalised_eq_idealCoeff`). -/
noncomputable def uEigenvalueNormalised (hψ : ψ.IsUEigenform) (h𝔞 : (𝔞 : Ideal (𝓞 F)).IsPrime)
    (h𝔑𝔞 : 𝔑 ≤ 𝔞) : ℂ :=
  (((Ideal.absNorm (𝔞 : Ideal (𝓞 F)) : ℝ) ^ ((m : ℝ) / 2 - 1) : ℝ) : ℂ) * uEigenvalue 𝔞 hψ h𝔞 h𝔑𝔞

lemma coe_shimuraHeckeForm_toFun (h : NarrowClassGroup.mk0 𝔞 = 1) (c : NarrowClassGroup F) :
    (ψ.shimuraHeckeForm 𝔞).toFun c = shimuraHeckeOperator k 𝔑 𝔞 (𝔟 c) (𝔟 c)
      ⟨ψ.toFun c, ψ.toFun_mem_slashInvariants c⟩ := by
  have key (c' : NarrowClassGroup F) (hc : c' = c) :
      (shimuraHeckeOperator k 𝔑 𝔞 (𝔟 c) (𝔟 c') ⟨ψ.toFun c', ψ.toFun_mem_slashInvariants c'⟩ :
        ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) =
      shimuraHeckeOperator k 𝔑 𝔞 (𝔟 c) (𝔟 c) ⟨ψ.toFun c, ψ.toFun_mem_slashInvariants c⟩ := by
    subst hc
    rfl
  exact key _ (by rw [h, inv_one, mul_one])

end HilbertModularForm

namespace HilbertModularForm

variable {F : Type*} [Field F] [NumberField F] {π : Fˣ} {𝔟 : (FractionalIdeal (𝓞 F)⁰ F)ˣ}
  {𝔭 𝔑 : Ideal (𝓞 F)} {α : GL (Fin 2) F}

lemma exists_mk_heckeUpper_eq
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = (𝔭 : FractionalIdeal (𝓞 F)⁰ F))
    (h𝔭 : 𝔭.IsMaximal) (hπ : IsTotallyPositive (π : F)) (hα : α ∈ heckeSet 𝔑 𝔭 𝔟 𝔟)
    (ha' : (π : F)⁻¹ * α.val 0 0 ∉ (1 : Submodule (𝓞 F) F)) :
    ∃ q : HeckeTranslations π 𝔟, (⟦heckeUpper π q.out⟧ :
      gammaZeroRightCosets 𝔑 (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) = ⟦α⟧ := by
  rcases exists_algebraMap_eq_det_mul_inv hπ𝔭 hα with ⟨z, hz⟩
  rcases hα with ⟨hpos, hL, hL', -⟩
  have hdet : (α.det.val * (π : F)⁻¹)⁻¹ ∈ (1 : Submodule (𝓞 F) F) :=
    Submodule.mem_one.mpr ⟨(z⁻¹ : (𝓞 F)ˣ), by rw [map_units_inv, hz]⟩
  have hδ : (π : F)⁻¹ * (α.val 0 0 * α.val 1 1 - α.val 0 1 * α.val 1 0) ∈
      (1 : Submodule (𝓞 F) F) :=
    Submodule.mem_one.mpr ⟨z, by rw [hz, GeneralLinearGroup.val_det_apply, det_fin_two, mul_comm]⟩
  have ha : α.val 0 0 ∈ (1 : Submodule (𝓞 F) F) := apply_zero_zero_mem hL
  have hb (y : F) (hy : y ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
      α.val 0 1 * y ∈ (1 : Submodule (𝓞 F) F) :=
    apply_zero_one_mul_mem hL hy
  have hc : α.val 1 0 ∈ 𝔑 • ((𝔟 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) := by
    simpa [mulVec, dotProduct] using ((mem_gammaZeroLattice _ _).mp (hL' ![1, 0]
      ((mem_gammaZeroLattice _ _).mpr ⟨Submodule.mem_one.mpr ⟨1, map_one _⟩, zero_mem _⟩))).2
  have hcb : α.val 1 0 ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := Submodule.smul_le_right hc
  have hd : α.val 1 1 ∈ (1 : Submodule (𝓞 F) F) :=
    mem_one_of_forall_mul_mem (Units.ne_zero 𝔟) fun _ ↦ apply_one_one_mul_mem hL
  rcases exists_inv_mul_one_sub_mul_mem hπ𝔭 h𝔭 ha ha' with ⟨a', ha'1, hP⟩
  have hβ : a' * α.val 0 1 ∈ translationLattice 𝔟 :=
    mem_translationLattice_of_forall fun y hy ↦ mul_assoc a' _ y ▸ mul_mem_one ha'1 (hb y hy)
  refine ⟨QuotientAddGroup.mk ⟨_, hβ⟩, (mk_heckeUpper_out hπ ⟨_, hβ⟩).trans
    (mk_heckeUpper_eq_mk hpos hπ hdet ha (fun y hy ↦ ?_) hc ?_)⟩
  · convert mul_mem_one hP (hb y hy) using 1
    ring1
  · refine inv_mul_mem_one_of_mul_mem hπ𝔭 h𝔭.isPrime ha (sub_mem hd ?_) ?_ ha'
    · convert mul_mem_one ha'1 (hb _ hcb) using 1
      ring1
    · convert add_mem hδ (mul_mem_one (hb _ hcb) hP) using 1
      ring1

lemma inv_mul_apply_notMem_one
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = (𝔭 : FractionalIdeal (𝓞 F)⁰ F))
    (h𝔭 : 𝔭 ≠ ⊤) (h𝔑𝔭 : 𝔑 ≤ 𝔭) (hα : α ∈ shimuraHeckeSet 𝔑 𝔭 𝔟 𝔟) :
    (π : F)⁻¹ * α.val 0 0 ∉ (1 : Submodule (𝓞 F) F) := by
  rcases hα with ⟨-, r, hr, hu⟩
  rw [← hr, inv_mul_algebraMap_mem_one_iff hπ𝔭]
  intro hr𝔭
  rcases hu.exists_right_inv with ⟨v, hv⟩
  rcases Ideal.Quotient.mk_surjective v with ⟨s, rfl⟩
  rw [← map_mul, ← map_one (Ideal.Quotient.mk 𝔑), Ideal.Quotient.eq] at hv
  exact h𝔭 <| (Ideal.eq_top_iff_one _).mpr <| by
    simpa using sub_mem (𝔭.mul_mem_right s hr𝔭) (h𝔑𝔭 hv)

lemma heckeUpper_mem_shimuraHeckeSet
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = (𝔭 : FractionalIdeal (𝓞 F)⁰ F))
    (hπ : IsTotallyPositive (π : F)) (q : HeckeTranslations π 𝔟) :
    heckeUpper π q.out ∈ shimuraHeckeSet 𝔑 𝔭 𝔟 𝔟 :=
  ⟨heckeCosetRep_mem_heckeSet hπ𝔭 hπ (some q), 1, by simp [heckeUpper], by simp⟩

/-- **The coset decomposition of `U_𝔭`**: for a prime `𝔭 = (π) ⊇ 𝔑` with `π` totally positive, the
right cosets `Γ₀(𝔑)_𝔟 α`, `α ∈ shimuraHeckeSet 𝔑 𝔭 𝔟 𝔟`, are the cosets of the `(1, b; 0, π)`,
`b ∈ 𝔟⁻¹ / π 𝔟⁻¹`, each exactly once. -/
lemma bijOn_mk_heckeUpper
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = (𝔭 : FractionalIdeal (𝓞 F)⁰ F))
    (h𝔭 : 𝔭.IsPrime) (h𝔑𝔭 : 𝔑 ≤ 𝔭) (hπ : IsTotallyPositive (π : F)) :
    BijOn (fun q : HeckeTranslations π 𝔟 ↦ (⟦heckeUpper π q.out⟧ :
      gammaZeroRightCosets 𝔑 (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) univ
        (shimuraHeckeCosets 𝔑 𝔭 𝔟 𝔟) := by
  have h𝔭' : 𝔭.IsMaximal := h𝔭.isMaximal fun h ↦ π.ne_zero <| by
    rwa [h, FractionalIdeal.coeIdeal_bot, FractionalIdeal.spanSingleton_eq_zero_iff] at hπ𝔭
  exact ⟨fun q _ ↦ ⟨_, heckeUpper_mem_shimuraHeckeSet hπ𝔭 hπ q, rfl⟩,
    fun q _ q' _ h ↦ Option.some_injective _ <|
      injOn_mk_heckeCosetRep hπ𝔭 h𝔭.ne_top (mem_univ (some q)) (mem_univ (some q')) h,
    fun _ ⟨_, hα, hq⟩ ↦ hq ▸ (exists_mk_heckeUpper_eq hπ𝔭 h𝔭' hπ hα.1
      (inv_mul_apply_notMem_one hπ𝔭 h𝔭.ne_top h𝔑𝔭 hα)).imp fun q hq ↦ ⟨mem_univ q, hq⟩⟩

variable {k : {w : InfinitePlace F // w.IsReal} → ℤ} {m : ℤ} [NeZero 𝔑] [NeZero 𝔭]

lemma coe_shimuraHeckeOperator_eq_sum [Fintype (HeckeTranslations π 𝔟)]
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = (𝔭 : FractionalIdeal (𝓞 F)⁰ F))
    (h𝔭 : 𝔭.IsPrime) (h𝔑𝔭 : 𝔑 ≤ 𝔭) (hπ : IsTotallyPositive (π : F))
    (ψ : slashInvariants k (gammaZero (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (glPlus 𝔟) 𝔑)) :
    (shimuraHeckeOperator k 𝔑 𝔭 𝔟 𝔟 ψ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) =
      ∑ q : HeckeTranslations π 𝔟, slash k (heckeUpper π q.out) ψ := by
  have h : BijOn (fun q : HeckeTranslations π 𝔟 ↦ (⟦heckeUpper π q.out⟧ :
      gammaZeroRightCosets 𝔑 (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) univ
        (shimuraHeckeCosets 𝔑 𝔭 𝔟 𝔟) :=
    bijOn_mk_heckeUpper hπ𝔭 h𝔭 h𝔑𝔭 hπ
  rw [coe_shimuraHeckeOperator]
  refine (Finset.sum_nbij (fun q ↦ ⟦heckeUpper π q.out⟧)
    (fun q _ ↦ (Finite.mem_toFinset _).mpr (h.mapsTo (mem_univ q))) ?_ ?_
    fun q _ ↦ (slash_out_mk ψ.2 ?_).symm).symm
  · rw [Finset.coe_univ]
    exact h.injOn
  · rw [Finset.coe_univ, Finite.coe_toFinset]
    exact h.surjOn
  · rw [det_heckeUpper]
    exact hπ

/-- **The operator `U_𝔭` on Fourier expansions**, for a prime `𝔭 = (π) ⊇ 𝔑` with `π` totally
positive, in parallel weight `m`: if `ψ` has Fourier coefficients `a(ν)`, then `U_𝔭 ψ` has Fourier
coefficients `N(𝔭)^{1 - m/2} a(πμ)`. -/
lemma hasHilbertFourierExpansion_shimuraHeckeOperator [IsTotallyReal F]
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = (𝔭 : FractionalIdeal (𝓞 F)⁰ F))
    (h𝔭 : 𝔭.IsPrime) (h𝔑𝔭 : 𝔑 ≤ 𝔭) (hπ : IsTotallyPositive (π : F)) (hk : ∀ w, k w = m)
    (ψ : slashInvariants k (gammaZero (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (glPlus 𝔟) 𝔑))
    {a : fourierDual 𝔟 → ℂ} (hψ : HasHilbertFourierExpansion 𝔟 ψ a) :
    HasHilbertFourierExpansion 𝔟 (shimuraHeckeOperator k 𝔑 𝔭 𝔟 𝔟 ψ) fun μ ↦
      ((Ideal.absNorm 𝔭 : ℝ) ^ (1 - (m : ℝ) / 2) : ℝ) * a ⟨π * μ, mul_mem_fourierDual hπ𝔭 μ.2⟩ := by
  have hcard : Nat.card (HeckeTranslations π 𝔟) = Ideal.absNorm 𝔭 :=
    natCard_heckeTranslations π 𝔭 hπ𝔭
  have hN : Nat.card (HeckeTranslations π 𝔟) ≠ 0 := by
    rw [hcard, Ne, Ideal.absNorm_eq_zero_iff]
    exact NeZero.ne 𝔭
  have hN' : (0 : ℝ) < Ideal.absNorm 𝔭 := by
    rw [← hcard]
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have : Finite (HeckeTranslations π 𝔟) :=
    Nat.finite_of_card_ne_zero hN
  let _ : Fintype (HeckeTranslations π 𝔟) :=
    Fintype.ofFinite _
  have hcard' : (Fintype.card (HeckeTranslations π 𝔟) : ℂ) = Ideal.absNorm 𝔭 := by
    rw [Fintype.card_eq_nat_card, hcard]
  rw [coe_shimuraHeckeOperator_eq_sum hπ𝔭 h𝔭 h𝔑𝔭 hπ]
  convert hasHilbertFourierExpansion_sum_slash_heckeUpper π hπ hk
    (fun _ ↦ mul_mem_fourierDual hπ𝔭) hψ using 2 with μ
  rw [hcard', realNorm_eq_absNorm π 𝔭 hπ hπ𝔭, ← ofReal_natCast, ← ofReal_mul,
    ← Real.rpow_add_one hN'.ne']
  congr 3
  ring1

end HilbertModularForm

namespace HilbertModularForm

variable {F : Type*} [Field F] [NumberField F] {k : {w : InfinitePlace F // w.IsReal} → ℤ}
  {m : ℤ} {𝔑 : Ideal (𝓞 F)} [NeZero 𝔑] {𝔟 : NarrowClassGroup F → (FractionalIdeal (𝓞 F)⁰ F)ˣ}
  {h𝔟 : ∀ c, NarrowClassGroup.mk (𝔟 c) = c} {f : HilbertModularForm 𝔑 k 𝔟 h𝔟}
  {𝔭 : (Ideal (𝓞 F))⁰} {π : Fˣ}

/-- **The `U_𝔭`-eigenvalue of a normalised eigenform is its Fourier coefficient**: for `F` totally
real, an eigenform `f` of the `U_𝔭` of parallel weight `m` with `a_(1) = 1` whose component of `(1)`
has a Fourier expansion, and a prime `𝔭 = (π) ⊇ 𝔑` with `π` totally positive, the normalised
eigenvalue of `U_𝔭` is `a_𝔭`. -/
lemma uEigenvalueNormalised_eq_idealCoeff [IsTotallyReal F] (hk : ∀ w, k w = m)
    (hf : f.IsUEigenform) (hn : f.IsNormalised)
    (hexp : ∃ a, HasHilbertFourierExpansion (𝔟 (idealComponent 1)) (f.toFun (idealComponent 1)) a)
    (h𝔭 : (𝔭 : Ideal (𝓞 F)).IsPrime) (h𝔑𝔭 : 𝔑 ≤ 𝔭) (hπ : IsTotallyPositive (π : F))
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) =
      ((𝔭 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)) :
    uEigenvalueNormalised 𝔭 m hf h𝔭 h𝔑𝔭 = f.idealCoeff 𝔭 := by
  rcases hexp with ⟨a, ha⟩
  have h0 : IsIdealIndex 𝔟 1 (exists_isIdealIndex 𝔟 1 h𝔟).choose :=
    (exists_isIdealIndex 𝔟 1 h𝔟).choose_spec
  have hmem : (exists_isIdealIndex 𝔟 1 h𝔟).choose ∈ fourierDual (𝔟 (idealComponent 1)) :=
    mem_fourierDual_of_isIdealIndex h0
  have hT : HasHilbertFourierExpansion (𝔟 (idealComponent 1))
      (uEigenvalue 𝔭 hf h𝔭 h𝔑𝔭 • f.toFun (idealComponent 1)) fun μ ↦
        ((Ideal.absNorm (𝔭 : Ideal (𝓞 F)) : ℝ) ^ (1 - (m : ℝ) / 2) : ℝ) *
          a ⟨π * μ, mul_mem_fourierDual hπ𝔭 μ.2⟩ := by
    rw [← Pi.smul_apply, ← (hasShimuraHeckeEigenvalue_uEigenvalue 𝔭 hf h𝔭 h𝔑𝔭 :
      (f.shimuraHeckeForm 𝔭).toFun = _), coe_shimuraHeckeForm_toFun 𝔭 f (mk0_eq_one 𝔭 hπ hπ𝔭)]
    exact hasHilbertFourierExpansion_shimuraHeckeOperator hπ𝔭 h𝔭 h𝔑𝔭 hπ hk _ ha
  have h1 : ((Ideal.absNorm (𝔭 : Ideal (𝓞 F)) : ℝ) ^ (1 - (m : ℝ) / 2) : ℝ) *
      a ⟨π * (exists_isIdealIndex 𝔟 1 h𝔟).choose, mul_mem_fourierDual hπ𝔭 hmem⟩ =
        uEigenvalue 𝔭 hf h𝔭 h𝔑𝔭 * a ⟨_, hmem⟩ :=
    congrFun (hT.unique _ (ha.const_smul _ _)) ⟨_, hmem⟩
  have ha1 : a ⟨_, hmem⟩ = 1 := by
    rw [← (hn : f.idealCoeff 1 = 1), idealCoeff, ha.fourierCoeff_eq]
  have hspan1 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (exists_isIdealIndex 𝔟 1 h𝔟).choose *
      ↑(𝔟 (idealComponent 1))⁻¹ * (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) = 1 :=
    h0.2.trans (by simp)
  have hc : idealComponent 𝔭 = idealComponent 1 := by
    rw [idealComponent, idealComponent, mk0_eq_one 𝔭 hπ hπ𝔭, map_one]
  have hspan :
      FractionalIdeal.spanSingleton (𝓞 F)⁰ ((π : F) * (exists_isIdealIndex 𝔟 1 h𝔟).choose) *
        ↑(𝔟 (idealComponent 1))⁻¹ * (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) =
          (𝔭 : Ideal (𝓞 F)) := by
    rw [map_mul, mul_assoc (FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F)),
      mul_assoc (FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F)), hspan1, mul_one, hπ𝔭]
  have hpos : IsTotallyPositive ((π : F) * (exists_isIdealIndex 𝔟 1 h𝔟).choose) := fun w hw ↦ by
    rw [map_mul]
    exact mul_pos (hπ w hw) (h0.1 w hw)
  have hN : (0 : ℝ) < Ideal.absNorm (𝔭 : Ideal (𝓞 F)) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors 𝔭))
  rw [ha1, mul_one] at h1
  rw [idealCoeff_eq_of_eq f hk hc (mul_mem_fourierDual hπ𝔭 hmem) hpos hspan,
    uEigenvalueNormalised, ← h1, ← mul_assoc, ← ofReal_mul, ← Real.rpow_add hN,
    sub_add_sub_cancel', sub_self, Real.rpow_zero, ofReal_one, one_mul, ha.fourierCoeff_eq]

end HilbertModularForm
