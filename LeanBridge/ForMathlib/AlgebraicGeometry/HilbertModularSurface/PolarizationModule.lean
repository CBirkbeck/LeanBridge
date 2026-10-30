import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Basic

/-!
# Isomorphisms of polarization modules with fractional ideals

Let `F` be a totally real number field and `(A, ι)` an abelian variety with real multiplication by
`ι : 𝒪_F → End(A_{ℚ̄})`. Its **polarization module** (LMFDB `hmsurface.polarization_module`) is the
`𝒪_F`-module `PM(A) = {λ ∈ Hom_{𝒪_F}(A, A^∨) : λ = λ^∨} ⊆ NS(A)` of the symmetric `𝒪_F`-linear
homomorphisms from `A` to its dual abelian variety, and its **polarization cone** `PM⁺(A) ⊆ PM(A)`
is the set of polarizations, which equips `PM(A)` with a notion of positivity. Dual abelian
varieties, polarizations and Néron–Severi groups are not available (Tau Ceti has abelian varieties
and their endomorphisms, but not their duals), so neither notion is formalised here.

The knowl says that the polarization module is **isomorphic** to a fractional ideal `J` of `F` if
there is an orientation preserving isomorphism of `𝒪_F`-modules `φ : PM(A) → J`, that is, one with
`φ(PM⁺(A)) = J⁺`, the totally positive elements of `J`. This is formalised for any `𝒪_F`-module `P`
with a subset `P⁺`, in the roles of `PM(A)` and `PM⁺(A)`. The fractional ideal `𝒪_F`, with the
totally positive integers, is isomorphic in this sense to `J` exactly when the narrow ideal class
of `J` is trivial: this is how the narrow class group enters the moduli interpretation of Hilbert
modular surfaces (LMFDB `hmsurface.component_ideal`), a principal polarization generating the
polarization module.

The definitions make sense for any field `F`, `𝒪_F` being the integral closure of `ℤ` in `F`.

## Main definitions

* `FractionalIdeal.totallyPositivePart`: the totally positive elements `J⁺` of a fractional ideal.
* `FractionalIdeal.IsOrientedIsomorphic` (LMFDB `hmsurface.polarization_module`): an `𝒪_F`-module
  with a positive cone is isomorphic to a fractional ideal.

## Main results

* `FractionalIdeal.isOrientedIsomorphic_iff_mk_eq_one`: a fractional ideal is isomorphic to `𝒪_F`
  exactly when its narrow ideal class is trivial.
-/

open NumberField

open scoped nonZeroDivisors

namespace FractionalIdeal

variable {F : Type*} [Field F] (J : FractionalIdeal (𝓞 F)⁰ F) {P : Type*} [AddCommGroup P]
  [Module (𝓞 F) P]

/-- The **totally positive elements** `J⁺` of a fractional ideal `J` of a field `F`, which is
totally real for the LMFDB: the elements of `J` that are positive at every real place of `F`. -/
def totallyPositivePart : Set J :=
  {x | IsTotallyPositive (x : F)}

/-- An `𝒪_F`-module `P` with a subset `P⁺`, such as the polarization module `PM(A)` of an abelian
variety with real multiplication by `𝒪_F` and its polarization cone `PM⁺(A)`, is **isomorphic**
(LMFDB `hmsurface.polarization_module`) to a fractional ideal `J` if there is an orientation
preserving isomorphism of `𝒪_F`-modules `φ : P → J`, that is, one with `φ(P⁺) = J⁺`. -/
def IsOrientedIsomorphic (Pplus : Set P) : Prop :=
  ∃ φ : P ≃ₗ[𝓞 F] J, φ '' Pplus = J.totallyPositivePart

variable [NumberField F]

/-- **A fractional ideal `J` is isomorphic to `𝒪_F`, with the totally positive integers as
positive cone, if and only if its narrow ideal class is trivial**: an orientation preserving
isomorphism `𝒪_F → J` is the multiplication by a totally positive generator of `J`. -/
lemma isOrientedIsomorphic_iff_mk_eq_one (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    I.val.IsOrientedIsomorphic {x : 𝓞 F | IsTotallyPositive (x : F)} ↔
      NarrowClassGroup.mk I = 1 := by
  rw [NarrowClassGroup.mk_eq_one_iff, mem_narrowPrincipalSubgroup]
  constructor
  · rintro ⟨φ, hφ⟩
    have h₁ : φ 1 ∈ I.val.totallyPositivePart := hφ ▸ ⟨1, by simp, rfl⟩
    have h₀ : (φ 1 : F) ≠ 0 := fun h ↦ one_ne_zero <| φ.injective <|
      (Subtype.ext h).trans φ.map_zero.symm
    have hI : I.val = spanSingleton (𝓞 F)⁰ (φ 1 : F) := by
      refine le_antisymm (fun y hy ↦ (mem_spanSingleton _).mpr ⟨φ.symm ⟨y, hy⟩, ?_⟩) <|
        spanSingleton_le_iff_mem.mpr (φ 1).2
      have h : φ (φ.symm ⟨y, hy⟩ • 1) = ⟨y, hy⟩ := by
        rw [smul_eq_mul, mul_one, φ.apply_symm_apply]
      rw [φ.map_smul] at h
      exact congrArg Subtype.val h
    exact ⟨Units.mk0 _ h₀, h₁, Units.ext <| (coe_toPrincipalIdeal _).trans hI.symm⟩
  · rintro ⟨x, hx, rfl⟩
    rw [coe_toPrincipalIdeal]
    let φ : 𝓞 F →ₗ[𝓞 F] spanSingleton (𝓞 F)⁰ (x : F) :=
      LinearMap.toSpanSingleton (𝓞 F) _ ⟨x, mem_spanSingleton_self _ _⟩
    have hφ : Function.Bijective φ := by
      refine ⟨(injective_iff_map_eq_zero φ).mpr fun r hr ↦ ?_, fun y ↦ ?_⟩
      · have h : algebraMap (𝓞 F) F r * x = 0 := (Algebra.smul_def r (x : F)).symm.trans <|
          congrArg Subtype.val hr
        exact (injective_iff_map_eq_zero _).mp (IsFractionRing.injective (𝓞 F) F) r <|
          (mul_eq_zero.mp h).resolve_right x.ne_zero
      · rcases (mem_spanSingleton _).mp y.2 with ⟨r, hr⟩
        exact ⟨r, Subtype.ext hr⟩
    refine ⟨LinearEquiv.ofBijective φ hφ, ?_⟩
    ext ⟨y, hy⟩
    refine ⟨?_, fun h ↦ ?_⟩
    · rintro ⟨r, hr, h⟩
      have h' : (r : F) * x = y := (Algebra.smul_def r (x : F)).symm.trans <| congrArg Subtype.val h
      exact h' ▸ hr.mul hx
    · rcases (mem_spanSingleton _).mp hy with ⟨r, hr⟩
      have h' : (r : F) = y * (x : F)⁻¹ := by
        rw [← hr, Algebra.smul_def, mul_inv_cancel_right₀ x.ne_zero]
      exact ⟨r, (h' ▸ h.mul hx.inv : IsTotallyPositive (r : F)), Subtype.ext hr⟩

end FractionalIdeal
