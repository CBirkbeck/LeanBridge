import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Normed.Algebra.NoSmallSubgroups

/-!
# Artin representations

An Artin representation is a continuous representation of the absolute Galois group of `ℚ` on a
finite-dimensional complex vector space. Continuity means that the kernel is open, equivalently that
the representation factors through the Galois group of a finite Galois extension, or that it is
continuous for the usual topology of the general linear group. The fixed field of the kernel, the
Artin field, is the smallest such extension.

The definitions make sense over any field `K` (the LMFDB takes `K = ℚ`); the results assume that
`K` has characteristic zero, so that its algebraic closure is a Galois extension and the Galois
correspondence for open subgroups applies.

## Main definitions

* `Representation.IsArtin` (LMFDB `artin`): Artin representations.
* `Representation.artinField` (LMFDB `artin`): the Artin field of a representation.

## Main results

* `Representation.isArtin_iff_exists_finiteGaloisIntermediateField`: a representation on a
  finite-dimensional space is an Artin representation if and only if it factors through the Galois
  group of a finite Galois extension.
* `Representation.isArtin_iff_continuous`: a representation on a finite-dimensional normed space
  is an Artin representation if and only if it is continuous for the norm topology.
* `Representation.IsArtin.fixingSubgroup_artinField`, `Representation.IsArtin.finiteDimensional`
  and `Representation.IsArtin.isGalois`: an Artin representation factors through the Galois group
  of its Artin field, which is a finite Galois extension.
* `Representation.IsArtin.artinField_le_iff`: the Artin field is the smallest extension through
  whose Galois group an Artin representation factors.
-/

open IntermediateField

namespace Representation

variable {K V : Type*} [Field K] [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ Gal(AlgebraicClosure K/K) V)

/-- A representation `ρ` of the absolute Galois group `Gal(K̄/K)` of a field `K` (Mathlib's
`Field.absoluteGaloisGroup K`) on a complex vector space `V` is an **Artin representation** (LMFDB
`artin`, where `K = ℚ`) if `V` is finite-dimensional and `ρ` is continuous, which means that its
kernel is open in the Krull topology: equivalently, `ρ` factors through the Galois group of a
finite Galois extension of `K` (`Representation.isArtin_iff_exists_finiteGaloisIntermediateField`).
-/
structure IsArtin : Prop where
  /-- An Artin representation is finite-dimensional. -/
  finiteDimensional_space : FiniteDimensional ℂ V
  /-- An Artin representation is continuous: its kernel is open. -/
  isOpen_ker : IsOpen (ρ.ker : Set Gal(AlgebraicClosure K/K))

/-- The **Artin field** of a representation `ρ` of `Gal(K̄/K)` (LMFDB `artin`): the subfield of
`K̄` fixed by the kernel of `ρ`. For an Artin representation, it is the smallest extension of `K`
in `K̄` through whose Galois group `ρ` factors (`Representation.IsArtin.artinField_le_iff`). -/
noncomputable def artinField : IntermediateField K (AlgebraicClosure K) :=
  fixedField ρ.ker

variable {ρ} [CharZero K]

/-- **An Artin representation is a representation factoring through a finite Galois quotient**:
a representation on a finite-dimensional space is an Artin representation if and only if it is
trivial on `Gal(K̄/L)` for a finite Galois extension `L` of `K`. -/
lemma isArtin_iff_exists_finiteGaloisIntermediateField : ρ.IsArtin ↔ FiniteDimensional ℂ V ∧ ∃ L :
    FiniteGaloisIntermediateField K (AlgebraicClosure K), L.fixingSubgroup ≤ ρ.ker := by
  refine ⟨fun h ↦ ⟨h.1, ?_⟩, fun ⟨hV, L, hL⟩ ↦ ⟨hV, Subgroup.isOpen_mono hL ?_⟩⟩
  · exact (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois _).mp
      (h.2.mem_nhds ρ.ker.one_mem)
  · exact L.fixingSubgroup_isOpen

/-- **An Artin representation is a continuous homomorphism to `GL(W)`**: a representation `π` on a
finite-dimensional normed space `W` is an Artin representation if and only if `σ ↦ π(σ)` is
continuous for the norm topology on the endomorphisms of `W`, since the profinite group `Gal(K̄/K)`
has arbitrarily small open subgroups, while `GL(W)` has no small subgroups. -/
lemma isArtin_iff_continuous {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (π : Representation ℂ Gal(AlgebraicClosure K/K) W) :
    π.IsArtin ↔ Continuous fun σ ↦ LinearMap.toContinuousLinearMap (π σ) := by
  refine ⟨fun h ↦ continuous_iff_continuousAt.mpr fun σ ↦ ?_, fun h ↦ ⟨inferInstance, ?_⟩⟩
  · refine (continuousAt_const (y := LinearMap.toContinuousLinearMap (π σ))).congr
      (Filter.eventuallyEq_of_mem ((h.isOpen_ker.smul σ).mem_nhds ⟨1, π.ker.one_mem, mul_one σ⟩) ?_)
    rintro _ ⟨k, hk, rfl⟩
    dsimp only
    rw [smul_eq_mul, map_mul, MonoidHom.mem_ker.mp hk, mul_one]
  · let f : Gal(AlgebraicClosure K/K) →* (W →L[ℂ] W) :=
      { toFun σ := LinearMap.toContinuousLinearMap (π σ)
        map_one' := by
          ext
          simp
        map_mul' σ τ := by
          ext
          simp }
    have : NormSMulClass ℤ (W →L[ℂ] W) :=
      ⟨fun n a ↦ by simpa only [Int.norm_cast_real] using norm_zsmul ℝ n a⟩
    have hF : Continuous f.toHomUnits := by
      refine Units.continuous_iff.mpr ⟨h, ?_⟩
      have heq : (fun σ ↦ ((f.toHomUnits σ)⁻¹ : (W →L[ℂ] W)ˣ).val) = (fun σ ↦
          LinearMap.toContinuousLinearMap (π σ)) ∘ fun σ ↦ σ⁻¹ := by
        funext σ
        rw [← map_inv, MonoidHom.coe_toHomUnits]
        rfl
      exact heq ▸ h.comp continuous_inv
    have hker : (⟨f.toHomUnits, hF⟩ : Gal(AlgebraicClosure K/K) →ₜ* (W →L[ℂ] W)ˣ).ker = π.ker := by
      have h1 : LinearMap.toContinuousLinearMap (1 : W →ₗ[ℂ] W) = 1 := by
        ext
        simp
      ext σ
      simp [f, ← h1]
    exact hker ▸ ContinuousMonoidHom.isOpen_ker_of_compactSpace_of_totallyDisconnectedSpace _

namespace IsArtin

variable (h : ρ.IsArtin)

include h

/-- **An Artin representation factors through the Galois group of its Artin field**: the subgroup
fixing the Artin field is the kernel. -/
lemma fixingSubgroup_artinField : ρ.artinField.fixingSubgroup = ρ.ker :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨ρ.ker, ρ.ker.isClosed_of_isOpen h.isOpen_ker⟩

/-- **The Artin field of an Artin representation is a finite extension.** -/
lemma finiteDimensional : FiniteDimensional K ρ.artinField :=
  (InfiniteGalois.isOpen_iff_finite _).mp <| h.fixingSubgroup_artinField ▸ h.isOpen_ker

/-- **The Artin field of an Artin representation is a Galois extension.** -/
lemma isGalois : IsGalois K ρ.artinField :=
  (InfiniteGalois.normal_iff_isGalois _).mp <| h.fixingSubgroup_artinField ▸ ρ.normal_ker

/-- **The Artin field is the smallest field through whose Galois group an Artin representation
factors**: `ρ` is trivial on `Gal(K̄/L)` if and only if `L` contains the Artin field of `ρ`. -/
lemma artinField_le_iff (L : IntermediateField K (AlgebraicClosure K)) :
    ρ.artinField ≤ L ↔ L.fixingSubgroup ≤ ρ.ker := by
  refine ⟨fun hL ↦ ?_, fun hL ↦ ?_⟩
  · exact h.fixingSubgroup_artinField ▸ fixingSubgroup_antitone hL
  · exact InfiniteGalois.fixedField_fixingSubgroup L ▸ fixedField_antitone hL

end IsArtin

end Representation
