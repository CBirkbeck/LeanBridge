import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RepresentationTheory.Character
import TauCeti.LinearAlgebra.End.FiniteOrder

/-!
# The character criterion for faithfulness in characteristic zero

A representation `ρ` of a finite group `G` on a finite-dimensional vector space over a field of
characteristic `0` is faithful exactly when its character `χ` satisfies `χ(g) = χ(1) → g = 1`
(LMFDB `group.representation.faithful`). Tau Ceti proves this over `ℂ`
(`FDRep.ker_eq_bot_iff`); here it is proved over every field `k` of characteristic `0`.

The key step is that an endomorphism `f` with `fⁿ = 1` and trace `dim V` is the identity. Over an
algebraically closed field `K` of characteristic `0`, `f` is diagonalizable with eigenvalues `μ`
that are `n`-th roots of unity, and `∑ dim(V_μ) (1 - μ) = 0`. The eigenvalues generate an algebraic
extension of `ℚ`, which embeds into `ℂ`; there each `1 - μ` has nonnegative real part, vanishing
only for `μ = 1`, so every eigenvalue is `1` and `f = 1`. Over an arbitrary field `k` of
characteristic `0` the matrix of `f` is mapped to the algebraic closure of `k`.

## Main results

* `Module.End.eq_one_of_trace_eq_finrank_of_charZero`: over a field of characteristic `0`, an
  endomorphism of finite order whose trace is the dimension is the identity.
* `Representation.injective_iff_character_eq_character_one` (LMFDB
  `group.representation.faithful`): a representation of a finite group over a field of
  characteristic `0` is faithful exactly when `χ(g) = χ(1)` implies `g = 1`.
-/

open Module End

namespace Module.End

variable {K W : Type*} [Field K] [CharZero K] [IsAlgClosed K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {f : End K W} {n : ℕ}

lemma eq_one_of_hasEigenvalue_of_trace_eq_finrank (hn : n ≠ 0) (hf : f ^ n = 1)
    (htr : LinearMap.trace K W f = finrank K W) {μ : K} (hμ : f.HasEigenvalue μ) : μ = 1 := by
  classical
  have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h1 : LinearMap.trace K W (f ^ 1) =
      ∑ ν ∈ f.finite_hasEigenvalue.toFinset, (finrank K (f.eigenspace ν) : K) * ν ^ 1 :=
    trace_pow_eq_sum_eigenvalue_pow hn' hf 1
  have h0 : LinearMap.trace K W (f ^ 0) =
      ∑ ν ∈ f.finite_hasEigenvalue.toFinset, (finrank K (f.eigenspace ν) : K) * ν ^ 0 :=
    trace_pow_eq_sum_eigenvalue_pow hn' hf 0
  rw [pow_one, htr] at h1
  rw [pow_zero, LinearMap.trace_one] at h0
  have hmemT {ν : K} : ν ∈ f.finite_hasEigenvalue.toFinset ↔ f.HasEigenvalue ν :=
    Set.Finite.mem_toFinset _
  have hint (ν : K) (hν : ν ∈ (f.finite_hasEigenvalue.toFinset : Set K)) : IsIntegral ℚ ν := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
    rw [pow_eq_one_of_hasEigenvalue hf (hmemT.mp hν)]
    exact isIntegral_one
  let L : IntermediateField ℚ K :=
    IntermediateField.adjoin ℚ (f.finite_hasEigenvalue.toFinset : Set K)
  have : Algebra.IsAlgebraic ℚ L := IntermediateField.isAlgebraic_adjoin hint
  let φ : L →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hmem (ν : f.finite_hasEigenvalue.toFinset) : (ν : K) ∈ L :=
    IntermediateField.subset_adjoin ℚ _ ν.2
  have hsum : ∑ ν ∈ f.finite_hasEigenvalue.toFinset.attach,
      (finrank K (f.eigenspace ν) : L) * (1 - ⟨ν, hmem ν⟩) = 0 := by
    refine Subtype.ext ?_
    push_cast
    rw [Finset.sum_attach f.finite_hasEigenvalue.toFinset
      fun ν ↦ (finrank K (f.eigenspace ν) : K) * (1 - ν)]
    simp only [pow_one, pow_zero, mul_one] at h0 h1
    rw [Finset.sum_congr rfl fun ν _ ↦ mul_sub _ (1 : K) ν, Finset.sum_sub_distrib]
    simp only [mul_one]
    rw [← h0, ← h1, sub_self]
  have hsumC : ∑ ν ∈ f.finite_hasEigenvalue.toFinset.attach,
      (finrank K (f.eigenspace ν) : ℂ) * (1 - φ ⟨ν, hmem ν⟩) = 0 := by
    simpa using congrArg φ hsum
  have hnorm (ν : f.finite_hasEigenvalue.toFinset) : ‖φ ⟨ν, hmem ν⟩‖ = 1 := by
    refine Complex.norm_eq_one_of_pow_eq_one ?_ hn
    rw [← map_pow, ← map_one φ]
    exact congrArg φ <| Subtype.ext <| pow_eq_one_of_hasEigenvalue hf (hmemT.mp ν.2)
  have hnonneg : ∀ ν ∈ f.finite_hasEigenvalue.toFinset.attach,
      0 ≤ ((finrank K (f.eigenspace ν) : ℂ) * (1 - φ ⟨ν, hmem ν⟩)).re := fun ν _ ↦ by
    simpa using mul_nonneg (Nat.cast_nonneg (finrank K (f.eigenspace ν)))
      (sub_nonneg.mpr ((Complex.re_le_norm _).trans (hnorm ν).le))
  have hre : ∑ ν ∈ f.finite_hasEigenvalue.toFinset.attach,
      ((finrank K (f.eigenspace ν) : ℂ) * (1 - φ ⟨ν, hmem ν⟩)).re = 0 := by
    rw [← Complex.re_sum, hsumC, Complex.zero_re]
  have hzero : ((finrank K (f.eigenspace μ) : ℂ) * (1 - φ ⟨μ, hmem ⟨μ, hmemT.mpr hμ⟩⟩)).re = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hre ⟨μ, hmemT.mpr hμ⟩ (Finset.mem_attach _ _)
  have hd : finrank K (f.eigenspace μ) ≠ 0 := fun h ↦
    hasEigenvalue_iff.mp hμ (Submodule.finrank_eq_zero.mp h)
  have hz : ‖φ ⟨μ, hmem ⟨μ, hmemT.mpr hμ⟩⟩‖ = 1 := hnorm ⟨μ, hmemT.mpr hμ⟩
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
    Complex.sub_re, Complex.one_re] at hzero
  have hre1 : (φ ⟨μ, hmem ⟨μ, hmemT.mpr hμ⟩⟩).re = 1 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd (Nat.cast_eq_zero.mp h) hd
    · linarith
  have him : (φ ⟨μ, hmem ⟨μ, hmemT.mpr hμ⟩⟩).im = 0 := by
    have h2 :
        ‖φ ⟨μ, hmem ⟨μ, hmemT.mpr hμ⟩⟩‖ ^ 2 = Complex.normSq (φ ⟨μ, hmem ⟨μ, hmemT.mpr hμ⟩⟩) :=
      Complex.sq_norm _
    rw [hz, Complex.normSq_apply, hre1] at h2
    nlinarith
  exact congrArg Subtype.val <| φ.injective <| (Complex.ext hre1 him).trans (map_one φ).symm

lemma eq_one_of_trace_eq_finrank_of_isAlgClosed (hn : n ≠ 0) (hf : f ^ n = 1)
    (htr : LinearMap.trace K W f = finrank K W) : f = 1 := by
  have htop : ⨆ μ, f.eigenspace μ = ⊤ :=
    (isSemisimple_of_pow_eq_one (Nat.cast_ne_zero.mpr hn) hf).iSup_eigenspace_eq_top
  have h1 : f.eigenspace 1 = ⊤ := eq_top_iff.mpr <| htop.ge.trans <| iSup_le fun μ ↦ by
    by_cases hμ : f.HasEigenvalue μ
    · rw [eq_one_of_hasEigenvalue_of_trace_eq_finrank hn hf htr hμ]
    · rw [hasEigenvalue_iff, not_not] at hμ
      rw [hμ]
      exact bot_le
  ext x
  simpa using mem_eigenspace_iff.mp (h1 ▸ Submodule.mem_top : x ∈ f.eigenspace 1)

variable {k V : Type*} [Field k] [CharZero k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- **An endomorphism of finite order whose trace is the dimension is the identity**, over any
field of characteristic `0`: its matrix, mapped to the algebraic closure, is the identity there. -/
lemma eq_one_of_trace_eq_finrank_of_charZero {g : End k V} (hn : n ≠ 0) (hg : g ^ n = 1)
    (htr : LinearMap.trace k V g = finrank k V) : g = 1 := by
  let b : Basis (Fin (finrank k V)) k V := Module.finBasis k V
  let M : Matrix (Fin (finrank k V)) (Fin (finrank k V)) k := LinearMap.toMatrixAlgEquiv b g
  let MK : Matrix (Fin (finrank k V)) (Fin (finrank k V)) (AlgebraicClosure k) :=
    (algebraMap k (AlgebraicClosure k)).mapMatrix M
  have hMK : Matrix.toLinAlgEquiv' MK ^ n = 1 := by
    rw [← map_pow, ← map_pow, ← map_pow, hg, map_one, map_one, map_one]
  have htrK : LinearMap.trace (AlgebraicClosure k) _ (Matrix.toLinAlgEquiv' MK) =
      finrank (AlgebraicClosure k) (Fin (finrank k V) → AlgebraicClosure k) := by
    rw [Module.finrank_fin_fun, ← map_natCast (algebraMap k (AlgebraicClosure k)), ← htr,
      LinearMap.trace_eq_matrix_trace k b g, AddMonoidHom.map_trace]
    exact Matrix.trace_toLin'_eq MK
  have hM : MK = 1 := Matrix.toLinAlgEquiv'.injective <|
    (eq_one_of_trace_eq_finrank_of_isAlgClosed hn hMK htrK).trans (map_one _).symm
  have hM' : M = 1 := Matrix.map_injective (algebraMap k (AlgebraicClosure k)).injective <|
    hM.trans (Matrix.map_one _ (map_zero _) (map_one _)).symm
  exact (LinearMap.toMatrixAlgEquiv b).injective <| hM'.trans (map_one _).symm

end Module.End

namespace Representation

variable {k G V : Type*} [Field k] [CharZero k] [Group G] [Finite G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] (ρ : Representation k G V)

/-- **The character criterion for faithfulness in characteristic zero** (LMFDB
`group.representation.faithful`): a representation `ρ` of a finite group on a finite-dimensional
vector space over a field of characteristic `0` is faithful, that is injective, exactly when its
character `χ` satisfies `χ(g) = χ(1) → g = 1`. -/
lemma injective_iff_character_eq_character_one :
    Function.Injective ρ ↔ ∀ g : G, ρ.character g = ρ.character 1 → g = 1 := by
  rw [injective_iff_map_eq_one]
  refine forall_congr' fun g ↦ imp_congr_left ⟨fun h ↦ by simp [character, h], fun h ↦ ?_⟩
  rw [char_one] at h
  exact eq_one_of_trace_eq_finrank_of_charZero (orderOf_pos g).ne'
    (by rw [← map_pow, pow_orderOf_eq_one, map_one]) h

end Representation
