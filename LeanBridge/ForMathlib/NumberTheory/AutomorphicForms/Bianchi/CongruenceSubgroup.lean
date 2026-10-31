import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.Level
import Mathlib.Data.Fintype.Parity
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.NumberTheory.NumberField.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Congruence subgroups of Bianchi groups

Let `K` be an imaginary quadratic field with ring of integers `𝒪_K`, and `𝔑` a nonzero ideal of
`𝒪_K`. The **principal congruence subgroup** `Γ(𝔑)` of the Bianchi group `PSL₂(𝒪_K)` is the group
of the `γ ∈ PSL₂(𝒪_K)` with `γ ≡ ±1 (mod 𝔑)`: the image in `PSL₂(𝒪_K)` of the kernel of the
reduction `SL₂(𝒪_K) → SL₂(𝒪_K / 𝔑)`. A **congruence subgroup** of `PSL₂(𝒪_K)` is a subgroup
containing `Γ(𝔑)` for some nonzero `𝔑`. The definitions are made over any commutative ring `R`.

## Main definitions

* `Ideal.gammaSL`: the kernel of the reduction `SL₂(R) → SL₂(R / 𝔑)`.
* `Ideal.gammaPSL` (LMFDB `mf.bianchi.bianchicongruencesubgroup`): the principal congruence
  subgroup `Γ(𝔑)` of `PSL₂(R)`.
* `Subgroup.IsPSLCongruenceSubgroup` (LMFDB `mf.bianchi.bianchicongruencesubgroup`): congruence
  subgroups of `PSL₂(R)`.
* `Ideal.gamma0PSL`: the image in `PSL₂(R)` of the level `Γ₀(𝔑) ∩ SL₂(R)`.

## Main results

* `Ideal.mem_gammaSL_iff`: `g ∈ SL₂(R)` lies in the kernel of the reduction exactly when
  `g ≡ 1 (mod 𝔑)` entrywise.
* `Ideal.mk_mem_gammaPSL_iff`: for a domain `R`, the class of `g ∈ SL₂(R)` lies in `Γ(𝔑)` exactly
  when `g ≡ ±1 (mod 𝔑)`, which is the LMFDB's definition.
* `Ideal.gammaPSL_normal`: `Γ(𝔑)` is a normal subgroup.
* `Ideal.finiteIndex_gammaPSL`: `Γ(𝔑)` has finite index when `R / 𝔑` is finite, as for a nonzero
  ideal of `𝒪_K`.
* `Subgroup.IsPSLCongruenceSubgroup.finiteIndex`: the congruence subgroups of `PSL₂(𝒪_K)` have
  finite index.
* `Ideal.isPSLCongruenceSubgroup_gamma0PSL`: `Γ₀(𝔑)` is a congruence subgroup.
-/

open Matrix NumberField Subgroup

open scoped MatrixGroups

variable {R K : Type*} [CommRing R] [Field K] [NumberField K] (𝔑 : Ideal R) {𝔐 : Ideal R}
  (g : SL(2, R)) (Γ : Subgroup PSL(2, R)) {Γ' : Subgroup PSL(2, R)}

namespace Ideal

/-- The **principal congruence subgroup** of `SL₂(R)` of level `𝔑`: the kernel of the reduction
`SL₂(R) → SL₂(R / 𝔑)` modulo `𝔑`, that is the matrices `g ≡ 1 (mod 𝔑)`
(`Ideal.mem_gammaSL_iff`). -/
def gammaSL : Subgroup SL(2, R) :=
  (SpecialLinearGroup.map (Quotient.mk 𝔑)).ker

lemma mem_gammaSL : g ∈ 𝔑.gammaSL ↔ SpecialLinearGroup.map (Quotient.mk 𝔑) g = 1 :=
  MonoidHom.mem_ker

/-- **`g` lies in the kernel of the reduction modulo `𝔑` exactly when `g ≡ 1 (mod 𝔑)`**: every
entry of `g - 1` lies in `𝔑`. -/
lemma mem_gammaSL_iff : g ∈ 𝔑.gammaSL ↔ ∀ i j, g i j - (1 : Matrix (Fin 2) (Fin 2) R) i j ∈ 𝔑 := by
  refine (mem_gammaSL 𝔑 g).trans <| (SpecialLinearGroup.ext_iff _ _).trans <|
    forall₂_congr fun i j ↦ ?_
  rw [← Quotient.eq]
  by_cases h : i = j <;> simp [one_apply, h]

/-- The **principal congruence subgroup** `Γ(𝔑)` (LMFDB `mf.bianchi.bianchicongruencesubgroup`) of
`PSL₂(R)` of level `𝔑`: the image in `PSL₂(R) = SL₂(R) / Z(SL₂(R))` of the kernel of the reduction
`SL₂(R) → SL₂(R / 𝔑)`. For a domain `R`, such as the ring of integers `𝒪_K` of an imaginary
quadratic field, whose `SL₂` has centre `{±1}`, it is the group of the `γ ∈ PSL₂(R)` with
`γ ≡ ±1 (mod 𝔑)` (`Ideal.mk_mem_gammaPSL_iff`). The LMFDB takes `𝔑` nonzero. -/
def gammaPSL : Subgroup PSL(2, R) :=
  𝔑.gammaSL.map (QuotientGroup.mk' _)

lemma map_neg_eq_neg : SpecialLinearGroup.map (Quotient.mk 𝔑) (-g) =
    -SpecialLinearGroup.map (Quotient.mk 𝔑) g :=
  Subtype.ext <| (Quotient.mk 𝔑).mapMatrix.map_neg (g : Matrix (Fin 2) (Fin 2) R)

/-- **The principal congruence subgroup `Γ(𝔑)` is `{γ ≡ ±1 (mod 𝔑)}`**: for a domain `R`, the class
in `PSL₂(R)` of `g ∈ SL₂(R)` lies in `Γ(𝔑)` exactly when `g ≡ 1` or `g ≡ -1` modulo `𝔑`. -/
lemma mk_mem_gammaPSL_iff [IsDomain R] : (QuotientGroup.mk g : PSL(2, R)) ∈ 𝔑.gammaPSL ↔
    SpecialLinearGroup.map (Quotient.mk 𝔑) g = 1 ∨
      SpecialLinearGroup.map (Quotient.mk 𝔑) g = -1 := by
  refine ⟨fun ⟨h, hh, hhg⟩ ↦ ?_, fun hg ↦ ?_⟩
  · rcases SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp (QuotientGroup.eq.mp hhg) with
      h₁ | h₁
    · left
      rw [← mul_inv_cancel_left h g, h₁, mul_one]
      exact hh
    · right
      rw [← mul_inv_cancel_left h g, h₁, mul_neg_one, map_neg_eq_neg, (mem_gammaSL 𝔑 h).mp hh]
  · rcases hg with hg | hg
    · exact ⟨g, hg, rfl⟩
    · refine ⟨-g, (mem_gammaSL 𝔑 (-g)).mpr ?_, QuotientGroup.eq.mpr ?_⟩
      · rw [map_neg_eq_neg, hg, neg_neg]
      · rw [inv_neg, neg_mul, inv_mul_cancel]
        exact SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mpr (Or.inr rfl)

/-- **`Γ(𝔑)` is normal** in `PSL₂(R)`, as the image of the kernel of the reduction modulo `𝔑`. -/
lemma gammaPSL_normal : 𝔑.gammaPSL.Normal :=
  (SpecialLinearGroup.map (Quotient.mk 𝔑)).normal_ker.map _ (QuotientGroup.mk'_surjective _)

/-- **`Γ(𝔑)` has finite index** in `PSL₂(R)` when `R / 𝔑` is finite, as for a nonzero ideal of the
ring of integers of a number field: the kernel of the reduction `SL₂(R) → SL₂(R / 𝔑)` has finite
index. -/
lemma finiteIndex_gammaPSL [Finite (R ⧸ 𝔑)] : 𝔑.gammaPSL.FiniteIndex :=
  have : 𝔑.gammaSL.FiniteIndex := Subgroup.finiteIndex_ker _
  FiniteIndex.map_of_surjective _ (QuotientGroup.mk'_surjective _)

lemma gammaPSL_mono (h : 𝔐 ≤ 𝔑) : 𝔐.gammaPSL ≤ 𝔑.gammaPSL :=
  Subgroup.map_mono fun g hg ↦ (mem_gammaSL_iff 𝔑 g).mpr fun i j ↦
    h <| (mem_gammaSL_iff 𝔐 g).mp hg i j

lemma gammaPSL_top : (⊤ : Ideal R).gammaPSL = ⊤ := by
  have h : (⊤ : Ideal R).gammaSL = ⊤ :=
    eq_top_iff.mpr fun g _ ↦ (mem_gammaSL_iff ⊤ g).mpr fun _ _ ↦ Submodule.mem_top
  rw [gammaPSL, h]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

/-- The image `Γ₀(𝔑)` in `PSL₂(R)` of the `SL₂`-level `Γ₀(𝔑) ∩ SL₂(R)` (`Ideal.gamma0SL`, LMFDB
`mf.bianchi.level`): the classes of the matrices `(a, b; c, d)` of `SL₂(R)` with `c ∈ 𝔑`. -/
def gamma0PSL : Subgroup PSL(2, R) :=
  𝔑.gamma0SL.map (QuotientGroup.mk' _)

lemma gammaSL_le_gamma0SL : 𝔑.gammaSL ≤ 𝔑.gamma0SL :=
  fun g hg ↦ (mem_gamma0SL 𝔑).mpr <| by simpa using (mem_gammaSL_iff 𝔑 g).mp hg 1 0

lemma gammaPSL_le_gamma0PSL : 𝔑.gammaPSL ≤ 𝔑.gamma0PSL :=
  Subgroup.map_mono (gammaSL_le_gamma0SL 𝔑)

end Ideal

namespace Subgroup

/-- A subgroup `Γ` of `PSL₂(R)` is a **congruence subgroup** (LMFDB
`mf.bianchi.bianchicongruencesubgroup`) if it contains the principal congruence subgroup `Γ(𝔑)`
(`Ideal.gammaPSL`) of some nonzero ideal `𝔑` of `R`. For `R = 𝒪_K`, `K` imaginary quadratic, these
are the congruence subgroups of the Bianchi group `PSL₂(𝒪_K)`; they have finite index
(`Subgroup.IsPSLCongruenceSubgroup.finiteIndex`). -/
def IsPSLCongruenceSubgroup : Prop :=
  ∃ 𝔞 : Ideal R, 𝔞 ≠ ⊥ ∧ 𝔞.gammaPSL ≤ Γ

variable {Γ} in
lemma IsPSLCongruenceSubgroup.mono (hΓ : Γ.IsPSLCongruenceSubgroup) (h : Γ ≤ Γ') :
    Γ'.IsPSLCongruenceSubgroup := by
  rcases hΓ with ⟨𝔞, h𝔞, hle⟩
  exact ⟨𝔞, h𝔞, hle.trans h⟩

/-- **The congruence subgroups of `PSL₂(𝒪_K)` have finite index**, as `𝒪_K / 𝔑` is finite for every
nonzero ideal `𝔑` of the ring of integers `𝒪_K` of a number field `K`. -/
lemma IsPSLCongruenceSubgroup.finiteIndex {Δ : Subgroup PSL(2, 𝓞 K)}
    (hΔ : Δ.IsPSLCongruenceSubgroup) : Δ.FiniteIndex := by
  rcases hΔ with ⟨𝔞, h𝔞, hle⟩
  have h₁ : Finite (𝓞 K ⧸ 𝔞) := Ideal.finiteQuotientOfFreeOfNeBot 𝔞 h𝔞
  have h₂ : 𝔞.gammaPSL.FiniteIndex := 𝔞.finiteIndex_gammaPSL
  exact finiteIndex_of_le hle

end Subgroup

namespace Ideal

variable {𝔑}

/-- **`Γ₀(𝔑)` is a congruence subgroup** of `PSL₂(R)` for a nonzero ideal `𝔑`, as it contains
`Γ(𝔑)`. -/
lemma isPSLCongruenceSubgroup_gamma0PSL (h𝔑 : 𝔑 ≠ ⊥) : 𝔑.gamma0PSL.IsPSLCongruenceSubgroup :=
  ⟨𝔑, h𝔑, 𝔑.gammaPSL_le_gamma0PSL⟩

lemma isPSLCongruenceSubgroup_gammaPSL (h𝔑 : 𝔑 ≠ ⊥) : 𝔑.gammaPSL.IsPSLCongruenceSubgroup :=
  ⟨𝔑, h𝔑, le_rfl⟩

end Ideal
