import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RepresentationTheory.Irreducible

/-!
# Permutation representations containing an irreducible representation

A representation `ρ` contains a representation `σ` if `σ` is isomorphic to a subrepresentation of
`ρ`. A complex representation of a finite group is a direct sum of irreducible representations, and
an irreducible representation is contained in it exactly when it occurs in such a decomposition.

The permutation representation `k[G ⧸ H]` contains an irreducible representation `σ` exactly when
`σ` has a nonzero `H`-invariant linear form (Frobenius reciprocity). For `H = ⊥` this is the regular
representation, which therefore contains every irreducible representation of a finite group, so
that there is a smallest degree of a transitive permutation representation containing it.

## Main definitions

* `Representation.Contains` (LMFDB `artin.permutation_container`).
* `Representation.minPermutationDegree` (LMFDB `artin.permutation_container`): the smallest degree
  of a permutation representation containing an irreducible representation.

## Main results

* `Representation.contains_ofMulAction_quotient_iff`: the permutation representation `k[G ⧸ H]`
  contains an irreducible representation `σ` exactly when `σ` has a nonzero `H`-invariant linear
  form.
* `Representation.contains_ofMulAction_quotient_bot`: the regular representation `k[G ⧸ ⊥]` of a
  finite group contains every irreducible representation.
* `Representation.exists_index_eq_minPermutationDegree`: the smallest degree is the index of a
  subgroup `H` such that `k[G ⧸ H]` contains the representation.
-/

open MonoidAlgebra Module

namespace Representation

variable {k G V W : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W] (ρ : Representation k G V) (σ : Representation k G W) (H : Subgroup G)

/-- A representation `ρ` **contains** a representation `σ` (LMFDB `artin.permutation_container`)
if `σ` is isomorphic to a subrepresentation of `ρ`, that is, if there is an injective intertwining
map from `σ` to `ρ`. For an irreducible `σ`, a nonzero intertwining map suffices
(`Representation.contains_iff_exists_ne_zero`). For a representation of a finite group in
characteristic zero, which is a direct sum of irreducible representations by Maschke's theorem,
this says that `σ` is a direct summand of `ρ`; for an irreducible `σ`, that it occurs in a
decomposition of `ρ` into irreducible representations, as in the LMFDB. -/
def Contains : Prop :=
  ∃ f : IntertwiningMap σ ρ, Function.Injective f

/-- The **smallest degree of a permutation representation containing `σ`** (LMFDB
`artin.permutation_container`): the least index of a subgroup `H` of finite index such that the
permutation representation `k[G ⧸ H]` contains `σ`, or `0` if there is none.

A permutation representation `k[X]` of a finite `G`-set `X` is the direct sum of the transitive ones
`k[G ⧸ H]` given by its orbits, so an irreducible representation contained in `k[X]` is contained
in one of these, of smaller degree: the least degree of a permutation representation containing an
irreducible `σ` is attained by a transitive one. For a finite group it exists and is at most `|G|`
(`Representation.contains_ofMulAction_quotient_bot`). Among the subgroups attaining it, the LMFDB
chooses one whose image in the symmetric group has the smallest T-number, a database ordering not
formalised here. -/
noncomputable def minPermutationDegree : ℕ :=
  sInf {n | ∃ H : Subgroup G, H.FiniteIndex ∧ H.index = n ∧ (ofMulAction k G (G ⧸ H)).Contains σ}

variable {ρ σ} [H.FiniteIndex]

lemma minPermutationDegree_le_index (h : (ofMulAction k G (G ⧸ H)).Contains σ) :
    σ.minPermutationDegree ≤ H.index :=
  Nat.sInf_le ⟨H, ‹_›, rfl, h⟩

variable [σ.IsIrreducible]

variable (σ) in
include σ in
private lemma exists_ne_zero_of_isIrreducible : ∃ w : W, w ≠ 0 := by
  have : Nontrivial W := IsSimpleModule.nontrivial k[G] σ.asModule
  exact exists_ne 0

lemma contains_iff_exists_ne_zero : ρ.Contains σ ↔ ∃ f : IntertwiningMap σ ρ, f ≠ 0 := by
  refine ⟨fun ⟨f, hf⟩ ↦ ⟨f, fun h ↦ ?_⟩,
    fun ⟨f, hf⟩ ↦ ⟨f, (IsIrreducible.injective_or_eq_zero f).resolve_right hf⟩⟩
  rcases exists_ne_zero_of_isIrreducible σ with ⟨w, hw⟩
  exact hw <| hf <| by simp [h]

variable (σ)

/-- **Frobenius reciprocity for permutation representations**: the permutation representation
`k[G ⧸ H]` of a subgroup `H` of finite index contains an irreducible representation `σ` if and only
if `σ` has a nonzero `H`-invariant linear form. -/
lemma contains_ofMulAction_quotient_iff :
    (ofMulAction k G (G ⧸ H)).Contains σ ↔ ∃ φ : Dual k W, φ ≠ 0 ∧ ∀ h ∈ H, φ ∘ₗ σ h = φ := by
  refine ⟨fun ⟨f, hf⟩ ↦ ?_, fun ⟨φ, hφ, hH⟩ ↦ ?_⟩
  · let φ : Dual k W := Finsupp.lapply (QuotientGroup.mk 1 : G ⧸ H) ∘ₗ
      (coeffLinearEquiv k).toLinearMap ∘ₗ f.toLinearMap
    have hφ (g : G) (w : W) : φ (σ g⁻¹ w) = (f w).coeff (QuotientGroup.mk g) := by
      simp [φ, f.isIntertwining]
    refine ⟨φ, fun h0 ↦ ?_, fun h hh ↦ LinearMap.ext fun w ↦ ?_⟩
    · rcases exists_ne_zero_of_isIrreducible σ with ⟨w, hw⟩
      have hfw : (f w).coeff ≠ 0 := fun h ↦ hw <| hf <| by simpa using h
      rcases Finsupp.ne_iff.mp hfw with ⟨x, hx⟩
      induction x using QuotientGroup.induction_on with | H a => ?_
      exact hx <| (hφ a w).symm.trans <| by simp [h0]
    · have h1 : φ w = (f w).coeff (QuotientGroup.mk 1) := by
        simpa using hφ 1 w
      rw [LinearMap.comp_apply, ← inv_inv h, hφ, h1]
      exact congrArg (f w).coeff <| QuotientGroup.eq.mpr <| by simpa using hh
  · let L : W →ₗ[k] k[G ⧸ H] := (coeffLinearEquiv k).symm.toLinearMap ∘ₗ
      (Finsupp.linearEquivFunOnFinite k k (G ⧸ H)).symm.toLinearMap ∘ₗ
      LinearMap.pi fun x ↦ φ ∘ₗ σ (Quotient.out x)⁻¹
    have hL (g : G) (w : W) : (L w).coeff (QuotientGroup.mk g) = φ (σ g⁻¹ w) := by
      rcases QuotientGroup.mk_out_eq_mul H g with ⟨h, hh⟩
      simpa [L, hh] using LinearMap.congr_fun (hH _ (H.inv_mem h.2)) (σ g⁻¹ w)
    refine (contains_iff_exists_ne_zero).mpr ⟨L.intertwiningMap_of_isIntertwiningMap _ _
      fun g w ↦ ?_, fun h0 ↦ hφ <| LinearMap.ext fun w ↦ ?_⟩
    · ext x
      induction x using QuotientGroup.induction_on with | H a => ?_
      simp [hL]
    · have h1 : L w = 0 := DFunLike.congr_fun h0 w
      simpa [h1] using (hL 1 w).symm

variable [Finite G]

/-- **The regular representation contains every irreducible representation**: for a finite group
`G`, the permutation representation `k[G ⧸ ⊥]`, isomorphic to `k[G]`, contains every irreducible
representation of `G`. -/
lemma contains_ofMulAction_quotient_bot : (ofMulAction k G (G ⧸ (⊥ : Subgroup G))).Contains σ := by
  rcases exists_ne_zero_of_isIrreducible σ with ⟨w, hw⟩
  rcases not_forall.mp <| (forall_dual_apply_eq_zero_iff k w).not.mpr hw with ⟨φ, hφ⟩
  refine (contains_ofMulAction_quotient_iff σ ⊥).mpr ⟨φ, fun h ↦ hφ <| by simp [h], fun h hh ↦ ?_⟩
  rw [Subgroup.mem_bot.mp hh, map_one]
  rfl

/-- **The smallest degree of a permutation representation containing an irreducible representation
is attained**: it is the index of a subgroup `H` such that `k[G ⧸ H]` contains it. -/
lemma exists_index_eq_minPermutationDegree :
    ∃ H : Subgroup G, H.index = σ.minPermutationDegree ∧ (ofMulAction k G (G ⧸ H)).Contains σ := by
  rcases (Nat.sInf_mem ⟨_, ⊥, inferInstance, rfl, contains_ofMulAction_quotient_bot σ⟩ :
    σ.minPermutationDegree ∈ _) with ⟨H, -, hH, h⟩
  exact ⟨H, hH, h⟩

end Representation
