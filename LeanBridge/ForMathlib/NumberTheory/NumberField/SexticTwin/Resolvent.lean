import TauCeti.FieldTheory.GaloisGroups.Resolvent.Spec
import LeanBridge.ForMathlib.NumberTheory.NumberField.SexticTwin.Basic
import LeanBridge.ForMathlib.NumberTheory.NumberField.SexticTwin.ProjectiveLine

/-!
# The sextic resolvent of `PGL₂(𝔽₅) ≤ S₆` and the twin of a sextic algebra

The inclusion in `S₆` of the image of `PGL₂(𝔽₅)` (`Equiv.Perm.pglTwoFiveToPerm`), the image of
`S₅` under the outer automorphism `θ`, gives an absolute resolvent of degree
`[S₆ : PGL₂(𝔽₅)] = 6`. In Tau Ceti's framework of resolvent specifications
(`TauCeti.ResolventSpec`), this is an integral invariant `Φ` of six formal roots whose stabilizer
under permutation of the variables is exactly `PGL₂(𝔽₅)`; the resolvent of a sextic `f` is the
orbit product `∏ (X - Ψ(x))` over the six renamings `Ψ` of `Φ`, at the roots `x` of `f`.

The image of `PGL₂(𝔽₅)` is the stabilizer of the synthematic total `T₅` in the action of `S₆` on
the six totals, since `σ • T₅ = T_{θ(σ)(5)}`. So we take `Φ = Σ_{s ∈ T₅} (Σ_{{a, b} ∈ s} x_a x_b)³`,
a sum over the five synthemes of `T₅`: renaming the variables by `σ` gives the invariant of
`σ • T₅`, and the value at `(0, 1, 2, 3, 5, 4)` separates `T₅` from the five other totals.

The coset of `σ` is labelled by `θ(σ)(5) ∈ Fin 6`, and `σ` then acts on the labels by `θ(σ)`. So for
a sextic algebra `A` with Galois action `ρ_A` on the labelled Galois set, the cosets of `PGL₂(𝔽₅)`
permuted by `ρ_A` form the Galois set `θ ∘ ρ_A` of the twin of `A`. These cosets index the roots
of a separable resolvent: by Tau Ceti's factorization theorem
(`TauCeti.ResolventSpec.orbitQuotientEquivFactors`), the irreducible factors of a separable
resolvent of a sextic `f` correspond to the orbits on the cosets of the Galois group of `f`, read
through a numbering of its roots. Identifying the twin of `F[x]/(f)` with the algebra `F[x]/(R)` of
a separable resolvent `R` would need moreover the Galois set of `F[x]/(f)` to be that of the roots
of `f`, which is not formalised here.

## Main definitions

* `Equiv.Perm.synthematicInvariant`: the invariant `Σ_{s ∈ T} (Σ_{{a, b} ∈ s} x_a x_b)³` of a set
  `T` of synthemes.
* `Equiv.Perm.pglTwoFiveResolventSpec` (LMFDB `nf.sextic_twin`): the resolvent specification of
  `PGL₂(𝔽₅) ≤ S₆`.
* `Equiv.Perm.quotientPglTwoFiveEquiv` (LMFDB `nf.sextic_twin`): the labelling of the cosets of
  `PGL₂(𝔽₅)` in `S₆` by `Fin 6`.

## Main results

* `Equiv.Perm.rename_synthematicInvariant_eq_self_iff`: the stabilizer of the invariant of `T₅` is
  exactly the image of `PGL₂(𝔽₅)`.
* `Equiv.Perm.index_range_pglTwoFiveToPerm`: `[S₆ : PGL₂(𝔽₅)] = 6`.
* `Equiv.Perm.natDegree_specialize_pglTwoFiveResolventSpec` (LMFDB `nf.sextic_twin`): the resolvent
  of `PGL₂(𝔽₅)` has degree `6`.
* `Equiv.Perm.quotientPglTwoFiveEquiv_smul`: `σ` acts on the labels of the cosets by `θ(σ)`.
* `Algebra.quotientPglTwoFiveEquiv_smul_galoisSetPerm` (LMFDB `nf.sextic_twin`): the cosets of
  `PGL₂(𝔽₅)` in `S₆`, permuted by the Galois action on a sextic algebra, form the Galois set of
  its twin.
-/

open Equiv MulAction MvPolynomial Perm Subgroup TauCeti

open scoped Pointwise

namespace Equiv.Perm

variable (σ : Perm (Fin 6)) (T : Finset (Finset (Finset (Fin 6))))

/-- The invariant `Σ_{s ∈ T} (Σ_{{a, b} ∈ s} x_a x_b)³` of a set `T` of synthemes of `Fin 6`, each
syntheme being the finset of its pairs. For the synthematic total `T₅` its stabilizer is the image
of `PGL₂(𝔽₅)` (`Equiv.Perm.rename_synthematicInvariant_eq_self_iff`). -/
noncomputable def synthematicInvariant : MvPolynomial (Fin 6) ℤ :=
  ∑ s ∈ T, (∑ p ∈ s, ∏ a ∈ p, X a) ^ 3

lemma rename_synthematicInvariant :
    rename σ (synthematicInvariant T) = synthematicInvariant (σ • T) := by
  rw [synthematicInvariant, synthematicInvariant, map_sum, Finset.smul_finset_def,
    Finset.sum_image fun _ _ _ _ h ↦ smul_left_cancel σ h]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [map_pow, map_sum, Finset.smul_finset_def,
    Finset.sum_image fun _ _ _ _ h ↦ smul_left_cancel σ h]
  refine congrArg (· ^ 3) (Finset.sum_congr rfl fun p _ ↦ ?_)
  rw [map_prod, Finset.smul_finset_def, Finset.prod_image fun _ _ _ _ h ↦ smul_left_cancel σ h]
  simp

lemma eval_synthematicInvariant (v : Fin 6 → ℤ) :
    eval v (synthematicInvariant T) = ∑ s ∈ T, (∑ p ∈ s, ∏ a ∈ p, v a) ^ 3 := by
  simp [synthematicInvariant]

lemma synthematicInvariant_synthematicTotal_eq_iff (i : Fin 6) :
    synthematicInvariant (synthematicTotal i) = synthematicInvariant (synthematicTotal 5) ↔
      i = 5 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have h2 : ∑ s ∈ synthematicTotal i, (∑ p ∈ s, ∏ a ∈ p, (![0, 1, 2, 3, 5, 4] : Fin 6 → ℤ) a) ^ 3 =
      ∑ s ∈ synthematicTotal 5, (∑ p ∈ s, ∏ a ∈ p, (![0, 1, 2, 3, 5, 4] : Fin 6 → ℤ) a) ^ 3 := by
    rw [← eval_synthematicInvariant, ← eval_synthematicInvariant, h]
  clear h
  revert i
  decide

lemma mem_range_pglTwoFiveToPerm_iff : σ ∈ pglTwoFiveToPerm.range ↔ outerAutFinSix σ 5 = 5 := by
  rw [← map_stabilizer_outerAutFinSix, mem_map]
  refine ⟨fun ⟨τ, hτ, h⟩ ↦ ?_, fun h ↦ ⟨outerAutFinSix σ, h, outerAutFinSix_outerAutFinSix σ⟩⟩
  rw [← h, MulEquiv.coe_toMonoidHom, outerAutFinSix_outerAutFinSix]
  exact hτ

/-- **The stabilizer of the invariant of the synthematic total `T₅` is exactly the image of
`PGL₂(𝔽₅)`**: renaming the variables by `σ` gives the invariant of `σ • T₅ = T_{θ(σ)(5)}`, and the
invariants of the six totals differ from that of `T₅` at the point `(0, 1, 2, 3, 5, 4)`. -/
lemma rename_synthematicInvariant_eq_self_iff :
    rename σ (synthematicInvariant roundRobinTotal) = synthematicInvariant roundRobinTotal ↔
      σ ∈ pglTwoFiveToPerm.range := by
  have h5 : roundRobinTotal = synthematicTotal 5 := by decide
  rw [rename_synthematicInvariant, h5, ← synthematicTotal_outerAutFinSix_apply,
    synthematicInvariant_synthematicTotal_eq_iff, mem_range_pglTwoFiveToPerm_iff]

/-- **The absolute resolvent of `PGL₂(𝔽₅) ≤ S₆`** (LMFDB `nf.sextic_twin`): the resolvent
specification (Tau Ceti's `TauCeti.ResolventSpec`) of the image of `PGL₂(𝔽₅)` in `S₆`, with the
invariant `Equiv.Perm.synthematicInvariant` of the synthematic total `T₅`, whose stabilizer is
exactly that image. Its specialization at a sextic is the resolvent, of degree
`[S₆ : PGL₂(𝔽₅)] = 6` (`Equiv.Perm.natDegree_specialize_pglTwoFiveResolventSpec`). -/
noncomputable def pglTwoFiveResolventSpec : ResolventSpec 6 :=
  ResolventSpec.mk' pglTwoFiveToPerm.range (synthematicInvariant roundRobinTotal)
    rename_synthematicInvariant_eq_self_iff

/-- **`PGL₂(𝔽₅)` has index `6` in `S₆`.** -/
lemma index_range_pglTwoFiveToPerm : pglTwoFiveToPerm.range.index = 6 := by
  have h :
      pglTwoFiveToPerm.range.index * Nat.card pglTwoFiveToPerm.range = Nat.card (Perm (Fin 6)) :=
    index_mul_card _
  rw [natCard_range_pglTwoFiveToPerm, Nat.card_perm, Nat.card_eq_fintype_card,
    Fintype.card_fin] at h
  have h720 : Nat.factorial 6 = 720 := rfl
  omega

/-- **The absolute resolvent of `PGL₂(𝔽₅) ≤ S₆` has degree `[S₆ : PGL₂(𝔽₅)] = 6`** (LMFDB
`nf.sextic_twin`): its specialization at any polynomial over a nonzero commutative ring has
degree `6`. -/
lemma natDegree_specialize_pglTwoFiveResolventSpec (R : Type*) [CommRing R] [Nontrivial R]
    (f : Polynomial R) : (pglTwoFiveResolventSpec.specialize R f).natDegree = 6 := by
  rw [ResolventSpec.natDegree_specialize, pglTwoFiveResolventSpec, ResolventSpec.mk'_H,
    index_range_pglTwoFiveToPerm]

/-- The labelling of the cosets of `PGL₂(𝔽₅)` in `S₆` by `Fin 6` (LMFDB `nf.sextic_twin`): the coset
of `σ` is labelled by `θ(σ)(5)`, where `θ` is the outer automorphism of `S₆`, and `σ` acts on the
labels by `θ(σ)` (`Equiv.Perm.quotientPglTwoFiveEquiv_smul`). -/
noncomputable def quotientPglTwoFiveEquiv : Perm (Fin 6) ⧸ pglTwoFiveToPerm.range ≃ Fin 6 where
  toFun := Quotient.lift (fun σ ↦ outerAutFinSix σ 5) fun σ τ h ↦ by
    have h' : outerAutFinSix (σ⁻¹ * τ) 5 = 5 :=
      (mem_range_pglTwoFiveToPerm_iff _).mp (QuotientGroup.leftRel_apply.mp h)
    rw [map_mul, map_inv, mul_apply, inv_eq_iff_eq] at h'
    exact h'.symm
  invFun j := (outerAutFinSix (swap 5 j) : Perm (Fin 6) ⧸ pglTwoFiveToPerm.range)
  left_inv q := by
    induction q using QuotientGroup.induction_on with | H σ => ?_
    refine QuotientGroup.eq.mpr ?_
    rw [mem_range_pglTwoFiveToPerm_iff, map_mul, map_inv, outerAutFinSix_outerAutFinSix, mul_apply,
      inv_eq_iff_eq]
    exact (swap_apply_left _ _).symm
  right_inv j :=
    (DFunLike.congr_fun (outerAutFinSix_outerAutFinSix (swap 5 j)) 5).trans (swap_apply_left 5 j)

/-- **`σ ∈ S₆` acts on the labels of the cosets of `PGL₂(𝔽₅)` by `θ(σ)`.** -/
lemma quotientPglTwoFiveEquiv_smul (q : Perm (Fin 6) ⧸ pglTwoFiveToPerm.range) :
    quotientPglTwoFiveEquiv (σ • q) = outerAutFinSix σ (quotientPglTwoFiveEquiv q) := by
  induction q using QuotientGroup.induction_on with | H τ => ?_
  rw [Quotient.smul_mk, smul_eq_mul]
  exact DFunLike.congr_fun (map_mul outerAutFinSix σ τ) 5

end Equiv.Perm

namespace Algebra

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]

/-- **The cosets of `PGL₂(𝔽₅)` in `S₆`, permuted by the Galois action on a sextic algebra, form
the Galois set of its twin** (LMFDB `nf.sextic_twin`): for an `F`-algebra `A` whose Galois set is
labelled by `e`, an element `τ` of `Gal(F^sep/F)` acts through `ρ_A(τ)` on the cosets, which index
the roots of a separable resolvent of `PGL₂(𝔽₅)`, as `θ(ρ_A(τ))` acts on their labels, that is, as
on the Galois set of the twin of `A` (`Algebra.sexticTwinPerm`). -/
lemma quotientPglTwoFiveEquiv_smul_galoisSetPerm (e : (A →ₐ[F] SeparableClosure F) ≃ Fin 6)
    (τ : Gal(SeparableClosure F/F)) (q : Perm (Fin 6) ⧸ pglTwoFiveToPerm.range) :
    quotientPglTwoFiveEquiv (e.permCongr (galoisSetPerm F _ A τ) • q) =
      sexticTwinPerm e τ (quotientPglTwoFiveEquiv q) := by
  rw [quotientPglTwoFiveEquiv_smul, sexticTwinPerm_apply]

end Algebra
