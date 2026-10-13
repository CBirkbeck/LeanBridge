/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanBridge.IdealArithmetic.Galois.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.RingTheory.Frobenius
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.FieldTheory.Finite.Extension

/-!
# Core Theorem 1 — Dedekind's theorem on the cycle type of Frobenius

For a monic separable `f ∈ ℤ[X]` and a prime `p ∤ disc f`, the cycle type of an arithmetic Frobenius
`σ` acting on the roots of `f` (in the splitting field) equals the multiset of degrees of the monic
irreducible factors of `f mod p`.

This file builds the bridge in the order of `.mathlib-quality/decomposition.md` (Result R3):
* **L_b1** `partition_parts_eq_orbit_card` — pure group theory: the partition attached to a
  permutation is the multiset of its `⟨σ⟩`-orbit cardinalities.
* `partition_parts_permCongr` — the conjugacy glue: the cycle-type partition is invariant under
  relabeling the underlying type (used to transport `galActionHom σ` to the residue Frobenius).
* **L_b2**–**L_b4** — the arithmetic bridge (reduction intertwines Galois with residue Frobenius).
* **R3 main** + certificate.

See `.mathlib-quality/tickets.md`, T008–T013.
-/

namespace IdealArithmetic.Galois

open Polynomial Finset

section Lb1

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The set of `⟨σ⟩`-orbits on a finite type is finite, hence a `Fintype` (noncomputably). -/
noncomputable instance orbitRelZpowersFintype (σ : Equiv.Perm α) :
    Fintype (MulAction.orbitRel.Quotient (Subgroup.zpowers σ) α) :=
  Fintype.ofFinite _

omit [Fintype α] [DecidableEq α] in
/-- Membership in the `⟨σ⟩ = zpowers σ` orbit is exactly `σ.SameCycle`. -/
theorem mem_orbit_zpowers_iff (σ : Equiv.Perm α) (x y : α) :
    y ∈ MulAction.orbit (Subgroup.zpowers σ) x ↔ σ.SameCycle x y := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨⟨σ ^ n, Subgroup.zpow_mem_zpowers σ n⟩, rfl⟩

/-- For a point in the support of `σ`, its `⟨σ⟩`-orbit is the support of `σ.cycleOf x`. -/
theorem orbit_zpowers_eq_support_cycleOf (σ : Equiv.Perm α) {x : α} (hx : x ∈ σ.support) :
    MulAction.orbit (Subgroup.zpowers σ) x = ↑(σ.cycleOf x).support := by
  ext y
  rw [mem_orbit_zpowers_iff, Finset.mem_coe, Equiv.Perm.mem_support_cycleOf_iff]
  exact ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩

omit [Fintype α] [DecidableEq α] in
/-- A fixed point's `⟨σ⟩`-orbit is a singleton. -/
theorem orbit_zpowers_of_fixed (σ : Equiv.Perm α) {x : α} (hx : σ x = x) :
    MulAction.orbit (Subgroup.zpowers σ) x = {x} := by
  ext y
  rw [mem_orbit_zpowers_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, rfl⟩
    rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hx]
  · rintro rfl
    exact ⟨0, rfl⟩

omit [Fintype α] [DecidableEq α] in
/-- Two points give the same `⟨σ⟩`-orbit class iff they are in the same cycle. -/
theorem quotient_mk_eq_iff_sameCycle (σ : Equiv.Perm α) (x y : α) :
    (Quotient.mk'' x : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) α) = Quotient.mk'' y
      ↔ σ.SameCycle x y := by
  rw [Quotient.eq'', MulAction.orbitRel_apply, mem_orbit_zpowers_iff]
  exact ⟨Equiv.Perm.SameCycle.symm, Equiv.Perm.SameCycle.symm⟩

/-- With `rep` a choice of representative in the support of each cyclic factor of `σ`, sending a
factor to the `⟨σ⟩`-orbit class of its representative and a fixed point to its own class is a
bijection `cycleFactorsFinset σ ⊕ fixedPoints σ ≃ ⟨σ⟩-orbits`. Injectivity: two representatives with
the same class are `SameCycle`, forcing equal cycle factors (resp. equal fixed points), and the
factor/fixed-point cases cannot collide since representatives lie in `σ.support`. Surjectivity: every
point is either fixed or lies in the support of `σ.cycleOf`, a cyclic factor. -/
private theorem repClass_sumElim_bijective (σ : Equiv.Perm α)
    (rep : {c // c ∈ σ.cycleFactorsFinset} → α)
    (hcycleOf_rep : ∀ c : {c // c ∈ σ.cycleFactorsFinset}, σ.cycleOf (rep c) = ↑c)
    (hrep_supp : ∀ c : {c // c ∈ σ.cycleFactorsFinset}, rep c ∈ σ.support)
    (hrep_mem : ∀ c : {c // c ∈ σ.cycleFactorsFinset}, rep c ∈ (c : Equiv.Perm α).support) :
    Function.Bijective
      (Sum.elim (fun c => Quotient.mk'' (rep c))
          (fun x : {x // σ x = x} => Quotient.mk'' x.1) :
        ({c // c ∈ σ.cycleFactorsFinset} ⊕ {x // σ x = x}) →
          MulAction.orbitRel.Quotient (Subgroup.zpowers σ) α) := by
  constructor
  · rintro (c₁ | x₁) (c₂ | x₂) h
    · simp only [Sum.elim_inl] at h
      rw [quotient_mk_eq_iff_sameCycle] at h
      have : σ.cycleOf (rep c₁) = σ.cycleOf (rep c₂) := h.cycleOf_eq
      rw [hcycleOf_rep, hcycleOf_rep] at this
      exact congrArg Sum.inl (Subtype.ext this)
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      rw [quotient_mk_eq_iff_sameCycle] at h
      obtain ⟨m, hm⟩ := h.symm
      rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self x₂.2] at hm
      have hfix : σ (rep c₁) = rep c₁ := by rw [← hm]; exact x₂.2
      exact absurd hfix (Equiv.Perm.mem_support.mp (hrep_supp c₁))
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      rw [quotient_mk_eq_iff_sameCycle] at h
      obtain ⟨n, hn⟩ := h
      rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self x₁.2] at hn
      have hfix : σ (rep c₂) = rep c₂ := by rw [← hn]; exact x₁.2
      exact absurd hfix (Equiv.Perm.mem_support.mp (hrep_supp c₂))
    · simp only [Sum.elim_inr] at h
      rw [quotient_mk_eq_iff_sameCycle] at h
      obtain ⟨n, hn⟩ := h
      rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self x₁.2] at hn
      exact congrArg Sum.inr (Subtype.ext hn)
  · intro ω
    induction ω using Quotient.inductionOn' with
    | h y =>
      by_cases hy : σ y = y
      · exact ⟨Sum.inr ⟨y, hy⟩, rfl⟩
      · have hys : y ∈ σ.support := Equiv.Perm.mem_support.mpr hy
        refine ⟨Sum.inl ⟨σ.cycleOf y, Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hys⟩, ?_⟩
        simp only [Sum.elim_inl]
        rw [quotient_mk_eq_iff_sameCycle]
        have hmem := hrep_mem ⟨σ.cycleOf y, Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hys⟩
        rw [Equiv.Perm.mem_support_cycleOf_iff] at hmem
        exact hmem.1.symm

/-- The `⟨σ⟩`-orbits on `α` biject with `cycleFactorsFinset σ ⊕ fixedPoints σ` in such a way that the
orbit corresponding to a cyclic factor has that factor's support cardinality, while the orbit of a
fixed point is a singleton. Packages the bijection with its orbit-size data for
`partition_parts_eq_orbit_card`. -/
private theorem exists_orbitQuotient_equiv_orbit_card (σ : Equiv.Perm α) :
    ∃ e : ({c // c ∈ σ.cycleFactorsFinset} ⊕ {x // σ x = x}) ≃
        MulAction.orbitRel.Quotient (Subgroup.zpowers σ) α,
      (∀ c, Nat.card (e (Sum.inl c)).orbit = (c : Equiv.Perm α).support.card) ∧
      (∀ x, Nat.card (e (Sum.inr x)).orbit = 1) := by
  have hne : ∀ c : {c // c ∈ σ.cycleFactorsFinset}, (↑c : Equiv.Perm α).support.Nonempty :=
    fun c => ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1).nonempty_support
  set rep : {c // c ∈ σ.cycleFactorsFinset} → α := fun c => (hne c).choose with hrep
  have hrep_mem : ∀ c : {c // c ∈ σ.cycleFactorsFinset}, rep c ∈ (c : Equiv.Perm α).support :=
    fun c => (hne c).choose_spec
  have hcycleOf_rep : ∀ c, σ.cycleOf (rep c) = ↑c :=
    fun c => (Equiv.Perm.cycle_is_cycleOf (hrep_mem c) c.2).symm
  have hrep_supp : ∀ c, rep c ∈ σ.support := by
    intro c
    have := hrep_mem c
    rw [← hcycleOf_rep c] at this
    exact (Equiv.Perm.mem_support_cycleOf_iff.mp this).2
  refine ⟨Equiv.ofBijective _ (repClass_sumElim_bijective σ rep hcycleOf_rep hrep_supp hrep_mem),
    fun c => ?_, fun x => ?_⟩
  · rw [Equiv.ofBijective_apply, Sum.elim_inl, MulAction.orbitRel.Quotient.orbit_mk,
      orbit_zpowers_eq_support_cycleOf σ (hrep_supp c), hcycleOf_rep c, Nat.card_coe_set_eq,
      Set.ncard_coe_finset]
  · rw [Equiv.ofBijective_apply, Sum.elim_inr, MulAction.orbitRel.Quotient.orbit_mk,
      orbit_zpowers_of_fixed σ x.2, Nat.card_coe_set_eq, Set.ncard_singleton]

/-- **L_b1 / T008.** The partition of `Fintype.card α` attached to a permutation `σ` is the multiset
of cardinalities of the orbits of `⟨σ⟩ = Subgroup.zpowers σ` acting on `α`. (Length-`≥2` cycles are
the nontrivial orbits; fixed points are the singleton orbits — which is why `partition` is the right
object, not `cycleType`, since the latter drops fixed points.) -/
theorem partition_parts_eq_orbit_card (σ : Equiv.Perm α) :
    σ.partition.parts =
      (Finset.univ : Finset (MulAction.orbitRel.Quotient (Subgroup.zpowers σ) α)).val.map
        (fun ω => Nat.card ω.orbit) := by
  classical
  obtain ⟨e, hsize_inl, hsize_inr⟩ := exists_orbitQuotient_equiv_orbit_card σ
  have hfix_card : Fintype.card {x // σ x = x} = Fintype.card α - σ.support.card := by
    rw [Fintype.card_subtype, ← Finset.card_compl]
    congr 1
    ext x
    simp [Finset.mem_filter, Finset.mem_compl, Equiv.Perm.mem_support]
  rw [Equiv.Perm.parts_partition]
  have key : (Finset.univ :
        Finset (MulAction.orbitRel.Quotient (Subgroup.zpowers σ) α)).val.map
        (fun ω => Nat.card ω.orbit)
      = σ.cycleType + Multiset.replicate (Fintype.card α - σ.support.card) 1 := by
    rw [← Finset.map_univ_equiv e, Finset.map_val, Multiset.map_map,
      ← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.map_disjSum]
    simp only [Function.comp_apply, Equiv.coe_toEmbedding, hsize_inl, hsize_inr]
    congr 1
    · rw [Equiv.Perm.cycleType]
      conv_rhs => rw [← Multiset.attach_map_val σ.cycleFactorsFinset.val, Multiset.map_map]
      rw [Finset.univ_eq_attach, Finset.attach_val]
      rfl
    · rw [Multiset.map_const',
        show (Finset.univ : Finset {x // σ x = x}).val.card = Fintype.card {x // σ x = x} from rfl,
        hfix_card]
  rw [key]

end Lb1

section PermGlue

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- Relabeling a permutation by `e : α ≃ β` (via `permCongr`) is the same as extending `τ` over the
whole of `β` through `e` (`Equiv.Perm.extendDomain` with the always-true predicate). -/
theorem permCongr_eq_extendDomain (e : α ≃ β) (τ : Equiv.Perm α) :
    e.permCongr τ = τ.extendDomain (e.trans (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm) := by
  ext b
  simp [Equiv.Perm.extendDomain_apply_subtype, Equiv.permCongr_apply]

/-- Cycle type is invariant under relabeling the underlying type. -/
theorem cycleType_permCongr (e : α ≃ β) (τ : Equiv.Perm α) :
    (e.permCongr τ).cycleType = τ.cycleType := by
  rw [permCongr_eq_extendDomain, Equiv.Perm.cycleType_extendDomain]

/-- **Conjugacy glue for R3.** The cycle-type partition is invariant under relabeling the underlying
type by an equivalence `e : α ≃ β`. Applied with `e` the reduction bijection `rootSet E ≃ rootSet k`
(a Frobenius-equivariant relabeling), this transports the partition of `galActionHom σ` to that of
the residue Frobenius `x ↦ x ^ p`. -/
theorem partition_parts_permCongr (e : α ≃ β) (τ : Equiv.Perm α) :
    (e.permCongr τ).partition.parts = τ.partition.parts := by
  rw [Equiv.Perm.parts_partition, Equiv.Perm.parts_partition, cycleType_permCongr,
    permCongr_eq_extendDomain, Equiv.Perm.card_support_extend_domain, ← Fintype.card_congr e]

end PermGlue

section FrobeniusPerm

open scoped Classical IntermediateField
open MulAction Function

variable (p : ℕ) [Fact p.Prime] (k : Type*) [CommRing k] [IsDomain k] [Finite k]
    [Algebra (ZMod p) k]

/-- **The residue Frobenius as a root permutation.** For a finite integral domain `k` that is an
`𝔽ₚ`-algebra (hence a finite field) and `g : (ZMod p)[X]`, the map `x ↦ xᵖ` restricts to a
permutation of the roots of `g` in `k`. It preserves the root set because `x ↦ xᵖ` is the
`𝔽ₚ`-algebra automorphism `FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k` (an `AlgEquiv` over
`ZMod p`, hence sends roots of a `ZMod p`-polynomial to roots). This is the object whose partition
L_b4 computes. (We take `[CommRing k] [IsDomain k]` rather than `[Field k]` so that when `k` is a
quotient `𝓞E ⧸ 𝔔` the canonical quotient ring structure is used throughout — avoiding an expensive
`Field`/quotient instance diamond — deriving the field structure locally.) -/
noncomputable def frobeniusPerm (g : (ZMod p)[X]) : Equiv.Perm (g.rootSet k) := by
  haveI : Fintype k := Fintype.ofFinite _
  letI : Field k := (Finite.isField_of_domain k).toField
  haveI : Algebra.IsAlgebraic (ZMod p) k := Algebra.IsAlgebraic.of_finite _ _
  refine Equiv.Perm.subtypePerm (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k).toEquiv ?_
  intro x
  have key : (aeval ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k) x)) g
      = (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k) ((aeval x) g) :=
    Polynomial.aeval_algHom_apply
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k).toAlgHom x g
  simp only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, Polynomial.mem_rootSet', key,
    map_eq_zero_iff _ (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k).injective]

/-- The underlying map of `frobeniusPerm` is indeed `x ↦ xᵖ`. -/
@[simp] theorem frobeniusPerm_coe_apply (g : (ZMod p)[X]) (x : g.rootSet k) :
    ((frobeniusPerm p k g x : k)) = (x : k) ^ p := by
  haveI : Fintype k := Fintype.ofFinite _
  letI : Field k := (Finite.isField_of_domain k).toField
  haveI : Algebra.IsAlgebraic (ZMod p) k := Algebra.IsAlgebraic.of_finite _ _
  show (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k) (x : k) = (x : k) ^ p
  rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card]

/-- The `n`-th iterate of `frobeniusPerm` is `x ↦ x^(pⁿ)`. Turns `frobeniusPerm^n γ = γ` into
`γ^(pⁿ) = γ` for the orbit-size computation. -/
theorem frobeniusPerm_pow_coe (g : (ZMod p)[X]) (n : ℕ) (x : g.rootSet k) :
    (((frobeniusPerm p k g ^ n) x : g.rootSet k) : k) = (x : k) ^ (p ^ n) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, frobeniusPerm_coe_apply, ih, ← pow_mul, ← pow_succ]

/-- **B2 single step.** `minpoly` over `𝔽ₚ` is invariant under the Frobenius `y ↦ yᵖ` on `k`
(which is the `𝔽ₚ`-algebra automorphism `frobeniusAlgEquivOfAlgebraic`). -/
theorem minpoly_pow_p (y : k) :
    minpoly (ZMod p) (y ^ p) = minpoly (ZMod p) y := by
  haveI : Fintype k := Fintype.ofFinite k
  letI : Field k := (Finite.isField_of_domain k).toField
  haveI : Algebra.IsAlgebraic (ZMod p) k := Algebra.IsAlgebraic.of_finite _ _
  have he : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k) y = y ^ p := by simp
  rw [← he]
  exact minpoly.algEquiv_eq _ _

/-- **B2, iterated (both directions).** `minpoly` is invariant along the whole `⟨frobeniusPerm⟩`
orbit: any integer power of `frobeniusPerm` preserves the minimal polynomial of a root. -/
theorem minpoly_zpow (g : (ZMod p)[X]) (n : ℤ) (x : g.rootSet k) :
    minpoly (ZMod p) (((frobeniusPerm p k g ^ n) x : g.rootSet k) : k)
      = minpoly (ZMod p) ((x : g.rootSet k) : k) := by
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ i ih =>
      rw [zpow_add_one, Equiv.Perm.mul_apply, ih (frobeniusPerm p k g x),
        frobeniusPerm_coe_apply, minpoly_pow_p]
  | pred i ih =>
      rw [zpow_sub_one, Equiv.Perm.mul_apply, ih ((frobeniusPerm p k g)⁻¹ x),
        ← minpoly_pow_p p k (((frobeniusPerm p k g)⁻¹ x : g.rootSet k) : k)]
      congr 1
      simp [← frobeniusPerm_coe_apply]

/-- **B2 packaged.** Any two roots in the same `⟨frobeniusPerm⟩`-orbit have the same minpoly. -/
theorem minpoly_orbit_invariant (g : (ZMod p)[X]) {x a : g.rootSet k}
    (ha : a ∈ MulAction.orbit (Subgroup.zpowers (frobeniusPerm p k g)) x) :
    minpoly (ZMod p) ((a : g.rootSet k) : k) = minpoly (ZMod p) ((x : g.rootSet k) : k) := by
  rw [MulAction.mem_orbit_iff] at ha
  obtain ⟨c, hc⟩ := ha
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp c.2
  have hax : a = (frobeniusPerm p k g ^ n) x := by
    rw [← hc, hn]; rfl
  rw [hax, minpoly_zpow]

/-- **Fact A (finite-field subfield criterion, easy direction).** For `x` in the finite field `k`,
`x ^ (p ^ d) = x` where `d = deg (minpoly 𝔽ₚ x)`: `x` lies in the subfield `𝔽ₚ(x)`, of cardinality
`p ^ d`, so `FiniteField.pow_card` applies. -/
theorem pow_pow_natDegree (x : k) :
    x ^ (p ^ (minpoly (ZMod p) x).natDegree) = x := by
  haveI : Fintype k := Fintype.ofFinite k
  letI : Field k := (Finite.isField_of_domain k).toField
  haveI : Module.Finite (ZMod p) k := Module.finite_iff_finite.mpr inferInstance
  have hx_int : IsIntegral (ZMod p) x := IsIntegral.of_finite (ZMod p) x
  have hxF : x ∈ (ZMod p)⟮x⟯ := IntermediateField.mem_adjoin_simple_self (ZMod p) x
  haveI : Fintype (ZMod p)⟮x⟯ := Fintype.ofFinite _
  have hcard : Fintype.card (ZMod p)⟮x⟯ = p ^ (minpoly (ZMod p) x).natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), IntermediateField.adjoin.finrank hx_int, ZMod.card]
  have hpc := FiniteField.pow_card (⟨x, hxF⟩ : (ZMod p)⟮x⟯)
  rw [hcard] at hpc
  simpa using congrArg Subtype.val hpc

/-- **B3/B4 core (CRUX).** The minimal period of `frobeniusPerm` at a root `x` equals the degree of
its minimal polynomial: `d ∣ period` by the finite-field criterion
(`Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`), and `period ∣ d` by `x ^ (p^d) = x`
(`pow_pow_natDegree`). -/
theorem minimalPeriod_eq_natDegree (g : (ZMod p)[X]) (x : g.rootSet k) :
    Function.minimalPeriod (frobeniusPerm p k g • ·) x
      = (minpoly (ZMod p) ((x : g.rootSet k) : k)).natDegree := by
  haveI : Fintype k := Fintype.ofFinite k
  letI : Field k := (Finite.isField_of_domain k).toField
  haveI : Module.Finite (ZMod p) k := Module.finite_iff_finite.mpr inferInstance
  have hx_int : IsIntegral (ZMod p) ((x : g.rootSet k) : k) := IsIntegral.of_finite (ZMod p) _
  have hirr : Irreducible (minpoly (ZMod p) ((x : g.rootSet k) : k)) := minpoly.irreducible hx_int
  refine Nat.dvd_antisymm ?_ ?_
  · apply Function.IsPeriodicPt.minimalPeriod_dvd
    have hfix : (frobeniusPerm p k g ^ (minpoly (ZMod p) ((x : g.rootSet k) : k)).natDegree) x = x :=
      Subtype.ext (by rw [frobeniusPerm_pow_coe, pow_pow_natDegree])
    show (frobeniusPerm p k g • ·)^[(minpoly (ZMod p) ((x : g.rootSet k) : k)).natDegree] x = x
    rw [smul_iterate]
    exact hfix
  · have hper : (frobeniusPerm p k g ^
        Function.minimalPeriod (frobeniusPerm p k g • ·) x) x = x := by
      have h : (frobeniusPerm p k g • ·)^[Function.minimalPeriod (frobeniusPerm p k g • ·) x] x = x :=
        Function.isPeriodicPt_minimalPeriod (frobeniusPerm p k g • ·) x
      rwa [smul_iterate] at h
    have hxm : ((x : g.rootSet k) : k) ^ (p ^ Function.minimalPeriod (frobeniusPerm p k g • ·) x)
        = ((x : g.rootSet k) : k) := by
      rw [← frobeniusPerm_pow_coe, hper]
    have hdvd : minpoly (ZMod p) ((x : g.rootSet k) : k) ∣
        X ^ (p ^ Function.minimalPeriod (frobeniusPerm p k g • ·) x) - X := by
      apply minpoly.dvd
      rw [map_sub, map_pow, aeval_X, hxm, sub_self]
    apply Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hirr
    rw [Nat.card_zmod]
    exact hdvd

/-- **B1.** The minpoly of a root of `g` is one of the (monic, irreducible) normalized factors. -/
theorem minpoly_mem_normalizedFactors (g : (ZMod p)[X]) (hg0 : g ≠ 0) (x : g.rootSet k) :
    minpoly (ZMod p) ((x : g.rootSet k) : k) ∈ UniqueFactorizationMonoid.normalizedFactors g := by
  haveI : Fintype k := Fintype.ofFinite k
  letI : Field k := (Finite.isField_of_domain k).toField
  haveI : Module.Finite (ZMod p) k := Module.finite_iff_finite.mpr inferInstance
  have hx_int : IsIntegral (ZMod p) ((x : g.rootSet k) : k) := IsIntegral.of_finite (ZMod p) _
  rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff' hg0]
  exact ⟨minpoly.irreducible hx_int, (minpoly.monic hx_int).normalize_eq_self,
    minpoly.dvd _ _ (aeval_eq_zero_of_mem_rootSet x.2)⟩

/-- **B1 backward.** Each normalized factor `q` of the splitting `g` is the minpoly of some root of
`g` in `k` (its root exists because `q ∣ g` splits; that root's minpoly is `q` because `q` is
irreducible and normalized ⇒ monic). -/
theorem exists_root_minpoly_eq (g : (ZMod p)[X]) (hg0 : g ≠ 0)
    (hsplit : (g.map (algebraMap (ZMod p) k)).Splits) {q : (ZMod p)[X]}
    (hq : q ∈ UniqueFactorizationMonoid.normalizedFactors g) :
    ∃ γ : g.rootSet k, minpoly (ZMod p) ((γ : g.rootSet k) : k) = q := by
  haveI : Fintype k := Fintype.ofFinite k
  letI : Field k := (Finite.isField_of_domain k).toField
  haveI : Module.Finite (ZMod p) k := Module.finite_iff_finite.mpr inferInstance
  have hinj : Function.Injective (algebraMap (ZMod p) k) := (algebraMap (ZMod p) k).injective
  rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff' hg0] at hq
  obtain ⟨hq_irr, hq_norm, hq_dvd⟩ := hq
  have hg0map : g.map (algebraMap (ZMod p) k) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hg0
  have hqsplit : (q.map (algebraMap (ZMod p) k)).Splits :=
    Splits.of_dvd hsplit hg0map (Polynomial.map_dvd (algebraMap (ZMod p) k) hq_dvd)
  have hdeg : (q.map (algebraMap (ZMod p) k)).degree ≠ 0 := by
    rw [degree_map_eq_of_injective hinj]; exact hq_irr.degree_pos.ne'
  obtain ⟨a, ha⟩ := hqsplit.exists_eval_eq_zero hdeg
  have haeval : aeval a g = 0 := by
    rw [aeval_def, eval₂_eq_eval_map]
    exact eval_eq_zero_of_dvd_of_eval_eq_zero (Polynomial.map_dvd (algebraMap (ZMod p) k) hq_dvd) ha
  have ha_g : a ∈ g.rootSet k := by rw [mem_rootSet']; exact ⟨hg0map, haeval⟩
  refine ⟨⟨a, ha_g⟩, ?_⟩
  have hx_int : IsIntegral (ZMod p) a := IsIntegral.of_finite (ZMod p) a
  have hdvd_min : minpoly (ZMod p) a ∣ q := by
    apply minpoly.dvd; rw [aeval_def, eval₂_eq_eval_map]; exact ha
  have hassoc : Associated (minpoly (ZMod p) a) q :=
    Irreducible.associated_of_dvd (minpoly.irreducible hx_int) hq_irr hdvd_min
  have hnorm := normalize_eq_normalize_iff_associated.mpr hassoc
  rwa [(minpoly.monic hx_int).normalize_eq_self, hq_norm] at hnorm

/-- **B4.** The cardinality of a `⟨frobeniusPerm⟩`-orbit equals the degree of the minimal polynomial
of (any representative of) that orbit. -/
theorem natCard_orbit_eq_natDegree (g : (ZMod p)[X])
    (ω : orbitRel.Quotient (Subgroup.zpowers (frobeniusPerm p k g)) (g.rootSet k)) :
    Nat.card ω.orbit = (minpoly (ZMod p) ((Quotient.out ω : g.rootSet k) : k)).natDegree := by
  rw [orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq']
  haveI : Fintype (orbit (Subgroup.zpowers (frobeniusPerm p k g)) (Quotient.out ω)) :=
    Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, ← MulAction.minimalPeriod_eq_card, minimalPeriod_eq_natDegree]

/-- **B3 (transitivity, set form).** The image in `k` of a `⟨frobeniusPerm⟩`-orbit of a root `x` is
*exactly* the root set of `minpoly x`. `⊆` is `minpoly_orbit_invariant`; equality follows because
both finite sets have cardinality `deg (minpoly x)` (orbit: `minimalPeriod_eq_natDegree`; root set:
`card_rootSet_eq_natDegree`). -/
theorem orbit_image_eq_rootSet (g : (ZMod p)[X]) (hsep : g.Separable)
    (hsplit : (g.map (algebraMap (ZMod p) k)).Splits) (x : g.rootSet k) :
    (fun a : g.rootSet k => (a : k)) '' (orbit (Subgroup.zpowers (frobeniusPerm p k g)) x)
      = (minpoly (ZMod p) ((x : g.rootSet k) : k)).rootSet k := by
  haveI : Fintype k := Fintype.ofFinite k
  letI : Field k := (Finite.isField_of_domain k).toField
  haveI : Module.Finite (ZMod p) k := Module.finite_iff_finite.mpr inferInstance
  have hinj : Function.Injective (algebraMap (ZMod p) k) := (algebraMap (ZMod p) k).injective
  have hx_int : IsIntegral (ZMod p) ((x : g.rootSet k) : k) := IsIntegral.of_finite (ZMod p) _
  have hdvd_g : minpoly (ZMod p) ((x : g.rootSet k) : k) ∣ g :=
    minpoly.dvd _ _ (aeval_eq_zero_of_mem_rootSet x.2)
  have hmsep : (minpoly (ZMod p) ((x : g.rootSet k) : k)).Separable := hsep.of_dvd hdvd_g
  have hmsplit : ((minpoly (ZMod p) ((x : g.rootSet k) : k)).map (algebraMap (ZMod p) k)).Splits :=
    Splits.of_dvd hsplit ((Polynomial.map_ne_zero_iff hinj).mpr hsep.ne_zero)
      (Polynomial.map_dvd (algebraMap (ZMod p) k) hdvd_g)
  have himg_sub : (fun a : g.rootSet k => (a : k)) ''
      (orbit (Subgroup.zpowers (frobeniusPerm p k g)) x)
      ⊆ (minpoly (ZMod p) ((x : g.rootSet k) : k)).rootSet k := by
    rintro y ⟨z, hz, rfl⟩
    rw [mem_rootSet']
    refine ⟨(Polynomial.map_ne_zero_iff hinj).mpr (minpoly.ne_zero hx_int), ?_⟩
    rw [← minpoly_orbit_invariant p k g hz]
    exact minpoly.aeval _ _
  have horb : Nat.card (orbit (Subgroup.zpowers (frobeniusPerm p k g)) x)
      = (minpoly (ZMod p) ((x : g.rootSet k) : k)).natDegree := by
    haveI : Fintype (orbit (Subgroup.zpowers (frobeniusPerm p k g)) x) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, ← MulAction.minimalPeriod_eq_card, minimalPeriod_eq_natDegree]
  have himg : ((fun a : g.rootSet k => (a : k)) ''
      (orbit (Subgroup.zpowers (frobeniusPerm p k g)) x)).ncard
      = (minpoly (ZMod p) ((x : g.rootSet k) : k)).natDegree := by
    rw [Set.ncard_image_of_injective _ Subtype.coe_injective, ← Nat.card_coe_set_eq, horb]
  have hroot : ((minpoly (ZMod p) ((x : g.rootSet k) : k)).rootSet k).ncard
      = (minpoly (ZMod p) ((x : g.rootSet k) : k)).natDegree := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, card_rootSet_eq_natDegree hmsep hmsplit]
  exact Set.eq_of_subset_of_ncard_le himg_sub (le_of_eq (hroot.trans himg.symm)) (Set.toFinite _)

/-- **B3 (transitivity).** Two roots of `g` with equal minimal polynomial lie in the same
`⟨frobeniusPerm⟩`-orbit. -/
theorem sameOrbit_of_minpoly_eq (g : (ZMod p)[X]) (hsep : g.Separable)
    (hsplit : (g.map (algebraMap (ZMod p) k)).Splits) {a b : g.rootSet k}
    (h : minpoly (ZMod p) ((a : g.rootSet k) : k) = minpoly (ZMod p) ((b : g.rootSet k) : k)) :
    a ∈ orbit (Subgroup.zpowers (frobeniusPerm p k g)) b := by
  haveI : Fintype k := Fintype.ofFinite k
  letI : Field k := (Finite.isField_of_domain k).toField
  haveI : Module.Finite (ZMod p) k := Module.finite_iff_finite.mpr inferInstance
  have hinj : Function.Injective (algebraMap (ZMod p) k) := (algebraMap (ZMod p) k).injective
  have ha_int : IsIntegral (ZMod p) ((a : g.rootSet k) : k) := IsIntegral.of_finite (ZMod p) _
  have ha_root : ((a : g.rootSet k) : k) ∈ (minpoly (ZMod p) ((b : g.rootSet k) : k)).rootSet k := by
    rw [← h, mem_rootSet']
    exact ⟨(Polynomial.map_ne_zero_iff hinj).mpr (minpoly.ne_zero ha_int), minpoly.aeval _ _⟩
  rw [← orbit_image_eq_rootSet p k g hsep hsplit b] at ha_root
  obtain ⟨a', ha'_mem, ha'_eq⟩ := ha_root
  have haa : a' = a := Subtype.coe_injective ha'_eq
  rwa [haa] at ha'_mem

/-- **B5 (bijection, multiset form).** Mapping each orbit to the minpoly of a representative is a
bijection onto `normalizedFactors g`: the map is injective (B3 transitivity), lands in the factors
(B1), and hits every factor (B1 backward); both multisets are `nodup` (`g` separable), so equality
of supports gives equality of multisets. -/
theorem univ_map_minpoly_out_eq_normalizedFactors (g : (ZMod p)[X]) (hsep : g.Separable)
    (hsplit : (g.map (algebraMap (ZMod p) k)).Splits) :
    (Finset.univ.val.map fun ω : orbitRel.Quotient (Subgroup.zpowers (frobeniusPerm p k g))
        (g.rootSet k) => minpoly (ZMod p) ((Quotient.out ω : g.rootSet k) : k))
      = UniqueFactorizationMonoid.normalizedFactors g := by
  have hg0 : g ≠ 0 := hsep.ne_zero
  have hnodup_nf : (UniqueFactorizationMonoid.normalizedFactors g).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hg0).mp hsep.squarefree
  have hinj : Function.Injective (fun ω : orbitRel.Quotient
      (Subgroup.zpowers (frobeniusPerm p k g)) (g.rootSet k) =>
      minpoly (ZMod p) ((Quotient.out ω : g.rootSet k) : k)) := by
    intro ω₁ ω₂ hΨeq
    have hsame : Quotient.out ω₁ ∈ ω₂.orbit := by
      rw [orbitRel.Quotient.orbit_eq_orbit_out ω₂ Quotient.out_eq']
      exact sameOrbit_of_minpoly_eq p k g hsep hsplit hΨeq
    have h2 := orbitRel.Quotient.mem_orbit.mp hsame
    rwa [Quotient.out_eq'] at h2
  rw [Multiset.Nodup.ext (Finset.univ.nodup.map hinj) hnodup_nf]
  intro q
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨ω, -, rfl⟩
    exact minpoly_mem_normalizedFactors p k g hg0 (Quotient.out ω)
  · intro hq
    obtain ⟨γ, hγ⟩ := exists_root_minpoly_eq p k g hg0 hsplit hq
    let ω₀ : orbitRel.Quotient (Subgroup.zpowers (frobeniusPerm p k g)) (g.rootSet k) :=
      Quotient.mk'' γ
    have hmem : Quotient.out ω₀ ∈ orbit (Subgroup.zpowers (frobeniusPerm p k g)) γ := by
      have hh : Quotient.out ω₀ ∈ ω₀.orbit :=
        orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' ω₀)
      rwa [show ω₀.orbit = orbit (Subgroup.zpowers (frobeniusPerm p k g)) γ from
        orbitRel.Quotient.orbit_mk γ] at hh
    exact ⟨ω₀, Finset.mem_univ_val _, by rw [← hγ]; exact minpoly_orbit_invariant p k g hmem⟩

/-- **L_b4 / T011.** For a separable `g : (ZMod p)[X]` that splits in the finite field `k`, the
cycle-type partition of the residue Frobenius `frobeniusPerm` acting on the roots of `g` in `k`
equals the multiset of degrees of the monic irreducible factors of `g` over `𝔽ₚ`.

Each monic irreducible factor of degree `d` has its `d` distinct roots in `k` (it splits, `g`
separable) forming a single `⟨x ↦ xᵖ⟩`-orbit — a `d`-cycle — because the roots of a degree-`d`
irreducible over `𝔽ₚ` are `{γ, γᵖ, …, γ^{p^{d-1}}}` and `orderOf` of the Frobenius on `γ` is
`[𝔽ₚ(γ):𝔽ₚ] = d` (`FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic`). Distinct factors give
disjoint orbits partitioning the root set, so the partition is exactly the factor-degree multiset
(degree-`1` factors are the fixed points, kept by `partition` — not `cycleType`). -/
theorem frobeniusPerm_partition_parts_eq_factor_degrees (g : (ZMod p)[X]) (hsep : g.Separable)
    (hsplit : (g.map (algebraMap (ZMod p) k)).Splits) :
    (frobeniusPerm p k g).partition.parts =
      (UniqueFactorizationMonoid.normalizedFactors g).map Polynomial.natDegree := by
  rw [partition_parts_eq_orbit_card,
    ← univ_map_minpoly_out_eq_normalizedFactors p k g hsep hsplit, Multiset.map_map]
  exact Multiset.map_congr rfl (fun ω _ => natCard_orbit_eq_natDegree p k g ω)

end FrobeniusPerm

section Dedekind

open NumberField UniqueFactorizationMonoid

/-- The splitting field of a rational polynomial is a number field (`FiniteDimensional` is already a
Mathlib instance, `CharZero` holds as a `ℚ`-algebra). -/
instance splittingField_numberField (g : ℚ[X]) : NumberField g.SplittingField := ⟨⟩

/-- **T013 helper.** For a multiset `s` of irreducible polynomials over `𝔽ₚ`, the degrees of the
normalized factors of their product equal the degrees of the members of `s`. This turns the abstract
`normalizedFactors (f mod p)` appearing in R3 into the concrete factor-degree multiset that a
certificate supplies (monic irreducible witnesses whose product is `f mod p`). -/
theorem normalizedFactors_prod_map_natDegree {p : ℕ} [Fact p.Prime] (s : Multiset (ZMod p)[X])
    (hs : ∀ q ∈ s, Irreducible q) :
    (normalizedFactors s.prod).map Polynomial.natDegree = s.map Polynomial.natDegree := by
  rw [normalizedFactors_prod_eq s hs, Multiset.map_map]
  exact Multiset.map_congr rfl fun q _ =>
    natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (normalize_associated q))

/-- **L_b2 core (Conrad step 6).** Reduction modulo a prime `𝔔` lying over `p` intertwines the
arithmetic Frobenius `σ = arithFrobAt` with the `p`-power (residue Frobenius) map:
`π (σ • x) = (π x) ^ p` in the residue field `𝓞E ⧸ 𝔔`. This is the algebraic heart of Dedekind's
theorem; combined with the reduction bijection on root sets it yields the cycle-type statement. -/
theorem reduction_arithFrob_eq_pow (p : ℕ) [Fact p.Prime] {E : Type*} [Field E] [NumberField E]
    [IsGalois ℚ E] [Algebra.IsInvariant ℤ (𝓞 E) (E ≃ₐ[ℚ] E)]
    (𝔔 : Ideal (𝓞 E)) [𝔔.IsPrime] [Finite (𝓞 E ⧸ 𝔔)]
    (hlies : 𝔔.under ℤ = Ideal.span {(p : ℤ)}) (x : 𝓞 E) :
    Ideal.Quotient.mk 𝔔 ((arithFrobAt ℤ (E ≃ₐ[ℚ] E) 𝔔) • x) = (Ideal.Quotient.mk 𝔔 x) ^ p := by
  have h := (IsArithFrobAt.arithFrobAt ℤ (E ≃ₐ[ℚ] E) 𝔔).mk_apply x
  calc Ideal.Quotient.mk 𝔔 ((arithFrobAt ℤ (E ≃ₐ[ℚ] E) 𝔔) • x)
      = Ideal.Quotient.mk 𝔔
          ((MulSemiringAction.toAlgHom ℤ (𝓞 E) (arithFrobAt ℤ (E ≃ₐ[ℚ] E) 𝔔)) x) := rfl
    _ = (Ideal.Quotient.mk 𝔔 x) ^ Nat.card (ℤ ⧸ 𝔔.under ℤ) := h
    _ = (Ideal.Quotient.mk 𝔔 x) ^ p := by
        have hq : Nat.card (ℤ ⧸ 𝔔.under ℤ) = p := by
          have e : (ℤ ⧸ Ideal.span {(p : ℤ)}) ≃+* ZMod p := Int.quotientSpanEquivZMod p
          rw [hlies, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card]
        rw [hq]

/-- A ring hom applied to a product of linear factors `∏ (X - C a)` distributes as
`∏ (X - C (φ a))`. Used to descend the `E`-factorization of `f` through `𝓞 E` and then mod `𝔔`. -/
theorem map_prod_X_sub_C {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (m : Multiset R) :
    ((m.map fun a => X - C a).prod).map φ = ((m.map φ).map fun a => X - C a).prod := by
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
  intro a _
  simp [Function.comp, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

/-- If a prime `𝔔` of a `ℤ`-algebra `A` lies over `p` (its contraction to `ℤ` is `span {p}`), then
`p` vanishes in the residue ring, so `A ⧸ 𝔔` has characteristic `p`. -/
private theorem charP_residue_of_under_eq_span {A : Type*} [CommRing A] [Algebra ℤ A] (p : ℕ)
    [hp : Fact p.Prime] (𝔔 : Ideal A) [𝔔.IsPrime] (hlies : 𝔔.under ℤ = Ideal.span {(p : ℤ)}) :
    CharP (A ⧸ 𝔔) p := by
  have hmem : ((p : ℕ) : A) ∈ 𝔔 := by
    have h1 : ((p : ℤ)) ∈ 𝔔.under ℤ := by rw [hlies]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap] at h1
    have h2 : algebraMap ℤ A (p : ℤ) = ((p : ℕ) : A) := by push_cast; ring
    rwa [h2] at h1
  have h0 : ((p : ℕ) : A ⧸ 𝔔) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk 𝔔) p]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  exact (CharP.charP_iff_prime_eq_zero hp.out).mpr h0

/-- A prime `𝔔` of a `ℤ`-algebra `A` (into which `ℤ` maps injectively) lying over a nonzero `p` is
itself nonzero: its contraction `span {p} ≠ ⊥` forces `𝔔 ≠ ⊥`. -/
private theorem ne_bot_of_under_eq_span {A : Type*} [CommRing A] [Algebra ℤ A] (p : ℕ)
    (hp0 : p ≠ 0) (hinj : Function.Injective (algebraMap ℤ A)) (𝔔 : Ideal A)
    (hlies : 𝔔.under ℤ = Ideal.span {(p : ℤ)}) : 𝔔 ≠ ⊥ := by
  rintro rfl
  have hunder : (⊥ : Ideal A).under ℤ = ⊥ := by
    rw [Ideal.under, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hinj
  rw [hunder] at hlies
  exact hp0 (by exact_mod_cast (Ideal.span_singleton_eq_bot).mp hlies.symm)

variable (p : ℕ) [hp : Fact p.Prime] (f : ℤ[X]) (hf : f.Monic)
    (hsepf : (f.map (Int.castRingHom (ZMod p))).Separable)
    [Fact (((f.map (Int.castRingHom ℚ)).map
      (algebraMap ℚ (f.map (Int.castRingHom ℚ)).SplittingField)).Splits)]
    [IsGalois ℚ (f.map (Int.castRingHom ℚ)).SplittingField]
    [Algebra.IsInvariant ℤ (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField)
      ((f.map (Int.castRingHom ℚ)).SplittingField ≃ₐ[ℚ]
        (f.map (Int.castRingHom ℚ)).SplittingField)]
    (𝔔 : Ideal (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField)) [hQp : 𝔔.IsPrime]
    [Finite (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField ⧸ 𝔔)]
    (hlies : 𝔔.under ℤ = Ideal.span {(p : ℤ)})

omit [IsGalois ℚ (f.map (Int.castRingHom ℚ)).SplittingField]
  [Algebra.IsInvariant ℤ (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField)
    ((f.map (Int.castRingHom ℚ)).SplittingField ≃ₐ[ℚ] (f.map (Int.castRingHom ℚ)).SplittingField)]
  [Finite (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField ⧸ 𝔔)] in
include hf hsepf in
open scoped Classical in
/-- The `𝓞E`-factorisation of `f` and its reduction. Writing `E` for the splitting field, there is a
multiset `M` of algebraic-integer roots of `f` such that `f` (mapped to `𝓞E`) is `∏ (X - m)`; hence
reducing mod `𝔔` factors `f mod p` over the residue field `𝓞E ⧸ 𝔔` as `∏ (X - m̄)`, and these reduced
roots are distinct (`f mod p` is separable). Membership in `M` is exactly being a root of `f` in `E`;
this characterisation is what the injectivity/surjectivity of the reduction map in
`exists_reduction_rootSet_equiv_permCongr` consume. -/
private theorem exists_reductionRoots_prod [𝔔.IsMaximal]
    [Algebra (ZMod p) (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField ⧸ 𝔔)] :
    ∃ M : Multiset (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField),
      (∀ x : 𝓞 (f.map (Int.castRingHom ℚ)).SplittingField,
          x ∈ M ↔ (aeval (x : (f.map (Int.castRingHom ℚ)).SplittingField)) f = 0) ∧
      (f.map (Int.castRingHom (ZMod p))).map
          (algebraMap (ZMod p) (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField ⧸ 𝔔))
        = ((M.map (Ideal.Quotient.mk 𝔔)).map fun a => X - C a).prod ∧
      (M.map (Ideal.Quotient.mk 𝔔)).Nodup := by
  classical
  set E := (f.map (Int.castRingHom ℚ)).SplittingField
  have hmapℤE : f.map (algebraMap ℤ E)
      = (f.map (Int.castRingHom ℚ)).map (algebraMap ℚ E) := by
    rw [Polynomial.map_map]
    exact congrArg (Polynomial.map · f) (Subsingleton.elim _ _)
  have hsplitE : (f.map (algebraMap ℤ E)).Splits := by rw [hmapℤE]; exact Fact.out
  have hmonicE : (f.map (algebraMap ℤ E)).Monic := hf.map _
  have hFE : f.map (algebraMap ℤ E)
      = ((f.map (algebraMap ℤ E)).roots.map fun a => X - C a).prod :=
    hsplitE.eq_prod_roots_of_monic hmonicE
  have hrootint : ∀ a ∈ (f.map (algebraMap ℤ E)).roots, IsIntegral ℤ a := by
    intro a ha
    have haroot : eval a (f.map (algebraMap ℤ E)) = 0 :=
      (Polynomial.mem_roots hmonicE.ne_zero).mp ha
    rw [Polynomial.eval_map] at haroot
    exact ⟨f, hf, haroot⟩
  set M : Multiset (𝓞 E) :=
    (f.map (algebraMap ℤ E)).roots.pmap (fun a ha => (⟨a, ha⟩ : 𝓞 E)) hrootint with hMdef
  have hMmap : M.map (algebraMap (𝓞 E) E) = (f.map (algebraMap ℤ E)).roots := by
    rw [hMdef]
    erw [Multiset.map_pmap]
    change Multiset.pmap (fun a (_ : IsIntegral ℤ a) => a)
      (f.map (algebraMap ℤ E)).roots hrootint = _
    rw [Multiset.pmap_eq_map, Multiset.map_id']
  have hF𝓞 : f.map (algebraMap ℤ (𝓞 E)) = (M.map fun a => X - C a).prod := by
    apply Polynomial.map_injective (algebraMap (𝓞 E) E) RingOfIntegers.coe_injective
    rw [map_prod_X_sub_C, hMmap, Polynomial.map_map,
      show (algebraMap (𝓞 E) E).comp (algebraMap ℤ (𝓞 E)) = algebraMap ℤ E from
        Subsingleton.elim _ _]
    exact hFE
  have hg_eq : (f.map (Int.castRingHom (ZMod p))).map (algebraMap (ZMod p) (𝓞 E ⧸ 𝔔))
      = (f.map (algebraMap ℤ (𝓞 E))).map (Ideal.Quotient.mk 𝔔) := by
    rw [Polynomial.map_map, Polynomial.map_map]
    exact congrArg (Polynomial.map · f) (Subsingleton.elim _ _)
  have hFk : (f.map (Int.castRingHom (ZMod p))).map (algebraMap (ZMod p) (𝓞 E ⧸ 𝔔))
      = ((M.map (Ideal.Quotient.mk 𝔔)).map fun a => X - C a).prod := by
    rw [hg_eq, hF𝓞, map_prod_X_sub_C]
  have hSnodup : (M.map (Ideal.Quotient.mk 𝔔)).Nodup := by
    have hsep : ((f.map (Int.castRingHom (ZMod p))).map
        (algebraMap (ZMod p) (𝓞 E ⧸ 𝔔))).Separable := hsepf.map
    rw [hFk] at hsep
    have hnd := Polynomial.nodup_roots hsep
    rwa [Polynomial.roots_multiset_prod_X_sub_C] at hnd
  refine ⟨M, fun x => ?_, hFk, hSnodup⟩
  rw [hMdef]
  erw [Multiset.mem_pmap]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have haroot : eval a (f.map (algebraMap ℤ E)) = 0 :=
      (Polynomial.mem_roots hmonicE.ne_zero).mp ha
    rw [Polynomial.eval_map, ← Polynomial.aeval_def] at haroot
    exact haroot
  · intro hx
    have hmem : (x : E) ∈ (f.map (algebraMap ℤ E)).roots := by
      rw [Polynomial.mem_roots hmonicE.ne_zero, Polynomial.IsRoot.def, Polynomial.eval_map,
        ← Polynomial.aeval_def]
      exact hx
    exact ⟨(x : E), hmem, RingOfIntegers.coe_injective rfl⟩

include hp hf hsepf hlies in
open scoped Classical in
/-- **L_b3 / T010.** The reduction `𝓞E → 𝓞E ⧸ 𝔔 =: k` restricts to a Frobenius-equivariant
bijection from the roots of `f` in the splitting field `E` to the roots of `f mod p` in the residue
field `k`, carrying the Galois Frobenius permutation `galActionHom σ` (`σ = arithFrobAt`) to the
residue Frobenius `frobeniusPerm` (`x ↦ xᵖ`). Reduction lands in `k` because roots are algebraic
integers; it is injective because `p ∤ disc f` keeps the roots distinct mod `𝔔`; it is onto because
`f = ∏(X − rᵢ)` reduces to a splitting of `f mod p` over `k`. Equivariance is L_b2
(`reduction_arithFrob_eq_pow`). -/
theorem exists_reduction_rootSet_equiv_permCongr [𝔔.IsMaximal]
    [Algebra (ZMod p) (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField ⧸ 𝔔)] :
    ∃ e : (f.map (Int.castRingHom ℚ)).rootSet (f.map (Int.castRingHom ℚ)).SplittingField ≃
        (f.map (Int.castRingHom (ZMod p))).rootSet
          (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField ⧸ 𝔔),
      ((f.map (Int.castRingHom (ZMod p))).map (algebraMap (ZMod p)
          (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField ⧸ 𝔔))).Splits ∧
      frobeniusPerm p (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField ⧸ 𝔔)
          (f.map (Int.castRingHom (ZMod p))) =
        e.permCongr (Polynomial.Gal.galActionHom (f.map (Int.castRingHom ℚ))
          (f.map (Int.castRingHom ℚ)).SplittingField
          (arithFrobAt ℤ ((f.map (Int.castRingHom ℚ)).SplittingField ≃ₐ[ℚ]
            (f.map (Int.castRingHom ℚ)).SplittingField) 𝔔)) := by
  classical
  set E := (f.map (Int.castRingHom ℚ)).SplittingField
  set g := f.map (Int.castRingHom (ZMod p)) with hgdef
  set σ := arithFrobAt ℤ (E ≃ₐ[ℚ] E) 𝔔
  have hroot : ∀ r : (f.map (Int.castRingHom ℚ)).rootSet E, (aeval (r : E)) f = 0 := by
    intro r
    have h := Polynomial.aeval_eq_zero_of_mem_rootSet r.2
    rw [Polynomial.aeval_def, Polynomial.eval₂_map] at h
    rwa [Subsingleton.elim ((algebraMap ℚ E).comp (Int.castRingHom ℚ)) (algebraMap ℤ E),
      ← Polynomial.aeval_def] at h
  have hint : ∀ r : (f.map (Int.castRingHom ℚ)).rootSet E, IsIntegral ℤ (r : E) :=
    fun r => ⟨f, hf, hroot r⟩
  let lift : (f.map (Int.castRingHom ℚ)).rootSet E → 𝓞 E := fun r => ⟨(r : E), hint r⟩
  have hmem : ∀ r, (Ideal.Quotient.mk 𝔔 (lift r)) ∈ g.rootSet (𝓞 E ⧸ 𝔔) := by
    intro r
    rw [Polynomial.mem_rootSet']
    refine ⟨(((hf.map _).map _).ne_zero), ?_⟩
    have e2 : (Polynomial.aeval (lift r)) f = 0 := by
      have hinj : Function.Injective (algebraMap (𝓞 E) E) := RingOfIntegers.coe_injective
      apply hinj
      rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂,
        Subsingleton.elim ((algebraMap (𝓞 E) E).comp (algebraMap ℤ (𝓞 E))) (algebraMap ℤ E)]
      show eval₂ (algebraMap ℤ E) (r : E) f = 0
      rw [← Polynomial.aeval_def]
      exact hroot r
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      Subsingleton.elim ((algebraMap (ZMod p) (𝓞 E ⧸ 𝔔)).comp (Int.castRingHom (ZMod p)))
        ((Ideal.Quotient.mk 𝔔).comp (algebraMap ℤ (𝓞 E))),
      ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, e2, map_zero]
  let ρ : (f.map (Int.castRingHom ℚ)).rootSet E → g.rootSet (𝓞 E ⧸ 𝔔) :=
    fun r => ⟨Ideal.Quotient.mk 𝔔 (lift r), hmem r⟩
  have hσroot : ∀ y : (f.map (Int.castRingHom ℚ)).rootSet E,
      σ (y : E) ∈ (f.map (Int.castRingHom ℚ)).rootSet E := by
    intro y
    have hy : (aeval (y : E)) (f.map (Int.castRingHom ℚ)) = 0 :=
      Polynomial.aeval_eq_zero_of_mem_rootSet y.2
    rw [Polynomial.mem_rootSet']
    refine ⟨(Polynomial.mem_rootSet'.mp y.2).1, ?_⟩
    rw [show σ (y : E) = σ.toAlgHom (y : E) from rfl, Polynomial.aeval_algHom_apply, hy, map_zero]
  let Hσ : (f.map (Int.castRingHom ℚ)).rootSet E → (f.map (Int.castRingHom ℚ)).rootSet E :=
    fun y => ⟨σ (y : E), hσroot y⟩
  have hequiv : ∀ y, frobeniusPerm p (𝓞 E ⧸ 𝔔) g (ρ y) = ρ (Hσ y) := by
    intro y
    apply Subtype.ext
    rw [frobeniusPerm_coe_apply]
    show (Ideal.Quotient.mk 𝔔 (lift y)) ^ p = Ideal.Quotient.mk 𝔔 (lift (Hσ y))
    have hlifteq : lift (Hσ y) = σ • (lift y) := by
      apply RingOfIntegers.coe_injective
      rw [show (algebraMap (𝓞 E) E) (σ • lift y) = σ (y : E) from rfl]
      rfl
    rw [hlifteq]
    exact (reduction_arithFrob_eq_pow p 𝔔 hlies (lift y)).symm
  obtain ⟨M, hMmem, hFk0, hSnodup⟩ := exists_reductionRoots_prod p f hf hsepf 𝔔
  have hFk : g.map (algebraMap (ZMod p) (𝓞 E ⧸ 𝔔))
      = ((M.map (Ideal.Quotient.mk 𝔔)).map fun a => X - C a).prod := hFk0
  have hmonick : (g.map (algebraMap (ZMod p) (𝓞 E ⧸ 𝔔))).Monic :=
    (hf.map (Int.castRingHom (ZMod p))).map (algebraMap (ZMod p) (𝓞 E ⧸ 𝔔))
  have hmemM : ∀ r0 : (f.map (Int.castRingHom ℚ)).rootSet E, lift r0 ∈ M :=
    fun r0 => (hMmem (lift r0)).mpr (hroot r0)
  have hρinj : Function.Injective ρ := by
    intro r r' hrr'
    have h1 : Ideal.Quotient.mk 𝔔 (lift r) = Ideal.Quotient.mk 𝔔 (lift r') :=
      Subtype.ext_iff.mp hrr'
    have hlift_eq : lift r = lift r' :=
      Multiset.inj_on_of_nodup_map hSnodup (lift r) (hmemM r) (lift r') (hmemM r') h1
    exact Subtype.ext (congrArg (algebraMap (𝓞 E) E) hlift_eq)
  have hρsurj : Function.Surjective ρ := by
    intro s0
    have haeval : (aeval (s0 : 𝓞 E ⧸ 𝔔)) g = 0 := (Polynomial.mem_rootSet'.mp s0.2).2
    have hs0mem : (s0 : 𝓞 E ⧸ 𝔔) ∈ M.map (Ideal.Quotient.mk 𝔔) := by
      rw [← Polynomial.roots_multiset_prod_X_sub_C (M.map (Ideal.Quotient.mk 𝔔)), ← hFk,
        Polynomial.mem_roots hmonick.ne_zero, Polynomial.IsRoot.def, Polynomial.eval_map,
        ← Polynomial.aeval_def]
      exact haeval
    rw [Multiset.mem_map] at hs0mem
    obtain ⟨m, hmM, hmk⟩ := hs0mem
    have ha_rootSet : (m : E) ∈ (f.map (Int.castRingHom ℚ)).rootSet E := by
      rw [Polynomial.mem_rootSet']
      refine ⟨((hf.map (Int.castRingHom ℚ)).map (algebraMap ℚ E)).ne_zero, ?_⟩
      rw [Polynomial.aeval_def, Polynomial.eval₂_map,
        Subsingleton.elim ((algebraMap ℚ E).comp (Int.castRingHom ℚ)) (algebraMap ℤ E),
        ← Polynomial.aeval_def]
      exact (hMmem m).mp hmM
    refine ⟨⟨(m : E), ha_rootSet⟩, ?_⟩
    apply Subtype.ext
    show Ideal.Quotient.mk 𝔔 (lift ⟨(m : E), ha_rootSet⟩) = (s0 : 𝓞 E ⧸ 𝔔)
    have hlm : lift ⟨(m : E), ha_rootSet⟩ = m := RingOfIntegers.coe_injective rfl
    rw [hlm]; exact hmk
  have hbij : Function.Bijective ρ := ⟨hρinj, hρsurj⟩
  refine ⟨(Polynomial.Gal.rootsEquivRootsAux (f.map (Int.castRingHom ℚ)) E).symm.trans
      (Equiv.ofBijective ρ hbij), ?_, ?_⟩
  · rw [Polynomial.splits_iff_exists_multiset]
    refine ⟨M.map (Ideal.Quotient.mk 𝔔), ?_⟩
    rw [hmonick.leadingCoeff, Polynomial.C_1, one_mul]
    exact hFk
  · have hfun : ∀ r : (f.map (Int.castRingHom ℚ)).rootSet E,
        frobeniusPerm p (𝓞 E ⧸ 𝔔) g
            (((Polynomial.Gal.rootsEquivRootsAux (f.map (Int.castRingHom ℚ)) E).symm.trans
              (Equiv.ofBijective ρ hbij)) r)
          = ((Polynomial.Gal.rootsEquivRootsAux (f.map (Int.castRingHom ℚ)) E).symm.trans
              (Equiv.ofBijective ρ hbij))
              (Polynomial.Gal.galActionHom (f.map (Int.castRingHom ℚ)) E σ r) := by
      intro r
      show frobeniusPerm p (𝓞 E ⧸ 𝔔) g
          (ρ ((Polynomial.Gal.rootsEquivRootsAux (f.map (Int.castRingHom ℚ)) E).symm r))
        = ρ ((Polynomial.Gal.rootsEquivRootsAux (f.map (Int.castRingHom ℚ)) E).symm
            (Polynomial.Gal.galActionHom (f.map (Int.castRingHom ℚ)) E σ r))
      rw [hequiv ((Polynomial.Gal.rootsEquivRootsAux (f.map (Int.castRingHom ℚ)) E).symm r)]
      congr 1
      -- `galActionHom σ` unfolds definitionally to `rootsEquivRootsAux ∘ Hσ ∘ rootsEquivRootsAux.symm`.
      rw [show Polynomial.Gal.galActionHom (f.map (Int.castRingHom ℚ)) E σ r
            = Polynomial.Gal.rootsEquivRootsAux (f.map (Int.castRingHom ℚ)) E
                (Hσ ((Polynomial.Gal.rootsEquivRootsAux (f.map (Int.castRingHom ℚ)) E).symm r))
          from rfl,
        Equiv.symm_apply_apply]
    apply Equiv.ext
    intro s
    rw [Equiv.permCongr_apply]
    have h := hfun (((Polynomial.Gal.rootsEquivRootsAux (f.map (Int.castRingHom ℚ)) E).symm.trans
      (Equiv.ofBijective ρ hbij)).symm s)
    rwa [Equiv.apply_symm_apply] at h

include hp hf hsepf hlies in
open scoped Classical in
/-- **R3 main / T012.** Dedekind's theorem: the cycle-type partition of an arithmetic Frobenius
`σ = arithFrobAt` acting on the roots of `f` in its splitting field equals the multiset of degrees of
the monic irreducible factors of `f mod p`. Hypotheses: `f` monic, `f mod p` separable (`p ∤ disc f`,
via `SeparableReduction`), and `𝔔` a prime of `𝓞E` lying over `p` (`hlies`). The splitting/Galois
structure of `E = (f mod ℚ).SplittingField` is supplied by instances. The residue field `k = 𝓞E ⧸ 𝔔`
is set up as a finite `𝔽ₚ`-algebra, then L_b3 (reduction bijection) + `partition_parts_permCongr`
(conjugacy transport) + L_b4 (residue-Frobenius partition = factor degrees) compose. -/
theorem galActionHom_arithFrob_partition_eq_factor_degrees :
    (Polynomial.Gal.galActionHom (f.map (Int.castRingHom ℚ))
        (f.map (Int.castRingHom ℚ)).SplittingField
        (arithFrobAt ℤ ((f.map (Int.castRingHom ℚ)).SplittingField ≃ₐ[ℚ]
          (f.map (Int.castRingHom ℚ)).SplittingField) 𝔔)).partition.parts =
      (normalizedFactors (f.map (Int.castRingHom (ZMod p)))).map Polynomial.natDegree := by
  classical
  haveI : IsDomain (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField ⧸ 𝔔) :=
    Ideal.Quotient.isDomain 𝔔
  have hinj : Function.Injective
      (algebraMap ℤ (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField)) := RingHom.injective_int _
  haveI : 𝔔.IsMaximal := hQp.isMaximal (ne_bot_of_under_eq_span p hp.out.ne_zero hinj 𝔔 hlies)
  haveI : CharP (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField ⧸ 𝔔) p :=
    charP_residue_of_under_eq_span p 𝔔 hlies
  haveI : Algebra (ZMod p) (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField ⧸ 𝔔) :=
    ZMod.algebra _ p
  obtain ⟨e, hsplit, hperm⟩ := exists_reduction_rootSet_equiv_permCongr p f hf hsepf 𝔔 hlies
  rw [← partition_parts_permCongr e, ← hperm]
  exact frobeniusPerm_partition_parts_eq_factor_degrees p _ _ hsepf hsplit

include hp hf hsepf in
open scoped Classical in
/-- **R3 existence form (toward T013).** The user need not exhibit the prime `𝔔`: for any monic `f`
with `f mod p` separable, there EXISTS an arithmetic Frobenius `σ` in the Galois group whose
cycle-type partition on the roots is the multiset of factor degrees of `f mod p`. A prime `𝔔` of
`𝓞E` lying over `p` is produced by going-up (`Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain`),
its residue field is finite (`Ideal.finiteQuotientOfFreeOfNeBot`, `𝓞E` free of finite rank over `ℤ`),
and `σ = arithFrobAt ℤ (E ≃ₐ[ℚ] E) 𝔔`; then R3 main applies. -/
theorem exists_galActionHom_partition_eq_factor_degrees :
    ∃ σ : (f.map (Int.castRingHom ℚ)).Gal,
      (Polynomial.Gal.galActionHom (f.map (Int.castRingHom ℚ))
          (f.map (Int.castRingHom ℚ)).SplittingField σ).partition.parts =
        (normalizedFactors (f.map (Int.castRingHom (ZMod p)))).map Polynomial.natDegree := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  haveI hpp : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp hp.out)
  have hinj : Function.Injective
      (algebraMap ℤ (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField)) := RingHom.injective_int _
  have hker : RingHom.ker (algebraMap ℤ (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField))
      ≤ Ideal.span {(p : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le
  obtain ⟨𝔔, h𝔔p, h𝔔comap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (Ideal.span {(p : ℤ)}) (S := 𝓞 (f.map (Int.castRingHom ℚ)).SplittingField) hker
  haveI : 𝔔.IsPrime := h𝔔p
  have hlies : 𝔔.under ℤ = Ideal.span {(p : ℤ)} := h𝔔comap
  have hbot : 𝔔 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.under, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp hinj] at hlies
    exact hp0 ((Ideal.span_singleton_eq_bot).mp hlies.symm)
  haveI : Finite (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField ⧸ 𝔔) :=
    Ideal.finiteQuotientOfFreeOfNeBot 𝔔 hbot
  exact ⟨arithFrobAt ℤ ((f.map (Int.castRingHom ℚ)).SplittingField ≃ₐ[ℚ]
      (f.map (Int.castRingHom ℚ)).SplittingField) 𝔔,
    galActionHom_arithFrob_partition_eq_factor_degrees p f hf hsepf 𝔔 hlies⟩

end Dedekind

end IdealArithmetic.Galois
