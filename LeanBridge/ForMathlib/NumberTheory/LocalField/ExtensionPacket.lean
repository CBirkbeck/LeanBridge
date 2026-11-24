import LeanBridge.ForMathlib.NumberTheory.LocalField.HiddenSlopes
import LeanBridge.ForMathlib.NumberTheory.LocalField.ResidualPolynomialTransportFamily
import LeanBridge.ForMathlib.NumberTheory.LocalField.TameUnramifiedDegree

/-!
# Packets in a family of extensions of `p`-adic fields

Let `K` be a `p`-adic field and `I / K` the family of a Herbrand invariant `I` at the residue
characteristic of `K` (LMFDB `lf.family_polynomial`): the `K`-isomorphism classes of the extensions
of `K` inside `K̄` with Herbrand invariant `I`. LMFDB `lf.packet` puts two elements `L₁ / K` and
`L₂ / K` of `I / K` in the same packet when their residual polynomials are equivalent and they have
the same hidden invariants: the Galois groups of their Galois closures are isomorphic as
permutation groups, the Galois closures have the same residue field degree and the same
ramification index, and `L₁ / K` and `L₂ / K` have the same hidden slopes. "Thus the family `I / K`
is partitioned into packets."

The equivalence of residual polynomials is read as lying in a common subfamily of `I / K` (LMFDB
`lf.subfamily`): two members of `I / K` do exactly when their classes of residual polynomials, read
over the residue field of the unramified extension `K_f` of degree `f`, differ by an element of
`Gal(K_f / K)`, and, for `f = 1`, exactly when they are equal. Isomorphism as permutation groups is
defined for any two extensions of a field, through the actions of the Galois groups of their Galois
closures on their embeddings; it is the relation the LMFDB tests through transitive group labels
`nTj`. Each of the five conditions is an invariant of the `K`-isomorphism classes, so the packet
relation is an equivalence relation on `I / K`, and its classes partition `I / K`.

## Main definitions

* `Algebra.GaloisPermIsomorphic` (LMFDB `lf.packet`, `group.permutation_representation`): the
  Galois groups of the Galois closures of two extensions are isomorphic as permutation groups.
* `IsNonarchimedeanLocalField.HerbrandInvariant.SamePacket` (LMFDB `lf.packet`): two classes of
  extensions are in the same packet of `I / K`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.packets` (LMFDB `lf.packet`): the packets of
  `I / K`.

## Main results

* `Algebra.galoisPermIsomorphic_of_algEquiv` (LMFDB `lf.packet`): isomorphic extensions have
  isomorphic Galois permutation groups.
* `IsNonarchimedeanLocalField.galoisUnramifiedDegree_eq_of_algEquiv`,
  `IsNonarchimedeanLocalField.ramificationIndex_galoisClosure_eq_of_algEquiv`,
  `IsNonarchimedeanLocalField.hiddenSwanSlopes_eq_of_algEquiv` and
  `IsNonarchimedeanLocalField.hiddenArtinSlopes_eq_of_algEquiv` (LMFDB `lf.packet`): the residue
  degree and the ramification index of the Galois closure and the hidden slopes are invariants of
  the `K`-isomorphism class.
* `IsNonarchimedeanLocalField.HerbrandInvariant.exists_mem_subfamilies_iff` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.exists_mem_subfamilies_iff_of_f_eq_one` (LMFDB
  `lf.packet`, `lf.field.label`): two members of `I / K` lie in a common subfamily exactly when
  their classes of residual polynomials differ by an element of `Gal(K_f / K)`, and, for `f = 1`,
  exactly when they are equal.
* `IsNonarchimedeanLocalField.HerbrandInvariant.samePacket_mk_iff` (LMFDB `lf.packet`): the packet
  relation does not depend on the members of the classes.
* `IsNonarchimedeanLocalField.HerbrandInvariant.isPartition_packets` (LMFDB `lf.packet`): the
  packets partition `I / K`.

## References

* J. Guàrdia, J. W. Jones, K. Keating, S. Pauli, D. P. Roberts and D. Roe, *Families of p-adic
  fields*, arXiv:2507.02360, §4.1.
-/

open Polynomial TauCeti ValuativeRel

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace Algebra

variable (K : Type*) [Field K] (E₁ E₂ E₃ : Type*) [Field E₁] [Field E₂] [Field E₃] [Algebra K E₁]
  [Algebra K E₂] [Algebra K E₃]

/-- The **Galois groups of the Galois closures of two extensions are isomorphic as permutation
groups** (LMFDB `lf.packet`, `group.permutation_representation`): for extensions `E₁` and `E₂` of a
field `K`, with Galois closures `E₁^Gal` and `E₂^Gal` in `K̄`, there are an isomorphism
`ψ : Gal(E₁^Gal / K) ≃ Gal(E₂^Gal / K)` and a bijection `β` from the `K`-embeddings of `E₁` into
`E₁^Gal` to those of `E₂` into `E₂^Gal` such that `β (g ∘ ι) = ψ(g) ∘ β(ι)`: the permutation
representations of the Galois groups on the embeddings, of degree `[E_i : K]` for separable `E_i`,
are isomorphic. The LMFDB compares them through their transitive group labels `nTj`. -/
def GaloisPermIsomorphic : Prop :=
  ∃ (ψ : Gal(galoisClosure K E₁/K) ≃* Gal(galoisClosure K E₂/K))
    (β : (E₁ →ₐ[K] galoisClosure K E₁) ≃ (E₂ →ₐ[K] galoisClosure K E₂)),
    ∀ (g : Gal(galoisClosure K E₁/K)) (ι : E₁ →ₐ[K] galoisClosure K E₁),
      β ((g : galoisClosure K E₁ →ₐ[K] galoisClosure K E₁).comp ι) =
        (ψ g : galoisClosure K E₂ →ₐ[K] galoisClosure K E₂).comp (β ι)

lemma galoisPermIsomorphic_refl : GaloisPermIsomorphic K E₁ E₁ :=
  ⟨MulEquiv.refl _, Equiv.refl _, fun _ _ ↦ rfl⟩

variable {K E₁ E₂ E₃}

lemma GaloisPermIsomorphic.symm (h : GaloisPermIsomorphic K E₁ E₂) :
    GaloisPermIsomorphic K E₂ E₁ := by
  rcases h with ⟨ψ, β, hβ⟩
  refine ⟨ψ.symm, β.symm, fun g ι ↦ β.injective ?_⟩
  rw [hβ, Equiv.apply_symm_apply, MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]

lemma GaloisPermIsomorphic.trans (h : GaloisPermIsomorphic K E₁ E₂)
    (h' : GaloisPermIsomorphic K E₂ E₃) : GaloisPermIsomorphic K E₁ E₃ := by
  rcases h with ⟨ψ, β, hβ⟩
  rcases h' with ⟨ψ', β', hβ'⟩
  exact ⟨ψ.trans ψ', β.trans β', fun g ι ↦ (congrArg β' (hβ g ι)).trans (hβ' (ψ g) (β ι))⟩

/-- **Isomorphic extensions have isomorphic Galois permutation groups** (LMFDB `lf.packet`): for a
`K`-isomorphism `σ : E₁ ≃ E₂`, the Galois closures of `E₁` and `E₂` in `K̄` are equal, and
`ι ↦ ι ∘ σ⁻¹`, read in the common Galois closure, is a bijection between the `K`-embeddings of `E₁`
and of `E₂` compatible with the actions of the Galois group. -/
lemma galoisPermIsomorphic_of_algEquiv (σ : E₁ ≃ₐ[K] E₂) : GaloisPermIsomorphic K E₁ E₂ := by
  let e : galoisClosure K E₁ ≃ₐ[K] galoisClosure K E₂ :=
    IntermediateField.equivOfEq (galoisClosure_eq_of_algEquiv σ)
  exact ⟨AlgEquiv.autCongr e, AlgEquiv.arrowCongr σ e, fun g ι ↦ AlgHom.ext fun x ↦
    congrArg (fun z ↦ e (g z)) (e.symm_apply_apply (ι (σ.symm x))).symm⟩

end Algebra

namespace IsNonarchimedeanLocalField

section Invariance

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {E E' M M' : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K E]
  [FiniteDimensional K E'] [FiniteDimensional K M] [FiniteDimensional K M']

lemma inertiaDegree_eq_of_eq (h : M = M') : inertiaDegree K M = inertiaDegree K M' := by
  subst h
  rfl

lemma ramificationIndex_eq_of_eq (h : M = M') :
    TauCeti.ramificationIndex K M = TauCeti.ramificationIndex K M' := by
  subst h
  rfl

/-- **The Galois unramified degree is an invariant of the isomorphism class** (LMFDB `lf.packet`,
`lf.unramified_degree`): `K`-isomorphic extensions `E` and `E'` of a nonarchimedean local field `K`
inside `K̄` have the same Galois closure `L^Gal`, so the same residue degree `f(L^Gal / K)`. -/
lemma galoisUnramifiedDegree_eq_of_algEquiv (σ : E ≃ₐ[K] E') :
    galoisUnramifiedDegree K E' = galoisUnramifiedDegree K E :=
  inertiaDegree_eq_of_eq (Algebra.galoisClosure_eq_of_algEquiv σ).symm

/-- **The ramification index of the Galois closure is an invariant of the isomorphism class**
(LMFDB `lf.packet`): `K`-isomorphic extensions `E` and `E'` of a nonarchimedean local field `K`
inside `K̄` have the same Galois closure `L^Gal`, so the same ramification index `e(L^Gal / K)`. -/
lemma ramificationIndex_galoisClosure_eq_of_algEquiv (σ : E ≃ₐ[K] E') : TauCeti.ramificationIndex
    K (Algebra.galoisClosure K E') = TauCeti.ramificationIndex K (Algebra.galoisClosure K E) :=
  ramificationIndex_eq_of_eq (Algebra.galoisClosure_eq_of_algEquiv σ).symm

variable [Algebra.IsSeparable K E] [Algebra.IsSeparable K E']

/-- **The hidden Swan slopes are an invariant of the isomorphism class** (LMFDB `lf.packet`,
`lf.hidden_slopes`): `K`-isomorphic finite separable extensions `E` and `E'` of a nonarchimedean
local field `K` inside `K̄` have the same Galois closure, so the same Galois Swan slopes, and the
same Swan slopes, so the same hidden Swan slopes. -/
lemma hiddenSwanSlopes_eq_of_algEquiv (σ : E ≃ₐ[K] E') :
    hiddenSwanSlopes E' = hiddenSwanSlopes E := by
  rw [hiddenSwanSlopes, hiddenSwanSlopes, galoisSwanSlopes, galoisSwanSlopes,
    Algebra.galoisClosure_eq_of_algEquiv σ, hullWildSwanSlopes_eq_visibleSwanSlopes E,
    hullWildSwanSlopes_eq_visibleSwanSlopes E', visibleSwanSlopes_eq_of_algEquiv σ]

/-- **The hidden Artin slopes are an invariant of the isomorphism class** (LMFDB `lf.packet`,
`lf.hidden_slopes`): they are the hidden Swan slopes plus `1`. -/
lemma hiddenArtinSlopes_eq_of_algEquiv (σ : E ≃ₐ[K] E') :
    hiddenArtinSlopes E' = hiddenArtinSlopes E := by
  rw [← map_add_one_hiddenSwanSlopes, ← map_add_one_hiddenSwanSlopes,
    hiddenSwanSlopes_eq_of_algEquiv σ]

lemma hiddenArtinSlopes_eq_iff :
    hiddenArtinSlopes E' = hiddenArtinSlopes E ↔ hiddenSwanSlopes E' = hiddenSwanSlopes E := by
  rw [← map_add_one_hiddenSwanSlopes, ← map_add_one_hiddenSwanSlopes]
  exact (Multiset.map_injective (add_left_injective 1)).eq_iff

end Invariance

namespace HerbrandInvariant

section Residual

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] {p : ℕ} {I : HerbrandInvariant p} {E₁ E₂ : IntermediateField K (AlgebraicClosure K)}
  [FiniteDimensional K E₁] [FiniteDimensional K E₂] (hE₁ : I.IsInvariantOf K E₁)
  (hE₂ : I.IsInvariantOf K E₂) {α₁ : 𝒪[E₁]} {α₂ : 𝒪[E₂]}

/-- **Equivalent residual polynomials** (LMFDB `lf.packet`, `lf.field.label`): two extensions `E₁`
and `E₂` in the family `I / K`, with uniformisers `α₁` and `α₂`, lie in a common subfamily of
`I / K` exactly when their classes of residual polynomials, read over the residue field of `K_f`,
differ by an element of `Gal(K_f / K)`, a power of Frobenius on the residue field. -/
lemma exists_mem_subfamilies_iff (hp : ringChar 𝓀[K] = p) (hα₁ : Irreducible α₁)
    (hα₂ : Irreducible α₂) : (∃ S ∈ I.subfamilies K,
      ⟦(⟨E₁, inferInstance⟩ : FiniteExtension K)⟧ ∈ S ∧
      ⟦(⟨E₂, inferInstance⟩ : FiniteExtension K)⟧ ∈ S) ↔
      ∃ g : Gal(unramifiedExtension K (AlgebraicClosure K) I.f/K), hE₂.residualClass α₂ = List.map
        (map (g.toAlgHom.residueFieldHom : _ →+* _)) '' hE₁.residualClass α₁ := by
  have h₁ : ⟦(⟨E₁, inferInstance⟩ : FiniteExtension K)⟧ ∈ I.subfamily K (hE₁.residualClass α₁) :=
    (mk_mem_subfamily_residualClass_iff hE₁ hE₁ hp hα₁ hα₁).mpr
      ⟨1, (image_map_residueFieldHom_one _ _).symm⟩
  have hS₁ : I.subfamily K (hE₁.residualClass α₁) ∈ I.subfamilies K :=
    ⟨⟨E₁, inferInstance⟩, hE₁, α₁, hα₁, rfl⟩
  refine ⟨fun ⟨S, hS, hS₁', hS₂⟩ ↦ ?_, fun h ↦ ⟨_, hS₁, h₁,
    (mk_mem_subfamily_residualClass_iff hE₂ hE₁ hp hα₂ hα₁).mpr h⟩⟩
  rw [eq_of_mem_subfamilies hp hS hS₁ hS₁' h₁] at hS₂
  exact (mk_mem_subfamily_residualClass_iff hE₂ hE₁ hp hα₂ hα₁).mp hS₂

/-- **Equivalent residual polynomials for `f = 1`** (LMFDB `lf.packet`): for a family `I / K` of
residue degree `f = 1`, two extensions `E₁` and `E₂` in `I / K` lie in a common subfamily exactly
when their classes of residual polynomials, at any uniformisers, are equal. -/
lemma exists_mem_subfamilies_iff_of_f_eq_one (hp : ringChar 𝓀[K] = p) (hf : I.f = 1)
    (hα₁ : Irreducible α₁) (hα₂ : Irreducible α₂) : (∃ S ∈ I.subfamilies K,
      ⟦(⟨E₁, inferInstance⟩ : FiniteExtension K)⟧ ∈ S ∧
      ⟦(⟨E₂, inferInstance⟩ : FiniteExtension K)⟧ ∈ S) ↔
      hE₂.residualClass α₂ = hE₁.residualClass α₁ := by
  rw [exists_mem_subfamilies_iff hE₁ hE₂ hp hα₁ hα₂]
  refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun h ↦ ⟨1, by rwa [image_map_residueFieldHom_one]⟩⟩
  rwa [eq_one_of_f_eq_one g hf, image_map_residueFieldHom_one] at hg

end Residual

section Packet

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] {p : ℕ} (I : HerbrandInvariant p)

/-- Two classes `c₁` and `c₂` of finite extensions of a `p`-adic field `K` are **in the same
packet** of the family `I / K` (LMFDB `lf.packet`) when they have members `E₁` and `E₂` inside `K̄`
such that
* `c₁` and `c₂` lie in a common subfamily of `I / K`: their residual polynomials are equivalent
  (`IsNonarchimedeanLocalField.HerbrandInvariant.exists_mem_subfamilies_iff`);
* the Galois groups of the Galois closures `E₁^Gal` and `E₂^Gal` are isomorphic as permutation
  groups;
* `E₁^Gal / K` and `E₂^Gal / K` have the same residue field degree;
* `E₁^Gal / K` and `E₂^Gal / K` have the same ramification index;
* `E₁ / K` and `E₂ / K` have the same hidden Swan slopes, equivalently the same hidden Artin slopes.

Each condition is an invariant of the `K`-isomorphism classes, so the choice of members does not
matter (`IsNonarchimedeanLocalField.HerbrandInvariant.samePacket_mk_iff`). -/
def SamePacket (c₁ c₂ : ExtensionClass K) : Prop :=
  ∃ E₁ E₂ : FiniteExtension K, ⟦E₁⟧ = c₁ ∧ ⟦E₂⟧ = c₂ ∧
    haveI : FiniteDimensional K E₁.1 := E₁.2
    haveI : FiniteDimensional K E₂.1 := E₂.2
    (∃ S ∈ I.subfamilies K, c₁ ∈ S ∧ c₂ ∈ S) ∧ Algebra.GaloisPermIsomorphic K E₁.1 E₂.1 ∧
      galoisUnramifiedDegree K E₁.1 = galoisUnramifiedDegree K E₂.1 ∧
      TauCeti.ramificationIndex K (Algebra.galoisClosure K E₁.1) =
        TauCeti.ramificationIndex K (Algebra.galoisClosure K E₂.1) ∧
      hiddenSwanSlopes E₁.1 = hiddenSwanSlopes E₂.1

/-- The **packets** of the family `I / K` (LMFDB `lf.packet`): the classes of the relation
`IsNonarchimedeanLocalField.HerbrandInvariant.SamePacket` on `I / K`. -/
def packets : Set (Set (I.family K)) :=
  {S | ∃ c : I.family K, S = {c' | I.SamePacket K c'.1 c.1}}

variable {K I} {c₁ c₂ c₃ : ExtensionClass K}

/-- **The packet relation does not depend on the members** (LMFDB `lf.packet`): for members `E₁`
and `E₂` of two classes, the classes are in the same packet exactly when `E₁` and `E₂` themselves
satisfy the five conditions, which are invariants of the `K`-isomorphism classes. -/
lemma samePacket_mk_iff {E₁ E₂ : FiniteExtension K} : I.SamePacket K ⟦E₁⟧ ⟦E₂⟧ ↔
    haveI : FiniteDimensional K E₁.1 := E₁.2
    haveI : FiniteDimensional K E₂.1 := E₂.2
    (∃ S ∈ I.subfamilies K, ⟦E₁⟧ ∈ S ∧ ⟦E₂⟧ ∈ S) ∧ Algebra.GaloisPermIsomorphic K E₁.1 E₂.1 ∧
      galoisUnramifiedDegree K E₁.1 = galoisUnramifiedDegree K E₂.1 ∧
      TauCeti.ramificationIndex K (Algebra.galoisClosure K E₁.1) =
        TauCeti.ramificationIndex K (Algebra.galoisClosure K E₂.1) ∧
      hiddenSwanSlopes E₁.1 = hiddenSwanSlopes E₂.1 := by
  have hfin₁ : FiniteDimensional K E₁.1 := E₁.2
  have hfin₂ : FiniteDimensional K E₂.1 := E₂.2
  refine ⟨?_, fun h ↦ ⟨E₁, E₂, rfl, rfl, h⟩⟩
  rintro ⟨E₁', E₂', h₁, h₂, hS, hG, hf, he, hH⟩
  have hfin₁' : FiniteDimensional K E₁'.1 := E₁'.2
  have hfin₂' : FiniteDimensional K E₂'.1 := E₂'.2
  rcases Quotient.exact h₁ with ⟨σ₁⟩
  rcases Quotient.exact h₂ with ⟨σ₂⟩
  refine ⟨hS, ((Algebra.galoisPermIsomorphic_of_algEquiv σ₁).symm.trans hG).trans
    (Algebra.galoisPermIsomorphic_of_algEquiv σ₂), ?_, ?_, ?_⟩
  · rw [galoisUnramifiedDegree_eq_of_algEquiv σ₁, hf, ← galoisUnramifiedDegree_eq_of_algEquiv σ₂]
  · rw [ramificationIndex_galoisClosure_eq_of_algEquiv σ₁, he,
      ← ramificationIndex_galoisClosure_eq_of_algEquiv σ₂]
  · rw [hiddenSwanSlopes_eq_of_algEquiv σ₁, hH, ← hiddenSwanSlopes_eq_of_algEquiv σ₂]

lemma samePacket_refl (hp : ringChar 𝓀[K] = p) (hc : c₁ ∈ I.family K) : I.SamePacket K c₁ c₁ := by
  rcases exists_mem_subfamilies hp hc with ⟨S, hS, hcS⟩
  rcases hc with ⟨E, -, rfl⟩
  exact ⟨E, E, rfl, rfl, ⟨S, hS, hcS, hcS⟩, Algebra.galoisPermIsomorphic_refl _ _, rfl, rfl, rfl⟩

lemma SamePacket.symm (h : I.SamePacket K c₁ c₂) : I.SamePacket K c₂ c₁ := by
  rcases h with ⟨E₁, E₂, h₁, h₂, ⟨S, hS, hS₁, hS₂⟩, hG, hf, he, hH⟩
  exact ⟨E₂, E₁, h₂, h₁, ⟨S, hS, hS₂, hS₁⟩, hG.symm, hf.symm, he.symm, hH.symm⟩

lemma SamePacket.trans (hp : ringChar 𝓀[K] = p) (h : I.SamePacket K c₁ c₂)
    (h' : I.SamePacket K c₂ c₃) : I.SamePacket K c₁ c₃ := by
  rcases h with ⟨E₁, E₂, rfl, rfl, ⟨S, hS, hS₁, hS₂⟩, hG, hf, he, hH⟩
  rcases h' with ⟨E₂', E₃, h₂, rfl, ⟨S', hS', hS₂', hS₃⟩, hG', hf', he', hH'⟩
  have hfin₂ : FiniteDimensional K E₂.1 := E₂.2
  have hfin₂' : FiniteDimensional K E₂'.1 := E₂'.2
  rcases Quotient.exact h₂ with ⟨σ⟩
  have hSS' : S = S' :=
    eq_of_mem_subfamilies hp hS hS' hS₂ (h₂ ▸ hS₂')
  refine ⟨E₁, E₃, rfl, rfl, ⟨S, hS, hS₁, hSS' ▸ hS₃⟩,
    hG.trans ((Algebra.galoisPermIsomorphic_of_algEquiv σ).symm.trans hG'), ?_, ?_, ?_⟩
  · rw [hf, galoisUnramifiedDegree_eq_of_algEquiv σ, hf']
  · rw [he, ramificationIndex_galoisClosure_eq_of_algEquiv σ, he']
  · rw [hH, hiddenSwanSlopes_eq_of_algEquiv σ, hH']

/-- **The family is partitioned into packets** (LMFDB `lf.packet`): for a family `I / K` of
extensions of a `p`-adic field `K`, at the residue characteristic of `K`, the relation of being in
the same packet is an equivalence relation on `I / K`, so its classes, the packets, partition
`I / K`. -/
lemma isPartition_packets (hp : ringChar 𝓀[K] = p) : Setoid.IsPartition (I.packets K) :=
  Setoid.isPartition_classes (⟨fun c c' ↦ I.SamePacket K c.1 c'.1, ⟨fun c ↦ samePacket_refl hp c.2,
    fun h ↦ h.symm, fun h h' ↦ h.trans hp h'⟩⟩ : Setoid (I.family K))

end Packet

end HerbrandInvariant

end IsNonarchimedeanLocalField
