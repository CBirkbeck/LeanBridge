import LeanBridge.ForMathlib.NumberTheory.LocalField.MongeRepresentationProof

/-!
# The families of extensions of a `p`-adic field are finite

Let `K` be a `p`-adic field and `I = (r_1, …, r_w)_ε^f` a Herbrand invariant. The family `I / K`
(LMFDB `lf.family_polynomial`) is the set of `K`-isomorphism classes of the extensions of `K` of
residue degree `f`, ramification index `ε p ^ w` and Swan slopes those of `I`
(`IsNonarchimedeanLocalField.HerbrandInvariant.family`), the Swan slopes of an extension being
Deligne's positive upper ramification breaks (`IsNonarchimedeanLocalField.visibleSwanSlopes`); that
these are the slopes of the lower convex hull of LMFDB `lf.slopes`, through which the knowl defines
the family, is not proved. Its field count (LMFDB `lf.family_field_count`) is its number of elements
and its masses (LMFDB `lf.family_mass`) are sums over its elements, which presupposes that `I / K`
is finite. We prove that it is.

At the residue characteristic `p` of `K`, Monge's representation theorem
(`IsNonarchimedeanLocalField.HerbrandInvariant.mongeRepresentation`) writes every class in a
nonempty family `I / K` as `K_f(α)` for a root `α ∈ K̄` of a semicanonical polynomial over the ring
of integers of the unramified extension `K_f` of `K` of degree `f`, for one uniformiser and one
choice of representatives. The coefficients of a semicanonical polynomial lie in the set `ℛ` of
representatives of the residue field of `K_f`, which is finite, and a semicanonical polynomial
depends only on its coefficients `f_σ` at the finitely many indices `σ` of the generic polynomial.
So the semicanonical polynomials, whatever Monge's subgroups are, lie in one finite set of monic
polynomials of degree `e = ε p ^ w`, with finitely many roots in `K̄`, and `I / K` is finite. A
family at another prime `p` is contained in the family of the Herbrand invariant, at the residue
characteristic of `K`, of any of its members, so it is finite as well.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.finite_family`: the family `I / K` is finite.
* `IsNonarchimedeanLocalField.HerbrandInvariant.natCast_fieldCount` (LMFDB `lf.family_field_count`):
  the field count of `I / K` is its number of elements.
* `IsNonarchimedeanLocalField.HerbrandInvariant.mass_eq_sum` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.absoluteMass_eq_sum` (LMFDB `lf.family_mass`): the
  mass and the absolute mass of `I / K` are the finite sums of the masses and absolute masses of its
  elements.
-/

open Polynomial TauCeti ValuativeRel

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable {p : ℕ} {I : HerbrandInvariant p} {R : Type*} [CommRing R] {𝔪 : Ideal R}
  (C : I.MongeChoice 𝔪) (ϖ : R)

lemma MongeChoice.mem_reps_of_mem_coeffSet (W : ℕ → AddSubgroup (R ⧸ 𝔪)) {σ : ℕ} {r : R}
    (hr : r ∈ (C.toSemicanonicalChoice W).coeffSet σ) : r ∈ C.reps := by
  rw [SemicanonicalChoice.coeffSet] at hr
  split at hr
  · exact (C.unitReps_subset hr).1
  · exact hr.1
  · exact hr
  · exact C.cosetReps_subset _ hr
  · exact Set.mem_singleton_iff.mp hr ▸ C.zero_mem_reps

variable (I) in
lemma finite_specialisations {s : Set R} (hs : s.Finite) : {g : R[X] | ∃ f : ℕ → R,
    (∀ σ ∈ I.genericIndices, f σ ∈ s) ∧ I.specialisation ϖ f = g}.Finite := by
  have hs' : Finite s :=
    hs.to_subtype
  refine (Set.finite_range fun g : I.genericIndices → s ↦ I.specialisation ϖ
    (Function.extend Subtype.val (fun σ ↦ (g σ : R)) 0)).subset ?_
  rintro - ⟨f, hf, rfl⟩
  exact ⟨fun σ ↦ ⟨f σ, hf σ σ.2⟩, specialisation_congr ϖ fun σ hσ ↦
    Subtype.val_injective.extend_apply _ _ ⟨σ, hσ⟩⟩

variable (I) (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [CharZero K]

lemma finite_family_of_ringChar_eq (hp : ringChar 𝓀[K] = p) : (I.family K).Finite := by
  rcases (I.family K).eq_empty_or_nonempty with h | hne
  · exact h ▸ Set.finite_empty
  let Kf : IntermediateField K (AlgebraicClosure K) :=
    unramifiedExtension K (AlgebraicClosure K) I.f
  let vF : ValuativeRel Kf :=
    finiteIntermediateFieldValuativeRel K _ _
  let tF : TopologicalSpace Kf :=
    finiteIntermediateFieldTopology K _ _
  have hF : IsNonarchimedeanLocalField Kf :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  let aF : Algebra 𝒪[Kf] (AlgebraicClosure K) :=
    ((algebraMap Kf (AlgebraicClosure K)).comp (algebraMap 𝒪[Kf] Kf)).toAlgebra
  have hk : Finite (𝒪[Kf] ⧸ 𝓂[Kf]) :=
    inferInstanceAs (Finite 𝓀[Kf])
  rcases IsDiscreteValuationRing.exists_irreducible 𝒪[Kf] with ⟨ϖ, hϖ⟩
  rcases (nonempty_mongeChoice : Nonempty (I.MongeChoice 𝓂[Kf])) with ⟨C⟩
  have hs (α : AlgebraicClosure K) : {c : ExtensionClass K | ∃ E : FiniteExtension K, E.1 =
      (IntermediateField.adjoin Kf {α}).restrictScalars K ∧ Quotient.mk _ E = c}.Subsingleton := by
    rintro - ⟨E₁, h₁, rfl⟩ - ⟨E₂, h₂, rfl⟩
    exact congrArg _ <| Subtype.ext <| h₁.trans h₂.symm
  refine (((finite_specialisations I ϖ C.finite_reps).biUnion fun g _ ↦
    g.rootSet_finite (AlgebraicClosure K)).biUnion fun α _ ↦ (hs α).finite).subset ?_
  intro c hc
  rcases (mongeRepresentation I K hp hne ϖ hϖ C c).mp hc with ⟨α, E, hE, rfl, q, hq₀, f, hf, rfl⟩
  refine Set.mem_biUnion (Set.mem_biUnion ⟨f, fun σ hσ ↦ C.mem_reps_of_mem_coeffSet _ (hf σ hσ),
    rfl⟩ ?_) ⟨E, hE, rfl⟩
  have hp₀ : NeZero p :=
    ⟨hp ▸ (CharP.prime_ringChar 𝓀[K]).ne_zero⟩
  rw [← Subalgebra.coe_eq_zero, aeval_subalgebra_coe] at hq₀
  exact mem_rootSet'.mpr ⟨((monic_specialisation ϖ f).map _).ne_zero, hq₀⟩

variable {I K} in
lemma IsInvariantOf.of_isInvariantOf {p' : ℕ} {J : HerbrandInvariant p'}
    {L L' : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K L]
    [FiniteDimensional K L'] (hJ : J.IsInvariantOf K L) (hI : I.IsInvariantOf K L)
    (hI' : I.IsInvariantOf K L') : J.IsInvariantOf K L' := by
  rcases hJ with ⟨h₁, h₂, h₃⟩
  rcases hI with ⟨h₄, h₅, h₆⟩
  rcases hI' with ⟨h₇, h₈, h₉⟩
  rw [IsInvariantOf]
  exact ⟨h₇.trans (h₄.symm.trans h₁), h₈.trans (h₅.symm.trans h₂), h₉.trans (h₆.symm.trans h₃)⟩

/-- **The families of extensions of a `p`-adic field are finite**: for a `p`-adic field `K` and a
Herbrand invariant `I`, there are finitely many `K`-isomorphism classes of extensions in the family
`I / K`. At the residue characteristic of `K` this follows from Monge's representation theorem, the
semicanonical polynomials lying in a finite set of monic polynomials; a family at another prime lies
in the family of the Herbrand invariant of any of its members. -/
lemma finite_family : (I.family K).Finite := by
  rcases (I.family K).eq_empty_or_nonempty with h | ⟨-, E, hE, rfl⟩
  · exact h ▸ Set.finite_empty
  have hE₁ : FiniteDimensional K E.1 :=
    E.2
  refine (finite_family_of_ringChar_eq (visibleHerbrandInvariant E.1) K rfl).subset ?_
  rintro - ⟨E', hE', rfl⟩
  have hE'₁ : FiniteDimensional K E'.1 :=
    E'.2
  exact ⟨E', (isInvariantOf_visibleHerbrandInvariant E.1).of_isInvariantOf hE hE', rfl⟩

/-- **The field count of a family is its number of elements** (LMFDB `lf.family_field_count`): the
field count of `I / K`, defined as `Set.ncard`, is the cardinality `Set.encard` of `I / K`, which is
finite. -/
lemma natCast_fieldCount : (I.fieldCount K : ℕ∞) = (I.family K).encard :=
  (I.finite_family K).cast_ncard_eq

lemma fieldCount_eq_card_toFinset : I.fieldCount K = (I.finite_family K).toFinset.card :=
  (I.family K).ncard_eq_toFinset_card (I.finite_family K)

/-- **The mass of a family is the sum of the masses of its elements** (LMFDB `lf.family_mass`): the
mass of `I / K`, defined as a `finsum`, is the finite sum of the masses `1 / |Aut(L / K_f)|` over
the classes in `I / K`. -/
lemma mass_eq_sum : I.mass K = ∑ c ∈ (I.finite_family K).toFinset,
    c.liftOn (fun E ↦ extensionMass E.1 I.f) fun _ _ ⟨φ⟩ ↦ extensionMass_eq_of_algEquiv I.f φ :=
  finsum_mem_eq_finite_toFinset_sum _ _

variable [Fact p.Prime] [Algebra ℚ_[p] K] in
/-- **The absolute mass of a family is the sum of the absolute masses of its elements** (LMFDB
`lf.family_mass`): the absolute mass of `I / K`, defined as a `finsum`, is the finite sum of the
absolute masses `1 / |Aut(L / ℚ_p)|` over the classes in `I / K`. -/
lemma absoluteMass_eq_sum : I.absoluteMass K = ∑ c ∈ (I.finite_family K).toFinset,
    c.liftOn (fun E ↦ absoluteExtensionMass p E.1) fun _ _ ⟨φ⟩ ↦
      absoluteExtensionMass_eq_of_algEquiv p φ :=
  finsum_mem_eq_finite_toFinset_sum _ _

end IsNonarchimedeanLocalField.HerbrandInvariant
