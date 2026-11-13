import LeanBridge.ForMathlib.NumberTheory.LocalField.ExtensionFamilyFinite

/-!
# The mass of a family over its unramified extension

Let `K` be a `p`-adic field, `I = (r_1, …, r_w)_ε^f` a Herbrand invariant and `K_f` the unramified
extension of `K` of degree `f` inside `K̄`, which lies in every extension in the family `I / K`. The
mass of an extension `L` in `I / K` is `1 / |Aut(L / K_f)|` (LMFDB `lf.family_mass`,
`IsNonarchimedeanLocalField.extensionMass`). The knowl states that, for `K = ℚ_p`, the mass of the
family is `f` times its absolute mass, the sum of the `1 / |Aut(L / ℚ_p)|`; this is false for the
mass of the family as the knowl defines it, a sum over the `K`-isomorphism classes in `I / K` (see
`LeanBridge.ForMathlib.NumberTheory.LocalField.ExtensionFamily`), and true for the sum of the masses
over the `K_f`-isomorphism classes of the extensions in `I / K`, which we prove here.

Two finite extensions `L`, `L'` of `K` inside `K̄` containing `K_f` are `K_f`-isomorphic when there
is a `K`-isomorphism `L ≃ L'` fixing the elements of `K_f`; we take this relation, a `K`-isomorphism
fixing the elements of `L` in `K_f`, on all finite extensions of `K`
(`IsNonarchimedeanLocalField.fixingExtensionSetoid`), as `IsNonarchimedeanLocalField.extensionMass`
does for `Aut(L / K_f)`. The proof counts fields. For a finite extension `L` of `K` inside `K̄`, a
set `S ⊆ K̄` and the group `G_S` of the automorphisms of `L / K` fixing the elements of `L` in `S`,
the `K`-embeddings `L → K̄` fixing these elements are in bijection with the pairs of an extension
`L'` of `K` inside `K̄`, `K`-isomorphic to `L` by a map fixing them, and an element of `G_S`. So
there are `[L : K] / |Aut(L / K)|` extensions `K`-isomorphic to `L` (`S = ∅`), and
`[L : K_f] / |Aut(L / K_f)|` extensions `K_f`-isomorphic to `L` (`S = K_f`). Both masses therefore
count the `N` extensions inside `K̄` whose classes lie in `I / K`, all of degree `e f` over `K`,
`e = ε p ^ w`: the sum of the `1 / |Aut(L / K_f)|` over the `K_f`-classes is `N / e`, and the sum of
the `1 / |Aut(L / K)|` over the `K`-classes is `N / (e f)`.

## Main definitions

* `IsNonarchimedeanLocalField.fixingExtensionSetoid`: isomorphism over a normal subextension `E` of
  `K̄ / K`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.familyOverUnramified` (LMFDB `lf.family_mass`): the
  `K_f`-isomorphism classes of the extensions in `I / K`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.massOverUnramified` (LMFDB `lf.family_mass`): the
  sum of the masses over these classes.

## Main results

* `IsNonarchimedeanLocalField.natCard_fixingClass_mul_natCard_fixingSubgroup`: the extensions
  isomorphic to `L` by a map fixing a set `S`, counted by the embeddings of `L` fixing `S`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.massOverUnramified_eq_mul`: the sum of the masses
  over the `K_f`-classes is `f` times the sum of the `1 / |Aut(L / K)|` over `I / K`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.massOverUnramified_padic_eq` (LMFDB
  `lf.family_mass`): for `K = ℚ_p`, the sum of the masses over the `K_f`-classes is `f` times the
  absolute mass.
-/

open Finset TauCeti ValuativeRel

namespace IsNonarchimedeanLocalField

variable {K : Type*} [Field K] (S : Set (AlgebraicClosure K)) (L : FiniteExtension K)

lemma fieldRange_val_comp_algEquiv {L' : IntermediateField K (AlgebraicClosure K)}
    (g : L.1 ≃ₐ[K] L') : (L'.val.comp g.toAlgHom).fieldRange = L' := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨g.symm ⟨x, hx⟩, by simp⟩⟩
  rintro ⟨y, rfl⟩
  exact (g y).2

/-- **The extensions isomorphic to `L` by a map fixing a set `S`, counted by the embeddings of
`L`**: for a finite extension `L` of `K` inside `K̄` and a set `S ⊆ K̄`, the `K`-embeddings
`L → K̄` fixing the elements of `L` in `S` are in bijection with the pairs of an extension `L'` of
`K` inside `K̄` with a `K`-isomorphism `L ≃ L'` fixing them and of an automorphism of `L / K` fixing
them. -/
lemma natCard_fixingClass_mul_natCard_fixingSubgroup : Nat.card {L' : FiniteExtension K //
    ∃ φ : L.1 ≃ₐ[K] L'.1, ∀ x : L.1, (x : AlgebraicClosure K) ∈ S →
      (φ x : AlgebraicClosure K) = x} *
      Nat.card (fixingSubgroup (L.1 ≃ₐ[K] L.1) (((↑) : L.1 → AlgebraicClosure K) ⁻¹' S)) =
    Nat.card {τ : L.1 →ₐ[K] AlgebraicClosure K // ∀ x : L.1, (x : AlgebraicClosure K) ∈ S →
      τ x = x} := by
  rw [← Nat.card_prod]
  refine Nat.card_eq_of_bijective (fun y ↦ ⟨y.1.1.1.val.comp (y.2.1.trans y.1.2.choose).toAlgHom,
    fun x hx ↦ ?_⟩) ⟨?_, ?_⟩
  · have ha : y.2.1 x = x :=
      (mem_fixingSubgroup_iff _).mp y.2.2 x hx
    exact (congrArg (fun z ↦ (y.1.2.choose z : AlgebraicClosure K)) ha).trans
      (y.1.2.choose_spec x hx)
  · rintro ⟨⟨L₁, h₁⟩, a₁⟩ ⟨⟨L₂, h₂⟩, a₂⟩ h
    have h' : L₁.1.val.comp (a₁.1.trans h₁.choose).toAlgHom =
        L₂.1.val.comp (a₂.1.trans h₂.choose).toAlgHom :=
      congrArg Subtype.val h
    have hL : L₁ = L₂ :=
      Subtype.ext <| (fieldRange_val_comp_algEquiv L _).symm.trans <|
        (congrArg AlgHom.fieldRange h').trans <| fieldRange_val_comp_algEquiv L _
    subst hL
    have ha : a₁ = a₂ :=
      Subtype.ext <| AlgEquiv.ext fun x ↦ h₁.choose.injective <| Subtype.ext <|
        AlgHom.congr_fun h' x
    rw [ha]
  · rintro ⟨τ, hτ⟩
    have hfd : FiniteDimensional K L.1 :=
      L.2
    have hL' : ∃ φ : L.1 ≃ₐ[K] τ.fieldRange, ∀ x : L.1, (x : AlgebraicClosure K) ∈ S →
        (φ x : AlgebraicClosure K) = x :=
      ⟨τ.equivFieldRange, fun x hx ↦ hτ x hx⟩
    refine ⟨(⟨⟨τ.fieldRange, τ.equivFieldRange.toLinearEquiv.finiteDimensional⟩, hL'⟩,
      ⟨τ.equivFieldRange.trans hL'.choose.symm, ?_⟩), ?_⟩
    · refine (mem_fixingSubgroup_iff _).mpr fun x hx ↦ ?_
      have h₁ : hL'.choose x = τ.equivFieldRange x :=
        Subtype.ext <| (hL'.choose_spec x hx).trans (hτ x hx).symm
      rw [AlgEquiv.smul_def, AlgEquiv.trans_apply, ← h₁, AlgEquiv.symm_apply_apply]
    · refine Subtype.ext <| AlgHom.ext fun x ↦ ?_
      simp

variable [Algebra.IsSeparable K L.1]

lemma natCard_algHom_fixing_mul_finrank {E : IntermediateField K (AlgebraicClosure K)}
    (h : E ≤ L.1) : Nat.card {τ : L.1 →ₐ[K] AlgebraicClosure K // ∀ x : L.1,
      (x : AlgebraicClosure K) ∈ E → τ x = x} * Module.finrank K E = Module.finrank K L.1 := by
  let a : Algebra E L.1 :=
    (IntermediateField.inclusion h).toAlgebra
  have h₁ : IsScalarTower K E L.1 :=
    .of_algebraMap_eq fun _ ↦ rfl
  have h₂ : IsScalarTower E L.1 (AlgebraicClosure K) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have h₃ : FiniteDimensional K L.1 :=
    L.2
  have h₄ : FiniteDimensional E L.1 :=
    .of_restrictScalars_finite K E L.1
  have h₅ : Algebra.IsSeparable E L.1 :=
    Algebra.isSeparable_tower_top_of_isSeparable K E L.1
  rw [mul_comm, ← Module.finrank_mul_finrank K E L.1, ← AlgHom.card E L.1 (AlgebraicClosure K),
    ← Nat.card_eq_fintype_card]
  refine congrArg _ <| Nat.card_congr
    { toFun := fun τ ↦ { τ.1 with commutes' := fun r ↦ τ.2 _ r.2 }
      invFun := fun ψ ↦ ⟨ψ.restrictScalars K, fun x hx ↦
        (congrArg ψ (Subtype.ext rfl : algebraMap E L.1 ⟨x, hx⟩ = x)).symm.trans
          (ψ.commutes ⟨x, hx⟩)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

lemma natCard_algEquivClass_mul_natCard_algEquiv :
    Nat.card {L' // (finiteExtensionSetoid K).r L L'} * Nat.card (L.1 ≃ₐ[K] L.1) =
      Module.finrank K L.1 := by
  have hfd : FiniteDimensional K L.1 :=
    L.2
  have h₁ : Nat.card {L' // (finiteExtensionSetoid K).r L L'} = Nat.card {L' : FiniteExtension K //
      ∃ φ : L.1 ≃ₐ[K] L'.1, ∀ x : L.1, (x : AlgebraicClosure K) ∈ (∅ : Set (AlgebraicClosure K)) →
        (φ x : AlgebraicClosure K) = x} :=
    Nat.card_congr <| Equiv.subtypeEquivRight fun _ ↦
      ⟨fun ⟨φ⟩ ↦ ⟨φ, fun _ h ↦ h.elim⟩, fun ⟨φ, _⟩ ↦ ⟨φ⟩⟩
  have h₂ : Nat.card (L.1 ≃ₐ[K] L.1) =
      Nat.card (fixingSubgroup (L.1 ≃ₐ[K] L.1) (((↑) : L.1 → AlgebraicClosure K) ⁻¹' ∅)) := by
    rw [Set.preimage_empty, fixingSubgroup_empty, Subgroup.card_top]
  rw [h₁, h₂, natCard_fixingClass_mul_natCard_fixingSubgroup,
    ← AlgHom.card K L.1 (AlgebraicClosure K), ← Nat.card_eq_fintype_card]
  exact Nat.card_congr <| Equiv.subtypeUnivEquiv fun _ _ h ↦ h.elim

lemma sum_image_mul_eq_card {α β : Type*} [DecidableEq β] (s : Finset α) (g : α → β) (m : β → ℚ)
    {k : ℚ} (hm : ∀ x ∈ s, m (g x) * k = #{y ∈ s | g y = g x}) :
    (∑ c ∈ s.image g, m c) * k = #s := by
  rw [sum_mul, card_eq_sum_card_image g s, Nat.cast_sum]
  refine sum_congr rfl fun c hc ↦ ?_
  rcases mem_image.mp hc with ⟨x, hx, rfl⟩
  exact hm x hx

lemma card_filter_mk_eq_natCard {α : Type*} {r : Setoid α} [DecidableEq (Quotient r)] {T : Set α}
    (hT : T.Finite) {x : α} (hx : ∀ y, r.r x y → y ∈ T) :
    #{y ∈ hT.toFinset | Quotient.mk r y = Quotient.mk r x} = Nat.card {y // r.r x y} := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr <| Equiv.subtypeEquivRight fun y ↦ ?_
  rw [mem_filter, hT.mem_toFinset, Quotient.eq]
  exact ⟨fun h ↦ r.iseqv.symm h.2, fun h ↦ ⟨hx y h, r.iseqv.symm h⟩⟩

variable (K) in
/-- **Isomorphism over a normal subextension** `E` of `K̄ / K`, of finite extensions of `K` inside
`K̄`: `L` and `L'` are related if there is a `K`-isomorphism `L ≃ L'` fixing the elements of `L`
that lie in `E`. For `L` and `L'` containing `E`, such as the extensions in a family `I / K` and
`E = K_f`, these are the `E`-isomorphisms `L ≃ L'`. -/
def fixingExtensionSetoid (E : IntermediateField K (AlgebraicClosure K)) [Normal K E] :
    Setoid (FiniteExtension K) where
  r L L' := ∃ φ : L.1 ≃ₐ[K] L'.1, ∀ x : L.1, (x : AlgebraicClosure K) ∈ E →
    (φ x : AlgebraicClosure K) = x
  iseqv := ⟨fun _ ↦ ⟨.refl, fun _ _ ↦ rfl⟩, fun ⟨φ, hφ⟩ ↦ ⟨φ.symm, fun y hy ↦
    ((congrArg Subtype.val (φ.apply_symm_apply y)).symm.trans
      (hφ _ (coe_algEquiv_mem_of_normal φ.symm hy))).symm⟩,
    fun ⟨φ, hφ⟩ ⟨ψ, hψ⟩ ↦ ⟨φ.trans ψ, fun x hx ↦ (hψ (φ x) ((hφ x hx) ▸ hx)).trans (hφ x hx)⟩⟩

namespace HerbrandInvariant

variable {p : ℕ} (I : HerbrandInvariant p) (K) [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [CharZero K]

/-- The **`K_f`-isomorphism classes of the extensions in the family** `I / K` (LMFDB
`lf.family_mass`), `K_f` the unramified extension of `K` of degree `f` inside `K̄`: the classes, for
isomorphism over `K_f`, of the finite extensions of `K` inside `K̄` whose `K`-isomorphism class lies
in `I / K`. -/
noncomputable def familyOverUnramified :
    Set (Quotient (fixingExtensionSetoid K (unramifiedExtension K (AlgebraicClosure K) I.f))) :=
  Quotient.mk _ '' (Quotient.mk (finiteExtensionSetoid K) ⁻¹' I.family K)

/-- The **sum of the masses over the `K_f`-isomorphism classes** of the extensions in the family
`I / K` (LMFDB `lf.family_mass`): the sum of the masses `1 / |Aut(L / K_f)|` over
`familyOverUnramified`, well defined since `K_f`-isomorphic extensions are `K`-isomorphic, and `0`
if there were infinitely many classes. -/
noncomputable def massOverUnramified : ℚ :=
  ∑ᶠ c ∈ I.familyOverUnramified K, c.liftOn (fun E ↦ extensionMass E.1 I.f) fun _ _ ⟨φ, _⟩ ↦
    extensionMass_eq_of_algEquiv I.f φ

variable {I K} {E : FiniteExtension K}

lemma unramifiedExtension_le_of_mem_family (hE : Quotient.mk _ E ∈ I.family K) :
    unramifiedExtension K (AlgebraicClosure K) I.f ≤ E.1 := by
  rcases hE with ⟨E₀, hE₀, h⟩
  rcases Quotient.exact h with ⟨φ⟩
  have hE₀' : FiniteDimensional K E₀.1 :=
    E₀.2
  have hle : unramifiedExtension K (AlgebraicClosure K) I.f ≤ E₀.1 :=
    unramifiedExtension_le_of_isInvariantOf hE₀
  rw [← ((E.1.val.comp φ.toAlgHom).comp (IntermediateField.inclusion hle)).fieldRange_of_normal]
  rintro - ⟨x, rfl⟩
  exact (φ _).2

lemma finrank_of_mem_family (hE : Quotient.mk _ E ∈ I.family K) :
    Module.finrank K E.1 = I.ramificationIndex * I.f := by
  rcases hE with ⟨E₀, hE₀, h⟩
  rcases Quotient.exact h with ⟨φ⟩
  have hE₀' : FiniteDimensional K E₀.1 :=
    E₀.2
  let v : ValuativeRel E₀.1 :=
    finiteIntermediateFieldValuativeRel K _ E₀.1
  let t : TopologicalSpace E₀.1 :=
    finiteIntermediateFieldTopology K _ E₀.1
  have h₁ : IsNonarchimedeanLocalField E₀.1 :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ E₀.1
  have h₂ : ValuativeExtension K E₀.1 :=
    finiteIntermediateField_valuativeExtension K _ E₀.1
  rw [← φ.toLinearEquiv.finrank_eq, ← ramificationIndex_mul_inertiaDegree K E₀.1, hE₀.1, hE₀.2.1]
  rfl

lemma natCard_classOverUnramified_mul (hE : Quotient.mk _ E ∈ I.family K) : Nat.card {E' //
    (fixingExtensionSetoid K (unramifiedExtension K (AlgebraicClosure K) I.f)).r E E'} *
      Nat.card (fixingSubgroup (E.1 ≃ₐ[K] E.1)
        (((↑) : E.1 → AlgebraicClosure K) ⁻¹' unramifiedExtension K (AlgebraicClosure K) I.f)) =
    I.ramificationIndex := by
  have h : Nat.card {τ : E.1 →ₐ[K] AlgebraicClosure K // ∀ x : E.1,
      (x : AlgebraicClosure K) ∈ unramifiedExtension K (AlgebraicClosure K) I.f → τ x = x} * I.f =
      I.ramificationIndex * I.f := by
    rw [← finrank_of_mem_family hE,
      ← natCard_algHom_fixing_mul_finrank E (unramifiedExtension_le_of_mem_family hE),
      finrank_unramifiedExtension I.f_pos.ne']
  exact (natCard_fixingClass_mul_natCard_fixingSubgroup _ E).trans <|
    Nat.eq_of_mul_eq_mul_right I.f_pos h

variable (I K) in
lemma finite_preimage_family : (Quotient.mk (finiteExtensionSetoid K) ⁻¹' I.family K).Finite := by
  refine (I.finite_family K).preimage' fun c hc ↦ ?_
  rcases Quotient.mk_surjective c with ⟨E, rfl⟩
  have hfd : FiniteDimensional K E.1 :=
    E.2
  have h : Nat.card {E' // (finiteExtensionSetoid K).r E E'} ≠ 0 :=
    left_ne_zero_of_mul <| (natCard_algEquivClass_mul_natCard_algEquiv E).trans_ne
      Module.finrank_pos.ne'
  have hfin : Finite {E' // (finiteExtensionSetoid K).r E E'} :=
    Nat.finite_of_card_ne_zero h
  exact (Set.finite_coe_iff.mp hfin : {E' | (finiteExtensionSetoid K).r E E'}.Finite).subset
    fun E' hE' ↦ (finiteExtensionSetoid K).iseqv.symm (Quotient.exact hE')

variable (I K) in
/-- **The sum of the masses over the `K_f`-classes is `f` times the sum of the `1 / |Aut(L / K)|`**
over the family `I / K`, `K_f` the unramified extension of `K` of degree `f` inside `K̄`. Both sides
count the extensions inside `K̄` whose classes lie in `I / K`, all of degree `e f` over `K`: there
are `[L : K] / |Aut(L / K)|` extensions `K`-isomorphic to `L` and `[L : K_f] / |Aut(L / K_f)|`
extensions `K_f`-isomorphic to `L`. -/
lemma massOverUnramified_eq_mul : I.massOverUnramified K = I.f * ∑ᶠ c ∈ I.family K,
    c.liftOn (fun E ↦ (Nat.card (E.1 ≃ₐ[K] E.1) : ℚ)⁻¹) fun _ _ ⟨φ⟩ ↦
      congrArg (fun n : ℕ ↦ (n : ℚ)⁻¹) (Nat.card_congr φ.autCongr.toEquiv) := by
  classical
  rcases (I.family K).eq_empty_or_nonempty with h | ⟨-, E, hE, rfl⟩
  · simp [massOverUnramified, familyOverUnramified, h]
  have hfd : FiniteDimensional K E.1 :=
    E.2
  have hE' : Quotient.mk (finiteExtensionSetoid K) E ∈ I.family K :=
    ⟨E, hE, rfl⟩
  have he : (I.ramificationIndex : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr <| left_ne_zero_of_mul <|
      (finrank_of_mem_family hE').symm.trans_ne Module.finrank_pos.ne'
  have hT : (Quotient.mk (finiteExtensionSetoid K) ⁻¹' I.family K).Finite :=
    I.finite_preimage_family K
  have h₁ : I.massOverUnramified K * I.ramificationIndex = #hT.toFinset := by
    rw [massOverUnramified, familyOverUnramified, finsum_mem_eq_finite_toFinset_sum _ (hT.image _),
      hT.toFinset_image _]
    refine sum_image_mul_eq_card _ _ _ fun E hE ↦ ?_
    rw [hT.mem_toFinset] at hE
    have hfd : FiniteDimensional K E.1 :=
      E.2
    have hcl : ∀ E', (fixingExtensionSetoid K (unramifiedExtension K (AlgebraicClosure K) I.f)).r
        E E' → E' ∈ Quotient.mk (finiteExtensionSetoid K) ⁻¹' I.family K := fun E' ⟨φ, _⟩ ↦
      Set.mem_preimage.mpr <| (Quotient.sound ⟨φ⟩ : Quotient.mk (finiteExtensionSetoid K) E = _) ▸
        Set.mem_preimage.mp hE
    rw [card_filter_mk_eq_natCard hT hcl, ← natCard_classOverUnramified_mul hE, Nat.cast_mul,
      mul_comm, mul_assoc, Quotient.liftOn_mk, extensionMass,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), mul_one]
  have h₂ : (∑ᶠ c ∈ I.family K, c.liftOn (fun E ↦ (Nat.card (E.1 ≃ₐ[K] E.1) : ℚ)⁻¹)
      fun _ _ ⟨φ⟩ ↦ congrArg (fun n : ℕ ↦ (n : ℚ)⁻¹) (Nat.card_congr φ.autCongr.toEquiv)) *
        ((I.ramificationIndex * I.f : ℕ) : ℚ) = #hT.toFinset := by
    conv_lhs => rw [← Set.image_preimage_eq (I.family K) Quotient.mk_surjective]
    rw [finsum_mem_eq_finite_toFinset_sum _ (hT.image _), hT.toFinset_image _]
    refine sum_image_mul_eq_card _ _ _ fun E hE ↦ ?_
    rw [hT.mem_toFinset] at hE
    have hfd : FiniteDimensional K E.1 :=
      E.2
    have hcl : ∀ E', (finiteExtensionSetoid K).r E E' →
        E' ∈ Quotient.mk (finiteExtensionSetoid K) ⁻¹' I.family K := fun E' h ↦
      Set.mem_preimage.mpr <| (Quotient.sound h : Quotient.mk (finiteExtensionSetoid K) E = _) ▸
        Set.mem_preimage.mp hE
    rw [card_filter_mk_eq_natCard hT hcl, ← finrank_of_mem_family hE,
      ← natCard_algEquivClass_mul_natCard_algEquiv E, Nat.cast_mul, mul_comm, mul_assoc,
      Quotient.liftOn_mk, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), mul_one]
  refine mul_right_cancel₀ he ?_
  rw [h₁, ← h₂]
  push_cast
  ring1

variable (I) [Fact p.Prime] in
/-- **The mass over the `K_f`-classes of an absolute family is `f` times its absolute mass** (LMFDB
`lf.family_mass`, with the text corrected): for `K = ℚ_p`, the sum of the masses
`1 / |Aut(L / K_f)|` over the `K_f`-isomorphism classes of the extensions in `I / ℚ_p` is `f` times
the absolute mass of `I / ℚ_p`, the sum of the `1 / |Aut(L / ℚ_p)|` over `I / ℚ_p`. -/
lemma massOverUnramified_padic_eq : I.massOverUnramified ℚ_[p] = I.f * I.absoluteMass ℚ_[p] :=
  I.massOverUnramified_eq_mul ℚ_[p]

end HerbrandInvariant

end IsNonarchimedeanLocalField
