import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import TauCeti.RingTheory.Etale.Galois
import LeanBridge.ForMathlib.NumberTheory.NumberField.SexticTwin.Basic

/-!
# Galois descent for finite Galois sets and the twin of a sextic algebra

Let `Ω / F` be a Galois extension and `X` a finite set on which `Gal(Ω/F)` acts continuously, that
is with an open kernel. The `F`-algebra of `X`, the algebra of maps `f : X → Ω` with
`f (σ • x) = σ (f x)`, is the product over the orbits of `X` of the fixed fields of the
stabilizers of points of the orbits. It is a finite separable `F`-algebra of degree the size of
`X`, and its `F`-algebra maps to `Ω` are the evaluations at the points of `X`, so that its Galois
set is `X`.

Applied to the Galois set of a sextic algebra `A` twisted by the outer automorphism of `S₆`, with
`Ω` the separable closure of `F`, this shows that the twin of `A` is a finite separable algebra of
degree `6` whose Galois action is the twisted one, that is, a twin of `A` in the sense of
`Algebra.IsSexticTwin`. Conversely, by Galois descent in the other direction (Tau Ceti's
`Algebra.Etale.algHomEquivMulActionHom`), finite separable algebras with isomorphic Galois sets are
isomorphic, so that the twin of `A` is unique up to isomorphism.

## Main definitions

* `Algebra.galoisSetAlgebraEquivPi`: the `F`-algebra of a Galois set `X` is the product, over the
  orbits of `X`, of the fixed fields of the stabilizers of representatives.

## Main results

* `Algebra.finrank_galoisSetAlgebra`: the `F`-algebra of a finite Galois set `X` has dimension the
  size of `X`.
* `Algebra.etale_galoisSetAlgebra`: it is a finite separable (étale) `F`-algebra.
* `Algebra.bijective_evalGaloisSetAlgebra`: its `F`-algebra maps to `Ω` are the evaluations at the
  points of `X`, each once.
* `Algebra.Etale.natCard_algHom_separableClosure`: a finite separable `F`-algebra `A` has `[A : F]`
  algebra maps to the separable closure of `F`.
* `Algebra.finrank_sexticTwin` and `Algebra.etale_sexticTwin` (LMFDB `nf.sextic_twin`): the twin of
  a sextic algebra is a finite separable algebra of degree `6`.
* `Algebra.isSexticTwin_sexticTwin` (LMFDB `nf.sextic_twin`): it is a twin of the algebra.
* `Algebra.exists_isSexticTwin` (LMFDB `nf.sextic_twin`): every finite separable algebra of degree
  `6` has a twin, a finite separable algebra of degree `6`.
* `Algebra.IsSexticTwin.nonempty_algEquiv` (LMFDB `nf.sextic_twin`): two finite separable twins of
  an algebra are isomorphic.
-/

open Equiv IntermediateField MulAction Module

namespace Algebra

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {X : Type*}

section Action

variable [MulAction Gal(Ω/F) X]
  (a : Π ω : orbitRel.Quotient Gal(Ω/F) X, fixedField (stabilizer Gal(Ω/F) ω.out)) {x : X}

variable (F Ω x) in
private lemma exists_smul_out_mk_eq :
    ∃ σ : Gal(Ω/F), σ • (Quotient.mk'' x : orbitRel.Quotient Gal(Ω/F) X).out = x := by
  rcases mem_orbit_iff.mp <| orbitRel_apply.mp <| Quotient.mk_out' (s₁ := orbitRel Gal(Ω/F) X) x
    with ⟨σ, hσ⟩
  exact ⟨σ⁻¹, by rw [← hσ, inv_smul_smul]⟩

private lemma apply_eq_apply_of_smul_eq {r : X} {σ τ : Gal(Ω/F)} (h : σ • r = τ • r) {v : Ω}
    (hv : v ∈ fixedField (stabilizer Gal(Ω/F) r)) : σ v = τ v := by
  have hσ : τ⁻¹ * σ ∈ stabilizer Gal(Ω/F) r := by
    rw [mem_stabilizer_iff, mul_smul, h, inv_smul_smul]
  simpa using congrArg τ ((mem_fixedField_iff _ v).mp hv _ hσ)

variable (X x) in
/-- The value at a point `x` of a Galois set `X` of the element of its `F`-algebra with given
values `a ω` at the representatives `ω.out` of the orbits `ω`: `σ (a ω)` for `σ` sending the
representative of the orbit of `x` to `x`. -/
noncomputable def galoisSetAlgebraOfPiFun : Ω :=
  (exists_smul_out_mk_eq F Ω x).choose (a (Quotient.mk'' x))

lemma galoisSetAlgebraOfPiFun_eq {ω : orbitRel.Quotient Gal(Ω/F) X} {σ : Gal(Ω/F)}
    (hσ : σ • ω.out = x) : galoisSetAlgebraOfPiFun X a x = σ (a ω) := by
  have hx : Quotient.mk'' x = ω :=
    hσ ▸ (Quotient.sound' (orbitRel_apply.mpr (mem_orbit ω.out σ))).trans ω.out_eq'
  subst hx
  exact apply_eq_apply_of_smul_eq ((exists_smul_out_mk_eq F Ω x).choose_spec.trans hσ.symm) (a _).2

variable (x) in
lemma galoisSetAlgebraOfPiFun_smul (τ : Gal(Ω/F)) :
    galoisSetAlgebraOfPiFun X a (τ • x) = τ (galoisSetAlgebraOfPiFun X a x) :=
  (galoisSetAlgebraOfPiFun_eq a <| (mul_smul τ _ _).trans <|
    congrArg (τ • ·) (exists_smul_out_mk_eq F Ω x).choose_spec).trans (AlgEquiv.mul_apply _ _ _)

variable (X) in
/-- The element of the `F`-algebra of a Galois set `X` with given values `a ω` at the
representatives `ω.out` of the orbits `ω`, which must be fixed by the stabilizers of the
representatives. -/
noncomputable def galoisSetAlgebraOfPi :
    (Π ω : orbitRel.Quotient Gal(Ω/F) X, fixedField (stabilizer Gal(Ω/F) ω.out)) →ₐ[F]
      galoisSetAlgebra (toPermHom Gal(Ω/F) X) where
  toFun b := ⟨galoisSetAlgebraOfPiFun X b, fun τ y ↦ galoisSetAlgebraOfPiFun_smul b y τ⟩
  map_one' := Subtype.ext <| funext fun y ↦ map_one (exists_smul_out_mk_eq F Ω y).choose
  map_mul' b c := Subtype.ext <| funext fun y ↦ map_mul (exists_smul_out_mk_eq F Ω y).choose
    (b (Quotient.mk'' y) : Ω) (c (Quotient.mk'' y))
  map_zero' := Subtype.ext <| funext fun y ↦ map_zero (exists_smul_out_mk_eq F Ω y).choose
  map_add' b c := Subtype.ext <| funext fun y ↦ map_add (exists_smul_out_mk_eq F Ω y).choose
    (b (Quotient.mk'' y) : Ω) (c (Quotient.mk'' y))
  commutes' r := Subtype.ext <| funext fun y ↦ (exists_smul_out_mk_eq F Ω y).choose.commutes r

variable (X) in
/-- The values of an element of the `F`-algebra of a Galois set `X` at the representatives `ω.out`
of the orbits `ω`, which are fixed by the stabilizers of the representatives. -/
noncomputable def galoisSetAlgebraToPi : galoisSetAlgebra (toPermHom Gal(Ω/F) X) →ₐ[F]
    Π ω : orbitRel.Quotient Gal(Ω/F) X, fixedField (stabilizer Gal(Ω/F) ω.out) where
  toFun f ω := ⟨f.1 ω.out, (mem_fixedField_iff _ _).mpr fun σ hσ ↦
    (f.2 σ ω.out).symm.trans (congrArg f.1 hσ)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

variable (X) in
/-- **The `F`-algebra of a Galois set `X` is the product, over the orbits `ω` of `X`, of the fixed
fields of the stabilizers of representatives `ω.out`**, by evaluation at the representatives. -/
noncomputable def galoisSetAlgebraEquivPi : galoisSetAlgebra (toPermHom Gal(Ω/F) X) ≃ₐ[F]
    Π ω : orbitRel.Quotient Gal(Ω/F) X, fixedField (stabilizer Gal(Ω/F) ω.out) :=
  AlgEquiv.ofAlgHom (galoisSetAlgebraToPi X) (galoisSetAlgebraOfPi X)
    (AlgHom.ext fun b ↦ funext fun ω ↦ Subtype.ext <|
      (galoisSetAlgebraOfPiFun_eq b (one_smul _ ω.out)).trans (AlgEquiv.one_apply _))
    (AlgHom.ext fun f ↦ Subtype.ext <| funext fun y ↦
      (f.2 _ _).symm.trans (congrArg f.1 (exists_smul_out_mk_eq F Ω y).choose_spec))

variable [IsGalois F Ω]

lemma fixingSubgroup_fixedField_stabilizer (hx : IsOpen (stabilizer Gal(Ω/F) x).carrier) :
    (fixedField (stabilizer Gal(Ω/F) x)).fixingSubgroup = stabilizer Gal(Ω/F) x :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨_, Subgroup.isClosed_of_isOpen _ hx⟩

lemma finiteDimensional_fixedField_stabilizer (hx : IsOpen (stabilizer Gal(Ω/F) x).carrier) :
    FiniteDimensional F (fixedField (stabilizer Gal(Ω/F) x)) :=
  (InfiniteGalois.isOpen_iff_finite _).mp <| by
    rw [fixingSubgroup_fixedField_stabilizer hx]
    exact hx

lemma finrank_fixedField_stabilizer (hx : IsOpen (stabilizer Gal(Ω/F) x).carrier) :
    finrank F (fixedField (stabilizer Gal(Ω/F) x)) = Nat.card (orbit Gal(Ω/F) x) := by
  rw [finrank_eq_fixingSubgroup_index, fixingSubgroup_fixedField_stabilizer hx, index_stabilizer,
    Nat.card_coe_set_eq]

lemma etale_fixedField_stabilizer (hx : IsOpen (stabilizer Gal(Ω/F) x).carrier) :
    Algebra.Etale F (fixedField (stabilizer Gal(Ω/F) x)) := by
  have : FiniteDimensional F (fixedField (stabilizer Gal(Ω/F) x)) :=
    finiteDimensional_fixedField_stabilizer hx
  have : Algebra.IsSeparable F (fixedField (stabilizer Gal(Ω/F) x)) :=
    isSeparable_tower_bot_of_isSeparable F _ Ω
  exact ⟨FormallyEtale.of_isSeparable F _, FinitePresentation.of_finiteType.mp inferInstance⟩

lemma injective_evalGaloisSetAlgebra_toPermHom
    (hX : ∀ y : X, IsOpen (stabilizer Gal(Ω/F) y).carrier) :
    Function.Injective (evalGaloisSetAlgebra (toPermHom Gal(Ω/F) X)) := by
  classical
  intro y z hyz
  have key (b : Π ω : orbitRel.Quotient Gal(Ω/F) X, fixedField (stabilizer Gal(Ω/F) ω.out)) :
      galoisSetAlgebraOfPiFun X b y = galoisSetAlgebraOfPiFun X b z :=
    DFunLike.congr_fun hyz (galoisSetAlgebraOfPi X b)
  rcases exists_smul_out_mk_eq F Ω y with ⟨σ, hσ⟩
  have hω : (Quotient.mk'' z : orbitRel.Quotient Gal(Ω/F) X) = Quotient.mk'' y := by
    by_contra h
    have h1 : galoisSetAlgebraOfPiFun X (Pi.single (Quotient.mk'' y) 1) y =
        galoisSetAlgebraOfPiFun X (Pi.single (Quotient.mk'' y) 1) z :=
      key (Pi.single (Quotient.mk'' y) 1)
    rw [galoisSetAlgebraOfPiFun_eq _ hσ,
      galoisSetAlgebraOfPiFun_eq _ (exists_smul_out_mk_eq F Ω z).choose_spec, Pi.single_eq_same,
      Pi.single_eq_of_ne h] at h1
    simp at h1
  rcases mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact' hω)) with ⟨τ, rfl⟩
  have hfix :
      σ⁻¹ * τ * σ ∈ stabilizer Gal(Ω/F) (Quotient.mk'' y : orbitRel.Quotient Gal(Ω/F) X).out := by
    rw [← fixingSubgroup_fixedField_stabilizer (hX _), IntermediateField.mem_fixingSubgroup_iff]
    intro v hv
    have h1 : galoisSetAlgebraOfPiFun X (Pi.single (Quotient.mk'' y) ⟨v, hv⟩) y =
        galoisSetAlgebraOfPiFun X (Pi.single (Quotient.mk'' y) ⟨v, hv⟩) (τ • y) :=
      key (Pi.single (Quotient.mk'' y) ⟨v, hv⟩)
    rw [galoisSetAlgebraOfPiFun_smul, galoisSetAlgebraOfPiFun_eq _ hσ, Pi.single_eq_same] at h1
    simp [← h1]
  rw [mem_stabilizer_iff, mul_smul, mul_smul, hσ, inv_smul_eq_iff, hσ] at hfix
  exact hfix.symm

variable [Finite X]

lemma finrank_galoisSetAlgebra_toPermHom (hX : ∀ y : X, IsOpen (stabilizer Gal(Ω/F) y).carrier) :
    finrank F (galoisSetAlgebra (toPermHom Gal(Ω/F) X)) = Nat.card X := by
  have : ∀ y : X, FiniteDimensional F (fixedField (stabilizer Gal(Ω/F) y)) :=
    fun y ↦ finiteDimensional_fixedField_stabilizer (hX y)
  let _ : Fintype (orbitRel.Quotient Gal(Ω/F) X) := Fintype.ofFinite _
  rw [(galoisSetAlgebraEquivPi X).toLinearEquiv.finrank_eq, finrank_pi_fintype,
    Nat.card_congr (selfEquivSigmaOrbits Gal(Ω/F) X), Nat.card_sigma]
  exact Finset.sum_congr rfl fun ω _ ↦ finrank_fixedField_stabilizer (hX ω.out)

lemma etale_galoisSetAlgebra_toPermHom (hX : ∀ y : X, IsOpen (stabilizer Gal(Ω/F) y).carrier) :
    Algebra.Etale F (galoisSetAlgebra (toPermHom Gal(Ω/F) X)) := by
  have : ∀ y : X, Algebra.Etale F (fixedField (stabilizer Gal(Ω/F) y)) :=
    fun y ↦ etale_fixedField_stabilizer (hX y)
  exact Etale.of_equiv (galoisSetAlgebraEquivPi X).symm

lemma bijective_evalGaloisSetAlgebra_toPermHom
    (hX : ∀ y : X, IsOpen (stabilizer Gal(Ω/F) y).carrier) :
    Function.Bijective (evalGaloisSetAlgebra (toPermHom Gal(Ω/F) X)) := by
  have : Algebra.Etale F (galoisSetAlgebra (toPermHom Gal(Ω/F) X)) :=
    etale_galoisSetAlgebra_toPermHom hX
  have : Module.Finite F (galoisSetAlgebra (toPermHom Gal(Ω/F) X)) :=
    FormallyUnramified.finite_of_free F _
  refine (injective_evalGaloisSetAlgebra_toPermHom hX).bijective_of_nat_card_le ?_
  rw [← finrank_galoisSetAlgebra_toPermHom hX]
  exact card_algHom_le_finrank F _ _

end Action

section Hom

variable {ρ : Gal(Ω/F) →* Perm X}

lemma isOpen_comap_stabilizer (hρ : IsOpen (ρ.ker : Set Gal(Ω/F))) (x : X) :
    IsOpen ((stabilizer (Perm X) x).comap ρ : Set Gal(Ω/F)) :=
  Subgroup.isOpen_mono (fun _ hσ ↦
    (DFunLike.congr_fun (MonoidHom.mem_ker.mp hσ) x).trans (Perm.one_apply x)) hρ

variable [IsGalois F Ω] [Finite X]

/-- **The `F`-algebra of a finite Galois set `X` has dimension the size of `X`**, when the action of
`Gal(Ω/F)` on `X` is continuous, that is, has an open kernel. -/
lemma finrank_galoisSetAlgebra (hρ : IsOpen (ρ.ker : Set Gal(Ω/F))) :
    finrank F (galoisSetAlgebra ρ) = Nat.card X := by
  let _ : MulAction Gal(Ω/F) X := MulAction.compHom X ρ
  exact finrank_galoisSetAlgebra_toPermHom (isOpen_comap_stabilizer hρ)

/-- **The `F`-algebra of a finite Galois set is a finite separable (étale) `F`-algebra**, when the
action of `Gal(Ω/F)` is continuous. -/
lemma etale_galoisSetAlgebra (hρ : IsOpen (ρ.ker : Set Gal(Ω/F))) :
    Algebra.Etale F (galoisSetAlgebra ρ) := by
  let _ : MulAction Gal(Ω/F) X := MulAction.compHom X ρ
  exact etale_galoisSetAlgebra_toPermHom (isOpen_comap_stabilizer hρ)

/-- **The `F`-algebra maps to `Ω` of the `F`-algebra of a finite Galois set `X` are the evaluations
at the points of `X`, each once**, when the action of `Gal(Ω/F)` is continuous. With
`galoisSetPerm_evalGaloisSetAlgebra`, the Galois set of the algebra of `X` is `X`. -/
lemma bijective_evalGaloisSetAlgebra (hρ : IsOpen (ρ.ker : Set Gal(Ω/F))) :
    Function.Bijective (evalGaloisSetAlgebra ρ) := by
  let _ : MulAction Gal(Ω/F) X := MulAction.compHom X ρ
  exact bijective_evalGaloisSetAlgebra_toPermHom (isOpen_comap_stabilizer hρ)

end Hom

variable (F) (A : Type*) [CommRing A] [Algebra F A]

variable [Algebra.Etale F A] in
/-- **A finite separable `F`-algebra `A` has `[A : F]` algebra maps to the separable closure of
`F`**: `A` is a product of finite separable extensions `Kᵢ` of `F`, each with `[Kᵢ : F]`
embeddings, and the algebra maps from `A` are those of the factors. -/
lemma Etale.natCard_algHom_separableClosure :
    Nat.card (A →ₐ[F] SeparableClosure F) = finrank F A := by
  classical
  have : Module.Finite F A := FormallyUnramified.finite_of_free F A
  refine le_antisymm (card_algHom_le_finrank F A _) ?_
  rcases (Etale.iff_exists_algEquiv_prod F A).mp inferInstance with ⟨I, _, K, _, _, e, hK⟩
  let _ : Fintype I := Fintype.ofFinite I
  have : ∀ i, Module.Finite F (K i) := fun i ↦ (hK i).1
  have : ∀ i, Algebra.IsSeparable F (K i) := fun i ↦ (hK i).2
  have hcard (i : I) : Nat.card (K i →ₐ[F] SeparableClosure F) = finrank F (K i) :=
    AlgHom.natCard_of_splits F (K i) _ fun y ↦
      IsSepClosed.splits_codomain _ (IsSeparable.isSeparable F y)
  rw [e.toLinearEquiv.finrank_eq, finrank_pi_fintype, ← Finset.sum_congr rfl fun i _ ↦ hcard i,
    ← Nat.card_sigma]
  refine Nat.card_le_card_of_injective (fun p ↦ (p.2.comp (Pi.evalAlgHom F K p.1)).comp e.toAlgHom)
    ?_
  rintro ⟨i, φ⟩ ⟨j, ψ⟩ h
  have hij : i = j := by
    by_contra hij
    simpa [Pi.single_eq_of_ne' hij] using DFunLike.congr_fun h (e.symm (Pi.single i 1))
  subst hij
  exact congrArg (Sigma.mk i) <| AlgHom.ext fun b ↦ by
    simpa using DFunLike.congr_fun h (e.symm (Pi.single i b))

section Finite

variable [Module.Finite F A]

lemma isOpen_ker_galoisSetPerm [Algebra.IsAlgebraic F Ω] :
    IsOpen ((galoisSetPerm F Ω A).ker : Set Gal(Ω/F)) := by
  let b : Basis (Fin (finrank F A)) F A := Module.finBasis F A
  let S : Set Ω := ⋃ f : A →ₐ[F] Ω, Set.range (f ∘ b)
  have : Finite S := (Set.finite_iUnion fun _ ↦ Set.finite_range _).to_subtype
  have : FiniteDimensional F (IntermediateField.adjoin F S) :=
    finiteDimensional_adjoin fun y _ ↦ IsIntegral.isIntegral y
  refine Subgroup.isOpen_mono (fun σ hσ ↦ ?_) (fixingSubgroup_isOpen (IntermediateField.adjoin F S))
  refine MonoidHom.mem_ker.mpr <| Equiv.ext fun f ↦ AlgHom.toLinearMap_injective <| b.ext fun i ↦ ?_
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ <|
    IntermediateField.subset_adjoin F S <| Set.mem_iUnion.mpr ⟨f, Set.mem_range_self i⟩

variable {F A} (e : (A →ₐ[F] SeparableClosure F) ≃ Fin 6)

lemma isOpen_ker_sexticTwinPerm : IsOpen ((sexticTwinPerm e).ker : Set Gal(SeparableClosure F/F)) :=
  Subgroup.isOpen_mono (fun σ hσ ↦ by
    rw [MonoidHom.mem_ker, sexticTwinPerm_apply, MonoidHom.mem_ker.mp hσ]
    exact (congrArg _ (map_one e.permCongrHom)).trans (map_one _)) (isOpen_ker_galoisSetPerm F A)

/-- **The twin of a sextic algebra has degree `6`** (LMFDB `nf.sextic_twin`). -/
lemma finrank_sexticTwin : finrank F (sexticTwin e) = 6 :=
  (finrank_galoisSetAlgebra (isOpen_ker_sexticTwinPerm e)).trans (Nat.card_fin 6)

/-- **The twin of a sextic algebra is a finite separable (étale) algebra** (LMFDB
`nf.sextic_twin`). -/
lemma etale_sexticTwin : Algebra.Etale F (sexticTwin e) :=
  etale_galoisSetAlgebra (isOpen_ker_sexticTwinPerm e)

/-- **The twin of a sextic algebra `A` is a twin of `A`** (LMFDB `nf.sextic_twin`): its Galois
set, labelled by the evaluations, carries the Galois action of `A` twisted by the outer
automorphism of `S₆`. -/
lemma isSexticTwin_sexticTwin : IsSexticTwin F A (sexticTwin e) := by
  have hρ : Function.Bijective (evalGaloisSetAlgebra (sexticTwinPerm e)) :=
    bijective_evalGaloisSetAlgebra (isOpen_ker_sexticTwinPerm e)
  exact ⟨e, (Equiv.ofBijective _ hρ).symm, fun σ ↦ Equiv.ext fun i ↦
    (congrArg (Equiv.ofBijective _ hρ).symm (galoisSetPerm_evalGaloisSetAlgebra σ _ i)).trans
      (Equiv.ofBijective_symm_apply_apply _ hρ _)⟩

end Finite

variable {F A} [Algebra.Etale F A] in
/-- **Every finite separable algebra `A` of degree `6` has a twin** (LMFDB `nf.sextic_twin`), a
finite separable algebra of degree `6`: the twin `sexticTwin e` of `A` for any labelling `e` of
the six `F`-algebra maps `A → F^sep`. -/
lemma exists_isSexticTwin (h : finrank F A = 6) : ∃ B : Subalgebra F (Fin 6 → SeparableClosure F),
    Algebra.Etale F B ∧ finrank F B = 6 ∧ IsSexticTwin F A B := by
  have : Module.Finite F A := Module.finite_of_finrank_pos (by rw [h]; norm_num)
  let e : (A →ₐ[F] SeparableClosure F) ≃ Fin 6 :=
    Finite.equivFinOfCardEq ((Etale.natCard_algHom_separableClosure F A).trans h)
  exact ⟨sexticTwin e, etale_sexticTwin e, finrank_sexticTwin e, isSexticTwin_sexticTwin e⟩

variable {F A} in
/-- **Finite separable twins are unique up to isomorphism** (LMFDB `nf.sextic_twin`): two finite
separable algebras `B` and `B'` that are twins of `A` are isomorphic, so that the twin of a finite
separable algebra of degree `6` is well defined. Their Galois sets are isomorphic, and by Galois
descent (Tau Ceti's `Algebra.Etale.algHomEquivMulActionHom`) the `F`-algebra maps between finite
separable algebras are the `Gal(F^sep/F)`-equivariant maps between their Galois sets. -/
lemma IsSexticTwin.nonempty_algEquiv {B B' : Type*} [CommRing B] [Algebra F B] [CommRing B']
    [Algebra F B'] [Etale F B] [Etale F B'] (h : IsSexticTwin F A B) (h' : IsSexticTwin F A B') :
    Nonempty (B ≃ₐ[F] B') := by
  rcases h with ⟨eA, eB, h⟩
  rcases h' with ⟨eA', eB', h'⟩
  let g : Perm (Fin 6) := eA.symm.trans eA'
  have hg : eA' = eA.trans g := Equiv.ext fun φ ↦ by simp [g]
  let θg : Perm (Fin 6) := Perm.outerAutFinSix g
  have key (τ : Gal(SeparableClosure F/F)) : eB'.permCongr (galoisSetPerm F _ B' τ) =
      θg * eB.permCongr (galoisSetPerm F _ B τ) * θg⁻¹ := by
    rw [h' τ, hg, permCongr_trans_eq_mul, map_mul, map_mul, map_inv, ← h τ]
  let u : (B →ₐ[F] SeparableClosure F) ≃ (B' →ₐ[F] SeparableClosure F) :=
    (eB.trans θg).trans eB'.symm
  have hu (τ : Gal(SeparableClosure F/F)) (ψ : B →ₐ[F] SeparableClosure F) :
      u (galoisSetPerm F _ B τ ψ) = galoisSetPerm F _ B' τ (u ψ) :=
    eB'.symm_apply_eq.mpr <| by simpa [u] using (DFunLike.congr_fun (key τ) (θg (eB ψ))).symm
  let f : B' →ₐ[F] B := (Etale.algHomEquivMulActionHom _).symm ⟨u, hu⟩
  let f' : B →ₐ[F] B' := (Etale.algHomEquivMulActionHom _).symm ⟨u.symm, fun τ ψ ↦
    u.symm_apply_eq.mpr ((hu τ _).trans (congrArg _ (u.apply_symm_apply ψ))).symm⟩
  have hf (ψ : B →ₐ[F] SeparableClosure F) : ψ.comp f = u ψ :=
    DFunLike.congr_fun ((Etale.algHomEquivMulActionHom _).apply_symm_apply _) ψ
  have hf' (ψ : B' →ₐ[F] SeparableClosure F) : ψ.comp f' = u.symm ψ :=
    DFunLike.congr_fun ((Etale.algHomEquivMulActionHom _).apply_symm_apply _) ψ
  refine ⟨AlgEquiv.ofAlgHom f' f ?_ ?_⟩ <;>
    refine (Etale.algHomEquivMulActionHom (SeparableClosure F)).injective <|
      MulActionHom.ext fun ψ ↦ ?_ <;>
    simp [← AlgHom.comp_assoc, hf, hf']

end Algebra
